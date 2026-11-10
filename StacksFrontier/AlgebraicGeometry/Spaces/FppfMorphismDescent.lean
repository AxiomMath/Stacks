module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Descending a morphism of algebraic spaces along an fppf covering

Let `S` be a scheme contained in a big fppf site `B` and let `{f i : X i ⟶ F}` be an fppf
covering of algebraic spaces over `S`. A family of morphisms `g i : X i ⟶ Z` into a presheaf
`Z` satisfying the fppf sheaf condition which agree on the fibre products `X i ×_F X j`
descends to a unique morphism `F ⟶ Z`. Equivalently, an fppf covering of algebraic spaces is
an effective epimorphism for morphisms into an fppf sheaf, hence into any algebraic space.

This is the fppf case of the equalizer diagram of Stacks 04P2, which asserts the fpqc case.
The fpqc case rests on Gabber's Stacks 0APL, which this library does not carry; it is recorded
with that statement as an explicit hypothesis in
`StacksFrontier/AlgebraicGeometry/Spaces/FpqcMorphismDescent.lean`. Nothing of the kind is needed
here: an algebraic space is by definition a sheaf for the fppf topology of its site, and the
only other input is that an fppf covering is surjective as a map of fppf sheaves, Stacks 0469.

## Main results

* `AlgebraicGeometry.Space.exists_sieve_factorization_of_isFppfCovering`: a scheme-valued point
  of the target of an fppf covering factors through a member of the covering after restriction
  along a covering sieve of its source.
* `AlgebraicGeometry.Space.existsUnique_desc_of_isFppfCovering`: the descent, for a presheaf
  target satisfying the fppf sheaf condition.
* `AlgebraicGeometry.Space.hom_ext_of_isFppfCovering`: its separatedness half, that an fppf
  covering can be cancelled on the left.
* `AlgebraicGeometry.AlgebraicSpaces.existsUnique_desc_of_isFppfCovering` and
  `AlgebraicGeometry.AlgebraicSpaces.hom_ext_of_isFppfCovering`: both read in the category of
  algebraic spaces over `S`.

## Implementation notes

The local factorization statement is extracted from the proof of Stacks 0469
(`AlgebraicGeometry.Space.isLocallySurjective_coproductDesc_of_isFppfCovering`): that proof
pulls the covering back along a scheme-valued point of the target, refines the pullback by
schemes, transports the refinement to an fppf covering inside the site, and observes that each
member of the resulting covering sieve factors through a member of the original family. It is
the factorization, rather than the local surjectivity it implies, that the descent needs, since
the index of the member through which a given restriction factors must be available.

The compatibility hypothesis is stated as the equality of two morphisms into members of the
covering with a common composite to the target, rather than on the fibre product `X i ×_F X j`.
The two are equivalent — a pair with a common composite factors through the fibre product — and
the former is the form every step of the proof consumes.

## References

* [Stacks Project, Tag 0469](https://stacks.math.columbia.edu/tag/0469)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-! ### Local factorizations through a member of the covering -/

/-- If the representable family `yoneda.map (q i)` is an fppf covering, then every member of a
covering sieve of `U` factors through some `q i`. -/
theorem exists_sieve_factorization_of_isFppfCovering_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {I : Type v}
    (T : I → BigFppfOver B S hS) (U : BigFppfOver B S hS) (q : ∀ i, T i ⟶ U)
    (hT' : IsFppfCovering B S hS (fun i => yoneda.obj (T i)) (fun i => yoneda.map (q i))) :
    ∃ R : Sieve U, R ∈ BigFppfOver.topology B S hS U ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ U), R k → ∃ (i : I) (m : W ⟶ T i), m ≫ q i = k := by
  classical
  let J := BigFppfOver.topology B S hS
  let E : PreZeroHypercover U := ⟨I, T, q⟩
  let ES := (E.map (BigFppfOver.forget B S hS)).map B.inclusion
  have hE : ES.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    simpa [ES, E, PreZeroHypercover.map, BigFppfOver.toScheme] using
      yoneda_fppfCovering_mem_fppfPrecoverage B S hS T U q hT'
  obtain ⟨V, hV, hRef⟩ := exists_isCovering_refining_fppfCovering B U.left ES hE
  rcases hRef with ⟨ref⟩
  let Vover : PreZeroHypercover U :=
    { I₀ := V.I₀
      X j := Over.mk (V.f j ≫ U.hom)
      f j := Over.homMk (V.f j) }
  have hVbase : V.sieve₀ ∈ B.topology U.left := by
    change V.sieve₀ ∈ B.precoverage.toGrothendieck U.left
    rw [Precoverage.mem_toGrothendieck_iff]
    have hmem : V.presieve₀ ∈ B.precoverage.coverings U.left := ⟨V, rfl, hV⟩
    simpa [PreZeroHypercover.sieve₀] using Precoverage.Saturate.of U.left V.presieve₀ hmem
  have hVover : Vover.sieve₀ ∈ J U := by
    change Vover.sieve₀ ∈ B.topology.over (B.obj hS) U
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [Vover, PreZeroHypercover.sieve₀] using hVbase
  refine ⟨Vover.sieve₀, hVover, ?_⟩
  intro W k hk
  obtain ⟨j, l, hl⟩ := Sieve.ofArrows.exists hk
  let j0 : V.I₀ := j
  let jmap : (PreZeroHypercover.map B.inclusion V).I₀ := j0
  let i : I := ref.s₀ jmap
  have hw : ref.h₀ jmap ≫ B.inclusion.map (q i).left = B.inclusion.map (V.f j0) := by
    simpa [ES, E, PreZeroHypercover.map, jmap, j0, i] using ref.w₀ jmap
  have hpre : B.inclusion.map (B.inclusion.preimage (ref.h₀ jmap)) = ref.h₀ jmap :=
    B.inclusion.map_preimage _
  have hqmap : B.inclusion.map (T i).hom =
      B.inclusion.map (q i).left ≫ B.inclusion.map U.hom := by
    rw [← (q i).w, Functor.map_comp]
  have hrbase : (B.inclusion.preimage (ref.h₀ jmap)) ≫ (T i).hom = (Vover.X j0).hom := by
    apply B.inclusion.map_injective
    exact (B.inclusion.map_comp _ _).trans
      ((congrArg (fun t => t ≫ B.inclusion.map (T i).hom) hpre).trans
      ((congrArg (fun t => ref.h₀ jmap ≫ t) hqmap).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ B.inclusion.map U.hom) hw).trans
        ((B.inclusion.map_comp _ _).symm.trans (by simp [Vover]))))))
  let r : Vover.X j ⟶ T i := Over.homMk (B.inclusion.preimage (ref.h₀ jmap)) hrbase
  have hrfac : r ≫ q i = Vover.f j := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map
      (B.inclusion.preimage (ref.h₀ jmap) ≫ (q i).left) = B.inclusion.map (V.f j0)
    exact (B.inclusion.map_comp _ _).trans
      ((congrArg (fun t => t ≫ B.inclusion.map (q i).left) hpre).trans hw)
  exact ⟨i, l ≫ r, by rw [Category.assoc, hrfac, hl.symm]⟩

/-- A scheme-valued point `g` of the target of an fppf covering of algebraic spaces factors
through a member of the covering after restriction along a covering sieve: there is a covering
sieve of the source of `g` each of whose members `k` admits an `i` and a morphism
`η : h_W ⟶ X i` with `η ≫ f i = h_k ≫ g`. -/
theorem exists_sieve_factorization_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f)
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ F) :
    ∃ R : Sieve U, R ∈ BigFppfOver.topology B S hS U ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ U), R k →
        ∃ (i : I) (η : yoneda.obj W ⟶ X i), η ≫ f i = yoneda.map k ≫ g := by
  classical
  let Fspace : AlgebraicSpaces B S hS := ⟨F, hf.target_isAlgebraicSpace⟩
  let Xspace (i : I) : AlgebraicSpaces B S hS := ⟨X i, hf.source_isAlgebraicSpace i⟩
  let gspace : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ Fspace := ObjectProperty.homMk g
  let fspace (i : I) : Xspace i ⟶ Fspace := ObjectProperty.homMk (f i)
  let Y (i : I) := AlgebraicSpaces.fiberProduct B S hS gspace (fspace i)
  have hY : IsFppfCovering B S hS (fun i => (Y i).1) (fun i => pullback.fst g (f i)) :=
    isFppfCovering_fibreProduct B S hS Xspace fspace gspace hf
  obtain ⟨T, a, hT⟩ := exists_fppfCovering_scheme_refinement B S hS
    (fun i => (Y i).1) (fun i => pullback.fst g (f i)) hY
  let p₁ (i : I) := pullback.fst gspace.hom (fspace i).hom
  let p₂ (i : I) := pullback.snd gspace.hom (fspace i).hom
  let aa (i : I) : yoneda.obj (T i) ⟶ pullback gspace.hom (fspace i).hom := by
    simpa [Y, AlgebraicSpaces.fiberProduct] using a i
  let q (i : I) : T i ⟶ U := yonedaEquiv (aa i ≫ p₁ i)
  have hproj : ∀ i, aa i ≫ p₁ i = yoneda.map (q i) := by
    intro i
    apply (yonedaEquiv (X := T i) (F := yoneda.obj U)).injective
    simp only [q, yonedaEquiv_yoneda_map]
  have hT' : IsFppfCovering B S hS (fun i => yoneda.obj (T i))
      (fun i => yoneda.map (q i)) := by
    have heq : (fun i => yoneda.map (q i)) = (fun i => a i ≫ pullback.fst g (f i)) :=
      funext fun i => (hproj i).symm
    rw [heq]
    exact hT
  obtain ⟨R, hR, hfac⟩ := exists_sieve_factorization_of_isFppfCovering_yoneda B S hS T U q hT'
  refine ⟨R, hR, fun W k hk => ?_⟩
  obtain ⟨i, m, hcomp⟩ := hfac k hk
  refine ⟨i, yoneda.map m ≫ aa i ≫ p₂ i, ?_⟩
  change (yoneda.map m ≫ aa i ≫ p₂ i) ≫ (fspace i).hom = yoneda.map k ≫ g
  have hpc : p₂ i ≫ (fspace i).hom = p₁ i ≫ g := by
    simpa [p₁, p₂, gspace] using (pullback.condition).symm
  simp only [Category.assoc, hpc]
  simp only [← Category.assoc, hproj, ← yoneda.map_comp, hcomp]

/-! ### The descent -/

/-- The section of the target over an object of the site determined by a descent datum along an
fppf covering: it is characterised by its restrictions along the local factorizations through
members of the covering. -/
private theorem existsUnique_localSection_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ (i j : I) (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (α : P ⟶ X i) (β : P ⟶ X j),
      α ≫ f i = β ≫ f j → α ≫ g i = β ≫ g j)
    (T : BigFppfOver B S hS) (y : F.obj (op T)) :
    ∃! z : Z.obj (op T),
      ∀ (T' : BigFppfOver B S hS) (q : T' ⟶ T) (i : I) (b : yoneda.obj T' ⟶ X i),
        b ≫ f i = yoneda.map q ≫ yonedaEquiv.symm y →
        Z.map q.op z = yonedaEquiv (b ≫ g i) := by
  classical
  let J := BigFppfOver.topology B S hS
  have hZ' : Presieve.IsSheaf J Z := (isSheaf_iff_isSheaf_of_type J Z).mp hZ
  obtain ⟨R, hR, hlift⟩ :=
    exists_sieve_factorization_of_isFppfCovering B S hS X f hf T (yonedaEquiv.symm y)
  choose idx lift hliftSpec using
    fun (W : BigFppfOver B S hS) (k : W ⟶ T) (hk : R k) => hlift k hk
  let x : Presieve.FamilyOfElements Z R.arrows :=
    fun W k hk => yonedaEquiv (lift W k hk ≫ g (idx W k hk))
  have hx : x.Compatible := by
    intro W₁ W₂ P e₁ e₂ k₁ k₂ h₁ h₂ hcomm
    have key : (yoneda.map e₁ ≫ lift W₁ k₁ h₁) ≫ f (idx W₁ k₁ h₁) =
        (yoneda.map e₂ ≫ lift W₂ k₂ h₂) ≫ f (idx W₂ k₂ h₂) := by
      rw [Category.assoc, Category.assoc, hliftSpec, hliftSpec, ← Category.assoc,
        ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, hcomm]
    change Z.map e₁.op (yonedaEquiv (lift W₁ k₁ h₁ ≫ g (idx W₁ k₁ h₁))) =
      Z.map e₂.op (yonedaEquiv (lift W₂ k₂ h₂ ≫ g (idx W₂ k₂ h₂)))
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv (by simpa only [Category.assoc] using hg _ _ _ _ _ key)
  obtain ⟨z, hz, hzu⟩ := hZ' R hR x hx
  refine ⟨z, ?_, ?_⟩
  · intro T' q i b hb
    refine (hZ' (R.pullback q) (J.pullback_stable q hR)).isSeparatedFor.ext ?_
    intro W r hr
    have hrR : R (r ≫ q) := hr
    have hfac : lift W (r ≫ q) hrR ≫ f (idx W (r ≫ q) hrR) =
        (yoneda.map r ≫ b) ≫ f i := by
      rw [hliftSpec, Category.assoc, hb, ← Category.assoc, ← yoneda.map_comp]
    calc
      Z.map r.op (Z.map q.op z) = Z.map (r ≫ q).op z := by
        rw [← Functor.map_comp_apply, ← op_comp]
      _ = x (r ≫ q) hrR := hz _ hrR
      _ = yonedaEquiv ((yoneda.map r ≫ b) ≫ g i) :=
        congrArg yonedaEquiv (hg _ _ _ _ _ hfac)
      _ = Z.map r.op (yonedaEquiv (b ≫ g i)) := by
        rw [yonedaEquiv_naturality, Category.assoc]
  · intro z' hz'
    refine (hZ' R hR).isSeparatedFor.ext ?_
    intro W k hk
    exact (hz' W k (idx W k hk) (lift W k hk) (hliftSpec W k hk)).trans (hz k hk).symm

/-- A morphism of presheaves `d` with `f ≫ d = g` evaluates, on a section `y` whose restriction
along `q` lifts along `f` to `b`, to the restriction determined by `b ≫ g`. -/
theorem map_app_eq_yonedaEquiv_comp {C : Type*} [Category.{v} C] {X F Z : Cᵒᵖ ⥤ Type v}
    {f : X ⟶ F} {g : X ⟶ Z} {d : F ⟶ Z} (hd : f ≫ d = g) {T T' : C} (y : F.obj (op T))
    (q : T' ⟶ T) (b : yoneda.obj T' ⟶ X) (hb : b ≫ f = yoneda.map q ≫ yonedaEquiv.symm y) :
    Z.map q.op (d.app (op T) y) = yonedaEquiv (b ≫ g) := by
  have hy : yonedaEquiv (b ≫ f) = F.map q.op y := by
    rw [hb, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  rw [← NatTrans.naturality_apply, ← hy, ← yonedaEquiv_comp, Category.assoc, hd]

/-- The existence half of the fppf case of Stacks 04P2, for a family of morphisms any two of
which agree on morphisms with a common composite to the target of the covering. -/
theorem exists_desc_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ (i j : I) (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (α : P ⟶ X i) (β : P ⟶ X j),
      α ≫ f i = β ≫ f j → α ≫ g i = β ≫ g j) :
    ∃ d : F ⟶ Z, ∀ i, f i ≫ d = g i := by
  classical
  let localDesc := existsUnique_localSection_fppf B S hS X f hf hZ g hg
  let sectionAt (T : BigFppfOver B S hS) (y : F.obj (op T)) : Z.obj (op T) :=
    (localDesc T y).choose
  have sectionAt_spec (T : BigFppfOver B S hS) (y : F.obj (op T)) :
      ∀ (T' : BigFppfOver B S hS) (q : T' ⟶ T) (i : I) (b : yoneda.obj T' ⟶ X i),
        b ≫ f i = yoneda.map q ≫ yonedaEquiv.symm y →
        Z.map q.op (sectionAt T y) = yonedaEquiv (b ≫ g i) :=
    (localDesc T y).choose_spec.1
  have sectionAt_unique (T : BigFppfOver B S hS) (y : F.obj (op T)) (z : Z.obj (op T))
      (hzspec : ∀ (T' : BigFppfOver B S hS) (q : T' ⟶ T) (i : I) (b : yoneda.obj T' ⟶ X i),
        b ≫ f i = yoneda.map q ≫ yonedaEquiv.symm y →
        Z.map q.op z = yonedaEquiv (b ≫ g i)) :
      z = sectionAt T y :=
    (localDesc T y).choose_spec.2 z hzspec
  let η : F ⟶ Z :=
    { app := fun T => TypeCat.ofHom (sectionAt T.unop)
      naturality := by
        intro T' T q
        apply ConcreteCategory.ext
        ext y
        change sectionAt T.unop (F.map q y) = Z.map q (sectionAt T'.unop y)
        refine (sectionAt_unique T.unop (F.map q y)
          (Z.map q (sectionAt T'.unop y)) ?_).symm
        intro T'' r i b hb
        have hfactor : b ≫ f i = yoneda.map (r ≫ q.unop) ≫ yonedaEquiv.symm y := by
          rw [hb, yonedaEquiv_symm_map, yoneda.map_comp, Category.assoc]
        simpa only [op_comp, Functor.map_comp_apply, Quiver.Hom.op_unop] using
          sectionAt_spec T'.unop y T'' (r ≫ q.unop) i b hfactor }
  refine ⟨η, fun i => NatTrans.ext (funext fun T => ?_)⟩
  obtain ⟨T⟩ := T
  apply ConcreteCategory.ext
  ext w
  change sectionAt T ((f i).app (op T) w) = (g i).app (op T) w
  have hglocal : yonedaEquiv (yonedaEquiv.symm w ≫ g i) = (g i).app (op T) w := by
    simpa using yonedaEquiv_comp (yonedaEquiv.symm w) (g i)
  simpa using (sectionAt_spec T ((f i).app (op T) w) T (𝟙 T) i
    (yonedaEquiv.symm w) (yonedaEquiv_symm_naturality_right T (f i) w)).trans hglocal

/-- **The fppf case of Stacks 04P2.** A family of morphisms from the members of an fppf
covering of algebraic spaces over `S` to a presheaf satisfying the fppf sheaf condition, any
two of which agree on morphisms with a common composite to the target of the covering,
descends to a unique morphism out of that target. -/
theorem existsUnique_desc_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ i j : I,
      pullback.fst (f i) (f j) ≫ g i = pullback.snd (f i) (f j) ≫ g j) :
    ∃! d : F ⟶ Z, ∀ i, f i ≫ d = g i := by
  have hguniv : ∀ (i j : I) (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (α : P ⟶ X i) (β : P ⟶ X j), α ≫ f i = β ≫ f j → α ≫ g i = β ≫ g j := by
    intro i j P α β h
    calc
      α ≫ g i = (pullback.lift α β h ≫ pullback.fst (f i) (f j)) ≫ g i := by
        rw [pullback.lift_fst]
      _ = pullback.lift α β h ≫ pullback.snd (f i) (f j) ≫ g j := by
        rw [Category.assoc, hg]
      _ = β ≫ g j := by rw [← Category.assoc, pullback.lift_snd]
  refine existsUnique_of_exists_of_unique
    (exists_desc_of_isFppfCovering B S hS X f hf hZ g hguniv) fun d₁ d₂ hd₁ hd₂ => ?_
  refine NatTrans.ext (funext fun T => ?_)
  obtain ⟨T⟩ := T
  apply ConcreteCategory.ext
  ext y
  change d₁.app (op T) y = d₂.app (op T) y
  exact (existsUnique_localSection_fppf B S hS X f hf hZ g hguniv T y).unique
    (fun _ q _ b hb => map_app_eq_yonedaEquiv_comp (hd₁ _) y q b hb)
    (fun _ q _ b hb => map_app_eq_yonedaEquiv_comp (hd₂ _) y q b hb)

/-- An fppf covering of algebraic spaces over `S` can be cancelled on the left in morphisms
into a presheaf satisfying the fppf sheaf condition. -/
theorem hom_ext_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    {a b : F ⟶ Z} (hab : ∀ i, f i ≫ a = f i ≫ b) : a = b := by
  obtain ⟨d, _, hdu⟩ := existsUnique_desc_of_isFppfCovering B S hS X f hf hZ
    (fun i => f i ≫ a) fun i j => pullback.condition_assoc a
  exact (hdu a fun _ => rfl).trans (hdu b fun i => (hab i).symm).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.AlgebraicSpaces

/-- **The fppf case of Stacks 04P2**, in the category of algebraic spaces over `S`. A
compatible family of morphisms from the members of an fppf covering to an algebraic space `Z`
descends to a unique morphism from the target of the covering. -/
theorem existsUnique_desc_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y)
    (hf : AlgebraicGeometry.Space.IsFppfCovering B S hS (fun i => (X i).obj) (fun i => (f i).hom))
    (Z : AlgebraicSpaces B S hS)
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ (i j : I) (T : AlgebraicSpaces B S hS) (α : T ⟶ X i) (β : T ⟶ X j),
      α ≫ f i = β ≫ f j → α ≫ g i = β ≫ g j) :
    ∃! h : Y ⟶ Z, ∀ i, f i ≫ h = g i := by
  have hg' : ∀ i j : I, pullback.fst (f i).hom (f j).hom ≫ (g i).hom =
      pullback.snd (f i).hom (f j).hom ≫ (g j).hom := fun i j =>
    congrArg (fun m : AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ Z => m.hom)
      (hg i j (AlgebraicSpaces.fiberProduct B S hS (f i) (f j))
        (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom))
        (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom))
        (ObjectProperty.hom_ext _ pullback.condition))
  obtain ⟨d, hd, hdu⟩ := AlgebraicGeometry.Space.existsUnique_desc_of_isFppfCovering B S hS
    (fun i => (X i).obj) (fun i => (f i).hom) hf Z.property.isSheaf
    (fun i => (g i).hom) hg'
  exact ⟨ObjectProperty.homMk d, fun i => ObjectProperty.hom_ext _ (hd i), fun h' hh' =>
    ObjectProperty.hom_ext _ (hdu h'.hom fun i => congrArg (fun m : X i ⟶ Z => m.hom) (hh' i))⟩

/-- An fppf covering of algebraic spaces over `S` can be cancelled on the left in the category
of algebraic spaces over `S`. -/
theorem hom_ext_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y Z : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y)
    (hf : AlgebraicGeometry.Space.IsFppfCovering B S hS (fun i => (X i).obj) (fun i => (f i).hom))
    {a b : Y ⟶ Z} (hab : ∀ i, f i ≫ a = f i ≫ b) : a = b :=
  ObjectProperty.hom_ext _
    (AlgebraicGeometry.Space.hom_ext_of_isFppfCovering B S hS
      (fun i => (X i).obj) (fun i => (f i).hom) hf Z.property.isSheaf
      fun i => congrArg (fun m : X i ⟶ Z => m.hom) (hab i))

end AlgebraicGeometry.AlgebraicSpaces

end
