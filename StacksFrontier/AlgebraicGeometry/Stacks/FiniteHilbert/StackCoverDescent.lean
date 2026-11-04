module

public import StacksFrontier.AlgebraicGeometry.Descent.BigFppfSiteEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Basic
import all StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverDescent

/-!
# Descending the cover of an object of the relative finite Hilbert category

Given a covering family `{U i ⟶ U}` of the big fppf site and a descent datum of objects
`(U i, Z i, y i, x i, α i)` of the relative finite Hilbert category, the covers `Z i ⟶ U i`
themselves form a descent datum of schemes. It is effective, since a degree-`d` finite locally
free morphism is affine ([Stacks, Tag 0245](https://stacks.math.columbia.edu/tag/0245)), and the
descended morphism is again finite locally free of degree `d`, since that property is fpqc local
on the base ([Stacks, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)).

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.exists_fpqc_cover_refining`: a covering sieve of the big
  fppf site over `S` is refined by a covering family whose underlying family of schemes is an
  fpqc covering family.
* `AlgebraicGeometry.Stack.FiniteHilbert.exists_scheme_cocone_of_isFiniteLocallyFreeOfRank`: a
  descent datum of degree-`r` finite locally free morphisms over an fpqc covering family is
  effective, with descended morphism again finite locally free of degree `r`, in cocone form.
* `AlgebraicGeometry.Stack.FiniteHilbert.exists_site_cocone_of_scheme_cocone`: such a cocone,
  lifted into the big fppf category over `S`.
* `AlgebraicGeometry.Stack.FiniteHilbert.exists_fpqc_cocone_of_diagram`: **the covers of a
  diagram of objects of the relative finite Hilbert category over an fpqc covering family descend
  to a single degree-`d` finite locally free cover**, compatibly with the diagram.

## References

* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits


namespace AlgebraicGeometry.Stack.FiniteHilbert

universe u w v

/-! ### Refining a covering sieve by an fpqc covering family -/

section Refinement

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A covering sieve of the big fppf category over `S` is refined by a covering family whose
underlying family of schemes is an fpqc covering family.** -/
theorem exists_fpqc_refinement {U : BigFppfOver B S hS} {I : Type w}
    (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U) :
    ∃ E : PreZeroHypercover ((BigFppfOver.forget B S hS).obj U),
      B.IsCovering ⟨(BigFppfOver.forget B S hS).obj U, E⟩ ∧
      Presieve.ofArrows (fun i => B.inclusion.obj (E.X i))
        (fun i => B.inclusion.map (E.f i)) ∈
          Scheme.fpqcPrecoverage
            (B.inclusion.obj ((BigFppfOver.forget B S hS).obj U)) ∧
      E.presieve₀ ≤ Sieve.ofArrows (fun i => (BigFppfOver.forget B S hS).obj (V i))
        (fun i => (BigFppfOver.forget B S hS).map (f i)) := by
  have hbase : Sieve.ofArrows (fun i => (BigFppfOver.forget B S hS).obj (V i))
      (fun i => (BigFppfOver.forget B S hS).map (f i)) ∈
        B.topology ((BigFppfOver.forget B S hS).obj U) := by
    change Sieve.ofArrows V f ∈ (B.topology.over (B.obj hS)) U at hf
    rwa [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hf
  obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B hbase
  refine ⟨E, hE, Scheme.fppfPrecoverage_le_fpqcPrecoverage _ ?_, hER⟩
  simpa [AlgebraicGeometry.IsFppfCovering, Scheme.fppfPrecoverage,
    PreZeroHypercover.presieve₀_map] using B.isFppfCovering_of_isCovering hE

/-- **A covering sieve of the big fppf category over `S` contains a covering family whose
underlying family of schemes is an fpqc covering family**, stated inside the slice: the members of
the family are objects over `S` and the family is covering for the localized topology. -/
theorem exists_fpqc_cover_refining {U : BigFppfOver B S hS} {I : Type w}
    (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      Sieve.ofArrows E.X E.f ∈ BigFppfOver.topology B S hS U ∧
      (∀ i, Sieve.ofArrows V f (E.f i)) ∧
      Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (E.X i))
        (fun i => (BigFppfOver.toScheme B S hS).map (E.f i)) ∈
        Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U) := by
  classical
  obtain ⟨E, hE, hfpqc, hle⟩ := exists_fpqc_refinement B S hS V f hf
  have hfac (j : E.I₀) := Functor.exists_factorization_of_ofArrows (hle _ _ ⟨j⟩)
  choose idx a ha using hfac
  let E' : PreZeroHypercover U :=
    { I₀ := E.I₀
      X j := Over.mk (E.f j ≫ U.hom)
      f j := Over.homMk (E.f j) }
  let a' (j : E'.I₀) : E'.X j ⟶ V (idx j) := Over.homMk (a j) (by
    show a j ≫ (V (idx j)).hom = E.f j ≫ U.hom
    rw [← Over.w (f (idx j)), ← Category.assoc]
    exact congrArg (fun z => z ≫ U.hom) (ha j))
  have ha' (j : E'.I₀) : a' j ≫ f (idx j) = E'.f j := Over.OverMorphism.ext (ha j)
  refine ⟨E', ?_, fun j => ⟨_, a' j, _, ⟨idx j⟩, ha' j⟩, hfpqc⟩
  show Sieve.ofArrows E'.X E'.f ∈ (B.topology.over (B.obj hS)) U
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩

end Refinement

/-! ### Degree-`d` finite local freeness along an fpqc covering family -/

section Rank

/-- **Being finite locally free of degree `r` is fpqc local on the base**: a morphism whose base
change along every member of an fpqc covering family is finite locally free of degree `r` is
itself finite locally free of degree `r`. See
[Stacks, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO). -/
theorem isFiniteLocallyFreeOfRank_of_fpqcCover {T : Scheme.{u}} {I : Type w}
    (V : I → Scheme.{u}) (f : ∀ i, V i ⟶ T)
    (hf : Presieve.ofArrows V f ∈ Scheme.fpqcPrecoverage T)
    {Z : Scheme.{u}} (q : Z ⟶ T) (r : ℕ)
    (h : ∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd q (f i)) r) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank q r := by
  let P : MorphismProperty Scheme.{u} :=
    fun _ _ g => Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r
  have : MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc r
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hf ?_
  rintro _ _ _ ⟨i⟩
  exact h i

end Rank

/-! ### Products in a slice from cartesian squares -/

section Products

variable {C : Type u} [Category.{v} C]

/-- **A cartesian square exhibits its source as a product in the slice.** A cartesian square over
the two structure morphisms identifies its source with the product in the slice, compatibly with
both projections. -/
theorem over_exists_product_iso [HasPullbacks C] {S : C} {W X Y : Over S} [HasBinaryProduct X Y]
    (a : W ⟶ X) (b : W ⟶ Y) (sq : IsPullback a.left b.left X.hom Y.hom) :
    ∃ e : W ≅ X ⨯ Y, e.hom ≫ prod.fst = a ∧ e.hom ≫ prod.snd = b := by
  let e := sq.isoPullback ≪≫ (Over.prodLeftIsoPullback X Y).symm
  have h₁ : e.hom ≫ (prod.fst : X ⨯ Y ⟶ X).left = a.left := by simp [e]
  have h₂ : e.hom ≫ (prod.snd : X ⨯ Y ⟶ Y).left = b.left := by simp [e]
  refine ⟨Over.isoMk e (by
    rw [← Over.w (prod.fst : X ⨯ Y ⟶ X), ← Category.assoc, h₁, Over.w]),
    Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩

/-- **The cocycle condition of a transition datum, checked on a presentation of the triple
product.** Given an identification `t` of `T` with the left-associated triple product and two
further projections `m` and `n` compatible with `t`, the two ways round the cocycle triangle
agree as soon as they agree after `m` and `n` on the last component. -/
theorem productTransition_cocycle [HasBinaryProducts C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ T : C} (q₁ : Y₁ ⟶ X₁) (q₂ : Y₂ ⟶ X₂)
    (a : Y₁ ⨯ X₂ ⟶ X₁ ⨯ Y₂) (b : Y₂ ⨯ X₃ ⟶ X₂ ⨯ Y₃) (c : Y₁ ⨯ X₃ ⟶ X₁ ⨯ Y₃)
    (ha : a ≫ prod.fst = prod.fst ≫ q₁) (ha' : a ≫ prod.snd ≫ q₂ = prod.snd)
    (hb : b ≫ prod.fst = prod.fst ≫ q₂) (hc : c ≫ prod.fst = prod.fst ≫ q₁)
    (t : T ≅ (Y₁ ⨯ X₂) ⨯ X₃) (m : T ⟶ Y₂ ⨯ X₃) (n : T ⟶ Y₁ ⨯ X₃)
    (hm₁ : m ≫ prod.fst = t.hom ≫ prod.fst ≫ a ≫ prod.snd)
    (hm₂ : m ≫ prod.snd = t.hom ≫ prod.snd)
    (hn₁ : n ≫ prod.fst = t.hom ≫ prod.fst ≫ prod.fst)
    (hn₂ : n ≫ prod.snd = t.hom ≫ prod.snd)
    (hmn : m ≫ b ≫ prod.snd = n ≫ c ≫ prod.snd) :
    prod.map a (𝟙 X₃) ≫ prodMapLastTwo b = prodMapFirstThird c := by
  refine (cancel_epi t.hom).mp ?_
  refine prod.hom_ext ?_ ?_
  · refine prod.hom_ext ?_ ?_
    · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc, ha, hc]
    · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc, hb, ha']
  · have hm : t.hom ≫ prod.map a (𝟙 X₃) ≫ prod.lift (prod.fst ≫ prod.snd) prod.snd = m := by
      refine prod.hom_ext ?_ ?_ <;> simp [hm₁, hm₂]
    have hn : t.hom ≫ prod.lift (prod.fst ≫ prod.fst) prod.snd = n := by
      refine prod.hom_ext ?_ ?_ <;> simp [hn₁, hn₂]
    simp only [prodMapLastTwo, prodMapFirstThird, Limits.prod.associator,
      Limits.prod.braiding, prod.map_fst_assoc, prod.map_snd_assoc, prod.map_fst, prod.map_snd,
      prod.lift_fst, prod.lift_snd, prod.lift_fst_assoc, prod.lift_snd_assoc, prod.comp_lift,
      Category.comp_id]
    simpa only [Category.assoc] using
      (congrArg (fun z => z ≫ b ≫ prod.snd) hm).trans
        (hmn.trans (congrArg (fun z => z ≫ c ≫ prod.snd) hn).symm)

end Products

/-! ### The scheme-level descent -/

section SchemeDescent

/-- **A descent datum of degree-`r` finite locally free morphisms over an fpqc covering family is
effective**, in cocone form: there are a degree-`r` finite locally free morphism `q : Z ⟶ T` and
gluing-invariant morphisms `g i` from the members of the datum to `Z`, each forming a cartesian
square over `f i`. -/
theorem exists_scheme_cocone_of_isFiniteLocallyFreeOfRank {T : Scheme.{u}} {I : Type w}
    {V : I → Scheme.{u}} (f : ∀ i, V i ⟶ T)
    (hf : Presieve.ofArrows V f ∈ Scheme.fpqcPrecoverage T)
    (D : DescentData f) (r : ℕ)
    (hD : ∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.obj i).hom r) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ T),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank q r ∧
      ∃ g : ∀ i, (D.obj i).left ⟶ Z,
        (∀ i, IsPullback (g i) (D.obj i).hom q (f i)) ∧ D.IsGluingInvariant g := by
  obtain ⟨C⟩ := DescentData.nonempty_chart_of_isFamilyEffective D
    (DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex f hf D
      fun i => (hD i).toIsAffineHom)
  refine ⟨C.base.left, C.base.hom, ?_, C.proj, C.isPullback,
    (DescentData.isGluingInvariant_iff D C.proj).2 C.compat⟩
  refine isFiniteLocallyFreeOfRank_of_fpqcCover V f hf C.base.hom r fun i => ?_
  have := hD i
  have hsq : IsPullback (C.isPullback i).isoPullback.inv (pullback.snd C.base.hom (f i))
      (D.obj i).hom (𝟙 (V i)) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, Iso.inv_comp_eq]
    exact (C.isPullback i).isoPullback_hom_snd.symm
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hsq

end SchemeDescent

/-! ### Lifting a cocone of schemes into the big fppf category -/

section Lift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A cocone of schemes whose vertex carries a degree-`r` finite locally free morphism to an
object of the site lifts into the site.** -/
theorem exists_site_cocone_of_scheme_cocone {U : BigFppfOver B S hS} {I : Type w}
    {V W : I → BigFppfOver B S hS} (f : ∀ i, V i ⟶ U) (p : ∀ i, W i ⟶ V i)
    {Z : Scheme.{u}} (q : Z ⟶ (BigFppfOver.toScheme B S hS).obj U) (r : ℕ)
    (hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank q r)
    (g : ∀ i, (BigFppfOver.toScheme B S hS).obj (W i) ⟶ Z)
    (sq : ∀ i, IsPullback (g i) ((BigFppfOver.toScheme B S hS).map (p i)) q
      ((BigFppfOver.toScheme B S hS).map (f i))) :
    ∃ (Z' : BigFppfOver B S hS) (q' : Z' ⟶ U) (g' : ∀ i, W i ⟶ Z'),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map q') r ∧
      (∀ i, IsPullback (g' i) (p i) q' (f i)) ∧
      ∀ {A : BigFppfOver B S hS} (i j : I) (a : A ⟶ W i) (b : A ⟶ W j),
        (BigFppfOver.toScheme B S hS).map a ≫ g i =
          (BigFppfOver.toScheme B S hS).map b ≫ g j → a ≫ g' i = b ≫ g' j := by
  classical
  have hz : B.Contains Z :=
    contains_source_of_isFiniteLocallyFreeOfRank B q r U.left.property hq
  let q₀ : B.obj hz ⟶ U.left := B.inclusion.preimage q
  let Z' : BigFppfOver B S hS := Over.mk (q₀ ≫ U.hom)
  let q' : Z' ⟶ U := Over.homMk q₀
  let g₀ (i : I) : (W i).left ⟶ B.obj hz := B.inclusion.preimage (g i)
  have hq₀ : B.inclusion.map q₀ = q :=
    B.inclusion.map_preimage (X := B.obj hz) (Y := U.left) q
  have hg₀map (i : I) : B.inclusion.map (g₀ i) = g i :=
    B.inclusion.map_preimage (X := (W i).left) (Y := B.obj hz) (g i)
  have hg₀ (i : I) : g₀ i ≫ q₀ = (p i).left ≫ (f i).left := by
    refine B.inclusion.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hq₀, hg₀map]
    exact (sq i).w
  let g' (i : I) : W i ⟶ Z' := Over.homMk (g₀ i) (by
    show g₀ i ≫ (q₀ ≫ U.hom) = (W i).hom
    rw [← Category.assoc, hg₀, Category.assoc, Over.w, Over.w])
  have hq' : (BigFppfOver.toScheme B S hS).map q' = q := hq₀
  have hg' (i : I) : (BigFppfOver.toScheme B S hS).map (g' i) = g i := hg₀map i
  refine ⟨Z', q', g', ?_, ?_, ?_⟩
  · rwa [hq']
  · intro i
    refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
    simpa only [hq', hg'] using sq i
  · intro A i j a b hab
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    simpa only [Functor.map_comp, hg'] using hab

end Lift

/-! ### The covers of a diagram of objects descend -/

section Diagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- The cover of an object of the relative finite Hilbert category, viewed as an object of the
slice of schemes over a prescribed base object. -/
abbrev sourceOver {U : BigFppfOver B S hS} (P : Object B S hS 𝒳 𝒴 F d) (f : P.U ⟶ U) :=
  (Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
    (Over.mk ((BigFppfOver.toScheme B S hS).map P.q))

/-- The cover component of a morphism of the relative finite Hilbert category, viewed as a
morphism of the slice of schemes over a prescribed base object. -/
def sourceOverMap {U : BigFppfOver B S hS} {P Q : Object B S hS 𝒳 𝒴 F d} (φ : P ⟶ Q)
    {f : P.U ⟶ U} {g : Q.U ⟶ U} (h : φ.f ≫ g = f) : sourceOver P f ⟶ sourceOver Q g :=
  Over.homMk ((BigFppfOver.toScheme B S hS).map φ.g) (by
    change (BigFppfOver.toScheme B S hS).map φ.g ≫
      ((BigFppfOver.toScheme B S hS).map Q.q ≫ (BigFppfOver.toScheme B S hS).map g) =
      (BigFppfOver.toScheme B S hS).map P.q ≫ (BigFppfOver.toScheme B S hS).map f
    have heq : φ.g ≫ (Q.q ≫ g) = P.q ≫ f := by
      rw [← Category.assoc, φ.square.w, Category.assoc, h]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (BigFppfOver.toScheme B S hS).map heq)

/-- The cartesian square of a morphism over a cartesian square of base objects stays cartesian
in the base schemes, with the second leg the cover map followed by the target's cover. -/
private theorem isPullback_map_cover {U : BigFppfOver B S hS} {P Q R : Object B S hS 𝒳 𝒴 F d}
    {f : P.U ⟶ U} {g : Q.U ⟶ U} (a : R ⟶ P) (b : R ⟶ Q) (sq : IsPullback a.f b.f f g) :
    IsPullback ((BigFppfOver.toScheme B S hS).map a.g)
      ((BigFppfOver.toScheme B S hS).map b.g ≫ (BigFppfOver.toScheme B S hS).map Q.q)
      ((BigFppfOver.toScheme B S hS).map P.q ≫ (BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map g) := by
  have := preservesPullbacks_bigFppfOverToScheme B S hS
  rw [← Functor.map_comp, b.square.w]
  simpa only [Functor.map_comp] using ((a.square.paste_vert sq).map (BigFppfOver.toScheme B S hS))

/-- Two factorizations of a morphism of the relative finite Hilbert category through the same
object give equal composites of the induced morphisms of covers. -/
private theorem sourceOverMap_comp_eq {U : BigFppfOver B S hS}
    {A M M' Z : Object B S hS 𝒳 𝒴 F d} (φ : A ⟶ M) (ψ : M ⟶ Z) (φ' : A ⟶ M') (ψ' : M' ⟶ Z)
    (h : φ ≫ ψ = φ' ≫ ψ') {u : A.U ⟶ U} {fM : M.U ⟶ U} {fM' : M'.U ⟶ U} {fZ : Z.U ⟶ U}
    (h₁ : φ.f ≫ fM = u) (h₂ : ψ.f ≫ fZ = fM) (h₁' : φ'.f ≫ fM' = u) (h₂' : ψ'.f ≫ fZ = fM') :
    sourceOverMap φ h₁ ≫ sourceOverMap ψ h₂ = sourceOverMap φ' h₁' ≫ sourceOverMap ψ' h₂' := by
  refine Over.OverMorphism.ext ?_
  change (BigFppfOver.toScheme B S hS).map φ.g ≫ (BigFppfOver.toScheme B S hS).map ψ.g =
    (BigFppfOver.toScheme B S hS).map φ'.g ≫ (BigFppfOver.toScheme B S hS).map ψ'.g
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun z => (BigFppfOver.toScheme B S hS).map z.g) h

/-- **The two product identifications attached to a cartesian square of base objects.** For a
cartesian square of base objects filled by two morphisms of the relative finite Hilbert category,
the cover of the corner is simultaneously the product of the cover of the first object with the
second base object and the product of the first base object with the cover of the second, and the
two identifications match the four projections. -/
theorem sourceOver_pair {U : BigFppfOver B S hS} {P Q R : Object B S hS 𝒳 𝒴 F d}
    (f : P.U ⟶ U) (g : Q.U ⟶ U) (a : R ⟶ P) (b : R ⟶ Q)
    (sq : IsPullback a.f b.f f g) :
    ∃ (l : sourceOver R (a.f ≫ f) ≅
        sourceOver P f ⨯ Over.mk ((BigFppfOver.toScheme B S hS).map g))
      (r : sourceOver R (a.f ≫ f) ≅
        Over.mk ((BigFppfOver.toScheme B S hS).map f) ⨯ sourceOver Q g),
      l.hom ≫ prod.fst = sourceOverMap a rfl ∧
      r.hom ≫ prod.snd = sourceOverMap b sq.w.symm ∧
      l.hom ≫ prod.snd = r.hom ≫ prod.snd ≫
        structureMap ((BigFppfOver.toScheme B S hS).map g)
          (Over.mk ((BigFppfOver.toScheme B S hS).map Q.q)) ∧
      r.hom ≫ prod.fst = l.hom ≫ prod.fst ≫
        structureMap ((BigFppfOver.toScheme B S hS).map f)
          (Over.mk ((BigFppfOver.toScheme B S hS).map P.q)) := by
  have := preservesPullbacks_bigFppfOverToScheme B S hS
  have := hasPullbacks_bigFppfOver B S hS
  let H := BigFppfOver.toScheme B S hS
  let ca := sourceOverMap a (g := f) rfl
  let cb := sourceOverMap b (g := g) sq.w.symm
  let p₁ : sourceOver R (a.f ≫ f) ⟶ Over.mk (H.map f) :=
    ca ≫ structureMap (H.map f) (Over.mk (H.map P.q))
  let p₂ : sourceOver R (a.f ≫ f) ⟶ Over.mk (H.map g) :=
    cb ≫ structureMap (H.map g) (Over.mk (H.map Q.q))
  have hs₁ : IsPullback ca.left p₂.left (sourceOver P f).hom (H.map g) :=
    isPullback_map_cover a b sq
  have hs₂ : IsPullback p₁.left cb.left (H.map f) (sourceOver Q g).hom :=
    (isPullback_map_cover b a sq.flip).flip
  obtain ⟨l, hl₁, hl₂⟩ := over_exists_product_iso ca p₂ hs₁
  obtain ⟨r, hr₁, hr₂⟩ := over_exists_product_iso p₁ cb hs₂
  refine ⟨l, r, hl₁, hr₂, ?_, ?_⟩
  · rw [hl₂, ← Category.assoc, hr₂]
  · rw [hr₁, ← Category.assoc, hl₁]

/-- **The covers of a diagram of objects of the relative finite Hilbert category over an fpqc
covering family descend.** The diagram consists of objects `P i` over the members of the family,
objects `R i j` over the overlaps with cartesian base squares, and objects `T i j k` over the
triple overlaps making the cocycle triangle commute. The covers of the `P i` descend to a single
degree-`d` finite locally free cover of the base, compatibly with the diagram. -/
theorem exists_fpqc_cocone_of_diagram {U : BigFppfOver B S hS} {I : Type v}
    (P : I → Object B S hS 𝒳 𝒴 F d) (f : ∀ i, (P i).U ⟶ U)
    (hf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (P i).U)
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U))
    (R : I → I → Object B S hS 𝒳 𝒴 F d)
    (a : ∀ i j, R i j ⟶ P i) (b : ∀ i j, R i j ⟶ P j)
    (sq : ∀ i j, IsPullback (a i j).f (b i j).f (f i) (f j))
    (T : I → I → I → Object B S hS 𝒳 𝒴 F d)
    (c₁₂ : ∀ i j k, T i j k ⟶ R i j) (c₂₃ : ∀ i j k, T i j k ⟶ R j k)
    (c₁₃ : ∀ i j k, T i j k ⟶ R i k)
    (h₁ : ∀ i j k, c₁₂ i j k ≫ a i j = c₁₃ i j k ≫ a i k)
    (h₂ : ∀ i j k, c₁₂ i j k ≫ b i j = c₂₃ i j k ≫ a j k)
    (h₃ : ∀ i j k, c₂₃ i j k ≫ b j k = c₁₃ i j k ≫ b i k)
    (sq₃ : ∀ i j k, IsPullback (c₁₂ i j k).f ((c₂₃ i j k ≫ b j k).f)
      ((a i j).f ≫ f i) (f k)) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ (BigFppfOver.toScheme B S hS).obj U)
      (g : ∀ i, (BigFppfOver.toScheme B S hS).obj (P i).Z ⟶ Z),
      (∀ i, IsPullback (g i) ((BigFppfOver.toScheme B S hS).map (P i).q) q
        ((BigFppfOver.toScheme B S hS).map (f i))) ∧
      ∀ i j, (BigFppfOver.toScheme B S hS).map (a i j).g ≫ g i =
        (BigFppfOver.toScheme B S hS).map (b i j).g ≫ g j := by
  classical
  have := preservesPullbacks_bigFppfOverToScheme B S hS
  let H := BigFppfOver.toScheme B S hS
  let X (i : I) : Over (H.obj U) := Over.mk (H.map (f i))
  let Y (i : I) := sourceOver (P i) (f i)
  let qY (i : I) : Y i ⟶ X i :=
    structureMap (H.map (f i)) (Over.mk (H.map (P i).q))
  choose l r hl hr hp₂ hp₁ using fun i j => sourceOver_pair (f i) (f j) (a i j) (b i j) (sq i j)
  let φ (i j : I) : Y i ⨯ X j ≅ X i ⨯ Y j := (l i j).symm ≪≫ r i j
  have hlφ (i j : I) : (l i j).hom ≫ (φ i j).hom = (r i j).hom := by simp [φ]
  have hφ₁ (i j : I) : (φ i j).hom ≫ prod.fst = prod.fst ≫ qY i := by
    refine (cancel_epi (l i j).hom).mp ?_
    rw [← Category.assoc, hlφ]
    exact hp₁ i j
  have hφ₂ (i j : I) : (φ i j).hom ≫ prod.snd ≫ qY j = prod.snd := by
    refine (cancel_epi (l i j).hom).mp ?_
    rw [← Category.assoc, hlφ]
    exact (hp₂ i j).symm
  have hcocycle (i j k : I) : prod.map (φ i j).hom (𝟙 (X k)) ≫
      prodMapLastTwo (φ j k).hom = prodMapFirstThird (φ i k).hom := by
    let uT := (c₁₂ i j k).f ≫ (a i j).f ≫ f i
    have h23 : (c₂₃ i j k).f ≫ ((a j k).f ≫ f j) = uT := by
      show (c₂₃ i j k).f ≫ ((a j k).f ≫ f j) = (c₁₂ i j k).f ≫ (a i j).f ≫ f i
      rw [← Category.assoc, ← show (c₁₂ i j k).f ≫ (b i j).f =
        (c₂₃ i j k).f ≫ (a j k).f from congrArg Hom.f (h₂ i j k), Category.assoc, (sq i j).w]
    have h13 : (c₁₃ i j k).f ≫ ((a i k).f ≫ f i) = uT := by
      have hh := congrArg (fun z => z.f ≫ f i) (h₁ i j k).symm
      change ((c₁₃ i j k).f ≫ (a i k).f) ≫ f i = ((c₁₂ i j k).f ≫ (a i j).f) ≫ f i at hh
      simpa only [Category.assoc] using hh
    let m₁₂ := sourceOverMap (c₁₂ i j k) (f := uT) rfl
    let m₂₃ := sourceOverMap (c₂₃ i j k) h23
    let m₁₃ := sourceOverMap (c₁₃ i j k) h13
    let z₃ := sourceOverMap (c₂₃ i j k ≫ b j k) (f := uT) (sq₃ i j k).w.symm
    let p₃ := z₃ ≫ qY k
    have hsqT : IsPullback m₁₂.left p₃.left
        (sourceOver (R i j) ((a i j).f ≫ f i)).hom (H.map (f k)) :=
      isPullback_map_cover (c₁₂ i j k) (c₂₃ i j k ≫ b j k) (sq₃ i j k)
    obtain ⟨t₀, ht₁, ht₂⟩ := over_exists_product_iso m₁₂ p₃ hsqT
    let t := t₀ ≪≫ prod.mapIso (l i j) (Iso.refl (X k))
    let m := m₂₃ ≫ (l j k).hom
    let n := m₁₃ ≫ (l i k).hom
    have hm12 : m₁₂ ≫ sourceOverMap (a i j) rfl = m₁₃ ≫ sourceOverMap (a i k) rfl :=
      sourceOverMap_comp_eq _ _ _ _ (h₁ i j k) _ _ _ _
    have hm23 : m₁₂ ≫ sourceOverMap (b i j) (sq i j).w.symm =
        m₂₃ ≫ sourceOverMap (a j k) rfl :=
      sourceOverMap_comp_eq _ _ _ _ (h₂ i j k) _ _ _ _
    have hm3 : m₂₃ ≫ sourceOverMap (b j k) (sq j k).w.symm = z₃ :=
      Over.OverMorphism.ext (H.map_comp _ _).symm
    have hn3 : m₁₃ ≫ sourceOverMap (b i k) (sq i k).w.symm = z₃ :=
      (sourceOverMap_comp_eq _ _ _ _ (h₃ i j k).symm _ _ _ _).trans hm3
    have ht1 : t.hom ≫ prod.fst = m₁₂ ≫ (l i j).hom := by
      show (t₀.hom ≫ prod.map (l i j).hom (𝟙 (X k))) ≫ prod.fst = _
      rw [Category.assoc, prod.map_fst, ← Category.assoc, ht₁]
    have ht2 : t.hom ≫ prod.snd = p₃ := by
      show (t₀.hom ≫ prod.map (l i j).hom (𝟙 (X k))) ≫ prod.snd = _
      rw [Category.assoc, prod.map_snd, Category.comp_id, ht₂]
    have htphi : t.hom ≫ prod.fst ≫ (φ i j).hom = m₁₂ ≫ (r i j).hom := by
      rw [← Category.assoc, ht1, Category.assoc, hlφ]
    refine productTransition_cocycle (qY i) (qY j) (φ i j).hom (φ j k).hom (φ i k).hom
      (hφ₁ i j) (hφ₂ i j) (hφ₁ j k) (hφ₁ i k) t m n ?_ ?_ ?_ ?_ ?_
    · show (m₂₃ ≫ (l j k).hom) ≫ prod.fst = _
      rw [Category.assoc, hl, ← Category.assoc _ _ prod.snd, ← Category.assoc t.hom, htphi,
        Category.assoc, hr]
      exact hm23.symm
    · show (m₂₃ ≫ (l j k).hom) ≫ prod.snd = _
      rw [Category.assoc, hp₂, ← Category.assoc (r j k).hom, hr, ← Category.assoc, hm3, ht2]
    · show (m₁₃ ≫ (l i k).hom) ≫ prod.fst = _
      rw [Category.assoc, hl, ← Category.assoc _ _ prod.fst, ht1, Category.assoc, hl]
      exact hm12.symm
    · show (m₁₃ ≫ (l i k).hom) ≫ prod.snd = _
      rw [Category.assoc, hp₂, ← Category.assoc (r i k).hom, hr, ← Category.assoc, hn3, ht2]
    · show (m₂₃ ≫ (l j k).hom) ≫ (φ j k).hom ≫ prod.snd =
        (m₁₃ ≫ (l i k).hom) ≫ (φ i k).hom ≫ prod.snd
      rw [Category.assoc, Category.assoc, ← Category.assoc (l j k).hom,
        ← Category.assoc (l i k).hom, hlφ, hlφ, hr, hr]
      exact hm3.trans hn3.symm
  let E : DescentData (fun i => H.map (f i)) :=
    { obj i := Over.mk (H.map (P i).q)
      gluing i j := Over.isoMk (φ i j) (by
        show (φ i j).hom ≫ prod.map (𝟙 (X i)) (qY j) = prod.map (qY i) (𝟙 (X j))
        refine prod.hom_ext ?_ ?_
        · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc, Category.comp_id]
            using hφ₁ i j
        · simpa only [Category.assoc, prod.map_snd, prod.map_snd_assoc, Category.comp_id]
            using hφ₂ i j)
      cocycle := hcocycle }
  obtain ⟨Z, q, hq, g, hsq, hg⟩ := exists_scheme_cocone_of_isFiniteLocallyFreeOfRank
    (fun i => H.map (f i)) hf E d (fun i => (P i).finiteLocallyFree)
  refine ⟨Z, q, g, hsq, fun i j => ?_⟩
  have h' : (φ i j).hom.left ≫ (prod.snd : X i ⨯ Y j ⟶ Y j).left ≫ g j =
      (prod.fst : Y i ⨯ X j ⟶ Y i).left ≫ g i := by
    have h := hg i j
    simp only [Over.comp_left, Category.assoc] at h
    exact h.symm
  have hh := congrArg (fun z => (l i j).hom.left ≫ z) h'
  have hl' := congrArg Over.Hom.left (hl i j)
  have hr' := congrArg Over.Hom.left (hr i j)
  have he := congrArg Over.Hom.left (hlφ i j)
  dsimp only [Over.comp_left] at hl' hr' he
  rw [← Category.assoc (l i j).hom.left (φ i j).hom.left, he,
    ← Category.assoc (r i j).hom.left, hr', ← Category.assoc (l i j).hom.left, hl'] at hh
  exact hh.symm

end Diagram

end AlgebraicGeometry.Stack.FiniteHilbert

end

end
