module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveSheafify
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MainstreamRepresentability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type locally constant sheaves on a geometrically unibranch scheme are trivialized by
finite étale covers

Let `X` be an irreducible, geometrically unibranch scheme, `Λ` a ring and `F` a finite type
locally constant sheaf of `Λ`-modules on the small étale site of `X`. This file shows that `F`
becomes constant on a pointed Galois cover of `X`.

Every étale `X`-scheme is locally irreducible
(`AlgebraicGeometry.exists_isOpen_isPreirreducible_of_etale_of_isGeometricallyUnibranch`), and
over an irreducible étale `X`-scheme `T` the sections of a constant sheaf are the constants. Fix
a trivialization `ψ₀ : M̲ ≅ F|_{U₀}` over an affine étale `X`-scheme `U₀` lying over an affine
open of `X`. For an irreducible `T` with two maps `b₁, b₂ : T ⟶ U₀` the two trivializations
`ψ₀|_{b₁}, ψ₀|_{b₂}` of `F(T)` differ by an automorphism of `M`; these automorphisms form the
*monodromy set* `K`, which is finite because `U₀ ×_X U₀` is affine, hence a finite union of
irreducible opens.

The *monodromy torsor* `Q ⊆ Hom(M, F(-))` consists of the maps `M → F(W)` which, over every
irreducible `T` mapping to `W` and to `U₀`, are `ψ₀` up to an element of `K`. It is a finite
locally constant sheaf of sets, nonempty on irreducible objects over `U₀`.

## Main results

* `AlgebraicGeometry.exists_irreducible_refinement` — two étale `X`-schemes over a common base
  with points having a common image have a common irreducible refinement.
* `AlgebraicGeometry.finite_monodromySet` — the monodromy set is finite.
* `AlgebraicGeometry.isSheaf_monodromyTorsor` — the monodromy torsor is a sheaf.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Irreducible refinements -/

section Refinement

/-- An open subscheme of an étale `X`-scheme, as an étale `X`-scheme. -/
abbrev etaleOfOpens (W : X.Etale) (O : W.left.Opens) : X.Etale :=
  Scheme.Etale.mk (O.ι ≫ W.hom)

/-- The inclusion of an open subscheme of an étale `X`-scheme. -/
def etaleOfOpensι (W : X.Etale) (O : W.left.Opens) : etaleOfOpens W O ⟶ W :=
  MorphismProperty.Over.homMk O.ι rfl

/-- The underlying morphism of `etaleOfOpensι W O` is the open immersion `O.ι`. -/
@[simp]
theorem etaleOfOpensι_left (W : X.Etale) (O : W.left.Opens) :
    (etaleOfOpensι W O).left = O.ι :=
  rfl

/-- A morphism of the small étale site is étale. -/
instance etale_left {V W : X.Etale} (a : V ⟶ W) : Etale a.left :=
  MorphismProperty.of_postcomp @Etale (W' := @Etale) a.left W.hom (inferInstanceAs (Etale W.hom))
    ((MorphismProperty.Over.w a).symm ▸ inferInstanceAs (Etale V.hom))

variable [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)

include hX in
/-- **Every point of an étale `X`-scheme has an irreducible open neighbourhood.** -/
theorem exists_irreducible_opens (W : X.Etale) (w : W.left) :
    ∃ O : W.left.Opens, w ∈ O ∧ IrreducibleSpace O := by
  have : IrreducibleSpace ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (IrreducibleSpace X)
  obtain ⟨U, hU, hwU, hirr⟩ :=
    exists_isOpen_isPreirreducible_of_etale_of_isGeometricallyUnibranch (X := X) W.hom hX w
  exact ⟨⟨U, hU⟩, hwU, Subtype.irreducibleSpace ⟨⟨w, hwU⟩, hirr⟩⟩

include hX in
/-- **Common irreducible refinements.** Two étale `X`-schemes mapping to a common `X`-scheme `Z`,
one of them étale over `Z`, with points having a common image, have a common irreducible
refinement. -/
theorem exists_irreducible_refinement {T₁ T₂ : X.Etale} {Z : Scheme.{u}} (zX : Z ⟶ X)
    (a₁ : T₁.left ⟶ Z) (a₂ : T₂.left ⟶ Z) [Etale a₂] (h₁ : a₁ ≫ zX = T₁.hom)
    (h₂ : a₂ ≫ zX = T₂.hom) {t₁ : T₁.left} {t₂ : T₂.left} (ht : a₁.base t₁ = a₂.base t₂) :
    ∃ (S : X.Etale) (_ : IrreducibleSpace S.left) (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂),
      s₁.left ≫ a₁ = s₂.left ≫ a₂ := by
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback t₁ t₂ ht
  let P : X.Etale := Scheme.Etale.mk (pullback.fst a₁ a₂ ≫ T₁.hom)
  obtain ⟨O, -, hO⟩ := exists_irreducible_opens hX P p
  refine ⟨etaleOfOpens P O, hO, MorphismProperty.Over.homMk (O.ι ≫ pullback.fst a₁ a₂)
    (Category.assoc _ _ _), MorphismProperty.Over.homMk (O.ι ≫ pullback.snd a₁ a₂) ?_, ?_⟩
  · have e : pullback.snd a₁ a₂ ≫ T₂.hom = pullback.fst a₁ a₂ ≫ T₁.hom := by
      rw [← h₁, ← h₂, pullback.condition_assoc]
    exact (Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) e)
  · exact (Category.assoc _ _ _).trans ((congrArg (O.ι ≫ ·) pullback.condition).trans
      (Category.assoc _ _ _).symm)

omit [IrreducibleSpace X] hX in
/-- Two étale `X`-schemes over an irreducible one, both nonempty, have points with a common
image. -/
theorem exists_eq_of_irreducibleSpace {V T₁ T₂ : X.Etale} [IrreducibleSpace V.left]
    [Nonempty T₁.left] [Nonempty T₂.left] (a₁ : T₁ ⟶ V) (a₂ : T₂ ⟶ V) :
    ∃ (t₁ : T₁.left) (t₂ : T₂.left), a₁.left.base t₁ = a₂.left.base t₂ := by
  have ho₁ : IsOpen (Set.range a₁.left.base) := a₁.left.isOpenMap.isOpen_range
  have ho₂ : IsOpen (Set.range a₂.left.base) := a₂.left.isOpenMap.isOpen_range
  obtain ⟨v, -, ⟨t₁, rfl⟩, ⟨t₂, ht⟩⟩ := (IrreducibleSpace.isIrreducible_univ V.left).2 _ _
    ho₁ ho₂ ⟨_, trivial, Set.mem_range_self (Classical.arbitrary _)⟩
    ⟨_, trivial, Set.mem_range_self (Classical.arbitrary _)⟩
  exact ⟨t₁, t₂, ht.symm⟩

include hX in
/-- A covering sieve of a nonempty étale `X`-scheme contains an arrow out of an irreducible
étale `X`-scheme. -/
theorem exists_irreducible_mem_of_mem {T : X.Etale} [Nonempty T.left] {S : Sieve T}
    (hS : S ∈ X.smallEtaleTopology T) :
    ∃ (T' : X.Etale) (_ : IrreducibleSpace T'.left) (r : T' ⟶ T), S r := by
  have hcov : S ∈ X.smallEtaleTopology T := hS
  have h : Sieve.ofArrows (fun a : Σ W : X.Etale, {f : W ⟶ T // S f} ↦ a.1)
      (fun a ↦ a.2.1) = S := by
    refine le_antisymm ?_ fun W f hf ↦ ?_
    · rw [Sieve.generate_le_iff]
      rintro W f ⟨a⟩
      exact a.2.2
    · exact Sieve.ofArrows_mk _ _ (⟨W, f, hf⟩ : Σ W : X.Etale, {f : W ⟶ T // S f})
  rw [← h] at hcov
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 ((Scheme.ofArrows_mem_smallEtaleTopology_iff
    (fun a : Σ W : X.Etale, {f : W ⟶ T // S f} ↦ a.2.1)).1 hcov ▸
      Set.mem_univ (Classical.arbitrary T.left))
  obtain ⟨w, -⟩ := ha
  obtain ⟨O, -, hO⟩ := exists_irreducible_opens hX a.1 w
  exact ⟨etaleOfOpens a.1 O, hO, etaleOfOpensι a.1 O ≫ a.2.1, S.downward_closed a.2.2 _⟩

end Refinement

/-! ### Sections of a trivialized sheaf over irreducible objects -/

section Sections

variable {Λ : Type r} [Ring Λ] {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  {M : ModuleCat.{max (u + 1) r} Λ} {U : X.Etale}
  (e : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
    (X.smallEtaleTopology.overPullback _ U).obj F)

/-- The map `M → F(T)` given by a trivialization of `F` over `U` and a morphism `T ⟶ U`: the
constant sections followed by the trivialization. -/
def trivSection {T : X.Etale} (c : T ⟶ U) : M ⟶ F.obj.obj (op T) :=
  (toSheafify (X.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).app
    (op (Over.mk c)) ≫ e.hom.hom.app (op (Over.mk c))

/-- The map `trivSection e (r ≫ c)` is `trivSection e c` followed by restriction along `r`. -/
theorem trivSection_comp {T T' : X.Etale} (c : T ⟶ U) (r : T' ⟶ T) :
    trivSection e (r ≫ c) = trivSection e c ≫ F.obj.map r.op := by
  let m : Over.mk (r ≫ c) ⟶ Over.mk c := Over.homMk r rfl
  have h1 : (toSheafify (X.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).app
      (op (Over.mk (r ≫ c))) =
      (toSheafify (X.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).app
        (op (Over.mk c)) ≫
        ((constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) r} Λ)).obj
          M).obj.map m.op :=
    (Category.id_comp _).symm.trans
      ((toSheafify (X.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).naturality
        m.op)
  have h2 := e.hom.hom.naturality m.op
  have h3 := congrArg (fun k ↦ (toSheafify (X.smallEtaleTopology.over U)
    ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk c)) ≫ k) h2
  exact ((congrArg (· ≫ e.hom.hom.app (op (Over.mk (r ≫ c)))) h1).trans
    (Category.assoc _ _ _)).trans (h3.trans (Category.assoc _ _ _).symm)

/-- Over an irreducible object, the map given by a trivialization is bijective. -/
theorem bijective_trivSection {T : X.Etale} [IrreducibleSpace T.left] (c : T ⟶ U) :
    Function.Bijective (trivSection e c) := by
  have : IrreducibleSpace (Over.mk c).left.left := inferInstanceAs (IrreducibleSpace T.left)
  have h₁ := bijective_toSheafify_over_const_app Λ M (Over.mk c)
  have h₂ : Function.Bijective (e.hom.hom.app (op (Over.mk c))) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact h₂.comp h₁

/-- The trivialization over an irreducible object, as a linear equivalence. -/
def trivSectionEquiv {T : X.Etale} [IrreducibleSpace T.left] (c : T ⟶ U) :
    M ≃ₗ[Λ] F.obj.obj (op T) :=
  LinearEquiv.ofBijective (trivSection e c).hom (bijective_trivSection e c)

/-- The linear equivalence `trivSectionEquiv e c` acts as `trivSection e c`. -/
@[simp]
theorem trivSectionEquiv_apply {T : X.Etale} [IrreducibleSpace T.left] (c : T ⟶ U) (m : M) :
    trivSectionEquiv e c m = trivSection e c m :=
  rfl

/-- Restricting the inverse trivialization along a morphism of irreducible objects. -/
theorem trivSectionEquiv_symm_map {T T' : X.Etale} [IrreducibleSpace T.left]
    [IrreducibleSpace T'.left] (c : T ⟶ U) (r : T' ⟶ T) (y : F.obj.obj (op T)) :
    (trivSectionEquiv e (r ≫ c)).symm (F.obj.map r.op y) = (trivSectionEquiv e c).symm y := by
  apply (trivSectionEquiv e (r ≫ c)).injective
  rw [LinearEquiv.apply_symm_apply, trivSectionEquiv_apply, trivSection_comp, ModuleCat.comp_apply]
  congr 1
  exact ((trivSectionEquiv e c).apply_symm_apply y).symm

end Sections

/-! ### The monodromy set and the monodromy torsor -/

section Torsor

variable {Λ : Type r} [Ring Λ] {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  {M : ModuleCat.{max (u + 1) r} Λ} {U : X.Etale}
  (e : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
    (X.smallEtaleTopology.overPullback _ U).obj F)

/-- The automorphism of `M` comparing the trivializations of `F(T)` pulled back along two
morphisms `T ⟶ U`. -/
def monodromyElt {T : X.Etale} [IrreducibleSpace T.left] (b₁ b₂ : T ⟶ U) : M →ₗ[Λ] M :=
  (trivSectionEquiv e b₂).symm.toLinearMap ∘ₗ (trivSectionEquiv e b₁).toLinearMap

/-- The automorphism `monodromyElt e b₁ b₂` is unchanged by precomposing `b₁` and `b₂` with a
morphism of irreducible objects. -/
theorem monodromyElt_comp {T T' : X.Etale} [IrreducibleSpace T.left] [IrreducibleSpace T'.left]
    (b₁ b₂ : T ⟶ U) (r : T' ⟶ T) :
    monodromyElt e (r ≫ b₁) (r ≫ b₂) = monodromyElt e b₁ b₂ := by
  ext m
  change (trivSectionEquiv e (r ≫ b₂)).symm (trivSection e (r ≫ b₁) m) =
    (trivSectionEquiv e b₂).symm (trivSection e b₁ m)
  rw [trivSection_comp, ModuleCat.comp_apply, ← trivSectionEquiv_symm_map e b₂ r]

/-- **The monodromy set**: the automorphisms of `M` comparing two pullbacks of the
trivialization over irreducible objects. -/
def monodromySet : Set (M →ₗ[Λ] M) :=
  {k | ∃ (T : X.Etale) (_ : IrreducibleSpace T.left) (b₁ b₂ : T ⟶ U), k = monodromyElt e b₁ b₂}

/-- The endomorphism of `M` comparing a map `M → F(W)`, pulled back to an irreducible `T`,
with the trivialization pulled back along `T ⟶ U`. -/
def monodromyComparison {W T : X.Etale} [IrreducibleSpace T.left]
    (n : M ⟶ F.obj.obj (op W)) (a : T ⟶ W) (b : T ⟶ U) : M →ₗ[Λ] M :=
  (trivSectionEquiv e b).symm.toLinearMap ∘ₗ (n ≫ F.obj.map a.op).hom

/-- The endomorphism `monodromyComparison e n a b` is unchanged by precomposing `a` and `b` with a
morphism of irreducible objects. -/
theorem monodromyComparison_comp {W T T' : X.Etale} [IrreducibleSpace T.left]
    [IrreducibleSpace T'.left] (n : M ⟶ F.obj.obj (op W)) (a : T ⟶ W) (b : T ⟶ U)
    (r : T' ⟶ T) :
    monodromyComparison e n (r ≫ a) (r ≫ b) = monodromyComparison e n a b := by
  ext m
  change (trivSectionEquiv e (r ≫ b)).symm (F.obj.map (r ≫ a).op (n m)) =
    (trivSectionEquiv e b).symm (F.obj.map a.op (n m))
  rw [op_comp, Functor.map_comp, ModuleCat.comp_apply, trivSectionEquiv_symm_map]

/-- Comparing the restriction of `n` along `g` via `a` is comparing `n` via `a ≫ g`. -/
theorem monodromyComparison_map {W W' T : X.Etale} [IrreducibleSpace T.left]
    (n : M ⟶ F.obj.obj (op W)) (g : W' ⟶ W) (a : T ⟶ W') (b : T ⟶ U) :
    monodromyComparison e (n ≫ F.obj.map g.op) a b = monodromyComparison e n (a ≫ g) b := by
  ext m
  change (trivSectionEquiv e b).symm (F.obj.map a.op (F.obj.map g.op (n m))) =
    (trivSectionEquiv e b).symm (F.obj.map (a ≫ g).op (n m))
  rw [op_comp, Functor.map_comp, ModuleCat.comp_apply]

/-- **The monodromy torsor**: the maps `M → F(W)` which, over every irreducible `T` mapping to
`W` and to `U`, are the trivialization up to an element of the monodromy set. -/
def monodromyTorsor : Subfunctor (F.obj ⋙ coyoneda.obj (op M)) where
  obj W := {n | ∀ (T : X.Etale) (_ : IrreducibleSpace T.left) (a : T ⟶ W.unop) (b : T ⟶ U),
    monodromyComparison e n a b ∈ monodromySet e}
  map {W W'} g n hn T _ a b := by
    have h := hn T inferInstance (a ≫ g.unop) b
    rw [← monodromyComparison_map] at h
    exact h

variable [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)

include hX in
/-- **The monodromy torsor is a sheaf**: membership is tested on irreducible objects, which
refine every covering. -/
theorem isSheaf_monodromyTorsor :
    Presieve.IsSheaf X.smallEtaleTopology (monodromyTorsor e).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (F.property M)]
  intro W n hn T _ a b
  have : Nonempty T.left := inferInstance
  obtain ⟨T', _, r, hr⟩ := exists_irreducible_mem_of_mem hX
    (X.smallEtaleTopology.pullback_stable a hn)
  have h := hr T' inferInstance (𝟙 _) (r ≫ b)
  change monodromyComparison e (n ≫ F.obj.map (r ≫ a).op) (𝟙 T') (r ≫ b) ∈ monodromySet e at h
  rw [monodromyComparison_map, Category.id_comp, monodromyComparison_comp] at h
  exact h

include hX in
/-- **The monodromy set is finite** when `U` is affine and lies over an affine open `X₀` of `X`:
`U ×_{X₀} U` is affine, hence covered by finitely many irreducible opens, and every comparison
over an irreducible object is refined by one over one of these. -/
theorem finite_monodromySet [IsAffine U.left] (X₀ : X.affineOpens) (j : U.left ⟶ X₀.1)
    (hj : j ≫ X₀.1.ι = U.hom) : (monodromySet e).Finite := by
  have : IsAffine X₀.1 := X₀.2
  have : Etale j := MorphismProperty.of_postcomp @Etale (W' := @Etale) j X₀.1.ι
    (inferInstanceAs (Etale X₀.1.ι)) (hj.symm ▸ inferInstanceAs (Etale U.hom))
  let P := pullback j j
  let Pz : X.Etale := Scheme.Etale.mk (pullback.fst j j ≫ U.hom)
  let q₁ : Pz ⟶ U := MorphismProperty.Over.homMk (pullback.fst j j) rfl
  let q₂ : Pz ⟶ U := MorphismProperty.Over.homMk (pullback.snd j j) (by
    change pullback.snd j j ≫ U.hom = pullback.fst j j ≫ U.hom
    rw [← hj, pullback.condition_assoc])
  choose O hzO hO using fun z : Pz.left ↦ exists_irreducible_opens hX Pz z
  have : CompactSpace Pz.left := inferInstanceAs (CompactSpace P)
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set Pz.left)).elim_finite_subcover
    (fun z : Pz.left ↦ ((O z : Set Pz.left))) (fun z ↦ (O z).2)
    (fun z _ ↦ Set.mem_iUnion.2 ⟨z, hzO z⟩)
  let v : Pz.left → M →ₗ[Λ] M := fun z ↦ by
    have : IrreducibleSpace (etaleOfOpens Pz (O z)).left := hO z
    exact monodromyElt e (etaleOfOpensι Pz (O z) ≫ q₁) (etaleOfOpensι Pz (O z) ≫ q₂)
  refine (t.finite_toSet.image v).subset ?_
  rintro k ⟨T, hT, b₁, b₂, rfl⟩
  have hb : b₁.left ≫ j = b₂.left ≫ j := by
    rw [← cancel_mono X₀.1.ι, Category.assoc, Category.assoc, hj, MorphismProperty.Over.w b₁,
      MorphismProperty.Over.w b₂]
  let tm : T.left ⟶ P := pullback.lift b₁.left b₂.left hb
  have : Nonempty T.left := inferInstance
  let t₀ : T.left := Classical.arbitrary _
  obtain ⟨z, hz, hz₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (tm.base t₀)))
  have : IrreducibleSpace (etaleOfOpens Pz (O z)).left := hO z
  let t₂ : (etaleOfOpens Pz (O z)).left := (⟨tm.base t₀, hz₀⟩ : ↥(O z))
  let a₂ : (etaleOfOpens Pz (O z)).left ⟶ P := (O z).ι
  have : Etale a₂ := inferInstanceAs (Etale (O z).ι)
  obtain ⟨S, _, s₁, s₂, hs⟩ := exists_irreducible_refinement hX (T₁ := T)
    (T₂ := etaleOfOpens Pz (O z)) (pullback.fst j j ≫ U.hom) tm
    a₂ (by rw [pullback.lift_fst_assoc]; exact MorphismProperty.Over.w b₁) rfl
    (t₁ := t₀) (t₂ := t₂) rfl
  refine ⟨z, hz, ?_⟩
  have e₁ : s₁ ≫ b₁ = s₂ ≫ etaleOfOpensι Pz (O z) ≫ q₁ := by
    have h := congrArg (· ≫ pullback.fst j j) hs
    simp only [Category.assoc, tm, pullback.lift_fst] at h
    exact MorphismProperty.Over.Hom.ext h
  have e₂ : s₁ ≫ b₂ = s₂ ≫ etaleOfOpensι Pz (O z) ≫ q₂ := by
    have h := congrArg (· ≫ pullback.snd j j) hs
    simp only [Category.assoc, tm, pullback.lift_snd] at h
    exact MorphismProperty.Over.Hom.ext h
  change monodromyElt e (etaleOfOpensι Pz (O z) ≫ q₁) (etaleOfOpensι Pz (O z) ≫ q₂) =
    monodromyElt e b₁ b₂
  rw [← monodromyElt_comp e b₁ b₂ s₁, e₁, e₂, monodromyElt_comp e
    (etaleOfOpensι Pz (O z) ≫ q₁) (etaleOfOpensι Pz (O z) ≫ q₂) s₂]

end Torsor

/-! ### The monodromy torsor over irreducible objects -/

section TorsorSections

variable {Λ : Type r} [Ring Λ] {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  {M : ModuleCat.{max (u + 1) r} Λ} {U : X.Etale}
  (e : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
    (X.smallEtaleTopology.overPullback _ U).obj F)

/-- The sections of the monodromy torsor over `W`. -/
abbrev torsorSections (W : X.Etale) : Set (M ⟶ F.obj.obj (op W)) :=
  (monodromyTorsor e).obj (op W)

/-- The trivialization pulled back to an irreducible object over `U` is a section of the
monodromy torsor. -/
theorem trivSection_mem_torsorSections {Z : X.Etale} [IrreducibleSpace Z.left] (c : Z ⟶ U) :
    trivSection e c ∈ torsorSections e Z := by
  intro T _ a b
  refine ⟨T, inferInstance, a ≫ c, b, ?_⟩
  ext m
  change (trivSectionEquiv e b).symm (F.obj.map a.op (trivSection e c m)) =
    (trivSectionEquiv e b).symm (trivSection e (a ≫ c) m)
  rw [trivSection_comp, ModuleCat.comp_apply]

/-- Over an irreducible object over `U`, a section of the monodromy torsor is determined by its
comparison with the trivialization, which lies in the monodromy set. -/
theorem injective_torsorSections {Z : X.Etale} [IrreducibleSpace Z.left] (c : Z ⟶ U) :
    Function.Injective (fun n : torsorSections e Z ↦
      (⟨monodromyComparison e n.1 (𝟙 Z) c, n.2 Z inferInstance (𝟙 Z) c⟩ : monodromySet e)) := by
  intro n₁ n₂ h
  apply Subtype.ext
  ext m
  have h' := congrArg (fun k : monodromySet e ↦ trivSectionEquiv e c (k.1 m)) h
  simp only [monodromyComparison, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h'
  simpa using h'

variable [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)

include hX in
/-- **Over an irreducible object on which `F` is constant, restriction of sections of the
monodromy torsor to an irreducible object over it is bijective.** -/
theorem bijective_torsorSections_restrict {E : ModuleCat.{max (u + 1) r} Λ} {V : X.Etale}
    [IrreducibleSpace V.left]
    (eV : (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
      (X.smallEtaleTopology.overPullback _ V).obj F)
    {Z : X.Etale} [IrreducibleSpace Z.left] (r : Z ⟶ V) :
    Function.Bijective (fun n : torsorSections e V ↦
      (⟨n.1 ≫ F.obj.map r.op, (monodromyTorsor e).map r.op n.2⟩ : torsorSections e Z)) := by
  have hb := bijective_map_of_iso_constantSheaf eV r
  let ρ := LinearEquiv.ofBijective (F.obj.map r.op).hom hb
  refine ⟨fun n₁ n₂ h ↦ Subtype.ext (ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)),
    fun q ↦ ?_⟩
  · have h' := congrArg (fun k : torsorSections e Z ↦ k.1 m) h
    exact hb.1 h'
  · let n : M ⟶ F.obj.obj (op V) := ModuleCat.ofHom (ρ.symm.toLinearMap ∘ₗ q.1.hom)
    have hn : n ≫ F.obj.map r.op = q.1 := by
      ext m
      exact ρ.apply_symm_apply (q.1 m)
    refine ⟨⟨n, fun T _ a b ↦ ?_⟩, Subtype.ext hn⟩
    have : Nonempty T.left := inferInstance
    have : Nonempty Z.left := inferInstance
    obtain ⟨t, z, htz⟩ := exists_eq_of_irreducibleSpace a r
    obtain ⟨S, _, s₁, s₂, hs⟩ := exists_irreducible_refinement hX V.hom a.left r.left
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w r) htz
    have hs' : s₁ ≫ a = s₂ ≫ r := MorphismProperty.Over.Hom.ext hs
    rw [← monodromyComparison_comp e n a b s₁, hs', ← monodromyComparison_map, hn]
    exact q.2 S inferInstance s₂ (s₁ ≫ b)

omit [IrreducibleSpace X] hX in
/-- Over an irreducible object over `U`, the monodromy torsor has finitely many sections. -/
theorem finite_torsorSections (hK : (monodromySet e).Finite) {Z : X.Etale}
    [IrreducibleSpace Z.left] (c : Z ⟶ U) : Finite (torsorSections e Z) :=
  have := hK.to_subtype
  Finite.of_injective _ (injective_torsorSections e c)

include hX in
/-- Every irreducible étale `X`-scheme and `U` have a common irreducible refinement. -/
theorem exists_irreducible_over_both [Nonempty U.left] (V : X.Etale) [IrreducibleSpace V.left] :
    ∃ (Z : X.Etale) (_ : IrreducibleSpace Z.left) (_ : Z ⟶ V), Nonempty (Z ⟶ U) := by
  have : IrreducibleSpace (Scheme.Etale.mk (𝟙 X)).left := ‹IrreducibleSpace X›
  obtain ⟨v, w, hvw⟩ := exists_eq_of_irreducibleSpace (V := Scheme.Etale.mk (𝟙 X))
    (MorphismProperty.Over.homMk V.hom) (MorphismProperty.Over.homMk U.hom)
  obtain ⟨Z, hZ, s₁, s₂, -⟩ := exists_irreducible_refinement hX (𝟙 X) V.hom U.hom
    (Category.comp_id _) (Category.comp_id _) hvw
  exact ⟨Z, hZ, s₁, ⟨s₂⟩⟩

include hX in
/-- **Over an irreducible object on which `F` is constant, the monodromy torsor has finitely
many sections, and at least one.** -/
theorem finite_nonempty_torsorSections [Nonempty U.left] (hK : (monodromySet e).Finite)
    {E : ModuleCat.{max (u + 1) r} Λ} {V : X.Etale} [IrreducibleSpace V.left]
    (eV : (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
      (X.smallEtaleTopology.overPullback _ V).obj F) :
    Finite (torsorSections e V) ∧ Nonempty (torsorSections e V) := by
  obtain ⟨Z, _, r, ⟨c⟩⟩ := exists_irreducible_over_both hX V (U := U)
  have hb := bijective_torsorSections_restrict e hX eV r
  have := finite_torsorSections e hK c
  refine ⟨Finite.of_injective _ hb.1, ?_⟩
  obtain ⟨n, -⟩ := hb.2 ⟨trivSection e c, trivSection_mem_torsorSections e c⟩
  exact ⟨n⟩

variable (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F)

include hX hF in
/-- **Every point of an étale `X`-scheme lies in the image of an irreducible étale `X`-scheme on
which `F` is constant.** -/
theorem exists_irreducible_trivialization (W : X.Etale) (w : W.left) :
    ∃ (T : X.Etale) (_ : IrreducibleSpace T.left) (τ : T ⟶ W)
      (E : ModuleCat.{max (u + 1) r} Λ), Module.Finite Λ E ∧
      Nonempty ((constantSheaf (X.smallEtaleTopology.over T)
        (ModuleCat.{max (u + 1) r} Λ)).obj E ≅ (X.smallEtaleTopology.overPullback _ T).obj F) ∧
      w ∈ Set.range τ.left.base := by
  obtain ⟨I, V, f, hcov, htriv⟩ := hF W
  have hsurj := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).1 hcov
  obtain ⟨i, v, hv⟩ := Set.mem_iUnion.1 (hsurj ▸ Set.mem_univ w)
  obtain ⟨E, hE, ⟨eV⟩⟩ := htriv i
  obtain ⟨O, hvO, hO⟩ := exists_irreducible_opens hX (V i) v
  refine ⟨etaleOfOpens (V i) O, hO, etaleOfOpensι _ O ≫ f i, E, hE,
    ⟨Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap X.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ) (etaleOfOpensι _ O) F E eV⟩, ⟨⟨v, hvO⟩, ?_⟩⟩
  rw [← hv]
  rfl

end TorsorSections

/-- A morphism of presheaves on the slice at `V` is locally injective if two sections with the
same image are equal as soon as the underlying scheme has a point. -/
private theorem isLocallyInjective_over_of_forall {V : X.Etale} {D : Type*} [Category D]
    {FD : D → D → Type*} {CD : D → Type*} [∀ A B, FunLike (FD A B) (CD A) (CD B)]
    [ConcreteCategory D FD] {P Q : (Over V)ᵒᵖ ⥤ D} (φ : P ⟶ Q)
    (h : ∀ (T : (Over V)ᵒᵖ) (x y : ToType (P.obj T)), φ.app T x = φ.app T y →
      T.unop.left.left → x = y) :
    Presheaf.IsLocallyInjective (X.smallEtaleTopology.over V) φ := by
  refine ⟨fun {T} x y hxy ↦ ?_⟩
  by_cases hne : x = y
  · rw [hne, Presheaf.equalizerSieve_self_eq_top]
    exact GrothendieckTopology.top_mem _ _
  · rw [GrothendieckTopology.mem_over_iff]
    exact X.smallEtaleTopology.superset_covering bot_le
      (smallEtale_bot_mem X ⟨fun t ↦ hne (h T x y hxy t)⟩)

/-- A family of étale `X`-schemes over `W` whose images cover `W` generates a covering sieve. -/
private theorem ofArrows_mem_smallEtaleTopology_of_forall {W : X.Etale} {ι : Type*}
    (T : ι → X.Etale) (τ : ∀ i, T i ⟶ W) (hw : ∀ w : W.left, ∃ i, w ∈ Set.range (τ i).left.base) :
    Sieve.ofArrows T τ ∈ X.smallEtaleTopology W := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion.2 (hw w)

/-- A sieve is covering if every point of `W` lies in the image of an arrow `T ⟶ W` with `T`
satisfying `P`, and the sieve contains all such arrows. -/
private theorem mem_smallEtaleTopology_of_forall_exists {W : X.Etale} (S : Sieve W)
    (P : X.Etale → Prop)
    (hP : ∀ w : W.left, ∃ (T : X.Etale) (τ : T ⟶ W), P T ∧ w ∈ Set.range τ.left.base)
    (h : ∀ (T : X.Etale) (g : T ⟶ W), P T → S g) : S ∈ X.smallEtaleTopology W := by
  choose T τ hT hw using hP
  refine X.smallEtaleTopology.superset_covering (fun Y f hf ↦ ?_)
    (ofArrows_mem_smallEtaleTopology_of_forall T τ fun w ↦ ⟨w, hw w⟩)
  obtain ⟨w, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  exact S.downward_closed (h _ _ (hT w)) k

/-! ### The monodromy torsor as a finite locally constant sheaf of sets -/

section Shrink

variable {Λ : Type r} [Ring Λ] {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  {M : ModuleCat.{max (u + 1) r} Λ} {U : X.Etale}
  (e : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
    (X.smallEtaleTopology.overPullback _ U).obj F)
  [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F)
  (hK : (monodromySet e).Finite) [Nonempty U.left]

include hX hF hK in
/-- The sections of the monodromy torsor form a small type: they are determined by their
restrictions to irreducible objects on which `F` is constant, where there are finitely many. -/
theorem small_torsorSections (W : X.Etale) : Small.{u + 1} (torsorSections e W) := by
  choose T hT τ E hE heV hw using exists_irreducible_trivialization hX hF W
  have hfin : ∀ w, Finite (torsorSections e (T w)) := fun w ↦ by
    have := hT w
    exact (finite_nonempty_torsorSections e hX hK (heV w).some).1
  let Φ : torsorSections e W → ∀ w, torsorSections e (T w) := fun n w ↦
    ⟨n.1 ≫ F.obj.map (τ w).op, (monodromyTorsor e).map (τ w).op n.2⟩
  have hcov := ofArrows_mem_smallEtaleTopology_of_forall T τ fun w ↦ ⟨w, hw w⟩
  have hinj : Function.Injective Φ := by
    intro n₁ n₂ h
    apply Subtype.ext
    refine (F.property M _ hcov).isSeparatedFor.ext fun Y g hg ↦ ?_
    obtain ⟨w, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    have h' := congrArg (fun φ ↦ (φ w).1) h
    change n₁.1 ≫ F.obj.map (k ≫ τ w).op = n₂.1 ≫ F.obj.map (k ≫ τ w).op
    rw [op_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ F.obj.map k.op) h'
  exact small_of_injective hinj

/-- The monodromy torsor, shrunk to the universe of sheaves of sets of the small étale site. -/
def shrunkTorsor : (X.Etale)ᵒᵖ ⥤ Type (u + 1) :=
  have : FunctorToTypes.Small.{u + 1} (monodromyTorsor e).toFunctor :=
    fun W ↦ small_torsorSections e hX hF hK W.unop
  FunctorToTypes.shrink.{u + 1} (monodromyTorsor e).toFunctor

/-- The sections of the shrunk monodromy torsor are the sections of the monodromy torsor. -/
def shrunkTorsorEquiv (W : X.Etale) :
    (shrunkTorsor e hX hF hK).obj (op W) ≃ torsorSections e W :=
  have : Small.{u + 1} ((monodromyTorsor e).toFunctor.obj (op W)) :=
    small_torsorSections e hX hF hK W
  (equivShrink.{u + 1} ((monodromyTorsor e).toFunctor.obj (op W))).symm

/-- Under `shrunkTorsorEquiv`, restriction in the shrunk monodromy torsor along `g` is
postcomposition with `F.obj.map g.op`. -/
theorem shrunkTorsor_map_equiv {W W' : X.Etale} (g : W' ⟶ W)
    (x : (shrunkTorsor e hX hF hK).obj (op W)) :
    (shrunkTorsorEquiv e hX hF hK W' ((shrunkTorsor e hX hF hK).map g.op x)).1 =
      (shrunkTorsorEquiv e hX hF hK W x).1 ≫ F.obj.map g.op := by
  have : FunctorToTypes.Small.{u + 1} (monodromyTorsor e).toFunctor :=
    fun W ↦ small_torsorSections e hX hF hK W.unop
  have h : (shrunkTorsor e hX hF hK).map g.op x = equivShrink.{u + 1} _
      ((monodromyTorsor e).toFunctor.map g.op ((equivShrink.{u + 1} _).symm x)) := rfl
  rw [h]
  have : Small.{u + 1} ((monodromyTorsor e).toFunctor.obj (op W')) :=
    small_torsorSections e hX hF hK W'
  exact congrArg Subtype.val (Equiv.symm_apply_apply
    (equivShrink.{u + 1} ((monodromyTorsor e).toFunctor.obj (op W'))) _)

/-- Two sections of the shrunk monodromy torsor over `V` are equal if their images in `F` agree
after restriction along `r`, provided restriction of sections of the monodromy torsor along `r`
is injective. -/
theorem shrunkTorsorEquiv_injective_restrict {V Z : X.Etale} (r : Z ⟶ V)
    {x y : (shrunkTorsor e hX hF hK).obj (op V)}
    (h : (shrunkTorsorEquiv e hX hF hK V x).1 ≫ F.obj.map r.op =
      (shrunkTorsorEquiv e hX hF hK V y).1 ≫ F.obj.map r.op)
    (hr : Function.Injective (fun n : torsorSections e V ↦
      (⟨n.1 ≫ F.obj.map r.op, (monodromyTorsor e).map r.op n.2⟩ : torsorSections e Z))) :
    x = y :=
  (shrunkTorsorEquiv e hX hF hK V).injective (hr (Subtype.ext h))

include hX in
omit hF hK [Nonempty U.left] in
/-- A sieve containing every arrow out of an irreducible étale `X`-scheme is covering. -/
theorem mem_smallEtaleTopology_of_irreducible {W : X.Etale} (S : Sieve W)
    (h : ∀ (Z : X.Etale) (_ : IrreducibleSpace Z.left) (g : Z ⟶ W), S g) :
    S ∈ X.smallEtaleTopology W := by
  refine mem_smallEtaleTopology_of_forall_exists S (fun Z ↦ IrreducibleSpace Z.left)
    (fun w ↦ ?_) fun Z g hZ ↦ h Z hZ g
  obtain ⟨O, hwO, hO⟩ := exists_irreducible_opens hX W w
  exact ⟨etaleOfOpens W O, etaleOfOpensι W O, hO, ⟨w, hwO⟩, rfl⟩

/-- The shrunk monodromy torsor is a sheaf. -/
theorem isSheaf_shrunkTorsor :
    Presieve.IsSheaf X.smallEtaleTopology (shrunkTorsor e hX hF hK) := by
  let i : (monodromyTorsor e).toFunctor ⋙ uliftFunctor.{u + 1} ≅
      shrunkTorsor e hX hF hK ⋙ uliftFunctor.{max (u + 1) r} :=
    NatIso.ofComponents (fun W ↦ Equiv.toIso (Equiv.ulift.trans
      ((shrunkTorsorEquiv e hX hF hK W.unop).symm.trans Equiv.ulift.symm))) (by
      intro W W' g
      ext ⟨q⟩
      apply ULift.ext
      apply (shrunkTorsorEquiv e hX hF hK W'.unop).injective
      apply Subtype.ext
      change (shrunkTorsorEquiv e hX hF hK W'.unop ((shrunkTorsorEquiv e hX hF hK W'.unop).symm
          ((monodromyTorsor e).toFunctor.map g q))).1 =
        (shrunkTorsorEquiv e hX hF hK W'.unop ((shrunkTorsor e hX hF hK).map g.unop.op
          ((shrunkTorsorEquiv e hX hF hK W.unop).symm q))).1
      rw [shrunkTorsor_map_equiv]
      refine (congrArg Subtype.val (Equiv.apply_symm_apply _ _)).trans ?_
      refine Eq.trans ?_ (congrArg (fun k : torsorSections e W.unop ↦ k.1 ≫ F.obj.map g.unop.op)
        (Equiv.apply_symm_apply (shrunkTorsorEquiv e hX hF hK W.unop) q).symm)
      rfl)
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 (Presieve.isSheaf_iso _ i
    (Presieve.isSheaf_comp_uliftFunctor _ (isSheaf_monodromyTorsor e hX)))

/-- The shrunk monodromy torsor, as a sheaf of sets. -/
abbrev shrunkTorsorSheaf : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ⟨shrunkTorsor e hX hF hK,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_shrunkTorsor e hX hF hK)⟩

/-- The restriction maps from the sections over `V`, as a map from the constant presheaf on the
slice at `V`. -/
def shrunkTorsorConstMap (V : X.Etale) :
    (Functor.const (Over V)ᵒᵖ).obj ((shrunkTorsor e hX hF hK).obj (op V)) ⟶
      (Over.forget V).op ⋙ shrunkTorsor e hX hF hK where
  app T := (shrunkTorsor e hX hF hK).map T.unop.hom.op
  naturality T T' k := by
    change (shrunkTorsor e hX hF hK).map T'.unop.hom.op =
      (shrunkTorsor e hX hF hK).map T.unop.hom.op ≫
        (shrunkTorsor e hX hF hK).map k.unop.left.op
    rw [← Functor.map_comp, ← op_comp, Over.w k.unop]

/-- Restriction of the shrunk torsor along a composite, read through the identification with the
monodromy torsor. -/
theorem shrunkTorsorEquiv_map_map {V W Z : X.Etale} (a : W ⟶ V) (g : Z ⟶ W)
    (x : (shrunkTorsor e hX hF hK).obj (op V)) :
    (shrunkTorsorEquiv e hX hF hK Z ((shrunkTorsor e hX hF hK).map g.op
      ((shrunkTorsor e hX hF hK).map a.op x))).1 =
      (shrunkTorsorEquiv e hX hF hK V x).1 ≫ F.obj.map (g ≫ a).op := by
  rw [shrunkTorsor_map_equiv, shrunkTorsor_map_equiv, Category.assoc, ← Functor.map_comp,
    ← op_comp]

variable {E : ModuleCat.{max (u + 1) r} Λ} {V : X.Etale} [IrreducibleSpace V.left]
  (eV : (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
    (X.smallEtaleTopology.overPullback _ V).obj F)

include eV

/-- Over an irreducible object `V` on which `F` is constant, the map `shrunkTorsorConstMap` is
locally injective. -/
theorem isLocallyInjective_shrunkTorsorConstMap :
    Presheaf.IsLocallyInjective (X.smallEtaleTopology.over V)
      (shrunkTorsorConstMap e hX hF hK V) := by
  refine isLocallyInjective_over_of_forall _ fun T x y h t ↦ ?_
  obtain ⟨O, -, hO⟩ := exists_irreducible_opens hX T.unop.left t
  have : IrreducibleSpace (etaleOfOpens T.unop.left O).left := hO
  let r := etaleOfOpensι T.unop.left O ≫ T.unop.hom
  refine shrunkTorsorEquiv_injective_restrict e hX hF hK r ?_
    (bijective_torsorSections_restrict e hX eV r).1
  have h' := congrArg (fun z ↦ (shrunkTorsorEquiv e hX hF hK _
    ((shrunkTorsor e hX hF hK).map (etaleOfOpensι T.unop.left O).op z)).1) h
  change (shrunkTorsorEquiv e hX hF hK _ ((shrunkTorsor e hX hF hK).map
      (etaleOfOpensι T.unop.left O).op ((shrunkTorsor e hX hF hK).map T.unop.hom.op x))).1 =
    (shrunkTorsorEquiv e hX hF hK _ ((shrunkTorsor e hX hF hK).map
      (etaleOfOpensι T.unop.left O).op ((shrunkTorsor e hX hF hK).map T.unop.hom.op y))).1 at h'
  rw [shrunkTorsorEquiv_map_map, shrunkTorsorEquiv_map_map] at h'
  exact h'

/-- Over an irreducible object `V` on which `F` is constant, the map `shrunkTorsorConstMap` is
locally surjective. -/
theorem isLocallySurjective_shrunkTorsorConstMap :
    Presheaf.IsLocallySurjective (X.smallEtaleTopology.over V)
      (shrunkTorsorConstMap e hX hF hK V) := by
  refine ⟨fun {T} q ↦ ?_⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine mem_smallEtaleTopology_of_irreducible hX _ fun Z _ g ↦ ?_
  rw [Sieve.overEquiv_iff]
  obtain ⟨n, hn⟩ := (bijective_torsorSections_restrict e hX eV (g ≫ T.hom)).2
    (shrunkTorsorEquiv e hX hF hK Z ((shrunkTorsor e hX hF hK).map g.op q))
  refine ⟨(shrunkTorsorEquiv e hX hF hK V).symm n, ?_⟩
  apply (shrunkTorsorEquiv e hX hF hK Z).injective
  apply Subtype.ext
  change (shrunkTorsorEquiv e hX hF hK Z ((shrunkTorsor e hX hF hK).map (g ≫ T.hom).op
    ((shrunkTorsorEquiv e hX hF hK V).symm n))).1 =
      (shrunkTorsorEquiv e hX hF hK Z ((shrunkTorsor e hX hF hK).map g.op q)).1
  rw [shrunkTorsor_map_equiv, Equiv.apply_symm_apply]
  exact congrArg Subtype.val hn

/-- **The shrunk monodromy torsor is constant over an irreducible object on which `F` is
constant**, with value its sections there. -/
def shrunkTorsorConstIso :
    (constantSheaf (X.smallEtaleTopology.over V) (Type (u + 1))).obj
        ((shrunkTorsor e hX hF hK).obj (op V)) ≅
      (X.smallEtaleTopology.overPullback (Type (u + 1)) V).obj (shrunkTorsorSheaf e hX hF hK) :=
  Stacks.ConstantSheaf.presheafToSheafObjIso (X.smallEtaleTopology.over V)
    (shrunkTorsorConstMap e hX hF hK V) (isLocallyInjective_shrunkTorsorConstMap e hX hF hK eV)
    (isLocallySurjective_shrunkTorsorConstMap e hX hF hK eV)

omit [IrreducibleSpace V.left] in
omit eV in
/-- **The shrunk monodromy torsor is a finite locally constant sheaf of sets.** -/
theorem isFiniteLocallyConstant_shrunkTorsorSheaf :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology
      (shrunkTorsorSheaf e hX hF hK) := by
  refine ⟨fun W ↦ ?_⟩
  choose T hT τ E' hE' heV hw using exists_irreducible_trivialization hX hF W
  refine ⟨ULift.{u + 1} W.left, fun w ↦ T w.down, fun w ↦ τ w.down, ?_, fun w ↦ ?_⟩
  · exact ofArrows_mem_smallEtaleTopology_of_forall _ _ fun x ↦ ⟨⟨x⟩, hw x⟩
  · have := hT w.down
    have hfin := (finite_nonempty_torsorSections e hX hK (heV w.down).some).1
    exact ⟨(shrunkTorsor e hX hF hK).obj (op (T w.down)),
      Finite.of_equiv _ (shrunkTorsorEquiv e hX hF hK (T w.down)).symm,
      ⟨shrunkTorsorConstIso e hX hF hK (heV w.down).some⟩⟩

end Shrink

/-! ### A section of the monodromy torsor trivializes `F` -/

section Trivialize

variable {Λ : Type r} [Ring Λ] {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  {M : ModuleCat.{max (u + 1) r} Λ} {U : X.Etale}
  (e : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
    (X.smallEtaleTopology.overPullback _ U).obj F)
  [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F)
  [Nonempty U.left]

omit [IrreducibleSpace X] [Nonempty U.left] in
/-- Every element of the monodromy set is bijective. -/
theorem bijective_of_mem_monodromySet {k : M →ₗ[Λ] M} (hk : k ∈ monodromySet e) :
    Function.Bijective k := by
  obtain ⟨T, _, b₁, b₂, rfl⟩ := hk
  exact ((trivSectionEquiv e b₂).symm.toEquiv.bijective).comp
    (trivSectionEquiv e b₁).toEquiv.bijective

include hX in
/-- **A section of the monodromy torsor restricts bijectively to every irreducible object on
which `F` is constant.** -/
theorem bijective_of_mem_torsorSections {W : X.Etale} {n : M ⟶ F.obj.obj (op W)}
    (hn : n ∈ torsorSections e W) {E : ModuleCat.{max (u + 1) r} Λ} {Z : X.Etale}
    [IrreducibleSpace Z.left]
    (eZ : (constantSheaf (X.smallEtaleTopology.over Z) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
      (X.smallEtaleTopology.overPullback _ Z).obj F) (r : Z ⟶ W) :
    Function.Bijective (n ≫ F.obj.map r.op) := by
  obtain ⟨Z', _, s, ⟨c⟩⟩ := exists_irreducible_over_both hX Z (U := U)
  have hs := bijective_map_of_iso_constantSheaf eZ s
  have hk := bijective_of_mem_monodromySet e (hn Z' inferInstance (s ≫ r) c)
  have h : ⇑(F.obj.map s.op) ∘ ⇑(n ≫ F.obj.map r.op) =
      ⇑(trivSectionEquiv e c) ∘ ⇑(monodromyComparison e n (s ≫ r) c) := by
    funext m
    change F.obj.map s.op (F.obj.map r.op (n m)) =
      trivSectionEquiv e c ((trivSectionEquiv e c).symm (F.obj.map (s ≫ r).op (n m)))
    rw [LinearEquiv.apply_symm_apply, op_comp, Functor.map_comp, ModuleCat.comp_apply]
  have h2 : Function.Bijective (⇑(F.obj.map s.op) ∘ ⇑(n ≫ F.obj.map r.op)) := by
    rw [h]
    exact (trivSectionEquiv e c).toEquiv.bijective.comp hk
  exact (Function.Bijective.of_comp_iff' hs _).1 h2

include hX hF in
/-- A sieve containing every arrow out of an irreducible étale `X`-scheme on which `F` is
constant is covering. -/
theorem mem_smallEtaleTopology_of_irreducible_trivialization {W : X.Etale} (S : Sieve W)
    (h : ∀ (Z : X.Etale) (_ : IrreducibleSpace Z.left) (E : ModuleCat.{max (u + 1) r} Λ)
      (_ : (constantSheaf (X.smallEtaleTopology.over Z) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
        (X.smallEtaleTopology.overPullback _ Z).obj F) (g : Z ⟶ W), S g) :
    S ∈ X.smallEtaleTopology W := by
  refine mem_smallEtaleTopology_of_forall_exists S
    (fun Z ↦ ∃ (_ : IrreducibleSpace Z.left) (E : ModuleCat.{max (u + 1) r} Λ),
      Nonempty ((constantSheaf (X.smallEtaleTopology.over Z)
        (ModuleCat.{max (u + 1) r} Λ)).obj E ≅ (X.smallEtaleTopology.overPullback _ Z).obj F))
    (fun w ↦ ?_) fun Z g ⟨hZ, E, ⟨eZ⟩⟩ ↦ h Z hZ E eZ g
  obtain ⟨T, hT, τ, E, -, heV, hw⟩ := exists_irreducible_trivialization hX hF W w
  exact ⟨T, τ, ⟨hT, E, heV⟩, hw⟩

/-- The map from the constant presheaf on the slice at `W` defined by a map `M → F(W)`. -/
def constMapOfSection {W : X.Etale} (n : M ⟶ F.obj.obj (op W)) :
    (Functor.const (Over W)ᵒᵖ).obj M ⟶
      ((X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) r} Λ) W).obj F).obj where
  app T := n ≫ F.obj.map T.unop.hom.op
  naturality T T' k := by
    change 𝟙 M ≫ n ≫ F.obj.map T'.unop.hom.op =
      (n ≫ F.obj.map T.unop.hom.op) ≫ F.obj.map k.unop.left.op
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp, ← op_comp, Over.w k.unop]

omit [Nonempty U.left] in
include hX hF in
/-- If `n : M → F(W)` restricts bijectively to every irreducible object on which `F` is constant,
then `constMapOfSection n` is locally injective. -/
theorem isLocallyInjective_constMapOfSection {W : X.Etale} {n : M ⟶ F.obj.obj (op W)}
    (hbij : ∀ (Z : X.Etale) (_ : IrreducibleSpace Z.left) (E : ModuleCat.{max (u + 1) r} Λ)
      (_ : (constantSheaf (X.smallEtaleTopology.over Z) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
        (X.smallEtaleTopology.overPullback _ Z).obj F) (r : Z ⟶ W),
        Function.Bijective (n ≫ F.obj.map r.op)) :
    Presheaf.IsLocallyInjective (X.smallEtaleTopology.over W) (constMapOfSection n) := by
  refine isLocallyInjective_over_of_forall _ fun T x y h t ↦ ?_
  obtain ⟨Z, hZ, τ, E, -, ⟨eZ⟩, -⟩ := exists_irreducible_trivialization hX hF T.unop.left t
  refine (hbij Z hZ E eZ (τ ≫ T.unop.hom)).1 ?_
  have h' := congrArg (F.obj.map τ.op) h
  change F.obj.map τ.op (F.obj.map T.unop.hom.op (n x)) =
    F.obj.map τ.op (F.obj.map T.unop.hom.op (n y)) at h'
  change F.obj.map (τ ≫ T.unop.hom).op (n x) = F.obj.map (τ ≫ T.unop.hom).op (n y)
  rw [op_comp, Functor.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply]
  exact h'

omit [Nonempty U.left] in
include hX hF in
/-- If `n : M → F(W)` restricts bijectively to every irreducible object on which `F` is constant,
then `constMapOfSection n` is locally surjective. -/
theorem isLocallySurjective_constMapOfSection {W : X.Etale} {n : M ⟶ F.obj.obj (op W)}
    (hbij : ∀ (Z : X.Etale) (_ : IrreducibleSpace Z.left) (E : ModuleCat.{max (u + 1) r} Λ)
      (_ : (constantSheaf (X.smallEtaleTopology.over Z) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
        (X.smallEtaleTopology.overPullback _ Z).obj F) (r : Z ⟶ W),
        Function.Bijective (n ≫ F.obj.map r.op)) :
    Presheaf.IsLocallySurjective (X.smallEtaleTopology.over W) (constMapOfSection n) := by
  refine ⟨fun {T} q ↦ ?_⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine mem_smallEtaleTopology_of_irreducible_trivialization hX hF _ fun Z hZ E eZ g ↦ ?_
  rw [Sieve.overEquiv_iff]
  obtain ⟨m, hm⟩ := (hbij Z hZ E eZ (g ≫ T.hom)).2 (F.obj.map g.op q)
  exact ⟨m, hm⟩

include hX hF in
/-- **A section of the monodromy torsor over `W` trivializes `F` over `W`.** -/
theorem nonempty_iso_of_mem_torsorSections {W : X.Etale} {n : M ⟶ F.obj.obj (op W)}
    (hn : n ∈ torsorSections e W) :
    Nonempty ((constantSheaf (X.smallEtaleTopology.over W) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      (X.smallEtaleTopology.overPullback _ W).obj F) := by
  have hbij : ∀ (Z : X.Etale) (_ : IrreducibleSpace Z.left) (E : ModuleCat.{max (u + 1) r} Λ)
      (_ : (constantSheaf (X.smallEtaleTopology.over Z) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
        (X.smallEtaleTopology.overPullback _ Z).obj F) (r : Z ⟶ W),
        Function.Bijective (n ≫ F.obj.map r.op) :=
    fun Z _ E eZ r ↦ bijective_of_mem_torsorSections e hX hn eZ r
  have : (X.smallEtaleTopology.over W).WEqualsLocallyBijective (ModuleCat.{max (u + 1) r} Λ) :=
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, max (u + 1) r} _ Λ
  let α : (constantSheaf (X.smallEtaleTopology.over W) (ModuleCat.{max (u + 1) r} Λ)).obj M ⟶
      (X.smallEtaleTopology.overPullback _ W).obj F :=
    ⟨sheafifyLift (X.smallEtaleTopology.over W) (constMapOfSection n)
      ((X.smallEtaleTopology.overPullback _ W).obj F).property⟩
  have : IsIso α := Presheaf.isIso_of_toSheafify_comp_eq_of_isLocallyBijective _
    (constMapOfSection n) α (toSheafify_sheafifyLift _ _ _)
    (isLocallyInjective_constMapOfSection hX hF hbij)
    (isLocallySurjective_constMapOfSection hX hF hbij)
  exact ⟨asIso α⟩

end Trivialize

/-! ### Finite type locally constant sheaves are trivialized by pointed Galois covers -/

section Main

variable [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X) {Λ : Type r} [Ring Λ]
  {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F)

include hX hF in
/-- `F` is trivialized, with finitely generated value, over a nonempty affine étale `X`-scheme
lying over an affine open of `X`. -/
theorem exists_affine_trivialization :
    ∃ (U : X.Etale) (_ : IsAffine U.left) (_ : Nonempty U.left) (X₀ : X.affineOpens)
      (j : U.left ⟶ X₀.1) (_ : j ≫ X₀.1.ι = U.hom) (M : ModuleCat.{max (u + 1) r} Λ),
      Module.Finite Λ M ∧ Nonempty ((constantSheaf (X.smallEtaleTopology.over U)
        (ModuleCat.{max (u + 1) r} Λ)).obj M ≅ (X.smallEtaleTopology.overPullback _ U).obj F) := by
  have : Nonempty X := inferInstance
  let x₀ : X := Classical.arbitrary X
  obtain ⟨T, _, τ, E, hE, ⟨eT⟩, t, ht⟩ :=
    exists_irreducible_trivialization hX hF (Scheme.Etale.mk (𝟙 X)) x₀
  have hTt : T.hom.base t = x₀ := by
    rw [← ht, ← MorphismProperty.Over.w τ]
    rfl
  obtain ⟨X₀, hX₀, hx₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x₀) (U := ⊤)
    (by simp)
  obtain ⟨U', hU', htU', hU'le⟩ := exists_isAffineOpen_mem_and_subset (X := T.left) (x := t)
    (U := T.hom ⁻¹ᵁ X₀) (by rw [Scheme.Hom.mem_preimage, hTt]; exact hx₀)
  have : IsAffine U' := hU'
  let U := etaleOfOpens T U'
  have hrange : Set.range U.hom.base ⊆ Set.range X₀.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU'le y.2
  refine ⟨U, hU', ⟨⟨t, htU'⟩⟩, ⟨X₀, hX₀⟩, IsOpenImmersion.lift X₀.ι U.hom hrange,
    IsOpenImmersion.lift_fac _ _ _, E, hE,
    ⟨Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap X.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ) (etaleOfOpensι T U') F E eT⟩⟩

include hX hF in
/-- **`F` is trivialized by a finite étale `X`-scheme with nonempty source.** The monodromy
torsor is a finite locally constant sheaf of sets, hence represented by a finite étale
`X`-scheme `Y` (Tag 03RV, read on the small étale site of Tag 021B); its universal section is
a section of the torsor over `Y`, which trivializes `F` there. -/
@[sga "4½ Th_finitude 2.2" "Clause (c)"]
theorem exists_finiteEtale_trivialization :
    ∃ (Y : X.Etale) (_ : IsFinite Y.hom) (_ : Nonempty Y.left)
      (M : ModuleCat.{max (u + 1) r} Λ), Module.Finite Λ M ∧
      Nonempty ((constantSheaf (X.smallEtaleTopology.over Y)
        (ModuleCat.{max (u + 1) r} Λ)).obj M ≅ (X.smallEtaleTopology.overPullback _ Y).obj F) := by
  obtain ⟨U, _, hU, X₀, j, hj, M, hM, ⟨e⟩⟩ := exists_affine_trivialization hX hF
  have hK := finite_monodromySet e hX X₀ j hj
  have := isFiniteLocallyConstant_shrunkTorsorSheaf e hX hF hK
  let B := BigEtaleSite.containing X
  have hXB : B.Contains X := BigEtaleSite.contains_containing X
  let G := SmallEtale.toEtaleSite B X hXB
  let QB := (G.sheafPushforwardContinuous (Type (u + 1)) (SmallEtale.topology B X hXB)
    X.smallEtaleTopology).obj (shrunkTorsorSheaf e hX hF hK)
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X hXB) QB :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPushforwardContinuous _ _ G _
  obtain ⟨V, hVfin, ⟨φ⟩⟩ :=
    (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable B ⟨X, hXB⟩
      QB).1 this
  let ψ := φ ≪≫ ((Sheaf.uliftYonedaIsoSheafifiedYoneda (SmallEtale.topology B X hXB)).app V).symm
  let ξ : QB.obj.obj (op V) := ψ.inv.hom.app (op V) (ULift.up (𝟙 V))
  let n := shrunkTorsorEquiv e hX hF hK (G.obj V) ξ
  obtain ⟨eY⟩ := nonempty_iso_of_mem_torsorSections e hX hF n.2
  obtain ⟨O, hu₀, hO⟩ := exists_irreducible_opens hX U (Classical.arbitrary U.left)
  have : IrreducibleSpace (etaleOfOpens U O).left := hO
  let c := etaleOfOpensι U O
  obtain ⟨W, g, w₀, hw₀⟩ := SmallEtale.exists_obj_mem_range B X hXB (etaleOfOpens U O)
    (⟨Classical.arbitrary U.left, hu₀⟩ : ↥O)
  let qW : torsorSections e (G.obj W) := ⟨trivSection e c ≫ F.obj.map g.op,
    (monodromyTorsor e).map g.op (trivSection_mem_torsorSections e c)⟩
  let h : W ⟶ V := (ψ.hom.hom.app (op W) ((shrunkTorsorEquiv e hX hF hK (G.obj W)).symm qW)).down
  exact ⟨G.obj V, hVfin, ⟨(G.map h).left.base w₀⟩, M, hM, ⟨eY⟩⟩

end Main

/-- **Every finite type locally constant sheaf of `Λ`-modules on an irreducible, geometrically
unibranch scheme is trivialized, with finitely generated value, by a pointed Galois cover.** A
Galois object of `FÉt_X` dominating the finite étale `X`-scheme trivializing `F` does. -/
@[sga "4½ Rapport 5.12" "partial",
  sga "4½ Th_finitude 2.2" "Clause (c), special case",
  sga "5 X 6.1" "Condition ii)"]
theorem trivializedByPointedGaloisCovers [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
    (x : GeometricPoint X) (Λ : Type r) [Ring Λ] : TrivializedByPointedGaloisCovers X x Λ := by
  intro F hF
  obtain ⟨Y, hYfin, hYne, M, hM, ⟨eY⟩⟩ := exists_finiteEtale_trivialization hX hF
  let Yf : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ Y.hom ⟨hYfin, inferInstance⟩
  have hfib : Nonempty ((finiteEtaleFiberFintypeFunctor X x).obj Yf) :=
    (PreGaloisCategory.not_initial_iff_fiber_nonempty _ Yf).1 fun hi ↦
      (isEmpty_left_of_isInitial_finiteEtaleOver Yf hi).elim (Classical.arbitrary Y.left)
  obtain ⟨y⟩ := hfib
  obtain ⟨A, f, a, hA, -⟩ :=
    PreGaloisCategory.exists_hom_from_galois_of_fiber (finiteEtaleFiberFintypeFunctor X x) Yf y
  exact ⟨⟨A, a, hA⟩, M, hM, ⟨Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap
    X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ((finiteEtaleToEtale X).map f) F M eY⟩⟩

end AlgebraicGeometry

end
