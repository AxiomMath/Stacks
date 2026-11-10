module

public import StacksFrontier.AlgebraicGeometry.Stacks.FirstOrderThickeningAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FirstOrderThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismLift
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesStack
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftCartesianTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovePostcomposition
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The automorphism sheaves of the category of smooth lifts are abelian (Stacks 0CKG (1))

Let `𝒳 ⊂ 𝒳'` be a first-order thickening of algebraic stacks, `W` an algebraic space with a smooth
`x : W ⟶ 𝒳`, and let `p : 𝒞 ⟶ W_{spaces, étale}` be the category of smooth lifts of the étale
opens of `W` (`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP). Part (1) of Stacks 0CKG
says that the automorphism sheaves of the objects of `𝒞` are abelian; this is
`AlgebraicGeometry.Stack.EtaleSmoothLift.fiber_endomorphisms_comm`, in the form of the
hypothesis of Stacks 0CJY: the endomorphisms of every object of every fibre of `p` commute.

## The argument

For an object `ξ = (U, U', a, i, x', α)` the source identifies `Aut(ξ)` with the sheaf of
sections `δ : U' ⟶ I'` of `p' : I' = U' ×_{𝒳'} U' ⟶ U'` restricting to the diagonal over `U`
(`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismLift`), then with
`SheafHom(Δ^*Ω_{I/U}, 𝒞_{U/U'})` through the action of More on Morphisms of Spaces, Lemma 061C,
and asserts — "we omit the detailed verification" — that composition corresponds to addition.
The proof here does not need that verification in that form:

* `U ⊂ U'` is a first-order thickening of algebraic spaces
  (`AlgebraicGeometry.Stack.EtaleSmoothLift.isFirstOrderThickening_range_inclusion`, from
  Stacks 0BPR), hence so is its inverse image `I ⊂ I'`, and `Δ : (U ⊂ U') ⟶ (I ⊂ I')` is a
  morphism of thickenings over `U'` in the cartesian situation of Stacks 0CK7, whose conormal
  datum is supplied by the conormal map of the diagonal
  (`AlgebraicGeometry.Stack.EtaleSmoothLift.isCartesianConormalCompatible_diagonalConormalMap`,
  the composition law of Stacks 04G2);
* the sections `δ_σ` are lifts of `Δ` over `U'`, on which the group of Stacks 061C acts simply
  transitively (`AlgebraicGeometry.Space.conormalLiftSheafAddAction_bijective`);
* right translation `R_τ` restricts to the identity of `I`, so the postcomposition law of
  Stacks 0CK6 (`AlgebraicGeometry.Space.derivationMove_comp`) makes it equivariant for one fixed
  reparametrization `θ ↦ θ''` of the action
  (`AlgebraicGeometry.Stack.EtaleSmoothLift.vadd_diagonal_comp_rightTranslation`);
* since `δ_{σ ≫ τ} = R_τ ∘ δ_σ`, writing `δ_σ = θ_σ · Δ'` gives `δ_{σ ≫ τ} = θ_σ'' · δ_τ`; taking
  `τ = id` forces `θ_σ'' = θ_σ`, so `δ_{σ ≫ τ} = (θ_σ + θ_τ) · Δ'` is symmetric in `σ` and `τ`
  (`AddAction.eq_of_translation`), and `δ` is injective.

Smoothness of `x'` is not used: it enters the source's part (2), through finite local freeness of
`Ω_{I/U}`, and not the commutativity.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory Opposite

namespace CategoryTheory

/-- Precomposing with an `eqToHom` does not change a morphism up to heterogeneous equality. -/
theorem heq_eqToHom_comp {𝒞 : Type*} [Category 𝒞] {X X' Y : 𝒞} (h : X = X') (f : X' ⟶ Y) :
    HEq (eqToHom h ≫ f) f := by
  subst h
  simp

end CategoryTheory

/-- **A torsor argument for commutativity.** Let `T` act on `L` freely, let `o ∈ L` and let
`x : M → L` be a family with translation parameters `θ m` (`x m = θ m +ᵥ o`). If a binary law
`m * n` on `M` satisfies `x (m * n) = φ (θ m) +ᵥ x n` for some map `φ`, and `x (m * e) = x m`,
`x e = o` for some `e`, then `x (m * n) = x (n * m)`. -/
theorem AddAction.eq_of_translation {T L M : Type*} [AddCommGroup T] [AddAction T L] (o : L)
    (hfree : ∀ θ₁ θ₂ : T, θ₁ +ᵥ o = θ₂ +ᵥ o → θ₁ = θ₂) (x : M → L) (θ : M → T)
    (hθ : ∀ m, θ m +ᵥ o = x m) (φ : T → T) (mul : M → M → M)
    (hmul : ∀ m n, x (mul m n) = φ (θ m) +ᵥ x n) (e : M) (he : x e = o)
    (hre : ∀ m, x (mul m e) = x m) (m n : M) : x (mul m n) = x (mul n m) := by
  have hφ : ∀ k, φ (θ k) = θ k := fun k =>
    hfree _ _ (((congrArg (φ (θ k) +ᵥ ·) he).symm.trans (hmul k e).symm).trans
      ((hre k).trans (hθ k).symm))
  rw [hmul, hmul, hφ, hφ, ← hθ m, ← hθ n, vadd_vadd, vadd_vadd, add_comm]

namespace AlgebraicGeometry.Space

universe u₀

/-- **The action `θ · c` depends only on its data**, with the edge `e₀` allowed to change along an
equality, the datum `θ` along a heterogeneous equality. -/
theorem derivationMove_congr_edge (B : BigFppfSite.{u₀}) (S : Scheme.{u₀}) (hS : B.Contains S)
    {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (W₀ : ClosedSubspaces B S hS W.1)
    {e₀ e₀' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)} (he : e₀ = e₀')
    (q : W ⟶ T) (hZ : IsFirstOrderThickening B S hS X Z.1) {c c' : X ⟶ W} (hcc : c = c')
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀' ≫ subspaceInclusion B S hS W W₀)
    {θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z}
    {θ' : (modulePullback B S hS e₀').obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z} (hθ : HEq θ θ') {p p' : X ⟶ T} (hp : p = p')
    (hcq : c ≫ q = p) (hcq' : c' ≫ q = p') :
    derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq =
      derivationMove B S hS Z W₀ e₀' q hZ c' hc' θ' p' hcq' := by
  subst he hcc hp
  obtain rfl := eq_of_heq hθ
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

/-- For a first-order thickening `ι`, the image of the inclusion `i : U ⟶ U'` of a smooth lift is
a first-order thickening of `U'`. -/
theorem isFirstOrderThickening_range_inclusion
    (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
    (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    Space.IsFirstOrderThickening B S hS ξ.ambient (Subfunctor.range ξ.inclusion.hom) :=
  isFirstOrderThickening_range_of_isFirstOrderThickening_algebraicSpaceStackFunctor_map.{u, w}
    ξ.inclusion (isThickening_inclusion.{u, w, u} ξ)
    (AlgebraicStacks.isFirstOrderThickening_fst_of_isTwoFibreProduct B S hS hι₁ _
      (Bicategory.isTwoFibreProduct_swap ξ.isTwoFibreProduct))

section Setup

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)

include hι₁ in
/-- The thickening `U ⊂ U'` of algebraic spaces, `U` the image of `i`. -/
theorem isThickening_range_inclusion :
    Space.IsThickening B S hS ξ.ambient (Subfunctor.range ξ.inclusion.hom) :=
  (isFirstOrderThickening_range_inclusion hι₁ ξ).1

include hι₁ in
/-- The closed subspace `U ⊂ U'`, the base thickening of the deformation problem. -/
abbrev baseSubspace : Space.ClosedSubspaces B S hS ξ.ambient.1 :=
  ⟨Subfunctor.range ξ.inclusion.hom, (isThickening_range_inclusion hι₁ ξ).1⟩

include hι₁ in
/-- The thickening `I = U ×_{U'} I' ⊂ I'`, the inverse image of `U` along `p'`. -/
theorem isFirstOrderThickening_preimage_fst :
    Space.IsFirstOrderThickening B S hS ξ.selfIntersection.pt
      (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)).1 :=
  Space.isFirstOrderThickening_preimage B S hS _ ξ.selfIntersection.fst
    (isFirstOrderThickening_range_inclusion hι₁ ξ)

/-- The diagonal `Δ' : U' ⟶ I'`, the section of `p'` attached to the identity of `ξ`. -/
abbrev diagonal : ξ.ambient ⟶ ξ.selfIntersection.pt :=
  ξ.autLift (Hom.id ξ)

/-- The diagonal `Δ'` is a section of the first projection `p' : I' ⟶ U'`. -/
theorem diagonal_fst : ξ.diagonal ≫ ξ.selfIntersection.fst = 𝟙 _ :=
  autLift_fst ξ (Hom.id ξ)

/-- Right translation by `τ` carries the diagonal `Δ'` to the section `δ_τ`. -/
private theorem diagonal_comp_rightTranslation (τ : Hom ξ ξ) :
    ξ.diagonal ≫ ξ.rightTranslation τ = ξ.autLift τ :=
  (autLift_comp ξ (Hom.id ξ) τ).symm.trans (congrArg ξ.autLift
    (Category.id_comp (obj := EtaleSmoothLift B S hS ι hι W x hx) (X := ξ) (Y := ξ) τ))

include hι₁ in
include hι₁ in
/-- The restriction `Δ : U ⟶ I` of the diagonal to the thickenings. -/
def diagonalRestriction :=
  ObjectProperty.homMk
    (X := (⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩ : AlgebraicSpaces B S hS))
    (Y := (⟨(Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)).1.toFunctor,
      (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)).2.1⟩ :
        AlgebraicSpaces B S hS))
    (Subfunctor.lift
    (G := (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)).1)
    ((Subfunctor.range ξ.inclusion.hom).ι ≫ ξ.diagonal.hom)
    (by
      rintro V _ ⟨g, rfl⟩
      change (ξ.diagonal ≫ ξ.selfIntersection.fst).hom.app V g.1 ∈
        (Subfunctor.range ξ.inclusion.hom).obj V
      rw [diagonal_fst]
      exact g.2))

/-- On `U ⊂ U'` the diagonal `Δ'` restricts to `Δ : U ⟶ I`, followed by `I ⊂ I'`. -/
theorem inclusion_comp_diagonal :
    Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) ≫ ξ.diagonal =
      diagonalRestriction hι₁ ξ ≫ Space.subspaceInclusion B S hS ξ.selfIntersection.pt
        (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) :=
  ObjectProperty.hom_ext _ rfl

include hι₁ in
include hι₁ in
/-- The map `A : Δ^*𝒞_{I/I'} ⟶ 𝒞_{U/U'}` of conormal modules of the diagonal. -/
def diagonalConormalMap :=
  Space.conormalMap B S hS (baseSubspace hι₁ ξ)
    (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) ξ.diagonal
    (diagonalRestriction hι₁ ξ) (inclusion_comp_diagonal hι₁ ξ)

/-- The conormal map `A` of the diagonal is compatible with the cartesian square of thickenings
formed by `Δ : (U ⊂ U') ⟶ (I ⊂ I')` over `p' : I' ⟶ U'` and the identity of `U'`. -/
theorem isCartesianConormalCompatible_diagonalConormalMap :
    Space.IsCartesianConormalCompatible B S hS (baseSubspace hι₁ ξ) (baseSubspace hι₁ ξ)
      (𝟙 ξ.ambient) ξ.selfIntersection.fst (diagonalRestriction hι₁ ξ)
      (diagonalConormalMap hι₁ ξ) := by
  have hsq₁ : Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) ≫ 𝟙 ξ.ambient =
      (diagonalRestriction hι₁ ξ ≫
        Space.preimageProjection B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) ≫
        Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) := by
    rw [Category.comp_id, Category.assoc,
      ← Space.conormalEtaleRestrictionSquare B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ),
      ← Category.assoc, ← inclusion_comp_diagonal hι₁ ξ, Category.assoc, diagonal_fst,
      Category.comp_id]
  have hsq : Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) ≫
        ξ.diagonal ≫ ξ.selfIntersection.fst =
      (diagonalRestriction hι₁ ξ ≫
        Space.preimageProjection B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) ≫
        Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) := by
    rw [diagonal_fst]
    exact hsq₁
  refine ⟨hsq₁, ?_⟩
  refine (Space.conormalMap_congr_upper B S hS _ _ (diagonal_fst ξ).symm _ hsq₁ hsq).trans ?_
  exact Space.conormalMap_comp B S hS ξ.diagonal ξ.selfIntersection.fst (baseSubspace hι₁ ξ)
    (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) (baseSubspace hι₁ ξ)
    (diagonalRestriction hι₁ ξ)
    (Space.preimageProjection B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ))
    (inclusion_comp_diagonal hι₁ ξ)
    (Space.conormalEtaleRestrictionSquare B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) hsq

/-- The image `G` of `i : U ⟶ U'` is reached from `U`: its inclusion factors through `i`, as `i` is
a thickening, so an isomorphism onto its image. -/
theorem exists_subspaceInclusion_eq_comp :
    ∃ v : (⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩ : AlgebraicSpaces B S hS) ⟶
        ξ.base.obj.left,
      Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) = v ≫ ξ.inclusion := by
  have : IsIso (Subfunctor.toRange ξ.inclusion.hom) :=
    (isThickeningHom_of_isThickening_algebraicSpaceStackFunctor_map.{u, w} ξ.inclusion
      (isThickening_inclusion.{u, w, u} ξ)).1
  refine ⟨ObjectProperty.homMk (CategoryTheory.inv (Subfunctor.toRange ξ.inclusion.hom)), ?_⟩
  apply ObjectProperty.hom_ext
  change (Subfunctor.range ξ.inclusion.hom).ι =
    CategoryTheory.inv (Subfunctor.toRange ξ.inclusion.hom) ≫ ξ.inclusion.hom
  rw [eq_comm, IsIso.inv_comp_eq]
  exact (Subfunctor.toRange_ι _).symm

/-- **Right translation by an endomorphism over the identity fixes the points of `I'` whose first
projection lies in `U`.** -/
theorem comp_rightTranslation_of_fst_eq (τ : Hom ξ ξ) (hτ : τ.base = 𝟙 ξ.base)
    {T : AlgebraicSpaces B S hS} (z : T ⟶ ξ.selfIntersection.pt)
    (w : T ⟶ (⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩ :
      AlgebraicSpaces B S hS))
    (hz : z ≫ ξ.selfIntersection.fst = w ≫ Space.subspaceInclusion B S hS ξ.ambient
      (baseSubspace hι₁ ξ)) :
    z ≫ ξ.rightTranslation τ = z := by
  obtain ⟨v, hv⟩ := exists_subspaceInclusion_eq_comp hι₁ ξ
  exact comp_rightTranslation_of_fst ξ τ hτ z (u := w ≫ v) (by rw [hz, hv, Category.assoc])

/-- Right translation fixes the thickening `I ⊂ I'`. -/
theorem subspaceInclusion_comp_rightTranslation (τ : Hom ξ ξ) (hτ : τ.base = 𝟙 ξ.base) :
    Space.subspaceInclusion B S hS ξ.selfIntersection.pt
        (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) ≫
        ξ.rightTranslation τ =
      Space.subspaceInclusion B S hS ξ.selfIntersection.pt
        (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) :=
  comp_rightTranslation_of_fst_eq hι₁ ξ τ hτ _
    (Space.preimageProjection B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ))
    (Space.conormalEtaleRestrictionSquare B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ))

/-- The section `δ_σ` of an endomorphism over the identity restricts to the diagonal over `U`. -/
theorem subspaceInclusion_comp_autLift (σ : Hom ξ ξ) (hσ : σ.base = 𝟙 ξ.base) :
    Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) ≫ ξ.autLift σ =
      diagonalRestriction hι₁ ξ ≫ Space.subspaceInclusion B S hS ξ.selfIntersection.pt
        (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)) := by
  rw [← diagonal_comp_rightTranslation ξ σ, ← Category.assoc,
    comp_rightTranslation_of_fst_eq hι₁ ξ σ hσ _ (𝟙 _)
    (by rw [Category.assoc, diagonal_fst, Category.comp_id, Category.id_comp]),
    inclusion_comp_diagonal hι₁ ξ]

/-- **The sheaf of lifts of the diagonal**, Stacks 061B for the morphism of thickenings
`Δ : (U ⊂ U') ⟶ (I ⊂ I')` over `U'` (through `id` and `p'`), as a subfunctor of the presheaf of
morphisms `U' ⟶ I'` on the spaces-étale site of `U'`. -/
abbrev liftsSubfunctor :=
  Space.conormalLiftSubfunctor B S hS (isThickening_range_inclusion hι₁ ξ)
    (isFirstOrderThickening_preimage_fst hι₁ ξ).1 (𝟙 ξ.ambient) ξ.selfIntersection.fst
    (diagonalRestriction hι₁ ξ) (diagonalConormalMap hι₁ ξ)

/-- **The lifts of the diagonal over `U'`**: morphisms `U' ⟶ I'` over `U'` restricting to `Δ` on
`U`, the sections over the final object of the sheaf of lifts. -/
abbrev Lifts := (liftsSubfunctor hι₁ ξ).obj (op (Space.SpacesEtale.final B S hS ξ.ambient))

/-- A section of `p'` restricting to `Δ` on `U` is a lift of the diagonal over `U'`. -/
theorem mem_lifts {d : ξ.ambient ⟶ ξ.selfIntersection.pt} (h₁ : d ≫ ξ.selfIntersection.fst = 𝟙 _)
    (h₂ : Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) ≫ d =
      diagonalRestriction hι₁ ξ ≫ Space.subspaceInclusion B S hS ξ.selfIntersection.pt
        (Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ))) :
    d ∈ (liftsSubfunctor hι₁ ξ).obj (op (Space.SpacesEtale.final B S hS ξ.ambient)) := by
  have heq := Space.conormalLiftSubfunctor_eq_liftSubfunctor_of_cartesian B S hS
    (baseSubspace hι₁ ξ) (isThickening_range_inclusion hι₁ ξ) (𝟙 _) ξ.selfIntersection.fst
    (isFirstOrderThickening_preimage_fst hι₁ ξ).1 (diagonalRestriction hι₁ ξ)
    (diagonalConormalMap hι₁ ξ) (isCartesianConormalCompatible_diagonalConormalMap hι₁ ξ)
  have hw := ((Space.spacesBaseChange B S hS (Space.IsThickening.inclusion B S hS
    (isThickening_range_inclusion hι₁ ξ))).isPullback (Space.SpacesEtale.final B S hS ξ.ambient)).w
  have hmem : Space.IsLiftOver B S hS (isThickening_range_inclusion hι₁ ξ)
      (isFirstOrderThickening_preimage_fst hι₁ ξ).1 (𝟙 _) ξ.selfIntersection.fst
      (diagonalRestriction hι₁ ξ) (Space.SpacesEtale.final B S hS ξ.ambient) d := by
    refine ⟨h₁.trans (Category.comp_id _).symm, ?_⟩
    have hw' := (Category.comp_id _).symm.trans hw
    rw [hw']
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂)
  exact (congrArg (fun F : Subfunctor (Space.spacesEtaleHomPresheaf B S hS ξ.ambient
    ξ.selfIntersection.pt) => d ∈ F.obj (op (Space.SpacesEtale.final B S hS ξ.ambient))) heq).mpr
    hmem

/-- **The section `δ_σ` as a lift of the diagonal over `U'`**, for `σ` over the identity. -/
def autLiftLift (σ : Hom ξ ξ) (hσ : σ.base = 𝟙 ξ.base) : Lifts hι₁ ξ :=
  ⟨ξ.autLift σ, mem_lifts hι₁ ξ (autLift_fst ξ σ) (subspaceInclusion_comp_autLift hι₁ ξ σ hσ)⟩

/-- The group acting on the lifts of the diagonal over `U'`: the `𝒪_U`-linear maps
`Δ^*Ω_{I/U'} ⟶ 𝒞_{U/U'}` of Stacks 061C. -/
abbrev LiftsActingGroup :=
  Space.conormalLiftActionHom B S hS (isThickening_range_inclusion hι₁ ξ)
    (isFirstOrderThickening_preimage_fst hι₁ ξ).1 ξ.selfIntersection.fst (diagonalRestriction hι₁ ξ)
    (Space.SpacesEtale.final B S hS ξ.ambient)

/-- **The action of Stacks 061C on the lifts of the diagonal over `U'`.** -/
@[instance_reducible]
def liftsAction : AddAction (LiftsActingGroup hι₁ ξ) (Lifts hι₁ ξ) :=
  Space.conormalLiftSheafAddAction B S hS (𝟙 _) ξ.selfIntersection.fst (diagonalRestriction hι₁ ξ)
    (diagonalConormalMap hι₁ ξ) (isFirstOrderThickening_range_inclusion hι₁ ξ)
    (isFirstOrderThickening_preimage_fst hι₁ ξ) _

/-- The closed subspace `U ⊂ U'` read on the final object of the spaces-étale site of `U'`. -/
abbrev liftsZ : Space.ClosedSubspaces B S hS
    ((Space.SpacesEtale.toSpaces B S hS ξ.ambient).obj
      (Space.SpacesEtale.final B S hS ξ.ambient)).1 :=
  Space.preimageSubspace B S hS
    ((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
      (Space.SpacesEtale.final B S hS ξ.ambient)).hom
    ⟨Subfunctor.range ξ.inclusion.hom, (isThickening_range_inclusion hι₁ ξ).1⟩

/-- The closed subspace `I ⊂ I'`. -/
abbrev liftsW₀ : Space.ClosedSubspaces B S hS ξ.selfIntersection.pt.1 :=
  ⟨(Space.preimageSubspace B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)).1,
    (isFirstOrderThickening_preimage_fst hι₁ ξ).1.1⟩

/-- The restriction `U ⟶ I` of the diagonal, read on the final object. -/
abbrev liftsEdge :=
  Space.preimageProjection B S hS
    ((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
      (Space.SpacesEtale.final B S hS ξ.ambient)).hom
    ⟨Subfunctor.range ξ.inclusion.hom, (isThickening_range_inclusion hι₁ ξ).1⟩ ≫
  diagonalRestriction hι₁ ξ

/-- The action of `θ` on a lift `s` of the diagonal is the move of `s` by the derivation `θ`. -/
theorem coe_lifts_vadd (θ : LiftsActingGroup hι₁ ξ) (s : Lifts hι₁ ξ) :
    letI := liftsAction hι₁ ξ
    (θ +ᵥ s).1 = Space.derivationMove B S hS (liftsZ hι₁ ξ) (liftsW₀ hι₁ ξ) (liftsEdge hι₁ ξ)
      ξ.selfIntersection.fst
      (Space.isFirstOrderThickening_preimage B S hS _ _
        (isFirstOrderThickening_range_inclusion hι₁ ξ))
      s.1 s.2.2.square θ
      (((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
        (Space.SpacesEtale.final B S hS ξ.ambient)).hom ≫ 𝟙 _) s.2.1.1 :=
  rfl

/-- The composite `I ⊂ I' ⟶ U'` commutes with the identities of `I` and `U'`. -/
theorem liftsBase_comm :
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (𝟙 _)
        (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
          ξ.selfIntersection.fst) =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _
        (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
          ξ.selfIntersection.fst) (𝟙 ξ.ambient) :=
  (Category.id_comp _).trans (Category.comp_id _).symm

/-- **The datum of the postcomposition law of Stacks 0CK6** for a morphism of thickenings which
is the identity on `I`, over the identity of `U'`, read back on the edge `Δ` itself. -/
def liftsTranslationDatum (θ : LiftsActingGroup hι₁ ξ) : LiftsActingGroup hι₁ ξ :=
    Space.postcompDerivationDatum B S hS
      (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
        ξ.selfIntersection.fst)
      (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
        ξ.selfIntersection.fst) (𝟙 _) (𝟙 ξ.ambient) (liftsBase_comm hι₁ ξ) (liftsEdge hι₁ ξ)
      (Space.conormalModule B S hS _ (liftsZ hι₁ ξ)) θ

/-- **Right translation is equivariant at the diagonal**: by the postcomposition law of
Stacks 0CK6 at the morphism of thickenings `(id_I, R_τ) : (I ⊂ I') ⟶ (I ⊂ I')` over the identity
of `U'`, `(θ · Δ') ≫ R_τ = θ'' · (Δ' ≫ R_τ) = θ'' · δ_τ`. -/
theorem vadd_diagonal_comp_rightTranslation (τ : Hom ξ ξ) (hτ : τ.base = 𝟙 ξ.base)
    (θ : LiftsActingGroup hι₁ ξ) :
    letI := liftsAction hι₁ ξ
    (θ +ᵥ autLiftLift hι₁ ξ (Hom.id ξ) rfl).1 ≫ ξ.rightTranslation τ =
      (liftsTranslationDatum hι₁ ξ θ +ᵥ autLiftLift hι₁ ξ τ hτ).1 := by
  let := liftsAction hι₁ ξ
  have hcc := diagonal_comp_rightTranslation ξ τ
  refine (congrArg (· ≫ ξ.rightTranslation τ) (coe_lifts_vadd hι₁ ξ θ _)).trans ?_
  refine (Space.derivationMove_comp B S hS (liftsZ hι₁ ξ) (liftsW₀ hι₁ ξ) (liftsW₀ hι₁ ξ)
    (liftsEdge hι₁ ξ) (𝟙 _) (ξ.rightTranslation τ)
    ((subspaceInclusion_comp_rightTranslation hι₁ ξ τ hτ).trans (Category.id_comp _).symm)
    ξ.selfIntersection.fst ξ.selfIntersection.fst (𝟙 ξ.ambient) (liftsBase_comm hι₁ ξ)
    ((rightTranslation_fst ξ τ).trans (Category.comp_id _).symm)
    (Space.isFirstOrderThickening_preimage B S hS _ _
      (isFirstOrderThickening_range_inclusion hι₁ ξ))
    (isFirstOrderThickening_preimage_fst hι₁ ξ) (isFirstOrderThickening_preimage_fst hι₁ ξ)
    _ _ θ _ _).trans ?_
  refine Eq.trans ?_ (coe_lifts_vadd hι₁ ξ _ _).symm
  exact Space.derivationMove_congr_edge B S hS (liftsZ hι₁ ξ) (liftsW₀ hι₁ ξ)
    (Category.comp_id _) _ _ hcc _ _ HEq.rfl (Category.comp_id _) _ _

include hι₁ in
/-- **Endomorphisms of a smooth lift over the identity commute**, for a first-order thickening.
The sections `δ_σ` of `p'` are lifts of the diagonal over `U'`, on which the sheaf of Stacks 061C
acts simply transitively; right translation by `τ` is equivariant for a fixed reparametrization of
that action, by the postcomposition law of Stacks 0CK6, and `δ_{σ ≫ τ} = R_τ ∘ δ_σ`. So
`δ_{σ ≫ τ}` is the translate of the diagonal by the sum of the parameters of `δ_σ` and `δ_τ`, which
is symmetric in `σ` and `τ`, and `δ` is injective. -/
theorem comp_comm_of_base_eq_id (σ τ : Hom ξ ξ) (hσ : σ.base = 𝟙 ξ.base)
    (hτ : τ.base = 𝟙 ξ.base) : σ.comp τ = τ.comp σ := by
  let := liftsAction hι₁ ξ
  have hbij := Space.conormalLiftSheafAddAction_bijective B S hS (𝟙 _) ξ.selfIntersection.fst
    (diagonalRestriction hι₁ ξ) (diagonalConormalMap hι₁ ξ)
    (isFirstOrderThickening_range_inclusion hι₁ ξ) (isFirstOrderThickening_preimage_fst hι₁ ξ)
    (Space.SpacesEtale.final B S hS ξ.ambient) (autLiftLift hι₁ ξ (Hom.id ξ) rfl)
  let M := {m : Hom ξ ξ // m.base = 𝟙 ξ.base}
  let xx : M → Lifts hι₁ ξ := fun m => autLiftLift hι₁ ξ m.1 m.2
  let mul : M → M → M := fun m n => ⟨m.1.comp n.1, by
    change m.1.base ≫ n.1.base = _
    rw [m.2, n.2, Category.comp_id]⟩
  have key := AddAction.eq_of_translation (autLiftLift hι₁ ξ (Hom.id ξ) rfl)
    (fun θ₁ θ₂ h => hbij.1 h) xx (fun m => (hbij.2 (xx m)).choose)
    (fun m => (hbij.2 (xx m)).choose_spec) (liftsTranslationDatum hι₁ ξ) mul
    (fun m n => Subtype.ext ((autLift_comp ξ m.1 n.1).trans
      ((congrArg (· ≫ ξ.rightTranslation n.1)
        (congrArg Subtype.val (hbij.2 (xx m)).choose_spec).symm).trans
        (vadd_diagonal_comp_rightTranslation hι₁ ξ n.1 n.2 _))))
    ⟨Hom.id ξ, rfl⟩ rfl
    (fun m => Subtype.ext (congrArg ξ.autLift
      (Category.comp_id (obj := EtaleSmoothLift B S hS ι hι W x hx) (X := ξ) (Y := ξ) m.1)))
    ⟨σ, hσ⟩ ⟨τ, hτ⟩
  refine ξ.autLift_injective (congrArg Subtype.val key) ?_
  change σ.base ≫ τ.base = τ.base ≫ σ.base
  rw [hσ, hτ]

end Setup

/-- An endomorphism in a fibre of the projection to the spaces-étale site lies over the identity,
so its base component is an identity. -/
theorem base_eq_id_of_fiber {U : Space.SpacesEtale B S hS W}
    {ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U} (α : ζ ⟶ ζ) :
    Hom.base (Functor.Fiber.fiberInclusion.map α) = 𝟙 _ := by
  have h := IsHomLift.fac' (p := (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)) (𝟙 U)
    (Functor.Fiber.fiberInclusion.map α)
  change (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).map _ = _
  rw [h]
  simp
  rfl

/-- **Stacks 0CKG, part (1).** Let `𝒳 ⊂ 𝒳'` be a first-order thickening of algebraic stacks, `W` an
algebraic space and `x : W ⟶ 𝒳` smooth, and consider the category `𝒞` of smooth lifts of the étale
opens of `W` along the thickening with its projection `p : 𝒞 ⟶ W_{spaces, étale}`
(Stacks 0CJP). Then the automorphism sheaves of the objects of `𝒞` are abelian: for every étale
open `U` of `W` and every object `ζ` of the fibre over `U`, the endomorphisms of `ζ` in that fibre
commute. -/
@[stacks 0CKG "part (1): the automorphism sheaves of objects of the category of smooth lifts \
are abelian"]
theorem fiber_endomorphisms_comm (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
    (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (α β : ζ ⟶ ζ) :
    α ≫ β = β ≫ α := by
  apply Functor.Fiber.fiberInclusion.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  exact comp_comm_of_base_eq_id hι₁ ζ.1 _ _ (base_eq_id_of_fiber α) (base_eq_id_of_fiber β)

end AlgebraicGeometry.Stack.EtaleSmoothLift

end
