module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietorisConstruction

/-!
# The single Mayer--Vietoris cover of the union step of Tag 0DI7, read at the stages

The union step of Stacks 0DI7 compares the four systems of derived morphism sets attached to
`U₀`, `V₀`, `U₀ ∩ V₀` and `U₀ ∪ V₀` of a relative descent situation. The Mayer--Vietoris
sequence of Stacks 08BW that relates them is instantiated **once**, on the single scheme
`U₀ ∪ V₀` covered by the two opens cut out there by `U₀` and by `V₀`, and then pushed to each
stage and to the limit by the derived pullback, which is a triangulated functor. Instantiating
it once is what makes the connecting homomorphism usable: each stage's connecting map is the
image of one fixed map under a functor, so its compatibility with the transition maps is the
cocycle identity of Tag 0D5S rather than a comparison of two independently chosen connecting
maps on two different spaces.

This file supplies the geometry and the shift bookkeeping that the push-forward needs: the two
opens of `U₀ ∪ V₀` and the fact that they cover it, the identification of the opens they cut out
at a stage with the open ranges along which
`AlgebraicGeometry.RelativeDescentSituation.homRestrictToSmaller` restricts, and the
identification of the derived morphism sets of a shifted second argument with the shifted
morphism sets the Mayer--Vietoris sequence is stated in.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.restrictSupOpenLeft` and `restrictSupOpenRight`:
  the two opens of `U₀ ∪ V₀` cut out by `U₀` and by `V₀`.
* `AlgebraicGeometry.RelativeDescentSituation.restrictStageObj` and `restrictLimitObj`: the
  derived pullback of the restriction of an object of `D(𝒪_{X₀})`, at a stage and at the limit;
  the derived morphism sets of the system are the morphisms between these.
* `AlgebraicGeometry.RelativeDescentSituation.restrictStageShiftIso` and
  `restrictLimitShiftIso`: the shift passes through both derived pullbacks.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomStageShiftAddEquiv` and
  `restrictHomLimitShiftAddEquiv`: consequently the derived morphism sets at the shifted second
  argument `L₀⟦n⟧` are the shifted morphism sets `Hom(K, L⟦n⟧)` of Stacks 08BW.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.restrictSupOpenLeft_sup_restrictSupOpenRight`:
  **the two opens cover `U₀ ∪ V₀`**, which is the hypothesis `U ⊔ V = ⊤` of Stacks 08BW.
* `AlgebraicGeometry.RelativeDescentSituation.restrictSupOpenLeft_inf_restrictSupOpenRight`:
  their intersection is the open cut out by `U₀ ∩ V₀`.
* `AlgebraicGeometry.RelativeDescentSituation.preimage_restrictSupOpenLeft` and
  `preimage_restrictSupOpenRight`: at a stage, the open cut out by `U₀` is the open range of the
  inclusion of the stage of the situation restricted to `U₀`, and likewise for `V₀`; the limit
  versions are `preimage_restrictSupOpenLeft_limit` and `preimage_restrictSupOpenRight_limit`.

## Implementation notes

The two opens are `(U₀ ⊔ V₀).ι ⁻¹ᵁ U₀` and `(U₀ ⊔ V₀).ι ⁻¹ᵁ V₀`, so that they cover by
`AlgebraicGeometry.Scheme.Opens.ι_preimage_self` and their intersection is the open cut out by
`U₀ ⊓ V₀` by `AlgebraicGeometry.Scheme.Hom.preimage_inf`, both on the nose. Taking instead the
opens abstractly isomorphic to `U₀` and `V₀` over `U₀ ∪ V₀` would make the cover a transported
equality and every later comparison carry that transport.

The shift isomorphism is the composite of the commutation of the two derived pullbacks with the
shift, which is `Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift`, the first
clause of Stacks 06YJ. No flatness and no boundedness enters.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

variable (K₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-! ### The two opens of the union -/

section Cover

variable (U₀ V₀ : D.X₀.left.Opens)

/-- The open of `U₀ ∪ V₀` cut out by `U₀`. -/
abbrev restrictSupOpenLeft : (U₀ ⊔ V₀ : D.X₀.left.Opens).toScheme.Opens :=
  (U₀ ⊔ V₀ : D.X₀.left.Opens).ι ⁻¹ᵁ U₀

/-- The open of `U₀ ∪ V₀` cut out by `V₀`. -/
abbrev restrictSupOpenRight : (U₀ ⊔ V₀ : D.X₀.left.Opens).toScheme.Opens :=
  (U₀ ⊔ V₀ : D.X₀.left.Opens).ι ⁻¹ᵁ V₀

/-- **The two opens cut out by `U₀` and by `V₀` cover `U₀ ∪ V₀`.** This is the hypothesis
`U ⊔ V = ⊤` under which the Mayer--Vietoris sequence of Stacks 08BW is available, and it holds
on the nose because the two opens are taken as preimages. -/
theorem restrictSupOpenLeft_sup_restrictSupOpenRight :
    D.restrictSupOpenLeft U₀ V₀ ⊔ D.restrictSupOpenRight U₀ V₀ = ⊤ :=
  (U₀ ⊔ V₀ : D.X₀.left.Opens).ι_preimage_self

/-- The intersection of the two opens is the open of `U₀ ∪ V₀` cut out by `U₀ ∩ V₀`. -/
theorem restrictSupOpenLeft_inf_restrictSupOpenRight :
    D.restrictSupOpenLeft U₀ V₀ ⊓ D.restrictSupOpenRight U₀ V₀ =
      (U₀ ⊔ V₀ : D.X₀.left.Opens).ι ⁻¹ᵁ (U₀ ⊓ V₀) :=
  rfl

end Cover

/-! ### The opens cut out at a stage and at the limit -/

section Stage

variable (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (hV₀ : IsCompact (V₀ : Set D.X₀.left))
  (hsup : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))

/-- **At a stage, the open cut out by `U₀` is the open range of the inclusion of the stage of
the situation restricted to `U₀`.** This is what lets the Mayer--Vietoris sequence on the stage
of `U₀ ∪ V₀` be read on the system of derived morphism sets attached to `U₀`. -/
theorem preimage_restrictSupOpenLeft (i : D.LaterIndex) :
    (D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i ⁻¹ᵁ D.restrictSupOpenLeft U₀ V₀ =
      (D.restrictToLarger (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i).opensRange :=
  (D.opensRange_restrictToLarger (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i).symm

/-- **At a stage, the open cut out by `V₀` is the open range of the inclusion of the stage of
the situation restricted to `V₀`.** -/
theorem preimage_restrictSupOpenRight (i : D.LaterIndex) :
    (D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i ⁻¹ᵁ D.restrictSupOpenRight U₀ V₀ =
      (D.restrictToLarger (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i).opensRange :=
  (D.opensRange_restrictToLarger (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i).symm

/-- **At the limit, the open cut out by `U₀` is the open range of the inclusion of the limit of
the situation restricted to `U₀`.** -/
theorem preimage_restrictSupOpenLeft_limit :
    (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage ⁻¹ᵁ D.restrictSupOpenLeft U₀ V₀ =
      (D.restrictToLargerLimit (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left).opensRange :=
  (D.opensRange_restrictToLargerLimit (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left).symm

/-- **At the limit, the open cut out by `V₀` is the open range of the inclusion of the limit of
the situation restricted to `V₀`.** -/
theorem preimage_restrictSupOpenRight_limit :
    (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage ⁻¹ᵁ D.restrictSupOpenRight U₀ V₀ =
      (D.restrictToLargerLimit (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right).opensRange :=
  (D.opensRange_restrictToLargerLimit (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right).symm

end Stage

/-! ### The shift of the second argument -/

section Shift

variable (W₀ : D.X₀.left.Opens) (hW₀ : IsCompact (W₀ : Set D.X₀.left))
  (M₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- The derived pullback to a stage of the restriction of an object of `D(𝒪_{X₀})` to a
quasi-compact open. The derived morphism sets of the system are the morphisms between these. -/
abbrev restrictStageObj (i : D.LaterIndex) :
    DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((D.restrict W₀ hW₀).schemeAt i).toRingedSpace)) :=
  (derivedPullback ((D.restrict W₀ hW₀).toFixedStage i).toLRSHom.toShHom).obj
    ((derivedPullback W₀.ι.toLRSHom.toShHom).obj M₀)

/-- The derived pullback to the limit of the restriction of an object of `D(𝒪_{X₀})` to a
quasi-compact open. -/
abbrev restrictLimitObj :
    DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (D.restrict W₀ hW₀).limitScheme.toRingedSpace)) :=
  (derivedPullback (D.restrict W₀ hW₀).limitToFixedStage.toLRSHom.toShHom).obj
    ((derivedPullback W₀.ι.toLRSHom.toShHom).obj M₀)

/-- **The shift passes through both derived pullbacks, at a stage.** Derived pullback commutes
with the shift by the first clause of Stacks 06YJ, so the restriction to a stage of `L₀⟦n⟧` is
the `n`-th shift of the restriction of `L₀`. -/
def restrictStageShiftIso (n : ℤ) (i : D.LaterIndex) :
    D.restrictStageObj W₀ hW₀ (M₀⟦n⟧) i ≅ (D.restrictStageObj W₀ hW₀ M₀ i)⟦n⟧ :=
  (derivedPullback ((D.restrict W₀ hW₀).toFixedStage i).toLRSHom.toShHom).mapIso
      (((derivedPullback W₀.ι.toLRSHom.toShHom).commShiftIso n).app M₀) ≪≫
    ((derivedPullback ((D.restrict W₀ hW₀).toFixedStage i).toLRSHom.toShHom).commShiftIso n).app _

/-- **The shift passes through both derived pullbacks, at the limit.** -/
def restrictLimitShiftIso (n : ℤ) :
    D.restrictLimitObj W₀ hW₀ (M₀⟦n⟧) ≅ (D.restrictLimitObj W₀ hW₀ M₀)⟦n⟧ :=
  (derivedPullback (D.restrict W₀ hW₀).limitToFixedStage.toLRSHom.toShHom).mapIso
      (((derivedPullback W₀.ι.toLRSHom.toShHom).commShiftIso n).app M₀) ≪≫
    ((derivedPullback (D.restrict W₀ hW₀).limitToFixedStage.toLRSHom.toShHom).commShiftIso
      n).app _

/-- **The derived morphism sets at the shifted second argument are the shifted morphism sets of
Stacks 08BW, at a stage.** Postcomposition with `restrictStageShiftIso` identifies
`Hom(Kᵢ, (L₀⟦n⟧)ᵢ)` with `Hom(Kᵢ, (L₀)ᵢ⟦n⟧)`, which is the spot the Mayer--Vietoris sequence
occupies in degree `n`. -/
def restrictHomStageShiftAddEquiv (n : ℤ) (i : D.LaterIndex) :
    D.restrictHomStage K₀ W₀ hW₀ (M₀⟦n⟧) i ≃+
      (D.restrictStageObj W₀ hW₀ K₀ i ⟶ (D.restrictStageObj W₀ hW₀ M₀ i)⟦n⟧) where
  toFun x := x ≫ (D.restrictStageShiftIso W₀ hW₀ M₀ n i).hom
  invFun y := y ≫ (D.restrictStageShiftIso W₀ hW₀ M₀ n i).inv
  left_inv x :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => x ≫ m) (Iso.hom_inv_id _)).trans (Category.comp_id x))
  right_inv y :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => y ≫ m) (Iso.inv_hom_id _)).trans (Category.comp_id y))
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- **The derived morphism sets at the shifted second argument are the shifted morphism sets of
Stacks 08BW, at the limit.** -/
def restrictHomLimitShiftAddEquiv (n : ℤ) :
    D.restrictHomLimit K₀ W₀ hW₀ (M₀⟦n⟧) ≃+
      (D.restrictLimitObj W₀ hW₀ K₀ ⟶ (D.restrictLimitObj W₀ hW₀ M₀)⟦n⟧) where
  toFun x := x ≫ (D.restrictLimitShiftIso W₀ hW₀ M₀ n).hom
  invFun y := y ≫ (D.restrictLimitShiftIso W₀ hW₀ M₀ n).inv
  left_inv x :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => x ≫ m) (Iso.hom_inv_id _)).trans (Category.comp_id x))
  right_inv y :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => y ≫ m) (Iso.inv_hom_id _)).trans (Category.comp_id y))
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

end Shift

end AlgebraicGeometry.RelativeDescentSituation

end
