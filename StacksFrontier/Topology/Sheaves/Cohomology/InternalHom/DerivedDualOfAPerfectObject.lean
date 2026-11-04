module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect

/-!
# The derived dual of a perfect object computes the derived internal Hom

Let `X` be a ringed site and let `M` be a **perfect** object of `D(O)`. Write
`M^∨ = RSheafHom(M, O[0])` for its derived dual. This file proves

`K ⊗^L_O M^∨ ≅ RSheafHom(M, K)` for every `K`, naturally in `K`.

This is the content of the third assertion of Stacks 08JJ, obtained by reading Stacks 0ATN
part (1) at the unit of the derived tensor product: the diagonal morphism of Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is invertible at a perfect `M` with no hypothesis on `K` or `L`
(`AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_isPerfect`), and at `L = O[0]`
the target is `RSheafHom(M, K ⊗^L_O O[0])`, which the right unit constraint of the derived tensor
product identifies with `RSheafHom(M, K)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorSiteDatum`: the canonical derived tensor product of
  a ringed site, read as a datum of the ring-sheaf-indexed interface that the unit and
  commutativity constraints are stated for.
* `AlgebraicGeometry.RingedSite.derivedTensorRightUnitor`: the right unit constraint
  `- ⊗^L_O O[0] ≅ 𝟭` of the canonical derived tensor product.
* `AlgebraicGeometry.RingedSite.derivedDualTensorIsoDerivedSheafHom`: the isomorphism
  `K ⊗^L_O M^∨ ≅ RSheafHom(M, K)` at a perfect `M`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedDualTensorIsoDerivedSheafHom_hom_naturality`: that
  isomorphism is natural in `K`.

## Implementation notes

*Two interfaces for one derived tensor product.* The derived tensor product of a ringed site is
carried by two structures with the same fields: `Stacks.SheafOfModules.DerivedTensorProduct`,
indexed by the ringed site, which is what `canonicalDerivedTensorProduct` and hence the diagonal
morphism of Stacks 0BYS use; and `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, indexed
by the structure sheaf, which is what the unit, associativity and commutativity constraints are
built for. `derivedTensorSiteDatum` transports the canonical datum from the first to the second
field by field — exactly as `Stacks.SheafOfModules.derivedTensorAsSiteDatum` does for a ringed
space — and `derivedTensorSiteDatum_tensor` records that it does not change the bifunctor, so the
two readings agree on the nose and no comparison isomorphism enters any statement below.

*What this does not give.* The isomorphism below is **not** asserted to be the canonical map
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` of Stacks 08JD, which is built from
the derived composition of Stacks 0A98 rather than from the interchange of Stacks 0BYR. Nothing
below identifies the two, and the section "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage` records what
such an identification would need. So the *existence* of the isomorphism of Stacks 08JJ (3) at a
perfect object is settled here, while the assertion that the canonical map of Stacks 08JD realises
it is not; for that reason no attribute is placed on the declarations below.

The dual is spelled `RSheafHom(M, O[0])` with the structure sheaf in degree zero written as
`Stacks.DerivedTensor.RingedSite.unitObject`, the spelling the unit constraint is stated at; it
is the same object as `AlgebraicGeometry.RingedSite.derivedDual` evaluated at `M`, whose unit is
`AlgebraicGeometry.RingedSite.derivedStructureSheaf`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- The canonical derived tensor product of a ringed site, read as a datum of the
ring-sheaf-indexed interface `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` that the
unit and commutativity constraints are stated for. Every field is the corresponding field of
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`. -/
def derivedTensorSiteDatum : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O :=
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct X
  { tensor := T.tensor
    comparison := T.comparison
    comparison_naturality := T.comparison_naturality
    comparisonRight := T.comparisonRight
    comparisonRight_naturality := T.comparisonRight_naturality
    comparisonRight_eq_comparison := T.comparisonRight_eq_comparison
    comparisonLeft := T.comparisonLeft
    comparisonLeft_naturality := T.comparisonLeft_naturality
    comparisonLeft_eq_comparison := T.comparisonLeft_eq_comparison
    toTensor := T.toTensor
    toTensor_naturality := T.toTensor_naturality
    toTensor_eq_comparisonRight := T.toTensor_eq_comparisonRight
    toTensor_eq_comparisonLeft := T.toTensor_eq_comparisonLeft
    commShift₂ := T.commShift₂
    exact_left := T.exact_left
    exact_right := T.exact_right }

/-- Reading the canonical derived tensor product in the other interface does not change the
bifunctor. -/
theorem derivedTensorSiteDatum_tensor :
    (derivedTensorSiteDatum X).tensor =
      Stacks.SheafOfModules.derivedTensorProductFunctor X := rfl

/-- **The right unit constraint of the derived tensor product of a ringed site**,
`- ⊗^L_O O[0] ≅ 𝟭 D(O)`. This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso` at the canonical
datum. -/
def derivedTensorRightUnitor :
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj
        (Stacks.DerivedTensor.RingedSite.unitObject X) ≅
      𝟭 (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))) :=
  (derivedTensorSiteDatum X).rightUnitorNatIso X

/-- The naturality square of `AlgebraicGeometry.RingedSite.derivedTensorRightUnitor`: tensoring
a morphism with the identity of `O[0]` and then cancelling the unit is cancelling the unit and
then the morphism. -/
theorem derivedTensorRightUnitor_naturality
    {K K' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))}
    (f : K ⟶ K') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app
          (Stacks.DerivedTensor.RingedSite.unitObject X) ≫
        (derivedTensorRightUnitor X).hom.app K' =
      (derivedTensorRightUnitor X).hom.app K ≫ f :=
  (derivedTensorSiteDatum X).rightUnitorNatIso_naturality X f

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **Stacks 08JJ (3): the derived dual of a perfect object computes the derived internal Hom.**
For a perfect object `M` of `D(O)` and an arbitrary object `K`,

`K ⊗^L_O RSheafHom(M, O[0]) ≅ RSheafHom(M, K)`.

It is the diagonal morphism of Stacks 0BYS at `L = O[0]`, invertible by Stacks 0ATN part (1),
followed by the right unit constraint inside the internal Hom. It is natural in `K` by
`AlgebraicGeometry.RingedSite.derivedDualTensorIsoDerivedSheafHom_hom_naturality`. -/
def derivedDualTensorIsoDerivedSheafHom
    (K M : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)))
    (hM : X.IsPerfect M) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj
          (Stacks.DerivedTensor.RingedSite.unitObject X)) ≅
      ((derivedSheafHomBifunctor X).obj (op M)).obj K :=
  haveI := isIso_derivedTensorHomDiagonal_of_isPerfect X K
    (Stacks.DerivedTensor.RingedSite.unitObject X) M hM
  asIso (derivedTensorHomDiagonal X K
      (Stacks.DerivedTensor.RingedSite.unitObject X) M) ≪≫
    ((derivedSheafHomBifunctor X).obj (op M)).mapIso
      ((derivedTensorRightUnitor X).app K)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The isomorphism of Stacks 08JJ (3) at a perfect object is natural in the tensor factor.**
For `f : K ⟶ K'` the morphism `f ⊗ 𝟙` on the duals is carried to `RSheafHom(M, f)`.

The diagonal morphism is covariant in the tensor factor by
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_natural_left` and the right unit
constraint is natural, so the square is the two naturality squares composed. -/
theorem derivedDualTensorIsoDerivedSheafHom_hom_naturality
    (M : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)))
    (hM : X.IsPerfect M)
    {K K' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))}
    (f : K ⟶ K') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app
          (((derivedSheafHomBifunctor X).obj (op M)).obj
            (Stacks.DerivedTensor.RingedSite.unitObject X)) ≫
        (derivedDualTensorIsoDerivedSheafHom X K' M hM).hom =
      (derivedDualTensorIsoDerivedSheafHom X K M hM).hom ≫
        ((derivedSheafHomBifunctor X).obj (op M)).map f := by
  dsimp only [derivedDualTensorIsoDerivedSheafHom, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, derivedTensorHomDiagonal_natural_left X
    (Stacks.DerivedTensor.RingedSite.unitObject X) M f, Category.assoc,
    ← CategoryTheory.Functor.map_comp, derivedTensorRightUnitor_naturality X f,
    CategoryTheory.Functor.map_comp, Category.assoc]

end AlgebraicGeometry.RingedSite

end
