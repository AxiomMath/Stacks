module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived projection formula `K ⊗^L_ℬ Rf_*M ≅ Rf_*(Lf^*K ⊗^L_𝒜 M)`

Let `S` be a scheme, `π : X ⟶ Y` a finite morphism of algebraic spaces over `S`, `𝒜` a sheaf of
rings on `X_étale`, `ℬ` a sheaf of rings on `Y_étale` and `φ : ℬ ⟶ π_{small,*}𝒜` a homomorphism
of sheaves of rings; these data are the morphism of ringed topoi

`f : (Sh(X_étale), 𝒜) ⟶ (Sh(Y_étale), ℬ)`

of Stacks 0DK4, available as `AlgebraicGeometry.Space.smallEtaleRingedToposHomOfSharp`.
**Stacks 0DK5** asserts that for `K ∈ D(ℬ)` and `M ∈ D(𝒜)` the canonical map of
Equation 21.50.0.1 is an isomorphism

`K ⊗^L_ℬ Rf_*M ≅ Rf_*(Lf^*K ⊗^L_𝒜 M)`

in `D(ℬ)`.

This file states that isomorphism in the form the available proof supports, which is **not** the
form the tag is written in. Two restrictions enter, both recorded in the tag attributes below.

*The universe and the site presentation.* The canonical map itself, Equation 21.50.0.1, is
`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap` (Stacks 0B56), and it is
built from the comparison `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` of Stacks 07A4
(`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`) and the derived adjunction
`Lf^* ⊣ Rf_*` of Stacks 07A6 (`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction`).
Both of those are available only for an `AlgebraicGeometry.RingedToposSiteHom` between ringed
topoi at `AlgebraicGeometry.RingedTopos.{u, u, u}` whose underlying functor is a morphism of
sites — a narrowing that comes down from the K-flat resolutions of Stacks 06YS through the
derived tensor product of Stacks 06YU, as the implementation notes of the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison`
record. The small étale ringed topos of an algebraic space is
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`
(`AlgebraicGeometry.Space.smallEtaleRingedToposOfRings`, whose site has objects in `Type (u + 1)`
and sections in `Type u`), so it does not meet the universe condition; and a morphism of
algebraic spaces induces no functor between the two small étale sites, so even at matching
universes the morphism of ringed topoi of Stacks 0DK4 is not presented by a morphism of sites.
The statements here are therefore about a morphism of ringed topoi satisfying 07A4's own
hypotheses, carried explicitly, and the datum of Stacks 0DK4 is an instance of neither.

*The invertibility.* What is proved is the formal half of the source's argument: the canonical
map is the adjoint transpose of the comparison of Stacks 07A4 followed by the counit
`Lf^*Rf_*M ⟶ M` in the first factor, so once that counit is invertible at `M` and the unit of
`Lf^* ⊣ Rf_*` is invertible at `Rf_*M ⊗^L_ℬ K`, the transpose is a composite of isomorphisms.
Finiteness of `π` is what the source uses to supply those two conditions, through the stalk
computation of Stacks 0DK3 and the underived projection formula of Stacks 0DK4; neither is
available in this tree for the small étale topos, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleTensorPushforward.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteStalkPushforward.lean` record. So the two conditions
are carried as hypotheses, exactly as the underived statement of Stacks 04G0 and Stacks 0DK4
carries them in `AlgebraicGeometry.Space.isIso_tensorPushforwardMap`.

Nothing here is an assumption of the conclusion: `hε` is a condition on `Rf_*` alone — it is
equivalent, over all `M`, to `Rf_*` being fully faithful — and `hη` is the condition that
`Rf_*M ⊗^L_ℬ K` lie in the essential image of `Rf_*`, neither of which mentions the canonical
map.

## Main definitions

* `AlgebraicGeometry.Space.derivedProjectionFormulaIso`: **Stacks 0DK5** as an isomorphism
  `Rf_*M ⊗^L_ℬ K ≅ Rf_*(M ⊗^L_𝒜 Lf^*K)`, the factors in the order Equation 21.50.0.1 is written
  in.
* `AlgebraicGeometry.Space.derivedProjectionFormulaIsoSourceOrder`: the same isomorphism with
  both tensor products transposed, `K ⊗^L_ℬ Rf_*M ≅ Rf_*(Lf^*K ⊗^L_𝒜 M)`, which is the order the
  source writes Stacks 0DK5 in.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedProjectionFormulaMap`: **Stacks 0DK5**, the invertibility
  clause, from the counit at `M` and the unit at `Rf_*M ⊗^L_ℬ K`.

## Implementation notes

The canonical map is not redefined. `Stacks.Cohomology.ProjectionFormulaOnRingedTopoi` already
builds it with no hypothesis beyond `hmos`, and tags it `0B56`; Stacks 0DK5 is the assertion that
*that* map is invertible, so the statements here are about it and the `0DK5` attributes sit on the
invertibility and on the two isomorphisms, not on a second copy of the map.

The proof of `isIso_derivedProjectionFormulaMap` is the three-factor argument of
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap`, which proves the underived
projection formula for a closed quotient morphism of ringed spaces by the same rewriting of the
adjoint transpose through the unit: `projectionFormulaMap_eq_unit_comp` exhibits the map as
`η ≫ Rf_*(t ≫ (ε ×ₘ 𝟙))` with `t` the comparison of Stacks 07A4, which is an isomorphism
outright, and the two remaining factors are the hypotheses.

The transposed form uses the commutativity constraint of the derived tensor product, Stacks 0FPT
in the form `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`, on both sides —
once on `D(ℬ)` and once, under `Rf_*`, on `D(𝒜)`. It is a presentational variant and carries no
further hypothesis: the ringed sites it is taken over are the presenting ringed sites
`AlgebraicGeometry.RingedTopos.toRingedSite` of the two ringed topoi, whose structure sheaves are
the structure sheaves of the topoi, so the derived tensor products are the same ones.

## References

* [Stacks Project, Tag 0DK5](https://stacks.math.columbia.edu/tag/0DK5)
* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi (derivedAdjunction)
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.ProjectionFormulaOnRingedTopoi
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **Stacks 0DK5, the invertibility clause**, reduced to the derived adjunction of Stacks 07A6:
the canonical map `Rf_*M ⊗^L_{𝒪_D} K ⟶ Rf_*(M ⊗^L_{𝒪_C} Lf^*K)` of Equation 21.50.0.1 is an
isomorphism once the counit of `Lf^* ⊣ Rf_*` is invertible at `M` and its unit is invertible at
`Rf_*M ⊗^L_{𝒪_D} K`.

Writing the canonical map through the unit, `projectionFormulaMap_eq_unit_comp`, it becomes

`Rf_*M ⊗^L K --η--> Rf_*Lf^*(Rf_*M ⊗^L K) --Rf_*(t)--> Rf_*(Lf^*Rf_*M ⊗^L Lf^*K)
   --Rf_*(ε ⊗ 1)--> Rf_*(M ⊗^L Lf^*K)`,

whose middle factor is the comparison of Stacks 07A4 and so invertible with no hypothesis, and
whose two outer factors are `hη` and `hε`. -/
@[stacks 0DK5 "the invertibility clause, for a morphism of ringed topoi arising from a morphism \
  of sites at a single universe, which is what the derived pullback tensor comparison of 07A4 \
  requires — the small étale ringed topos of an algebraic space does not satisfy this — and \
  given the counit of 07A6 at `M` and its unit at `Rf_*M ⊗^L K`, which is what finiteness of \
  `π` is used for"]
theorem isIso_derivedProjectionFormulaMap
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hε : IsIso ((derivedAdjunction f hmos).counit.app M))
    (hη : IsIso ((derivedAdjunction f hmos).unit.app
      ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O)).obj
        ((derivedPushforward f).obj M, K)))) :
    IsIso (projectionFormulaMap f hmos M K) := by
  have hprod : IsIso
      ((derivedAdjunction f hmos).counit.app M ×ₘ
        𝟙 ((derivedPullback f).obj K)) :=
    ((asIso ((derivedAdjunction f hmos).counit.app M)).prod
      (Iso.refl ((derivedPullback f).obj K))).isIso_hom
  rw [projectionFormulaMap_eq_unit_comp]
  infer_instance

/-- **Stacks 0DK5** as an isomorphism `Rf_*M ⊗^L_{𝒪_D} K ≅ Rf_*(M ⊗^L_{𝒪_C} Lf^*K)`, with the
tensor factors in the order Equation 21.50.0.1 of Stacks 0B56 is written in; the forward map is
the canonical one, not an unspecified isomorphism of objects. -/
@[stacks 0DK5 "the isomorphism, for a morphism of ringed topoi arising from a morphism of sites \
  at a single universe, which is what the derived pullback tensor comparison of 07A4 requires — \
  the small étale ringed topos of an algebraic space does not satisfy this — and given the \
  counit of 07A6 at `M` and its unit at `Rf_*M ⊗^L K`, which is what finiteness of `π` is used \
  for; the tensor factors in the order of Equation 21.50.0.1"]
def derivedProjectionFormulaIso
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hε : IsIso ((derivedAdjunction f hmos).counit.app M))
    (hη : IsIso ((derivedAdjunction f hmos).unit.app
      ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O)).obj
        ((derivedPushforward f).obj M, K)))) :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj M)).obj K ≅
      (derivedPushforward f).obj
        (((derivedTensorProductFunctor X.O).obj M).obj ((derivedPullback f).obj K)) :=
  have := isIso_derivedProjectionFormulaMap f hmos M K hε hη
  asIso (projectionFormulaMap f hmos M K)

/-- The forward map of `AlgebraicGeometry.Space.derivedProjectionFormulaIso` is Equation
21.50.0.1. -/
@[simp]
theorem derivedProjectionFormulaIso_hom
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hε : IsIso ((derivedAdjunction f hmos).counit.app M))
    (hη : IsIso ((derivedAdjunction f hmos).unit.app
      ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O)).obj
        ((derivedPushforward f).obj M, K)))) :
    (derivedProjectionFormulaIso f hmos M K hε hη).hom = projectionFormulaMap f hmos M K :=
  rfl

/-- **Stacks 0DK5 in the order the source writes it**,
`K ⊗^L_{𝒪_D} Rf_*M ≅ Rf_*(Lf^*K ⊗^L_{𝒪_C} M)`.

This is `AlgebraicGeometry.Space.derivedProjectionFormulaIso` read through the commutativity
constraint of the derived tensor product (Stacks 0FPT) on each side: on `D(𝒪_D)` to transpose the
source, and inside `Rf_*` on `D(𝒪_C)` to transpose the target. No hypothesis is added. -/
@[stacks 0DK5 "the isomorphism in the source's order of tensor factors, for a morphism of ringed \
  topoi arising from a morphism of sites at a single universe, which is what the derived \
  pullback tensor comparison of 07A4 requires — the small étale ringed topos of an algebraic \
  space does not satisfy this — and given the counit of 07A6 at `M` and its unit at \
  `Rf_*M ⊗^L K`, which is what finiteness of `π` is used for"]
def derivedProjectionFormulaIsoSourceOrder
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hε : IsIso ((derivedAdjunction f hmos).counit.app M))
    (hη : IsIso ((derivedAdjunction f hmos).unit.app
      ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O)).obj
        ((derivedPushforward f).obj M, K)))) :
    ((derivedTensorProductFunctor Y.O).obj K).obj ((derivedPushforward f).obj M) ≅
      (derivedPushforward f).obj
        (((derivedTensorProductFunctor X.O).obj ((derivedPullback f).obj K)).obj M) :=
  (canonicalDerivedTensorProduct Y.O).braidingIso (RingedTopos.toRingedSite Y) K
      ((derivedPushforward f).obj M) ≪≫
    derivedProjectionFormulaIso f hmos M K hε hη ≪≫
      (derivedPushforward f).mapIso
        ((canonicalDerivedTensorProduct X.O).braidingIso (RingedTopos.toRingedSite X) M
          ((derivedPullback f).obj K))

end AlgebraicGeometry.Space

end
