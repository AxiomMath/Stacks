module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# Being a dualizing complex does not depend on the model of the derived category

The derived category of `𝒪_X`-modules is used at two models in this repository: the standard one,
`HasDerivedCategory.standard`, with morphisms in `Type (u + 1)`, and the locally small one of
[Stacks, Tag 079Q], `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, with morphisms in
`Type u`. The second is obtained from the first by shrinking the morphism types, so both have the
same objects (`StacksDraft.DerivedModel.derivedCategory_eq_standard`), and an object of one is an
object of the other. This file shows that the two readings of such an object agree on what
matters for dualizing complexes: its cohomology sheaves, and being a dualizing complex
([Stacks, Tag 0A87]).

## Main definitions

* `Stacks.Duality.homologyModelIso`: the cohomology sheaves of an object of the derived category
  computed at the standard model and at the locally small model are isomorphic.

## Main results

* `Stacks.Duality.hasDualizingModelOn_standard_iff`: carrying a dualizing model on an affine open
  does not depend on the model.
* `Stacks.Duality.isDualizingComplex_standard_iff`: being a dualizing complex does not depend on
  the model.

## Implementation notes

Both comparisons are uniqueness of lifts along a localization functor: the cohomology functor and
the derived restriction functor are lifts of functors on cochain complexes along the localization
functor of their source model, and the two localization functors agree on the nose after the
comparison equivalence `Stacks.Injectives.grothendieckModelEquiv`, which is the identity on
objects. The derived restriction comparison is `Stacks.Injectives.mapDerivedCategoryObjIso`.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-- **The cohomology sheaves do not depend on the model.** For an object `K` of the derived
category of `𝒪_X`-modules — an object of the standard model, which is also an object of the
locally small model — the `n`-th cohomology sheaf computed at the standard model is isomorphic to
the one computed at the locally small model. -/
def homologyModelIso (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) (n : ℤ) :
    (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).obj K ≅
      (DerivedCategory.homologyFunctor X.Modules n).obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor.obj K) :=
  letI inst := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} X.Modules
  letI : Localization.Lifting (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _))
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) n)
      ((Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor ⋙
        @DerivedCategory.homologyFunctor X.Modules _ _ inst n) :=
    ⟨@DerivedCategory.homologyFunctorFactors X.Modules _ _ inst n⟩
  letI : Localization.Lifting (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _))
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) n)
      (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) n) :=
    ⟨@DerivedCategory.homologyFunctorFactors X.Modules _ _ (HasDerivedCategory.standard _) n⟩
  (Localization.liftNatIso (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _))
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) n)
    (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) n)
    ((Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor ⋙
      @DerivedCategory.homologyFunctor X.Modules _ _ inst n) (Iso.refl _)).app K

variable [IsLocallyNoetherian X]

/-- **Carrying a dualizing model on an affine open does not depend on the model** of the derived
category of `𝒪_X`-modules: the derived restriction to the open computed at the two models agree
at every object (`Stacks.Injectives.mapDerivedCategoryObjIso`). -/
theorem hasDualizingModelOn_standard_iff
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) (U : X.Opens)
    (hU : IsAffineOpen U) :
    @HasDualizingModelOn X _ (HasDerivedCategory.standard _) K U hU ↔
      HasDualizingModelOn ((Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor.obj K)
        U hU := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  have e := Stacks.Injectives.mapDerivedCategoryObjIso.{u} X.Modules
    (Scheme.Modules.restrictFunctor U.ι) K
  constructor
  · rintro ⟨ω, hω, ⟨i⟩⟩
    exact ⟨ω, hω, ⟨e.symm ≪≫ i⟩⟩
  · rintro ⟨ω, hω, ⟨i⟩⟩
    exact ⟨ω, hω, ⟨e ≪≫ i⟩⟩

/-- **Being a dualizing complex does not depend on the model** of the derived category of
`𝒪_X`-modules ([Stacks, Tag 0A87]). -/
theorem isDualizingComplex_standard_iff
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) :
    @IsDualizingComplex X _ (HasDerivedCategory.standard _) K ↔
      IsDualizingComplex ((Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor.obj K) :=
  forall₂_congr fun U hU => hasDualizingModelOn_standard_iff K U hU

end Stacks.Duality

end
