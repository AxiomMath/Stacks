module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint

/-!
# Direct sums in `D_QCoh` of an arbitrary scheme, and the twisted inverse image

Let `X` be a scheme. [Stacks, Tag 08DT] says that `D_QCoh(𝒪_X)` has direct sums: direct sums in
`D(𝒪_X)` are computed termwise, cohomology commutes with them because it is exact in a
Grothendieck abelian category, and a direct sum of quasi-coherent modules is quasi-coherent.

Both inputs are now available for an arbitrary scheme — the abstract half as
`Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts`, which asks for a weak Serre
subcategory closed under direct sums, and the two hypotheses it asks for as
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre` and
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma`. The companion file
`StacksFrontier/AlgebraicGeometry/Duality/QuasiCoherentAdjoint.lean` proves the same statements over
an affine base only, because the weak Serre input was available only there.

Together with
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated` this
discharges three of the five hypotheses of
`Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward` for an arbitrary morphism of
schemes, leaving the three inputs [Stacks, Tag 0A9E] derives from quasi-compactness and
quasi-separatedness: Tags 08D5, 08DZ and 09IS.

## Main results

* `Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory` — `D_QCoh(𝒪_X)`
  has direct sums indexed by any type of the scheme universe, for an arbitrary scheme `X`.
* `Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator`:
  the Stacks proof of [Stacks, Tag 0A9E] for an arbitrary morphism of schemes, with the
  triangulated-subcategory and direct-sum inputs discharged.

## Implementation notes

The index universe is the scheme universe `u`, which is also the morphism universe of the derived
category in force (`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`), so what comes out is
exactly the `HasCoproducts.{u}` that Brown representability ([Stacks, Tag 0A8G]) asks for. With
`HasDerivedCategory.standard` instead, the morphisms of `D(𝒪_X)` would live in `Type (u + 1)`
while its direct sums are only `Type u`-indexed, so the hypothesis would be false rather than
unavailable and the conclusion vacuous.

No `@[stacks]` attribute is attached. Tag 08DT is stated here for the index types of one
universe rather than for arbitrary index sets, and Tag 0A9E's statement — that `Rf_*` has a right
adjoint for a morphism of quasi-compact, quasi-separated schemes with no further hypotheses — is
not reached: `isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator` still carries
Tags 08D5, 08DZ and 09IS as hypotheses. A tag on either declaration would report an open tag as
formalized.

## References

* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite

universe u

namespace Stacks.Duality.DerivedPushforward

open Stacks.AlgebraicGeometry.QuasicoherentColimits
open Stacks.AlgebraicGeometry.QuasicoherentWeakSerre

variable (X : Scheme.{u})

/-! ### Direct sums in `D_QCoh` of an arbitrary scheme -/

/-- The direct sum of a family of quasi-coherent `𝒪_X`-modules is quasi-coherent, in the form
that `Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts` consumes. -/
theorem isQuasicoherent_sigmaObj {J : Type u} (M : J → X.Modules)
    (hM : ∀ j, SheafOfModules.isQuasicoherent X.ringCatSheaf (M j)) :
    SheafOfModules.isQuasicoherent X.ringCatSheaf (∐ M) :=
  have (j : J) : (M j).IsQuasicoherent := hM j
  isQuasicoherent_sigma M

/-- **`D_QCoh(𝒪_X)` is closed under direct sums** indexed by any type of the scheme universe:
cohomology commutes with direct sums in a Grothendieck abelian category, and the quasi-coherent
modules form a weak Serre subcategory closed under them. This is [Stacks, Tag 08DT] for an
arbitrary scheme. -/
theorem derivedQuasicoherent_isClosedUnderCoproducts (J : Type u) :
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderColimitsOfShape
      (Discrete J) :=
  Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts _ _ (isQuasicoherent_isWeakSerre X)
    (isQuasicoherent_sigmaObj X)

/-- **`D_QCoh(𝒪_X)` has direct sums** indexed by any type of the scheme universe — which is also
the morphism universe of the derived category in force, so this is the hypothesis Brown
representability ([Stacks, Tag 0A8G]) asks for. -/
instance hasColimitsOfShape_discrete_quasiCoherentDerivedCategory (J : Type u) :
    HasColimitsOfShape (Discrete J) (Stacks.Duality.quasiCoherentDerivedCategory X) :=
  have := derivedQuasicoherent_isClosedUnderCoproducts X J
  inferInstance

/-- `D_QCoh(𝒪_X)` has all direct sums indexed by the scheme universe, for an arbitrary scheme
`X`. -/
theorem hasCoproducts_quasiCoherentDerivedCategory :
    HasCoproducts.{u} (Stacks.Duality.quasiCoherentDerivedCategory X) :=
  fun J => hasColimitsOfShape_discrete_quasiCoherentDerivedCategory X J

/-! ### The twisted inverse image -/

/-- **The Stacks proof of [Stacks, Tag 0A9E] for an arbitrary morphism of schemes.** Let
`f : X ⟶ Y` be a morphism of schemes and suppose derived direct image preserves quasi-coherent
cohomology. If the restricted derived direct image is exact and commutes with direct sums, and
`D_QCoh(𝒪_X)` is compactly generated by a family `E`, then it has a right adjoint — the twisted
inverse image `f^×`.

Compared with `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward` this discharges
three hypotheses: that `D_QCoh` is a triangulated subcategory on either side, which is
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated`, and that
`D_QCoh(𝒪_X)` has direct sums, which is `hasCoproducts_quasiCoherentDerivedCategory`. What
remains are the three inputs the source derives from quasi-compactness and quasi-separatedness of
`f`: Tags 08D5, 08DZ and 09IS. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [(Stacks.Duality.quasiCoherentDerivedPushforward f hpush).CommShift ℤ]
    [(Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsTriangulated]
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)]
    {ι : Type u} (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X)
    [∀ (i : ι) (α : Type u),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X,
      ((ofObj E).shiftClosure ℤ).rightOrthogonal K → IsZero K) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  have := hasCoproducts_quasiCoherentDerivedCategory X
  Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward f hpush E hE

end Stacks.Duality.DerivedPushforward

end
