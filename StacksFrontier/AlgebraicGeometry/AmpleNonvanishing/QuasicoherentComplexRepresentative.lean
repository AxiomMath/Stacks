module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDiagonalEquivalence

/-!
# Presenting an object of `D_QCoh(𝒪_X)` by a complex of quasi-coherent modules

[Stacks, Tag 08DB] says that on a quasi-compact scheme with affine diagonal the comparison
functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT] is an equivalence. The
argument of [Stacks, Tag 0BQR] uses that in one specific shape: it needs an actual *cochain
complex* `G` of quasi-coherent `𝒪_X`-modules whose class in `D(𝒪_X)` is the given object, so
that a cocycle of `G` in a degree can be written down and twisted. This file assembles that
shape out of the equivalence.

## Main results

* `Stacks.AmpleNonvanishing.exists_quasicoherentComplex_iso`: **[Stacks, Tag 08DB] in the form
  the cocycle argument of [Stacks, Tag 0BQR] consumes.** On a quasi-compact scheme with affine
  diagonal every object of `D_QCoh(𝒪_X)` is isomorphic, in `D(𝒪_X)`, to the class of a cochain
  complex of quasi-coherent `𝒪_X`-modules.

## Implementation notes

Three steps, none of them new mathematics. The comparison functor is an equivalence, hence
essentially surjective, so the given object is `i_X E`; the localization functor
`DerivedCategory.Q` is essentially surjective, so `E` is the class of a cochain complex `G` of
quasi-coherent modules; and `i_X` followed by the inclusion of `D_QCoh(𝒪_X)` is
`Functor.mapDerivedCategory` of the inclusion of the quasi-coherent modules
(`Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonCompι`), which on
a class of a complex is the class of that complex read in all `𝒪_X`-modules
(`CategoryTheory.Functor.mapDerivedCategoryFactors`).

The derived categories are the ones the free `HasDerivedCategory.{w}` binders of
`Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison` default to,
namely the locally small model at `w := u`; this is the model [Stacks, Tag 08DB] is available
at. No statement here mentions a derived tensor product, so no second model is involved.

## References

* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace Stacks.AmpleNonvanishing

/-- **[Stacks, Tag 08DB], as the cocycle argument of [Stacks, Tag 0BQR] uses it.** On a
quasi-compact scheme with affine diagonal every object `K` of `D_QCoh(𝒪_X)` is isomorphic in
`D(𝒪_X)` to the class of a cochain complex `G` of quasi-coherent `𝒪_X`-modules. -/
theorem exists_quasicoherentComplex_iso (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (K : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory) :
    ∃ G : CochainComplex
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ℤ,
      Nonempty (K.1 ≅ DerivedCategory.Q.obj
        (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)) := by
  let := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal X
  set F := derivedQuasicoherentComparison.{u} X with hF
  let E := F.objPreimage K
  refine ⟨DerivedCategory.Q.objPreimage E, ⟨?_⟩⟩
  refine (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.mapIso
    (F.objObjPreimageIso K).symm ≪≫ ?_
  exact (derivedQuasicoherentComparisonCompι.{u} X).app E ≪≫
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategoryFactors).app _

end Stacks.AmpleNonvanishing

end
