module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`

Let `X` be a scheme. The quasi-coherent `𝒪_X`-modules form a weak Serre subcategory of all
`𝒪_X`-modules, so `QCoh(𝒪_X)` is abelian and its inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is exact.
An exact functor induces a functor of unbounded derived categories, and the cohomology sheaves of
`ι(K)` are the images under `ι` of the cohomology objects of `K`, hence quasi-coherent. The
induced functor therefore factors through the strictly full subcategory
`D_QCoh(𝒪_X) ⊆ D(𝒪_X)` of complexes with quasi-coherent cohomology, and the factorisation is the
canonical comparison functor of [Stacks, Tag 06VT]. It commutes with translation and is exact for
the triangulated structures.

## Main definitions

* `Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison` — the comparison
  functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`.

## Main results

* `Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison_mem` — the derived
  inclusion lands in `D_QCoh(𝒪_X)`, which is what makes the comparison exist.
* `Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonCommShift` and
  `Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonIsTriangulated` —
  the comparison commutes with translation and preserves distinguished triangles.
* `Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonCompι` — composing
  the comparison with the inclusion of `D_QCoh(𝒪_X)` recovers the derived inclusion.

## Implementation notes

The two derived categories are left as instance arguments rather than pinned to
`CategoryTheory.HasDerivedCategory.standard`. That model puts the morphisms of `D(𝒪_X)` one
universe above its objects, which makes the direct sums appearing in Stacks 09IS and 0A9A *false*
rather than merely unavailable (see the implementation notes of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`); since the comparison functor is an
input to those statements, fixing the standard model here would make it unusable for them.
Leaving the instance free means the statements hold in particular at
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the locally small model, and at the
standard one.

Everything is phrased over `SheafOfModules.{u} X.ringCatSheaf` rather than
`AlgebraicGeometry.Scheme.Modules`. The two are definitionally equal but carry separately
declared `Category`, `Preadditive` and `Abelian` instances; this is the spelling in which
`SheafOfModules.isQuasicoherent X.ringCatSheaf` and
`AlgebraicGeometry.quasicoherentModules_abelian` are stated.

That `D_QCoh(𝒪_X)` is triangulated is re-derived here, at the ambient derived category of the
section, from `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre` and
Stacks 06UP. The instance in that file is stated at the global locally small derived category and
so does not apply to a free `HasDerivedCategory` argument.

## References

* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w u

namespace Stacks.AlgebraicGeometry.QuasicoherentDerived

variable (X : Scheme.{u})

/-! ### Exactness of the inclusion of quasi-coherent modules -/

/-- The inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` preserves finite limits, quasi-coherence being a weak
Serre subcategory. -/
instance isQuasicoherent_ι_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` preserves finite colimits, quasi-coherence being a weak
Serre subcategory. -/
instance isQuasicoherent_ι_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  preservesFiniteColimits_ι_of_isWeakSerreClass _

/-! ### The comparison functor -/

variable [HasDerivedCategory.{w} (SheafOfModules X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]

/-- `D_QCoh(𝒪_X)` is a strictly full saturated triangulated subcategory of `D(𝒪_X)`, by Stacks
06UP applied to the weak Serre subcategory of quasi-coherent modules. -/
instance isTriangulated_derivedQuasicoherent :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)

/-- **The derived inclusion of quasi-coherent modules has quasi-coherent cohomology in every
degree.** The inclusion `ι` is exact, so `Hⁿ(ι K) ≅ ι (Hⁿ K)`, and the right-hand side is
quasi-coherent by construction. This is what allows the derived inclusion to be factored through
`D_QCoh(𝒪_X)`. -/
theorem derivedQuasicoherentComparison_mem
    (K : DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.obj K) := fun n =>
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι n).app K).symm
    ((DerivedCategory.homologyFunctor _ n).obj K).2

/-- **Stacks 06VT.** The canonical comparison functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` from the
derived category of quasi-coherent `𝒪_X`-modules to the complexes of `𝒪_X`-modules with
quasi-coherent cohomology: the derived functor of the exact inclusion, factored through
`D_QCoh(𝒪_X)`. -/
@[stacks 06VT "comparison functor"]
def derivedQuasicoherentComparison :
    DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).lift
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory
    (derivedQuasicoherentComparison_mem X)

/-- **Stacks 06VT.** The comparison functor is compatible with translation of complexes. -/
@[stacks 06VT "shift compatibility"]
instance derivedQuasicoherentComparisonCommShift :
    (derivedQuasicoherentComparison.{w} X).CommShift ℤ :=
  inferInstanceAs
    (((DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).lift
      _ (derivedQuasicoherentComparison_mem X)).CommShift ℤ)

/-- **Stacks 06VT.** The comparison functor preserves distinguished triangles, so it is an exact
functor of triangulated categories. -/
@[stacks 06VT "exactness"]
instance derivedQuasicoherentComparisonIsTriangulated :
    (derivedQuasicoherentComparison.{w} X).IsTriangulated :=
  inferInstanceAs
    (((DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).lift
      _ (derivedQuasicoherentComparison_mem X)).IsTriangulated)

/-- Forgetting the quasi-coherence condition after comparison gives back the derived functor of
the inclusion of quasi-coherent modules. -/
def derivedQuasicoherentComparisonCompι :
    derivedQuasicoherentComparison.{w} X ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

end Stacks.AlgebraicGeometry.QuasicoherentDerived

end
