module

public import StacksFrontier.Cotangent.CotangentDerivedTensorModule
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriekDerived
public import StacksFrontier.Cotangent.Triangle.DerivedFirstVertex
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat

/-!
# The Moore complex of `i^*Ω_{𝒪/A}` tensored with a module

The first vertex of the Atiyah triangle of [Stacks, Tag 09DD] is computed by the extended Moore
complex of the `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` evaluated on the standard resolution, and
the source reads that complex as `L_{B/A} ⊗^𝐋_B M`. This file does that reading.

The `B̲`-module in question is, objectwise, `M ⊗_B -` applied to `i^*Ω_{𝒪/A}`; the computation is
therefore the commutation of the Moore complex with an additive functor applied degreewise,
followed by the case `M = B` which is already proved as
`CommAlgCat.standardResolutionCotangentMooreCochainIso`, followed by the identification of a
degreewise tensor product with a tensor product of complexes.

## Main results

* `Stacks.ChaoticSite.GeneralValued.mooreCochainMapHomologicalComplexIso`: **the extended Moore
  complex commutes with an additive functor applied degreewise.** Before the reindexing into
  cohomological degrees this is Mathlib's `AlgebraicTopology.map_alternatingFaceMapComplex`; the
  reindexing is what makes it an isomorphism rather than an equality, and that part is
  `AlgebraicTopology.alternatingFaceMapCochainComplexCompMapHomologicalComplexIso`.
* `CommAlgCat.smallAtiyahMooreTensorIso`: the extended Moore complex of
  `M ⊗_B i^*Ω_{𝒪/A}` on the standard resolution is `M ⊗_B -` applied degreewise to `L_{B/A}`.
* `CommAlgCat.nonempty_smallAtiyahMooreDerivedTensorIso`: **that complex is
  `L_{B/A} ⊗^𝐋_B M`** in `D(B)`.

## Implementation notes

`Nonempty` in the last statement is inherited from
`CommAlgCat.nonempty_cotangentComplexDerivedTensorModule_iso`, where it comes from the
non-canonical choice of a K-flat resolution; it is the same idiom as
`CommAlgCat.nonempty_derivedExtensionScalars_cotangentTriangle_obj₁_iso` for the analogous first
vertex of Tag 08SD.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicTopology Opposite
open Stacks.ChaoticSite.ModuleValued

universe u

namespace Stacks.ChaoticSite.GeneralValued

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)
  {A A' : Type*} [Category* A] [Category* A'] [Abelian A] [Abelian A']

/-- **The extended Moore complex of `ℱ(U_•)` commutes with an additive functor applied
degreewise.** Before the reindexing of simplicial degree `n` into cohomological degree `-n` this
is the equality `AlgebraicTopology.map_alternatingFaceMapComplex` of Mathlib; the reindexing
contributes `AlgebraicTopology.alternatingFaceMapCochainComplexCompMapHomologicalComplexIso`,
and it is what makes the comparison an isomorphism and not an equality — extension by zero sends
a zero object to only *a* zero object. -/
def mooreCochainMapHomologicalComplexIso (T : A ⥤ A') [T.Additive] (F : Cᵒᵖ ⥤ A) :
    (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((mooreCochainComplex U A).obj F) ≅
      (mooreCochainComplex U A').obj (F ⋙ T) :=
  (AlgebraicTopology.alternatingFaceMapCochainComplexCompMapHomologicalComplexIso T).app
    (U.op ⋙ F)

end Stacks.ChaoticSite.GeneralValued

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (M : ModuleCat.{u} (B : Type u))

/-- **The extended Moore complex of `M ⊗_B i^*Ω_{𝒪/A}` on the standard resolution is `M ⊗_B -`
applied degreewise to the cotangent complex.** The Moore complex commutes with the additive
functor `M ⊗_B -` applied degreewise
(`Stacks.ChaoticSite.GeneralValued.mooreCochainMapHomologicalComplexIso`), and the case `M = B`
is `CommAlgCat.standardResolutionCotangentMooreCochainIso`. -/
def smallAtiyahMooreTensorIso :
    (mooreCochainComplex (standardResolutionSmallCosimplicialObject A B)).obj
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B) ⋙
          tensorLeft M) ≅
      ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, u} A B) :=
  (Stacks.ChaoticSite.GeneralValued.mooreCochainMapHomologicalComplexIso
      (standardResolutionSmallCosimplicialObject A B) (tensorLeft M)
      (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B))).symm ≪≫
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (standardResolutionCotangentMooreCochainIso A B)

/-- **The extended Moore complex of `M ⊗_B i^*Ω_{𝒪/A}` on the standard resolution is
`L_{B/A} ⊗^𝐋_B M`** in `D(B)`. This is the right-hand side of the first identification displayed
in [Stacks, Tag 09DD], reached from the degreewise computation
`CommAlgCat.smallAtiyahMooreTensorIso` through
`StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso`, which turns
the degreewise tensor product into the tensor product of complexes `M[0] ⊗ L_{B/A}`, and
`CommAlgCat.nonempty_cotangentComplexDerivedTensorModule_iso`, which identifies that with the
derived tensor product.

`Nonempty` is inherited from the latter, where it records the non-canonical choice of a K-flat
resolution. -/
theorem nonempty_smallAtiyahMooreDerivedTensorIso :
    Nonempty (DerivedCategory.Q.obj
        ((mooreCochainComplex (standardResolutionSmallCosimplicialObject A B)).obj
          (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B) ⋙
            tensorLeft M)) ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor (B : Type u)).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B))).obj
        (DerivedCategory.Q.obj (moduleSingleComplex A B M))) :=
  (nonempty_cotangentComplexDerivedTensorModule_iso A B M).map fun e =>
    DerivedCategory.Q.mapIso (smallAtiyahMooreTensorIso A B M ≪≫
      (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso
        M (cotangentComplex.{u, u} A B)).symm) ≪≫ e.symm

end CommAlgCat

end
