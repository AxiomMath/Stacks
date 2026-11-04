module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorHomAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorMonoidalLift

/-!
# The cochain-level comparison of internal Hom complexes along a morphism of ringed spaces

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  This file builds the canonical map

`h^*𝓗om^•_{𝒪_Y}(E, F) ⟶ 𝓗om^•_{𝒪_X}(h^*E, h^*F)`

of complexes of `𝒪_X`-modules, for cochain complexes `E`, `F` of `𝒪_Y`-modules.  It is the
abstract transpose construction that Tag 08I3 is built from —
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` — instantiated at the
*monoidal closed structure on `Comp(Mod(𝒪))`* rather than at the derived categories, with the
monoidality comparison of Tag 01CD on total tensor complexes
(`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso`) in place of the
monoidality comparison of Tag 079U.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivComplex`: the tensor–internal-hom
  bijection of `Comp(Mod(𝒪_Z))`, in the shape the abstract transpose construction asks for.
* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackSheafHomComplexMap`: **the cochain-level
  comparison** `h^*𝓗om^•(E, F) ⟶ 𝓗om^•(h^*E, h^*F)`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackSheafHomComplexMap_adjoint`: the
  transpose of the comparison is the monoidality comparison followed by `h^*` of the evaluation,
  which pins the comparison down.
* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackSheafHomComplexMap_eq_curryingSpelling`:
  the comparison read at the `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex`
  abbreviation for the monoidal-closed internal hom is the same map.  This is a type ascription
  *inside* the monoidal-closed development and nothing more; see the implementation notes for
  what it is **not**.

## Nothing here is tagged

The map built here is a step of the *proof* of Tag 0GM7, not a clause of any published statement:
the published map is the derived one, `derivedPullbackSheafHomMap` of
`…DerivedPushforward.InternalHomPullbackMap`, which already carries `@[stacks 08I3]`.  So no
declaration below carries a tag.

## Relation to the Tag 0A8Z spelling

This comparison runs between the monoidal-closed internal homs `(ihom E).obj F`, not between the
internal Hom complexes `AlgebraicGeometry.RingedSite.sheafHomComplex` of Tag 0A8Z (see the
implementation notes below). The same recipe at the Tag 0A8Z complexes, `Transpose.homComparison`
at `sheafHomComplexBifunctor` with `AlgebraicGeometry.RingedSite.curryHomEquivPair` on both sides,
is `Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackHomComplexMap`.
The map built here is the one at the monoidal-closed internal hom, the spelling its own
monoidality input is stated at.

## Implementation notes

*The instance seating, and the clash it avoids.*  Complexes of `𝒪`-modules carry several monoidal
and several closed structures, so neither is a global instance; the recipe for seating them is the
one in `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorHomAdjunction`, and the
implementation notes there record why each instance of a ringed-space section has to be *applied
by name with its site written out* rather than synthesized: over `Opens X` the universe of the
site and the universe of the sections of `𝒪_X` coincide, and instance search then has to solve
`max ?u ?v =?= u` with both unknown.

Both monoidal structures here are taken from the `sheafTensor` development
(`SheafOfModules.monoidalCategorySheafTensor` on modules,
`Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory` on complexes).
The `Strict` structure `Stacks.SheafOfModules.Strict.monoidalCategoryCochainComplex` on complexes
is a different monoidal structure on the same category: seated next to `sheafTensor` on modules,
`CochainComplex.monoidalClosed` and the braiding `β_` land at the wrong structure.

*Why `tensorHomEquivComplex` is built from `ihom.adjunction` and the braiding.*  The abstract
transpose construction asks for a bijection `(A ⟶ hom(B, C)) ≃ (T(A, B) ⟶ C)` with the tensor
factor `B` on the *right*, whereas Mathlib's `ihom.adjunction B : tensorLeft B ⊣ ihom B` puts it
on the left.  The two are traded by the braiding, which is where the symmetry of `⊗_{𝒪_Z}` enters.

*The total tensor complex is the monoidal product on the nose — and the internal hom is NOT the
internal Hom complex of Tag 0A8Z.*  On the tensor side,
`(totalComplexPair (sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, L) = K ⊗ L` holds by `rfl`
(`totalComplexPair_obj_eq_tensorObj`), and `((Tensor.tensorComplex Z.sheaf).obj K).obj L` equals
`(totalComplexPair (sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, L)` by `rfl` as well, which is
what lets the comparison be stated at the uncurried pair functor that `pullbackTensorComplexNatIso`
is given at.

On the Hom side the corresponding statement is **false**.
`(MonoidalClosed.internalHom.obj (op K)).obj L = sheafHomComplex Z.sheaf K L` holds by `rfl`
only because `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex` is an
*abbreviation for `(ihom K).obj L`* — the very internal hom on the left.  It is **not** the
internal Hom complex `AlgebraicGeometry.RingedSite.sheafHomComplex` of Tag 0A8Z, which is a
different complex: `ihom` is a degreewise sheafification of a presheaf Hom, while the internal Hom
sheaf of Tag 03EM is already a sheaf.  Giving `pullbackSheafHomComplexMap h E F` the Tag 0A8Z type
`(pullbackComplex h).obj (RingedSite.sheafHomComplex (ringedSite Y.sheaf) E F).obj ⟶ …` is a
**type mismatch**, machine-checked.  So the comparison built here does *not* reach the Hom
complexes Tag 08DM is stated at: `Stacks.SheafOfModules.strictlyPerfectHomComparison` is stated at
`RingedSite.sheafHomComplex`, and the two developments are joined by no isomorphism of complexes —
`AlgebraicGeometry.RingedSite.ihomIsoInternalHomSheaf` identifies the two internal homs of single
sheaves of modules only, as the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingOnARingedSpace` record.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 0A8M](https://stacks.math.columbia.edu/tag/0A8M)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.SheafHomComplexCurrying

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

-- The pullback/pushforward development and the tensor-product development name the structure
-- sheaf of a ringed space differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`; the two are the same sheaf of rings by `rfl`, and
-- every statement here mixes them, the degreewise pullback being named at one spelling and the
-- total tensor complex at the other.
attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-! ### The monoidal closed structure on `Comp(Mod(𝒪_Z))` -/

section Seating

variable (Z : RingedSpace.{u, u})

attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.monoidalModules
  Stacks.Cohomology.DerivedPullbackTensor.symmetricModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalPreadditiveModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalClosedModules

/-- `- ⊗_{𝒪_Z} 𝒢` commutes with colimits, named for the same reason. -/
local instance preservesColimitTensorRightSpace {T : Type*} [Category T]
    (F : T ⥤ AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)
    (N : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :
    PreservesColimit F (CategoryTheory.MonoidalCategory.tensorRight N) :=
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
    (J := Opens.grothendieckTopology Z.carrier) Z.sheaf F N

attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.hasTensorModules

/-- The left-bracketed triple graded tensor products are good. -/
local instance hasGoodTensor₁₂TensorSpace :
    ∀ A B D : GradedObject ℤ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z),
      GradedObject.HasGoodTensor₁₂Tensor A B D := fun _ _ _ => inferInstance

/-- The right-bracketed triple graded tensor products are good. -/
local instance hasGoodTensorTensor₂₃Space :
    ∀ A B D : GradedObject ℤ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z),
      GradedObject.HasGoodTensorTensor₂₃ A B D := fun _ _ _ => inferInstance

/-- A morphism out of a fourfold graded tensor product is determined on the summands. -/
local instance hasTensor₄ObjExtSpace :
    ∀ A B D E : GradedObject ℤ
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z),
      GradedObject.HasTensor₄ObjExt A B D E := fun _ _ _ _ => inferInstance

/-- The total complexes of the tensor double complexes exist. -/
local instance hasMapBifunctorSpace :
    ∀ K L : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Z.sheaf) (ComplexShape.up ℤ) :=
  fun _ _ => inferInstance

/-- The monoidal structure on `Comp(Mod(𝒪_Z))` whose tensor product is the total tensor complex.
Applied by name with its site written out, for the reason in the implementation notes; taking it
from the `Strict` development instead is the clash recorded there. -/
local instance monoidalComplexSpace :
    MonoidalCategory (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :=
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
    (J := Opens.grothendieckTopology Z.carrier) Z.sheaf

/-- `Comp(Mod(𝒪_Z))` is monoidal closed, with internal hom the internal Hom complex of
Tag 0A8Z. -/
local instance monoidalClosedComplexSpace :
    MonoidalClosed (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :=
  CochainComplex.monoidalClosed
    (A := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)

/-- The total tensor complex is symmetric, by the Koszul symmetry. -/
local instance symmetricComplexSpace :
    SymmetricCategory (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :=
  CochainComplex.symmetricCategory
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)

/-- The total tensor complex of the pair functor is the monoidal product of `Comp(Mod(𝒪_Z))`. -/
theorem totalComplexPair_obj_eq_tensorObj (K L : CochainComplex
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Z.sheaf)).obj (K, L) =
      K ⊗ L := rfl

/-- The internal hom of `Comp(Mod(𝒪_Z))` is the internal Hom complex of Tag 0A8Z. -/
theorem internalHom_obj_obj_eq_sheafHomComplex (K L : CochainComplex
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (MonoidalClosed.internalHom.obj (op K)).obj L = sheafHomComplex Z.sheaf K L := rfl

/-- **The tensor–internal-hom bijection of `Comp(Mod(𝒪_Z))`**, in the shape the abstract
transpose construction of Tag 08I3 asks for: the tensor factor on the right, so that the
monoidal-closed adjunction `ihom.adjunction` — which puts it on the left — is read through the
braiding.  It is the cochain-level counterpart of the bijection of Tag 08DI, which is
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquiv`. -/
def tensorHomEquivComplex
    (A B C : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (A ⟶ ((MonoidalClosed.internalHom.obj (op B)).obj C)) ≃
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Z.sheaf)).obj (A, B) ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    (Iso.homCongr (β_ A B).symm (Iso.refl C))

end Seating

/-! ### The comparison -/

section Comparison

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.monoidalModules
  Stacks.Cohomology.DerivedPullbackTensor.symmetricModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalPreadditiveModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalClosedModules
  preservesColimitTensorRightSpace Stacks.Cohomology.DerivedPullbackTensor.hasTensorModules
  hasGoodTensor₁₂TensorSpace
  hasGoodTensorTensor₂₃Space hasTensor₄ObjExtSpace hasMapBifunctorSpace
  monoidalComplexSpace monoidalClosedComplexSpace symmetricComplexSpace

/-- **The cochain-level comparison of internal Hom complexes along a morphism of ringed
spaces**, `h^*𝓗om^•_{𝒪_Y}(E, F) ⟶ 𝓗om^•_{𝒪_X}(h^*E, h^*F)`.

It is the abstract transpose construction of Tag 08I3 instantiated at the monoidal closed
structure on `Comp(Mod(𝒪))` rather than at the derived categories, with the monoidality
comparison of Tag 01CD on total tensor complexes in place of the one of Tag 079U.  So it is the
cochain-level counterpart of `derivedPullbackSheafHomMap`, built from the same recipe. -/
def pullbackSheafHomComplexMap
    (E F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackComplex h).obj ((MonoidalClosed.internalHom.obj (op E)).obj F) ⟶
      (MonoidalClosed.internalHom.obj (op ((pullbackComplex h).obj E))).obj
        ((pullbackComplex h).obj F) :=
  Transpose.homComparison
    (pullbackComplex h) MonoidalClosed.internalHom MonoidalClosed.internalHom
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))
    (tensorHomEquivComplex Y) (tensorHomEquivComplex X)
    (pullbackTensorComplexNatIso h) E F

/-- **The transpose of the cochain-level comparison is the transpose datum**: the monoidality
comparison of Tag 01CD followed by `h^*` of the evaluation `𝓗om^•(E, F) ⊗ E ⟶ F`.  The
tensor–internal-hom bijection being a bijection, this pins the comparison down — so the
construction above is not satisfiable by a degenerate map.

This is `Transpose.homComparison_adjoint` at the cochain-level data. -/
theorem pullbackSheafHomComplexMap_adjoint
    (E F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    tensorHomEquivComplex X
        ((pullbackComplex h).obj ((MonoidalClosed.internalHom.obj (op E)).obj F))
        ((pullbackComplex h).obj E) ((pullbackComplex h).obj F)
        (pullbackSheafHomComplexMap h E F) =
      Transpose.homComparisonDatum (pullbackComplex h) MonoidalClosed.internalHom
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))
        (tensorHomEquivComplex Y) (pullbackTensorComplexNatIso h) E F :=
  Transpose.homComparison_adjoint
    (pullbackComplex h) MonoidalClosed.internalHom MonoidalClosed.internalHom
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))
    (tensorHomEquivComplex Y) (tensorHomEquivComplex X)
    (pullbackTensorComplexNatIso h) E F

/-- **The comparison read at the `SheafHomComplexCurrying` spelling of the monoidal-closed
internal hom.**  `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex Z.sheaf K L` is an
abbreviation for `(ihom K).obj L`, so this is a **type ascription inside the monoidal-closed
development**: both sides of the `rfl` are the same term `(ihom E).obj F`.

It is recorded only so that a statement written at the `sheafHomComplex` spelling can be fed the
comparison without unfolding the abbreviation.  **It does not reach Tag 08DM.**  The Hom complexes
of Tag 0A8Z are `AlgebraicGeometry.RingedSite.sheafHomComplex`, a different complex; ascribing
`pullbackSheafHomComplexMap` the corresponding type is a type mismatch.  See the implementation
notes above, and `AlgebraicGeometry.RingedSite.curryHomEquivPair` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv` for the datum that lets
`Transpose.homComparison` be instantiated at the Tag 0A8Z/0A90 world instead. -/
theorem pullbackSheafHomComplexMap_eq_curryingSpelling
    (E F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackSheafHomComplexMap h E F :
        (pullbackComplex h).obj (sheafHomComplex Y.sheaf E F) ⟶
          sheafHomComplex X.sheaf ((pullbackComplex h).obj E)
            ((pullbackComplex h).obj F)) =
      pullbackSheafHomComplexMap h E F := rfl

end Comparison

end Stacks.Cohomology.DerivedInternalHomPullback

end
