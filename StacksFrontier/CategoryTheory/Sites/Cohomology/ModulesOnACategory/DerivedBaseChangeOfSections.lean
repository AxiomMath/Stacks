module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentCohomologyUnderFlatRestrictions

/-!
# The base-change condition without flatness

Let `C` be a category viewed as a site with the chaotic topology and let `O` be a presheaf of
rings on `C` whose section rings are commutative. For `a : V ⟶ U` in `Cᵒᵖ` the cartesian
condition of Stacks 0GYV on an object `K` of `D(O)` is the invertibility of
`comparison bc a K : RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)`, which is by definition an adjoint
transpose under the base-change datum `bc`. Statements about derived base change on *complexes* —
Stacks 0GYI among them — instead speak of the invertibility of `α.app M ≫ Q.map b`, where `α`
presents a total left derived functor of termwise extension of scalars and `b` is a map of
complexes out of that termwise extension.

This file identifies the two for an object in the image of `DerivedCategory.Q`. Nothing here
assumes the restriction homomorphism `O(V) → O(U)` is flat; that hypothesis is what
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.isIso_comparison_iff` needs and avoids, by
using the exactness of extension of scalars to descend it to derived categories as it stands
instead of deriving it.

## Main results

* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_homEquiv_symm`: the
  adjoint transpose, under the adjunction between a left derived model of extension of scalars and
  derived restriction of scalars, of a morphism of the form `Q(g)` followed by the factorization of
  derived restriction of scalars: it is the comparison of the model, followed by `Q` of the
  degreewise adjoint transpose of `g`.
* `Stacks.ModulesOnACategory.CartesianObjects.isIso_comparison_Q_iff_isLeftDerived`: the canonical
  comparison map at `Q(P^•)` is invertible exactly when `α` followed by `Q` of the base-change map
  of sections of `P^•` is.

## Implementation notes

The two halves of the identification are already available and neither is about flatness. That
invertibility of the transpose does not depend on which left adjoint of derived restriction of
scalars forms it is
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.isIso_homEquiv_symm_iff`; it is what allows the
abstract `bc.baseChange a` to be replaced by a left derived model. That the counit of the derived
adjunction involves nothing beyond the degreewise counit is
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`; it is
what makes the transpose computable, and it is the only place where being a left *derived* functor
rather than an exact one enters.

The first result is therefore the exact analogue, for a left derived functor, of
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.mapDerivedCategory_homEquiv_symm`, and the
second has the same proof as
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.isIso_comparison_Q_iff` with the former put in
place of the latter.

Commutativity of the two section rings is unavoidable and is not a hypothesis beyond those of the
source: extension of scalars `M ↦ M ⊗_{O(V)} O(U)` requires a commutative `O(V)`, so there is no
base change along a restriction map of `O` without it. It is introduced as
`Stacks.ModulesOnACategory.CartesianObjects.commRingOfComm`, which keeps the underlying ring
structure of `RingCat`, so that the module categories involved are the ones `D(O)` is built from.

## References

* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.QuasiCoherentCohomology (isIso_homEquiv_symm_iff sectionsBaseChange)

namespace CochainComplex.DerivedExtensionScalars

universe uR uA uM wR wA

/-- **The adjoint transpose under the derived extension–restriction adjunction.** Let
`f : R →+* A` be a homomorphism of commutative rings, let `F` be a total left derived model of
extension of scalars with comparison `comparison`, and let `g : X^• ⟶ Y^•|_R` be a map of
complexes into the restriction of scalars of `Y^•`. The adjoint transpose of `g`, formed in the
derived categories under `derivedExtensionScalarsAdjunction`, is the comparison of the model at
`X^•` followed by `Q` of the degreewise adjoint transpose of `g`.

This is the analogue, for a left derived functor, of
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.mapDerivedCategory_homEquiv_symm`, which
computes the same transpose when extension of scalars is exact and so needs no derived correction.
Only the normalization of the derived counit
(`derivedExtensionScalarsAdjunction_counit_app_eq`) and the naturality of `comparison` enter. -/
public theorem derivedExtensionScalarsAdjunction_homEquiv_symm
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (Y : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (g : X ⟶ ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Y),
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv
          (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y)).symm
        (DerivedCategory.Q.map g ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
            f).mapDerivedCategoryFactors.inv.app Y) =
      comparison.app X ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv X Y |>.symm g) := by
  let _ : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let _ : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  let _ : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let _ : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
  intro F comparison hF X Y g
  have := hF
  have hnat : F.map (DerivedCategory.Q.map g) ≫
      comparison.app (((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Y) =
      comparison.app X ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) :=
    comparison.naturality g
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    derivedExtensionScalarsAdjunction_counit_app_eq.{uR, uA, uM} f F comparison Y,
    ← Category.assoc (F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
      f).mapDerivedCategoryFactors.inv.app Y)) (F.map _), ← F.map_comp, Iso.inv_hom_id_app,
    F.map_id, Category.id_comp, ← Category.assoc, hnat, Category.assoc,
    ← DerivedCategory.Q.map_comp, Adjunction.homEquiv_counit]

end CochainComplex.DerivedExtensionScalars

namespace Stacks.ModulesOnACategory.CartesianObjects

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-- **The base-change condition on a complex, without flatness.** Let `a : V ⟶ U` in `Cᵒᵖ`, with
`O(V)` and `O(U)` commutative, let `T` be a total left derived model of extension of scalars along
`O(V) → O(U)` with comparison `α`, and let `bc` be a derived base-change datum for `O`. Then the
canonical comparison map `RΓ(V, Q(P^•)) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, Q(P^•))` is an isomorphism exactly
when `α` at `P^•(V)`, followed by `Q` of the base-change map of sections of `P^•`, is.

The left-hand condition is `IsQC bc` at `a`, and the right-hand one is the hypothesis and the
conclusion of Stacks 0GYI. Invertibility of the left-hand map does not depend on the choice of
`bc`, by `isIso_homEquiv_symm_iff`; which left adjoint of derived restriction of scalars forms the
transpose is immaterial, and taking it to be `T` makes the transpose computable through
`derivedExtensionScalarsAdjunction_homEquiv_symm`.

Unlike `Stacks.ModulesOnACategory.QuasiCoherentCohomology.isIso_comparison_iff`, no flatness of
the restriction homomorphism is assumed: extension of scalars is not required to be exact, only to
have a left derived functor, which it always has. -/
public theorem isIso_comparison_Q_iff_isLeftDerived {U V : Cᵒᵖ} (a : V ⟶ U)
    (hV : ∀ x y : O.obj V, x * y = y * x) (hU : ∀ x y : O.obj U, x * y = y * x) :
    letI := commRingOfComm (O.obj V) hV
    letI := commRingOfComm (O.obj U) hU
    letI : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).left_adjoint_additive
    ∀ (T : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max u v r w} (O.obj V)))
      (DerivedCategory (ModuleCat.{max u v r w} (O.obj U))))
    (α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v r w} (O.obj V)) (ComplexShape.up ℤ))]
    (bc : BaseChangeData.{w} O)
    (P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ),
    IsIso (comparison.{w} bc a (DerivedCategory.Q.obj P)) ↔
      IsIso (α.app (((PresheafOfModules.evaluation.{max u v r w} O V).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (sectionsBaseChange.{w} O a
            (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom))
          (ComplexShape.up ℤ)).app P)) := by
  let := commRingOfComm (O.obj V) hV
  let := commRingOfComm (O.obj U) hU
  let : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).isLeftAdjoint
  let : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).left_adjoint_additive
  intro T α hT bc P
  have := hT
  unfold comparison
  rw [isIso_homEquiv_symm_iff (bc.baseChangeAdj a)
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{r, r,
        max u v w} (O.map a).hom T α),
    restrictionMap_Q]
  simp only [← Category.assoc, Adjunction.homEquiv_naturality_right_symm, isIso_comp_right_iff]
  rw [Category.assoc, Adjunction.homEquiv_naturality_left_symm, isIso_comp_left_iff]
  dsimp only [Functor.comp_obj]
  rw [CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_homEquiv_symm.{r, r,
    max u v w} (O.map a).hom T α]
  exact Iff.rfl

end Stacks.ModulesOnACategory.CartesianObjects

end
