module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityCanonical
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityReduction

/-!
# The projection-formula compatibility, reduced to one equation at complexes of `A`-modules

`Dualizing.ProjectionFormulaCompatibility` is the one obligation on which
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibility` makes Stacks 0BZP
and both cases of Stacks 0BZM depend, and
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityReduction` reduces
it in the variable `K`: it holds everywhere as soon as it holds at the classes of K-flat complexes
of `R`-modules.  That reduction leaves two objects uncomputed, and they are the ones every factor
of the equation is evaluated at: the derived base change `baseChangeA.obj (RHom_R(A, K))` along
`A → A ⊗_R R'`, and the restriction `RHom_R(A, K)|_R`.  K-flatness of a representative of `K` says
nothing about either.

This file reduces the obligation in the *other* variable.  Both sides of
`Dualizing.projectionFormulaCompatibility_of_algebraActionSquare` — the sufficient condition in
which the evaluation counit of Stacks 0A70 does not occur — depend on `K` only through
`RHom_R(A, K)`, and they are the components at that object of two natural transformations of
functors of an *arbitrary* object `W` of `D(A)`:

`baseChangeA(W)|_{R'} ⊗ᴸ_{R'} (A ⊗ᴸ_R R') ⟶ (W|_R) ⊗ᴸ_R R'`.

One is the `A ⊗_R R'`-action on the restriction of a derived base change, transported by the
comparison of Stacks 0661; the other is the derived base change along `R → R'` of the `A`-action on
`W|_R`.  Their equality is therefore decided at `W = Q N` for `N` a cochain complex of
`A`-modules, and — since the obligation is invariant under isomorphism of `W` as well — at the
classes of **K-flat complexes of `A`-modules**.  At such an `N` the two objects the `K`-variable
reduction left uncomputed become `N ⊗_A (A ⊗_R R')` and `N|_R`.

The transposition in the `K` variable is not what is gained: that was already available and, as
recorded in `…ProjectionCompatibilityReduction`, both transposes of the comparison square of
Stacks 0E2A are available, so transposing again returns to the square.  What is gained is that the
object `RHom_R(A, K)`, which no hypothesis on `K` controls, is replaced by an arbitrary complex of
`A`-modules.

Three witnesses are also recorded, of a shape complementary to
`Dualizing.projectionFormulaCompatibility_of_isZero_baseChange`: there the hypothesis is that the
derived base change of `K` vanishes, here that the *source* of the equation does.  One of them,
`Dualizing.projectionFormulaCompatibility_of_isZero_baseChangeAlgebra`, is a condition on the
square alone and gives the obligation at **every** `K` at once.

## Main definitions

* `Dualizing.restrictionBaseChangeIsoGeneral` — the comparison of Stacks 0661 before it is
  whiskered by `RHom_R(A, -)`; `Dualizing.restrictionBaseChangeIso` is its whiskering.
* `Dualizing.algebraActionSource` — the common source of the two actions, as a functor of the
  object of `D(A)`.
* `Dualizing.algebraActionLeft`, `Dualizing.algebraActionRight` — the two actions as natural
  transformations, and `Dualizing.algebraActionLeftCanonical`,
  `Dualizing.algebraActionRightCanonical` at the canonical models.

## Main results

* `Dualizing.projectionFormulaCompatibility_of_algebraAction` — the obligation at every object of
  `D(R)`, from the equality of the two actions.
* `Dualizing.algebraAction_eq_of_qObj`, `Dualizing.algebraAction_eq_of_resolving`,
  `Dualizing.algebraAction_eq_of_kFlat` — that equality is decided on classes of complexes of
  `A`-modules, on any resolving class of them, and in particular on the K-flat ones.
* `Dualizing.projectionFormulaCompatibility_of_kFlatAlgebraAction` and
  `Dualizing.projectionFormulaCompatibilityCanonical_of_kFlatAlgebraAction` — **the reduction**:
  the obligation at every object of `D(R)`, at arbitrary models and at the canonical ones, from one
  equation at the classes of K-flat complexes of `A`-modules.
* `Dualizing.projectionFormulaCompatibility_of_isZero_restrictionBaseChange`,
  `Dualizing.projectionFormulaCompatibility_of_isZero_baseChangeAlgebra` and their canonical
  forms — witnesses with a zero source.
* `Dualizing.algebraAction_eq_of_isZero_baseChangeAlgebra` — the hypothesis of the reduction is
  inhabited.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.isZero_tensor_obj_left` and
  `.isZero_tensor_obj_right` — a derived tensor product with a zero factor is zero.

## Implementation notes

`Dualizing.restrictionBaseChangeIso` is `Iso.trans` of two associators around the whiskering of the
unwhiskered comparison, and the associators contribute identity components; the component identity
`Dualizing.restrictionBaseChangeIso_hom_app` is therefore one `rfl` followed by
`CategoryTheory.Category.id_comp` and `CategoryTheory.Category.comp_id`.  The two comparisons are
built from the same call to
`RingTheory.TorIndependence.derivedBaseChangeComparison`; the proof of the commuting square of ring
maps and the `IsIso` instance are propositions, so they do not have to be reproduced on the nose.

The two natural transformations are composites of whiskerings only, so
`CategoryTheory.NatTrans.naturality` supplies every naturality square, and their components are the
two sides of `Dualizing.projectionFormulaCompatibility_of_algebraActionSquare` definitionally:
composition of natural transformations, `CategoryTheory.Functor.whiskerLeft` and
`CategoryTheory.Functor.whiskerRight` all compute their components by `rfl`, and the bracketing is
chosen to match.

`Dualizing.algebraAction_eq_of_qObj` is `CategoryTheory.Localization.natTrans_ext` for
`DerivedCategory.Q`, not the universal property of a left derived functor: neither side's target is
a left derived functor along the localization of complexes of `A`-modules — `(W|_R) ⊗ᴸ_R R'` is not
computed by a K-flat resolution over `A` — and faithfulness of restriction along a localization
functor is all that is needed.

The canonical forms pass the two `IsLeftDerivedFunctor` arguments explicitly as the fields of the
chosen models, as `…ProjectionCompatibilityCanonical` does and for the reason recorded there.

No `@[stacks]` attribute is placed here: the obligation is still open, so none of the three
statements of Stacks 0BZM and Stacks 0BZP that depend on it is unconditional.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp v

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

variable {S : Type uR} [CommRing S] [HasDerivedCategory.{v} (ModuleCat.{uA} S)]
  (d : DerivedHomAdjunction S)

/-- The derived tensor product of a zero object with anything is zero: every morphism out of
the tensor product is a transpose of a morphism out of the zero object. -/
theorem isZero_tensor_obj_left {X : DerivedCategory (ModuleCat.{uA} S)} (hX : IsZero X)
    (L : DerivedCategory (ModuleCat.{uA} S)) : IsZero (d.tensor.obj (X, L)) := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨a, ha⟩ := (d.homEquiv X L (d.tensor.obj (X, L))).surjective (𝟙 _)
  rw [← ha, hX.eq_of_src a 0, map_zero]

/-- The derived tensor product of anything with a zero object is zero. -/
theorem isZero_tensor_obj_right (X : DerivedCategory (ModuleCat.{uA} S))
    {L : DerivedCategory (ModuleCat.{uA} S)} (hL : IsZero L) :
    IsZero (d.tensor.obj (X, L)) :=
  (d.isZero_tensor_obj_left hL X).of_iso (d.tensorSwap X L)

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

/-- The comparison of Stacks 0661 before whiskering. -/
noncomputable def restrictionBaseChangeIsoGeneral :
    baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeR := by
  have := isLeftDerivedR
  have := isLeftDerivedA
  let c := RingTheory.TorIndependence.derivedBaseChangeComparison (algebraMap R A)
    (algebraMap R R') (algebraMap A (TensorProduct R A R'))
    (algebraMap R' (TensorProduct R A R'))
    ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
    baseChangeR baseChangeA comparisonR comparisonA
  have hc : IsIso c.2.1 :=
    RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent
      hTor baseChangeR baseChangeA comparisonR comparisonA
  exact (asIso c.2.1).symm

/-- `Dualizing.restrictionBaseChangeIso` is `Dualizing.restrictionBaseChangeIsoGeneral`
whiskered by `RHom_R(A, -)`. -/
theorem restrictionBaseChangeIso_hom_app (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA).hom.app K =
      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA).hom.app
        ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K) := by
  have h : (restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA).hom.app K =
      𝟙 _ ≫ (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).hom.app
          ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K) ≫ 𝟙 _ := rfl
  rw [h, Category.id_comp, Category.comp_id]

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

/-- Source of the two algebra actions, as a functor of the object of `D(A)`. -/
noncomputable def algebraActionSource :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R') :=
  (baseChangeA ⋙
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory) ⋙
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensorAt
      (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))

/-- The `A ⊗_R R'`-action, transported by the comparison of Stacks 0661. -/
noncomputable def algebraActionLeft :
    algebraActionSource baseChangeR baseChangeA ⟶
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeR :=
  Functor.whiskerLeft
      (baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory)
      ((Functor.curry.obj
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor).flip.map
        (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).hom) ≫
    Functor.whiskerLeft
      (baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory)
      (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft baseChangeA
        (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit)
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory ≫
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA).hom

/-- The derived base change of the `A`-action, preceded by the comparison of Stacks 0661. -/
noncomputable def algebraActionRight :
    algebraActionSource baseChangeR baseChangeA ⟶
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeR :=
  Functor.whiskerRight
      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA).hom
      ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensorAt
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
    Functor.whiskerLeft
        ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory)
        (derivedTensorBaseChangeSquare.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
          comparisonR (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory)
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).inv ≫
          Functor.whiskerRight
            (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).counit
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory))
        baseChangeR

/-- The obligation at every object, from the equality of the two algebra actions. -/
theorem projectionFormulaCompatibility_of_algebraAction
    (h : algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai =
      algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K := by
  refine projectionFormulaCompatibility_of_algebraActionSquare hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K ?_
  rw [restrictionBaseChangeIso_hom_app hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA K]
  exact congrArg (fun z => NatTrans.app z
    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) h

/-- **The two algebra actions agree as soon as they agree on classes of complexes.**
`DerivedCategory.Q` is a localization functor, so precomposition with it is faithful on natural
transformations. -/
theorem algebraAction_eq_of_qObj
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Fi alphai).app (DerivedCategory.Q.obj X) =
        (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Ff alphaf).app (DerivedCategory.Q.obj X)) :
    algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai =
      algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)) h

/-- **The two algebra actions agree as soon as they agree on a resolving class of complexes of
`A`-modules.** A class is resolving here if every cochain complex of `A`-modules receives a
quasi-isomorphism from a member of it; the classes of such members then exhaust `D(A)` up to
isomorphism, and both sides are natural, so the equation transports. The choice of class is left
open because the remaining work may want more of a representative than K-flatness over `A`. -/
theorem algebraAction_eq_of_resolving
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ → Prop)
    (hres : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      ∃ (Y : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ) (p : Y ⟶ X), P Y ∧ QuasiIso p)
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ, P X →
      (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Fi alphai).app (DerivedCategory.Q.obj X) =
        (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Ff alphaf).app (DerivedCategory.Q.obj X)) :
    algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai =
      algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf := by
  refine algebraAction_eq_of_qObj hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA Ff alphaf Fi alphai ?_
  intro X
  obtain ⟨Y, p, hY, hp⟩ := hres X
  have := hp
  have key : (algebraActionSource baseChangeR baseChangeA).map (DerivedCategory.Q.map p) ≫
        (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Fi alphai).app (DerivedCategory.Q.obj X) =
      (algebraActionSource baseChangeR baseChangeA).map (DerivedCategory.Q.map p) ≫
        (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Ff alphaf).app (DerivedCategory.Q.obj X) := by
    rw [(algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai).naturality,
      (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf).naturality, h Y hY]
  exact (cancel_epi _).1 key

/-- **The two algebra actions agree as soon as they agree on classes of K-flat complexes of
`A`-modules.** -/
theorem algebraAction_eq_of_kFlat
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp} X →
      (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Fi alphai).app (DerivedCategory.Q.obj X) =
        (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Ff alphaf).app (DerivedCategory.Q.obj X)) :
    algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai =
      algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf :=
  algebraAction_eq_of_resolving hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA Ff alphaf Fi alphai CochainComplex.KFlat.{uA, max v uR uRp}
    (fun X => by
      obtain ⟨Y, p, hY, _, hp, _⟩ :=
        CochainComplex.KFlat.exists_kFlat_resolution.{uA, max v uR uRp} X
      exact ⟨Y, p, hY, hp⟩)
    h

/-- **The obligation at every object of `D(R)`, from the equality of the two algebra actions at
classes of K-flat complexes of `A`-modules.** -/
theorem projectionFormulaCompatibility_of_kFlatAlgebraAction
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp} X →
      (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Fi alphai).app (DerivedCategory.Q.obj X) =
        (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Ff alphaf).app (DerivedCategory.Q.obj X))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K :=
  projectionFormulaCompatibility_of_algebraAction hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai
    (algebraAction_eq_of_kFlat hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai h) K

section Witnesses

/-- **The obligation holds wherever its source is a zero object.** -/
theorem projectionFormulaCompatibility_of_isZero_source
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hz : IsZero ((projectionCompatibilitySource baseChangeR baseChangeA).obj K)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K :=
  hz.eq_of_src _ _

/-- **The obligation holds wherever `RHom_R(A, K)` is killed by derived base change along
`A → A ⊗_R R'`.** -/
theorem projectionFormulaCompatibility_of_isZero_restrictionBaseChange
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hz : IsZero ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
      (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K :=
  projectionFormulaCompatibility_of_isZero_source hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').isZero_tensor_obj_left hz _)

/-- **The hypothesis of `Dualizing.projectionFormulaCompatibility_of_kFlatAlgebraAction` is
inhabited**: the two algebra actions are equal whenever the derived base change of the algebra is
a zero object, since then their common source is a zero object at every argument.  This is what
keeps the reduction from being a reduction to an empty hypothesis. -/
theorem algebraAction_eq_of_isZero_baseChangeAlgebra
    (hz : IsZero (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
    algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai =
      algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf := by
  ext W
  exact ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
    max v uR uA uRp + 1} R').isZero_tensor_obj_right _ hz).eq_of_src _ _

/-- **The obligation holds at every object of `D(R)` as soon as the derived base change of the
algebra is a zero object.** Unlike the two witnesses above, the hypothesis is a condition on the
square alone and the conclusion is uniform in `K`. -/
theorem projectionFormulaCompatibility_of_isZero_baseChangeAlgebra
    (hz : IsZero (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K :=
  projectionFormulaCompatibility_of_algebraAction hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai
    (algebraAction_eq_of_isZero_baseChangeAlgebra hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai hz) K

end Witnesses

section Canonical

/-- `Dualizing.algebraActionLeft` at the canonical model of derived extension of scalars along
`R' → A ⊗_R R'`. -/
noncomputable def algebraActionLeftCanonical :
    algebraActionSource baseChangeR baseChangeA ⟶
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeR :=
  @algebraActionLeft R A R' _ _ _ _ _ hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived

/-- `Dualizing.algebraActionRight` at the canonical model of derived extension of scalars along
`R → A`. -/
noncomputable def algebraActionRightCanonical :
    algebraActionSource baseChangeR baseChangeA ⟶
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeR :=
  @algebraActionRight R A R' _ _ _ _ _ hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived

/-- **The canonical obligation at every object of `D(R)`, from one equation at K-flat complexes
of `A`-modules.** -/
theorem projectionFormulaCompatibilityCanonical_of_kFlatAlgebraAction
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp} X →
      (algebraActionLeftCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X) =
        (algebraActionRightCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K :=
  @projectionFormulaCompatibility_of_kFlatAlgebraAction R A R' _ _ _ _ _ hTor baseChangeR
    comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived
    h K

/-- **The canonical obligation holds wherever `RHom_R(A, K)` is killed by derived base change
along `A → A ⊗_R R'`.** -/
theorem projectionFormulaCompatibilityCanonical_of_isZero_restrictionBaseChange
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hz : IsZero ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
      (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))) :
    ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K :=
  @projectionFormulaCompatibility_of_isZero_restrictionBaseChange R A R' _ _ _ _ _ hTor
    baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived
    K hz

/-- **The canonical obligation holds at every object of `D(R)` as soon as the derived base change
of the algebra is a zero object.** -/
theorem projectionFormulaCompatibilityCanonical_of_isZero_baseChangeAlgebra
    (hz : IsZero (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K :=
  @projectionFormulaCompatibility_of_isZero_baseChangeAlgebra R A R' _ _ _ _ _ hTor
    baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived
    hz K

end Canonical

end Dualizing

end
