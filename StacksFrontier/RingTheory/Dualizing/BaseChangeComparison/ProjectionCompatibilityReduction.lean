module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibility

/-!
# The projection-formula compatibility is decided at K-flat representatives

`Dualizing.ProjectionFormulaCompatibility` is the one obligation on which
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibility` makes Stacks 0BZP
and both cases of Stacks 0BZM depend. It is stated at a single object `K` of `D(R)`, and in that
form it says nothing about how it varies with `K`.

This file shows that both sides of the obligation are the components at `K` of *natural*
transformations
`RHom_R(A, -) ⊗ᴸ_{A'} A' |_{R'} ⊗ᴸ_{R'} (A ⊗ᴸ_R R') ⟶ (-) ⊗ᴸ_R R'`,
by exhibiting each as a composite of whiskerings of transformations that are already natural —
functoriality of the derived tensor product in its second argument, the inverse projection formula,
the counit of derived extension of scalars, the restriction/base-change identification of
Stacks 0661, the lax monoidal structure map of derived base change as the square
`Dualizing.derivedTensorBaseChangeSquare`, and the evaluation counit of Stacks 0A70.

Three reductions follow: the obligation at an arbitrary object is implied by the obligation at a
restricted supply of objects.

* It is invariant under isomorphism of `K`.
* It holds at every `K` as soon as it holds at the class of every **K-flat** cochain complex.
* It holds at every `K` as soon as, for every cochain complex `N` of `R`-modules, the two sides
  agree at `Q N` after composition with `comparisonR`. This is the universal property of
  `baseChangeR` as a left derived functor, i.e. of a right Kan extension along `Q`.

## Main definitions

* `Dualizing.projectionCompatibilitySource` — the common source functor of the two sides.
* `Dualizing.projectionCompatibilityLeft`, `Dualizing.projectionCompatibilityRight` — the two
  sides of `Dualizing.ProjectionFormulaCompatibility` as natural transformations to
  `baseChangeR`.

## Main results

* `Dualizing.projectionFormulaCompatibility_iff_app_eq` — the obligation at `K` *is* the equality
  of the two components at `K`; the two are interchangeable by `rfl`.
* `Dualizing.projectionFormulaCompatibility_of_iso` — the obligation is invariant under
  isomorphism of `K`.
* `Dualizing.projectionFormulaCompatibility_of_kFlat` — **the obligation at every object follows
  from the obligation at the classes of K-flat complexes.**
* `Dualizing.projectionFormulaCompatibility_of_qObj` — the obligation at every object follows from
  the equality of the two sides on classes of complexes after composition with the comparison
  morphism of `baseChangeR`.

## Implementation notes

The two sides are built as composites of whiskerings whose bracketing is chosen to match the
bracketing of `Dualizing.ProjectionFormulaCompatibility`, so that
`Dualizing.projectionFormulaCompatibility_iff_app_eq` is `Iff.rfl`. Composition of natural
transformations computes its components definitionally, and so do `Functor.whiskerLeft` and
`Functor.whiskerRight`; the functor composites that the whiskerings produce are associated
differently from one another, which is immaterial because `CategoryTheory.Functor.comp` is
associative definitionally.

Functoriality of the derived tensor product in its *second* argument is not among the recorded
equations of `StacksDraft.DerivedHom.DerivedHomAdjunction`, so it is taken as the action of
`(Functor.curry.obj _).flip` on a morphism, whose component is the required
`tensor.map (𝟙 _, _)` by `rfl`.

The algebra action over `R → A` is left inline rather than named: as a separate declaration its
type determines only `max v uRp`, so neither `v` nor `uRp` could be recovered at a use site.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp v

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

/-- The common source of the two sides of `Dualizing.ProjectionFormulaCompatibility`, as a
functor of the object `K` of `D(R)`: the derived base change along `A → A ⊗_R R'` of
`RHom_R(A, K)`, restricted to `R'`, tensored over `R'` with the derived base change along
`R → R'` of the algebra. -/
noncomputable def projectionCompatibilitySource :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R') :=
  (derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙ baseChangeA ⋙
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory) ⋙
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensorAt
      (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))

/-- **The left-hand side of `Dualizing.ProjectionFormulaCompatibility`, as a natural
transformation.** It is the base change of the algebra in the tensor factor, the inverse projection
formula at `R' → A ⊗_R R'`, the counit of derived extension of scalars there, the
restriction/base-change identification of Stacks 0661, and the derived base change of the
evaluation counit of Stacks 0A70. -/
noncomputable def projectionCompatibilityLeft :
    projectionCompatibilitySource baseChangeR baseChangeA ⟶ baseChangeR :=
  Functor.whiskerLeft
      (derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙ baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory)
      ((Functor.curry.obj
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor).flip.map
        (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).hom) ≫
    Functor.whiskerLeft
      (derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙ baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory)
      (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙ baseChangeA)
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uRp,
          max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit)
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory ≫
    ((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA).hom ≫
      Functor.whiskerRight
        (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit baseChangeR)

/-- **The right-hand side of `Dualizing.ProjectionFormulaCompatibility`, as a natural
transformation.** It is the restriction/base-change identification of Stacks 0661 in the first
tensor factor, the lax monoidal structure map of derived base change in the form of the square
`Dualizing.derivedTensorBaseChangeSquare`, and the derived base change of the algebra action over
`R → A` — the inverse projection formula at `R → A`, the counit of derived extension of scalars
there, and the evaluation counit of Stacks 0A70. -/
noncomputable def projectionCompatibilityRight :
    projectionCompatibilitySource baseChangeR baseChangeA ⟶ baseChangeR :=
  Functor.whiskerRight
      (restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA).hom
      ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensorAt
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
    (Functor.whiskerLeft
        (derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙
          (ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory)
        (derivedTensorBaseChangeSquare.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
          comparisonR (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ≫
      Functor.whiskerRight
        (
        Functor.whiskerLeft
            (derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory)
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).inv ≫
          (Functor.whiskerRight
              (Functor.whiskerLeft (derivedHom.{uR, max v uRp, uA} (algebraMap R A))
                (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA,
                  max v uRp} (algebraMap R A) Ff alphaf).counit)
              (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ≫
            (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit)) baseChangeR)

/-- **The obligation is the equality of two components of natural transformations.** The
right-hand side is the equation `Dualizing.ProjectionFormulaCompatibility` unfolds to. -/
theorem projectionFormulaCompatibility_iff_app_eq
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf Fi alphai K ↔
      (projectionCompatibilityLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Fi alphai).app K =
        (projectionCompatibilityRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Ff alphaf).app K :=
  Iff.rfl

/-- **The obligation is invariant under isomorphism of the object.** Both sides are natural in
`K`, and the derived base change of an isomorphism is an isomorphism, so the equation transports
along any `K ≅ K'`. -/
theorem projectionFormulaCompatibility_of_iso
    {K K' : DerivedCategory (ModuleCat.{max v uR uA uRp} R)} (theta : K ≅ K')
    (h : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K') :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K := by
  rw [projectionFormulaCompatibility_iff_app_eq] at h ⊢
  have hL := (projectionCompatibilityLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA Fi alphai).naturality theta.hom
  have hR := (projectionCompatibilityRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA Ff alphaf).naturality theta.hom
  exact (cancel_mono (baseChangeR.map theta.hom)).1 (by rw [← hL, ← hR, h])

/-- **The obligation at every object follows from the two sides agreeing on classes of
complexes, after composition with the comparison morphism.** This is the uniqueness half of the
universal property of `baseChangeR` as a left derived functor: it is a right Kan extension of
degreewise extension of scalars along the localization functor `Q`, so two natural transformations
into it that agree after whiskering with `Q` and composing with `comparisonR` are equal. -/
theorem projectionFormulaCompatibility_of_qObj
    (h : ∀ N : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      (projectionCompatibilityLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
            comparisonA isLeftDerivedA Fi alphai).app (DerivedCategory.Q.obj N) ≫
          comparisonR.app N =
        (projectionCompatibilityRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
            comparisonA isLeftDerivedA Ff alphaf).app (DerivedCategory.Q.obj N) ≫
          comparisonR.app N)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K := by
  rw [projectionFormulaCompatibility_iff_app_eq]
  refine NatTrans.congr_app (baseChangeR.leftDerived_ext comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)) _ _ _ ?_) K
  ext N
  exact h N

/-- **The obligation at every object follows from the obligation at the classes of K-flat
complexes.** Every object of `D(R)` is isomorphic to the class of a K-flat complex, and the
obligation is invariant under isomorphism. -/
theorem projectionFormulaCompatibility_of_kFlat
    (h : ∀ (N : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ),
      CochainComplex.KFlat.{uR, max v uA uRp} N →
      ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf Fi alphai (DerivedCategory.Q.obj N))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA Ff alphaf Fi alphai K := by
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{uR, max v uA uRp}
      (DerivedCategory.Q.objPreimage K)
  exact projectionFormulaCompatibility_of_iso hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai
    ((asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K).symm)
    (h P hP)

end Dualizing

end
