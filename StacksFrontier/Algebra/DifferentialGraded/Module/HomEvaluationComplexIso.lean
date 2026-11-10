module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCohomologyIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.CochainComplexFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Evaluation

/-!
# `Hom(K, -)` is evaluation at `K` of the differential graded Yoneda module

Let `B` be a preadditive category with morphisms in `Type 0` and let `K` be a cochain complex in
`B`. There are two constructions in this repository of "the complex of `ℤ`-modules `Hom^•(K, Y)`",
and they are *not* the same construction:

* through the differential graded category of complexes `C = Comp^dg(B)` of Tag 09L9, the
  representable right differential graded `C`-module `h_Y = C(-, Y)` of
  `DGCategory.yonedaRightModule`, evaluated at `K` — which by `DGCategory.homDGFunctor_obj_obj`
  has `C(K, Y)` in each degree, on the nose — read as a complex of `ℤ`-modules by
  `DGCategory.RightModule.cochainComplexFunctor`;
* through the endomorphism differential graded *algebra* `E = End(K)` of
  `DGCategory.endAlgebra`, the representable differential graded `E`-module
  `DGCategory.representableModule`, whose underlying module is the direct sum of the morphism
  groups and whose degree-`n` homogeneous component is therefore the *range of the `n`-th
  inclusion into that direct sum*, read as a complex by
  `DifferentialGradedModule.forgetToCochainComplex`.

The second is what Tag 09LK's functor `CochainComplex.homToDerivedCategoryForget` is built from;
the first is what the reflector of
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomReflectorExists.lean`
produces, since its unit has
`Φ ⋙ ev_K` as its source. This file identifies them: the two functors
`Comp^dg(B) ⥤ CochainComplex (ModuleCat ℤ)` are naturally isomorphic.

This is the computation `ev_K(h_X) = C(K, X)` which
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomForgetInterface.lean`
records as the missing input to the comparison `β` that step 3 of Tag 09LK consumes, read before
any localization. It is not a reflexivity: one side is a family of morphism groups and the other a
family of submodules of their direct sum.

## Main definitions

* `CochainComplex.homEvaluationComplexFunctor`: the first construction, `Y ↦ ev_K(h_Y)`.
* `CochainComplex.homModuleComplexFunctor`: the second, `Y ↦ Hom^•(K, Y)` as a differential
  graded `End(K)`-module with its action forgotten.
* `CochainComplex.homEvaluationComparison` and `CochainComplex.homEvaluationComparisonIso`:
  **the natural isomorphism between them.**

## Main results

* `CochainComplex.homEvaluationComparisonApp_naturality`: the comparison is natural, which is the
  statement that both sides send a closed degree-zero morphism to composition with it.
* `CochainComplex.homEvaluationComparisonIso_hom_app_f_apply` and
  `CochainComplex.homEvaluationComparisonIso_inv_app_f_apply`: **both directions of the
  comparison, elementwise.** Degreewise the comparison is the linear equivalence
  `CochainComplex.homGradingEquiv`, so unlike the inverses of links 3 and 4 of the chain of Tag
  09LK neither direction is a choice of preimage; both are closed formulas. These are what an
  elementwise computation against the comparison can use.

## Implementation notes

*Where the content is.* All three compatibilities are already available degreewise, from
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCohomologyIso.lean`:
`CochainComplex.homGradingEquiv` is the degreewise identification, `homGradingEquiv_delta`
carries the differential of the differential graded module to Mathlib's `δ` — which is the
differential of `Comp^dg(B)` on the nose — and `homGradingEquiv_comp` carries the map induced by
a cochain map to composition with it. What is added here is the assembly into complexes and the
naturality, together with the observation that the degree-`i` term of the first construction is
`Cochain K Y i` by reflexivity.

*Why the components are written through a named morphism of `ModuleCat ℤ`.* The degree-`i` term of
`ev_K(h_Y)` is `ModuleCat.of ℤ (((homDGFunctor C K).obj Y).obj PUnit.unit i)`, whose additive
group and module structures are *structure fields* of the right differential graded module, not
instances that typeclass resolution can reach through the definitional unfoldings of
`DGCategory.Comp` and `DGCategory.Obj`. Writing `ModuleCat.ofHom` directly at that type therefore
fails to synthesize `AddCommGroup`. `CochainComplex.homGradingComponent` and
`CochainComplex.homEvaluationDiff` state the two maps at the `Cochain` spelling, where the
instances are Mathlib's, and the reflexivity above makes them acceptable at the complex's own
types.

*A cocycle of `Comp^dg(B)` as a cochain map.* Naturality is stated for a morphism of
`Comp^dg(B)`, which is a closed degree-zero cochain, whereas `homGradingEquiv_comp` is stated for
`Cochain.ofHom` of a map of complexes. The two are matched by Mathlib's
`CochainComplex.HomComplex.Cocycle.homOf` and `Cocycle.cochain_ofHom_homOf_eq_coe`, rather than by
restating the degreewise lemma for an arbitrary degree-zero cochain.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor
  `Y ↦ Hom(K, Y)`;
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded category of
  complexes;
  [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 consumes the comparison this
  identification is an input to.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

universe u

namespace CochainComplex

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)

/-- **`Y ↦ ev_K(h_Y)`, read as a complex of `ℤ`-modules.** The differential graded Yoneda functor
of the differential graded category of complexes, followed by evaluation at `K` — which is the
functor `Y ↦ C(K, Y)` of [Stacks, Tag 09LE] — and then by the underlying complex of a right
differential graded module over the one-object category `C(K, K)`. Its degree-`i` term at `Y` is
the group of degree-`i` cochains from `K` to `Y`, by reflexivity. -/
abbrev homEvaluationComplexFunctor :
    (dgCategory B).Comp ⥤ CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (DGCategory.homDGFunctor.{0} (dgCategory B) K).onComp ⋙
    DGCategory.RightModule.cochainComplexFunctor.{0}
      (C := DGCategory.endDGCategory (dgCategory B) K) PUnit.unit

/-- **`Y ↦ Hom^•(K, Y)`, read as a complex of `ℤ`-modules.** The representable differential graded
module over the endomorphism differential graded algebra `End(K)` of [Stacks, Tag 09LE], with its
action forgotten. Its degree-`i` term at `Y` is the degree-`i` homogeneous component of a direct
sum, which is where it differs from `CochainComplex.homEvaluationComplexFunctor`. This is the
functor underlying Tag 09LK's `CochainComplex.homToDerivedCategoryForget`. -/
abbrev homModuleComplexFunctor :
    (dgCategory B).Comp ⥤ CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (DGCategory.homRepresentation (dgCategory B) K).complexesFunctor ⋙
    DifferentialGradedModule.forgetToCochainComplex
      (DGCategory.endAlgebra (dgCategory B) K)

/-- The degreewise identification of `CochainComplex.homGradingEquiv`, as a morphism of
`ModuleCat ℤ` from the degree-`i` homogeneous component of `Hom^•(K, Y)` to the degree-`i`
cochains from `K` to `Y`. -/
def homGradingComponent (Y : CochainComplex B ℤ) (i : ℤ) :
    ModuleCat.of ℤ ((DGCategory.representableModule (dgCategory B) K Y).grading i) ⟶
      ModuleCat.of ℤ (Cochain K Y i) :=
  ModuleCat.ofHom (homGradingEquiv B K Y i).toLinearMap

/-- The degreewise map `CochainComplex.homGradingComponent` is an isomorphism in `ModuleCat ℤ`. -/
instance (Y : CochainComplex B ℤ) (i : ℤ) : IsIso (homGradingComponent B K Y i) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (homGradingEquiv B K Y i).bijective

/-- The differential of `ev_K(h_Y)` in the `Cochain` spelling: Mathlib's `δ`, which is the
differential of the differential graded category of complexes on the nose. -/
def homEvaluationDiff (Y : CochainComplex B ℤ) (i : ℤ) :
    ModuleCat.of ℤ (Cochain K Y i) ⟶ ModuleCat.of ℤ (Cochain K Y (i + 1)) :=
  ModuleCat.ofHom (δ_hom ℤ K Y i (i + 1))

/-- **The comparison at an object**: the degreewise identifications assemble into a map of
complexes, because `CochainComplex.homGradingEquiv` carries the differential of the differential
graded module `Hom^•(K, Y)` to `δ`. -/
def homEvaluationComparisonApp (Y : CochainComplex B ℤ) :
    (homModuleComplexFunctor B K).obj Y ⟶ (homEvaluationComplexFunctor B K).obj Y where
  f i := homGradingComponent B K Y i
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have h₁ : ((homEvaluationComplexFunctor B K).obj Y).d i (i + 1) =
        homEvaluationDiff B K Y i := dite_eq_left rfl
    have h₂ : ((homModuleComplexFunctor B K).obj Y).d i (i + 1) =
        ModuleCat.ofHom
          ((DGCategory.representableModule (dgCategory B) K Y).gradedDifferential i) :=
      DifferentialGradedModule.toCochainComplex_d _ i
    rw [h₁, h₂]
    ext x
    exact (homGradingEquiv_delta B K Y (rfl : i + 1 = i + 1) x
      ((DGCategory.representableModule (dgCategory B) K Y).gradedDifferential i x) rfl).symm

/-- The comparison at an object is invertible: it is degreewise the linear equivalence
`CochainComplex.homGradingEquiv`. -/
theorem isIso_homEvaluationComparisonApp (Y : CochainComplex B ℤ) :
    IsIso (homEvaluationComparisonApp B K Y) :=
  have : ∀ n : ℤ, IsIso ((homEvaluationComparisonApp B K Y).f n) := fun n =>
    inferInstanceAs (IsIso (homGradingComponent B K Y n))
  HomologicalComplex.Hom.isIso_of_components _

/-- **The comparison is natural.** Both constructions send a closed degree-zero morphism
`φ : Y ⟶ Y'` to composition with `φ`: on the evaluated Yoneda side that is the composition of
`Comp^dg(B)` by `DGCategory.app_yonedaPostcomp`, and on the differential graded module side it is
`CochainComplex.homGradingEquiv_comp`. -/
theorem homEvaluationComparisonApp_naturality {Y Y' : CochainComplex B ℤ}
    (φ : (dgCategory B).Cocycle Y Y') :
    (homModuleComplexFunctor B K).map φ ≫ homEvaluationComparisonApp B K Y' =
      homEvaluationComparisonApp B K Y ≫ (homEvaluationComplexFunctor B K).map φ := by
  ext i x
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Y ⟶ Y', Cochain.ofHom ψ = (φ.1 : Cochain Y Y' 0) :=
    ⟨Cocycle.homOf (Cocycle.mk (φ.1 : Cochain Y Y' 0) (0 + 1) rfl φ.2),
      Cocycle.cochain_ofHom_homOf_eq_coe _⟩
  refine (homGradingEquiv_comp B K ψ i x _ ?_).trans ?_ <;> rw [hψ] <;> rfl

/-- **The comparison**, `Hom^•(K, -) ⟶ ev_K(h_-)` as functors on the category of complexes of the
differential graded category of complexes. -/
def homEvaluationComparison :
    homModuleComplexFunctor B K ⟶ homEvaluationComplexFunctor B K where
  app Y := homEvaluationComparisonApp B K Y
  naturality _ _ φ := homEvaluationComparisonApp_naturality B K φ

/-- The comparison is invertible, object by object. -/
theorem isIso_homEvaluationComparison : IsIso (homEvaluationComparison B K) :=
  have : ∀ X : (dgCategory B).Comp, IsIso ((homEvaluationComparison B K).app X) := fun X =>
    isIso_homEvaluationComparisonApp B K X
  NatIso.isIso_of_isIso_app _

/-- **The two constructions of `Hom^•(K, -)` agree.** The complex of `ℤ`-modules underlying the
representable differential graded `End(K)`-module `Hom^•(K, Y)` is naturally isomorphic to the
complex `C(K, Y)` obtained by evaluating the differential graded Yoneda module `h_Y` at `K`.

This is the identification `ev_K(h_Y) = C(K, Y)` of [Stacks, Tag 09LE] read as complexes, and the
unlocalized half of the comparison `β` that step 3 of [Stacks, Tag 09LK] consumes. -/
def homEvaluationComparisonIso :
    homModuleComplexFunctor B K ≅ homEvaluationComplexFunctor B K :=
  haveI := isIso_homEvaluationComparison B K
  asIso (homEvaluationComparison B K)

/-! ### The comparison, elementwise -/

/-- **The comparison, computed.** In degree `i` the comparison is the degreewise identification
`CochainComplex.homGradingEquiv`: it carries a homogeneous element of the representable
differential graded `End(K)`-module to the degree-`i` cochain it is.

The comparison is *defined* degreewise by that equivalence, so this is a definitional equality.
It is recorded because the identification `(*)` of step 3 of [Stacks, Tag 09LK] has to be
evaluated at an element — see
`CochainComplex.derivedHomLiftIdentificationOfNaturality`, whose `unit_app_id` clause is a
statement about the image of one cohomology class — and the comparison stands between that class
and the cocycle the differential graded Yoneda lemma consumes. -/
@[simp] theorem homEvaluationComparisonIso_hom_app_f_apply (Y : CochainComplex B ℤ) (i : ℤ)
    (x : (DGCategory.representableModule (dgCategory B) K Y).grading i) :
    ((homEvaluationComparisonIso B K).hom.app Y).f i x = homGradingEquiv B K Y i x := rfl

/-- **The inverse of the comparison, computed.** In degree `i` it is the inverse of the
degreewise identification `CochainComplex.homGradingEquiv`: a degree-`i` cochain `K ⟶ Y` goes to
the homogeneous element of the representable differential graded `End(K)`-module that it is.

Unlike the inverses of links 3 and 4 of the chain of [Stacks, Tag 09LK] this one is a closed
formula, because the comparison is degreewise a `LinearEquiv` and not a choice of preimage
supplied by fullness. -/
@[simp] theorem homEvaluationComparisonIso_inv_app_f_apply (Y : CochainComplex B ℤ) (i : ℤ)
    (y : Cochain K Y i) :
    ((homEvaluationComparisonIso B K).inv.app Y).f i y =
      (homGradingEquiv B K Y i).symm y := by
  have key := ConcreteCategory.congr_hom
    (congrArg (fun z => HomologicalComplex.Hom.f z i)
      ((homEvaluationComparisonIso B K).inv_hom_id_app Y)) y
  have h2 : homGradingEquiv B K Y i
      (((homEvaluationComparisonIso B K).inv.app Y).f i y) = y := key
  exact (((homGradingEquiv B K Y i).symm_apply_eq).2 h2.symm).symm

end CochainComplex

end
