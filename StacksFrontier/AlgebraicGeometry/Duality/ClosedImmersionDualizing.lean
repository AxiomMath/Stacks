module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionDualizing.Chart
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The right adjoint of pushforward along a closed immersion preserves dualizing complexes

Let `i : Z ⟶ W` be a closed immersion of locally Noetherian schemes and let `a` be a right
adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`, at the locally small derived categories of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` (the model at which `a` exists,
[Stacks, Tag 0A9E]). If `K` is a dualizing complex on `W` ([Stacks, Tag 0A87]), then `a(K)` is a
dualizing complex on `Z`.

## Main results

* `Stacks.Duality.ClosedImmersionDualizing.isDualizingComplex_standard_iff` — being a dualizing
  complex does not depend on the model of `D(𝒪_X)`.
* `Stacks.Duality.LocallySmall.isDualizingComplex_derivedSheafHomExactSupport_obj` —
  `R ℰom(𝒪_Z, K)` is a dualizing complex, at the locally small model.
* `Stacks.Duality.LocallySmall.isIso_rightAdjointToDerivedSheafHom_app_of_isDualizingComplex` —
  `a(K) ≅ R ℰom(𝒪_Z, K)` at a dualizing complex `K`, with no boundedness of `K` assumed.
* `Stacks.Duality.LocallySmall.isDualizingComplex_of_closedImmersion` — **`a(K)` is a dualizing
  complex.**

## Implementation notes

**No boundedness of `K` is used.** On a scheme which is not quasi-compact a dualizing complex need
not be bounded below (its cohomology lives in degrees `-dim` of the local rings, which may be
unbounded), so the bounded-below form of [Stacks, Tag 0A9X] does not apply to `K`. Its proof
does: the Yoneda argument identifying `a(K)` with `R ℰom(𝒪_Z, K)` needs only that the latter lies
in `D_QCoh(𝒪_Z)`, and that holds here because `R ℰom(𝒪_Z, K)` is itself a dualizing complex, by
the standard-model theorem of
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionDualizing/Chart.lean`, whose locality input
(`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionDualizing/Locality.lean`) assumes no
boundedness either.

**Crossing the models.** The two models of `D(𝒪_X)` have the same objects
(`StacksDraft.DerivedModel.derivedCategory_eq_standard`), and the restriction to an affine open,
computed out of either model, gives the same object up to isomorphism
(`Stacks.Injectives.mapDerivedCategoryObjIso`); so the predicate
`Stacks.Duality.IsDualizingComplex` does not depend on the model. `R ℰom(𝒪_Z, -)` at the two models
is compared by `StacksDraft.DerivedModel.rightDerivedModelIso`, both being total right derived
functors of the same functor on the homotopy category.

## References

* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality.ClosedImmersionDualizing

/-- Carrying a dualizing model at an affine open does not depend on the model of `D(𝒪_X)`: the
restriction to the open of an object, computed out of the standard model or out of the locally
small one, is the same object up to isomorphism. -/
theorem hasDualizingModelOn_standard_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : DerivedCategory X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    @HasDualizingModelOn X _ (HasDerivedCategory.standard X.Modules) M U hU ↔
      HasDualizingModelOn M U hU := by
  unfold HasDualizingModelOn
  have e := Stacks.Injectives.mapDerivedCategoryObjIso.{u} X.Modules
    (hd₂ := HasDerivedCategory.standard U.toScheme.Modules)
    (Scheme.Modules.restrictFunctor U.ι) M
  constructor
  · rintro ⟨ω, hω, ⟨e'⟩⟩
    exact ⟨ω, hω, ⟨e.symm ≪≫ e'⟩⟩
  · rintro ⟨ω, hω, ⟨e'⟩⟩
    exact ⟨ω, hω, ⟨e ≪≫ e'⟩⟩

/-- Being a dualizing complex does not depend on the model of `D(𝒪_X)`. -/
theorem isDualizingComplex_standard_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : DerivedCategory X.Modules) :
    @IsDualizingComplex X _ (HasDerivedCategory.standard X.Modules) M ↔
      IsDualizingComplex M :=
  forall_congr' fun _ => forall_congr' fun hU => hasDualizingModelOn_standard_iff M hU

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-- **`R ℰom(𝒪_Z, -)` read at the two models.** The right derived functor of sheaf Hom with
exact support taken at the standard model and at the locally small model agree up to the
comparison equivalences, both being total right derived functors of the same functor on the
homotopy category. -/
def rhomModelIso :
    rhom i ⋙ (Stacks.Injectives.grothendieckModelEquiv.{u}
        (SheafOfModules.{u} (structureSheafRing
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).Z))).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u}
        (SheafOfModules.{u} (structureSheafRing
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X))).functor ⋙
        LocallySmall.derivedSheafHomExactSupport i :=
  StacksDraft.DerivedModel.rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)) (ComplexShape.up ℤ))
    (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).derivedSheafHomExactSupportComparison
    (LocallySmall.derivedSheafHomExactSupportComparison i)
    (StacksDraft.DerivedModel.shrinkComparisonQhIso _).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.shrinkComparisonQhIso _).symm)

end Stacks.Duality.ClosedImmersionDualizing

namespace Stacks.Duality.LocallySmall

open Stacks.Duality.ClosedImmersionDualizing

variable {Z W : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z] (i : Z ⟶ W)
  [IsClosedImmersion i]

/-- **`R ℰom(𝒪_Z, K)` is a dualizing complex on `Z`**, at the locally small model, for `K` a
dualizing complex on `W`. This is `Stacks.Duality.ClosedImmersionDualizing.isDualizingComplex_rhom`
read across the comparison of the standard and the locally small models. -/
theorem isDualizingComplex_derivedSheafHomExactSupport_obj
    (K : DerivedCategory W.Modules) (hK : IsDualizingComplex K) :
    IsDualizingComplex ((derivedSheafHomExactSupport i).obj K : DerivedCategory Z.Modules) := by
  have h1 := @isDualizingComplex_rhom Z W i _ _ _ K ((isDualizingComplex_standard_iff K).2 hK)
  have h2 : IsDualizingComplex
      ((((Stacks.Injectives.grothendieckModelEquiv.{u}
        (SheafOfModules.{u} (structureSheafRing
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).Z))).functor.obj
            ((rhom i).obj K)) : DerivedCategory Z.Modules)) :=
    (isDualizingComplex_standard_iff _).1 h1
  exact isDualizingComplex_of_iso ((rhomModelIso i).app K) h2

/-- **The comparison `a(K) ⟶ R ℰom(𝒪_Z, K)` of [Stacks, Tag 0A9X] is invertible at a dualizing
complex `K`.** No boundedness of `K` is needed — a dualizing complex on a scheme which is not
quasi-compact need not be bounded — only that `R ℰom(𝒪_Z, K)` lies in `D_QCoh(𝒪_Z)`, which holds
because it is itself a dualizing complex; the Yoneda argument of
`Stacks.Duality.LocallySmall.isIso_rightAdjointToDerivedSheafHom_app` then applies verbatim. -/
theorem isIso_rightAdjointToDerivedSheafHom_app_of_isDualizingComplex
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : affineHomQuasiCoherentDerivedPushforward i ⊣ a)
    (K : quasiCoherentDerivedCategory W) (hK : IsDualizingComplex K.obj) :
    IsIso ((rightAdjointToDerivedSheafHom i
      (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i) a adj).app K) := by
  have hR := isDualizingComplex_derivedSheafHomExactSupport_obj i K.obj hK
  let M : quasiCoherentDerivedCategory Z :=
    ⟨(derivedSheafHomExactSupport i).obj K.obj, fun n =>
      have := isCoherent_homology_of_isDualizingComplex hR n
      isQuasicoherent_of_isCoherent _⟩
  let hpush := isQuasicoherent_homology_derivedPushforward_of_isAffineHom i
  obtain ⟨t, ht⟩ := (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K M).surjective
    (𝟙 _)
  refine ⟨t, ?_, ht⟩
  refine (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K (a.obj K)).injective ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun x => (rightAdjointToDerivedSheafHom i hpush a adj).app K ≫ x) ht).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- **The right adjoint of pushforward along a closed immersion carries dualizing complexes to
dualizing complexes**, at the locally small derived categories. Let `i : Z ⟶ W` be a closed
immersion of locally Noetherian schemes, let `a` be a right adjoint of
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`, and let `K` be a dualizing complex on `W`. Then `a(K)` is a
dualizing complex on `Z`.

By `isIso_rightAdjointToDerivedSheafHom_app_of_isDualizingComplex`, `a(K) ≅ R ℰom(𝒪_Z, K)`
([Stacks, Tag 0A9X]); over an
affine open `V ⊆ W` with `K|_V` modelled by a dualizing complex `ω` over `Γ(W, V)`, the restriction
of `R ℰom(𝒪_Z, K)` to the affine open `i⁻¹V` is modelled by `RHom_{Γ(W, V)}(Γ(Z, i⁻¹V), ω)`
(locality of `R ℰom(𝒪_Z, -)` and part (2) of [Stacks, Tag 0A78]), which is dualizing by
[Stacks, Tag 0AX0]; [Stacks, Tag 0A86] glues. -/
theorem isDualizingComplex_of_closedImmersion
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : affineHomQuasiCoherentDerivedPushforward i ⊣ a)
    (K : quasiCoherentDerivedCategory W) (hK : IsDualizingComplex K.obj) :
    IsDualizingComplex (a.obj K).obj :=
  have := isIso_rightAdjointToDerivedSheafHom_app_of_isDualizingComplex i a adj K hK
  isDualizingComplex_of_iso
    (asIso ((rightAdjointToDerivedSheafHom i
      (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i) a adj).app K)).symm
    (isDualizingComplex_derivedSheafHomExactSupport_obj i K.obj hK)

end Stacks.Duality.LocallySmall
