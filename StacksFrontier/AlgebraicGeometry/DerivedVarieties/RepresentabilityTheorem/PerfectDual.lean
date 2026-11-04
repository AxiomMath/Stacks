module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.RepresentabilityTheorem.ProperOverField
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.RepresentabilityTheorem.DualOverField
public import StacksFrontier.CategoryTheory.Triangulated.ContravariantDuality
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Homology.Perfect.ModelIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomContravariantCommShiftOnARingedSpace

/-!
# The dual on `D_perf(𝒪_X)` at the locally small model

Let `X` be a scheme. The dual `E ↦ E^∨ = R𝓗om(E, 𝒪_X)` of [Stacks, Tag 08DQ] is constructed at
the standard model of `D(𝒪_X)`. This file carries it to the locally small model, at which
`D_perf(𝒪_X)` is `AlgebraicGeometry.perfectDerived`, along the triangulated comparison
equivalence `StacksDraft.Perfect.derivedEquivalence`, and records there the properties the proof
of [Stacks, Tag 0H4A] uses: the dual of a perfect object is perfect, the dual reverses
distinguished triangles ([Stacks, Tag 08I0]), it commutes with the shift up to a sign of the
degree, it is additive and linear over the base field, and the biduality map is a natural
isomorphism on perfect objects.

## Main definitions

* `Stacks.AlgebraicGeometry.DerivedVarieties.Representability.modelEquivalence`: the comparison
  of the standard model of `D(𝒪_X)` with the locally small one.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Representability.perfectDual`: the dual on
  `D(𝒪_X)` at the locally small model.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 0H4A](https://stacks.math.columbia.edu/tag/0H4A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Representability

section Duality

variable (Y : Scheme.{u})

local notation "Dstd" => @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard Y.Modules)
local notation "Qstd" => @DerivedCategory.Q Y.Modules _ _ (HasDerivedCategory.standard Y.Modules)

/-- The comparison of the standard model of `D(𝒪_X)` with the locally small one, as the
triangulated equivalence of `StacksDraft.Perfect.derivedEquivalence`. -/
abbrev modelEquivalence : Dstd ≌ DerivedCategory Y.Modules :=
  StacksDraft.Perfect.derivedEquivalence _ _

/-- The shift functors of the standard model of `D(𝒪_X)` are additive. -/
instance standard_shiftFunctor_additive (n : ℤ) : (shiftFunctor Dstd n).Additive :=
  @DerivedCategory.instAdditiveShiftFunctorInt _ _ _ (HasDerivedCategory.standard Y.Modules) n

/-- The comparison of models commutes with the shift. -/
instance modelEquivalence_functor_commShift : (modelEquivalence Y).functor.CommShift ℤ :=
  StacksDraft.Perfect.derivedEquivalenceCommShift _ _

/-- The comparison of models is a triangulated functor. -/
instance modelEquivalence_functor_isTriangulated : (modelEquivalence Y).functor.IsTriangulated :=
  StacksDraft.Perfect.derivedEquivalence_isTriangulated _ _

/-- The inverse of the comparison of models commutes with the shift. -/
instance modelEquivalence_inverse_commShift : (modelEquivalence Y).inverse.CommShift ℤ :=
  (modelEquivalence Y).commShiftInverse ℤ

/-- The inverse of the comparison of models is a triangulated functor. -/
instance modelEquivalence_inverse_isTriangulated : (modelEquivalence Y).inverse.IsTriangulated :=
  have := (modelEquivalence Y).commShift_of_functor ℤ
  have := Equivalence.IsTriangulated.mk' (modelEquivalence Y) inferInstance
  inferInstance

/-- **Perfectness is invariant under the comparison of models.** -/
theorem isPerfect_modelEquivalence_functor_obj_iff (K : Dstd) :
    IsPerfect.{u, u, u} (X := Y.toRingedSpace) ((modelEquivalence Y).functor.obj K) ↔
      @IsPerfect.{u, u, u + 1} Y.toRingedSpace (HasDerivedCategory.standard Y.Modules) K :=
  let e₂ : DerivedCategory.Q.obj ((Qstd).objPreimage K) ≅ (modelEquivalence Y).functor.obj K :=
    ((StacksDraft.Perfect.derivedEquivalenceCompQIso _ _).app ((Qstd).objPreimage K)).symm ≪≫
      (modelEquivalence Y).functor.mapIso ((Qstd).objObjPreimageIso K)
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model (X := Y.toRingedSpace)
    (HasDerivedCategory.standard Y.Modules) (Scheme.Modules.hasDerivedCategory Y)
    (E := (Qstd).objPreimage K) ((Qstd).objObjPreimageIso K) e₂).symm

/-- Perfectness is invariant under isomorphism. -/
theorem isPerfect_of_iso {K L : DerivedCategory Y.Modules} (e : K ≅ L)
    (hK : IsPerfect.{u, u, u} (X := Y.toRingedSpace) K) :
    IsPerfect.{u, u, u} (X := Y.toRingedSpace) L :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := Y.toRingedSpace) e hK

/-- An object of the locally small model is perfect exactly when its image at the standard model
is. -/
theorem isPerfect_modelEquivalence_inverse_obj_iff (K : DerivedCategory Y.Modules) :
    @IsPerfect.{u, u, u + 1} Y.toRingedSpace (HasDerivedCategory.standard Y.Modules)
        ((modelEquivalence Y).inverse.obj K) ↔
      IsPerfect.{u, u, u} (X := Y.toRingedSpace) K := by
  refine (isPerfect_modelEquivalence_functor_obj_iff Y _).symm.trans ?_
  exact ⟨isPerfect_of_iso Y ((modelEquivalence Y).counitIso.app K),
    isPerfect_of_iso Y ((modelEquivalence Y).counitIso.app K).symm⟩

/-- **The dual `E ↦ E^∨ = R𝓗om(E, 𝒪_X)` at the locally small model of `D(𝒪_X)`**: the dual
`Stacks.AlgebraicGeometry.DerivedVarieties.DualOverField.dual` of the standard model, read through
`modelEquivalence`. -/
abbrev perfectDual : (DerivedCategory Y.Modules)ᵒᵖ ⥤ DerivedCategory Y.Modules :=
  (modelEquivalence Y).transportDual (DualOverField.dual Y)

/-- **The dual of a perfect object is perfect** ([Stacks, Tag 08DQ]). -/
theorem isPerfect_perfectDual_obj (K : DerivedCategory Y.Modules)
    (hK : IsPerfect.{u, u, u} (X := Y.toRingedSpace) K) :
    IsPerfect.{u, u, u} (X := Y.toRingedSpace) ((perfectDual Y).obj (op K)) :=
  (isPerfect_modelEquivalence_functor_obj_iff Y _).2
    (Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace Y.toRingedSpace _
      ((isPerfect_modelEquivalence_inverse_obj_iff Y K).2 hK))

/-- **The dual reverses distinguished triangles** ([Stacks, Tag 08I0]): a distinguished triangle
`A ⟶ B ⟶ C ⟶ A[1]` gives a distinguished triangle `C^∨ ⟶ B^∨ ⟶ A^∨ ⟶ C^∨[1]`. -/
theorem exists_distinguished_perfectDual :
    ∀ T ∈ distTriang (DerivedCategory Y.Modules),
      ∃ δ : (perfectDual Y).obj (op T.obj₁) ⟶ ((perfectDual Y).obj (op T.obj₃))⟦(1 : ℤ)⟧,
        Triangle.mk ((perfectDual Y).map T.mor₂.op) ((perfectDual Y).map T.mor₁.op) δ ∈
          distTriang (DerivedCategory Y.Modules) :=
  (modelEquivalence Y).exists_distinguished_transportDual (DualOverField.dual Y)
    (fun T hT => Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first Y.sheaf _ T hT)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The biduality map `E ⟶ (E^∨)^∨`** at the locally small model, natural in `E`. -/
def perfectBidual : 𝟭 (DerivedCategory Y.Modules) ⟶ (perfectDual Y).rightOp ⋙ perfectDual Y :=
  (modelEquivalence Y).transportBidual (DualOverField.dual Y)
    (Stacks.SheafOfModules.derivedBidualNatTrans Y.sheaf)

/-- **The biduality map of a perfect object is an isomorphism** ([Stacks, Tag 08DQ]). -/
theorem isIso_perfectBidual_app (K : DerivedCategory Y.Modules)
    (hK : IsPerfect.{u, u, u} (X := Y.toRingedSpace) K) : IsIso ((perfectBidual Y).app K) :=
  (modelEquivalence Y).isIso_transportBidual_app _ _ K
    (Stacks.SheafOfModules.isIso_derivedBidualMap_of_isPerfectSpace Y.toRingedSpace _
      ((isPerfect_modelEquivalence_inverse_obj_iff Y K).2 hK))

/-- The dual on the standard model of `D(𝒪_X)` is additive. -/
instance dual_additive : (DualOverField.dual Y).Additive :=
  RingedSite.additive_derivedSheafHom_flip_obj _ _

/-- The dual `perfectDual` on the locally small model of `D(𝒪_X)` is additive. -/
instance perfectDual_additive : (perfectDual Y).Additive := by
  dsimp only [perfectDual, Equivalence.transportDual]
  infer_instance

/-- **The dual commutes with the shift up to the sign of the degree**:
`(E[n])^∨ ≅ (E^∨)[-n]`. -/
def perfectDualShiftIso (E : DerivedCategory Y.Modules) (n : ℤ) :
    (perfectDual Y).obj (op (E⟦n⟧)) ≅ ((perfectDual Y).obj (op E))⟦-n⟧ :=
  (modelEquivalence Y).functor.mapIso
      (((DualOverField.dual Y).mapIso
          (((modelEquivalence Y).inverse.commShiftIso n).app E).op).symm ≪≫
        Stacks.SheafOfModules.derivedSheafHomSourceShiftIso Y.sheaf
          ((modelEquivalence Y).inverse.obj E) _ n) ≪≫
    ((modelEquivalence Y).functor.commShiftIso (-n)).app _

end Duality

section Linear

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

attribute [local instance] AlgebraicGeometry.modulesLinear

local notation "Dstd" =>
  @DerivedCategory X.left.Modules _ _ (HasDerivedCategory.standard X.left.Modules)

/-- The comparison of models is `k`-linear: both linear structures are induced from that of the
homotopy category, along the two localization functors which the comparison intertwines. -/
instance modelEquivalence_functor_linear : (modelEquivalence X.left).functor.Linear k :=
  (Localization.functor_linear_iff
    (@DerivedCategory.Qh X.left.Modules _ _ (HasDerivedCategory.standard X.left.Modules))
    (HomotopyCategory.subcategoryAcyclic X.left.Modules).trW k
    (DerivedCategory.Qh (C := X.left.Modules)) (modelEquivalence X.left).functor).1 inferInstance

/-- **The dual at the locally small model is `k`-linear.** -/
theorem perfectDual_map_smul {E E' : DerivedCategory X.left.Modules} (f : E ⟶ E') (r : k) :
    (perfectDual X.left).map (r • f).op = r • (perfectDual X.left).map f.op := by
  change (modelEquivalence X.left).functor.map ((DualOverField.dual X.left).map
      ((modelEquivalence X.left).inverse.map (r • f)).op) = _
  rw [Functor.map_smul, DualOverField.dual_map_smul, Functor.map_smul]
  rfl

end Linear

end Stacks.AlgebraicGeometry.DerivedVarieties.Representability

end
