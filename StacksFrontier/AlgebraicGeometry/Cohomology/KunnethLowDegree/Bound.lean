module

public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.Dimension
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.Edge
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# The dimension bound `h¹(X ×_k Y, 𝒪) ≤ h¹(X, 𝒪) + h¹(Y, 𝒪)`

For `X`, `Y` proper and geometrically integral over an algebraically closed field `k`, the
low-degree Leray sequence of the projection `π₂ : X ×_k Y ⟶ Y`,

`H¹(Y, π₂_* 𝒪) ⟶ H¹(X ×_k Y, 𝒪) ⟶ Γ(Y, R¹π₂_* 𝒪)`,

is exact, `π₂_* 𝒪 = 𝒪_Y` and `Γ(Y, R¹π₂_* 𝒪)` has dimension `h¹(X, 𝒪_X)`. This is the
dimension half of the degree-one Künneth formula ([Stacks, Tag 0BED]) that the proof of
[Stacks, Tag 0BF3] uses.

## Main results

* `Stacks.KunnethLowDegree.finiteDimensional_and_finrank_le_of_exact`: the middle term of an exact
  sequence `A ⟶ B ⟶ C` of vector spaces with finite dimensional ends is finite dimensional, of
  dimension at most `dim A + dim C`.
* `Stacks.KunnethLowDegree.finrank_H1_pullback_le`: `H¹(X ×_k Y, 𝒪)` is finite dimensional and
  `h¹(X ×_k Y, 𝒪) ≤ h¹(X, 𝒪) + h¹(Y, 𝒪)`.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.KunnethLowDegree

/-- In an exact sequence `A ⟶ B ⟶ C` of vector spaces with finite dimensional ends, the middle
term is finite dimensional of dimension at most the sum. -/
theorem finiteDimensional_and_finrank_le_of_exact {k A B C : Type*} [Field k] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module k A] [Module k B] [Module k C]
    [FiniteDimensional k A] [FiniteDimensional k C] (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (h : LinearMap.range f = LinearMap.ker g) :
    FiniteDimensional k B ∧ Module.finrank k B ≤ Module.finrank k A + Module.finrank k C := by
  have hker : (LinearMap.ker g).FG := by
    rw [← h, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  have hrange : (Submodule.map g ⊤).FG := IsNoetherian.noetherian _
  have htop : (⊤ : Submodule k B).FG :=
    Submodule.fg_of_fg_map_of_fg_inf_ker g hrange (by rwa [top_inf_eq])
  have : FiniteDimensional k B := Module.Finite.of_fg_top htop
  refine ⟨inferInstance, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker g, ← h, add_comm]
  exact add_le_add (LinearMap.finrank_range_le _) (Submodule.finrank_le _)

variable {k : Type u} [Field k]

/-- The `k`-module `cohomologyOverField k p F n` is `Hⁿ(T, F)` with scalars restricted along
`kOf p`. -/
def cohomologyOverFieldIso {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) (F : T.Modules) (n : ℕ) :
    cohomologyOverField k p F n ≅
      (ModuleCat.restrictScalars (kOf p)).obj (((moduleGlobalSections T).rightDerived n).obj F) :=
  eqToIso (congrArg (fun φ => (ModuleCat.restrictScalars φ).obj
      (((moduleGlobalSections T).rightDerived n).obj F)) (kOf_eq p))

/-- **`h¹(X ×_k Y, 𝒪) ≤ h¹(X, 𝒪) + h¹(Y, 𝒪)`** for `X`, `Y` proper and geometrically integral
over an algebraically closed field. -/
theorem finrank_H1_pullback_le [IsAlgClosed k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k))
    (fY : Y ⟶ Spec (.of k)) [IsProper fX] [IsProper fY] [GeometricallyIntegral fX]
    [GeometricallyIntegral fY] :
    FiniteDimensional k (cohomologyOverField k (pullback.snd fX fY ≫ fY)
      (SheafOfModules.unit (pullback fX fY).ringCatSheaf) 1) ∧
    Module.finrank k (cohomologyOverField k (pullback.snd fX fY ≫ fY)
      (SheafOfModules.unit (pullback fX fY).ringCatSheaf) 1) ≤
      Module.finrank k (cohomologyOverField k fX (SheafOfModules.unit X.ringCatSheaf) 1) +
        Module.finrank k (cohomologyOverField k fY (SheafOfModules.unit Y.ringCatSheaf) 1) := by
  have := flat_of_spec_field fX
  let π := pullback.snd fX fY
  let O := SheafOfModules.unit (pullback fX fY).ringCatSheaf
  let R := ModuleCat.restrictScalars (kOf fY)
  have : R.PreservesHomology := Functor.preservesHomologyOfExact _
  have hS := (exact_leray₁_leray₂ π O).map R
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hS
  let eA : R.obj (((moduleGlobalSections Y).rightDerived 1).obj
      ((Scheme.Modules.pushforward π).obj O)) ≃ₗ[k]
      cohomologyOverField k fY (SheafOfModules.unit Y.ringCatSheaf) 1 :=
    (R.mapIso (((moduleGlobalSections Y).rightDerived 1).mapIso (pushforwardSndUnitIso fX fY)) ≪≫
      (cohomologyOverFieldIso fY _ 1).symm).toLinearEquiv
  let eB : R.obj ((ModuleCat.restrictScalars π.appTop.hom).obj
      (((moduleGlobalSections (pullback fX fY)).rightDerived 1).obj O)) ≃ₗ[k]
      cohomologyOverField k (π ≫ fY) O 1 :=
    ((ModuleCat.restrictScalarsComp'App _ _ (kOf (π ≫ fY)) rfl _).symm ≪≫
      (cohomologyOverFieldIso (π ≫ fY) O 1).symm).toLinearEquiv
  obtain ⟨hCfin, hC⟩ := finrank_globalSections_rightDerived_snd fX fY
  have := forall_finiteDimensional_cohomologyOverField_unit k fY 1
  have : FiniteDimensional k (R.obj (((moduleGlobalSections Y).rightDerived 1).obj
      ((Scheme.Modules.pushforward π).obj O))) := Module.Finite.equiv eA.symm
  obtain ⟨hBfin, hB⟩ := finiteDimensional_and_finrank_le_of_exact
    (R.map (leray₁ π O)).hom (R.map (leray₂ π O)).hom hS
  refine ⟨Module.Finite.equiv eB, ?_⟩
  rw [← eB.finrank_eq, ← eA.finrank_eq]
  exact hB.trans_eq (by rw [add_comm, hC])

end Stacks.KunnethLowDegree

end
