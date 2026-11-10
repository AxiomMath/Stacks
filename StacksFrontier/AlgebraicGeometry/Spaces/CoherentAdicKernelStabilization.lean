module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartTower

/-!
# Stabilization of the kernel images of a morphism of coherent adic systems on a chart

Let `F` be an algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and `τ : E ⟶ E'` a
morphism of coherent `𝓘`-adic systems. The images in `E_m` of the kernels `ker τ_l` at the
levels `l ≥ m` shrink as `l` grows. On the sections over a Noetherian affine étale chart `V` they
stabilize: for each level `m` there is a constant `c` beyond which the image in `E_m(V)` of
`ker (τ_l)(V)` no longer depends on `l`.

## Main results

* `AlgebraicGeometry.Space.exists_chartSectionsKernelImage_eventuallyConstant`: the kernel
  images in the sections over a Noetherian affine chart are eventually independent of the level
  they are computed from.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- The projection of the completed module of a coherent adic system over a chart onto the
sections at a level: the projection of the limit, read through the identification of the limit
with its own completion. -/
def chartCompletedLevel (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) {V : SmallEtale B S hS F}
    (hM : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V)) (n : ℕ) :
    chartCompletedSections B S hS F hF 𝓘 E V →ₗ[chartRing B S hS F hF V]
      (chartSectionsSystem B S hS F hF E V).obj (op n) :=
  (chartSectionsLevel B S hS F hF E V n).hom.comp
    (Stacks.Coherent.completeModuleEquivAdicCompletion
      (M := chartSectionsLimit B S hS F hF E V)
      (chartSectionIdeal B S hS F hF 𝓘 V)).symm.toLinearMap

/-- The projection of the completed module onto the sections at a level is surjective. -/
theorem surjective_chartCompletedLevel
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V))
    (hM : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V)) (n : ℕ) :
    Function.Surjective (chartCompletedLevel B S hS F hF 𝓘 E hM n) :=
  (surjective_chartSectionsLevel B S hS F hF 𝓘 hE hV n).comp
    (Stacks.Coherent.completeModuleEquivAdicCompletion
      (M := chartSectionsLimit B S hS F hF E V)
      (chartSectionIdeal B S hS F hF 𝓘 V)).symm.surjective

/-- The kernel of the projection of the completed module onto the sections at level `n` is
`𝓘(V) ^ (n + 1)` times the completed module. -/
theorem ker_chartCompletedLevel
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V)
    (hM : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V)) (n : ℕ) :
    LinearMap.ker (chartCompletedLevel B S hS F hF 𝓘 E hM n) =
      chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF V)
          (chartCompletedSections B S hS F hF 𝓘 E V)) :=
  Stacks.Coherent.ker_comp_linearEquiv_pow_smul_top _ _ _
    (ker_chartSectionsLevel B S hS F hF 𝓘 hE hIcart hV n)

/-- **Stabilization of the kernel images on the sections over a Noetherian affine chart.**

For a morphism `τ : E ⟶ E'` of coherent `𝓘`-adic systems and a level `m` there is a constant `c`
such that for every `l ≥ m + c` the image in `E_m(V)` of the kernel of `τ` on the sections at
level `l` is the same submodule as the one computed from level `m + c`. -/
theorem exists_chartSectionsKernelImage_eventuallyConstant
    {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (hE' : IsCoherentAdicSystem B S hS F hF 𝓘 E')
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V)
    (τ : E ⟶ E') (m : ℕ) :
    ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map ((chartSectionsSystem B S hS F hF E V).map
            (homOfLE ((Nat.le_add_right m c).trans h)).op).hom
          (LinearMap.ker ((chartSectionsSystemMap B S hS F hF τ V).app (op l)).hom) =
        Submodule.map ((chartSectionsSystem B S hS F hF E V).map
            (homOfLE (Nat.le_add_right m c)).op).hom
          (LinearMap.ker ((chartSectionsSystemMap B S hS F hF τ V).app (op (m + c))).hom) := by
  have hAnoeth : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have hJfg : (chartSectionIdeal B S hS F hF 𝓘 V).FG := Ideal.fg_of_isNoetherianRing _
  have hM : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  have hN : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E' V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE' hIcart hV
  have hNfin : Module.Finite
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (chartCompletedSections B S hS F hF 𝓘 E' V) :=
    moduleFinite_chartCompletedSections B S hS F hF 𝓘 hE' hIcart hV
  set eM := Stacks.Coherent.completeModuleEquivAdicCompletion
    (M := chartSectionsLimit B S hS F hF E V) (chartSectionIdeal B S hS F hF 𝓘 V) with heM
  set eN := Stacks.Coherent.completeModuleEquivAdicCompletion
    (M := chartSectionsLimit B S hS F hF E' V) (chartSectionIdeal B S hS F hF 𝓘 V) with heN
  set fA : chartCompletedSections B S hS F hF 𝓘 E V →ₗ[chartRing B S hS F hF V]
      chartCompletedSections B S hS F hF 𝓘 E' V :=
    (eN.toLinearMap.comp (chartSectionsLimitMap B S hS F hF τ V).hom).comp
      eM.symm.toLinearMap with hfA
  set f : chartCompletedSections B S hS F hF 𝓘 E V →ₗ[AdicCompletion
      (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)]
      chartCompletedSections B S hS F hF 𝓘 E' V :=
    { toFun := fA
      map_add' := fA.map_add
      map_smul' := fun r x =>
        Stacks.Coherent.completion_linearMap_smul _ hJfg fA r x } with hf
  obtain ⟨c, hc⟩ := Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq
    (P := (chartSectionsSystem B S hS F hF E V).obj (op m))
    (chartSectionIdeal B S hS F hF 𝓘 V) f
  have hsquare : ∀ l : ℕ,
      (((chartSectionsSystemMap B S hS F hF τ V).app (op l)).hom).comp
          (chartCompletedLevel B S hS F hF 𝓘 E hM l) =
        (chartCompletedLevel B S hS F hF 𝓘 E' hN l).comp
          (f.restrictScalars (chartRing B S hS F hF V)) := by
    intro l
    refine LinearMap.ext fun x => ?_
    have hw := congrArg
      (fun g : chartSectionsLimit B S hS F hF E V ⟶
          (chartSectionsSystem B S hS F hF E' V).obj (op l) =>
        g.hom (eM.symm x))
      (chartSectionsLimitMap_chartSectionsLevel B S hS F hF τ V l)
    change ((chartSectionsSystemMap B S hS F hF τ V).app (op l)).hom
        ((chartSectionsLevel B S hS F hF E V l).hom (eM.symm x)) = _
    change _ = (chartSectionsLevel B S hS F hF E' V l).hom
      (eN.symm (eN ((chartSectionsLimitMap B S hS F hF τ V).hom (eM.symm x))))
    rw [eN.symm_apply_apply]
    exact hw.symm
  have hstable : ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map ((chartSectionsSystem B S hS F hF E V).map
            (homOfLE ((Nat.le_add_right m c).trans h)).op).hom
          (LinearMap.ker ((chartSectionsSystemMap B S hS F hF τ V).app (op l)).hom) =
        Submodule.map (chartCompletedLevel B S hS F hF 𝓘 E hM m)
          ((LinearMap.ker f).restrictScalars (chartRing B S hS F hF V)) := by
    intro l h
    have hproj : (((chartSectionsSystem B S hS F hF E V).map
          (homOfLE ((Nat.le_add_right m c).trans h)).op).hom).comp
          (chartCompletedLevel B S hS F hF 𝓘 E hM l) =
        chartCompletedLevel B S hS F hF 𝓘 E hM m := by
      have hw := limit.w (chartSectionsSystem B S hS F hF E V)
        (homOfLE ((Nat.le_add_right m c).trans h)).op
      refine LinearMap.ext fun x => ?_
      exact congrArg
        (fun g : chartSectionsLimit B S hS F hF E V ⟶
            (chartSectionsSystem B S hS F hF E V).obj (op m) => g.hom (eM.symm x)) hw
    rw [Stacks.AdicCompletion.map_ker_eq_map_comap_ker
      (f.restrictScalars (chartRing B S hS F hF V))
      (chartCompletedLevel B S hS F hF 𝓘 E hM l)
      (chartCompletedLevel B S hS F hF 𝓘 E' hN l)
      (((chartSectionsSystemMap B S hS F hF τ V).app (op l)).hom)
      (((chartSectionsSystem B S hS F hF E V).map
        (homOfLE ((Nat.le_add_right m c).trans h)).op).hom)
      (surjective_chartCompletedLevel B S hS F hF 𝓘 hE hV.1 hM l) (hsquare l), hproj,
      ker_chartCompletedLevel B S hS F hF 𝓘 hE' hIcart hV hN l]
    exact hc (m + 1) (l + 1) (by omega) _
      (ker_chartCompletedLevel B S hS F hF 𝓘 hE hIcart hV hM m).ge
  exact ⟨c, fun l h => (hstable l h).trans (hstable (m + c) le_rfl).symm⟩

end AlgebraicGeometry.Space

end
