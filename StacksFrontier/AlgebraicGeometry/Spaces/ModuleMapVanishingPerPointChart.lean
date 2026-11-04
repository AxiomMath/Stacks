module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapFinitePresentationClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapVanishingAlongClosure

/-!
# One chart per point suffices for the vanishing of a map of modules after base change

Let `S = \Spec(R)` be an affine scheme of a big fppf site, let `X` be an algebraic space over `S`
and let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S`, as in
Stacks 0CWA. Let `J` be an ideal of `R`. Then `u_Z = 0` for `Z = \Spec(R/J)` as soon as every
point of `|X|` lies in the image of one affine étale chart of `X` over which `J` kills the image
of `u`.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.AbsorbedChart`: the étale charts of `X`
  admitting a morphism to an affine étale chart over which `J` absorbs the image of `u`.

## Main results

* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_forall_point`:
  `u_Z = 0` from one affine chart per point of `|X|`.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreMapEqZero_of_forall_point`: the same,
  read on the fibre over a point `s` of the base at which `J` vanishes.
* `ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure_of_forall_point`:
  the conclusion of Stacks 0CWB from one chart per point. For `T` a set of base points and
  `s` in its closure, `u_s = 0` follows from: for each point of `|X|`, an affine chart around it
  over which `𝔭_t · 𝒢` absorbs the image of `u` for every `t ∈ T` implies `𝔭_s · 𝒢` does.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0CVY](https://stacks.math.columbia.edu/tag/0CVY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapFlatTargetSituation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsAffine S]
    (D : ModuleMapFlatTargetSituation B S hS)

/-- The étale charts `V` of `X` admitting a morphism to an affine étale chart `Z₀` of `X` over
which `J` absorbs the image of `u`: `u(ℱ(Z₀)) ⊆ J · 𝒢(Z₀)`. -/
def AbsorbedChart (J : Ideal Γ(S, ⊤)) (V : SmallEtale B S hS D.X.1) : Prop :=
  ∃ Z₀ : SmallEtale B S hS D.X.1,
    IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀) ∧
      Nonempty (V ⟶ Z₀) ∧
      letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
      ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u))

/-- A chart admitting a morphism to an absorbed chart is absorbed. -/
theorem absorbedChart_of_hom {J : Ideal Γ(S, ⊤)} {V V' : SmallEtale B S hS D.X.1} (φ : V' ⟶ V)
    (h : D.AbsorbedChart B S hS J V) : D.AbsorbedChart B S hS J V' := by
  obtain ⟨Z₀, hZ₀, ⟨ψ⟩, hcond⟩ := h
  exact ⟨Z₀, hZ₀, ⟨φ ≫ ψ⟩, hcond⟩

/-- **`u_Z = 0` from one affine chart per point of `|X|`.**  Let `J` be an ideal of the functions
on the affine base such that every point of `|X|` lies in the image of some affine étale chart of
`X` over which `J` absorbs the image of `u`.  Then the base change of `u` to
`Z = \Spec(\Gamma(S, ⊤)/J)` is zero. -/
theorem isZeroAt_specQuotient_of_forall_point (J : Ideal Γ(S, ⊤))
    (hJ : ∀ x : points B S hS D.X.1, ∃ V : SmallEtale B S hS D.X.1,
      D.AbsorbedChart B S hS J V ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj V)) V.1.hom)) :
    (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.specQuotientTest B S hS J) := by
  refine Modules.eq_zero_of_ofArrows B S hS
    ((D.toModuleMapSituation B S hS).baseChangeHom (modulePullbackSystem B S hS)
      (D.specQuotientTest B S hS J)) fun U => ?_
  obtain ⟨I, Y, π, hcov, hgood⟩ := exists_ofArrows_hasAffineChartDiagramWith B S hS
    (D.AbsorbedChart B S hS J)
    ((D.toModuleMapSituation B S hS).baseChangeProjection (D.specQuotientTest B S hS J))
    (fun φ h => D.absorbedChart_of_hom B S hS φ h) hJ U
  refine ⟨I, Y, π, hcov, fun j => ?_⟩
  obtain ⟨hWaff, V, q, hcomm, hVaff, Z₀, hZ₀aff, ⟨φ⟩, hcond⟩ := hgood j
  exact D.modulePullback_map_val_app_specQuotient_eq_zero B S hS J hZ₀aff
    { U := Y j, V := V, g := q, comm := hcomm.symm } hWaff hVaff φ hcond

/-- **`u_s = 0` from one affine chart per point of `|X|`.**  Let `s` be a point of the base and
`J` an ideal of the functions on the base contained in the ideal of `s`, such that every point of
`|X|` lies in the image of some affine étale chart of `X` over which `J` absorbs the image of `u`.
Then `u_s = 0`. -/
theorem fibreMapEqZero_of_forall_point (s : S) (J : Ideal Γ(S, ⊤))
    (hle : J ≤ basePointIdeal B S hS s)
    (hJ : ∀ x : points B S hS D.X.1, ∃ V : SmallEtale B S hS D.X.1,
      D.AbsorbedChart B S hS J V ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj V)) V.1.hom)) :
    D.FibreMapEqZero B S hS s := by
  obtain ⟨ψ⟩ := exists_hom_specQuotientOver B S hS J (specResidueFieldOver B S hS s) hle
  refine (D.toModuleMapSituation B S hS).isZeroAt_of_hom (modulePullbackSystem B S hS)
    (T := D.specQuotientTest B S hS J) (T' := D.fibreTest B S hS s) ?_
    (D.isZeroAt_specQuotient_of_forall_point B S hS J hJ)
  exact CostructuredArrow.homMk ψ ((terminalSpace_isTerminal B S hS).hom_ext _ _)

/-- In the situation of Stacks 0CWA, let `T` be a set of points of the base, let `s` be a point
of its closure, and suppose `u_t = 0` for every `t ∈ T`.  Suppose further that every point of
`|X|` lies in the image of an affine étale chart `Z₀` of `X` at which the ideal condition passes
from the points of `T` to `s`: if `u(ℱ(Z₀)) ⊆ 𝔭_t · 𝒢(Z₀)` for all `t ∈ T`, then
`u(ℱ(Z₀)) ⊆ 𝔭_s · 𝒢(Z₀)`.  Then `u_s = 0`. -/
theorem fibreMapEqZero_of_mem_closure_of_forall_point (T : Set S) (s : S)
    (hpoint : ∀ x : points B S hS D.X.1, ∃ Z₀ : SmallEtale B S hS D.X.1,
      IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀) ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj Z₀)) Z₀.1.hom) ∧
        letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
          Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
        ((∀ t ∈ T, ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
            basePointIdeal B S hS t •
              (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u))) →
          ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
            basePointIdeal B S hS s •
              (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u))))
    (hT : ∀ t ∈ T, D.FibreMapEqZero B S hS t) :
    D.FibreMapEqZero B S hS s := by
  refine D.fibreMapEqZero_of_forall_point B S hS s (basePointIdeal B S hS s) le_rfl fun x => ?_
  obtain ⟨Z₀, hZ₀aff, hxmem, himp⟩ := hpoint x
  refine ⟨Z₀, ⟨Z₀, hZ₀aff, ⟨CategoryStruct.id Z₀⟩, himp fun t ht => ?_⟩, hxmem⟩
  exact D.forall_mem_basePointIdeal_smul_top_of_fibreMapEqZero B S hS t (hT t ht) Z₀ hZ₀aff

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
