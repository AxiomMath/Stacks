module

public import StacksFrontier.RingTheory.FormsTrace.Framed

/-!
# The framed trace is compatible with base change

Let `f` be a frame (`Stacks.FormsTrace.ChartFrame`) of a finite free `A`-algebra `B`, and let
`(A, B) → (A', B')` be a pushout square of rings, so that `B' = A' ⊗_A B`. The image `e'` of the
basis `e` of `f` is a basis of `B'` over `A'` with first vector `1`; its table is the base change
of the table of `e`, so the classifying map of `e'` is that of `e` followed by `A → A'`, and the
same syntomic-good `g` gives a frame `f'` of `B'/A'` (`Stacks.FormsTrace.ChartFrame.baseChange`).

The chart ring `N_g[x_a : a ∈ A]` of `f` maps to the chart ring `N_g[x_{a'} : a' ∈ A']` of `f'` by
renaming the variables along `A → A'`; this is compatible with the evaluations and the base
changed universal algebras form a pushout square over it. So the presentation of `f'` refines that
of `f`, and `Stacks.FormsTrace.descendForms_formsMap_of_refinement` gives
`Θ_{A'}(x|_{B'}) = Θ_A(x)|_{A'}` (`Stacks.FormsTrace.ChartFrame.framedTrace_baseChange`), for any
families on the two chart rings with property (1) of Stacks, Lemma 0FLB.

## Main definitions

* `Stacks.FormsTrace.ChartFrame.baseChangeBasis`, `Stacks.FormsTrace.ChartFrame.baseChange`: the
  induced basis and frame of `B'/A'`.
* `Stacks.FormsTrace.ChartFrame.chartRename`, `Stacks.FormsTrace.ChartFrame.carrierRename`: the
  maps between the two presentations.

## Main results

* `Stacks.FormsTrace.ChartFrame.eval_chartRename`: the renaming is compatible with the
  evaluations.
* `Stacks.FormsTrace.ChartFrame.framedTrace_baseChange`: the framed trace commutes with base
  change.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra
open scoped TensorProduct nonZeroDivisors

universe u

namespace Stacks.FormsTrace

namespace ChartFrame

variable {d : ℕ} [NeZero d] {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (A' B' : Type u) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A B A' B']
  (f : ChartFrame d A B)

/-- The basis of `B' = A' ⊗_A B` induced by the basis of a frame of `B/A`. -/
def baseChangeBasis : Module.Basis (Fin d) A' B' :=
  (Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout A B A' B')).out.basis f.basis

/-- The induced basis is the image of the basis. -/
theorem baseChangeBasis_apply (i : Fin d) :
    f.baseChangeBasis A' B' i = algebraMap B B' (f.basis i) :=
  IsBaseChange.basis_apply _ _ i

/-- The first vector of the induced basis is `1`. -/
theorem baseChangeBasis_zero : f.baseChangeBasis A' B' 0 = 1 := by
  rw [baseChangeBasis_apply, f.basis_zero, map_one]

/-- The table of the induced basis is the base change of the table of the basis. -/
theorem ofBasis_baseChangeBasis :
    ofBasis (f.baseChangeBasis A' B') (f.baseChangeBasis_zero A' B') =
      FiniteFreeAlgebra.map (algebraMap A A') (ofBasis f.basis f.basis_zero) := by
  refine (ofBasis_map (algebraMap A A') (algebraMap B B') (fun r => ?_) f.basis f.basis_zero
    (f.baseChangeBasis A' B') (f.baseChangeBasis_zero A' B') fun i => ?_).symm
  · rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · rw [baseChangeBasis_apply]

/-- **The frame induced on a base change** `B' = A' ⊗_A B`: the image of the basis, and the same
syntomic-good element. -/
abbrev baseChange : ChartFrame d A' B' where
  basis := f.baseChangeBasis A' B'
  basis_zero := f.baseChangeBasis_zero A' B'
  g := f.g
  good := f.good
  isUnit := by
    rw [ofBasis_baseChangeBasis, classify_map_eq_comp]
    exact f.isUnit.map (algebraMap A A')

/-- The chart of a frame, composed with `A_d → N_g`, is the classifying map of its basis. -/
private theorem chartMap_classify {B : Type u} [CommRing B] [Algebra A B] (f : ChartFrame d A B)
    (a : universalRing d) :
    f.chartMap (universalChartBaseClassify.{u} f.g a) =
      (ofBasis f.basis f.basis_zero).classify a :=
  congrArg (fun φ : universalRing d →+* A => φ a) (chartOfBasis_comp f.basis f.basis_zero f.isUnit)

/-- The chart of the induced frame is the chart of the frame followed by `A → A'`. -/
theorem chartMap_baseChange :
    (f.baseChange A' B').chartMap = (algebraMap A A').comp f.chartMap := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (ULift.up.{u} f.g)) ?_
  refine RingHom.ext fun a => ?_
  change (f.baseChange A' B').chartMap (universalChartBaseClassify.{u} f.g a.down) =
    algebraMap A A' (f.chartMap (universalChartBaseClassify.{u} f.g a.down))
  rw [chartMap_classify, chartMap_classify]
  change (ofBasis (f.baseChangeBasis A' B') (f.baseChangeBasis_zero A' B')).classify a.down = _
  rw [ofBasis_baseChangeBasis, classify_map_eq_comp, RingHom.comp_apply]

/-- **The renaming of variables** `N_g[x_a] → N_g[x_{a'}]` along `A → A'`, from the chart ring of
the frame to the chart ring of the induced frame. -/
def chartRename : f.Chart →+* (f.baseChange A' B').Chart :=
  (MvPolynomial.rename (algebraMap A A') :
    MvPolynomial A (universalChartBase.{u} f.g) →ₐ[universalChartBase.{u} f.g]
      MvPolynomial A' (universalChartBase.{u} f.g)).toRingHom

/-- The renaming is the identity on `N_g`. -/
theorem chartRename_algebraMap (n : universalChartBase.{u} f.g) :
    f.chartRename A' B' (algebraMap _ f.Chart n) = algebraMap _ (f.baseChange A' B').Chart n :=
  MvPolynomial.rename_C _ n

/-- The renaming is compatible with the classifying maps of the charts. -/
theorem chartRename_comp_classify :
    (f.chartRename A' B').comp (universalChartClassify A f.g) =
      universalChartClassify A' (f.baseChange A' B').g :=
  RingHom.ext fun _ => f.chartRename_algebraMap A' B' _

/-- **The renaming is compatible with the evaluations**: `ψ' ∘ ρ = (A → A') ∘ ψ`. -/
theorem eval_chartRename (x : f.Chart) :
    (f.baseChange A' B').eval (f.chartRename A' B' x) = algebraMap A A' (f.eval x) := by
  have h : (f.baseChange A' B').eval.comp (f.chartRename A' B') =
      (algebraMap A A').comp f.eval := by
    refine MvPolynomial.ringHom_ext (fun n => ?_) (fun a => ?_)
    · change (f.baseChange A' B').eval (f.chartRename A' B' (algebraMap _ f.Chart n)) =
        algebraMap A A' (f.eval (algebraMap _ f.Chart n))
      rw [chartRename_algebraMap, eval_algebraMap, eval_algebraMap, chartMap_baseChange,
        RingHom.comp_apply]
    · change (f.baseChange A' B').eval (MvPolynomial.rename (R := universalChartBase.{u} f.g)
        (algebraMap A A') (MvPolynomial.X a)) = algebraMap A A' (f.eval (MvPolynomial.X a))
      rw [MvPolynomial.rename_X, eval_X, eval_X]
  exact congrArg (fun φ => φ x) h

/-- The base change along the renaming of the table of the chart is the table of the induced
chart. -/
theorem map_table_chartRename :
    FiniteFreeAlgebra.map (f.chartRename A' B') (tableOfHom (universalChartClassify A f.g)) =
      tableOfHom (universalChartClassify A' (f.baseChange A' B').g) := by
  rw [map_tableOfHom, chartRename_comp_classify]

/-- **The map of universal algebras** over the renaming: coordinatewise renaming. -/
def carrierRename : f.ChartAlgebra →+* (f.baseChange A' B').ChartAlgebra :=
  (carrierCongr (f.map_table_chartRename A' B')).toRingHom.comp
    (Carrier.mapRingHom (f.chartRename A' B') _)

/-- `Stacks.FormsTrace.ChartFrame.carrierRename` in coordinates. -/
theorem carrierRename_apply (x : f.ChartAlgebra) (k : Fin d) :
    f.carrierRename A' B' x k = f.chartRename A' B' (x k) :=
  carrierCongr_apply _ _ k

/-- **The framed trace commutes with base change** (Stacks 0FLB, 0FLC). For a frame `f` of
`B/A`, a pushout square `(A, B) → (A', B')`, and families `Θ`, `Θ'` with property (1) of
Stacks, Lemma 0FLB on the chart rings of `f` and of the induced frame `f'`,
`Θ'_{A'}(x|_{B'}) = Θ_A(x)|_{A'}`. -/
theorem framedTrace_baseChange
    {Θ : ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart]
      ⋀[f.Chart]^p Ω[f.Chart⁄ℤ]} (hΘ : IsFormsTrace f.Chart f.ChartAlgebra Θ)
    {Θ' : ∀ p : ℕ, ⋀[(f.baseChange A' B').ChartAlgebra]^p Ω[(f.baseChange A' B').ChartAlgebra⁄ℤ]
      →ₗ[(f.baseChange A' B').Chart] ⋀[(f.baseChange A' B').Chart]^p
        Ω[(f.baseChange A' B').Chart⁄ℤ]}
    (hΘ' : IsFormsTrace (f.baseChange A' B').Chart (f.baseChange A' B').ChartAlgebra Θ')
    (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]) :
    (f.baseChange A' B').framedTrace Θ' hΘ' p (formsMap B B' p x) =
      formsMap A A' p (f.framedTrace Θ hΘ p x) := by
  classical
  set f' := f.baseChange A' B' with hf'
  -- the presentation of `f`
  let := f.algebraChart
  let := f.algebraCarrier
  let := f.algebraChartTarget
  have := f.isScalarTower_chart
  have := f.isScalarTower_carrier
  have := f.isPushout
  -- the presentation of `f'`
  let := f'.algebraChart
  let := f'.algebraCarrier
  let := f'.algebraChartTarget
  have := f'.isScalarTower_chart
  have := f'.isScalarTower_carrier
  have := f'.isPushout
  have : Module.Finite A B := Module.Finite.of_basis f.basis
  have : Module.Free A B := Module.Free.of_basis f.basis
  have : Module.Finite A' B' := Module.Finite.of_basis f'.basis
  have : Module.Free A' B' := Module.Free.of_basis f'.basis
  -- the refinement of the presentation of `f` by that of `f'`
  let : Algebra f.Chart f'.Chart := (f.chartRename A' B').toAlgebra
  let : Algebra f.ChartAlgebra f'.ChartAlgebra := (f.carrierRename A' B').toAlgebra
  let : Algebra f.Chart f'.ChartAlgebra :=
    ((algebraMap f'.Chart f'.ChartAlgebra).comp (f.chartRename A' B')).toAlgebra
  have : IsScalarTower f.Chart f'.Chart f'.ChartAlgebra := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower f.Chart f.ChartAlgebra f'.ChartAlgebra :=
    IsScalarTower.of_algebraMap_eq fun r => by
      refine Carrier.ext fun k => ?_
      change (algebraMap f'.Chart f'.ChartAlgebra (f.chartRename A' B' r)) k =
        f.carrierRename A' B' (algebraMap f.Chart f.ChartAlgebra r) k
      rw [carrierRename_apply, Carrier.algebraMap_coord, Carrier.algebraMap_coord]
      split_ifs <;> simp
  have : Algebra.IsPushout f.Chart f.ChartAlgebra f'.Chart f'.ChartAlgebra := by
    refine isPushout_of_bases_one (Carrier.basis _) (Carrier.basis _) fun x => ?_
    refine Carrier.ext fun k => ?_
    change f.carrierRename A' B' x k = _
    rw [carrierRename_apply, Carrier.sum_apply]
    have hterm : ∀ i : Fin d, (algebraMap f.Chart f'.Chart ((Carrier.basis _).repr x i) •
        Carrier.basis (tableOfHom (universalChartClassify A' f'.g)) i) k =
          f.chartRename A' B' (x i) * (if k = i then 1 else 0) := fun i => by
      rw [Carrier.smul_apply, Carrier.basis_apply, Carrier.basisVector_apply,
        Carrier.basis_repr_apply]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_eq_single k
      (fun i _ hi => by simp [Ne.symm hi]) (fun h => absurd (Finset.mem_univ k) h)]
    simp
  -- the map of pairs
  let : Algebra f.Chart A' := ((algebraMap A A').comp f.eval).toAlgebra
  have : IsScalarTower f.Chart f'.Chart A' :=
    IsScalarTower.of_algebraMap_eq fun r => (f.eval_chartRename A' B' r).symm
  have : IsScalarTower f.Chart A A' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra f.ChartAlgebra B' := ((algebraMap B B').comp f.carrierMap).toAlgebra
  have : IsScalarTower f.ChartAlgebra B B' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower f.ChartAlgebra f'.ChartAlgebra B' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B B' (f.carrierMap x) = f'.carrierMap (f.carrierRename A' B' x)
      rw [carrierMap, carrierMap, carrierLift_apply, carrierLift_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [carrierRename_apply, eval_chartRename]
      change _ = algebraMap A A' (f.eval (x k)) • f.baseChangeBasis A' B' k
      rw [baseChangeBasis_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply A B B', IsScalarTower.algebraMap_apply A A' B']
  -- the nice elements
  obtain ⟨N, hN⟩ := f.nice.pow_smul_kaehler
  obtain ⟨N', hN'⟩ := f'.nice.pow_smul_kaehler
  have hΔ : algebraMap f.Chart f'.Chart
      (Algebra.discr f.Chart (Carrier.basis (tableOfHom (universalChartClassify A f.g)))) =
      Algebra.discr f'.Chart (Carrier.basis (tableOfHom (universalChartClassify A' f'.g))) := by
    rw [discr_tableOfHom, discr_tableOfHom, ← f.chartRename_comp_classify A' B']
    rfl
  have hreg : ∀ p, IsSMulRegular (⋀[f'.Chart]^p Ω[f'.Chart⁄ℤ]) (algebraMap f.Chart f'.Chart
      (Algebra.discr f.Chart (Carrier.basis (tableOfHom (universalChartClassify A f.g))))) :=
    fun p => hΔ ▸ f'.nice.regular p
  have hreg' : ∀ p, IsSMulRegular (⋀[f'.Chart]^p Ω[f'.Chart⁄ℤ]) (algebraMap f'.Chart f'.Chart
      (Algebra.discr f'.Chart (Carrier.basis (tableOfHom (universalChartClassify A' f'.g))))) :=
    fun p => f'.nice.regular p
  exact descendForms_formsMap_of_refinement (T := f'.Chart) (U := f'.ChartAlgebra)
    f.eval_surjective f'.eval_surjective f'.eval_surjective hN hreg hN' hreg' hΘ
    (hΘ.isWedgeLinear_of_isNiceElement f.nice) hΘ'
    (hΘ'.isWedgeLinear_of_isNiceElement f'.nice) hΘ'
    (hΘ'.isWedgeLinear_of_isNiceElement f'.nice) p x

end ChartFrame

end Stacks.FormsTrace

end
