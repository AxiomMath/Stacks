module

public import StacksFrontier.Homology.CyclesShortComplex
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# Dimension shifting along an acyclic complex

Let `F` be an additive functor out of an abelian category with enough injectives and let
`K` be an acyclic cochain complex, bounded above, all of whose terms have vanishing right
derived functors `RᵠF` in the degrees `q < n`. Splitting `K` into the short exact sequences
`0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0` of its cycles, the cycles have vanishing `RᵠF` in the same degrees,
and if moreover `K` vanishes in negative degrees, then

`0 ⟶ RⁿF(K⁰) ⟶ RⁿF(K¹) ⟶ RⁿF(K²)`

is exact.

## Main results

* `Stacks.Homology.AcyclicDimensionShifting.isZero_rightDerived_cycles`: the cycles of `K`
  have vanishing `RᵠF` for `q < n`.
* `Stacks.Homology.AcyclicDimensionShifting.mono_rightDerived_map_d_zero`: `RⁿF(K⁰) ⟶ RⁿF(K¹)`
  is a monomorphism.
* `Stacks.Homology.AcyclicDimensionShifting.exact_rightDerived_map_d`: `RⁿF(K⁰) ⟶ RⁿF(K¹) ⟶
  RⁿF(K²)` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Homology.AcyclicDimensionShifting

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] {K : CochainComplex C ℤ} (hK : K.Acyclic)

omit [EnoughInjectives C] in
include hK in
/-- The short exact sequence `0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0` of an acyclic complex. -/
theorem shortExact_cyclesShortComplex (j : ℤ) :
    (HomologicalComplex.cyclesShortComplex K j (j + 1)).ShortExact :=
  HomologicalComplex.cyclesShortComplex_shortExact K
    (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl) (hK (j + 1))

include hK in
/-- **The cycles of an acyclic complex inherit the vanishing of the lower derived functors of
its terms**, when the complex is bounded above. -/
theorem isZero_rightDerived_cycles (n : ℕ) (m : ℤ) (hm : ∀ j, m ≤ j → IsZero (K.X j))
    (hvan : ∀ (j : ℤ) (q : ℕ), q < n → IsZero ((F.rightDerived q).obj (K.X j)))
    (j : ℤ) (q : ℕ) (hq : q < n) : IsZero ((F.rightDerived q).obj (K.cycles j)) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m - j ≤ t := ⟨(m - j).toNat, Int.self_le_toNat _⟩
  induction t generalizing j q with
  | zero =>
    have hX : IsZero (K.X j) := hm j (by omega)
    exact Functor.map_isZero _ (IsZero.of_mono (K.iCycles j) hX)
  | succ t ih =>
    have hS := shortExact_cyclesShortComplex hK j
    cases q with
    | zero =>
      have hh := (Stacks.Cohomology.RightDerivedDelta.horseshoe hS).mono_rightDerived_zero_map_f F
      exact @IsZero.of_mono _ _ _ _ _ _ hh (hvan j 0 hq)
    | succ q =>
      exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁ hS F q
        (ih (j + 1) q (by omega) (by omega)) (hvan j (q + 1) hq)

omit [EnoughInjectives C] in
include hK in
/-- The map `Kⁱ ⟶ Zʲ` induced by the differential is an isomorphism when `Kⁱ⁻¹` vanishes. -/
theorem isIso_toCycles {i j : ℤ} (hij : i + 1 = j) (h : IsZero (K.X (i - 1))) :
    IsIso (K.toCycles i j) := by
  subst hij
  have hS := shortExact_cyclesShortComplex hK i
  have hS' := shortExact_cyclesShortComplex hK (i - 1)
  have hZ : IsZero (K.cycles i) := by
    have : Epi (K.toCycles (i - 1) (i - 1 + 1)) := hS'.epi_g
    have h' : IsZero (K.cycles (i - 1 + 1)) := IsZero.of_epi (K.toCycles (i - 1) (i - 1 + 1)) h
    simpa using h'
  exact (hS.isIso_g_iff).2 hZ

include hK in
/-- `Rⁿ⁺¹F(Zⁱ) ⟶ Rⁿ⁺¹F(Kⁱ)` is a monomorphism when `RⁿF(Zʲ)` vanishes, `j = i + 1`. -/
theorem mono_rightDerived_iCycles (n : ℕ) {i j : ℤ} (hij : i + 1 = j)
    (h : IsZero ((F.rightDerived n).obj (K.cycles j))) :
    Mono ((F.rightDerived (n + 1)).map (K.iCycles i)) := by
  subst hij
  have hS := shortExact_cyclesShortComplex hK i
  obtain ⟨δ, -, hex⟩ :=
    Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅ hS F
  exact ((hex n).exact 2).mono_g (h.eq_of_src _ _)

/-- `Rⁿ⁺¹F(Zⁱ) ⟶ Rⁿ⁺¹F(Kⁱ)` is a monomorphism under the vanishing hypotheses of
`mono_rightDerived_map_d_zero`. -/
private theorem mono_rightDerived_iCycles_of_vanishing (hK : K.Acyclic) (n : ℕ) (m : ℤ)
    (hm : ∀ j, m ≤ j → IsZero (K.X j))
    (hvan : ∀ (j : ℤ) (q : ℕ), q < n + 1 → IsZero ((F.rightDerived q).obj (K.X j))) (i : ℤ) :
    Mono ((F.rightDerived (n + 1)).map (K.iCycles i)) :=
  mono_rightDerived_iCycles F hK n rfl
    (isZero_rightDerived_cycles F hK (n + 1) m hm hvan (i + 1) n (by omega))

include hK in
/-- **`RⁿF(K⁰) ⟶ RⁿF(K¹)` is a monomorphism** for an acyclic complex vanishing in negative
degrees and above some degree, whose terms have vanishing `RᵠF` for `q < n`, `n ≥ 1`. -/
theorem mono_rightDerived_map_d_zero (n : ℕ) (m : ℤ) (hm : ∀ j, m ≤ j → IsZero (K.X j))
    (hvan : ∀ (j : ℤ) (q : ℕ), q < n + 1 → IsZero ((F.rightDerived q).obj (K.X j)))
    (hneg : IsZero (K.X (-1))) :
    Mono ((F.rightDerived (n + 1)).map (K.d 0 1)) := by
  have hiso : IsIso (K.toCycles 0 1) := isIso_toCycles hK (by norm_num) (by simpa using hneg)
  have hmono := mono_rightDerived_iCycles_of_vanishing F hK n m hm hvan 1
  rw [← HomologicalComplex.toCycles_i K 0 1, Functor.map_comp]
  infer_instance

include hK in
/-- **`RⁿF(K⁰) ⟶ RⁿF(K¹) ⟶ RⁿF(K²)` is exact** for an acyclic complex vanishing in negative
degrees and above some degree, whose terms have vanishing `RᵠF` for `q < n`, `n ≥ 1`. -/
theorem exact_rightDerived_map_d (n : ℕ) (m : ℤ) (hm : ∀ j, m ≤ j → IsZero (K.X j))
    (hvan : ∀ (j : ℤ) (q : ℕ), q < n + 1 → IsZero ((F.rightDerived q).obj (K.X j)))
    (hneg : IsZero (K.X (-1))) :
    (ShortComplex.mk ((F.rightDerived (n + 1)).map (K.d 0 1))
      ((F.rightDerived (n + 1)).map (K.d 1 2))
      (by rw [← Functor.map_comp, K.d_comp_d, Functor.map_zero])).Exact := by
  have hiso : IsIso (K.toCycles 0 1) := isIso_toCycles hK (by norm_num) (by simpa using hneg)
  have hmono := mono_rightDerived_iCycles_of_vanishing F hK n m hm hvan 2
  have hS := shortExact_cyclesShortComplex hK 1
  obtain ⟨δ, -, hex⟩ :=
    Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅ hS F
  have h0 : (ShortComplex.mk ((F.rightDerived (n + 1)).map (K.iCycles 1))
      ((F.rightDerived (n + 1)).map (K.toCycles 1 2))
      (by rw [← Functor.map_comp]
          exact (congrArg _ (HomologicalComplex.cyclesShortComplex K 1 2).zero).trans
            (Functor.map_zero _ _ _))).Exact :=
    (hex (n + 1)).exact 0
  let φ : ShortComplex.mk ((F.rightDerived (n + 1)).map (K.iCycles 1))
      ((F.rightDerived (n + 1)).map (K.toCycles 1 2))
      (by rw [← Functor.map_comp]
          exact (congrArg _ (HomologicalComplex.cyclesShortComplex K 1 2).zero).trans
            (Functor.map_zero _ _ _)) ⟶
    ShortComplex.mk ((F.rightDerived (n + 1)).map (K.d 0 1))
      ((F.rightDerived (n + 1)).map (K.d 1 2))
      (by rw [← Functor.map_comp, K.d_comp_d, Functor.map_zero]) :=
    { τ₁ := inv ((F.rightDerived (n + 1)).map (K.toCycles 0 1))
      τ₂ := 𝟙 _
      τ₃ := (F.rightDerived (n + 1)).map (K.iCycles 2)
      comm₁₂ := by
        dsimp
        rw [Category.comp_id, IsIso.inv_comp_eq, ← Functor.map_comp,
          HomologicalComplex.toCycles_i]
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, ← Functor.map_comp, HomologicalComplex.toCycles_i] }
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; exact hmono
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h0

end Stacks.Homology.AcyclicDimensionShifting

end
