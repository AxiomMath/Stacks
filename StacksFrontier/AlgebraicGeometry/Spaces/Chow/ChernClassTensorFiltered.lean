module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassDualFiltered
public import StacksFrontier.RingTheory.PowerSeries.ProdOneAddMulX
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The Chern classes of a tensor product of filtered modules

In Situation 0EDT let `P/B` be good and let `ℰ`, `ℱ` be finite locally free `𝒪_P`-modules with
filtrations of lengths `r`, `s` whose successive quotients `ℒ_1, …, ℒ_r` and `𝒩_1, …, 𝒩_s` are
invertible. Writing `x_i = c₁(ℒ_i)` and `y_j = c₁(𝒩_j)`,

  `c(ℰ) = ∏ (1 + x_i)`,  `c(ℱ) = ∏ (1 + y_j)`,  `c(ℰ ⊗ ℱ) = ∏_{i,j} (1 + x_i + y_j)`,

with the degree recorded by a power of `X`; and so

  `c₁(ℰ ⊗ ℱ) = r c₁(ℱ) + s c₁(ℰ)`,
  `c₂(ℰ ⊗ ℱ) = r c₂(ℱ) + s c₂(ℰ) + C(r,2) c₁(ℱ)² + (r s - 1) c₁(ℱ) c₁(ℰ) + C(s,2) c₁(ℰ)²`.

This is the computation of the proof of Stacks 0ESE after the reduction by the splitting
principle, derived from the properties of the Chern classes of chapter 82 which it uses, carried
as hypotheses as in `AlgebraicGeometry.Space.PrivateChern.chernCap_dual_of_hasFiltrationOfLength`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernSeries_of_rank_one`: `c(ℒ) = 1 + c₁(ℒ) X` for `ℒ` of
  rank one.
* `AlgebraicGeometry.Space.PrivateChern.exists_chernSeries_tensorObj_eq_prod`: the product
  formulas for a pair of filtered modules.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_tensorObj_of_hasFiltrationOfLength`: the
  identities for `c₁` and `c₂` of a tensor product of filtered modules.

## References

* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory PowerSeries

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}}

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

attribute [local instance 10000] smallEtaleModulesAbelian

/-- Cokernels of `𝒪_X`-modules, from the abelian structure at the universe of the schemes. -/
local instance (priority := high) instHasCokernelsModules' {D : BaseSpaceDimensionSituation.{u}}
    {X : D.Ambient} (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    CategoryTheory.Limits.HasCokernels (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  letI : Abelian (Modules.{u, u} D.site D.base D.base_mem X hX₁) := SheafOfModules.instAbelian _
  inferInstance

variable {P : D.Ambient} {sP : P ⟶ D.space} {hP : D.IsGood sP}

/-- **The total Chern class of a module of rank one is `1 + c₁ X`**, given that Chern classes
vanish above the rank. -/
theorem chernSeries_of_rank_one
    (hvan : ∀ (E : Modules.{u, u} D.site D.base D.base_mem P hP.1) r h n, r < n →
      chernCap.{u, v} (hX := hP) E r h n = 0)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (h : IsFiniteLocallyFreeOfRank D sP hP L 1) :
    PowerSeries.mk (chernCap.{u, v} (hX := hP) L 1 h) =
      1 + C (chernCap.{u, v} (hX := hP) L 1 h 1) * PowerSeries.X := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | _ | n
  · simp [chernCap_zero]
  · simp [coeff_one]
  · rw [coeff_mk, hvan L 1 h (n + 2) (by omega)]
    simp [coeff_one]

/-- **The product formulas for a pair of filtered modules.** For `ℰ`, `ℱ` with filtrations of
lengths `r`, `s` by invertible modules there are lists `ℒ_1, …, ℒ_r` and `𝒩_1, …, 𝒩_s` of
invertible modules, the successive quotients, with
`c(ℰ) = ∏ (1 + c₁(ℒ_i) X)`, `c(ℱ) = ∏ (1 + c₁(𝒩_j) X)` and
`c(ℰ ⊗ ℱ) = ∏_{i,j} (1 + (c₁(ℒ_i) + c₁(𝒩_j)) X)`, the pairs in lexicographic order. -/
theorem exists_chernSeries_tensorObj_eq_prod
    (hvan : ∀ (E : Modules.{u, u} D.site D.base D.base_mem P hP.1) r h n, r < n →
      chernCap.{u, v} (hX := hP) E r h n = 0)
    (hwhit : ∀ (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1)),
      T.ShortExact → ∀ (r₁ r₃ : ℕ) h₁ h₂ h₃ (n : ℕ),
        chernCap.{u, v} (hX := hP) T.X₂ (r₁ + r₃) h₂ n =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
            chernCap.{u, v} (hX := hP) T.X₁ r₁ h₁ p.1 *
              chernCap.{u, v} (hX := hP) T.X₃ r₃ h₃ p.2)
    (hc1 : ∀ (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1) hL hM hLM,
      chernCap.{u, v} (hX := hP) (L ⊗ M) 1 hLM 1 =
        chernCap.{u, v} (hX := hP) L 1 hL 1 + chernCap.{u, v} (hX := hP) M 1 hM 1)
    {r s : ℕ} {E F : Modules.{u, u} D.site D.base D.base_mem P hP.1}
    (hE : (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength r E)
    (hF : (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength s F) :
    ∃ Ls Ns : List {L : Modules.{u, u} D.site D.base D.base_mem P hP.1 //
        IsInvertibleModule (goodSpace hP) L}, Ls.length = r ∧ Ns.length = s ∧
      PowerSeries.mk (chernCap.{u, v} (hX := hP) E r
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE)) =
        (Ls.map fun L => 1 + C (chernCap.{u, v} (hX := hP) L.1 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1) *
            PowerSeries.X).prod ∧
      PowerSeries.mk (chernCap.{u, v} (hX := hP) F s
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hF)) =
        (Ns.map fun N => 1 + C (chernCap.{u, v} (hX := hP) N.1 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) N.2) 1) *
            PowerSeries.X).prod ∧
      PowerSeries.mk (chernCap.{u, v} (hX := hP) (E ⊗ F) (r * s)
          (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem P hP.1
            (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE)
            (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hF))) =
        (Ls.flatMap fun L => Ns.map fun N =>
          1 + C (chernCap.{u, v} (hX := hP) L.1 1
              (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1 +
            chernCap.{u, v} (hX := hP) N.1 1
              (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) N.2) 1) *
            PowerSeries.X).prod := by
  let c : ∀ (r : ℕ) (E : Modules.{u, u} D.site D.base D.base_mem P hP.1),
      IsFiniteLocallyFreeOfRank D sP hP E r →
        PowerSeries (AddMonoid.End (chowHomology.{u, v} D sP hP)) :=
    fun r E h => PowerSeries.mk (chernCap.{u, v} (hX := hP) E r h)
  have hzero : ∀ E h, c 0 E h = 1 := by
    intro E h
    refine PowerSeries.ext fun n => ?_
    rcases n with _ | n
    · simp [c, chernCap_zero]
    · simp [c, hvan E 0 h (n + 1) (Nat.succ_pos n), PowerSeries.coeff_one]
  have hmul : ∀ (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1)),
      T.ShortExact → ∀ (r₁ r₃ : ℕ) h₁ h₂ h₃, c (r₁ + r₃) T.X₂ h₂ = c r₁ T.X₁ h₁ * c r₃ T.X₃ h₃ := by
    intro T hT r₁ r₃ h₁ h₂ h₃
    refine PowerSeries.ext fun n => ?_
    simp only [c, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    exact hwhit T hT r₁ r₃ h₁ h₂ h₃ n
  obtain ⟨Ls, Ns, hLlen, hNlen, hcE, hcF, hcEF⟩ :=
    exists_lists_tensor_of_hasFiltrationOfLength c hzero hmul hE hF
  refine ⟨Ls, Ns, hLlen, hNlen, ?_, ?_, ?_⟩
  rotate_left 2
  · refine hcEF.trans (congrArg List.prod (List.flatMap_congr fun L _ =>
      List.map_congr_left fun N _ => ?_))
    have h1 := isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem P hP.1
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2)
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) N.2)
    have h1' : IsFiniteLocallyFreeOfRank D sP hP (L.1 ⊗ N.1) 1 := Nat.mul_one 1 ▸ h1
    rw [invariant_congr (Z := goodSpace hP) c (Nat.mul_one 1) _ h1']
    change PowerSeries.mk (chernCap.{u, v} (hX := hP) (L.1 ⊗ N.1) 1 h1') = _
    rw [chernSeries_of_rank_one hvan _ h1', hc1]
  all_goals
    first | refine hcE.trans ?_ | refine hcF.trans ?_
    refine congrArg List.prod (List.map_congr_left fun L _ => ?_)
    exact chernSeries_of_rank_one hvan L.1 _

/-- **The identities of Stacks 0ESE for a pair of filtered modules.** For `ℰ`, `ℱ` with filtrations
of lengths `r`, `s` by invertible modules, `c₁(ℰ ⊗ ℱ) = r c₁(ℱ) + s c₁(ℰ)` and
`c₂(ℰ ⊗ ℱ) = r c₂(ℱ) + s c₂(ℰ) + C(r,2) c₁(ℱ)² + (r s - 1) c₁(ℱ) c₁(ℰ) + C(s,2) c₁(ℰ)²`, from the
properties of the Chern classes carried as hypotheses. -/
theorem chernCap_tensorObj_of_hasFiltrationOfLength
    (hvan : ∀ (E : Modules.{u, u} D.site D.base D.base_mem P hP.1) r h n, r < n →
      chernCap.{u, v} (hX := hP) E r h n = 0)
    (hwhit : ∀ (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1)),
      T.ShortExact → ∀ (r₁ r₃ : ℕ) h₁ h₂ h₃ (n : ℕ),
        chernCap.{u, v} (hX := hP) T.X₂ (r₁ + r₃) h₂ n =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
            chernCap.{u, v} (hX := hP) T.X₁ r₁ h₁ p.1 *
              chernCap.{u, v} (hX := hP) T.X₃ r₃ h₃ p.2)
    (hc1 : ∀ (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1) hL hM hLM,
      chernCap.{u, v} (hX := hP) (L ⊗ M) 1 hLM 1 =
        chernCap.{u, v} (hX := hP) L 1 hL 1 + chernCap.{u, v} (hX := hP) M 1 hM 1)
    (hcomm : ∀ (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1) hL hM,
      Commute (chernCap.{u, v} (hX := hP) L 1 hL 1) (chernCap.{u, v} (hX := hP) M 1 hM 1))
    {r s : ℕ} {E F : Modules.{u, u} D.site D.base D.base_mem P hP.1}
    (hE : (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength r E)
    (hF : (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength s F) :
    let hr := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE
    let hs := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hF
    let hrs := isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem P hP.1 hr hs
    chernCap.{u, v} (hX := hP) (E ⊗ F) (r * s) hrs 1 =
        (r : ℤ) • chernCap.{u, v} (hX := hP) F s hs 1 +
          (s : ℤ) • chernCap.{u, v} (hX := hP) E r hr 1 ∧
      chernCap.{u, v} (hX := hP) (E ⊗ F) (r * s) hrs 2 =
        (r : ℤ) • chernCap.{u, v} (hX := hP) F s hs 2 +
          (s : ℤ) • chernCap.{u, v} (hX := hP) E r hr 2 +
          (r.choose 2 : ℤ) • chernCap.{u, v} (hX := hP) F s hs 1 ^ 2 +
          ((r : ℤ) * s - 1) •
            (chernCap.{u, v} (hX := hP) F s hs 1 * chernCap.{u, v} (hX := hP) E r hr 1) +
          (s.choose 2 : ℤ) • chernCap.{u, v} (hX := hP) E r hr 1 ^ 2 := by
  intro hr hs hrs
  obtain ⟨Ls, Ns, hLlen, hNlen, hcE, hcF, hcEF⟩ :=
    exists_chernSeries_tensorObj_eq_prod hvan hwhit hc1 hE hF
  set x : {L : Modules.{u, u} D.site D.base D.base_mem P hP.1 //
      IsInvertibleModule (goodSpace hP) L} → AddMonoid.End (chowHomology.{u, v} D sP hP) :=
    fun L => chernCap.{u, v} (hX := hP) L.1 1
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1 with hx
  have hcomm' : ∀ a ∈ Ls.map x ++ Ns.map x, ∀ b ∈ Ls.map x ++ Ns.map x, Commute a b := by
    intro a ha b hb
    obtain ⟨L, -, rfl⟩ : ∃ L, L ∈ Ls ++ Ns ∧ x L = a := by
      rw [← List.map_append] at ha
      exact List.mem_map.1 ha
    obtain ⟨M, -, rfl⟩ : ∃ M, M ∈ Ls ++ Ns ∧ x M = b := by
      rw [← List.map_append] at hb
      exact List.mem_map.1 hb
    exact hcomm _ _ _ _
  have eEF : PowerSeries.mk (chernCap.{u, v} (hX := hP) (E ⊗ F) (r * s) hrs) =
      ((Ls.map x).flatMap fun a => (Ns.map x).map fun b => 1 + C (a + b) * PowerSeries.X).prod := by
    rw [hcEF, List.flatMap_map]
    simp only [List.map_map]
    rfl
  have c1 := coeff_one_list_prod_one_add_C_add_mul_X_of_commute (Ls.map x) (Ns.map x) hcomm'
  have c2 := coeff_two_list_prod_one_add_C_add_mul_X_of_commute (Ls.map x) (Ns.map x) hcomm'
  rw [← eEF] at c1 c2
  simp only [List.map_map, Function.comp_def, hx] at c1 c2
  rw [← hcE, ← hcF] at c1 c2
  simp only [coeff_mk, List.length_map, hLlen, hNlen] at c1 c2
  exact ⟨c1.trans (add_comm _ _), c2.trans (by abel)⟩

end AlgebraicGeometry.Space.PrivateChern

end
