module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.DualMultiplicativeInvariant
public import StacksFrontier.RingTheory.PowerSeries.NegXHom

/-!
# The sign rule for the Chern classes of the dual of a filtered module

In Situation 0EDT let `P/B` be good and let `𝒢` be a finite locally free `𝒪_P`-module with a
filtration of length `r` whose successive quotients are invertible. Then

  `c_i(𝒢^∨) = (-1)^i c_i(𝒢)`

as operations on `CH_*(P)`. This is the computation of the proof of Stacks 0ESD after the
reduction by the splitting principle: the dual filtration has the quotients `ℒ_i^∨`, of first
Chern class `-c₁(ℒ_i)`, so `c(𝒢) = ∏ (1 + x_i)` and `c(𝒢^∨) = ∏ (1 - x_i)`.

It is derived here from the properties of the Chern classes of chapter 82 which the proof uses,
taken as hypotheses: vanishing above the rank, the Whitney formula (Stacks 0ES9), additivity of
`c₁` on tensor products of invertible modules and `c₁(𝒪) = 0` (Stacks 0EQK), invariance under
isomorphism, and the commutativity of the caps with first Chern classes (Stacks 0EQZ).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.commute_chernCap_of_rank_one`: Chern classes of modules of
  rank one commute when their first Chern classes do.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_dual_of_hasFiltrationOfLength`: the sign rule
  for a module with a filtration by invertible modules.

## Implementation notes

The total Chern class is packaged as the power series `∑ c_n(ℰ) X^n` over the ring of additive
endomorphisms of `CH_*(P)`, so that the Whitney formula is multiplicativity, and the sign rule is
the statement that `c(𝒢^∨)` is the image of `c(𝒢)` under `X ↦ -X`
(`PowerSeries.negXHom`); `AlgebraicGeometry.Space.map_dual_of_hasFiltrationOfLength` passes it
along the filtration.

## References

* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
* [Stacks Project, Tag 0ES9](https://stacks.math.columbia.edu/tag/0ES9)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 0EQZ](https://stacks.math.columbia.edu/tag/0EQZ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}}

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

attribute [local instance 10000] smallEtaleModulesAbelian

/-- Cokernels of `𝒪_X`-modules, from the abelian structure at the universe of the schemes; given
as a term, instance search otherwise stopping on a universe constraint once the Chern class API is
imported. -/
local instance (priority := high) instHasCokernelsModules {D : BaseSpaceDimensionSituation.{u}}
    {X : D.Ambient} (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    CategoryTheory.Limits.HasCokernels (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  letI : Abelian (Modules.{u, u} D.site D.base D.base_mem X hX₁) := SheafOfModules.instAbelian _
  inferInstance

/-- **Chern classes of modules of rank one commute** as soon as their first Chern classes do,
the higher ones vanishing. -/
theorem commute_chernCap_of_rank_one {P : D.Ambient} {sP : P ⟶ D.space} {hP : D.IsGood sP}
    (hvan : ∀ (E : Modules.{u, u} D.site D.base D.base_mem P hP.1) r h n, r < n →
      chernCap.{u, v} (hX := hP) E r h n = 0)
    (hcomm : ∀ (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1) hL hM,
      Commute (chernCap.{u, v} (hX := hP) L 1 hL 1) (chernCap.{u, v} (hX := hP) M 1 hM 1))
    (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsFiniteLocallyFreeOfRank D sP hP L 1)
    (hM : IsFiniteLocallyFreeOfRank D sP hP M 1) (i j : ℕ) :
    Commute (chernCap.{u, v} (hX := hP) L 1 hL i) (chernCap.{u, v} (hX := hP) M 1 hM j) := by
  rcases i with _ | _ | i
  · rw [chernCap_zero]; exact Commute.one_left _
  · rcases j with _ | _ | j
    · rw [chernCap_zero]; exact Commute.one_right _
    · exact hcomm L M hL hM
    · rw [hvan M 1 hM (j + 2) (by omega)]; exact Commute.zero_right _
  · rw [hvan L 1 hL (i + 2) (by omega)]; exact Commute.zero_left _

/-- **The sign rule of Stacks 0ESD for a module with a filtration by invertible modules**, from the
properties of the Chern classes of chapter 82 carried as hypotheses: vanishing above the rank
(`hvan`), the Whitney formula (`hwhit`), additivity of `c₁` on tensor products of invertible
modules (`hc1`) and `c₁(𝒪) = 0` (`hunit`), invariance under isomorphism (`hiso`), and the
commutativity of the first Chern classes of modules of rank one (`hcomm`). -/
theorem chernCap_dual_of_hasFiltrationOfLength {P : D.Ambient} {sP : P ⟶ D.space}
    {hP : D.IsGood sP}
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
    (hiso : ∀ (E E' : Modules.{u, u} D.site D.base D.base_mem P hP.1) r h h' n,
      Nonempty (E ≅ E') →
        chernCap.{u, v} (hX := hP) E r h n = chernCap.{u, v} (hX := hP) E' r h' n)
    (hunit : ∀ h, chernCap.{u, v} (hX := hP) (𝟙_ _) 1 h 1 = 0)
    (hcomm : ∀ (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1) hL hM,
      Commute (chernCap.{u, v} (hX := hP) L 1 hL 1) (chernCap.{u, v} (hX := hP) M 1 hM 1))
    {r : ℕ} {G : Modules.{u, u} D.site D.base D.base_mem P hP.1}
    (hG : (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength r G)
    (i : ℕ) :
    chernCap.{u, v} (hX := hP) ((ihom G).obj (𝟙_ _)) r
        (isFiniteLocallyFreeOfRank_dual D.site D.base D.base_mem P hP.1 G
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hG)) i =
      (-1 : ℤ) ^ i • chernCap.{u, v} (hX := hP) G r
        (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hG) i := by
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
  have key := map_dual_of_hasFiltrationOfLength c (PowerSeries.negXHom _) hzero hmul ?_ ?_ hG
  · have := congrArg (PowerSeries.coeff i) key
    simp only [c, PowerSeries.coeff_mk, PowerSeries.coeff_negXHom] at this
    rw [this, zsmul_eq_mul]
    push_cast
    rfl
  · intro L hL
    refine PowerSeries.ext fun n => ?_
    simp only [c, PowerSeries.coeff_mk, PowerSeries.coeff_negXHom]
    rcases n with _ | _ | n
    · simp [chernCap_zero]
    · have h := eq_neg_of_dual (Z := goodSpace hP)
        (fun L hL => chernCap.{u, v} (hX := hP) L 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) hL) 1)
        (fun L M hL hM hLM => hc1 L M _ _ _)
        (fun L L' hL hL' e => hiso L L' 1 _ _ 1 e) (fun h => hunit _) hL
      simp only at h
      rw [h, pow_one, neg_one_mul]
    · rw [hvan _ 1 _ (n + 2) (by omega), hvan _ 1 _ (n + 2) (by omega), mul_zero]
  · intro r A L hA hL
    obtain ⟨Ls, -, hcA, -⟩ := exists_list_of_hasFiltrationOfLength c hzero hmul hA
    rw [hcA]
    refine Commute.list_prod_left _ _ fun x hx => ?_
    obtain ⟨M, -, rfl⟩ := List.mem_map.1 hx
    exact PowerSeries.commute_mk fun i j => commute_chernCap_of_rank_one hvan hcomm _ _ _ _ i j

end AlgebraicGeometry.Space.PrivateChern

end
