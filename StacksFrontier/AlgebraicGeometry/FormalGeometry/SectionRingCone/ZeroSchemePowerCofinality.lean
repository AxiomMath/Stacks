module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodQuotientSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap

/-!
# Infinitesimal section completeness only depends on the ideal up to cofinality

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `I`, `J` two quasi-coherent ideal
sheaves with `I ^ e ⊆ J ⊆ I` for some `e ≥ 1`. The towers of quotients `F / I^(n+1) F` and
`F / J^(n+1) F` are then cofinal in each other, since `I^(e(n+1)) ⊆ J^(n+1) ⊆ I^(n+1)`, so they
have the same compatible families of global sections. This file proves the resulting statement
about the infinitesimal neighbourhoods of the two closed subschemes: the global sections of `F`
are the inverse limit of its sections over the infinitesimal neighbourhoods of `V(J)` exactly
when they are the inverse limit over those of `V(I)`.

The case met in practice is the zero scheme of a power: for a section `s` of an invertible
module, `Z(s^e)` is cut out by the `e`-th power of the ideal of `Z(s)`, so infinitesimal section
completeness along `Z(s)` and along `Z(s^e)` are the same condition.

## Main definitions

* `Stacks.Algebraization.SectionRingCone.idealPowerQuotientMap` — the canonical map
  `F / I^a F ⟶ F / J^b F` for `I^a ⊆ J^b`.
* `Stacks.Algebraization.SectionRingCone.IsIdealPowerQuotientSectionsComplete` — every compatible
  family of global sections of the quotients `F / I^(n+1) F` has a unique antecedent in `Γ(X, F)`.

## Main results

* `Stacks.Algebraization.SectionRingCone.isInfinitesimalSectionsComplete_iff_quotientSections` —
  for a closed immersion with ideal sheaf `J`, infinitesimal section completeness of `F` is
  `IsIdealPowerQuotientSectionsComplete J F`.
* `Stacks.Algebraization.SectionRingCone.isIdealPowerQuotientSectionsComplete_iff_of_pow_le` —
  the cofinality statement for the quotient towers.
* `Stacks.Algebraization.SectionRingCone.isInfinitesimalSectionsComplete_subschemeι_iff_of_pow_le`
  — **the cofinality statement for infinitesimal section completeness**: for `I ^ e ≤ J ≤ I` and
  `e ≥ 1`, completeness along `J.subschemeι` and along `I.subschemeι` agree.

## Implementation notes

Compatibility of a family of quotient sections is asked for every pair `n ≤ m`, as
`Stacks.Algebraization.IsInfinitesimalSectionsComplete` asks it, so that the two predicates are
literally exchanged by the bijections `neighbourhoodQuotientSectionsTopEquiv`.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization.SectionRingCone

variable {X : Scheme.{u}}

/-- **The canonical map `F / I^a F ⟶ F / J^b F`**, for `I^a ⊆ J^b`: the descent of the projection
onto `F / J^b F` through the projection onto `F / I^a F`. -/
def idealPowerQuotientMap (I J : X.IdealSheafData) {a b : ℕ} (h : I ^ a ≤ J ^ b)
    (F : X.Modules) [F.IsQuasicoherent] :
    Stacks.Algebraization.idealPowerQuotient I a F ⟶
      Stacks.Algebraization.idealPowerQuotient J b F :=
  Stacks.Algebraization.idealPowerQuotientDesc I a
    (cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple J b F).ι)
    (Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot_of_pow_le h F)

/-- The canonical map between quotients is compatible with the two projections. -/
@[reassoc]
theorem π_idealPowerQuotientMap (I J : X.IdealSheafData) {a b : ℕ} (h : I ^ a ≤ J ^ b)
    (F : X.Modules) [F.IsQuasicoherent] :
    cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple I a F).ι ≫
        idealPowerQuotientMap I J h F =
      cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple J b F).ι :=
  Stacks.Algebraization.idealPowerQuotientDesc_π _ _ _ _

/-- **A map between the quotients is determined by its compatibility with the projections.** -/
theorem eq_idealPowerQuotientMap (I J : X.IdealSheafData) {a b : ℕ} (h : I ^ a ≤ J ^ b)
    (F : X.Modules) [F.IsQuasicoherent]
    (τ : Stacks.Algebraization.idealPowerQuotient I a F ⟶
      Stacks.Algebraization.idealPowerQuotient J b F)
    (hτ : cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple I a F).ι ≫ τ =
      cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple J b F).ι) :
    τ = idealPowerQuotientMap I J h F := by
  have : Epi (cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple I a F).ι) :=
    coequalizer.π_epi
  exact (cancel_epi _).1 (hτ.trans (π_idealPowerQuotientMap I J h F).symm)

/-- **The canonical maps compose.** -/
theorem idealPowerQuotientMap_comp (I J K : X.IdealSheafData) {a b c : ℕ}
    (h : I ^ a ≤ J ^ b) (h' : J ^ b ≤ K ^ c) (F : X.Modules) [F.IsQuasicoherent] :
    idealPowerQuotientMap I J h F ≫ idealPowerQuotientMap J K h' F =
      idealPowerQuotientMap I K (h.trans h') F :=
  eq_idealPowerQuotientMap I K (h.trans h') F _ (by
    rw [π_idealPowerQuotientMap_assoc, π_idealPowerQuotientMap])

/-- The canonical maps on global sections compose. -/
theorem idealPowerQuotientMap_app_comp (I J K : X.IdealSheafData) {a b c : ℕ}
    (h : I ^ a ≤ J ^ b) (h' : J ^ b ≤ K ^ c) (F : X.Modules) [F.IsQuasicoherent]
    (y : Γ(Stacks.Algebraization.idealPowerQuotient I a F, ⊤)) :
    (idealPowerQuotientMap J K h' F).app ⊤ ((idealPowerQuotientMap I J h F).app ⊤ y) =
      (idealPowerQuotientMap I K (h.trans h') F).app ⊤ y := by
  rw [← idealPowerQuotientMap_comp I J K h h' F]
  rfl

/-- The canonical maps on global sections are compatible with the projections. -/
theorem idealPowerQuotientMap_app_π (I J : X.IdealSheafData) {a b : ℕ} (h : I ^ a ≤ J ^ b)
    (F : X.Modules) [F.IsQuasicoherent] (t : Γ(F, ⊤)) :
    (idealPowerQuotientMap I J h F).app ⊤
        ((cokernel.π (C := X.Modules)
          (Stacks.Algebraization.idealPowerMultiple I a F).ι).app ⊤ t) =
      (cokernel.π (C := X.Modules)
        (Stacks.Algebraization.idealPowerMultiple J b F).ι).app ⊤ t := by
  rw [← π_idealPowerQuotientMap I J h F]
  rfl

/-- `I ^ m ≤ I ^ n` for `n ≤ m`. -/
theorem idealSheafData_pow_le_pow (I : X.IdealSheafData) {n m : ℕ} (h : n ≤ m) :
    I ^ m ≤ I ^ n :=
  fun _ => Ideal.pow_le_pow_right h

/-- **Completeness of the global sections against the tower of quotients `F / I^(n+1) F`**:
every family of global sections of the quotients that is compatible under the canonical maps has
a unique antecedent in `Γ(X, F)`. -/
def IsIdealPowerQuotientSectionsComplete (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] : Prop :=
  ∀ σ : ∀ n : ℕ, Γ(Stacks.Algebraization.idealPowerQuotient I (n + 1) F, ⊤),
    (∀ (n m : ℕ) (h : n ≤ m),
      (idealPowerQuotientMap I I (idealSheafData_pow_le_pow I (Nat.succ_le_succ h)) F).app ⊤
        (σ m) = σ n) →
    ∃! t : Γ(F, ⊤), ∀ n : ℕ,
      (cokernel.π (C := X.Modules)
        (Stacks.Algebraization.idealPowerMultiple I (n + 1) F).ι).app ⊤ t = σ n

/-- **Infinitesimal section completeness is completeness against the quotient tower.** For a
closed immersion `i` with ideal sheaf `J`, the sections of `F` over the `n`-th infinitesimal
neighbourhood of `i` are the global sections of `F / J^(n+1) F` ([Stacks, Tag 0EL1], as
`Stacks.Algebraization.neighbourhoodQuotientSectionsTopEquiv`), compatibly with the projections
from `Γ(X, F)` and with the transition maps. -/
theorem isInfinitesimalSectionsComplete_iff_quotientSections {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (J : X.IdealSheafData) (hi : i.ker = J) (F : X.Modules)
    [F.IsQuasicoherent] :
    Stacks.Algebraization.IsInfinitesimalSectionsComplete i F ↔
      IsIdealPowerQuotientSectionsComplete J F := by
  let e := fun n => Stacks.Algebraization.neighbourhoodQuotientSectionsTopEquiv i J hi F n
  have hπ : ∀ (n : ℕ) (t : Γ(F, ⊤)), e n
      ((cokernel.π (C := X.Modules)
        (Stacks.Algebraization.idealPowerMultiple J (n + 1) F).ι).app ⊤ t) =
      AlgebraicGeometry.pullbackGlobalSections
        (Stacks.Algebraization.nthInfinitesimalNeighbourhoodι i n) F t := by
    intro n t
    refine ((Stacks.Algebraization.neighbourhoodQuotientSections_top i J hi F n _).symm).trans ?_
    exact Stacks.Algebraization.neighbourhoodQuotientSections_π i J hi F n _ t
  have htr : ∀ (n m : ℕ) (h : n ≤ m)
      (y : Γ(Stacks.Algebraization.idealPowerQuotient J (m + 1) F, ⊤)),
      AlgebraicGeometry.pullbackSectionsMap F
          (Stacks.Algebraization.nthInfinitesimalNeighbourhoodTransition i h) (e m y) =
        e n ((idealPowerQuotientMap J J
          (idealSheafData_pow_le_pow J (Nat.succ_le_succ h)) F).app ⊤ y) := fun n m h y =>
    Stacks.Algebraization.neighbourhoodQuotientSectionsTop_transition i J hi F h _
      (π_idealPowerQuotientMap _ _ _ F) y
  constructor
  · intro hc σ hσ
    obtain ⟨t, ht, huniq⟩ := hc (fun n => e n (σ n)) (fun n m h => by
      rw [htr n m h, hσ n m h])
    exact ⟨t, fun n => (e n).injective ((hπ n t).trans (ht n)),
      fun t' ht' => huniq t' fun n => by rw [← hπ n t', ht' n]⟩
  · intro hc s hs
    obtain ⟨t, ht, huniq⟩ := hc (fun n => (e n).symm (s n)) (fun n m h => by
      apply (e n).injective
      rw [← htr n m h, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hs n m h])
    refine ⟨t, fun n => ?_, fun t' ht' => huniq t' fun n => ?_⟩
    · rw [← hπ n t, ht n, Equiv.apply_symm_apply]
    · apply (e n).injective
      rw [hπ n t', ht' n, Equiv.apply_symm_apply]

/-- The arithmetic of the cofinality: `I ^ (e (n + 1)) ≤ J ^ (n + 1)` from `I ^ e ≤ J`. -/
theorem pow_mul_le_pow_of_pow_le {I J : X.IdealSheafData} {e : ℕ} (h : I ^ e ≤ J) (n : ℕ) :
    I ^ (e * n) ≤ J ^ n := by
  intro U
  change I.ideal U ^ (e * n) ≤ J.ideal U ^ n
  rw [pow_mul]
  exact Ideal.pow_right_mono (h U) n

/-- `J ^ n ≤ I ^ n` from `J ≤ I`. -/
theorem pow_le_pow_of_le {I J : X.IdealSheafData} (h : J ≤ I) (n : ℕ) : J ^ n ≤ I ^ n :=
  fun U => Ideal.pow_right_mono (h U) n

/-- A compatible family of quotient sections stays compatible when it is reindexed along a
monotone map `f` and pushed through the canonical maps `A ^ (f n + 1) ≤ B ^ (n + 1)`. -/
private theorem isCompatible_reindex (A B : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (f : ℕ → ℕ) (hf : ∀ n m, n ≤ m → f n ≤ f m)
    (h : ∀ n, A ^ (f n + 1) ≤ B ^ (n + 1))
    (σ : ∀ n : ℕ, Γ(Stacks.Algebraization.idealPowerQuotient A (n + 1) F, ⊤))
    (hσ : ∀ (n m : ℕ) (h : n ≤ m),
      (idealPowerQuotientMap A A (idealSheafData_pow_le_pow A (Nat.succ_le_succ h)) F).app ⊤
        (σ m) = σ n) (n m : ℕ) (hnm : n ≤ m) :
    (idealPowerQuotientMap B B (idealSheafData_pow_le_pow B (Nat.succ_le_succ hnm)) F).app ⊤
      ((idealPowerQuotientMap A B (h m) F).app ⊤ (σ (f m))) =
    (idealPowerQuotientMap A B (h n) F).app ⊤ (σ (f n)) := by
  rw [idealPowerQuotientMap_app_comp, ← hσ _ _ (hf n m hnm), idealPowerQuotientMap_app_comp]

/-- **The quotient towers of two cofinal ideals have the same complete sections.** If
`I ^ e ≤ J ≤ I` with `e ≥ 1`, then the global sections of `F` are complete against the tower
`F / J^(n+1) F` exactly when they are complete against `F / I^(n+1) F`. -/
theorem isIdealPowerQuotientSectionsComplete_iff_of_pow_le {I J : X.IdealSheafData} {e : ℕ}
    (he : 1 ≤ e) (hIJ : I ^ e ≤ J) (hJI : J ≤ I) (F : X.Modules) [F.IsQuasicoherent] :
    IsIdealPowerQuotientSectionsComplete J F ↔ IsIdealPowerQuotientSectionsComplete I F := by
  -- the index `e (n + 1) - 1` of the `I`-tower lying over the `n`-th term of the `J`-tower
  have hidx : ∀ n : ℕ, e * (n + 1) - 1 + 1 = e * (n + 1) := fun n => by
    have : 1 ≤ e * (n + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hle : ∀ n : ℕ, n ≤ e * (n + 1) - 1 := fun n => by
    have : n + 1 ≤ e * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hIJn : ∀ n : ℕ, I ^ (e * (n + 1) - 1 + 1) ≤ J ^ (n + 1) := fun n => by
    rw [hidx n]
    exact pow_mul_le_pow_of_pow_le hIJ (n + 1)
  have hJIn : ∀ n : ℕ, J ^ (n + 1) ≤ I ^ (n + 1) := fun n => pow_le_pow_of_le hJI (n + 1)
  constructor
  · intro hc σ hσ
    -- the `J`-family read off the `I`-family at the cofinal indices
    let τ : ∀ n : ℕ, Γ(Stacks.Algebraization.idealPowerQuotient J (n + 1) F, ⊤) := fun n =>
      (idealPowerQuotientMap I J (hIJn n) F).app ⊤ (σ (e * (n + 1) - 1))
    have hτ := isCompatible_reindex I J F (fun n => e * (n + 1) - 1)
      (fun n m h => by
        have : e * (n + 1) ≤ e * (m + 1) := Nat.mul_le_mul_left _ (by omega)
        omega) hIJn σ hσ
    obtain ⟨t, ht, huniq⟩ := hc τ hτ
    refine ⟨t, fun n => ?_, fun t' ht' => huniq t' fun n => by
      rw [← idealPowerQuotientMap_app_π I J (hIJn n) F t', ht']⟩
    rw [← idealPowerQuotientMap_app_π J I (hJIn n) F t, ht n]
    simp only [τ]
    rw [idealPowerQuotientMap_app_comp]
    exact hσ n _ (hle n)
  · intro hc τ hτ
    let σ : ∀ n : ℕ, Γ(Stacks.Algebraization.idealPowerQuotient I (n + 1) F, ⊤) := fun n =>
      (idealPowerQuotientMap J I (hJIn n) F).app ⊤ (τ n)
    have hσ := isCompatible_reindex J I F id (fun _ _ h => h) hJIn τ hτ
    obtain ⟨t, ht, huniq⟩ := hc σ hσ
    refine ⟨t, fun n => ?_, fun t' ht' => huniq t' fun n => by
      rw [← idealPowerQuotientMap_app_π J I (hJIn n) F t', ht']⟩
    rw [← idealPowerQuotientMap_app_π I J (hIJn n) F t, ht (e * (n + 1) - 1)]
    simp only [σ]
    rw [idealPowerQuotientMap_app_comp]
    exact hτ n _ (hle n)

/-- **Infinitesimal section completeness only depends on the ideal up to cofinality.** If
`I ^ e ≤ J ≤ I` with `e ≥ 1` and `F` is quasi-coherent, then the global sections of `F` are the
inverse limit of its sections over the infinitesimal neighbourhoods of `V(J)` exactly when they
are the inverse limit over those of `V(I)`. -/
theorem isInfinitesimalSectionsComplete_subschemeι_iff_of_pow_le {I J : X.IdealSheafData}
    {e : ℕ} (he : 1 ≤ e) (hIJ : I ^ e ≤ J) (hJI : J ≤ I) (F : X.Modules) [F.IsQuasicoherent] :
    Stacks.Algebraization.IsInfinitesimalSectionsComplete J.subschemeι F ↔
      Stacks.Algebraization.IsInfinitesimalSectionsComplete I.subschemeι F := by
  rw [isInfinitesimalSectionsComplete_iff_quotientSections J.subschemeι J J.ker_subschemeι F,
    isInfinitesimalSectionsComplete_iff_quotientSections I.subschemeι I I.ker_subschemeι F]
  exact isIdealPowerQuotientSectionsComplete_iff_of_pow_le he hIJ hJI F

end Stacks.Algebraization.SectionRingCone

end
