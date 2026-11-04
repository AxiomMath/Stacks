module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothCorrect

/-!
# The glueing datum of compatible smooth charts

Let `C` be a choice of charts (`Rig.SquareZeroLift.ChartData`) whose chart changes satisfy the
cocycle condition and are compatible with the maps to the `H_s`. This file assembles from it a
glueing datum (`Rig.SquareZeroLift.GlueDatum`): the lift over a nonempty `s` is the chart
`W_{m,s}` at the smallest index `m` of `s`, the transition maps are the restrictions followed by
the chart changes to the new smallest index, and the maps to the `H_s` are the `φ_{m,s}`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct

universe u

variable {R : Type u} [CommRing R] {N : Ideal R} (hN : N ^ 2 = ⊥)
variable {k : ℕ} {f : Fin k → R}
variable {S : Type u} [CommRing S] [Algebra R S]
variable {H : Type u} [CommRing H] [Algebra R H]
variable {e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S}
variable {W : ∀ i : Fin k, NilLift R N (Sl f S {i})}

/-- The identification of the carriers of two equal lifts. -/
noncomputable def NilLift.equivOfEq {s : Finset (Fin k)} {L L' : NilLift R N (Sl f S s)}
    (h : L = L') : L.carrier ≃ₐ[R] L'.carrier := by
  subst h
  exact AlgEquiv.refl

/-- The identification `NilLift.equivOfEq h` commutes with the maps `ψ` to `Sl f S s`. -/
theorem NilLift.psi_equivOfEq {s : Finset (Fin k)} {L L' : NilLift R N (Sl f S s)} (h : L = L')
    (x : L.carrier) : L'.ψ (NilLift.equivOfEq h x) = L.ψ x := by
  subst h
  rfl

namespace ChartData

variable (C : ChartData N f S H e W)
variable [hW : ∀ i, Module.Flat R (W i).carrier]

/-- The identity between two charts at equal indices. -/
noncomputable def eqChart {i j : Fin k} (h : i = j) (t : Finset (Fin k)) (hi : i ∈ t)
    (hj : j ∈ t) : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier := by
  subst h
  exact AlgHom.id R _

omit hW in
/-- The identity between the charts at an index and itself is the identity map. -/
theorem eqChart_rfl (i : Fin k) (t : Finset (Fin k)) (hi : i ∈ t) (v) :
    eqChart (W := W) (rfl : i = i) t hi hi v = v := rfl

/-- The chart change `W_{j,t} → W_{i,t}` for `i ≤ j`. -/
noncomputable def chg (i j : Fin k) (hij : i ≤ j) (t : Finset (Fin k)) (hi : i ∈ t) (hj : j ∈ t) :
    (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier :=
  if h : i = j then eqChart h t hi hj else C.γc i j (lt_of_le_of_ne hij h) t hi hj

omit hW in
/-- The chart change from an index to itself is the identity. -/
theorem chg_self (i : Fin k) (t : Finset (Fin k)) (hi : i ∈ t) (v) :
    C.chg i i le_rfl t hi hi v = v := by
  simp [chg, eqChart_rfl]

omit hW in
/-- For `i < j`, the chart change `chg i j` is the chart change `γc i j`. -/
theorem chg_of_lt {i j : Fin k} (hij : i < j) (t : Finset (Fin k)) (hi : i ∈ t) (hj : j ∈ t) :
    C.chg i j hij.le t hi hj = C.γc i j hij t hi hj := by
  simp [chg, ne_of_lt hij]

/-- A choice of charts is *compatible* if its chart changes satisfy the cocycle condition on
triples and are compatible with the maps to the `H_s` on pairs. -/
def Compatible : Prop :=
  (∀ (a b : Fin k) (hab : a < b),
    (C.φc a {a, b} (mem_pair_left a b)).comp
        (C.γc a b hab {a, b} (mem_pair_left a b) (mem_pair_right a b)) =
      C.φc b {a, b} (mem_pair_right a b)) ∧
  (∀ (a b c : Fin k) (hab : a < b) (hbc : b < c),
    (C.γc a b hab {a, b, c} (by simp) (by simp)).comp
        (C.γc b c hbc {a, b, c} (by simp) (by simp)) =
      C.γc a c (hab.trans hbc) {a, b, c} (by simp) (by simp))

omit hW in
/-- Chart changes commute with the maps `ψ` to `Sl f S t`. -/
theorem psi_chg (i j : Fin k) (hij : i ≤ j) (t : Finset (Fin k)) (hi : i ∈ t) (hj : j ∈ t) (v) :
    (Wc N f S W i t hi).ψ (C.chg i j hij t hi hj v) = (Wc N f S W j t hj).ψ v := by
  rcases hij.eq_or_lt with rfl | hlt
  · rw [chg_self]
  · rw [C.chg_of_lt hlt, psi_γc]

/-- Chart changes commute with the restriction maps `resW`. -/
theorem chg_resW (i j : Fin k) (hij : i ≤ j) {t t' : Finset (Fin k)} (h : t ⊆ t') (hi : i ∈ t)
    (hj : j ∈ t) (v) :
    C.chg i j hij t' (h hi) (h hj) (resW N f S W j h hj v) =
      resW N f S W i h hi (C.chg i j hij t hi hj v) := by
  rcases hij.eq_or_lt with rfl | hlt
  · rw [chg_self, chg_self]
  · rw [C.chg_of_lt hlt, C.chg_of_lt hlt, γc_resW]

/-- For a compatible choice of charts, the chart changes `γc` satisfy the cocycle condition on
every `t`. -/
theorem γc_comp_γc (hC : C.Compatible) {i j l : Fin k} (hij : i < j) (hjl : j < l)
    (t : Finset (Fin k)) (hi : i ∈ t) (hj : j ∈ t) (hl : l ∈ t) (v) :
    C.γc i j hij t hi hj (C.γc j l hjl t hj hl v) = C.γc i l (hij.trans hjl) t hi hl v := by
  have hsub : ({i, j, l} : Finset (Fin k)) ⊆ t :=
    Finset.insert_subset_iff.mpr ⟨hi, pair_subset_of_mem hj hl⟩
  have m1 : i ∈ ({i, j, l} : Finset (Fin k)) := by simp
  have m2 : j ∈ ({i, j, l} : Finset (Fin k)) := by simp
  have m3 : l ∈ ({i, j, l} : Finset (Fin k)) := by simp
  have key :
      (C.γc i j hij t hi hj).comp (C.γc j l hjl t hj hl) = C.γc i l (hij.trans hjl) t hi hl :=
    Wc_algHom_ext N f S W l t hl fun w ↦ by
      rw [AlgHom.comp_apply, ← resW_toWc N f S W l hsub m3,
        C.γc_resW j l hjl hsub m2 m3, C.γc_resW i j hij hsub m1 m2,
        C.γc_resW i l (hij.trans hjl) hsub m1 m3]
      congr 1
      exact AlgHom.congr_fun (hC.2 i j l hij hjl) _
  exact AlgHom.congr_fun key v

/-- For a compatible choice of charts, the chart changes `γc` commute with the maps `φc` to
`Hl f H t`. -/
theorem φc_comp_γc (hC : C.Compatible) {i j : Fin k} (hij : i < j) (t : Finset (Fin k))
    (hi : i ∈ t) (hj : j ∈ t) (v) :
    C.φc i t hi (C.γc i j hij t hi hj v) = C.φc j t hj v := by
  have hsub : ({i, j} : Finset (Fin k)) ⊆ t := pair_subset_of_mem hi hj
  have key : (C.φc i t hi).comp (C.γc i j hij t hi hj) = C.φc j t hj :=
    Wc_algHom_ext N f S W j t hj fun w ↦ by
      rw [AlgHom.comp_apply, ← resW_toWc N f S W j hsub (mem_pair_right i j),
        C.γc_resW i j hij hsub (mem_pair_left i j) (mem_pair_right i j),
        C.φc_resW i hsub (mem_pair_left i j), C.φc_resW j hsub (mem_pair_right i j)]
      congr 1
      exact AlgHom.congr_fun (hC.1 i j hij) _
  exact AlgHom.congr_fun key v

/-- For a compatible choice of charts, the chart changes `chg` satisfy the cocycle condition
`chg i j ∘ chg j l = chg i l` for `i ≤ j ≤ l`. -/
theorem chg_chg (hC : C.Compatible) {i j l : Fin k} (hij : i ≤ j) (hjl : j ≤ l)
    (t : Finset (Fin k)) (hi : i ∈ t) (hj : j ∈ t) (hl : l ∈ t) (v) :
    C.chg i j hij t hi hj (C.chg j l hjl t hj hl v) = C.chg i l (hij.trans hjl) t hi hl v := by
  rcases hij.eq_or_lt with rfl | hij'
  · rw [chg_self]
  rcases hjl.eq_or_lt with rfl | hjl'
  · rw [chg_self]
  rw [C.chg_of_lt hij', C.chg_of_lt hjl', C.chg_of_lt (hij'.trans hjl'),
    C.γc_comp_γc hC hij' hjl']

/-- For a compatible choice of charts, the chart changes `chg` commute with the maps `φc` to
`Hl f H t`. -/
theorem φc_chg (hC : C.Compatible) {i j : Fin k} (hij : i ≤ j) (t : Finset (Fin k)) (hi : i ∈ t)
    (hj : j ∈ t) (v) : C.φc i t hi (C.chg i j hij t hi hj v) = C.φc j t hj v := by
  rcases hij.eq_or_lt with rfl | hlt
  · rw [chg_self]
  · rw [C.chg_of_lt hlt, C.φc_comp_γc hC]

/-! ### The glueing datum -/

section Datum

variable (C : ChartData N f S H e W) (hC : C.Compatible)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
variable [hW : ∀ i, Module.Flat R (W i).carrier]
variable (hNS : N.map (algebraMap R S) = ⊥)

/-- The trivial lift of `Sl f S s` by itself, for `N` mapping to zero in `S`.  It is used only
for the empty set of indices, where `S_∅ = S`. -/
noncomputable def trivLift (s : Finset (Fin k)) : NilLift R N (Sl f S s) where
  carrier := Sl f S s
  ψ := AlgHom.id R _
  surj := Function.surjective_id
  ker := by
    rw [show RingHom.ker (AlgHom.id R (Sl f S s)).toRingHom = ⊥ from
      (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id]
    symm
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    have h1 := Ideal.mem_map_of_mem (algebraMap R S) hx
    rw [hNS, Ideal.mem_bot] at h1
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R S (Sl f S s), h1, map_zero]

variable (W) in
/-- The lift over `s`: the chart at the smallest index of `s` if `s` is nonempty. -/
noncomputable def Ld (s : Finset (Fin k)) : NilLift R N (Sl f S s) :=
  if hs : s.Nonempty then Wc N f S W (s.min' hs) s (s.min'_mem hs) else trivLift hNS s

omit [∀ i, Module.Flat R (W i).carrier] in
/-- Over a nonempty `s`, the lift `Ld W hNS s` is the chart at the smallest index of `s`. -/
theorem Ld_eq (s : Finset (Fin k)) (hs : s.Nonempty) :
    Ld W hNS s = Wc N f S W (s.min' hs) s (s.min'_mem hs) := dif_pos hs

/-- The identification of the lift over a nonempty `s` with the chart at its smallest index. -/
noncomputable def eqv (s : Finset (Fin k)) (hs : s.Nonempty) :
    (Ld W hNS s).carrier ≃ₐ[R] (Wc N f S W (s.min' hs) s (s.min'_mem hs)).carrier :=
  NilLift.equivOfEq (Ld_eq hNS s hs)

omit [∀ i, Module.Flat R (W i).carrier] in
/-- The identification `eqv` commutes with the maps `ψ` to `Sl f S s`. -/
theorem psi_eqv (s : Finset (Fin k)) (hs : s.Nonempty) (x : (Ld W hNS s).carrier) :
    (Wc N f S W (s.min' hs) s (s.min'_mem hs)).ψ (eqv hNS s hs x) = (Ld W hNS s).ψ x :=
  NilLift.psi_equivOfEq _ x

/-- If `s ⊆ t` with `s` nonempty, the smallest element of `t` is at most that of `s`. -/
theorem min'_le_min' {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) :
    t.min' (hs.mono h) ≤ s.min' hs :=
  Finset.min'_le _ _ (h (s.min'_mem hs))

/-- The transition maps of the glueing datum. -/
noncomputable def sigD {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) :
    (Ld W hNS s).carrier →ₐ[R] (Ld W hNS t).carrier :=
  (eqv hNS t (hs.mono h)).symm.toAlgHom.comp
    ((C.chg (t.min' (hs.mono h)) (s.min' hs) (min'_le_min' h hs) t (t.min'_mem _)
      (h (s.min'_mem hs))).comp
      ((resW N f S W (s.min' hs) h (s.min'_mem hs)).comp (eqv hNS s hs).toAlgHom))

/-- The maps to the `H_s` of the glueing datum. -/
noncomputable def rhoD (s : Finset (Fin k)) (hs : s.Nonempty) :
    (Ld W hNS s).carrier →ₐ[R] Hl f H s :=
  (C.φc (s.min' hs) s (s.min'_mem hs)).comp (eqv hNS s hs).toAlgHom

omit [∀ i, Module.Flat R (W i).carrier] in
/-- Under the identifications `eqv`, the transition map `sigD` is the restriction `resW` followed
by the chart change `chg` to the smallest index of `t`. -/
theorem eqv_sigD {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v) :
    eqv hNS t (hs.mono h) (C.sigD hNS h hs v) =
      C.chg (t.min' (hs.mono h)) (s.min' hs) (min'_le_min' h hs) t (t.min'_mem _)
        (h (s.min'_mem hs)) (resW N f S W (s.min' hs) h (s.min'_mem hs) (eqv hNS s hs v)) := by
  simp [sigD]

/-- **The glueing datum of compatible smooth charts.** -/
noncomputable def toGlueDatum : GlueDatum N f S H e where
  L := Ld W hNS
  flat s hs := Module.Flat.of_linearEquiv (eqv hNS s hs).toLinearEquiv
  sig h hs := C.sigD hNS h hs
  psi_sig {s t} h hs v := by
    rw [← psi_eqv hNS t (hs.mono h), eqv_sigD, psi_chg, psi_resW, psi_eqv]
  sig_sig {s t w} h h' hs v := by
    apply (eqv hNS w ((hs.mono h).mono h')).injective
    rw [eqv_sigD, eqv_sigD, eqv_sigD, ← C.chg_resW _ _ _ h', C.chg_chg hC, resW_resW]
  rho s hs := C.rhoD hNS s hs
  mk_rho s hs v := by
    rw [rhoD, AlgHom.comp_apply, mk_φc]
    exact congrArg (chi N f S H e s) (psi_eqv hNS s hs v)
  rho_sig {s t} h hs v := by
    change C.φc _ t _ (eqv hNS t (hs.mono h) (C.sigD hNS h hs v)) =
      locH f H h (C.φc _ s _ (eqv hNS s hs v))
    rw [eqv_sigD, C.φc_chg hC, C.φc_resW]

end Datum

end ChartData

end Rig.SquareZeroLift

end
