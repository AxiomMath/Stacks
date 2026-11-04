module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftCompare
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# The glued ring of the square-zero lifting step

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftData`, this file
defines the ring `T` obtained by glueing `S`, `H` and the lifts `V_{i}` of the localizations
`S_{f i}`: the subalgebra of `S × H × ∏_i V_i` of the tuples `(s, h, v)` with `e(h) = s` in
`S^∧`, `v_i = s` in `S_{f i}`, `ρ_i(v_i) = h` in `H_{f i}` and `σ(v_i) = σ(v_j)` in `V_{i,j}`.

## Main definitions

* `Rig.SquareZeroLift.glued`: the subalgebra `T`.
* `Rig.SquareZeroLift.prS`, `Rig.SquareZeroLift.prH`, `Rig.SquareZeroLift.prV`: the
  projections of `T` to `S`, `H` and the `V_i`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct Cech FormalGlueing

universe u

/-- The quotient by an ideal of a ring is the quotient of its completion by the extension of the
ideal. -/
theorem quotientMap_adicCompletion_bijective {A : Type*} [CommRing A] (J : Ideal A)
    (hJ : J.FG) :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap A (AdicCompletion J A)))
      (algebraMap A (AdicCompletion J A)) Ideal.le_comap_map) := by
  have hker := AdicCompletion.ker_evalOneₐ_eq_map J hJ
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← hker, RingHom.mem_ker] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  · intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ J b)
    refine ⟨Ideal.Quotient.mk J a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← hker, RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr ha

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (H : Type u) [CommRing H] [Algebra R H]
variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)
variable (L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s))
variable (hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier)

/-- A finite set of cardinality `p + 1` is nonempty. -/
theorem nonempty_of_card_eq {p : ℕ} (u : {s : Finset (Fin k) // s.card = p + 1}) :
    u.1.Nonempty :=
  Finset.card_pos.mp (by simp [u.2])

/-- The family of the lifts `V_s`. -/
abbrev XV (s : Finset (Fin k)) := (L s).carrier

/-- The transition maps of the family of lifts, as additive maps. -/
noncomputable def ιV {s t : Finset (Fin k)} (h : s ⊆ t) : XV N f S L s →+ XV N f S L t :=
  if hs : s.Nonempty then (sig N hN f S L hL h hs).toRingHom.toAddMonoidHom else 0

/-- For nonempty `s`, the map `ιV` is the transition map `sig` of the lifts. -/
theorem ιV_apply {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : XV N f S L s) :
    ιV N hN f S L hL h v = sig N hN f S L hL h hs v := by
  simp [ιV, hs]

/-- The transition maps of the family of localizations `H_s`, as additive maps. -/
noncomputable def ιH {s t : Finset (Fin k)} (h : s ⊆ t) : Hl f H s →+ Hl f H t :=
  (locH f H h).toRingHom.toAddMonoidHom

/-- The ambient algebra `S × H × ∏_i V_i`. -/
abbrev Amb := S × H × FamTerm (XV N f S L) 1

/-- The conditions defining the glued algebra. -/
def GlueCond (x : Amb N f S H L) : Prop :=
  e (Ideal.Quotient.mk _ x.2.1) = algebraMap S (Sh f S) x.1 ∧
  (∀ u, (L u.1).ψ (x.2.2 u) = algebraMap S (Sl f S u.1) x.1) ∧
  (∀ u, rho N hN f S H e L hL u.1 (nonempty_of_card_eq u) (x.2.2 u) =
    algebraMap H (Hl f H u.1) x.2.1) ∧
  (∀ (T : {s : Finset (Fin k) // s.card = 2}) (u v : {s : Finset (Fin k) // s.card = 1})
    (hu : u.1 ⊆ T.1) (hv : v.1 ⊆ T.1),
    sig N hN f S L hL hu (nonempty_of_card_eq u) (x.2.2 u) =
      sig N hN f S L hL hv (nonempty_of_card_eq v) (x.2.2 v))

/-- The glued algebra `T`. -/
noncomputable def glued : Subalgebra R (Amb N f S H L) where
  carrier := {x | GlueCond N hN f S H e L hL x}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3, a4⟩ := ha
    obtain ⟨b1, b2, b3, b4⟩ := hb
    refine ⟨?_, fun u ↦ ?_, fun u ↦ ?_, fun T u v hu hv ↦ ?_⟩
    · simp only [Prod.fst_mul, Prod.snd_mul, map_mul, a1, b1]
    · simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, a2 u, b2 u]
    · simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, a3 u, b3 u]
    · simp only [Prod.snd_mul, Pi.mul_apply, map_mul, a4 T u v hu hv, b4 T u v hu hv]
  add_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3, a4⟩ := ha
    obtain ⟨b1, b2, b3, b4⟩ := hb
    refine ⟨?_, fun u ↦ ?_, fun u ↦ ?_, fun T u v hu hv ↦ ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, map_add, a1, b1]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, a2 u, b2 u]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, a3 u, b3 u]
    · simp only [Prod.snd_add, Pi.add_apply, map_add, a4 T u v hu hv, b4 T u v hu hv]
  algebraMap_mem' r := by
    refine ⟨?_, fun u ↦ ?_, fun u ↦ ?_, fun T u v hu hv ↦ ?_⟩
    · simp only [Prod.algebraMap_apply, ← Ideal.Quotient.mkₐ_eq_mk R, AlgHom.commutes,
        AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    · simp only [Prod.algebraMap_apply, Pi.algebraMap_apply, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply]
    · simp only [Prod.algebraMap_apply, Pi.algebraMap_apply, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply]
    · simp only [Prod.algebraMap_apply, Pi.algebraMap_apply, AlgHom.commutes]

/-- An element of `S × H × ∏_i V_i` lies in `T` if and only if `e(h) = s` in `S^∧`, `v_i = s` in
`S_{f i}`, `ρ_i(v_i) = h` in `H_{f i}`, and the Čech differential of `v` vanishes. -/
theorem mem_glued (x : Amb N f S H L) :
    x ∈ glued N hN f S H e L hL ↔
      e (Ideal.Quotient.mk _ x.2.1) = algebraMap S (Sh f S) x.1 ∧
      (∀ u, (L u.1).ψ (x.2.2 u) = algebraMap S (Sl f S u.1) x.1) ∧
      (∀ u, rho N hN f S H e L hL u.1 (nonempty_of_card_eq u) (x.2.2 u) =
        algebraMap H (Hl f H u.1) x.2.1) ∧
      cechDiff (XV N f S L) (ιV N hN f S L hL) 1 x.2.2 = 0 := by
  rw [cechDiff_one_eq_zero_iff]
  simp only [ιV_apply N hN f S L hL _ (nonempty_of_card_eq _)]
  rfl

/-- The glued ring, as a type. -/
abbrev TT := ↥(glued N hN f S H e L hL)

/-- The projection `T → S`. -/
noncomputable def prS : TT N hN f S H e L hL →ₐ[R] S :=
  (AlgHom.fst R _ _).comp (glued N hN f S H e L hL).val

/-- The projection `T → H`. -/
noncomputable def prH : TT N hN f S H e L hL →ₐ[R] H :=
  ((AlgHom.fst R _ _).comp (AlgHom.snd R _ _)).comp (glued N hN f S H e L hL).val

/-- The projection `T → V_u`. -/
noncomputable def prV (u : {s : Finset (Fin k) // s.card = 1}) :
    TT N hN f S H e L hL →ₐ[R] (L u.1).carrier :=
  ((Pi.evalAlgHom R (fun u : {s : Finset (Fin k) // s.card = 1} ↦ (L u.1).carrier) u).comp
    ((AlgHom.snd R _ _).comp (AlgHom.snd R _ _))).comp (glued N hN f S H e L hL).val

/-- The projection `prS` sends `(s, h, v) ∈ T` to `s`. -/
theorem prS_apply (x : TT N hN f S H e L hL) : prS N hN f S H e L hL x = x.1.1 := rfl

/-- The projection `prH` sends `(s, h, v) ∈ T` to `h`. -/
theorem prH_apply (x : TT N hN f S H e L hL) : prH N hN f S H e L hL x = x.1.2.1 := rfl

/-- The projection `prV u` sends `(s, h, v) ∈ T` to `v_u`. -/
theorem prV_apply (u : {s : Finset (Fin k) // s.card = 1}) (x : TT N hN f S H e L hL) :
    prV N hN f S H e L hL u x = x.1.2.2 u := rfl

/-- For every `x` in `T`, the class of `prH x` modulo `N H`, mapped by `e` to `S^∧`, is the image
of `prS x`. -/
theorem compat (x : TT N hN f S H e L hL) :
    e (Ideal.Quotient.mk _ (prH N hN f S H e L hL x)) =
      algebraMap S (Sh f S) (prS N hN f S H e L hL x) :=
  ((mem_glued N hN f S H e L hL x.1).mp x.2).1

/-- Two elements of `T` with equal components in `S`, `H` and `∏_i V_i` are equal. -/
theorem ext_glued {x y : TT N hN f S H e L hL} (h1 : x.1.1 = y.1.1) (h2 : x.1.2.1 = y.1.2.1)
    (h3 : x.1.2.2 = y.1.2.2) : x = y :=
  Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))

end Rig.SquareZeroLift

end
