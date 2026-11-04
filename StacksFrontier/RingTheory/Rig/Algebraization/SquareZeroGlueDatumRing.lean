module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatum
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftRing

/-!
# The ring glued from a glueing datum

For a glueing datum `D` (`Rig.SquareZeroLift.GlueDatum`) this file defines the ring `T`
obtained by glueing `S`, `H` and the lifts `V_{i}` of the localizations `S_{f i}`: the
subalgebra of `S × H × ∏_i V_i` of the tuples `(s, h, v)` with `e(h) = s` in `S^∧`, `v_i = s`
in `S_{f i}`, `ρ_i(v_i) = h` in `H_{f i}` and `σ(v_i) = σ(v_j)` in `V_{i,j}`. For the datum of
étale lifts this is `Rig.SquareZeroLift.glued`.

## Main definitions

* `Rig.SquareZeroLift.GlueDatum.glued`: the subalgebra `T`.
* `Rig.SquareZeroLift.GlueDatum.prS`, `Rig.SquareZeroLift.GlueDatum.prH`,
  `Rig.SquareZeroLift.GlueDatum.prV`: the projections of `T` to `S`, `H` and the `V_i`.
-/

@[expose] public section

namespace Rig.SquareZeroLift.GlueDatum

open TensorProduct Cech FormalGlueing

universe u

variable {R : Type u} [CommRing R] {N : Ideal R}
variable {k : ℕ} {f : Fin k → R}
variable {S : Type u} [CommRing S] [Algebra R S]
variable {H : Type u} [CommRing H] [Algebra R H]
variable {e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S}
variable (D : GlueDatum N f S H e)

/-- The transition maps of the family of lifts, as additive maps. -/
noncomputable def ιV {s t : Finset (Fin k)} (h : s ⊆ t) : XV N f S D.L s →+ XV N f S D.L t :=
  if hs : s.Nonempty then (D.sig h hs).toRingHom.toAddMonoidHom else 0

/-- On a nonempty index set `s`, the map `ιV h` is the transition map `sig h hs`. -/
theorem ιV_apply {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : XV N f S D.L s) :
    D.ιV h v = D.sig h hs v := by
  simp [ιV, hs]

/-- The conditions defining the glued algebra. -/
def GlueCond (x : Amb N f S H D.L) : Prop :=
  e (Ideal.Quotient.mk _ x.2.1) = algebraMap S (Sh f S) x.1 ∧
  (∀ u, (D.L u.1).ψ (x.2.2 u) = algebraMap S (Sl f S u.1) x.1) ∧
  (∀ u, D.rho u.1 (nonempty_of_card_eq u) (x.2.2 u) =
    algebraMap H (Hl f H u.1) x.2.1) ∧
  (∀ (T : {s : Finset (Fin k) // s.card = 2}) (u v : {s : Finset (Fin k) // s.card = 1})
    (hu : u.1 ⊆ T.1) (hv : v.1 ⊆ T.1),
    D.sig hu (nonempty_of_card_eq u) (x.2.2 u) =
      D.sig hv (nonempty_of_card_eq v) (x.2.2 v))

/-- The glued algebra `T`. -/
noncomputable def glued : Subalgebra R (Amb N f S H D.L) where
  carrier := {x | D.GlueCond x}
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

/-- A tuple lies in `glued` if and only if it satisfies the compatibilities with `S^∧` and the
`S_{f i}` and `H_{f i}`, and its family of lifts is a Čech cocycle. -/
theorem mem_glued (x : Amb N f S H D.L) :
    x ∈ D.glued ↔
      e (Ideal.Quotient.mk _ x.2.1) = algebraMap S (Sh f S) x.1 ∧
      (∀ u, (D.L u.1).ψ (x.2.2 u) = algebraMap S (Sl f S u.1) x.1) ∧
      (∀ u, D.rho u.1 (nonempty_of_card_eq u) (x.2.2 u) =
        algebraMap H (Hl f H u.1) x.2.1) ∧
      cechDiff (XV N f S D.L) D.ιV 1 x.2.2 = 0 := by
  rw [cechDiff_one_eq_zero_iff]
  simp only [D.ιV_apply _ (nonempty_of_card_eq _)]
  rfl

/-- The glued ring, as a type. -/
abbrev TT := ↥D.glued

/-- The projection `T → S`. -/
noncomputable def prS : D.TT →ₐ[R] S :=
  (AlgHom.fst R _ _).comp D.glued.val

/-- The projection `T → H`. -/
noncomputable def prH : D.TT →ₐ[R] H :=
  ((AlgHom.fst R _ _).comp (AlgHom.snd R _ _)).comp D.glued.val

/-- The projection `T → V_u`. -/
noncomputable def prV (u : {s : Finset (Fin k) // s.card = 1}) :
    D.TT →ₐ[R] (D.L u.1).carrier :=
  ((Pi.evalAlgHom R (fun u : {s : Finset (Fin k) // s.card = 1} ↦ (D.L u.1).carrier) u).comp
    ((AlgHom.snd R _ _).comp (AlgHom.snd R _ _))).comp D.glued.val

/-- The projection `prS` takes a tuple to its `S`-component. -/
theorem prS_apply (x : D.TT) : D.prS x = x.1.1 := rfl

/-- The projection `prH` takes a tuple to its `H`-component. -/
theorem prH_apply (x : D.TT) : D.prH x = x.1.2.1 := rfl

/-- The projection `prV u` takes a tuple to its `V_u`-component. -/
theorem prV_apply (u : {s : Finset (Fin k) // s.card = 1}) (x : D.TT) :
    D.prV u x = x.1.2.2 u := rfl

/-- For `x` in `T`, the image of `prH x` in `S^∧` under `e` is the image of `prS x`. -/
theorem compat (x : D.TT) :
    e (Ideal.Quotient.mk _ (D.prH x)) = algebraMap S (Sh f S) (D.prS x) :=
  ((D.mem_glued x.1).mp x.2).1

/-- For `x` in `T`, the image of `prV u x` in `S_{f u}` is the image of `prS x`. -/
theorem psi_prV (u : {s : Finset (Fin k) // s.card = 1}) (x : D.TT) :
    (D.L u.1).ψ (D.prV u x) = algebraMap S (Sl f S u.1) (D.prS x) :=
  ((D.mem_glued x.1).mp x.2).2.1 u

/-- For `x` in `T`, the image of `prV u x` under `ρ_u` is the image of `prH x` in `H_{f u}`. -/
theorem rho_prV (u : {s : Finset (Fin k) // s.card = 1}) (x : D.TT) :
    D.rho u.1 (nonempty_of_card_eq u) (D.prV u x) = algebraMap H (Hl f H u.1) (D.prH x) :=
  ((D.mem_glued x.1).mp x.2).2.2.1 u

/-- Two elements of `T` with the same `S`-, `H`- and `V`-components are equal. -/
theorem ext_glued {x y : D.TT} (h1 : x.1.1 = y.1.1) (h2 : x.1.2.1 = y.1.2.1)
    (h3 : x.1.2.2 = y.1.2.2) : x = y :=
  Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))

end Rig.SquareZeroLift.GlueDatum

end
