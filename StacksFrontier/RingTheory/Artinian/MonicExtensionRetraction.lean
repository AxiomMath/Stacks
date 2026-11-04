module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# A retraction onto a square-zero extension through a monic extension

Let `f : B → A` be a surjection of commutative rings whose kernel has square zero, and let
`G ∈ B[X]` be monic of positive degree. Put `B' = B[X] / (G)` and `A' = A[X] / (f G)`, so that `f`
induces a surjection `f' : B' → A'`, and let `D = B' ×_{A'} A` be the fibre product. The ring `B`
maps to `D` by `b ↦ (b, f b)`. This file shows that this map has a retraction `ρ : D → B` of rings
over `A`: the constant coefficient of the reduced representative of the first component.

## Main definitions

* `Stacks.MonicExtension.extMap`: the induced map `f' : B[X] / (G) → A[X] / (f G)`.
* `Stacks.MonicExtension.constCoeff`: the constant coefficient `B[X] / (G) → B` of the reduced
  representative, a `B`-linear retraction of `B → B[X] / (G)`.
* `Stacks.MonicExtension.toPullback`: the map `B → B' ×_{A'} A`.
* `Stacks.MonicExtension.retraction`: the ring retraction `ρ : B' ×_{A'} A → B`.

## Main results

* `Stacks.MonicExtension.extMap_surjective`: `f'` is surjective.
* `Stacks.MonicExtension.ker_extMap_sq`: the kernel of `f'` has square zero.
* `Stacks.MonicExtension.retraction_comp_toPullback` and `Stacks.MonicExtension.comp_retraction`:
  `ρ` is a retraction of `B → B' ×_{A'} A`, and it is compatible with the projections to `A`.

## Implementation notes

This is the algebraic input of a descent argument for lifting problems along square-zero
extensions of Artinian local rings: a lifting problem solved after the base change `B → B'` is
glued, by the Rim–Schlessinger condition, into one over `D`, and then pulled back along `ρ`.
Multiplicativity of `ρ` only uses that two elements of the kernel of `f'` multiply to zero.
-/

@[expose] public section

open Polynomial

namespace Stacks.MonicExtension

variable {B A : Type*} [CommRing B] [CommRing A] (f : B →+* A) {G : B[X]} (hG : G.Monic)

/-- The map `B[X] / (G) → A[X] / (f G)` induced by `f`. -/
noncomputable abbrev extMap : AdjoinRoot G →+* AdjoinRoot (G.map f) :=
  AdjoinRoot.map f G (G.map f) dvd_rfl

/-- `f'` sends the class of `p` to the class of `f p`. -/
theorem extMap_mk (p : B[X]) :
    extMap f (AdjoinRoot.mk G p) = AdjoinRoot.mk (G.map f) (p.map f) := by
  rw [extMap, AdjoinRoot.map, AdjoinRoot.lift_mk, ← eval₂_map, ← AdjoinRoot.aeval_eq,
    aeval_def]
  rfl

/-- `f'` sends the image of `b ∈ B` to the image of `f b ∈ A`. -/
theorem extMap_of (b : B) :
    extMap f (AdjoinRoot.of G b) = AdjoinRoot.of (G.map f) (f b) := by
  simp

/-- The constant coefficient of the reduced representative, a `B`-linear map
`B[X] / (G) → B`. -/
noncomputable def constCoeff : AdjoinRoot G →ₗ[B] B :=
  (Polynomial.lcoeff B 0).comp (AdjoinRoot.modByMonicHom hG)

/-- `constCoeff` is the constant coefficient of the reduced representative. -/
theorem constCoeff_apply (x : AdjoinRoot G) :
    constCoeff hG x = (AdjoinRoot.modByMonicHom hG x).coeff 0 := rfl

/-- If `G` has positive degree, `constCoeff` is a retraction of `B → B[X] / (G)`. -/
theorem constCoeff_of (hdeg : 0 < G.natDegree) (b : B) :
    constCoeff hG (AdjoinRoot.of G b) = b := by
  nontriviality B
  rw [constCoeff_apply, ← AdjoinRoot.mk_C, AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff hG).2]
  · simp
  · exact lt_of_le_of_lt degree_C_le (natDegree_pos_iff_degree_pos.1 hdeg)

/-- `constCoeff` is `B`-linear: `constCoeff (b * x) = b * constCoeff x`. -/
theorem constCoeff_of_mul (b : B) (x : AdjoinRoot G) :
    constCoeff hG (AdjoinRoot.of G b * x) = b * constCoeff hG x := by
  have : AdjoinRoot.of G b * x = b • x := by rw [Algebra.smul_def]; rfl
  rw [this, LinearMap.map_smul, smul_eq_mul]

/-- The reduced representative of `f' x` is the image under `f` of the reduced representative
of `x`. -/
theorem modByMonicHom_extMap (x : AdjoinRoot G) :
    AdjoinRoot.modByMonicHom (hG.map f) (extMap f x) =
      (AdjoinRoot.modByMonicHom hG x).map f := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [extMap_mk, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
      map_modByMonic f hG]

/-- The constant coefficient of `f' x` is `f` applied to the constant coefficient of `x`. -/
theorem constCoeff_extMap (x : AdjoinRoot G) :
    constCoeff (hG.map f) (extMap f x) = f (constCoeff hG x) := by
  rw [constCoeff_apply, constCoeff_apply, modByMonicHom_extMap, coeff_map]

/-- If `G` has positive degree, the constant coefficient of the image of `a ∈ A` in
`A[X] / (f G)` is `a`. -/
theorem constCoeff_algebraMap_map (hdeg : 0 < G.natDegree) (a : A) :
    constCoeff (hG.map f) (algebraMap A (AdjoinRoot (G.map f)) a) = a := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  have hdeg' : 0 < (G.map f).natDegree := by
    rw [hG.natDegree_map]
    exact hdeg
  exact constCoeff_of (hG.map f) hdeg' a

/-- If `f` is surjective, then so is `f'`. -/
theorem extMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (extMap f (G := G)) := by
  intro y
  induction y using AdjoinRoot.induction_on with
  | ih q =>
    obtain ⟨p, rfl⟩ := Polynomial.map_surjective f hf q
    exact ⟨AdjoinRoot.mk G p, extMap_mk f p⟩

/-- The coefficients of the reduced representative of an element of the kernel of `f'` lie in
the kernel of `f`. -/
theorem coeff_mem_ker_of_extMap_eq_zero (hG : G.Monic) {x : AdjoinRoot G} (hx : extMap f x = 0)
    (n : ℕ) :
    (AdjoinRoot.modByMonicHom hG x).coeff n ∈ RingHom.ker f := by
  have h := modByMonicHom_extMap f hG x
  rw [hx, map_zero] at h
  have := congrArg (fun q => q.coeff n) h
  simpa [coeff_map, RingHom.mem_ker] using this.symm

/-- The kernel of `f'` has square zero as soon as the kernel of `f` does. -/
theorem mul_eq_zero_of_extMap_eq_zero (hG : G.Monic) (hker : RingHom.ker f ^ 2 = ⊥)
    {x y : AdjoinRoot G} (hx : extMap f x = 0) (hy : extMap f y = 0) : x * y = 0 := by
  have hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a * b = 0 := fun a ha b hb => by
    have : a * b ∈ RingHom.ker f ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha hb
    rw [hker] at this
    exact Ideal.mem_bot.1 this
  set p := AdjoinRoot.modByMonicHom hG x
  set q := AdjoinRoot.modByMonicHom hG y
  have hxp : x = AdjoinRoot.mk G p := (AdjoinRoot.mk_leftInverse hG x).symm
  have hyq : y = AdjoinRoot.mk G q := (AdjoinRoot.mk_leftInverse hG y).symm
  have hpq : p * q = 0 := by
    ext n
    rw [coeff_mul, coeff_zero]
    exact Finset.sum_eq_zero fun ij _ =>
      hsq _ (coeff_mem_ker_of_extMap_eq_zero f hG hx _) _
        (coeff_mem_ker_of_extMap_eq_zero f hG hy _)
  rw [hxp, hyq, ← map_mul, hpq, map_zero]

/-- If the kernel of `f` has square zero, then so does the kernel of `f'`. -/
theorem ker_extMap_sq (hG : G.Monic) (hker : RingHom.ker f ^ 2 = ⊥) :
    RingHom.ker (extMap f (G := G)) ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  exact (Ideal.mem_bot).2 (mul_eq_zero_of_extMap_eq_zero f hG hker hx hy)

/-- The fibre product `B' ×_{A'} A`. -/
noncomputable abbrev Pullback : Subring (AdjoinRoot G × A) :=
  (extMap f (G := G)).pullback (algebraMap A (AdjoinRoot (G.map f)))

/-- The map `B → B' ×_{A'} A`, `b ↦ (b, f b)`. -/
noncomputable def toPullback : B →+* ↥(Pullback f (G := G)) :=
  RingHom.codRestrict ((algebraMap B (AdjoinRoot G)).prod f) (Pullback f (G := G)) fun b => by
    change extMap f (AdjoinRoot.of G b) = AdjoinRoot.of (G.map f) (f b)
    exact extMap_of f b

/-- The first component of `toPullback f b` is the image of `b` in `B[X] / (G)`. -/
@[simp]
theorem toPullback_fst (b : B) : (toPullback f (G := G) b).1.1 =
    AdjoinRoot.of G b := rfl

/-- The second component of `toPullback f b` is `f b`. -/
@[simp]
theorem toPullback_snd (b : B) : (toPullback f (G := G) b).1.2 =
    f b := rfl

/-- The constant coefficient of the first component of an element of the fibre product maps to
its second component. -/
theorem f_constCoeff_fst (hdeg : 0 < G.natDegree) (d : ↥(Pullback f (G := G))) :
    f (constCoeff hG d.1.1) = d.1.2 := by
  have hd : extMap f d.1.1 = algebraMap A _ d.1.2 := d.2
  rw [← constCoeff_extMap f hG, hd]
  exact constCoeff_algebraMap_map f hG hdeg _

/-- **The retraction** `ρ : B' ×_{A'} A → B`: the constant coefficient of the reduced
representative of the first component. -/
noncomputable def retraction (hdeg : 0 < G.natDegree) (hker : RingHom.ker f ^ 2 = ⊥) :
    ↥(Pullback f (G := G)) →+* B where
  toFun d := constCoeff hG d.1.1
  map_one' := by
    change constCoeff hG 1 = 1
    rw [← map_one (AdjoinRoot.of G), constCoeff_of hG hdeg]
  map_zero' := by
    change constCoeff hG 0 = 0
    exact map_zero _
  map_add' d e := by
    change constCoeff hG (d.1.1 + e.1.1) = _
    exact map_add _ _ _
  map_mul' d e := by
    change constCoeff hG (d.1.1 * e.1.1) =
      constCoeff hG d.1.1 * constCoeff hG e.1.1
    set x := d.1.1
    set y := e.1.1
    set a := constCoeff hG x
    set b := constCoeff hG y
    have hjx : extMap f (x - AdjoinRoot.of G a) = 0 := by
      have hd : extMap f d.1.1 = algebraMap A _ d.1.2 := d.2
      rw [map_sub, extMap_of, hd, f_constCoeff_fst f hG hdeg d]; exact sub_self _
    have hjy : extMap f (y - AdjoinRoot.of G b) = 0 := by
      have he : extMap f e.1.1 = algebraMap A _ e.1.2 := e.2
      rw [map_sub, extMap_of, he, f_constCoeff_fst f hG hdeg e]; exact sub_self _
    have hcx : constCoeff hG (x - AdjoinRoot.of G a) = 0 := by
      rw [map_sub, constCoeff_of hG hdeg, sub_self]
    have hcy : constCoeff hG (y - AdjoinRoot.of G b) = 0 := by
      rw [map_sub, constCoeff_of hG hdeg, sub_self]
    have h0 := mul_eq_zero_of_extMap_eq_zero f hG hker hjx hjy
    have hxy : x * y = AdjoinRoot.of G (a * b) + AdjoinRoot.of G a * (y - AdjoinRoot.of G b) +
        AdjoinRoot.of G b * (x - AdjoinRoot.of G a) +
        (x - AdjoinRoot.of G a) * (y - AdjoinRoot.of G b) := by
      rw [map_mul]; ring
    rw [hxy, h0, add_zero, map_add, map_add, constCoeff_of_mul, constCoeff_of_mul, hcx, hcy,
      constCoeff_of hG hdeg]
    ring

/-- `ρ d` is the constant coefficient of the reduced representative of the first component
of `d`. -/
theorem retraction_apply (hdeg : 0 < G.natDegree) (hker : RingHom.ker f ^ 2 = ⊥)
    (d : ↥(Pullback f (G := G))) :
    retraction f hG hdeg hker d = constCoeff hG d.1.1 := rfl

/-- `ρ` is a retraction of `B → B' ×_{A'} A`. -/
theorem retraction_comp_toPullback (hdeg : 0 < G.natDegree) (hker : RingHom.ker f ^ 2 = ⊥) :
    (retraction f hG hdeg hker).comp (toPullback f) = RingHom.id B := by
  ext b
  exact constCoeff_of hG hdeg b

/-- `ρ` is compatible with the projections to `A`. -/
theorem comp_retraction (hdeg : 0 < G.natDegree) (hker : RingHom.ker f ^ 2 = ⊥) :
    f.comp (retraction f hG hdeg hker) =
      (extMap f (G := G)).pullbackSnd (algebraMap A (AdjoinRoot (G.map f))) := by
  ext d
  exact f_constCoeff_fst f hG hdeg d

/-- The first projection of `B → B' ×_{A'} A` is the structure map of `B'`. -/
theorem pullbackFst_comp_toPullback :
    ((extMap f (G := G)).pullbackFst (algebraMap A (AdjoinRoot (G.map f)))).comp
      (toPullback f) = algebraMap B (AdjoinRoot G) := rfl

/-- The second projection of `B → B' ×_{A'} A` is `f`. -/
theorem pullbackSnd_comp_toPullback :
    ((extMap f (G := G)).pullbackSnd (algebraMap A (AdjoinRoot (G.map f)))).comp
      (toPullback f) = f := rfl

end Stacks.MonicExtension
