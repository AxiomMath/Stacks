module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One monic polynomial per variable is a weakly regular sequence

Let `R` be a commutative ring and let `f₀, …, fₙ₋₁` be monic polynomials in one variable over `R`.
Then

`f₀(T₀), …, fₙ₋₁(Tₙ₋₁)`

is a weakly regular sequence in `R[T₀, …, Tₙ₋₁]`, with no hypothesis on `R`.

This is the regularity input of the proof of [Stacks, Tag 0C0G] for a finite ring map: the
intermediate algebra `C = R[T₀, …, Tₙ₋₁]/(f₀(T₀), …, fₙ₋₁(Tₙ₋₁))` through which such a map
factors is presented by `n` variables modulo `n` equations, and that the equations form a weakly
regular sequence of length `n` is what makes `ω_{C/R} = C` sit in degree `0`.

## Main results

* `MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic` — **the sequence `f₀(T₀), …, fₙ₋₁(Tₙ₋₁)` is
  weakly regular**, for monic `fᵢ`.
* `RingTheory.Sequence.IsWeaklyRegular.map_algebraMap_of_flat` — a weakly regular sequence stays
  weakly regular in a flat algebra.

## Implementation notes

The induction is on the number of variables, splitting off `T₀` with
`MvPolynomial.finSuccEquiv`: in `S[T₀]` with `S = R[T₁, …, Tₙ₋₁]` the first element becomes the
monic polynomial `f₀` with its coefficients pushed into `S`, which is a nonzerodivisor
(`Polynomial.Monic.isRegular`), and the remaining ones become constants.  Modulo the first element
the ring is `S[T₀]/(f₀) = AdjoinRoot f₀`, free over `S` because `f₀` is monic, so the remaining
elements stay weakly regular by flat base change along `S → AdjoinRoot f₀`.  The quotient is
therefore never identified with a polynomial ring in fewer variables — only with a free module
over one.
-/

@[expose] public section

open MvPolynomial Polynomial Pointwise RingTheory.Sequence

/-- **A weakly regular sequence stays weakly regular in a flat algebra.**  Weak regularity is
preserved by flat base change of the module (`isWeaklyRegular_lTensor`), and `T ⊗_S S = T`. -/
@[ega "0 15.1.13" "special case",
  ega "0 15.1.14" "forward implication, M=A",
  ega "IV 19.7.2" "more general", sga "3 VIIB 5.5.2" "partial"]
theorem RingTheory.Sequence.IsWeaklyRegular.map_algebraMap_of_flat {S T : Type*} [CommRing S]
    [CommRing T] [Algebra S T] [Module.Flat S T] {ys : List S} (h : IsWeaklyRegular S ys) :
    IsWeaklyRegular T (ys.map (algebraMap S T)) := by
  refine (isWeaklyRegular_map_algebraMap_iff T T ys).mpr ?_
  exact (LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid S T) ys).mp
    h.isWeaklyRegular_lTensor

/-- Constants stay weakly regular modulo a monic polynomial: the quotient `S[T]/(g)` is a free
`S`-module when `g` is monic, so flat base change along `S → S[T]/(g)` applies. -/
private theorem isWeaklyRegular_map_C_quotSMulTop {S : Type*} [CommRing S] {g : Polynomial S}
    (hg : g.Monic) {ys : List S} (h : IsWeaklyRegular S ys) :
    IsWeaklyRegular (QuotSMulTop g (Polynomial S)) (ys.map Polynomial.C) := by
  have : Module.Free S (Polynomial S ⧸ Ideal.span {g}) := hg.free_adjoinRoot
  have : Module.Flat S (Polynomial S ⧸ Ideal.span {g}) := Module.Flat.of_free
  have hlist : (ys.map Polynomial.C).map
        (algebraMap (Polynomial S) (Polynomial S ⧸ Ideal.span {g}))
      = ys.map (algebraMap S (Polynomial S ⧸ Ideal.span {g})) := by
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun a _ => rfl
  have h4 : IsWeaklyRegular (Polynomial S ⧸ Ideal.span {g}) (ys.map Polynomial.C) :=
    (isWeaklyRegular_map_algebraMap_iff (Polynomial S ⧸ Ideal.span {g})
        (Polynomial S ⧸ Ideal.span {g}) (ys.map Polynomial.C)).mp
      (by rw [hlist]; exact h.map_algebraMap_of_flat)
  have heq : (Ideal.span {g} : Submodule (Polynomial S) (Polynomial S))
      = g • (⊤ : Submodule (Polynomial S) (Polynomial S)) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]; simp
  exact (LinearEquiv.isWeaklyRegular_congr
    (Submodule.quotEquivOfEq _ _ heq) (ys.map Polynomial.C)).mp h4

/-- **One monic polynomial per variable is a weakly regular sequence.**  For monic `f₀, …, fₙ₋₁`
in `R[T]`, the sequence `f₀(T₀), …, fₙ₋₁(Tₙ₋₁)` is weakly regular in `R[T₀, …, Tₙ₋₁]`.  No
hypothesis is placed on the commutative ring `R`.

The induction splits off `T₀` by `MvPolynomial.finSuccEquiv`: the first element becomes `f₀` with
coefficients in `S = R[T₁, …, Tₙ₋₁]`, still monic and hence a nonzerodivisor, and the rest become
constants, which stay weakly regular modulo it because `S[T₀]/(f₀)` is a free `S`-module. -/
@[sga "6 VII 1.2" "partial"]
theorem MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic {R : Type*} [CommRing R] :
    ∀ (n : ℕ) (f : Fin n → Polynomial R), (∀ i, (f i).Monic) →
      IsWeaklyRegular (MvPolynomial (Fin n) R)
        (List.ofFn fun i =>
          Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) R) (f i)) := by
  intro n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have h0 : (MvPolynomial.finSuccEquiv R n)
          (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) (f 0))
        = (f 0).map (algebraMap R (MvPolynomial (Fin n) R)) := by
      rw [← Polynomial.aeval_algHom_apply (MvPolynomial.finSuccEquiv R n),
        MvPolynomial.finSuccEquiv_X_zero, Polynomial.aeval_X_left_eq_map]
    have hs : ∀ i : Fin n, (MvPolynomial.finSuccEquiv R n)
          (Polynomial.aeval (MvPolynomial.X i.succ) (f i.succ))
        = Polynomial.C (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) R)
            (f i.succ)) := fun i => by
      rw [← Polynomial.aeval_algHom_apply (MvPolynomial.finSuccEquiv R n),
        MvPolynomial.finSuccEquiv_X_succ]
      exact Polynomial.aeval_algHom_apply
        (Polynomial.CAlgHom (R := R) (A := MvPolynomial (Fin n) R)) _ _
    have hmap : (List.ofFn fun i : Fin (n + 1) =>
          Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) (f i)).map
            (MvPolynomial.finSuccEquiv R n)
        = ((f 0).map (algebraMap R (MvPolynomial (Fin n) R))) ::
          (List.ofFn fun i : Fin n =>
            Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) R)
              (f i.succ)).map Polynomial.C := by
      rw [List.map_ofFn, List.ofFn_succ, List.map_ofFn]
      simp only [Function.comp_def, h0, hs]
    have hcongr : List.Forall₂ (fun (r : MvPolynomial (Fin (n + 1)) R)
          (s : Polynomial (MvPolynomial (Fin n) R)) =>
        ∀ x, (MvPolynomial.finSuccEquiv R n).toAddEquiv (r • x) =
          s • (MvPolynomial.finSuccEquiv R n).toAddEquiv x)
        (List.ofFn fun i =>
          Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) (f i))
        ((List.ofFn fun i =>
            Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) (f i)).map
          (MvPolynomial.finSuccEquiv R n)) :=
      List.forall₂_map_right_iff.mpr
        (List.forall₂_same.mpr fun r _ x => map_mul (MvPolynomial.finSuccEquiv R n) r x)
    refine (AddEquiv.isWeaklyRegular_congr hcongr).mpr ?_
    rw [hmap]
    exact IsWeaklyRegular.cons (((hf 0).map _).isRegular.left)
      (isWeaklyRegular_map_C_quotSMulTop ((hf 0).map _)
        (ih (fun i => f i.succ) fun i => hf i.succ))
