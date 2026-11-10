module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalModule

/-!
# `hlocal` for the Stacks 0DZ2 counterexample

Fifteenth layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`. Layer
fourteen built the local lift `L_g = (P')_g ⧸ u·(P')_g` and proved it `A'`-flat. This layer
supplies the comparison equivalence and therefore the whole of `hlocal`, in the shape the
statement writes it:

`(P)_ḡ ⊗_{(P')_g} L_g ≃ₗ[(P)_ḡ] (P)_ḡ ⊗_P M`.

## Both sides are the same quotient of `(P)_ḡ`

The design of layer fourteen pays off here. Both `L_g` and `M` are quotients of their base, so
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot` — which is linear over the *left* factor,
i.e. over `(P)_ḡ`, exactly the linearity the statement demands — turns each side into a quotient
of `(P)_ḡ` by a mapped ideal. The comparison is then an identity of two ideals of `(P)_ḡ`:

* the left ideal is the image of `u = Y·x − t·Z`. In `(P)_ḡ` the image of `t` is zero, because
  `P = P'/t·P'`, so the image of `u` is `Y·x`;
* the right ideal is the image of `ker(P → M) = (x)`, computed here from the fact that `P'` is
  free on `{1, x}` over `A'` — division with remainder against the monic `pPoly` — so that an
  element of `P` killed by `P → M` has its constant coefficient in `(t)`;
* and `Y` is a unit in `(P)_ḡ`, because `ḡ ∈ Y·P`, so `(Y·x) = (x)`.

No `cancelBaseChange` chain appears, and with it goes the universe-metavariable risk that layer
seven flagged for that route: the two `quotIdealMapEquivTensorQuot`s are applied at one universe
each with every type in sight already fixed. The route layer seven proposed — a chain between
`(P)_ḡ ⊗_{(P')_g} L_g` and `(P)_ḡ ⊗_P M` through repeated base change — would have been needed
only if `L_g` were built as a localization; building it as a quotient of `(P')_g` and *proving*
it isomorphic to a localization (layer fourteen) moves the whole comparison into ideal
arithmetic.

## Main results

* `Deformation.Examples.ArtinSchreier.exists_add_mul_root`: every element of `P'` is `a + b·x`
  with `a, b ∈ A'`.
* `Deformation.Examples.ArtinSchreier.ker_algebraMap_PRed_NC`: `ker(P → M) = (x)`.
* `Deformation.Examples.ArtinSchreier.hlocal_nodal`: **`hlocal` of Stacks 0DZ2** for the
  counterexample, for every `g ∈ J' = Y·P'`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow
open scoped TensorProduct

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### `P'` is free on `{1, x}` over `A'` -/

/-- `x² − t·x − t²·Y` has degree two. -/
theorem pPoly_degree : pPoly.degree = 2 := by
  have hle : (-(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY)) :
      Polynomial ABase).degree ≤ 1 := by
    rw [Polynomial.degree_neg]
    exact Polynomial.degree_linear_le
  have hlt : (-(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY)) :
      Polynomial ABase).degree < (X ^ 2 : Polynomial ABase).degree := by
    rw [Polynomial.degree_X_pow]
    exact lt_of_le_of_lt hle (by norm_num)
  have h : pPoly.degree = (X ^ 2 : Polynomial ABase).degree :=
    Polynomial.degree_add_eq_left_of_degree_lt hlt
  rw [h, Polynomial.degree_X_pow]
  simp

/-- **Every element of `P'` is `a + b·x`** with `a, b ∈ A'`: divide with remainder against the
monic `x² − t·x − t²·Y`, whose degree is two, so the remainder is linear. -/
theorem exists_add_mul_root (p : PBase) :
    ∃ a b : ABase,
      p = algebraMap ABase PBase a + algebraMap ABase PBase b * AdjoinRoot.root pPoly := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective p
  have hmk : AdjoinRoot.mk pPoly f = AdjoinRoot.mk pPoly (f %ₘ pPoly) := by
    refine (AdjoinRoot.mk_eq_mk.2 ?_).symm
    refine ⟨-(f /ₘ pPoly), ?_⟩
    have h := Polynomial.modByMonic_add_div f pPoly
    linear_combination h
  have hdeg : (f %ₘ pPoly).degree ≤ 1 := by
    have h := Polynomial.degree_modByMonic_lt f pPoly_monic
    rw [pPoly_degree] at h
    rcases eq_or_ne (f %ₘ pPoly) 0 with h0 | h0
    · rw [h0]
      simp
    · have hnd := Polynomial.degree_eq_natDegree h0
      rw [hnd] at h
      have hn : (f %ₘ pPoly).natDegree < 2 := by exact_mod_cast h
      rw [hnd]
      exact_mod_cast Nat.lt_succ_iff.mp hn
  obtain ⟨a, b, hr⟩ : ∃ a b : ABase, f %ₘ pPoly = C b * X + C a :=
    ⟨(f %ₘ pPoly).coeff 0, (f %ₘ pPoly).coeff 1,
      Polynomial.eq_X_add_C_of_degree_le_one hdeg⟩
  refine ⟨a, b, ?_⟩
  change AdjoinRoot.mk pPoly f = _
  rw [hmk, hr, map_add, map_mul]
  have hX : AdjoinRoot.mk pPoly (X : Polynomial ABase) = AdjoinRoot.root pPoly := rfl
  have hCa : AdjoinRoot.mk pPoly (C a) = algebraMap ABase PBase a := rfl
  have hCb : AdjoinRoot.mk pPoly (C b) = algebraMap ABase PBase b := rfl
  rw [hX, hCa, hCb, add_comm]

/-! ### `ker(P → M) = (x)` -/

/-- The image of the thickening coordinate `x` in `P`. -/
def xRed : PRed := algebraMap PBase PRed (AdjoinRoot.root pPoly)

/-- The map `P' → M` sends the root `x` to zero. -/
theorem pBaseToNC_root : pBaseToNC (AdjoinRoot.root pPoly) = 0 :=
  AdjoinRoot.lift_root _

/-- The map `P → M` sends the image `xRed` of `x` to zero. -/
theorem algebraMap_PRed_NC_xRed : algebraMap PRed NC xRed = 0 := by
  rw [xRed, algebraMap_pRed_NC, pBaseToNC_root]

/-- The image of `t` in `P = P'/t·P'` is zero. -/
private theorem algebraMap_PBase_PRed_tauP : algebraMap PBase PRed tauP = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-- **The kernel of `P → M` is `(x)`.** An element of `P` lifts to `a + b·x` in `P'` by
`exists_add_mul_root`; the map sends it to the reduction of `a`, so the kernel forces `a ∈ (t)`,
and `t` is already zero in `P`. -/
theorem ker_algebraMap_PRed_NC :
    RingHom.ker (algebraMap PRed NC) = Ideal.span {xRed} := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, b, rfl⟩ := exists_add_mul_root p
    rw [RingHom.mem_ker] at hy
    have hval : algebraMap PRed NC
        (Ideal.Quotient.mk (Ideal.span {tauP})
          (algebraMap ABase PBase a + algebraMap ABase PBase b * AdjoinRoot.root pPoly)) =
        redA a := by
      change algebraMap PRed NC (algebraMap PBase PRed _) = _
      rw [algebraMap_pRed_NC, map_add, map_mul, pBaseToNC_root, mul_zero, add_zero,
        pBaseToNC_algebraMap]
    rw [hval] at hy
    rw [← RingHom.mem_ker, ker_redA, Ideal.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    refine Ideal.mem_span_singleton.2 ⟨algebraMap PBase PRed (algebraMap ABase PBase b), ?_⟩
    change algebraMap PBase PRed _ = _
    simp only [map_add, map_mul, xRed]
    rw [show algebraMap PBase PRed (algebraMap ABase PBase (tau NC)) = 0 from
      algebraMap_PBase_PRed_tauP]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact algebraMap_PRed_NC_xRed

/-- **`M = P/(x)`**, as `P`-algebras. This is the presentation of `M` that the comparison of
`hlocal` consumes; layer five's presentation of `M` as `NC` is what makes its flatness and
finiteness free, and the two are reconciled here. -/
def ncAlgEquivQuotXRed : (PRed ⧸ Ideal.span {xRed}) ≃ₐ[PRed] NC :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective
      (Ideal.Quotient.lift (Ideal.span {xRed})
        (algebraMap PRed NC : PRed →+* NC) (by
          intro y hy
          rw [← ker_algebraMap_PRed_NC, RingHom.mem_ker] at hy
          exact hy))
      ⟨RingHom.lift_injective_of_ker_le_ideal _ _ ker_algebraMap_PRed_NC.le,
       by
        intro n
        obtain ⟨z, hz⟩ := surjective_pRedToNC n
        exact ⟨Ideal.Quotient.mk _ z, hz⟩⟩)
    (fun r => rfl)

/-! ### `hlocal` -/

/-- **`hlocal` of Stacks 0DZ2 for the counterexample.** For every `g ∈ J' = Y·P'` the
localization `M_g` has an `A'`-flat `(P')_g`-module lift, namely `L_g = (P')_g ⧸ (Y·x − t·Z)`.

The comparison is an identity of ideals of `(P)_ḡ`: `t` dies there, so the image of `Y·x − t·Z`
is `Y·x`; `Y` is a unit there, because `ḡ ∈ Y·P`; and `(x)` is the kernel of `P → M`. Both sides
of the required equivalence are therefore `(P)_ḡ ⧸ (x)`, identified by
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, which is linear over `(P)_ḡ`. -/
theorem hlocal_nodal {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    letI : Algebra (Localization.Away g) (Localization.Away (algebraMap PBase PRed g)) :=
      (Localization.awayMap (algebraMap PBase PRed) g).toAlgebra
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
      (_ : Module ABase L) (_ : IsScalarTower ABase (Localization.Away g) L),
      Module.Flat ABase L ∧ Nonempty
        ((Localization.Away (algebraMap PBase PRed g) ⊗[Localization.Away g] L)
          ≃ₗ[Localization.Away (algebraMap PBase PRed g)]
            (Localization.Away (algebraMap PBase PRed g) ⊗[PRed] NC)) := by
  let : Algebra (Localization.Away g) (Localization.Away (algebraMap PBase PRed g)) :=
    (Localization.awayMap (algebraMap PBase PRed) g).toAlgebra
  have hfac : ∀ p : PBase,
      algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) p =
        algebraMap PRed (Localization.Away (algebraMap PBase PRed g)) (algebraMap PBase PRed p) :=
    IsScalarTower.algebraMap_apply PBase PRed (Localization.Away (algebraMap PBase PRed g))
  -- the structure map `P' → (P)_ḡ` factors both ways through the square
  have hcomp : ∀ p : PBase,
      algebraMap (PAway g) (Localization.Away (algebraMap PBase PRed g))
          (algebraMap PBase (PAway g) p) =
        algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) p := by
    intro p
    have h1 : Localization.awayMap (algebraMap PBase PRed) g (algebraMap PBase (PAway g) p) =
        algebraMap PRed (Localization.Away (algebraMap PBase PRed g))
          (algebraMap PBase PRed p) :=
      IsLocalization.map_eq _ p
    change Localization.awayMap (algebraMap PBase PRed) g (algebraMap PBase (PAway g) p) = _
    rw [h1, ← hfac]
  have htower :
      IsScalarTower PBase (PAway g) (Localization.Away (algebraMap PBase PRed g)) :=
    IsScalarTower.of_algebraMap_eq fun p => (hcomp p).symm
  -- `t` dies in `(P)_ḡ`
  have htauPg :
      algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) tauP = 0 := by
    rw [hfac, algebraMap_PBase_PRed_tauP, map_zero]
  -- `Y` is a unit in `(P)_ḡ`
  have hunit :
      IsUnit (algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) omegaP) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hg
    have hu : IsUnit (algebraMap PRed (Localization.Away (algebraMap PBase PRed g))
        (algebraMap PBase PRed g)) :=
      IsLocalization.map_units _
        (⟨algebraMap PBase PRed g, Submonoid.mem_powers _⟩ :
          Submonoid.powers (algebraMap PBase PRed g))
    rw [← hfac] at hu
    have hgc : algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) g =
        algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) omegaP *
          algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) c := by
      rw [← map_mul]
      exact congrArg _ hc
    rw [hgc] at hu
    exact isUnit_of_mul_isUnit_left hu
  -- the two ideals agree
  have hid : (localIdeal g).map
        (algebraMap (PAway g) (Localization.Away (algebraMap PBase PRed g))) =
      (Ideal.span {xRed}).map
        (algebraMap PRed (Localization.Away (algebraMap PBase PRed g))) := by
    have hl : (localIdeal g).map
          (algebraMap (PAway g) (Localization.Away (algebraMap PBase PRed g))) =
        Ideal.span {algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) uElt} := by
      rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
      exact congrArg Ideal.span
        (congrArg (fun z => ({z} : Set (Localization.Away (algebraMap PBase PRed g))))
          (hcomp uElt))
    have hu : algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) uElt =
        algebraMap PBase (Localization.Away (algebraMap PBase PRed g)) omegaP *
          algebraMap PBase (Localization.Away (algebraMap PBase PRed g))
            (AdjoinRoot.root pPoly) := by
      rw [uElt, map_sub, map_mul, map_mul, htauPg, zero_mul, sub_zero]
    have hr : (Ideal.span {xRed}).map
          (algebraMap PRed (Localization.Away (algebraMap PBase PRed g))) =
        Ideal.span {(algebraMap PBase (Localization.Away (algebraMap PBase PRed g))
          (AdjoinRoot.root pPoly))} := by
      rw [Ideal.map_span, Set.image_singleton, xRed, ← hfac]
    rw [hl, hu, hr]
    exact Ideal.span_singleton_mul_left_unit hunit _
  refine ⟨LocalModule g, inferInstance, inferInstance, inferInstance, inferInstance,
    flat_LocalModule hg, ⟨?_⟩⟩
  refine AlgEquiv.toLinearEquiv ?_
  refine (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (Localization.Away (algebraMap PBase PRed g)) (localIdeal g)).symm.trans ?_
  refine (Ideal.quotientEquivAlgOfEq
    (Localization.Away (algebraMap PBase PRed g)) hid).trans ?_
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (Localization.Away (algebraMap PBase PRed g)) (Ideal.span {xRed})).trans
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : Localization.Away (algebraMap PBase PRed g) ≃ₐ[_] _)
      ncAlgEquivQuotXRed)

end Deformation.Examples.ArtinSchreier

end
