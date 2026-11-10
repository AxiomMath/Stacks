module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.DividedPowers.Criteria
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.DividedPowers.Extend.Completion

/-!
# The completed divided power ring as an inverse limit

If `p` is nilpotent modulo a divided power ideal `I`, each divided power operation is
continuous for the `p`-adic filtration and therefore passes to the completion of `I`, and the
resulting divided power ring is the inverse limit of the divided power rings `A / pᵉ` for `e`
large.

## Main definitions

* `DividedPowers.quotientDividedPowers` — the divided powers induced on `A / pᵉ`.
* `DividedPowers.completedDividedPowers` — the divided powers on the completed ideal.
* `DividedPowers.IsDividedPowerCompletionLimit` — the inverse-limit universal property of the
  completed divided power ring in the category of divided power rings.

## Main results

* `DividedPowers.eventually_isDividedPowerCompletionLimit` — the completed divided power ring is
  the inverse limit of its finite-level quotients.

## Implementation notes

The inverse-limit assertion is expanded into the universal property for compatible divided
power morphisms out of an arbitrary divided power ring.

## References

* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public section

namespace DividedPowers

section Completion

open scoped nonZeroDivisors

universe u v

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : _root_.DividedPowers I) (p : ℕ)

private theorem pAdic_smul_ideal_exists_mul {e : ℕ} {z : A}
    (hz : z ∈ pAdicIdeal (A := A) p ^ e • (I : Submodule A A)) :
    ∃ y ∈ I, z = (p : A) ^ e * y := by
  rw [pAdicIdeal, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hz
  obtain ⟨y, hy, hEq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
  exact ⟨y, hy, by simpa [smul_eq_mul] using hEq.symm⟩

public def dividedPowerSequence (n : ℕ)
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) A := by
  classical
  refine ⟨fun k => γ.dpow n (c k), ?_⟩
  intro m k hmk
  by_cases hn : n = 0
  · subst n
    simp [γ.dpow_zero (c m).property, γ.dpow_zero (c k).property]
  · rw [SModEq.sub_mem]
    have hrel : c m - c k ∈
        pAdicIdeal (A := A) p ^ m • (⊤ : Submodule A I) := by
      rw [← SModEq.sub_mem]
      exact c.property hmk
    have hmem : ((c m : I) : A) - c k ∈
        pAdicIdeal (A := A) p ^ m • (I : Submodule A A) :=
      (mem_ideal_smul_iff_subtype_mem_smul
        (I := I) (J := pAdicIdeal (A := A) p ^ m)
        (I.sub_mem (c m).property (c k).property)).mpr hrel
    have hcont := dpow_congr_pAdic I γ p n m (c k).property (c m).property hmem
    have hle : pAdicIdeal (A := A) p ^ m • (I : Submodule A A) ≤
        pAdicIdeal (A := A) p ^ m • (⊤ : Submodule A A) := smul_mono_right _ le_top
    exact hle hcont

public theorem dividedPowerSequence_mk_eq (n : ℕ)
    {c d : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I}
    (h : AdicCompletion.mk (pAdicIdeal (A := A) p) I c =
      AdicCompletion.mk (pAdicIdeal (A := A) p) I d) :
    AdicCompletion.mk (pAdicIdeal (A := A) p) A
        (dividedPowerSequence I γ p n c) =
      AdicCompletion.mk (pAdicIdeal (A := A) p) A
        (dividedPowerSequence I γ p n d) := by
  apply AdicCompletion.ext
  intro e
  have hcoord :
      Submodule.Quotient.mk (p := (pAdicIdeal (A := A) p ^ e • ⊤ :
        Submodule A I)) (c e) =
      Submodule.Quotient.mk (p := (pAdicIdeal (A := A) p ^ e • ⊤ :
        Submodule A I)) (d e) := by
    have heq := congrArg (fun z : AdicCompletion (pAdicIdeal (A := A) p) I => z.val e) h
    simpa [AdicCompletion.mk_apply_coe] using heq
  have hmem : ((c e : I) : A) - d e ∈
      pAdicIdeal (A := A) p ^ e • (I : Submodule A A) := by
    have hquot := (Submodule.Quotient.eq
      (p := pAdicIdeal (A := A) p ^ e • (⊤ : Submodule A I))).mp hcoord
    exact (mem_ideal_smul_iff_subtype_mem_smul
      (I := I) (J := pAdicIdeal (A := A) p ^ e)
      (I.sub_mem (c e).property (d e).property)).mpr hquot
  have hcont := dpow_congr_pAdic I γ p n e (d e).property (c e).property hmem
  have hcontA : γ.dpow n (c e) - γ.dpow n (d e) ∈
      pAdicIdeal (A := A) p ^ e • (⊤ : Submodule A A) := by
    have hle : pAdicIdeal (A := A) p ^ e • (I : Submodule A A) ≤
        pAdicIdeal (A := A) p ^ e • (⊤ : Submodule A A) := smul_mono_right _ le_top
    exact hle hcont
  calc
    (AdicCompletion.mk (pAdicIdeal (A := A) p) A
        (dividedPowerSequence I γ p n c)).val e =
      Submodule.Quotient.mk (p := (pAdicIdeal (A := A) p ^ e • ⊤ :
        Submodule A A)) (γ.dpow n (c e)) := AdicCompletion.mk_apply_coe _ _ _ _
    _ = Submodule.Quotient.mk (p := (pAdicIdeal (A := A) p ^ e • ⊤ :
        Submodule A A)) (γ.dpow n (d e)) :=
      (Submodule.Quotient.eq
        (p := pAdicIdeal (A := A) p ^ e • (⊤ : Submodule A A))).mpr hcontA
    _ = (AdicCompletion.mk (pAdicIdeal (A := A) p) A
        (dividedPowerSequence I γ p n d)).val e := by
          rw [AdicCompletion.mk_apply_coe]
          rfl

public def dividedPowerSequenceInIdeal (n : ℕ) (hn : n ≠ 0)
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I := by
  classical
  refine ⟨fun k => ⟨γ.dpow n (c k), γ.dpow_mem hn (c k).property⟩, ?_⟩
  intro m k hmk
  rw [SModEq.sub_mem]
  have hrel : c m - c k ∈
      pAdicIdeal (A := A) p ^ m • (⊤ : Submodule A I) := by
    rw [← SModEq.sub_mem]
    exact c.property hmk
  have hmem : ((c m : I) : A) - c k ∈
      pAdicIdeal (A := A) p ^ m • (I : Submodule A A) :=
    (mem_ideal_smul_iff_subtype_mem_smul
      (I := I) (J := pAdicIdeal (A := A) p ^ m)
      (I.sub_mem (c m).property (c k).property)).mpr hrel
  have hcont := dpow_congr_pAdic I γ p n m (c k).property (c m).property hmem
  exact (mem_ideal_smul_iff_subtype_mem_smul
    (I := I) (J := pAdicIdeal (A := A) p ^ m)
    (I.sub_mem (γ.dpow_mem hn (c m).property) (γ.dpow_mem hn (c k).property))).mp hcont

public theorem map_dividedPowerSequenceInIdeal (n : ℕ) (hn : n ≠ 0)
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
      (AdicCompletion.mk (pAdicIdeal (A := A) p) I
        (dividedPowerSequenceInIdeal I γ p n hn c)) =
      AdicCompletion.mk (pAdicIdeal (A := A) p) A
        (dividedPowerSequence I γ p n c) := by
  apply AdicCompletion.ext
  intro e
  rw [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe,
    AdicCompletion.mk_apply_coe]
  rfl

public noncomputable def completionIdealRepSequence
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (x : completionIdeal I p hp) :
    AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I :=
  Classical.choose <| AdicCompletion.mk_surjective (pAdicIdeal (A := A) p) I
    ((completionIdealEquiv I p hp).1.symm x)

public theorem completionIdealRepSequence_spec
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (x : completionIdeal I p hp) :
    AdicCompletion.mk (pAdicIdeal (A := A) p) I
      (completionIdealRepSequence I p hp x) =
        ((completionIdealEquiv I p hp).1.symm x) :=
  Classical.choose_spec <| AdicCompletion.mk_surjective (pAdicIdeal (A := A) p) I
    ((completionIdealEquiv I p hp).1.symm x)

public theorem completionIdealRepSequence_map_eq
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (x : completionIdeal I p hp) :
    AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
      (AdicCompletion.mk (pAdicIdeal (A := A) p) I
        (completionIdealRepSequence I p hp x)) = x := by
  have hE := congrArg Subtype.val
    ((completionIdealEquiv I p hp).1.apply_symm_apply x)
  rw [← completionIdealRepSequence_spec I p hp x] at hE
  exact ((completionIdealEquiv I p hp).2
    (AdicCompletion.mk (pAdicIdeal (A := A) p) I
      (completionIdealRepSequence I p hp x))).symm.trans hE

public noncomputable def completedDpowAux
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) (n : ℕ)
    (x : AdicCompletion (pAdicIdeal (A := A) p) A) :
    AdicCompletion (pAdicIdeal (A := A) p) A := by
  classical
  by_cases hx : x ∈ completionIdeal I p hp
  · by_cases hn : n = 0
    · exact 1
    · let z : completionIdeal I p hp := ⟨x, hx⟩
      let w : completionIdeal I p hp := (completionIdealEquiv I p hp).1
        (AdicCompletion.mk (pAdicIdeal (A := A) p) I
          (dividedPowerSequenceInIdeal I γ p n hn
            (completionIdealRepSequence I p hp z)))
      exact w.val
  · exact 0

public theorem dividedPowerSequenceInIdeal_one
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    dividedPowerSequenceInIdeal I γ p 1 (by norm_num) c = c := by
  apply AdicCompletion.AdicCauchySequence.ext
  intro k
  apply Subtype.ext
  simp [dividedPowerSequenceInIdeal, γ.dpow_one (c k).property]

public theorem dividedPowerSequenceInIdeal_constant (n : ℕ) (hn : n ≠ 0)
    (x : I) :
    AdicCompletion.mk (pAdicIdeal (A := A) p) I
      (dividedPowerSequenceInIdeal I γ p n hn
        ⟨fun _ => x, by intro m k _; exact SModEq.refl _⟩) =
      AdicCompletion.of (pAdicIdeal (A := A) p) I
        ⟨γ.dpow n x, γ.dpow_mem hn x.property⟩ := by
  apply AdicCompletion.ext
  intro e
  rfl

public theorem completedDpowAux_mem
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) {n : ℕ}
    (hn : n ≠ 0) {x : AdicCompletion (pAdicIdeal (A := A) p) A}
    (hx : x ∈ completionIdeal I p hp) :
    completedDpowAux I γ p hp n x ∈ completionIdeal I p hp := by
  classical
  simp [completedDpowAux, hx, hn]

/-- The zeroth completed divided power of an element of the completed ideal is `1`. -/
private theorem completedDpowAux_zero_of_mem
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    {x : AdicCompletion (pAdicIdeal (A := A) p) A}
    (hx : x ∈ completionIdeal I p hp) :
    completedDpowAux I γ p hp 0 x = 1 := by
  classical
  simp [completedDpowAux, hx]

public theorem completedDpowAux_one
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    {x : AdicCompletion (pAdicIdeal (A := A) p) A}
    (hx : x ∈ completionIdeal I p hp) :
    completedDpowAux I γ p hp 1 x = x := by
  classical
  let z : completionIdeal I p hp := ⟨x, hx⟩
  let c := completionIdealRepSequence I p hp z
  have hc := completionIdealRepSequence_spec I p hp z
  have hseq := dividedPowerSequenceInIdeal_one I γ p c
  have hE : (completionIdealEquiv I p hp).1
      (AdicCompletion.mk (pAdicIdeal (A := A) p) I
        (dividedPowerSequenceInIdeal I γ p 1 (by norm_num) c)) = z := by
    rw [hseq, hc]
    exact (completionIdealEquiv I p hp).1.apply_symm_apply z
  have hv := congrArg Subtype.val hE
  simp [completedDpowAux, hx, z, c, one_ne_zero, hseq, hc]

public theorem completedDpowAux_of
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (n : ℕ) (x : A) (hx : x ∈ I) :
    completedDpowAux I γ p hp n
      (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x) =
      algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) (γ.dpow n x) := by
  classical
  let P := pAdicIdeal (A := A) p
  let xi : I := ⟨x, hx⟩
  have hmap : AdicCompletion.map P I.subtype (AdicCompletion.of P I xi) =
      algebraMap A (AdicCompletion P A) x := by
    rw [AdicCompletion.algebraMap_apply]
    simpa [xi] using AdicCompletion.map_of P I.subtype xi
  have hmem : algebraMap A (AdicCompletion P A) x ∈ completionIdeal I p hp := by
    rw [← hmap]
    exact completion_map_subtype_mem I p hp _
  let z : completionIdeal I p hp := ⟨_, hmem⟩
  let c := completionIdealRepSequence I p hp z
  have hc : AdicCompletion.mk P I c = AdicCompletion.of P I xi := by
    apply completion_map_subtype_injective I p hp
    exact (completionIdealRepSequence_map_eq I p hp z).trans hmap.symm
  by_cases hn : n = 0
  · subst n
    rw [completedDpowAux_zero_of_mem I γ p hp hmem, γ.dpow_zero hx, map_one]
  · have hconst :
        AdicCompletion.mk P I (dividedPowerSequenceInIdeal I γ p n hn c) =
          AdicCompletion.of P I ⟨γ.dpow n x, γ.dpow_mem hn hx⟩ := by
      let d : AdicCompletion.AdicCauchySequence P I :=
        ⟨fun _ => xi, by intro m k _; exact SModEq.refl _⟩
      have h := dividedPowerSequence_mk_eq I γ p n hc
        (d := d)
      have h' :
          AdicCompletion.mk P I (dividedPowerSequenceInIdeal I γ p n hn c) =
            AdicCompletion.mk P I (dividedPowerSequenceInIdeal I γ p n hn d) := by
        apply completion_map_subtype_injective I p hp
        calc
          _ = AdicCompletion.mk P A (dividedPowerSequence I γ p n c) :=
            map_dividedPowerSequenceInIdeal I γ p n hn c
          _ = AdicCompletion.mk P A (dividedPowerSequence I γ p n d) := h
          _ = _ := (map_dividedPowerSequenceInIdeal I γ p n hn d).symm
      exact h'.trans (by
        simpa [d] using dividedPowerSequenceInIdeal_constant I γ p n hn xi)
    have heq := congrArg Subtype.val
      (congrArg (completionIdealEquiv I p hp).1 hconst)
    have hE := (completionIdealEquiv I p hp).2
      (AdicCompletion.of P I ⟨γ.dpow n x, γ.dpow_mem hn hx⟩)
    rw [hE, AdicCompletion.map_of] at heq
    have hk : completionToQuotient I p hp
        (algebraMap A (AdicCompletion P A) x) = 0 := hmem
    have hk' : completionToQuotient I p hp (AdicCompletion.of P A x) = 0 := by
      simpa [AdicCompletion.algebraMap_apply] using hk
    simpa [completedDpowAux, hk, hk', hn, z, c, P, xi,
      AdicCompletion.algebraMap_apply] using heq

public theorem completedDpowAux_eq_mk
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (n : ℕ) (hn : n ≠ 0)
    (x : AdicCompletion (pAdicIdeal (A := A) p) A)
    (hx : x ∈ completionIdeal I p hp) :
    completedDpowAux I γ p hp n x =
      AdicCompletion.mk (pAdicIdeal (A := A) p) A
        (dividedPowerSequence I γ p n
          (completionIdealRepSequence I p hp ⟨x, hx⟩)) := by
  classical
  have h := (completionIdealEquiv I p hp).2
    (AdicCompletion.mk (pAdicIdeal (A := A) p) I
      (dividedPowerSequenceInIdeal I γ p n hn
        (completionIdealRepSequence I p hp ⟨x, hx⟩)))
  rw [map_dividedPowerSequenceInIdeal I γ p n hn] at h
  simpa [completedDpowAux, hx, hn] using h

/-- The `e`-th coordinate of an element of the completed ideal is the class of the `e`-th term
of its representing Cauchy sequence. -/
private theorem evalₐ_eq_mk_repSequence
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (e : ℕ) (x : AdicCompletion (pAdicIdeal (A := A) p) A)
    (hx : x ∈ completionIdeal I p hp) :
    AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e x =
      Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ e)
        (completionIdealRepSequence I p hp ⟨x, hx⟩ e : A) := by
  have h := congrArg (AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e)
    (completionIdealRepSequence_map_eq I p hp ⟨x, hx⟩)
  rw [AdicCompletion.map_mk, AdicCompletion.evalₐ_mk] at h
  exact h.symm

public theorem completionIdeal_eval_mem
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (e : ℕ) (x : AdicCompletion (pAdicIdeal (A := A) p) A)
    (hx : x ∈ completionIdeal I p hp) :
    AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e x ∈
      I.map (Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ e)) := by
  rw [evalₐ_eq_mk_repSequence I p hp e x hx]
  exact Ideal.mem_map_of_mem _ (completionIdealRepSequence I p hp ⟨x, hx⟩ e).property

/-- The divided powers induced on a finite-level quotient once the power of
`(p)` lies in the divided power ideal and is preserved by its operations. -/
public noncomputable def quotientDividedPowers (e : ℕ)
    (hcontained : pAdicIdeal (A := A) p ^ e ≤ I)
    (hstable : γ.IsSubDPIdeal (pAdicIdeal (A := A) p ^ e)) :
    DividedPowers (I.map (Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ e))) :=
  DividedPowers.Quotient.dividedPowers γ (by
    simpa [inf_eq_left.mpr hcontained] using hstable)

public theorem completedDpowAux_eval
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (e n : ℕ)
    (hcontained : pAdicIdeal (A := A) p ^ e ≤ I)
    (hstable : γ.IsSubDPIdeal (pAdicIdeal (A := A) p ^ e))
    (x : AdicCompletion (pAdicIdeal (A := A) p) A)
    (hx : x ∈ completionIdeal I p hp) :
    AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e
      (completedDpowAux I γ p hp n x) =
      (quotientDividedPowers I γ p e hcontained hstable).dpow n
        (AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e x) := by
  classical
  let P := pAdicIdeal (A := A) p
  let c := completionIdealRepSequence I p hp ⟨x, hx⟩
  by_cases hn : n = 0
  · subst n
    have hm : AdicCompletion.evalₐ P e x ∈ I.map (Ideal.Quotient.mk (P ^ e)) :=
      completionIdeal_eval_mem I p hp e x hx
    rw [completedDpowAux_zero_of_mem I γ p hp hx, map_one]
    exact ((quotientDividedPowers I γ p e hcontained hstable).dpow_zero hm).symm
  · rw [completedDpowAux_eq_mk I γ p hp n hn x hx,
      AdicCompletion.evalₐ_mk, evalₐ_eq_mk_repSequence I p hp e x hx]
    exact (DividedPowers.Quotient.dpow_apply γ (by
      simpa [inf_eq_left.mpr hcontained] using hstable) (c e).property).symm

public theorem ext_of_eval_ge (N : ℕ)
    {x y : AdicCompletion (pAdicIdeal (A := A) p) A}
    (h : ∀ e, N ≤ e → AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e x =
      AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e y) : x = y := by
  apply AdicCompletion.ext_evalₐ
  intro m
  let e := max N m
  have he := h e (le_max_left _ _)
  have hme : m ≤ e := le_max_right _ _
  rw [← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A) p) hme x,
    ← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A) p) hme y, he]

public theorem completedDpowAux_of_rep
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (n : ℕ) (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    completedDpowAux I γ p hp n
      (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
        (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) =
      AdicCompletion.mk (pAdicIdeal (A := A) p) A
        (dividedPowerSequence I γ p n c) := by
  classical
  let P := pAdicIdeal (A := A) p
  have hx := completion_map_subtype_mem I p hp (AdicCompletion.mk P I c)
  by_cases hn : n = 0
  · subst n
    rw [completedDpowAux_zero_of_mem I γ p hp hx]
    apply AdicCompletion.ext
    intro e
    change (1 : A ⧸ (P ^ e • ⊤ : Ideal A)) =
      Submodule.Quotient.mk (p := (P ^ e • ⊤ : Submodule A A))
        (γ.dpow 0 (c e : A))
    rw [γ.dpow_zero (c e).property]
    rfl
  · rw [completedDpowAux_eq_mk I γ p hp n hn _ hx]
    apply dividedPowerSequence_mk_eq I γ p n
    apply completion_map_subtype_injective I p hp
    exact (completionIdealRepSequence_map_eq I p hp ⟨_, hx⟩).trans rfl

public theorem completedDpowAux_eval_of_rep
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (n e : ℕ) (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e
      (completedDpowAux I γ p hp n
        (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
          (AdicCompletion.mk (pAdicIdeal (A := A) p) I c))) =
      Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ e) (γ.dpow n (c e : A)) := by
  rw [completedDpowAux_of_rep I γ p hp n c, AdicCompletion.evalₐ_mk]
  rfl

public theorem completedDpowAux_add_rep
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (n : ℕ) (c d : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    completedDpowAux I γ p hp n
      (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
        (AdicCompletion.mk (pAdicIdeal (A := A) p) I c) +
       AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
        (AdicCompletion.mk (pAdicIdeal (A := A) p) I d)) =
      (Finset.antidiagonal n).sum fun k =>
        completedDpowAux I γ p hp k.1
          (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
            (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) *
        completedDpowAux I γ p hp k.2
          (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
            (AdicCompletion.mk (pAdicIdeal (A := A) p) I d)) := by
  let P := pAdicIdeal (A := A) p
  have hsum : AdicCompletion.map P I.subtype (AdicCompletion.mk P I (c + d)) =
      AdicCompletion.map P I.subtype (AdicCompletion.mk P I c) +
      AdicCompletion.map P I.subtype (AdicCompletion.mk P I d) := by simp
  rw [← hsum]
  apply AdicCompletion.ext_evalₐ
  intro e
  rw [completedDpowAux_eval_of_rep I γ p hp n e (c + d), map_sum]
  simp_rw [map_mul, completedDpowAux_eval_of_rep]
  simp only [AdicCompletion.AdicCauchySequence.add_apply]
  simp only [Submodule.coe_add]
  rw [γ.dpow_add (c e).property (d e).property, map_sum]
  simp_rw [map_mul]

public theorem completedDpowAux_mul_dpow_rep
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (m n : ℕ) (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    completedDpowAux I γ p hp m
        (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
          (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) *
      completedDpowAux I γ p hp n
        (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
          (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) =
      Nat.choose (m + n) m * completedDpowAux I γ p hp (m + n)
        (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
          (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) := by
  apply AdicCompletion.ext_evalₐ
  intro e
  rw [map_mul, map_mul]
  simp_rw [completedDpowAux_eval_of_rep I γ p hp]
  simpa only [map_mul, map_natCast] using congrArg
    (Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ e))
    (γ.mul_dpow (c e).property (m := m) (n := n))

public theorem completedDpowAux_comp_rep
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (m n : ℕ) (hn : n ≠ 0)
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    completedDpowAux I γ p hp m
      (completedDpowAux I γ p hp n
        (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
          (AdicCompletion.mk (pAdicIdeal (A := A) p) I c))) =
      (Nat.uniformBell m n : AdicCompletion (pAdicIdeal (A := A) p) A) *
        completedDpowAux I γ p hp (m * n)
          (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
            (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) := by
  let P := pAdicIdeal (A := A) p
  let d := dividedPowerSequenceInIdeal I γ p n hn c
  have harg : completedDpowAux I γ p hp n
      (AdicCompletion.map P I.subtype (AdicCompletion.mk P I c)) =
      AdicCompletion.map P I.subtype (AdicCompletion.mk P I d) := by
    rw [completedDpowAux_of_rep I γ p hp n c,
      map_dividedPowerSequenceInIdeal I γ p n hn c]
  rw [harg]
  apply AdicCompletion.ext_evalₐ
  intro e
  rw [map_mul, completedDpowAux_eval_of_rep I γ p hp m e d,
    completedDpowAux_eval_of_rep I γ p hp (m * n) e c]
  simp only [map_natCast]
  exact congrArg (Ideal.Quotient.mk (P ^ e))
    (γ.dpow_comp hn (c e).property (m := m))

public def cauchySequenceMulIdeal
    (b : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) A)
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I := by
  let P := pAdicIdeal (A := A) p
  refine ⟨fun e => b e • c e, ?_⟩
  intro m e hme
  rw [SModEq.sub_mem]
  have hb : b m - b e ∈ P ^ m := by
    have h := SModEq.sub_mem.mp (b.property hme)
    simpa [Ideal.smul_eq_mul, Ideal.mul_top] using h
  have hc : c m - c e ∈ P ^ m • (⊤ : Submodule A I) :=
    SModEq.sub_mem.mp (c.property hme)
  have h1 : (b m - b e) • c m ∈ P ^ m • (⊤ : Submodule A I) :=
    Submodule.smul_mem_smul hb (Submodule.mem_top)
  have h2 : b e • (c m - c e) ∈ P ^ m • (⊤ : Submodule A I) :=
    Submodule.smul_mem _ _ hc
  convert Submodule.add_mem _ h1 h2 using 1; module

public theorem cauchySequenceMulIdeal_map
    (b : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) A)
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
      (AdicCompletion.mk (pAdicIdeal (A := A) p) I
        (cauchySequenceMulIdeal I p b c)) =
      AdicCompletion.mk (pAdicIdeal (A := A) p) A b *
        AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
          (AdicCompletion.mk (pAdicIdeal (A := A) p) I c) := by
  apply AdicCompletion.ext
  intro e
  simp only [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe,
    AdicCompletion.val_mul]
  rfl

public theorem completedDpowAux_mul_rep
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (n : ℕ)
    (b : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) A)
    (c : AdicCompletion.AdicCauchySequence (pAdicIdeal (A := A) p) I) :
    completedDpowAux I γ p hp n
      (AdicCompletion.mk (pAdicIdeal (A := A) p) A b *
        AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
          (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) =
      (AdicCompletion.mk (pAdicIdeal (A := A) p) A b) ^ n *
        completedDpowAux I γ p hp n
          (AdicCompletion.map (pAdicIdeal (A := A) p) I.subtype
            (AdicCompletion.mk (pAdicIdeal (A := A) p) I c)) := by
  let P := pAdicIdeal (A := A) p
  let d := cauchySequenceMulIdeal I p b c
  rw [← cauchySequenceMulIdeal_map I p b c]
  apply AdicCompletion.ext_evalₐ
  intro e
  rw [completedDpowAux_eval_of_rep I γ p hp n e d,
    map_mul, map_pow, completedDpowAux_eval_of_rep I γ p hp n e c,
    AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (P ^ e) (γ.dpow n (b e * (c e : A))) = _
  rw [γ.dpow_mul (c e).property, map_mul, map_pow]

/-- Part (3), extension: the divided powers on `I` extend to its completed
ideal.  The subtype records the naturality on the dense image of `I`. -/
@[stacks 07KD "part (3), extension"]
public noncomputable def completedDividedPowers
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) :
    { δ : DividedPowers (completionIdeal I p hp) //
      ∀ (n : ℕ) (x : A) (_hx : x ∈ I) (xhat : completionIdeal I p hp),
        (xhat : AdicCompletion (pAdicIdeal (A := A) p) A) =
            algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x →
          δ.dpow n xhat =
            algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) (γ.dpow n x) } := by
  classical
  refine ⟨{
    dpow := completedDpowAux I γ p hp
    dpow_null := ?_
    dpow_zero := ?_
    dpow_one := ?_
    dpow_mem := ?_
    dpow_add := ?_
    dpow_mul := ?_
    mul_dpow := ?_
    dpow_comp := ?_ }, ?_⟩
  · intro n x hx
    change completedDpowAux I γ p hp n x = 0
    simp [completedDpowAux, hx]
  · intro x hx
    change completedDpowAux I γ p hp 0 x = 1
    change (if hx' : _ ∈ completionIdeal I p hp then
      (if h0 : (0 : ℕ) = 0 then
        (1 : AdicCompletion (pAdicIdeal (A := A) p) A) else _) else 0) = 1
    rw [dite_eq_left hx, dite_eq_left rfl]
  · intro x hx
    exact completedDpowAux_one I γ p hp hx
  · intro n x hn hx
    exact completedDpowAux_mem I γ p hp hn hx
  · intro n x y hx hy
    let c := completionIdealRepSequence I p hp ⟨x, hx⟩
    let d := completionIdealRepSequence I p hp ⟨y, hy⟩
    have hc := completionIdealRepSequence_map_eq I p hp ⟨x, hx⟩
    have hd := completionIdealRepSequence_map_eq I p hp ⟨y, hy⟩
    simpa only [c, d, hc, hd] using completedDpowAux_add_rep I γ p hp n c d
  · intro n a x hx
    let c := completionIdealRepSequence I p hp ⟨x, hx⟩
    obtain ⟨b, hb⟩ := AdicCompletion.mk_surjective
      (pAdicIdeal (A := A) p) A a
    have hc := completionIdealRepSequence_map_eq I p hp ⟨x, hx⟩
    simpa only [c, hb, hc] using completedDpowAux_mul_rep I γ p hp n b c
  · intro m n x hx
    let c := completionIdealRepSequence I p hp ⟨x, hx⟩
    have hc := completionIdealRepSequence_map_eq I p hp ⟨x, hx⟩
    simpa only [c, hc] using completedDpowAux_mul_dpow_rep I γ p hp m n c
  · intro m n x hn hx
    let c := completionIdealRepSequence I p hp ⟨x, hx⟩
    have hc := completionIdealRepSequence_map_eq I p hp ⟨x, hx⟩
    simpa only [c, hc] using completedDpowAux_comp_rep I γ p hp m n hn c
  · intro n x hx xhat h
    change completedDpowAux I γ p hp n xhat = _
    rw [h]
    exact completedDpowAux_of I γ p hp n x hx

/-- The explicit universal property saying that a completed divided power ring
is the inverse limit of the quotients at all sufficiently large levels. -/
public def IsDividedPowerCompletionLimit
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) (N : ℕ)
    (hlevel : ∀ e, N ≤ e →
      (pAdicIdeal (A := A) p ^ e ≤ I) ∧
        γ.IsSubDPIdeal (pAdicIdeal (A := A) p ^ e)) : Prop :=
  let P := pAdicIdeal (A := A) p
  let δhat := (completedDividedPowers I γ p hp).1
  (∀ e (he : N ≤ e), δhat.IsDPMorphism
      (quotientDividedPowers I γ p e (hlevel e he).1 (hlevel e he).2)
      (AdicCompletion.evalₐ P e).toRingHom) ∧
    ∀ {B : Type v} [CommRing B] (J : Ideal B) (δ : DividedPowers J)
      (f : ∀ e (he : N ≤ e), DividedPowers.DPMorphism δ
        (quotientDividedPowers I γ p e (hlevel e he).1 (hlevel e he).2)),
      (∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right hme)).comp
            (f e he).toRingHom = (f m hm).toRingHom) →
      ∃! g : DividedPowers.DPMorphism δ δhat,
        ∀ e (he : N ≤ e),
          (AdicCompletion.evalₐ P e).toRingHom.comp g.toRingHom =
            (f e he).toRingHom

public noncomputable def tailLiftRingHom
    {B : Type v} [CommRing B] (N : ℕ)
    (f : ∀ e, N ≤ e → B →+* A ⧸ (pAdicIdeal (A := A) p) ^ e)
    (hf : ∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
      (Ideal.Quotient.factorPow (pAdicIdeal (A := A) p) hme).comp (f e he) = f m hm) :
    B →+* AdicCompletion (pAdicIdeal (A := A) p) A := by
  let P := pAdicIdeal (A := A) p
  let F : ∀ m, B →+* A ⧸ P ^ m := fun m =>
    (Ideal.Quotient.factorPow P (le_max_right N m)).comp
      (f (max N m) (le_max_left N m))
  have hF : ∀ {m e : ℕ} (hme : m ≤ e),
      (Ideal.Quotient.factorPow P hme).comp (F e) = F m := by
    intro m e hme
    let M := max N m
    let E := max N e
    have hME : M ≤ E := max_le_max le_rfl hme
    ext b
    have h := congrArg (fun g : B →+* A ⧸ P ^ M => g b)
      (hf M E (le_max_left N m) (le_max_left N e) hME)
    change Ideal.Quotient.factorPow P hme
      (Ideal.Quotient.factorPow P (le_max_right N e)
        (f E (le_max_left N e) b)) =
      Ideal.Quotient.factorPow P (le_max_right N m)
        (f M (le_max_left N m) b)
    calc
      _ = Ideal.Quotient.factorPow P (le_max_right N m)
          (Ideal.Quotient.factorPow P hME
            (f E (le_max_left N e) b)) := by
              simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_apply]
      _ = _ := by rw [show Ideal.Quotient.factorPow P hME
        (f E (le_max_left N e) b) = f M (le_max_left N m) b from h]
  exact AdicCompletion.liftRingHom P F hF

public theorem evalₐ_tailLiftRingHom
    {B : Type v} [CommRing B] (N : ℕ)
    (f : ∀ e, N ≤ e → B →+* A ⧸ (pAdicIdeal (A := A) p) ^ e)
    (hf : ∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
      (Ideal.Quotient.factorPow (pAdicIdeal (A := A) p) hme).comp (f e he) = f m hm)
    (e : ℕ) (he : N ≤ e) :
    (AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e).toRingHom.comp
        (tailLiftRingHom (A := A) p N f hf) = f e he := by
  classical
  rw [tailLiftRingHom]
  ext b
  change AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e
    (AdicCompletion.liftRingHom (pAdicIdeal (A := A) p)
      (fun m => (Ideal.Quotient.factorPow (pAdicIdeal (A := A) p)
        (le_max_right N m)).comp (f (max N m) (le_max_left N m)))
      _ b) = f e he b
  rw [AdicCompletion.evalₐ_liftRingHom]
  exact congrArg (fun g : B →+* A ⧸ (pAdicIdeal (A := A) p) ^ e => g b)
    (hf e (max N e) he (le_max_left N e) (le_max_right N e))

public theorem mem_completionIdeal_of_eval_mem
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (e : ℕ) (hte : nilpotencyExponent I p hp ≤ e)
    (x : AdicCompletion (pAdicIdeal (A := A) p) A)
    (hx : AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e x ∈
      I.map (Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ e))) :
    x ∈ completionIdeal I p hp := by
  let P := pAdicIdeal (A := A) p
  obtain ⟨a, ha, heq⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (P ^ e))
      Ideal.Quotient.mk_surjective).mp hx
  change completionToQuotient I p hp x = 0
  change (Ideal.Quotient.factor
    (pAdicIdeal_pow_nilpotencyExponent_le I p hp))
    (AdicCompletion.evalₐ P (nilpotencyExponent I p hp) x) = 0
  rw [← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A) p) hte x,
    ← heq]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factor_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- Part (4): over `ℤ_(p)`, sufficiently high powers of `(p)` are stable under
the divided powers and the completed divided power ring has the inverse-limit
universal property for the resulting quotient divided power rings. -/
@[stacks 07KD "part (4)"]
public theorem eventually_isDividedPowerCompletionLimit [Fact p.Prime]
    [Algebra (IntegersAtPrime p) A]
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) :
    ∃ N, ∃ hlevel : ∀ e, N ≤ e →
      (pAdicIdeal (A := A) p ^ e ≤ I) ∧
        γ.IsSubDPIdeal (pAdicIdeal (A := A) p ^ e),
      IsDividedPowerCompletionLimit I γ p hp N hlevel := by
  classical
  obtain ⟨N, hlevel⟩ := exists_eventual_pAdicDPIdeal I γ p hp
  refine ⟨N, hlevel, ?_⟩
  change (∀ e (he : N ≤ e),
      ((completedDividedPowers I γ p hp).1).IsDPMorphism
        (quotientDividedPowers I γ p e (hlevel e he).1 (hlevel e he).2)
        (AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e).toRingHom) ∧ _
  refine ⟨fun e he ↦ ⟨?_, fun {n} x hx ↦ ?_⟩, ?_⟩
  · exact Ideal.map_le_iff_le_comap.mpr fun x hx ↦ completionIdeal_eval_mem I p hp e x hx
  · simpa [completedDividedPowers] using
      (completedDpowAux_eval I γ p hp e n (hlevel e he).1 (hlevel e he).2 x hx).symm
  intro B _ J δ f hf
  let P := pAdicIdeal (A := A) p
  let F : ∀ e, N ≤ e → B →+* A ⧸ P ^ e := fun e he => (f e he).toRingHom
  have hF : ∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
      (Ideal.Quotient.factorPow P hme).comp (F e he) = F m hm := hf
  let gRing := tailLiftRingHom (A := A) p N F hF
  have hproj (e : ℕ) (he : N ≤ e) :
      (AdicCompletion.evalₐ P e).toRingHom.comp gRing = F e he :=
    evalₐ_tailLiftRingHom (A := A) p N F hF e he
  have hideal : J.map gRing ≤ completionIdeal I p hp := by
    refine Ideal.map_le_iff_le_comap.mpr fun b hb ↦ ?_
    let e := max N (nilpotencyExponent I p hp)
    have he : N ≤ e := le_max_left _ _
    have hmem : F e he b ∈ I.map (Ideal.Quotient.mk (P ^ e)) :=
      (f e he).ideal_comp (Ideal.mem_map_of_mem _ hb)
    rw [← DFunLike.congr_fun (hproj e he) b] at hmem
    exact mem_completionIdeal_of_eval_mem I p hp e (le_max_right _ _) (gRing b) hmem
  have hg : δ.IsDPMorphism (completedDividedPowers I γ p hp).1 gRing := by
    refine ⟨hideal, fun {n} b hb ↦ ?_⟩
    have hgb : gRing b ∈ completionIdeal I p hp := hideal (Ideal.mem_map_of_mem gRing hb)
    apply ext_of_eval_ge (A := A) p N
    intro e he
    change AdicCompletion.evalₐ P e (completedDpowAux I γ p hp n (gRing b)) =
      AdicCompletion.evalₐ P e (gRing (δ.dpow n b))
    rw [completedDpowAux_eval I γ p hp e n (hlevel e he).1 (hlevel e he).2 (gRing b) hgb,
      show AdicCompletion.evalₐ P e (gRing b) = F e he b from DFunLike.congr_fun (hproj e he) b,
      (f e he).dpow_comp b hb]
    exact (DFunLike.congr_fun (hproj e he) (δ.dpow n b)).symm
  refine ⟨DividedPowers.DPMorphism.mk' hg, hproj, fun g' hg' ↦ ?_⟩
  apply DividedPowers.DPMorphism.ext
  funext b
  apply ext_of_eval_ge (A := A) p N
  intro e he
  exact (DFunLike.congr_fun (hg' e he) b).trans (DFunLike.congr_fun (hproj e he) b).symm

end Completion

end DividedPowers
