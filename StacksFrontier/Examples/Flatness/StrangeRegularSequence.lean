module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# A regular sequence with a common annihilator modulo its last term

There is a local ring with a regular sequence `x, y, z` in its maximal ideal and a nonzero
element of the quotient by `z` annihilated by both `x` and `y`. So the image of `x` is a zero
divisor on `R/zR`, and the permuted sequence `z, x, y` is not regular, which cannot happen in a
Noetherian local ring.

The witness is built from a `ℚ`-vector space `E` with three commuting operators `X`, `Y`, `Z`
indexed so that `X` shifts the `p`-basis vectors `p i ↦ p (i+1)`, `Y` and `Z` shift and kill
them in a pattern for which `X, Y, Z` act on `E` as a weakly regular sequence. The ring is the
trivial square-zero extension `ℚ[X, Y, Z] ⋉ E`, localized at the kernel of its augmentation to
`ℚ`, and `x, y, z` are the images of the three variables. The module element `p 0` becomes the
common annihilator: `Y p 0 = 0`, while `X p 0 = p 1 = Z q 0` lies in `zR`, and `p 0` itself does
not, which is checked on the coefficient of the basis vector `p 0`. Weak regularity of the
sequence in the extension comes from weak regularity in `ℚ[X, Y, Z]` and in `E`, through the
short exact sequence relating them, and regularity in the localization follows because all three
elements lie in the augmentation prime.

## Main results

* `Stacks.Examples.exists_regularSequence_with_common_annihilator_mod_last`: the example.
* `Stacks.Examples.exists_regularSequence_with_common_annihilator_mod_last_withQ`: the same
  example, with the ring a `ℚ`-algebra.

## References

* [Stacks Project, Tag 0640](https://stacks.math.columbia.edu/tag/0640)
-/

@[expose] public section

universe u

namespace Stacks.Examples



open IsLocalRing

noncomputable section
open Finsupp
open RingTheory.Sequence
open scoped Pointwise

private inductive ExIx where
| p (i : ℤ) (j : {j : ℤ // j ≤ 0})
| q (n : ℕ) (j : ℤ)
deriving DecidableEq

private abbrev Ex := ExIx →₀ ℚ

private def opXBasis : ExIx → ExIx
| .p i j => .p (i + 1) j
| .q n j => .q (n + 1) j

private def opYBasis : ExIx → Option ExIx
| .p i j => if h : (j.val + 1) ≤ 0 then some (.p i ⟨j.val + 1, h⟩) else none
| .q n j => some (.q n (j + 1))

private def opZBasis : ExIx → Option ExIx
| .p _ _ => none
| .q n j => if h : j ≤ 0 then some (.p (n + 1) ⟨j, h⟩) else none

private def mapOpt (f : ExIx → Option ExIx) (i : ExIx) : Ex :=
  (f i).elim 0 (fun j => Finsupp.single j 1)

private def opX : Ex →ₗ[ℚ] Ex := Finsupp.lmapDomain ℚ ℚ opXBasis
private def opY : Ex →ₗ[ℚ] Ex := Finsupp.linearCombination ℚ (mapOpt opYBasis)
private def opZ : Ex →ₗ[ℚ] Ex := Finsupp.linearCombination ℚ (mapOpt opZBasis)

private theorem opX_opY : opX.comp opY = opY.comp opX := by
  ext i c
  cases i with
  | p i j =>
    by_cases hj : j.val + 1 ≤ 0
    · simp [opX, opY, opXBasis, opYBasis, mapOpt, hj, Finsupp.linearCombination_single]
    · have hj0 : j.val = 0 := by omega
      have hjeq : j = ⟨0, by omega⟩ := Subtype.ext hj0
      rw [hjeq]
      simp [opX, opY, opXBasis, opYBasis, mapOpt, Finsupp.linearCombination_single]
  | q n j =>
    simp [opX, opY, opXBasis, opYBasis, mapOpt, Finsupp.linearCombination_single]

private theorem opX_opZ : opX.comp opZ = opZ.comp opX := by
  ext i c
  cases i with
  | p i j => simp [opX, opZ, opXBasis, opZBasis, mapOpt, Finsupp.linearCombination_single]
  | q n j =>
    by_cases hj : j ≤ 0
    · simp [opX, opZ, opXBasis, opZBasis, mapOpt, hj, Finsupp.linearCombination_single]
    · simp [opX, opZ, opXBasis, opZBasis, mapOpt, hj, Finsupp.linearCombination_single]

private theorem opY_opZ : opY.comp opZ = opZ.comp opY := by
  ext i c
  cases i with
  | p i j =>
    by_cases hj : j.val + 1 ≤ 0
    · simp [opY, opZ, opYBasis, opZBasis, mapOpt, hj, Finsupp.linearCombination_single]
    · simp [opY, opZ, opYBasis, opZBasis, mapOpt, hj, Finsupp.linearCombination_single]
  | q n j =>
    by_cases hj : j ≤ 0
    · by_cases hj' : j + 1 ≤ 0
      · simp [opY, opZ, opYBasis, opZBasis, mapOpt, hj, hj', Finsupp.linearCombination_single]
      · have hjeq : j = 0 := by omega
        rw [hjeq]
        simp [opY, opZ, opYBasis, opZBasis, mapOpt, Finsupp.linearCombination_single]
    · have hj' : ¬ j + 1 ≤ 0 := by omega
      simp [opY, opZ, opYBasis, opZBasis, mapOpt, hj, hj', Finsupp.linearCombination_single]

private def genOps : Set (Module.End ℚ Ex) :=
  {opX, opY, opZ} ∪ Set.range (algebraMap ℚ (Module.End ℚ Ex))

private theorem genOps_comm (a : Module.End ℚ Ex) (ha : a ∈ genOps)
    (b : Module.End ℚ Ex) (hb : b ∈ genOps) : a * b = b * a := by
  simp only [genOps, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range] at ha hb
  rcases ha with ha | ⟨r, rfl⟩
  · rcases hb with hb | ⟨s, rfl⟩
    · rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · rfl
      · exact opX_opY
      · exact opX_opZ
      · exact opX_opY.symm
      · rfl
      · exact opY_opZ
      · exact opX_opZ.symm
      · exact opY_opZ.symm
      · rfl
    · exact (Algebra.commutes s a).symm
  · rcases hb with hb | ⟨s, rfl⟩
    · exact (Algebra.commutes r b)
    · exact Algebra.commutes r (algebraMap ℚ (Module.End ℚ Ex) s)

private abbrev ExAlg := Subring.closure genOps

private theorem exAlgComm : IsMulCommutative ExAlg :=
  Subring.isMulCommutative_closure genOps_comm

open scoped IsMulCommutative in
private noncomputable instance instExAlgCommRing : CommRing ExAlg := by
  let : IsMulCommutative ExAlg := exAlgComm
  exact inferInstance

private noncomputable def exScalar : ℚ →+* ExAlg := {
  toFun := fun r => ⟨algebraMap ℚ (Module.End ℚ Ex) r, by
    apply Subring.subset_closure
    simp [genOps]⟩
  map_one' := Subtype.ext (map_one (algebraMap ℚ (Module.End ℚ Ex)))
  map_mul' _ _ := Subtype.ext (map_mul (algebraMap ℚ (Module.End ℚ Ex)) _ _)
  map_zero' := Subtype.ext (map_zero (algebraMap ℚ (Module.End ℚ Ex)))
  map_add' _ _ := Subtype.ext (map_add (algebraMap ℚ (Module.End ℚ Ex)) _ _)
}

private noncomputable def exAlgAction : MvPolynomial (Fin 3) ℚ →+* ExAlg := by
  let : Algebra ℚ ExAlg := exScalar.toAlgebra
  exact (MvPolynomial.aeval (fun i =>
    if i = 0 then ⟨opX, Subring.subset_closure (by simp [genOps])⟩
    else if i = 1 then ⟨opY, Subring.subset_closure (by simp [genOps])⟩
    else ⟨opZ, Subring.subset_closure (by simp [genOps])⟩)).toRingHom

private noncomputable instance exModule : Module (MvPolynomial (Fin 3) ℚ) Ex :=
  Module.compHom Ex ((Subring.subtype ExAlg).comp exAlgAction)

private theorem exX_smul (e : Ex) : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) • e = opX e := by
  show ((Subring.subtype ExAlg) (exAlgAction (MvPolynomial.X 0))) e = _
  simp [exAlgAction]

private theorem opXBasis_injective : Function.Injective opXBasis := by
  intro a b hab
  cases a with
  | p i j => cases b with
    | p i' j' =>
      simp only [opXBasis, ExIx.p.injEq, add_left_inj] at hab
      rcases hab with ⟨rfl, rfl⟩
      rfl
    | q n j' => simp [opXBasis] at hab
  | q n j => cases b with
    | p i' j' => simp [opXBasis] at hab
    | q n' j' =>
      simp [opXBasis] at hab
      have hn : n = n' := by omega
      have hj : j = j' := by omega
      subst n; subst j; rfl

private theorem opX_injective : Function.Injective opX := by
  show Function.Injective (Finsupp.mapDomain opXBasis)
  exact Finsupp.mapDomain_injective opXBasis_injective

private theorem exX_regular : IsSMulRegular Ex (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) := by
  show Function.Injective (fun v : Ex => (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) • v)
  intro a b hab
  change (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) • a =
    (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) • b at hab
  rw [exX_smul a, exX_smul b] at hab
  exact opX_injective hab

private theorem exY_smul (e : Ex) : (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) • e = opY e := by
  show ((Subring.subtype ExAlg) (exAlgAction (MvPolynomial.X 1))) e = _
  simp [exAlgAction]

private theorem exZ_smul (e : Ex) : (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) • e = opZ e := by
  show ((Subring.subtype ExAlg) (exAlgAction (MvPolynomial.X 2))) e = _
  simp [exAlgAction]

private def qzero (j : ℤ) : ExIx := .q 0 j

private theorem qzero_injective : Function.Injective qzero := by
  intro a b h; cases h; rfl

private noncomputable def proj0 : Ex →ₗ[ℚ] (ℤ →₀ ℚ) :=
  Finsupp.lcomapDomain qzero qzero_injective

private theorem proj0_apply (e : Ex) (j : ℤ) : proj0 e j = e (.q 0 j) := by
  simp [proj0, qzero, Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]

private theorem opX_basis_range_compl (i : ExIx) (hi : i ∉ Set.range opXBasis) :
    ∃ j : ℤ, i = .q 0 j := by
  cases i with
  | p n j =>
    apply False.elim
    apply hi
    refine ⟨.p (n - 1) j, ?_⟩
    simp [opXBasis]
  | q n j =>
    cases n with
    | zero => exact ⟨j, rfl⟩
    | succ n =>
      apply False.elim
      apply hi
      refine ⟨.q n j, ?_⟩
      simp [opXBasis]

private theorem proj0_eq_zero_iff_range_opX (e : Ex) :
    proj0 e = 0 ↔
      e ∈ LinearMap.range (LinearMap.lsmul (MvPolynomial (Fin 3) ℚ) Ex (MvPolynomial.X 0)) := by
  constructor
  · intro he
    show ∃ v : Ex, (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) • v = e
    have hmap : e ∈ Set.range (Finsupp.mapDomain opXBasis) := by
      rw [Finsupp.mem_range_mapDomain_iff (f := opXBasis) opXBasis_injective]
      intro i hi
      obtain ⟨j, rfl⟩ := opX_basis_range_compl i hi
      have h := congrArg (fun f : ℤ →₀ ℚ => f j) he
      simpa [proj0_apply] using h
    obtain ⟨v, hv⟩ := hmap
    refine ⟨v, ?_⟩
    rw [exX_smul]
    exact hv
  · intro he
    change ∃ v : Ex, (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) • v = e at he
    obtain ⟨v, hv⟩ := he
    have hv' : opX v = e := by simpa [exX_smul] using hv
    rw [← hv']
    ext j
    have hq : ExIx.q 0 j ∉ Set.range opXBasis := by
      rintro ⟨i, hi⟩
      cases i <;> simp [opXBasis] at hi
    simp [proj0, qzero, Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply,
      opX, opXBasis, hq, Finsupp.mapDomain_of_notMem_range]

private theorem mapOpt_opY_coeff (i : ExIx) (j : ℤ) :
    mapOpt opYBasis i (.q 0 (j + 1)) = if i = .q 0 j then 1 else 0 := by
  cases i with
  | p n k =>
    by_cases hk : k.val + 1 ≤ 0
    · simp [mapOpt, opYBasis, hk]
    · simp [mapOpt, opYBasis, hk]
  | q n k =>
    by_cases hn : n = 0
    · subst n
      simp [mapOpt, opYBasis, Finsupp.single_apply]
    · simp [mapOpt, opYBasis, hn]

private theorem proj0_opY (e : Ex) (j : ℤ) : proj0 (opY e) (j + 1) = proj0 e j := by
  rw [proj0_apply, proj0_apply]
  rw [opY, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  classical
  show (∑ i ∈ e.support, e i * mapOpt opYBasis i (.q 0 (j + 1))) = e (.q 0 j)
  rw [Finset.sum_eq_single (.q 0 j)]
  · simp [mapOpt_opY_coeff]
  · intro i hi hne
    rw [mapOpt_opY_coeff]
    simp [hne]
  · intro hnot
    have hz : e (.q 0 j) = 0 := Finsupp.notMem_support_iff.mp hnot
    rw [hz]
    rw [mapOpt_opY_coeff]
    simp

private theorem exX_smulTop_eq_range_opX :
    (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) • (⊤ : Submodule (MvPolynomial (Fin 3) ℚ) Ex) =
      LinearMap.range (LinearMap.lsmul (MvPolynomial (Fin 3) ℚ) Ex (MvPolynomial.X 0)) := by
  ext e
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, trivial, hv⟩

private theorem exY_regular_quotient_x :
    IsSMulRegular (QuotSMulTop (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) Ex)
      (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro a ha
  rw [exX_smulTop_eq_range_opX] at ha
  have ha' : opY a ∈ LinearMap.range
      (LinearMap.lsmul (MvPolynomial (Fin 3) ℚ) Ex (MvPolynomial.X 0)) := by
    simpa [exY_smul] using ha
  have hp : proj0 (opY a) = 0 := (proj0_eq_zero_iff_range_opX _).2 ha'
  have haZero : proj0 a = 0 := by
    ext j
    have hj := congrArg (fun f : ℤ →₀ ℚ => f (j + 1)) hp
    rw [proj0_opY] at hj
    exact hj
  have hrange := (proj0_eq_zero_iff_range_opX a).1 haZero
  rw [exX_smulTop_eq_range_opX]
  exact hrange

private noncomputable def qEmbed : (ℤ →₀ ℚ) →ₗ[ℚ] Ex :=
  Finsupp.lmapDomain ℚ ℚ qzero

private theorem proj0_qEmbed (v : ℤ →₀ ℚ) : proj0 (qEmbed v) = v := by
  ext j
  rw [proj0_apply]
  show (Finsupp.mapDomain qzero v) (.q 0 j) = v j
  simpa [qzero] using Finsupp.mapDomain_apply qzero_injective v j

private noncomputable def shiftDown : (ℤ →₀ ℚ) →ₗ[ℚ] (ℤ →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (fun j : ℤ => j - 1)

private theorem shiftDown_apply (v : ℤ →₀ ℚ) (j : ℤ) : shiftDown v j = v (j + 1) := by
  have hi : Function.Injective (fun k : ℤ => k - 1) := by
    intro a b h
    have h' := congrArg (fun t : ℤ => t + 1) h
    simpa using h'
  show (Finsupp.mapDomain (fun k : ℤ => k - 1) v) j = v (j + 1)
  calc
    (Finsupp.mapDomain (fun k : ℤ => k - 1) v) j =
        (Finsupp.mapDomain (fun k : ℤ => k - 1) v) ((j + 1) - 1) := by congr 1; omega
    _ = v (j + 1) := by rw [Finsupp.mapDomain_apply hi v (j + 1)]

private theorem exXY_span_eq_top :
    (Ideal.ofList [(MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ),
      (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ)] •
      (⊤ : Submodule (MvPolynomial (Fin 3) ℚ) Ex)) = ⊤ := by
  rw [Ideal.ofList_cons_smul (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ)
    [MvPolynomial.X 1]
    (⊤ : Submodule (MvPolynomial (Fin 3) ℚ) Ex)]
  ext e
  rw [Submodule.mem_sup]
  constructor
  · intro _
    trivial
  · intro _
    let v := qEmbed (shiftDown (proj0 e))
    have hproj : proj0 (opY v) = proj0 e := by
      ext j
      have hj := proj0_opY v (j - 1)
      simpa [v, proj0_qEmbed, shiftDown_apply] using hj
    have hd : e - opY v ∈ LinearMap.range
        (LinearMap.lsmul (MvPolynomial (Fin 3) ℚ) Ex (MvPolynomial.X 0)) := by
      apply (proj0_eq_zero_iff_range_opX _).1
      rw [map_sub, hproj, sub_self]
    obtain ⟨w, hw⟩ := hd
    refine ⟨opX w, ?_, opY v, ?_, ?_⟩
    · rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨w, trivial, exX_smul w⟩
    · have hvY : opY v ∈ (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) •
          (⊤ : Submodule (MvPolynomial (Fin 3) ℚ) Ex) := by
        rw [Submodule.mem_smul_pointwise_iff_exists]
        exact ⟨v, trivial, exY_smul v⟩
      simpa only [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul] using hvY
    · have hw' : opX w = e - opY v := by simpa [exX_smul] using hw
      rw [hw']
      abel

private theorem exWeakRegular : IsWeaklyRegular Ex
    [(MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ), MvPolynomial.X 1, MvPolynomial.X 2] := by
  have htop : (⊤ : Submodule (MvPolynomial (Fin 3) ℚ) Ex) =
      Ideal.ofList [(MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ), MvPolynomial.X 1] •
        (⊤ : Submodule (MvPolynomial (Fin 3) ℚ) Ex) :=
    exXY_span_eq_top.symm
  have hquotTop : (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) •
      (⊤ : Submodule (MvPolynomial (Fin 3) ℚ)
        (QuotSMulTop (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) Ex)) = ⊤ := by
    have h := (Submodule.top_eq_ofList_cons_smul_iff (M := Ex)
      (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) [MvPolynomial.X 1]).mp htop
    simpa only [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul] using h.symm
  have hsub : Subsingleton (QuotSMulTop (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ)
      (QuotSMulTop (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) Ex)) :=
    Submodule.Quotient.subsingleton_iff.mpr hquotTop
  have hx := exX_regular
  have hy := exY_regular_quotient_x
  have hz : IsSMulRegular (QuotSMulTop (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ)
      (QuotSMulTop (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) Ex))
      (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) := by
    intro a b _
    exact Subsingleton.elim _ _
  apply (isWeaklyRegular_cons_iff Ex (MvPolynomial.X 0)
      [MvPolynomial.X 1, MvPolynomial.X 2]).2
  refine ⟨hx, ?_⟩
  apply (isWeaklyRegular_cons_iff (QuotSMulTop (MvPolynomial.X 0) Ex)
      (MvPolynomial.X 1) [MvPolynomial.X 2]).2
  exact ⟨hy, by
    apply (isWeaklyRegular_cons_iff
      (QuotSMulTop (MvPolynomial.X 1) (QuotSMulTop (MvPolynomial.X 0) Ex))
      (MvPolynomial.X 2) []).2
    exact ⟨hz, IsWeaklyRegular.nil (MvPolynomial (Fin 3) ℚ)
      (QuotSMulTop (MvPolynomial.X 2)
        (QuotSMulTop (MvPolynomial.X 1) (QuotSMulTop (MvPolynomial.X 0) Ex)))⟩⟩

private def pBasis (i : ℤ) : Ex := Finsupp.single (.p i ⟨0, by omega⟩) 1
private def qBasis : Ex := Finsupp.single (.q 0 0) 1
private def p00 : ExIx := .p 0 ⟨0, by omega⟩
private def p00Coeff (e : Ex) : ℚ := e p00

private theorem exC_smul (r : ℚ) (e : Ex) :
    (MvPolynomial.C r : MvPolynomial (Fin 3) ℚ) • e = r • e := by
  show ((Subring.subtype ExAlg) (exAlgAction (MvPolynomial.C r))) e = r • e
  let : Algebra ℚ ExAlg := exScalar.toAlgebra
  have hC : exAlgAction (MvPolynomial.C r) = exScalar r := by
    calc
      exAlgAction (MvPolynomial.C r) = algebraMap ℚ ExAlg r := by simp [exAlgAction]
      _ = exScalar r := by rw [RingHom.algebraMap_toAlgebra exScalar]
  rw [hC]
  show (algebraMap ℚ (Module.End ℚ Ex) r) e = r • e
  exact Module.algebraMap_end_apply ℚ ℚ Ex r e

private theorem opX_pBasis (i : ℤ) : opX (pBasis i) = pBasis (i + 1) := by
  simp [opX, pBasis, opXBasis, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private theorem opY_pBasis (i : ℤ) : opY (pBasis i) = 0 := by
  simp [opY, pBasis, opYBasis, mapOpt, Finsupp.linearCombination_single]

private theorem opZ_pBasis (i : ℤ) : opZ (pBasis i) = 0 := by
  simp [opZ, pBasis, opZBasis, mapOpt, Finsupp.linearCombination_single]

private theorem pBasis_p00Coeff (i : ℤ) (hi : i ≠ 0) : p00Coeff (pBasis i) = 0 := by
  have hne : ExIx.p i ⟨0, by omega⟩ ≠ ExIx.p 0 ⟨0, by omega⟩ := by
    intro h
    injection h with h'
    exact hi h'
  simp only [p00Coeff, p00, pBasis, Finsupp.single_apply, ite_eq_right hne]

private theorem pBasis_pos_action_coeff (f : MvPolynomial (Fin 3) ℚ) :
    ∀ i : ℤ, 0 < i → p00Coeff (f • pBasis i) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C r =>
      intro i hi
      rw [exC_smul]
      show r * p00Coeff (pBasis i) = 0
      rw [pBasis_p00Coeff i (ne_of_gt hi)]
      simp
  | add f g hf hg =>
      intro i hi
      rw [add_smul]
      show p00Coeff (f • pBasis i) + p00Coeff (g • pBasis i) = 0
      rw [hf i hi, hg i hi]
      simp
  | mul_X f n hf =>
      intro i hi
      rw [mul_smul]
      cases n using Fin.cases with
      | zero =>
          rw [exX_smul, opX_pBasis]
          exact hf (i + 1) (by omega)
      | succ j =>
          by_cases hj : j = 0
          · subst j
            show p00Coeff (f • ((MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) • pBasis i)) = 0
            rw [exY_smul, opY_pBasis]
            simp [p00Coeff, p00]
          · have hj2 : j = 1 := by omega
            subst j
            show p00Coeff (f • ((MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) • pBasis i)) = 0
            rw [exZ_smul, opZ_pBasis]
            simp [p00Coeff]

private theorem p00Coeff_smul_basis0 (f : MvPolynomial (Fin 3) ℚ) :
    p00Coeff (f • pBasis 0) = MvPolynomial.coeff 0 f := by
  induction f using MvPolynomial.induction_on with
  | C r => rw [exC_smul]; simp [p00Coeff, p00, pBasis]
  | add f g hf hg =>
      rw [add_smul]
      show p00Coeff (f • pBasis 0) + p00Coeff (g • pBasis 0) =
        MvPolynomial.coeff 0 f + MvPolynomial.coeff 0 g
      rw [hf, hg]
  | mul_X f n hf =>
      rw [mul_smul]
      cases n using Fin.cases with
      | zero =>
          rw [exX_smul, opX_pBasis]
          have hcoeff : p00Coeff (f • pBasis 1) = 0 :=
            pBasis_pos_action_coeff f 1 (by omega)
          show p00Coeff (f • pBasis 1) = MvPolynomial.coeff 0 (f * MvPolynomial.X 0)
          rw [hcoeff]
          simp [MvPolynomial.coeff_mul]
      | succ j =>
          by_cases hj : j = 0
          · subst j
            show p00Coeff (f • ((MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) • pBasis 0)) =
              MvPolynomial.coeff 0 (f * MvPolynomial.X 1)
            rw [exY_smul, opY_pBasis]
            simp [p00Coeff, MvPolynomial.coeff_mul]
          · have hj2 : j = 1 := by omega
            subst j
            show p00Coeff (f • ((MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) • pBasis 0)) =
              MvPolynomial.coeff 0 (f * MvPolynomial.X 2)
            rw [exZ_smul, opZ_pBasis]
            simp [p00Coeff, MvPolynomial.coeff_mul]




private noncomputable def polynomialQuotXEquiv (A : Type*) [CommRing A] :
    letI : Module (Polynomial A) A :=
      Module.compHom A (Polynomial.evalRingHom (0 : A))
    QuotSMulTop (Polynomial.X : Polynomial A) (Polynomial A) ≃ₗ[Polynomial A] A := by
  let : Module (Polynomial A) A := Module.compHom A (Polynomial.evalRingHom (0 : A))
  let f : Polynomial A →ₗ[Polynomial A] A := {
    toFun := Polynomial.evalRingHom (0 : A)
    map_add' := map_add _
    map_smul' := by
      intro p q
      change Polynomial.eval (0 : A) (p * q) =
        (Polynomial.evalRingHom (0 : A) p) • Polynomial.eval (0 : A) q
      rw [Polynomial.eval_mul]
      rfl }
  have hk : f.ker = (Polynomial.X : Polynomial A) •
      (⊤ : Submodule (Polynomial A) (Polynomial A)) := by
    change RingHom.ker (Polynomial.evalRingHom (0 : A)) =
      (Polynomial.X : Polynomial A) • (⊤ : Submodule (Polynomial A) (Polynomial A))
    rw [Polynomial.ker_evalRingHom]
    rw [← Submodule.ideal_span_singleton_smul (Polynomial.X : Polynomial A)
      (⊤ : Submodule (Polynomial A) (Polynomial A))]
    simp
  have hf : Function.Surjective f := by
    intro a
    exact ⟨Polynomial.C a, by simp [f]⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

private theorem poly_constant_action_rel (A : Type*) [CommRing A] (rs : List A) :
    let P := Polynomial A
    letI : Module P A := Module.compHom A (Polynomial.evalRingHom (0 : A))
    List.Forall₂ (fun (a : A) (p : P) => ∀ x : A, a • x = p • x)
      rs (rs.map (Polynomial.C : A →+* P)) := by
  let P := Polynomial A
  let : Module P A := Module.compHom A (Polynomial.evalRingHom (0 : A))
  induction rs with
  | nil => exact .nil
  | cons a rs ih =>
    apply List.Forall₂.cons
    · intro x
      show a * x = (Polynomial.evalRingHom (0 : A) (Polynomial.C a)) • x
      simp
    · exact ih

private theorem polynomial_weakreg_cons (A : Type*) [CommRing A] (rs : List A)
    (h : IsWeaklyRegular A rs) :
    IsWeaklyRegular (Polynomial A)
      (Polynomial.X :: rs.map (Polynomial.C : A →+* Polynomial A)) := by
  let P := Polynomial A
  let : Module P A := Module.compHom A (Polynomial.evalRingHom (0 : A))
  rw [isWeaklyRegular_cons_iff]
  refine ⟨?_, ?_⟩
  · exact (Polynomial.isRegular_X (R := A)).left.isSMulRegular
  · let e := polynomialQuotXEquiv A
    have hA : IsWeaklyRegular A (rs.map (Polynomial.C : A →+* P)) :=
      ((AddEquiv.refl A).isWeaklyRegular_congr (poly_constant_action_rel A rs)).mp h
    exact (e.isWeaklyRegular_congr (rs.map (Polynomial.C : A →+* P))).mpr hA

private noncomputable def mvVars (n : ℕ) : List (MvPolynomial (Fin n) ℚ) :=
  (List.finRange n).map MvPolynomial.X

private theorem mvPoly_vars_weakreg : ∀ n : ℕ,
    IsWeaklyRegular (MvPolynomial (Fin n) ℚ) (mvVars n) := by
  intro n
  induction n with
  | zero =>
      simp [mvVars]
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv ℚ n
      have hcongr : IsWeaklyRegular (MvPolynomial (Fin (n + 1)) ℚ) (mvVars (n + 1)) ↔
          IsWeaklyRegular (Polynomial (MvPolynomial (Fin n) ℚ))
            ((mvVars (n + 1)).map e) := by
        apply e.toAddEquiv.isWeaklyRegular_congr
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro r _ a
        simp [e, smul_eq_mul, map_mul]
      have hpoly : IsWeaklyRegular (Polynomial (MvPolynomial (Fin n) ℚ))
          (Polynomial.X :: (mvVars n).map (Polynomial.C : _ →+* _)) :=
        polynomial_weakreg_cons (MvPolynomial (Fin n) ℚ) (mvVars n) ih
      have hlist : (mvVars (n + 1)).map e =
          Polynomial.X :: (mvVars n).map (Polynomial.C : _ →+* _) := by
        simp [mvVars, List.finRange_succ, List.map_map, Function.comp_def, e,
          MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
      exact hcongr.mpr (hlist ▸ hpoly)


private theorem weakreg_middle_of_exact {R : Type*} [CommRing R]
    {M₁ M M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]
    (f : M₁ →ₗ[R] M) (g : M →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {rs : List R} (h₁ : IsWeaklyRegular M₁ rs) (h₂ : IsWeaklyRegular M₂ rs) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M₁ M M₂ f g with
  | nil => exact IsWeaklyRegular.nil R M
  | cons x rs ih =>
    rw [isWeaklyRegular_cons_iff] at h₁ h₂ ⊢
    rcases h₁ with ⟨h₁x, h₁tail⟩
    rcases h₂ with ⟨h₂x, h₂tail⟩
    refine ⟨isSMulRegular_of_range_eq_ker hf (LinearMap.exact_iff.mp hfg).symm h₁x h₂x, ?_⟩
    · let f' := QuotSMulTop.map x f
      let g' := QuotSMulTop.map x g
      have hzero : Function.Exact (0 : M₁ →ₗ[R] M₁) f := by
        rw [LinearMap.exact_iff, LinearMap.ker_eq_bot.mpr hf, LinearMap.range_zero]
      have hgzero : Function.Exact g (0 : M₂ →ₗ[R] M₂) := by
        rw [LinearMap.exact_iff, LinearMap.ker_zero, LinearMap.range_eq_top.mpr hg]
      have hfirst := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        hzero hfg h₂x
      have hsecond := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        hfg hgzero h₂x
      have hf' : Function.Injective f' := by
        apply LinearMap.ker_eq_bot.mp
        rw [LinearMap.exact_iff] at hfirst
        have hmap0 : QuotSMulTop.map x (0 : M₁ →ₗ[R] M₁) = 0 := by
          ext a
          rfl
        rw [hmap0, LinearMap.range_zero] at hfirst
        simpa [f'] using hfirst
      have hfg' : Function.Exact f' g' := by simpa [f', g'] using hsecond
      have hg' : Function.Surjective g' := QuotSMulTop.map_surjective x hg
      exact ih f' g' hf' hfg' hg' h₁tail h₂tail

private abbrev StrangeBase := MvPolynomial (Fin 3) ℚ
private abbrev StrangeExt := TrivSqZeroExt StrangeBase Ex

private noncomputable instance exOppModule : Module StrangeBaseᵐᵒᵖ Ex :=
  Module.compHom Ex (RingEquiv.toOpposite StrangeBase).symm.toRingHom
private instance exCentral : IsCentralScalar StrangeBase Ex := ⟨by intro r e; rfl⟩

private noncomputable def extInr : Ex →ₗ[StrangeBase] StrangeExt :=
  TrivSqZeroExt.inrHom StrangeBase Ex

private noncomputable def extFst : StrangeExt →ₗ[StrangeBase] StrangeBase :=
  (TrivSqZeroExt.fstHom StrangeBase StrangeBase Ex).toLinearMap

private theorem extInr_injective : Function.Injective extInr := LinearMap.inr_injective

private theorem extFst_surjective : Function.Surjective extFst := by
  intro a; exact ⟨TrivSqZeroExt.inl a, by simp [extFst]⟩

private theorem ext_exact : Function.Exact extInr extFst := by
  rw [LinearMap.exact_iff]
  ext a
  constructor
  · intro ha
    have ha0 : a.fst = 0 := by simpa [extFst] using ha
    refine ⟨a.snd, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [extInr, ha0]
    · simp [extInr]
  · rintro ⟨m, rfl⟩
    show TrivSqZeroExt.fst (TrivSqZeroExt.inr m) = 0
    exact TrivSqZeroExt.fst_inr (R := StrangeBase) (M := Ex) m

private theorem extWeakRegular : IsWeaklyRegular StrangeExt
    [(MvPolynomial.X 0 : StrangeBase), MvPolynomial.X 1, MvPolynomial.X 2] := by
  have hA : IsWeaklyRegular StrangeBase
      [(MvPolynomial.X 0 : StrangeBase), MvPolynomial.X 1, MvPolynomial.X 2] := by
    show IsWeaklyRegular StrangeBase (mvVars 3)
    exact mvPoly_vars_weakreg 3
  exact weakreg_middle_of_exact extInr extFst extInr_injective
    ext_exact extFst_surjective exWeakRegular hA

private theorem extSelfWeakRegular : IsWeaklyRegular StrangeExt
    [(@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 0)),
      (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 1)),
      (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2))] := by
  let : Module StrangeExt StrangeExt := inferInstance
  have hrel : List.Forall₂ (fun r s => ∀ a : StrangeExt, r • a = s • a)
      ([(MvPolynomial.X 0 : StrangeBase), MvPolynomial.X 1, MvPolynomial.X 2])
      [(@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 0)),
        (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 1)),
        (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2))] := by
    simp [List.forall₂_cons, TrivSqZeroExt.inl_mul_eq_smul]
  exact ((AddEquiv.refl StrangeExt).isWeaklyRegular_congr hrel).mp extWeakRegular

private noncomputable def aug : StrangeExt →+* ℚ :=
  (MvPolynomial.constantCoeff : StrangeBase →+* ℚ).comp
    (TrivSqZeroExt.fstHom StrangeBase StrangeBase Ex)

private noncomputable def augPrime : Ideal StrangeExt := RingHom.ker aug

private theorem opZ_p00Coeff (e : Ex) : p00Coeff (opZ e) = 0 := by
  classical
  show (opZ e) (.p 0 ⟨0, by omega⟩) = 0
  rw [opZ, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  cases i with
  | p n j => simp [mapOpt, opZBasis]
  | q n j =>
      by_cases hj : j ≤ 0
      · have hne : (↑n + 1 : ℤ) ≠ 0 := by omega
        simp [mapOpt, opZBasis, hj, hne]
      · simp [mapOpt, opZBasis, hj]

private theorem inlX_mul_inr_pBasis :
    (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 0)) *
      (@TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 0)) =
    @TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 1) := by
  rw [TrivSqZeroExt.inl_mul_inr, exX_smul]
  simp [opX_pBasis]

private theorem inlY_mul_inr_pBasis_zero :
    (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 1)) *
      (@TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 0)) = 0 := by
  rw [TrivSqZeroExt.inl_mul_inr, exY_smul, opY_pBasis]
  rfl

private theorem inlZ_mul_inr_qBasis :
    (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2)) *
      (@TrivSqZeroExt.inr StrangeBase Ex _ qBasis) =
    @TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 1) := by
  rw [TrivSqZeroExt.inl_mul_inr, exZ_smul]
  simp [qBasis, pBasis, opZ, opZBasis, mapOpt, Finsupp.linearCombination_single]

private theorem ext_main :
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra ℚ S) (x y z : S),
      x ∈ IsLocalRing.maximalIdeal S ∧ y ∈ IsLocalRing.maximalIdeal S ∧
        z ∈ IsLocalRing.maximalIdeal S ∧ RingTheory.Sequence.IsRegular S [x, y, z] ∧
        ∃ δ : S ⧸ Ideal.span {z}, δ ≠ 0 ∧
          (Ideal.Quotient.mk (Ideal.span {z}) x) * δ = 0 ∧
          (Ideal.Quotient.mk (Ideal.span {z}) y) * δ = 0 := by
  let : augPrime.IsPrime := RingHom.ker_isPrime aug
  let S := Localization.AtPrime augPrime
  let : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S augPrime
  let x : S := algebraMap StrangeExt S (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 0))
  let y : S := algebraMap StrangeExt S (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 1))
  let z : S := algebraMap StrangeExt S (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2))
  let d : S := algebraMap StrangeExt S (@TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 0))
  have hmem : ∀ a ∈ [(@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 0)),
      (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 1)),
      (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2))], a ∈ augPrime := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil] at ha
    rcases ha with rfl | rfl | rfl | h
    iterate 3 (show aug _ = 0; simp [aug])
    · contradiction
  have hreg := extSelfWeakRegular.isRegular_of_isLocalization_of_mem
    S augPrime hmem
  have hreg' : RingTheory.Sequence.IsRegular S [x, y, z] := by
    simpa [x, y, z] using hreg
  have hmemS : ∀ a ∈ augPrime, algebraMap StrangeExt S a ∈ IsLocalRing.maximalIdeal S := fun a ha =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff S augPrime a).2 ha
  let δ : S ⧸ Ideal.span {z} := Ideal.Quotient.mk _ d
  have hnot : d ∉ Ideal.span {z} := by
    intro hd
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hd
    obtain ⟨u, hu⟩ := IsLocalization.surj augPrime.primeCompl r
    have hdz : d = z * r := by simpa [d, z] using hr
    have hcleared :
        algebraMap StrangeExt S
            ((@TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 0)) * (u.2 : StrangeExt)) =
          algebraMap StrangeExt S
            ((@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2)) * u.1) := by
      calc
        _ = d * algebraMap StrangeExt S (u.2 : StrangeExt) := by simp [d]
        _ = (z * r) * algebraMap StrangeExt S (u.2 : StrangeExt) := by rw [hdz]
        _ = z * (r * algebraMap StrangeExt S (u.2 : StrangeExt)) := by ring
        _ = z * algebraMap StrangeExt S u.1 := by rw [hu]
        _ = _ := by simp [z, ← map_mul]
    obtain ⟨c, hc⟩ :=
      (IsLocalization.eq_iff_exists augPrime.primeCompl S).mp hcleared
    have hc' : ((c : StrangeExt) * u.2) *
          @TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 0) =
        (@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2)) *
          ((c : StrangeExt) * u.1) := by
      calc
        _ = (c : StrangeExt) *
            ((@TrivSqZeroExt.inr StrangeBase Ex _ (pBasis 0)) * u.2) := by ring
        _ = (c : StrangeExt) *
            ((@TrivSqZeroExt.inl StrangeBase Ex _ (MvPolynomial.X 2)) * u.1) := by rw [hc]
        _ = _ := by ring
    have hcoeff :
        p00Coeff (((c : StrangeExt) * u.2).fst • pBasis 0) =
          p00Coeff (opZ (((c : StrangeExt) * u.1).snd)) := by
      have hs := congrArg TrivSqZeroExt.snd hc'
      have hs' := congrArg p00Coeff hs
      simpa [TrivSqZeroExt.snd_mul, exZ_smul] using hs'
    have hcoeffZero : p00Coeff (((c : StrangeExt) * u.2).fst • pBasis 0) = 0 := by
      rw [hcoeff, opZ_p00Coeff]
    have hconstant := p00Coeff_smul_basis0 (((c : StrangeExt) * u.2).fst)
    have hauC : aug c ≠ 0 := fun hzero => c.2 hzero
    have hauU : aug u.2 ≠ 0 := fun hzero => u.2.2 hzero
    have hprod : aug ((c : StrangeExt) * u.2) =
        aug ((c : StrangeExt)) * aug (u.2 : StrangeExt) :=
      map_mul aug (c : StrangeExt) (u.2 : StrangeExt)
    have : aug c * aug u.2 = 0 := by
      have hcoeffZero' : MvPolynomial.coeff 0
          (TrivSqZeroExt.fst ((c : StrangeExt) * (u.2 : StrangeExt))) = 0 := by
        rw [← hconstant]
        exact hcoeffZero
      have hprod' : aug ((c : StrangeExt) * (u.2 : StrangeExt)) =
          MvPolynomial.coeff 0
            (TrivSqZeroExt.fst ((c : StrangeExt) * (u.2 : StrangeExt))) := by
        simp [aug, MvPolynomial.constantCoeff_eq]
      calc
        aug c * aug u.2 = aug ((c : StrangeExt) * (u.2 : StrangeExt)) := hprod.symm
        _ = MvPolynomial.coeff 0
            (TrivSqZeroExt.fst ((c : StrangeExt) * (u.2 : StrangeExt))) := hprod'
        _ = 0 := hcoeffZero'
    exact (mul_ne_zero hauC hauU) this
  have hδ : δ ≠ 0 := fun hzero => hnot (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hxrel : x * d = z * algebraMap StrangeExt S
      (@TrivSqZeroExt.inr StrangeBase Ex _ qBasis) := by
    dsimp [x, d, z]
    rw [← map_mul, ← map_mul, inlX_mul_inr_pBasis, inlZ_mul_inr_qBasis]
  have hyrel : y * d = 0 := by
    dsimp [y, d]
    rw [← map_mul, inlY_mul_inr_pBasis_zero, map_zero]
  refine ⟨S, inferInstance, inferInstance, inferInstance, x, y, z,
    hmemS _ (hmem _ (by simp)), hmemS _ (hmem _ (by simp)),
    hmemS _ (hmem _ (by simp)), hreg', ?_⟩
  have hann : ∀ t : S, t * d ∈ Ideal.span {z} →
      Ideal.Quotient.mk (Ideal.span {z}) t * δ = 0 := fun t ht => by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ht
  refine ⟨δ, hδ, hann x ?_, hann y ?_⟩
  · exact Ideal.mem_span_singleton.mpr ⟨_, hxrel⟩
  · rw [hyrel]
    exact zero_mem _

end

/-- There is a local `ℚ`-algebra `R` with a regular sequence `x, y, z` in its maximal ideal and a
nonzero element of `R ⧸ (z)` annihilated by both `x` and `y`. -/
theorem exists_regularSequence_with_common_annihilator_mod_last_withQ :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (_ : Algebra ℚ R)
      (x y z : R),
      x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ z ∈ maximalIdeal R ∧
        RingTheory.Sequence.IsRegular R [x, y, z] ∧
        ∃ δ : R ⧸ Ideal.span {z},
          δ ≠ 0 ∧
            (Ideal.Quotient.mk (Ideal.span {z}) x) * δ = 0 ∧
            (Ideal.Quotient.mk (Ideal.span {z}) y) * δ = 0 := by
  obtain ⟨S, hSring, hSlocal, hSalg, x, y, z, hxmem, hymem, hzmem, hreg,
      δ, hδ, hxδ, hyδ⟩ := ext_main
  let : CommRing S := hSring
  let : IsLocalRing S := hSlocal
  let : Algebra ℚ S := hSalg
  let R : Type u := ULift.{u, 0} S
  let e : S ≃+* R := (ULift.ringEquiv (R := S)).symm
  let : IsLocalHom e.toRingHom := ⟨fun a ha => by
    have h' : IsUnit (e.symm (e a)) := ha.map e.symm.toMonoidHom
    simpa using h'⟩
  let : IsLocalRing R := IsLocalRing.of_surjective e.toRingHom e.surjective
  let hRalg : Algebra ℚ R :=
    RingHom.toAlgebra ((e.toRingHom).comp (algebraMap ℚ S))
  let : Algebra ℚ R := hRalg
  let x' : R := e x
  let y' : R := e y
  let z' : R := e z
  have hrel : List.Forall₂ (fun a b => ∀ t : S, e (a * t) = b * e t)
      [x, y, z] [x', y', z'] := by
    simp [x', y', z']
  have hreg' : RingTheory.Sequence.IsRegular R [x', y', z'] :=
    (e.toAddEquiv.isRegular_congr hrel).mp hreg
  have hmem : ∀ s ∈ maximalIdeal S, e s ∈ maximalIdeal R := by
    intro s hs hu
    exact hs (by simpa [e] using hu.map e.symm.toMonoidHom)
  obtain ⟨d, hdq⟩ := Ideal.Quotient.mk_surjective δ
  have hdnot : d ∉ Ideal.span {z} := by
    intro hdm
    have hz0 := Ideal.Quotient.eq_zero_iff_mem.mpr hdm
    apply hδ
    calc
      δ = Ideal.Quotient.mk (Ideal.span {z}) d := hdq.symm
      _ = 0 := hz0
  let d' : R := e d
  have hdnot' : d' ∉ Ideal.span {z'} := by
    intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp h
    apply hdnot
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.symm r, ?_⟩
    simpa [d', z', e] using congrArg e.symm hr
  have hann : ∀ t : S, Ideal.Quotient.mk (Ideal.span {z}) t * δ = 0 →
      Ideal.Quotient.mk (Ideal.span {z'}) (e t) * Ideal.Quotient.mk (Ideal.span {z'}) d' = 0 := by
    intro t ht
    have htd : t * d ∈ Ideal.span {z} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hdq]
      exact ht
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp htd
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨e r, by simpa [d', z', e] using congrArg e hr⟩
  exact ⟨R, inferInstance, inferInstance, hRalg, x', y', z', hmem _ hxmem, hmem _ hymem,
    hmem _ hzmem, hreg', Ideal.Quotient.mk _ d',
    fun h => hdnot' (Ideal.Quotient.eq_zero_iff_mem.mp h), hann x hxδ, hann y hyδ⟩

/-- A regular sequence in a local ring can have its first two terms annihilate a common nonzero
element modulo its last term. -/
@[stacks 0640]
theorem exists_regularSequence_with_common_annihilator_mod_last :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (x y z : R),
      x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ z ∈ maximalIdeal R ∧
        RingTheory.Sequence.IsRegular R [x, y, z] ∧
        ∃ δ : R ⧸ Ideal.span {z},
          δ ≠ 0 ∧
            (Ideal.Quotient.mk (Ideal.span {z}) x) * δ = 0 ∧
            (Ideal.Quotient.mk (Ideal.span {z}) y) * δ = 0 := by
  obtain ⟨R, hR, hRlocal, _, x, y, z, hrest⟩ :=
    exists_regularSequence_with_common_annihilator_mod_last_withQ.{u}
  exact ⟨R, hR, hRlocal, x, y, z, hrest⟩

end Stacks.Examples

end
