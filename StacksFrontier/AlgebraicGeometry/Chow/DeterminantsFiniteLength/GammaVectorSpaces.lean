module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.ExteriorPower
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.ExactSequence

/-!
# The determinant map of a short exact sequence of vector spaces

For a short exact sequence of finite-dimensional vector spaces over the residue field of a
local ring, the determinant map defined using admissible sequences is the usual map on top
exterior powers: it wedges a basis of the subspace with lifts of a basis of the quotient.

## Main results

* `Module.FiniteLength.determinantExactSequenceMap_comparison_apply` identifies the
  determinant map of an exact sequence with the usual exterior-product map.

## Implementation notes

The usual determinant isomorphism is stated by its canonical multilinear rule. Exactness
supplies the equality of the three dimensions, and the formula is independent of both that
proof and the chosen lifts. The maps in the short exact sequence are linear over the residue
field and are restricted to the local ring when applying the determinant construction.

## References

* [Stacks Project, Tag 02PA](https://stacks.math.columbia.edu/tag/02PA)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
namespace Module.FiniteLength

universe u v w x

/-- The dimension of the middle term of a short exact sequence of vector spaces is the sum of
the dimensions of the outer terms. -/
private theorem finrank_exact_sequence
    {k : Type u} [Field k]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module k K] [FiniteDimensional k K]
    [AddCommGroup L] [Module k L] [FiniteDimensional k L]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (i : K →ₗ[k] L) (p : L →ₗ[k] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p) :
    Module.finrank k L = Module.finrank k K + Module.finrank k M := by
  have hker : p.ker = i.range := LinearMap.exact_iff.mp hip
  have h := LinearMap.finrank_range_add_finrank_ker p
  have hrange : p.range = ⊤ := LinearMap.range_eq_top.mpr hp
  rw [hrange, finrank_top, hker, i.finrank_range_of_inj hi] at h
  simpa [add_comm] using h.symm

/-- A family whose top wedge vanishes is linearly dependent. -/
private theorem not_linearIndependent_of_topWedge_eq_zero
    {k : Type u} [Field k] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (v : Fin (Module.finrank k V) → V)
    (hv : exteriorPower.ιMulti k (Module.finrank k V) v = 0) :
    ¬ LinearIndependent k v := by
  classical
  intro hli
  let s : Set.powersetCard (Fin (Module.finrank k V)) (Module.finrank k V) :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.id _)
  have h := (exteriorPower.ιMulti_family_linearIndependent_field
    (n := Module.finrank k V) hli).ne_zero s
  apply h
  simpa [exteriorPower.ιMulti_family, s] using hv

/-- A concatenated family is dependent as soon as its left block is. -/
private theorem append_not_linearIndependent_of_not_linearIndependent_left
    {k : Type u} [Field k]
    {K : Type v} {L : Type w}
    [AddCommGroup K] [Module k K]
    [AddCommGroup L] [Module k L]
    {m n : ℕ} (i : K →ₗ[k] L) (e : Fin m → K) (f : Fin n → L)
    (hdep : ¬ LinearIndependent k e) :
    ¬ LinearIndependent k (Fin.append (fun b ↦ i (e b)) f) := by
  intro htotal
  have heImage : LinearIndependent k (fun b : Fin m ↦ i (e b)) := by
    have h := htotal.comp (Fin.castAdd n) (Fin.castAdd_injective m n)
    change LinearIndependent k
      (fun b => Fin.append (fun b ↦ i (e b)) f (Fin.castAdd n b)) at h
    simpa only [Fin.append_left] using h
  exact hdep (LinearIndependent.of_comp i heImage)

/-- A concatenated family is dependent as soon as the images of its right block are dependent
in the quotient. -/
private theorem append_not_linearIndependent_of_not_linearIndependent_quotient
    {k : Type u} [Field k]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module k K] [FiniteDimensional k K]
    [AddCommGroup L] [Module k L] [FiniteDimensional k L]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (i : K →ₗ[k] L) (p : L →ₗ[k] M)
    (_hi : Function.Injective i) (_hp : Function.Surjective p)
    (hip : Function.Exact i p)
    {m n : ℕ} (hm : m = Module.finrank k K)
    (e : Fin m → K) (fbar : Fin n → M) (f : Fin n → L)
    (hpf : ∀ a, p (f a) = fbar a)
    (hdep : ¬ LinearIndependent k fbar) :
    ¬ LinearIndependent k (Fin.append (fun b ↦ i (e b)) f) := by
  classical
  intro htotal
  have he : LinearIndependent k e := by
    by_contra h
    exact append_not_linearIndependent_of_not_linearIndependent_left i e f h htotal
  let eb : Module.Basis (Fin m) k K :=
    basisOfLinearIndependentOfCardEqFinrank' e he (by simp [hm])
  have heb : (eb : Fin m → K) = e :=
    coe_basisOfLinearIndependentOfCardEqFinrank' e he (by simp [hm])
  rcases (Fintype.not_linearIndependent_iff.mp hdep) with ⟨g, hg, a, hga⟩
  let x : L := ∑ j, g j • f j
  have hxker : p x = 0 := by
    simp [x, hg, hpf]
  have hker : p.ker = i.range := LinearMap.exact_iff.mp hip
  have hxrange : x ∈ i.range := by
    rw [← hker, LinearMap.mem_ker]
    exact hxker
  rcases (LinearMap.mem_range.mp hxrange) with ⟨y, hy⟩
  let c : Fin m → k := fun b => eb.repr y b
  have hsume : ∑ b, c b • e b = y := by
    simpa only [c, ← heb] using eb.sum_repr y
  have hsumi : ∑ b, c b • i (e b) = x := by
    calc
      ∑ b, c b • i (e b) = i (∑ b, c b • e b) := by simp
      _ = i y := by rw [hsume]
      _ = x := hy
  let coeff : Fin (m + n) → k := Fin.append (fun b => -c b) g
  have hsum :
      ∑ q, coeff q • (Fin.append (fun b ↦ i (e b)) f q) = 0 := by
    calc
      _ = (-(∑ b, c b • i (e b))) + (∑ j, g j • f j) := by
        rw [Fin.sum_univ_add]
        simp [coeff, Fin.append_left, Fin.append_right, neg_smul]
      _ = -x + x := by rw [hsumi]
      _ = 0 := neg_add_cancel x
  have hcoeff := (Fintype.linearIndependent_iff.mp htotal) coeff hsum
  exact hga (by simpa [coeff, Fin.append_right] using hcoeff (Fin.natAdd m a))

/-- For a short exact sequence of finite-dimensional vector spaces over the residue field of a
local ring, under the canonical comparison of the determinant with the top exterior power, the
determinant map sends the exterior products of two lists of vectors to the exterior product of
the first list's image followed by arbitrary lifts of the second list. -/
@[stacks 02PA "gamma_vector_spaces"]
public theorem determinantExactSequenceMap_comparison_apply
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [Module (IsLocalRing.ResidueField R) K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [AddCommGroup L] [Module R L] [Module (IsLocalRing.ResidueField R) L]
    [IsScalarTower R (IsLocalRing.ResidueField R) L]
    [AddCommGroup M] [Module R M] [Module (IsLocalRing.ResidueField R) M]
    [IsScalarTower R (IsLocalRing.ResidueField R) M]
    [Module.Finite (IsLocalRing.ResidueField R) K]
    [Module.Finite (IsLocalRing.ResidueField R) L]
    [Module.Finite (IsLocalRing.ResidueField R) M]
    (i : K →ₗ[IsLocalRing.ResidueField R] L)
    (p : L →ₗ[IsLocalRing.ResidueField R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hM : IsFiniteLength R M) :
    ∃ hdim : Module.finrank (IsLocalRing.ResidueField R) L =
        Module.finrank (IsLocalRing.ResidueField R) K +
          Module.finrank (IsLocalRing.ResidueField R) M,
      ∀ (e : Fin (Module.finrank (IsLocalRing.ResidueField R) K) → K)
        (fbar : Fin (Module.finrank (IsLocalRing.ResidueField R) M) → M)
        (f : Fin (Module.finrank (IsLocalRing.ResidueField R) M) → L),
        (∀ a, p (f a) = fbar a) →
          (determinantExteriorPowerComparison R L).equiv
              (determinantExactSequenceMap (i.restrictScalars R) (p.restrictScalars R)
                hi hp hip hK hL hM
                ((determinantExteriorPowerComparison R K).equiv.symm
                    (exteriorPower.ιMulti (IsLocalRing.ResidueField R)
                      (Module.finrank (IsLocalRing.ResidueField R) K) e) ⊗ₜ
                  (determinantExteriorPowerComparison R M).equiv.symm
                    (exteriorPower.ιMulti (IsLocalRing.ResidueField R)
                      (Module.finrank (IsLocalRing.ResidueField R) M) fbar))) =
            exteriorPower.ιMulti (IsLocalRing.ResidueField R)
              (Module.finrank (IsLocalRing.ResidueField R) L)
              (fun a ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast hdim a)) := by
  classical
  let k := IsLocalRing.ResidueField R
  let cK := determinantExteriorPowerComparison R K
  let cL := determinantExteriorPowerComparison R L
  let cM := determinantExteriorPowerComparison R M
  let hdim := finrank_exact_sequence i p hi hp hip
  refine ⟨hdim, ?_⟩
  intro e fbar f hpf
  have hiR : Function.Injective (i.restrictScalars R) := hi
  have hpR : Function.Surjective (p.restrictScalars R) := hp
  have hipR : Function.Exact (i.restrictScalars R) (p.restrictScalars R) := hip
  let eR : Fin (moduleLength R K) → K := fun a => e (Fin.cast cK.length_eq_finrank a)
  let fbarR : Fin (moduleLength R M) → M := fun a =>
    fbar (Fin.cast cM.length_eq_finrank a)
  let fR : Fin (moduleLength R M) → L := fun a => f (Fin.cast cM.length_eq_finrank a)
  let eSeq : AdmissibleSequence R K := ⟨eR, all_admissible R K eR⟩
  let fbarSeq : AdmissibleSequence R M := ⟨fbarR, all_admissible R M fbarR⟩
  let z : Fin (Module.finrank k L) → L := fun a =>
    Fin.append (fun b ↦ i (e b)) f (Fin.cast hdim a)
  have hKsymm : cK.equiv.symm
      (exteriorPower.ιMulti k (Module.finrank k K) e) = symbol eSeq := by
    apply cK.equiv.injective
    simpa [cK, eSeq, eR, Fin.cast_cast] using (cK.equiv_symbol eSeq).symm
  have hMsymm : cM.equiv.symm
      (exteriorPower.ιMulti k (Module.finrank k M) fbar) = symbol fbarSeq := by
    apply cM.equiv.injective
    simpa [cM, fbarSeq, fbarR, Fin.cast_cast] using (cM.equiv_symbol fbarSeq).symm
  have hzero : ¬ LinearIndependent k (Fin.append (fun b ↦ i (e b)) f) →
      exteriorPower.ιMulti k (Module.finrank k L) z = 0 := fun hdep ↦
    AlternatingMap.map_linearDependent _ _ fun hz ↦ hdep (by
      have h := hz.comp (Fin.cast hdim.symm) (Fin.cast_injective hdim.symm)
      change LinearIndependent k (fun a =>
        Fin.append (fun b ↦ i (e b)) f (Fin.cast hdim (Fin.cast hdim.symm a))) at h
      simpa using h)
  by_cases he : symbol eSeq = 0
  · have hdepE := not_linearIndependent_of_topWedge_eq_zero e
      (cK.equiv.symm.map_eq_zero_iff.mp (hKsymm.trans he))
    rw [hKsymm, hMsymm, he]
    simpa [z] using (hzero
      (append_not_linearIndependent_of_not_linearIndependent_left i e f hdepE)).symm
  by_cases hf : symbol fbarSeq = 0
  · have hdepM := not_linearIndependent_of_topWedge_eq_zero fbar
      (cM.equiv.symm.map_eq_zero_iff.mp (hMsymm.trans hf))
    rw [hKsymm, hMsymm, hf]
    simpa [z] using (hzero (append_not_linearIndependent_of_not_linearIndependent_quotient
      i p hi hp hip rfl e fbar f hpf hdepM)).symm
  have hspec := determinantExactSequenceMap_spec
    (i.restrictScalars R) (p.restrictScalars R) hiR hpR hipR hK hL hM
  have hrule := hspec eSeq fbarSeq he hf fR fun a => hpf (Fin.cast cM.length_eq_finrank a)
  rcases hrule with ⟨hlen, hadm, hmap⟩
  have hlenDim : Module.finrank k L = Module.finrank k K + Module.finrank k M := by
    simpa only [cK.length_eq_finrank, cL.length_eq_finrank, cM.length_eq_finrank] using hlen
  have hlenProof : hlenDim = hdim := Subsingleton.elim _ _
  have hsum : moduleLength R K + moduleLength R M =
      Module.finrank k K + Module.finrank k M :=
    congrArg₂ Nat.add cK.length_eq_finrank cM.length_eq_finrank
  have htotal : (cL.length_eq_finrank.symm.trans hlen).trans hsum = hdim :=
    Subsingleton.elim _ _
  rw [hKsymm, hMsymm, hmap]
  show cL.equiv (symbol
    (⟨fun a ↦ Fin.append (fun b ↦ (i.restrictScalars R) (eSeq.1 b)) fR
      (Fin.cast hlen a), hadm⟩ : AdmissibleSequence R L)) = _
  rw [cL.equiv_symbol]
  congr 1
  funext a
  show Fin.append (fun b => i (e (Fin.cast cK.length_eq_finrank b)) )
      (fun b => f (Fin.cast cM.length_eq_finrank b))
      (Fin.cast hlen (Fin.cast cL.length_eq_finrank.symm a)) =
    Fin.append (fun b => i (e b)) f (Fin.cast hdim a)
  let q := Fin.cast hlen (Fin.cast cL.length_eq_finrank.symm a)
  have hq : Fin.cast hsum q = Fin.cast hdim a := by
    apply Fin.ext
    simp [q]
  show Fin.append (fun b => i (e (Fin.cast cK.length_eq_finrank b)))
      (fun b => f (Fin.cast cM.length_eq_finrank b)) q =
    Fin.append (fun b => i (e b)) f (Fin.cast hdim a)
  rw [← hq]
  cases q using Fin.addCases with
  | left b =>
      have hcast : Fin.cast hsum (Fin.castAdd (moduleLength R M) b) =
          Fin.castAdd (Module.finrank k M) (Fin.cast cK.length_eq_finrank b) := by
        apply Fin.ext
        simp
      rw [hcast, Fin.append_left, Fin.append_left]
  | right b =>
      have hcast : Fin.cast hsum (Fin.natAdd (moduleLength R K) b) =
          Fin.natAdd (Module.finrank k K) (Fin.cast cM.length_eq_finrank b) := by
        apply Fin.ext
        simp [cK.length_eq_finrank]
        rfl
      rw [hcast, Fin.append_right, Fin.append_right]

end Module.FiniteLength
end
