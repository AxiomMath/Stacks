module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Automorphisms
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison.ConnectingEquivs
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison.ConnectingEquivs

/-!
# The comparison formula for periodic determinants

The change of periodic determinant across an exact morphism of finite-length two-periodic
complexes whose differentials vanish on its kernel and cokernel is the determinant of the
relative automorphism of its two connecting isomorphisms.

## Main results

* `AlgebraicGeometry.periodicDeterminant_eq_det_connecting_mul` is the comparison formula.

## Implementation notes

The determinant of the relative automorphism of the two connecting isomorphisms is taken through
the determinant functor.

## References

* [Stacks Project, Tag 02PV](https://stacks.math.columbia.edu/tag/02PV)
-/

@[expose] public section

noncomputable section

open CategoryTheory

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v w

/-- Restricting `α` to the image of `f` gives a short exact sequence with the kernel of `α`. -/
private theorem exact_codRestrict_restrict_rangeRestrict
    {R : Type u} {M : Type v} {M' : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (α : M →ₗ[R] M') {p : Submodule R M} {q : Submodule R M'}
    (h : ∀ x ∈ p, α x ∈ q) (hK : LinearMap.ker α ≤ p) :
    Function.Injective (LinearMap.codRestrict p (LinearMap.ker α).subtype fun k => hK k.2) ∧
    Function.Exact (LinearMap.codRestrict p (LinearMap.ker α).subtype fun k => hK k.2)
      (α.restrict h).rangeRestrict ∧
    Function.Surjective (α.restrict h).rangeRestrict := by
  refine ⟨fun x y hxy => Subtype.ext (congrArg (Subtype.val : p → M) hxy), ?_,
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict _)⟩
  rw [LinearMap.exact_iff]
  ext a
  simp [Subtype.ext_iff]

/-- The sequence from the image of `α` on `range f` to `range f'` modulo `range α` is exact
and surjective. -/
private theorem exact_range_restrict_factorThroughRange
    {R : Type u} {M : Type v} {M' : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M) (f' : M' →ₗ[R] M') (α : M →ₗ[R] M')
    (hαf : α.comp f = f'.comp α) (h : ∀ x ∈ LinearMap.range f, α x ∈ LinearMap.range f')
    (hker : LinearMap.ker f' ≤ LinearMap.ker (LinearMap.range α).mkQ) :
    Function.Exact (LinearMap.range (α.restrict h)).subtype
      (factorThroughRange f' (LinearMap.range α).mkQ hker) ∧
    Function.Surjective (factorThroughRange f' (LinearMap.range α).mkQ hker) := by
  refine ⟨?_, fun q => ?_⟩
  · rw [LinearMap.exact_iff]
    ext ⟨_, x, rfl⟩
    rw [LinearMap.mem_ker, factorThroughRange_apply]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨_, LinearMap.mem_range_self (α.restrict h) ⟨f y, y, rfl⟩⟩,
        Subtype.ext (LinearMap.congr_fun hαf y)⟩
    · rintro ⟨⟨_, ⟨⟨_, y, rfl⟩, rfl⟩⟩, hy⟩
      have hy' : α (f y) = f' x := congrArg Subtype.val hy
      have hc : α (f y) = f' (α y) := LinearMap.congr_fun hαf y
      have := hker (x := x - α y) (by rw [LinearMap.mem_ker, map_sub, ← hy', hc, sub_self])
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp this
      exact ⟨z + y, by simp [hz]⟩
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    exact ⟨⟨f' x, x, rfl⟩, factorThroughRange_apply ..⟩

/-- **Stacks Project, Tag 02PV.** The change of periodic determinant is the determinant of the
second connecting isomorphism followed by the inverse of the first. -/
@[stacks 02PV "comparison formula"]
theorem periodicDeterminant_eq_det_connecting_mul
    {R : Type u} {M : Type v} {M' : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (φ ψ : M →ₗ[R] M) (φ' ψ' : M' →ₗ[R] M') (α : M →ₗ[R] M')
    (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M')
    (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hφ'ψ' : Function.Exact φ' ψ') (hψ'φ' : Function.Exact ψ' φ')
    (hαφ : α.comp φ = φ'.comp α) (hαψ : α.comp ψ = ψ'.comp α)
    (hKφ : LinearMap.ker α ≤ LinearMap.ker φ)
    (hKψ : LinearMap.ker α ≤ LinearMap.ker ψ)
    (hQφ : LinearMap.range φ' ≤ LinearMap.range α)
    (hQψ : LinearMap.range ψ' ≤ LinearMap.range α) :
    periodicDeterminant φ ψ hφψ hψφ hM =
      determinantAutomorphism
        ((connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
          hαφ hαψ hKφ hKψ hQφ hQψ).1.2.trans
          (connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
            hαφ hαψ hKφ hKψ hQφ hQψ).1.1.symm)
        (hM'.of_surjective (Submodule.mkQ_surjective (LinearMap.range α))) *
      periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM' := by
  classical
  let K := LinearMap.ker α
  let Q := M' ⧸ LinearMap.range α
  have hK : IsFiniteLength R K := hM.of_injective K.subtype_injective
  have hQ : IsFiniteLength R Q :=
    hM'.of_surjective (Submodule.mkQ_surjective (LinearMap.range α))
  let ePair := connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
    hαφ hαψ hKφ hKψ hQφ hQψ
  let e0 := ePair.1.1
  let e1 := ePair.1.2
  let A := LinearMap.range φ
  let A' := LinearMap.range φ'
  let B := LinearMap.range ψ
  let B' := LinearMap.range ψ'
  have hA : IsFiniteLength R A := hM.of_injective A.subtype_injective
  have hA' : IsFiniteLength R A' := hM'.of_injective A'.subtype_injective
  have hB : IsFiniteLength R B := hM.of_injective B.subtype_injective
  have hB' : IsFiniteLength R B' := hM'.of_injective B'.subtype_injective
  have hmapφ : ∀ x ∈ A, α x ∈ A' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨α x, (LinearMap.congr_fun hαφ x).symm⟩
  have hmapψ : ∀ x ∈ B, α x ∈ B' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨α x, (LinearMap.congr_fun hαψ x).symm⟩
  have hKA : LinearMap.ker α ≤ A := fun k hk => hφψ.linearMap_ker_eq.le (hKψ hk)
  have hKB : LinearMap.ker α ≤ B := fun k hk => hψφ.linearMap_ker_eq.le (hKφ hk)
  let iKφ : K →ₗ[R] A := LinearMap.codRestrict A K.subtype fun k => hKA k.2
  let iKψ : K →ₗ[R] B := LinearMap.codRestrict B K.subtype fun k => hKB k.2
  let αAφ := α.restrict hmapφ
  let αBψ := α.restrict hmapψ
  let Tφ := LinearMap.range αAφ
  let Tψ := LinearMap.range αBψ
  let pAφ := αAφ.rangeRestrict
  let pBψ := αBψ.rangeRestrict
  obtain ⟨hiKφ, hexAφ, hpAφ⟩ := exact_codRestrict_restrict_rangeRestrict α hmapφ hKA
  obtain ⟨hiKψ, hexBψ, hpBψ⟩ := exact_codRestrict_restrict_rangeRestrict α hmapψ hKB
  have hTφ : IsFiniteLength R Tφ := hA'.of_injective Tφ.subtype_injective
  have hTψ : IsFiniteLength R Tψ := hB'.of_injective Tψ.subtype_injective
  obtain ⟨z, hz, hzspan⟩ := exists_spanning_symbol hK
  obtain ⟨tφ, htφ, htφspan⟩ := exists_spanning_symbol hTφ
  obtain ⟨tψ, htψ, htψspan⟩ := exists_spanning_symbol hTψ
  let liftφ : Fin (moduleLength R Tφ) → A := fun j =>
    Classical.choose (hpAφ (tφ.1 j))
  have hliftφ (j : Fin (moduleLength R Tφ)) :
      pAφ (liftφ j) = tφ.1 j := Classical.choose_spec (hpAφ (tφ.1 j))
  let liftψ : Fin (moduleLength R Tψ) → B := fun j =>
    Classical.choose (hpBψ (tψ.1 j))
  have hliftψ (j : Fin (moduleLength R Tψ)) :
      pBψ (liftψ j) = tψ.1 j := Classical.choose_spec (hpBψ (tψ.1 j))
  have hαliftφ (i : Fin (moduleLength R Tφ)) :
      α (liftφ i : M) = (Tφ.subtype (tφ.1 i) : M') :=
    congrArg (fun t : Tφ => ((t : A') : M')) (hliftφ i)
  have hαliftψ (i : Fin (moduleLength R Tψ)) :
      α (liftψ i : M) = (Tψ.subtype (tψ.1 i) : M') :=
    congrArg (fun t : Tψ => ((t : B') : M')) (hliftψ i)
  obtain ⟨hlenφ, hadmφ, hspanφ⟩ := extend_generating_sequence
    iKφ pAφ hiKφ hpAφ hexAφ hK hA hTφ z hzspan tφ htφspan liftφ hliftφ
  obtain ⟨hlenψ, hadmψ, hspanψ⟩ := extend_generating_sequence
    iKψ pBψ hiKψ hpBψ hexBψ hK hB hTψ z hzspan tψ htψspan liftψ hliftψ
  let x : AdmissibleSequence R A :=
    ⟨fun j ↦ Fin.append (fun i ↦ iKφ (z.1 i)) liftφ (Fin.cast hlenφ j), hadmφ⟩
  let y : AdmissibleSequence R B :=
    ⟨fun j ↦ Fin.append (fun i ↦ iKψ (z.1 i)) liftψ (Fin.cast hlenψ j), hadmψ⟩
  have hxspan : Submodule.span R (Set.range x.1) = ⊤ := hspanφ
  have hyspan : Submodule.span R (Set.range y.1) = ⊤ := hspanψ
  let qα := (LinearMap.range α).mkQ
  have hkerφ' : LinearMap.ker φ' ≤ LinearMap.ker qα :=
    (hψ'φ'.linearMap_ker_eq.le.trans hQψ).trans (Submodule.ker_mkQ _).ge
  let pA' := factorThroughRange φ' qα hkerφ'
  obtain ⟨hexA', hpA'⟩ := exact_range_restrict_factorThroughRange φ φ' α hαφ hmapφ hkerφ'
  have hlenKQ : moduleLength R K = moduleLength R Q :=
    congrArg ENat.toNat e0.symm.length_eq
  have hzcast : IsAdmissibleSequence (R := R)
      (fun j : Fin (moduleLength R Q) => z.1 (Fin.cast hlenKQ.symm j)) :=
    admissible_cast hlenKQ.symm z.1 z.2
  have hzcastspan : Submodule.span R
      (Set.range (fun j : Fin (moduleLength R Q) =>
        z.1 (Fin.cast hlenKQ.symm j))) = ⊤ :=
    span_top_sequence_cast hlenKQ.symm z.1 hzspan
  let wφ : AdmissibleSequence R Q :=
    ⟨fun j ↦ e0.symm (z.1 (Fin.cast hlenKQ.symm j)),
      map_admissible_sequence e0.symm.toLinearMap
        (fun j ↦ z.1 (Fin.cast hlenKQ.symm j)) hzcast⟩
  have hwφspan : Submodule.span R (Set.range wφ.1) = ⊤ := by
    change Submodule.span R
      (Set.range (e0.symm ∘ fun j ↦ z.1 (Fin.cast hlenKQ.symm j))) = ⊤
    exact span_top_map_linearEquiv
      (fun j ↦ z.1 (Fin.cast hlenKQ.symm j)) hzcastspan e0.symm
  let wrepφ : Fin (moduleLength R Q) → M' := fun j =>
    Classical.choose (Submodule.mkQ_surjective (LinearMap.range α) (wφ.1 j))
  have hwrepφ (j : Fin (moduleLength R Q)) : qα (wrepφ j) = wφ.1 j :=
    Classical.choose_spec (Submodule.mkQ_surjective (LinearMap.range α) (wφ.1 j))
  let liftQφ : Fin (moduleLength R Q) → A' := fun j =>
    ⟨φ' (wrepφ j), LinearMap.mem_range_self φ' (wrepφ j)⟩
  have hliftQφ (j : Fin (moduleLength R Q)) : pA' (liftQφ j) = wφ.1 j := by
    rw [show liftQφ j = ⟨φ' (wrepφ j), LinearMap.mem_range_self φ' (wrepφ j)⟩ from rfl,
      factorThroughRange_apply φ' qα hkerφ' (wrepφ j), hwrepφ]
  obtain ⟨hlenA', hadmA', hspanA'⟩ := extend_generating_sequence
    Tφ.subtype pA' Tφ.subtype_injective hpA' hexA' hTφ hA' hQ
    tφ htφspan wφ hwφspan liftQφ hliftQφ
  let x' : AdmissibleSequence R A' :=
    ⟨fun j ↦ Fin.append (fun i ↦ Tφ.subtype (tφ.1 i)) liftQφ
      (Fin.cast hlenA' j), hadmA'⟩
  have hx'span : Submodule.span R (Set.range x'.1) = ⊤ := hspanA'
  have hkerψ' : LinearMap.ker ψ' ≤ LinearMap.ker qα :=
    (hφ'ψ'.linearMap_ker_eq.le.trans hQφ).trans (Submodule.ker_mkQ _).ge
  let pB' := factorThroughRange ψ' qα hkerψ'
  obtain ⟨hexB', hpB'⟩ := exact_range_restrict_factorThroughRange ψ ψ' α hαψ hmapψ hkerψ'
  let wψ : AdmissibleSequence R Q :=
    ⟨fun j ↦ e1.symm (z.1 (Fin.cast hlenKQ.symm j)),
      map_admissible_sequence e1.symm.toLinearMap
        (fun j ↦ z.1 (Fin.cast hlenKQ.symm j)) hzcast⟩
  have hwψspan : Submodule.span R (Set.range wψ.1) = ⊤ := by
    change Submodule.span R
      (Set.range (e1.symm ∘ fun j ↦ z.1 (Fin.cast hlenKQ.symm j))) = ⊤
    exact span_top_map_linearEquiv
      (fun j ↦ z.1 (Fin.cast hlenKQ.symm j)) hzcastspan e1.symm
  let wrepψ : Fin (moduleLength R Q) → M' := fun j =>
    Classical.choose (Submodule.mkQ_surjective (LinearMap.range α) (wψ.1 j))
  have hwrepψ (j : Fin (moduleLength R Q)) : qα (wrepψ j) = wψ.1 j :=
    Classical.choose_spec (Submodule.mkQ_surjective (LinearMap.range α) (wψ.1 j))
  let liftQψ : Fin (moduleLength R Q) → B' := fun j =>
    ⟨ψ' (wrepψ j), LinearMap.mem_range_self ψ' (wrepψ j)⟩
  have hliftQψ (j : Fin (moduleLength R Q)) : pB' (liftQψ j) = wψ.1 j := by
    rw [show liftQψ j = ⟨ψ' (wrepψ j), LinearMap.mem_range_self ψ' (wrepψ j)⟩ from rfl,
      factorThroughRange_apply ψ' qα hkerψ' (wrepψ j), hwrepψ]
  obtain ⟨hlenB', hadmB', hspanB'⟩ := extend_generating_sequence
    Tψ.subtype pB' Tψ.subtype_injective hpB' hexB' hTψ hB' hQ
    tψ htψspan wψ hwψspan liftQψ hliftQψ
  let y' : AdmissibleSequence R B' :=
    ⟨fun j ↦ Fin.append (fun i ↦ Tψ.subtype (tψ.1 i)) liftQψ
      (Fin.cast hlenB' j), hadmB'⟩
  have hy'span : Submodule.span R (Set.range y'.1) = ⊤ := hspanB'
  have hφQ (j : Fin (moduleLength R Q)) :
      φ' (wrepφ j) ∈ LinearMap.range α :=
    hQφ (LinearMap.mem_range_self φ' (wrepφ j))
  let zψpre : Fin (moduleLength R K) → M := fun i =>
    Classical.choose (hφQ (Fin.cast hlenKQ i))
  have hαzψpre (i : Fin (moduleLength R K)) :
      α (zψpre i) = φ' (wrepφ (Fin.cast hlenKQ i)) :=
    Classical.choose_spec (hφQ (Fin.cast hlenKQ i))
  have hψzψpre (i : Fin (moduleLength R K)) : ψ (zψpre i) = (z.1 i : M) := by
    have hconn := ePair.2.1 (wrepφ (Fin.cast hlenKQ i)) (zψpre i) (hαzψpre i)
    have he0 : e0 (qα (wrepφ (Fin.cast hlenKQ i))) = z.1 i := by
      rw [hwrepφ]
      simp [wφ]
    calc
      ψ (zψpre i) = (e0 (qα (wrepφ (Fin.cast hlenKQ i))) : M) := hconn.symm
      _ = (z.1 i : M) := congrArg Subtype.val he0
  have hψQ (j : Fin (moduleLength R Q)) :
      ψ' (wrepψ j) ∈ LinearMap.range α :=
    hQψ (LinearMap.mem_range_self ψ' (wrepψ j))
  let zφpre : Fin (moduleLength R K) → M := fun i =>
    Classical.choose (hψQ (Fin.cast hlenKQ i))
  have hαzφpre (i : Fin (moduleLength R K)) :
      α (zφpre i) = ψ' (wrepψ (Fin.cast hlenKQ i)) :=
    Classical.choose_spec (hψQ (Fin.cast hlenKQ i))
  have hφzφpre (i : Fin (moduleLength R K)) : φ (zφpre i) = (z.1 i : M) := by
    have hconn := ePair.2.2 (wrepψ (Fin.cast hlenKQ i)) (zφpre i) (hαzφpre i)
    have he1 : e1 (qα (wrepψ (Fin.cast hlenKQ i))) = z.1 i := by
      rw [hwrepψ]
      simp [wψ]
    calc
      φ (zφpre i) = (e1 (qα (wrepψ (Fin.cast hlenKQ i))) : M) := hconn.symm
      _ = (z.1 i : M) := congrArg Subtype.val he1
  let tailPreφ : Fin (moduleLength R Tφ) → M := fun i =>
    Classical.choose (liftφ i).property
  have htailPreφ (i : Fin (moduleLength R Tφ)) :
      φ (tailPreφ i) = (liftφ i : M) := Classical.choose_spec (liftφ i).property
  let tailPreψ : Fin (moduleLength R Tψ) → M := fun i =>
    Classical.choose (liftψ i).property
  have htailPreψ (i : Fin (moduleLength R Tψ)) :
      ψ (tailPreψ i) = (liftψ i : M) := Classical.choose_spec (liftψ i).property
  let xLift : Fin (moduleLength R A) → M := fun j =>
    Fin.append zφpre tailPreφ (Fin.cast hlenφ j)
  have hxLift (j : Fin (moduleLength R A)) : φ (xLift j) = (x.1 j : M) := by
    let q := Fin.cast hlenφ j
    have hq : Fin.cast hlenφ.symm q = j := by simp [q]
    rw [← hq]
    change φ (Fin.append zφpre tailPreφ q) =
      (Fin.append (fun i ↦ iKφ (z.1 i)) liftφ q : A)
    refine Fin.addCases ?_ ?_ q
    · intro i
      rw [Fin.append_left, Fin.append_left]
      simpa [iKφ] using hφzφpre i
    · intro i
      rw [Fin.append_right, Fin.append_right]
      exact htailPreφ i
  let yLift : Fin (moduleLength R B) → M := fun j =>
    Fin.append zψpre tailPreψ (Fin.cast hlenψ j)
  have hyLift (j : Fin (moduleLength R B)) : ψ (yLift j) = (y.1 j : M) := by
    let q := Fin.cast hlenψ j
    have hq : Fin.cast hlenψ.symm q = j := by simp [q]
    rw [← hq]
    change ψ (Fin.append zψpre tailPreψ q) =
      (Fin.append (fun i ↦ iKψ (z.1 i)) liftψ q : B)
    refine Fin.addCases ?_ ?_ q
    · intro i
      rw [Fin.append_left, Fin.append_left]
      simpa [iKψ] using hψzψpre i
    · intro i
      rw [Fin.append_right, Fin.append_right]
      exact htailPreψ i
  have hxsymspan : (IsLocalRing.ResidueField R) ∙ symbol x = ⊤ :=
    span_symbol_eq_top hA x hxspan
  have hysymspan : (IsLocalRing.ResidueField R) ∙ symbol y = ⊤ :=
    span_symbol_eq_top hB y hyspan
  obtain ⟨hsrcLlen, hsrcRlen, hsrcLadm, hsrcRadm, hsrcEq⟩ :=
    periodicDeterminant_symbol_eq φ ψ hφψ hψφ hM x y
      hxsymspan hysymspan xLift yLift hxLift hyLift
  let xLift' : Fin (moduleLength R A') → M' := fun j =>
    Fin.append (fun i => α (tailPreφ i)) wrepφ (Fin.cast hlenA' j)
  have hxLift' (j : Fin (moduleLength R A')) : φ' (xLift' j) = (x'.1 j : M') := by
    let q := Fin.cast hlenA' j
    have hq : Fin.cast hlenA'.symm q = j := by simp [q]
    rw [← hq]
    change φ' (Fin.append (fun i => α (tailPreφ i)) wrepφ q) =
      (Fin.append (fun i ↦ Tφ.subtype (tφ.1 i)) liftQφ q : A')
    refine Fin.addCases ?_ ?_ q
    · intro i
      rw [Fin.append_left, Fin.append_left]
      have hc : φ' (α (tailPreφ i)) = α (φ (tailPreφ i)) :=
        (LinearMap.congr_fun hαφ _).symm
      exact (hc.trans (congrArg α (htailPreφ i))).trans (hαliftφ i)
    · intro i
      rw [Fin.append_right, Fin.append_right]
  let yLift' : Fin (moduleLength R B') → M' := fun j =>
    Fin.append (fun i => α (tailPreψ i)) wrepψ (Fin.cast hlenB' j)
  have hyLift' (j : Fin (moduleLength R B')) : ψ' (yLift' j) = (y'.1 j : M') := by
    let q := Fin.cast hlenB' j
    have hq : Fin.cast hlenB'.symm q = j := by simp [q]
    rw [← hq]
    change ψ' (Fin.append (fun i => α (tailPreψ i)) wrepψ q) =
      (Fin.append (fun i ↦ Tψ.subtype (tψ.1 i)) liftQψ q : B')
    refine Fin.addCases ?_ ?_ q
    · intro i
      rw [Fin.append_left, Fin.append_left]
      have hc : ψ' (α (tailPreψ i)) = α (ψ (tailPreψ i)) :=
        (LinearMap.congr_fun hαψ _).symm
      exact (hc.trans (congrArg α (htailPreψ i))).trans (hαliftψ i)
    · intro i
      rw [Fin.append_right, Fin.append_right]
  have hx'symspan : (IsLocalRing.ResidueField R) ∙ symbol x' = ⊤ :=
    span_symbol_eq_top hA' x' hx'span
  have hy'symspan : (IsLocalRing.ResidueField R) ∙ symbol y' = ⊤ :=
    span_symbol_eq_top hB' y' hy'span
  obtain ⟨htgtLlen, htgtRlen, htgtLadm, htgtRadm, htgtEq⟩ :=
    periodicDeterminant_symbol_eq φ' ψ' hφ'ψ' hψ'φ' hM'
      x' y' hx'symspan hy'symspan xLift' yLift' hxLift' hyLift'
  let sourceLeft : AdmissibleSequence R M :=
    ⟨fun j ↦ Fin.append (fun i ↦ (x.1 i : M)) yLift (Fin.cast hsrcLlen j), hsrcLadm⟩
  let sourceRight : AdmissibleSequence R M :=
    ⟨fun j ↦ Fin.append (fun i ↦ (y.1 i : M)) xLift (Fin.cast hsrcRlen j), hsrcRadm⟩
  have hsrcEq' : symbol sourceLeft =
      (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R A * moduleLength R B)) *
        (periodicDeterminant φ ψ hφψ hψφ hM :
          IsLocalRing.ResidueField R)) • symbol sourceRight := by
    simpa [sourceLeft, sourceRight] using hsrcEq
  let iK : K →ₗ[R] M := K.subtype
  let qN : M →ₗ[R] LinearMap.range α := LinearMap.rangeRestrict α
  have hiK : Function.Injective iK := K.subtype_injective
  have hqN : Function.Surjective qN :=
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict α)
  have hexKMN : Function.Exact iK qN := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hN : IsFiniteLength R (LinearMap.range α) :=
    hM'.of_injective (LinearMap.range α).subtype_injective
  obtain ⟨sN, hsN, hsNspan⟩ := exists_spanning_symbol hN
  let liftN : Fin (moduleLength R (LinearMap.range α)) → M := fun j =>
    Classical.choose (hqN (sN.1 j))
  have hliftN (j : Fin (moduleLength R (LinearMap.range α))) :
      qN (liftN j) = sN.1 j := Classical.choose_spec (hqN (sN.1 j))
  obtain ⟨hlenKMN, hadmKMN, hspecKMN⟩ :=
    (determinantExactSequenceMap_spec iK qN hiK hqN hexKMN hK hM hN) z
      sN hz hsN liftN hliftN
  let preK : Fin (moduleLength R K) → M := fun i => K.subtype (z.1 i)
  let tailLeft : Fin (moduleLength R (LinearMap.range α)) → M := fun j =>
    sourceLeft.1 (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K) j))
  let tailRight : Fin (moduleLength R (LinearMap.range α)) → M := fun j =>
    sourceRight.1 (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K) j))
  have hdecompLeft : sourceLeft.1 = fun j ↦
      Fin.append preK tailLeft (Fin.cast hlenKMN j) := by
    funext j
    let q := Fin.cast hlenKMN j
    have hq : Fin.cast hlenKMN.symm q = j := by simp [q]
    rw [← hq]
    refine Fin.addCases ?_ ?_ q
    · intro i
      have hidx : Fin.cast hlenKMN.symm (Fin.castAdd
          (moduleLength R (LinearMap.range α)) i) =
          Fin.cast hsrcLlen.symm (Fin.castAdd (moduleLength R B)
            (Fin.cast hlenφ.symm (Fin.castAdd (moduleLength R Tφ) i))) := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_castAdd]
      rw [hidx]
      have hcast : Fin.cast hlenKMN
          (Fin.cast hsrcLlen.symm
            (Fin.castAdd (moduleLength R B)
              (Fin.cast hlenφ.symm (Fin.castAdd (moduleLength R Tφ) i)))) =
          Fin.castAdd (moduleLength R (LinearMap.range α)) i := by
        rw [← hidx]
        simp
      rw [hcast, Fin.append_left]
      simp [sourceLeft, preK, x, Fin.append_left, iKφ, K]
    · intro i
      simp [tailLeft]
  have hdecompRight : sourceRight.1 = fun j ↦
      Fin.append preK tailRight (Fin.cast hlenKMN j) := by
    funext j
    let q := Fin.cast hlenKMN j
    have hq : Fin.cast hlenKMN.symm q = j := by simp [q]
    rw [← hq]
    refine Fin.addCases ?_ ?_ q
    · intro i
      have hidx : Fin.cast hlenKMN.symm (Fin.castAdd
          (moduleLength R (LinearMap.range α)) i) =
          Fin.cast hsrcRlen.symm (Fin.castAdd (moduleLength R A)
            (Fin.cast hlenψ.symm (Fin.castAdd (moduleLength R Tψ) i))) := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_castAdd]
      rw [hidx]
      have hcast : Fin.cast hlenKMN
          (Fin.cast hsrcRlen.symm
            (Fin.castAdd (moduleLength R A)
              (Fin.cast hlenψ.symm (Fin.castAdd (moduleLength R Tψ) i)))) =
          Fin.castAdd (moduleLength R (LinearMap.range α)) i := by
        rw [← hidx]
        simp
      rw [hcast, Fin.append_left]
      simp [sourceRight, preK, y, Fin.append_left, iKψ, K]
    · intro i
      simp [tailRight]
  have hprezero (i : Fin (moduleLength R K)) : qN (preK i) = 0 := by
    apply Subtype.ext
    change α (K.subtype (z.1 i)) = 0
    exact LinearMap.mem_ker.mp (z.1 i).property
  have hadmTailLeft : IsAdmissibleSequence (R := R) (qN ∘ tailLeft) := by
    have hconcat : IsAdmissibleSequence (R := R) (Fin.append preK tailLeft) := by
      have hcast := admissible_cast hlenKMN.symm sourceLeft.1 sourceLeft.property
      simpa [hdecompLeft] using hcast
    exact admissible_tail_of_zero_prefix qN preK tailLeft
      (by intro i; exact hprezero i) hconcat
  have hadmTailRight : IsAdmissibleSequence (R := R) (qN ∘ tailRight) := by
    have hconcat : IsAdmissibleSequence (R := R) (Fin.append preK tailRight) := by
      have hcast := admissible_cast hlenKMN.symm sourceRight.1 sourceRight.property
      simpa [hdecompRight] using hcast
    exact admissible_tail_of_zero_prefix qN preK tailRight
      (by intro i; exact hprezero i) hconcat
  let nLeft : AdmissibleSequence R (LinearMap.range α) := ⟨qN ∘ tailLeft, hadmTailLeft⟩
  let nRight : AdmissibleSequence R (LinearMap.range α) := ⟨qN ∘ tailRight, hadmTailRight⟩
  have hsourceLeftRawSpan : Submodule.span R
      (Set.range (Fin.append (fun i ↦ (x.1 i : M)) yLift)) = ⊤ := by
    let pψ := ψ.rangeRestrict
    have hip : Function.Injective A.subtype := A.subtype_injective
    have hpp : Function.Surjective pψ :=
      LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict ψ)
    have hex : Function.Exact A.subtype pψ := by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      exact hφψ.linearMap_ker_eq
    exact append_spans_of_exact A.subtype pψ hip hpp hex
      x.1 y.1 yLift (by intro j; exact Subtype.ext (hyLift j)) hxspan hyspan
  have hsourceLeftSpan : Submodule.span R (Set.range sourceLeft.1) = ⊤ := by
    change Submodule.span R (Set.range
      (fun j ↦ Fin.append (fun i ↦ (x.1 i : M)) yLift (Fin.cast hsrcLlen j))) = ⊤
    exact span_top_append_cast hsrcLlen (fun i ↦ (x.1 i : M)) yLift hsourceLeftRawSpan
  have hsourceRightRawSpan : Submodule.span R
      (Set.range (Fin.append (fun i ↦ (y.1 i : M)) xLift)) = ⊤ := by
    let pφ := φ.rangeRestrict
    have hip : Function.Injective B.subtype := B.subtype_injective
    have hpp : Function.Surjective pφ :=
      LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict φ)
    have hex : Function.Exact B.subtype pφ := by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      exact hψφ.linearMap_ker_eq
    exact append_spans_of_exact B.subtype pφ hip hpp hex
      y.1 x.1 xLift (by intro j; exact Subtype.ext (hxLift j)) hyspan hxspan
  have hsourceRightSpan : Submodule.span R (Set.range sourceRight.1) = ⊤ := by
    change Submodule.span R (Set.range
      (fun j ↦ Fin.append (fun i ↦ (y.1 i : M)) xLift (Fin.cast hsrcRlen j))) = ⊤
    exact span_top_append_cast hsrcRlen (fun i ↦ (y.1 i : M)) xLift hsourceRightRawSpan
  have hkernelConcatLeftSpan : Submodule.span R
      (Set.range (Fin.append preK tailLeft)) = ⊤ := by
    have hcast := span_top_sequence_cast hlenKMN.symm sourceLeft.1 hsourceLeftSpan
    simpa [hdecompLeft] using hcast
  have hkernelConcatRightSpan : Submodule.span R
      (Set.range (Fin.append preK tailRight)) = ⊤ := by
    have hcast := span_top_sequence_cast hlenKMN.symm sourceRight.1 hsourceRightSpan
    simpa [hdecompRight] using hcast
  have hnLeftSpan : Submodule.span R (Set.range nLeft.1) = ⊤ := by
    change Submodule.span R (Set.range (qN ∘ tailLeft)) = ⊤
    exact append_tail_spans_of_surjective qN hqN preK tailLeft
      hprezero hkernelConcatLeftSpan
  have hnRightSpan : Submodule.span R (Set.range nRight.1) = ⊤ := by
    change Submodule.span R (Set.range (qN ∘ tailRight)) = ⊤
    exact append_tail_spans_of_surjective qN hqN preK tailRight
      hprezero hkernelConcatRightSpan
  have hnLeft0 : symbol nLeft ≠ 0 := symbol_ne_zero_of_span_top hN nLeft hnLeftSpan
  have hnRight0 : symbol nRight ≠ 0 := symbol_ne_zero_of_span_top hN nRight hnRightSpan
  let γN := determinantExactSequenceMap iK qN hiK hqN hexKMN hK hM hN
  have hγNbij : Function.Bijective γN :=
    determinantExactSequenceMap_bijective iK qN hiK hqN hexKMN hK hM hN
  obtain ⟨hlenLeft, hadmLeft, hspecLeft⟩ :=
    (determinantExactSequenceMap_spec iK qN hiK hqN hexKMN hK hM hN) z nLeft hz hnLeft0
      tailLeft (by intro j; rfl)
  obtain ⟨hlenRight, hadmRight, hspecRight⟩ :=
    (determinantExactSequenceMap_spec iK qN hiK hqN hexKMN hK hM hN) z nRight hz hnRight0
      tailRight (by intro j; rfl)
  have hhlenLeft : hlenLeft = hlenKMN := Subsingleton.elim _ _
  have hhlenRight : hlenRight = hlenKMN := Subsingleton.elim _ _
  have hγLeft : γN (symbol z ⊗ₜ symbol nLeft) = symbol sourceLeft := by
    rw [hhlenLeft] at hspecLeft
    calc
      _ = symbol ⟨fun a => Fin.append (fun b => iK (z.1 b)) tailLeft
            (Fin.cast hlenKMN a), hadmLeft⟩ := hspecLeft
      _ = symbol sourceLeft := by
        congr 1
        exact Subtype.ext hdecompLeft.symm
  have hγRight : γN (symbol z ⊗ₜ symbol nRight) = symbol sourceRight := by
    rw [hhlenRight] at hspecRight
    calc
      _ = symbol ⟨fun a => Fin.append (fun b => iK (z.1 b)) tailRight
            (Fin.cast hlenKMN a), hadmRight⟩ := hspecRight
      _ = symbol sourceRight := by
        congr 1
        exact Subtype.ext hdecompRight.symm
  rw [← hγLeft, ← hγRight] at hsrcEq'
  have htensor : symbol z ⊗ₜ[IsLocalRing.ResidueField R] symbol nLeft =
      (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R A * moduleLength R B)) *
        (periodicDeterminant φ ψ hφψ hψφ hM :
          IsLocalRing.ResidueField R)) •
        (symbol z ⊗ₜ[IsLocalRing.ResidueField R] symbol nRight) := by
    apply hγNbij.1
    rw [map_smul]
    exact hsrcEq'
  have hsourceQuotientRelation : symbol nLeft =
      (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R A * moduleLength R B)) *
        (periodicDeterminant φ ψ hφψ hψφ hM :
          IsLocalRing.ResidueField R)) • symbol nRight := by
    let : FiniteDimensional (IsLocalRing.ResidueField R) (determinant R K) :=
      FiniteDimensional.of_finrank_eq_succ (finrank_determinant_eq_one hK)
    apply tensor_left_injective_of_finrank_one
      (finrank_determinant_eq_one hK) (symbol z) hz
    simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using htensor
  have hlenSourceAB : moduleLength R M =
      moduleLength R (LinearMap.range φ) + moduleLength R (LinearMap.range ψ) := by
    simpa [A, B] using hsrcLlen
  have hlenA : moduleLength R (LinearMap.range φ) =
      moduleLength R K + moduleLength R Tφ := by
    simpa [A, K] using hlenφ
  have hlenB : moduleLength R (LinearMap.range ψ) =
      moduleLength R K + moduleLength R Tψ := by
    simpa [B, K] using hlenψ
  have hlenAsrc : moduleLength R A = moduleLength R K + moduleLength R Tφ := by
    simpa [A, K] using hlenA
  have hlenBsrc : moduleLength R B = moduleLength R K + moduleLength R Tψ := by
    simpa [B, K] using hlenB
  have hlenA'K : moduleLength R A' = moduleLength R Tφ + moduleLength R K := by
    calc
      _ = moduleLength R Tφ + moduleLength R Q := hlenA'
      _ = _ := by rw [← hlenKQ]
  have hlenN : moduleLength R (LinearMap.range α) =
      moduleLength R Tφ + (moduleLength R K + moduleLength R Tψ) := by omega
  have hlenNRight : moduleLength R (LinearMap.range α) =
      moduleLength R Tψ + (moduleLength R K + moduleLength R Tφ) := by omega
  have htailLeftDecomp : tailLeft =
      Fin.append (fun i ↦ (liftφ i : M)) (Fin.append zψpre tailPreψ) ∘
        Fin.cast hlenN := by
    funext i
    let q := Fin.cast hlenN i
    have hq : Fin.cast hlenN.symm q = i := by simp [q]
    rw [← hq]
    refine Fin.addCases ?_ ?_ q
    · intro i
      have hidx : Fin.cast hsrcLlen
          (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K)
            (Fin.cast hlenN.symm (Fin.castAdd
              (moduleLength R K + moduleLength R Tψ) i)))) =
          Fin.castAdd (moduleLength R B)
            (Fin.cast hlenφ.symm (Fin.natAdd (moduleLength R K) i)) := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
      simp only [tailLeft, sourceLeft, Function.comp_apply]
      rw [hidx]
      simp [x, yLift, iKφ, K, Fin.append_left, Fin.append_right]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        have hidx : Fin.cast hsrcLlen
            (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K)
              (Fin.cast hlenN.symm (Fin.natAdd (moduleLength R Tφ)
                (Fin.castAdd (moduleLength R Tψ) i))))) =
            Fin.natAdd (moduleLength R A)
              (Fin.cast hlenψ.symm (Fin.castAdd (moduleLength R Tψ) i)) := by
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
          omega
        simp only [tailLeft, sourceLeft, Function.comp_apply]
        rw [hidx]
        simp [x, yLift, iKφ, K, Fin.append_left, Fin.append_right]
      · intro i
        have hidx : Fin.cast hsrcLlen
            (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K)
              (Fin.cast hlenN.symm (Fin.natAdd (moduleLength R Tφ)
                (Fin.natAdd (moduleLength R K) i))))) =
            Fin.natAdd (moduleLength R A)
              (Fin.cast hlenψ.symm (Fin.natAdd (moduleLength R K) i)) := by
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_natAdd]
          omega
        simp only [tailLeft, sourceLeft, Function.comp_apply]
        rw [hidx]
        simp [x, yLift, iKφ, K, Fin.append_right]
  have htailRightDecomp : tailRight =
      Fin.append (fun i ↦ (liftψ i : M)) (Fin.append zφpre tailPreφ) ∘
        Fin.cast hlenNRight := by
    funext i
    let q := Fin.cast hlenNRight i
    have hq : Fin.cast hlenNRight.symm q = i := by simp [q]
    rw [← hq]
    refine Fin.addCases ?_ ?_ q
    · intro i
      have hidx : Fin.cast hsrcRlen
          (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K)
            (Fin.cast hlenNRight.symm (Fin.castAdd
              (moduleLength R K + moduleLength R Tφ) i)))) =
          Fin.castAdd (moduleLength R A)
            (Fin.cast hlenψ.symm (Fin.natAdd (moduleLength R K) i)) := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
      simp only [tailRight, sourceRight, Function.comp_apply]
      rw [hidx]
      simp [y, xLift, iKψ, K, Fin.append_left, Fin.append_right]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        have hidx : Fin.cast hsrcRlen
            (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K)
              (Fin.cast hlenNRight.symm (Fin.natAdd (moduleLength R Tψ)
                (Fin.castAdd (moduleLength R Tφ) i))))) =
            Fin.natAdd (moduleLength R B)
              (Fin.cast hlenφ.symm (Fin.castAdd (moduleLength R Tφ) i)) := by
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
          omega
        simp only [tailRight, sourceRight, Function.comp_apply]
        rw [hidx]
        simp [y, xLift, iKψ, K, Fin.append_left, Fin.append_right]
      · intro i
        have hidx : Fin.cast hsrcRlen
            (Fin.cast hlenKMN.symm (Fin.natAdd (moduleLength R K)
              (Fin.cast hlenNRight.symm (Fin.natAdd (moduleLength R Tψ)
                (Fin.natAdd (moduleLength R K) i))))) =
            Fin.natAdd (moduleLength R B)
              (Fin.cast hlenφ.symm (Fin.natAdd (moduleLength R K) i)) := by
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_natAdd]
          omega
        simp only [tailRight, sourceRight, Function.comp_apply]
        rw [hidx]
        simp [y, xLift, iKψ, K, Fin.append_right]
  let iN : LinearMap.range α →ₗ[R] M' := (LinearMap.range α).subtype
  let qQ : M' →ₗ[R] Q := (LinearMap.range α).mkQ
  have hiN : Function.Injective iN := (LinearMap.range α).subtype_injective
  have hqQ : Function.Surjective qQ := Submodule.mkQ_surjective (LinearMap.range α)
  have hexNQ : Function.Exact iN qQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  let γQ := determinantExactSequenceMap iN qQ hiN hqQ hexNQ hN hM' hQ
  have hγQbij : Function.Bijective γQ :=
    determinantExactSequenceMap_bijective iN qQ hiN hqQ hexNQ hN hM' hQ
  have hwφ0 : symbol wφ ≠ 0 := symbol_ne_zero_of_span_top hQ wφ hwφspan
  have hwψ0 : symbol wψ ≠ 0 := symbol_ne_zero_of_span_top hQ wψ hwψspan
  obtain ⟨hlenTargetLeft, hadmTargetLeft, hspecTargetLeft⟩ :=
    (determinantExactSequenceMap_spec iN qQ hiN hqQ hexNQ hN hM' hQ) nLeft wψ hnLeft0 hwψ0
      wrepψ (by intro j; exact hwrepψ j)
  obtain ⟨hlenTargetRight, hadmTargetRight, hspecTargetRight⟩ :=
    (determinantExactSequenceMap_spec iN qQ hiN hqQ hexNQ hN hM' hQ) nRight wφ hnRight0 hwφ0
      wrepφ (by intro j; exact hwrepφ j)
  let targetLeft : AdmissibleSequence R M' :=
    ⟨fun a ↦ Fin.append (fun b ↦ (x'.1 b : M')) yLift' (Fin.cast htgtLlen a), htgtLadm⟩
  let targetRight : AdmissibleSequence R M' :=
    ⟨fun a ↦ Fin.append (fun b ↦ (y'.1 b : M')) xLift' (Fin.cast htgtRlen a), htgtRadm⟩
  have htargetLeftEq : symbol
      ⟨fun a ↦ Fin.append (fun b ↦ iN (nLeft.1 b)) wrepψ
        (Fin.cast hlenTargetLeft a), hadmTargetLeft⟩ = symbol targetLeft := by
    apply congrArg symbol
    apply Subtype.ext
    funext a
    change Fin.append (fun b ↦ α (tailLeft b)) wrepψ (Fin.cast hlenTargetLeft a) =
      Fin.append (fun b ↦ (x'.1 b : M')) yLift' (Fin.cast htgtLlen a)
    rw [htailLeftDecomp]
    let q := Fin.cast hlenTargetLeft a
    have hq : Fin.cast hlenTargetLeft.symm q = a := by simp [q]
    rw [← hq]
    refine Fin.addCases ?_ ?_ q
    · intro i
      let qN := Fin.cast hlenN i
      have hqN : Fin.cast hlenN.symm qN = i := by simp [qN]
      rw [← hqN]
      refine Fin.addCases ?_ ?_ qN
      · intro i
        let idxN := Fin.cast hlenN.symm (Fin.castAdd
          (moduleLength R K + moduleLength R Tψ) i)
        let idxS := Fin.castAdd (moduleLength R Q) idxN
        have hidx : Fin.cast htgtLlen (Fin.cast hlenTargetLeft.symm idxS) =
            Fin.castAdd (moduleLength R B')
              (Fin.cast hlenA'.symm (Fin.castAdd (moduleLength R Q) i)) := by
          apply Fin.ext
          simp [idxN, idxS]
        rw [hidx]
        simp [x', liftQφ, yLift', Fin.append_left, hαliftφ]
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro i
          let idxN := Fin.cast hlenN.symm
            (Fin.natAdd (moduleLength R Tφ) (Fin.castAdd (moduleLength R Tψ) i))
          let idxS := Fin.castAdd (moduleLength R Q) idxN
          have hidx : Fin.cast htgtLlen (Fin.cast hlenTargetLeft.symm idxS) =
              Fin.castAdd (moduleLength R B')
                (Fin.cast hlenA'.symm
                  (Fin.natAdd (moduleLength R Tφ) (Fin.cast hlenKQ i))) := by
            apply Fin.ext
            simp [idxN, idxS]
          rw [hidx]
          simp [x', liftQφ, yLift', hαzψpre, Fin.append_left, Fin.append_right]
        · intro i
          let idxN := Fin.cast hlenN.symm
            (Fin.natAdd (moduleLength R Tφ) (Fin.natAdd (moduleLength R K) i))
          let idxS := Fin.castAdd (moduleLength R Q) idxN
          have hidx : Fin.cast htgtLlen (Fin.cast hlenTargetLeft.symm idxS) =
              Fin.natAdd (moduleLength R A')
                (Fin.cast hlenB'.symm (Fin.castAdd (moduleLength R Q) i)) := by
            apply Fin.ext
            simp [idxN, idxS]
            omega
          rw [hidx]
          simp [x', liftQφ, yLift', Fin.append_left, Fin.append_right]
    · intro i
      let idxS := Fin.natAdd (moduleLength R (LinearMap.range α)) i
      have hidx : Fin.cast htgtLlen (Fin.cast hlenTargetLeft.symm idxS) =
          Fin.natAdd (moduleLength R A')
            (Fin.cast hlenB'.symm (Fin.natAdd (moduleLength R Tψ) i)) := by
        apply Fin.ext
        simp [idxS]
        omega
      rw [hidx]
      simp [x', liftQφ, yLift', Fin.append_right]
  have htargetRightEq : symbol
      ⟨fun a ↦ Fin.append (fun b ↦ iN (nRight.1 b)) wrepφ
        (Fin.cast hlenTargetRight a), hadmTargetRight⟩ = symbol targetRight := by
    apply congrArg symbol
    apply Subtype.ext
    funext a
    change Fin.append (fun b ↦ α (tailRight b)) wrepφ (Fin.cast hlenTargetRight a) =
      Fin.append (fun b ↦ (y'.1 b : M')) xLift' (Fin.cast htgtRlen a)
    rw [htailRightDecomp]
    let q := Fin.cast hlenTargetRight a
    have hq : Fin.cast hlenTargetRight.symm q = a := by simp [q]
    rw [← hq]
    refine Fin.addCases ?_ ?_ q
    · intro i
      let qN := Fin.cast hlenNRight i
      have hqN : Fin.cast hlenNRight.symm qN = i := by simp [qN]
      rw [← hqN]
      refine Fin.addCases ?_ ?_ qN
      · intro i
        let idxN := Fin.cast hlenNRight.symm (Fin.castAdd
          (moduleLength R K + moduleLength R Tφ) i)
        let idxS := Fin.castAdd (moduleLength R Q) idxN
        have hidx : Fin.cast htgtRlen (Fin.cast hlenTargetRight.symm idxS) =
            Fin.castAdd (moduleLength R A')
              (Fin.cast hlenB'.symm (Fin.castAdd (moduleLength R Q) i)) := by
          apply Fin.ext
          simp [idxN, idxS]
        rw [hidx]
        simp [y', liftQψ, xLift', Fin.append_left, hαliftψ]
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro i
          let idxN := Fin.cast hlenNRight.symm
            (Fin.natAdd (moduleLength R Tψ) (Fin.castAdd (moduleLength R Tφ) i))
          let idxS := Fin.castAdd (moduleLength R Q) idxN
          have hidx : Fin.cast htgtRlen (Fin.cast hlenTargetRight.symm idxS) =
              Fin.castAdd (moduleLength R A')
                (Fin.cast hlenB'.symm
                  (Fin.natAdd (moduleLength R Tψ) (Fin.cast hlenKQ i))) := by
            apply Fin.ext
            simp [idxN, idxS]
          rw [hidx]
          simp [y', liftQψ, xLift', hαzφpre, Fin.append_left, Fin.append_right]
        · intro i
          let idxN := Fin.cast hlenNRight.symm
            (Fin.natAdd (moduleLength R Tψ) (Fin.natAdd (moduleLength R K) i))
          let idxS := Fin.castAdd (moduleLength R Q) idxN
          have hidx : Fin.cast htgtRlen (Fin.cast hlenTargetRight.symm idxS) =
              Fin.natAdd (moduleLength R B')
                (Fin.cast hlenA'.symm (Fin.castAdd (moduleLength R Q) i)) := by
            apply Fin.ext
            simp [idxN, idxS]
            omega
          rw [hidx]
          simp [y', liftQψ, xLift', Fin.append_left, Fin.append_right]
    · intro i
      let idxS := Fin.natAdd (moduleLength R (LinearMap.range α)) i
      have hidx : Fin.cast htgtRlen (Fin.cast hlenTargetRight.symm idxS) =
          Fin.natAdd (moduleLength R B')
            (Fin.cast hlenA'.symm (Fin.natAdd (moduleLength R Tφ) i)) := by
        apply Fin.ext
        simp [idxS]
        omega
      rw [hidx]
      simp [y', liftQψ, xLift', Fin.append_right]
  have htargetGammaRel :
      γQ (symbol nLeft ⊗ₜ symbol wψ) =
        (((-1 : IsLocalRing.ResidueField R) ^
          (moduleLength R A' * moduleLength R B')) *
          (periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM' :
            IsLocalRing.ResidueField R)) •
          γQ (symbol nRight ⊗ₜ symbol wφ) := by
    calc
      _ = symbol ⟨fun a ↦ Fin.append (fun b ↦ iN (nLeft.1 b)) wrepψ
            (Fin.cast hlenTargetLeft a), hadmTargetLeft⟩ := hspecTargetLeft
      _ = symbol targetLeft := htargetLeftEq
      _ = (((-1 : IsLocalRing.ResidueField R) ^
          (moduleLength R A' * moduleLength R B')) *
          (periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM' :
            IsLocalRing.ResidueField R)) • symbol targetRight := htgtEq
      _ = _ := by rw [← htargetRightEq, ← hspecTargetRight]
  have htargetTensorRel : symbol nLeft ⊗ₜ[IsLocalRing.ResidueField R] symbol wψ =
        (((-1 : IsLocalRing.ResidueField R) ^
          (moduleLength R A' * moduleLength R B')) *
          (periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM' :
            IsLocalRing.ResidueField R)) •
          (symbol nRight ⊗ₜ[IsLocalRing.ResidueField R] symbol wφ) := by
    apply hγQbij.1
    rw [map_smul]
    exact htargetGammaRel
  let κ := IsLocalRing.ResidueField R
  let D := periodicDeterminant φ ψ hφψ hψφ hM
  let D' := periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM'
  let c : κ := ((-1 : κ) ^ (moduleLength R A * moduleLength R B)) * (D : κ)
  let c' : κ := ((-1 : κ) ^ (moduleLength R A' * moduleLength R B')) * (D' : κ)
  have hsourceC : symbol nLeft = c • symbol nRight := by
    simpa [c, D] using hsourceQuotientRelation
  have hfactorTensor : c • (symbol nRight ⊗ₜ[κ] symbol wψ) =
      c' • (symbol nRight ⊗ₜ[κ] symbol wφ) := by
    calc
      _ = symbol nLeft ⊗ₜ[κ] symbol wψ := by
        rw [hsourceC]
        simp only [TensorProduct.smul_tmul']
      _ = _ := htargetTensorRel
  let : FiniteDimensional κ (determinant R (LinearMap.range α)) :=
    FiniteDimensional.of_finrank_eq_succ (finrank_determinant_eq_one hN)
  have hfactor : c • symbol wψ = c' • symbol wφ := by
    apply (tensor_left_injective_of_finrank_one
      (finrank_determinant_eq_one hN) (symbol nRight) hnRight0)
    simpa only [TensorProduct.tmul_smul] using hfactorTensor
  have hc' : c' ≠ 0 := by simp [c', D']
  have hratio : symbol wφ = (c'⁻¹ * c) • symbol wψ := by
    calc
      symbol wφ = c'⁻¹ • (c' • symbol wφ) := by rw [inv_smul_smul₀ hc']
      _ = c'⁻¹ • (c • symbol wψ) := by rw [← hfactor]
      _ = (c'⁻¹ * c) • symbol wψ := by rw [smul_smul]
  let f := e1.trans e0.symm
  let O : FiniteLengthModuleIso.{u, w} R := ⟨⟨ModuleCat.of R Q, hQ⟩⟩
  let fMor : O ⟶ O := ⟨ObjectProperty.isoMk _ f.toModuleIso⟩
  let F := determinantFunctor.{u, w} R
  have hmapSymbol := determinantFunctor_map_apply_symbol O fMor wψ
  have hmappedSeq :
      (⟨fun i ↦ fMor.iso.hom.hom.hom (wψ.1 (Fin.cast (F.map_length fMor).symm i)),
        F.map_admissible fMor wψ⟩ : AdmissibleSequence R Q) = wφ := by
    apply Subtype.ext
    funext i
    have hlen : F.map_length fMor =
        (rfl : moduleLength R Q = moduleLength R Q) := Subsingleton.elim _ _
    simp [fMor, f, wφ, wψ]
  have hdetMap : (determinantAutomorphism f hQ : κ) • symbol wψ = symbol wφ :=
    hmapSymbol.trans (congrArg symbol hmappedSeq)
  have hdetScalar : (determinantAutomorphism f hQ : κ) = c'⁻¹ * c := by
    have hsmul : ((determinantAutomorphism f hQ : κ) - c'⁻¹ * c) • symbol wψ = 0 := by
      rw [sub_smul, hdetMap, hratio, sub_self]
    have hcoeff : (determinantAutomorphism f hQ : κ) - c'⁻¹ * c = 0 :=
      (smul_eq_zero.mp hsmul).resolve_right hwψ0
    exact sub_eq_zero.mp hcoeff
  have hlenB'K : moduleLength R B' = moduleLength R Tψ + moduleLength R K := by
    calc
      _ = moduleLength R Tψ + moduleLength R Q := hlenB'
      _ = _ := by rw [← hlenKQ]
  have hlenAB : moduleLength R A * moduleLength R B =
      moduleLength R A' * moduleLength R B' := by
    rw [hlenAsrc, hlenBsrc, hlenA'K, hlenB'K]
    ring
  have hsign : ((-1 : κ) ^ (moduleLength R A' * moduleLength R B')) ≠ 0 := by simp
  have hcRatio : c'⁻¹ * c = (D' : κ)⁻¹ * (D : κ) := by
    change (((-1 : κ) ^ (moduleLength R A' * moduleLength R B')) * (D' : κ))⁻¹ *
      (((-1 : κ) ^ (moduleLength R A * moduleLength R B)) * (D : κ)) =
        (D' : κ)⁻¹ * (D : κ)
    rw [hlenAB, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hsign, one_mul]
  apply Units.ext
  change (D : κ) = (determinantAutomorphism f hQ : κ) * (D' : κ)
  rw [hdetScalar, hcRatio]
  field_simp

end AlgebraicGeometry
