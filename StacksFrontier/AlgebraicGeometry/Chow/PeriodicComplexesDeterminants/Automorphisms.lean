module

public import Mathlib.LinearAlgebra.Determinant
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Functor
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DeterminantLine

/-!
# The periodic determinant when one differential is zero

For an automorphism of a finite-length module over a local ring, the periodic determinant with
the other differential zero is its determinant, or its inverse.

## Main definitions

* `AlgebraicGeometry.determinantAutomorphism` is the residue-field determinant of a
  finite-length module automorphism, induced by the determinant functor.

## Main results

* `AlgebraicGeometry.periodicDeterminant_equiv_zero` computes the periodic determinant of an
  automorphism followed by zero.
* `AlgebraicGeometry.periodicDeterminant_zero_equiv` computes the periodic determinant of zero
  followed by an automorphism.

## Implementation notes

The source's `det_κ(φ)` is the determinant of the automorphism induced by the determinant
functor on its one-dimensional residue-field vector space. The two source conclusions are
separate lemmas.

## References

* [Stacks Project, Tag 02PN](https://stacks.math.columbia.edu/tag/02PN)
-/

@[expose] public section

noncomputable section

open CategoryTheory

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- Two linear maps out of a tensor product agree as soon as they agree on the tensor of a
generator of each factor. -/
private lemma tensorMap_eq_of_generators
    {K A B C : Type*} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C]
    (a : A) (b : B) (ha : K ∙ a = ⊤) (hb : K ∙ b = ⊤)
    (f g : A ⊗[K] B →ₗ[K] C)
    (hfg : f (a ⊗ₜ[K] b) = g (a ⊗ₜ[K] b)) : f = g := by
  apply TensorProduct.ext
  ext x y
  obtain ⟨r, rfl⟩ := (Submodule.mem_span_singleton.mp
    (ha ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule K A))))
  obtain ⟨s, rfl⟩ := (Submodule.mem_span_singleton.mp
    (hb ▸ (Submodule.mem_top : y ∈ (⊤ : Submodule K B))))
  simp only [map_smul]
  show s • (r • f (a ⊗ₜ[K] b)) = s • (r • g (a ⊗ₜ[K] b))
  rw [hfg]

/-- The image of the zero endomorphism is a subsingleton. -/
private lemma subsingleton_range_zero
    {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] :
    Subsingleton (LinearMap.range (0 : M →ₗ[R] M)) := by
  rw [LinearMap.range_zero]
  infer_instance

/-- The image of the zero endomorphism has length zero. -/
private lemma moduleLength_range_zero
    {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] :
    moduleLength R (LinearMap.range (0 : M →ₗ[R] M)) = 0 := by
  have := subsingleton_range_zero (R := R) (M := M)
  unfold moduleLength
  rw [Module.length_eq_zero]
  rfl

/-- The zero map followed by an automorphism is exact. -/
private lemma exact_zero_equiv {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] M) : Function.Exact (0 : M →ₗ[R] M) (e : M →ₗ[R] M) := by
  rw [LinearMap.exact_iff, LinearMap.ker_eq_bot.mpr e.injective, LinearMap.range_zero]

/-- An automorphism followed by the zero map is exact. -/
private lemma exact_equiv_zero {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] M) : Function.Exact (e : M →ₗ[R] M) (0 : M →ₗ[R] M) := by
  rw [LinearMap.exact_iff, LinearMap.ker_zero, LinearMap.range_eq_top.mpr e.surjective]

/-- For an automorphism `e` and the zero map, the two determinant maps of the associated short
exact sequences differ by the determinant functor applied to `e`. -/
private theorem periodicGamma_compare_equiv_zero
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] M)
    (hM : IsFiniteLength R M)
    (h0e : Function.Exact (0 : M →ₗ[R] M) (e : M →ₗ[R] M))
    (he0 : Function.Exact (e : M →ₗ[R] M) 0) :
    (periodicGamma (0 : M →ₗ[R] M) e he0 hM).comp
      (TensorProduct.comm (IsLocalRing.ResidueField R)
        (determinant R (LinearMap.range (0 : M →ₗ[R] M)))
        (determinant R (LinearMap.range (e : M →ₗ[R] M)))).toLinearMap =
      ((determinantFunctor.{u, v} R).mapLinearEquiv
        (M := ⟨⟨ModuleCat.of R M, hM⟩⟩)
        (N := ⟨⟨ModuleCat.of R M, hM⟩⟩)
        ⟨ObjectProperty.isoMk _ e.toModuleIso⟩).toLinearMap.comp
        (periodicGamma (e : M →ₗ[R] M) 0 h0e hM) := by
  classical
  let K := IsLocalRing.ResidueField R
  let Z := LinearMap.range (0 : M →ₗ[R] M)
  let E := LinearMap.range (e : M →ₗ[R] M)
  have hZ : IsFiniteLength R Z := hM.of_injective (Submodule.injective_subtype Z)
  have hE : IsFiniteLength R E := hM.of_injective (Submodule.injective_subtype E)
  have : Subsingleton Z := subsingleton_range_zero
  have hnZ : moduleLength R Z = 0 := moduleLength_range_zero

  let zseq : AdmissibleSequence R Z :=
    ⟨fun i => Fin.elim0 (hnZ ▸ i), fun i _ _ ↦ Fin.elim0 (hnZ ▸ i)⟩
  have hzspan : Submodule.span R (Set.range zseq.1) = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  have hzgen := span_symbol_eq_top hZ zseq hzspan
  have hzne : symbol zseq ≠ 0 := symbol_ne_zero_of_span_top hZ zseq hzspan
  obtain ⟨xseq, hxne⟩ := exists_nonzero_symbol hM
  have herange : Function.Bijective (e.rangeRestrict : M →ₗ[R] E) := by
    constructor
    · exact fun x y hxy ↦ e.injective (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
      exact ⟨x, Subtype.ext hx⟩
  let er : M ≃ₗ[R] E := LinearEquiv.ofBijective e.rangeRestrict herange
  let mObj : FiniteLengthModuleIso.{u, v} R := ⟨⟨ModuleCat.of R M, hM⟩⟩
  let eObj : FiniteLengthModuleIso.{u, v} R := ⟨⟨ModuleCat.of R E, hE⟩⟩
  let erMor : mObj ⟶ eObj := ⟨ObjectProperty.isoMk _ er.toModuleIso⟩
  let eMor : mObj ⟶ mObj := ⟨ObjectProperty.isoMk _ e.toModuleIso⟩
  let DF := determinantFunctor.{u, v} R
  let yseq : AdmissibleSequence R E :=
    ⟨fun i => erMor.iso.hom.hom.hom
        (xseq.1 (Fin.cast (DF.map_length erMor).symm i)),
      DF.map_admissible erMor xseq⟩
  let eseq : AdmissibleSequence R M :=
    ⟨fun i => eMor.iso.hom.hom.hom
        (xseq.1 (Fin.cast (DF.map_length eMor).symm i)),
      DF.map_admissible eMor xseq⟩
  have hmapY := DF.map_symbol erMor xseq
  have hyne : symbol yseq ≠ 0 := by
    intro hy
    apply hxne
    apply (DF.mapLinearEquiv erMor).injective
    calc
      (DF.mapLinearEquiv erMor) (symbol xseq) = symbol yseq := hmapY
      _ = 0 := hy
      _ = (DF.mapLinearEquiv erMor) 0 := by simp
  have hyspan := span_eq_top_of_symbol_ne_zero hE yseq hyne
  have hygen := span_symbol_eq_top hE yseq hyspan
  have hmapE := DF.map_symbol eMor xseq
  let F := DF.mapLinearEquiv eMor
  let lift : Fin (moduleLength R E) → M := fun i =>
    xseq.1 (Fin.cast (DF.map_length erMor).symm i)
  have hlift : ∀ i, e.rangeRestrict (lift i) = yseq.1 i := fun _ ↦ rfl
  let i10 := Z.subtype
  let p10 := e.rangeRestrict
  have hi10 : Function.Injective i10 := Submodule.injective_subtype Z
  have hp10 : Function.Surjective (e.rangeRestrict : M →ₗ[R] E) :=
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict (e : M →ₗ[R] M))
  have hip10 : Function.Exact i10 p10 := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    exact h0e.linearMap_ker_eq
  let i01 := E.subtype
  let p01 := (0 : M →ₗ[R] M).rangeRestrict
  have hi01 : Function.Injective i01 := Submodule.injective_subtype E
  have hp01 : Function.Surjective p01 :=
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict (0 : M →ₗ[R] M))
  have hip01 : Function.Exact i01 p01 := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    exact he0.linearMap_ker_eq
  have h10 := determinantExactSequenceMap_spec i10 p10 hi10 hp10 hip10 hZ hM hE
  have h01 := determinantExactSequenceMap_spec i01 p01 hi01 hp01 hip01 hE hM hZ
  obtain ⟨hlen10, hadm10, hval10⟩ := h10 zseq yseq hzne hyne lift hlift
  have hseq10 :
      (⟨fun a ↦ Fin.append (fun b ↦ i10 (zseq.1 b)) lift (Fin.cast hlen10 a),
        hadm10⟩ : AdmissibleSequence R M) = xseq := by
    apply Subtype.ext
    funext a
    show Fin.append (fun b ↦ i10 (zseq.1 b)) lift (Fin.cast hlen10 a) = xseq.1 a
    rw [Fin.append_left_nil _ _ hnZ]
    simp [lift]
  obtain ⟨hlen01, hadm01, hval01⟩ := h01 yseq zseq hyne hzne
    (fun i => Fin.elim0 (hnZ ▸ i)) (by intro i; exact Fin.elim0 (hnZ ▸ i))
  have hseq01 :
      (⟨fun a ↦ Fin.append (fun b ↦ i01 (yseq.1 b))
          (fun i => Fin.elim0 (hnZ ▸ i)) (Fin.cast hlen01 a), hadm01⟩ :
        AdmissibleSequence R M) = eseq := by
    apply Subtype.ext
    funext a
    show Fin.append (fun b ↦ i01 (yseq.1 b))
        (fun i => Fin.elim0 (hnZ ▸ i)) (Fin.cast hlen01 a) = eseq.1 a
    rw [Fin.append_right_nil _ _ hnZ]
    rfl
  have hgen :
      (periodicGamma (0 : M →ₗ[R] M) e he0 hM).comp
          (TensorProduct.comm K (determinant R Z) (determinant R E)).toLinearMap
          (symbol zseq ⊗ₜ[K] symbol yseq) =
        F ((periodicGamma (e : M →ₗ[R] M) 0 h0e hM)
          (symbol zseq ⊗ₜ[K] symbol yseq)) := by
    show determinantExactSequenceMap i01 p01 hi01 hp01 hip01 hE hM hZ
          (symbol yseq ⊗ₜ[K] symbol zseq) =
      F (determinantExactSequenceMap i10 p10 hi10 hp10 hip10 hZ hM hE
          (symbol zseq ⊗ₜ[K] symbol yseq))
    rw [hval01, hseq01, hval10, hseq10, hmapE]
  exact tensorMap_eq_of_generators (symbol zseq) (symbol yseq) hzgen hygen _ _ hgen

/-- The determinant over the residue field of an automorphism of a finite-length module, via
the determinant functor. -/
noncomputable def determinantAutomorphism
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] M)
    (hM : IsFiniteLength R M) : (IsLocalRing.ResidueField R)ˣ :=
  LinearEquiv.det ((determinantFunctor.{u, v} R).mapLinearEquiv
    (M := ⟨⟨ModuleCat.of R M, hM⟩⟩)
    (N := ⟨⟨ModuleCat.of R M, hM⟩⟩)
    ⟨ObjectProperty.isoMk _ e.toModuleIso⟩)

/-- **Stacks Project, Tag 02PN, part (1).** The periodic determinant of an automorphism and
zero is the determinant of the automorphism. -/
@[stacks 02PN "part (1)"]
theorem periodicDeterminant_equiv_zero
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] M)
    (hM : IsFiniteLength R M) :
    periodicDeterminant (e : M →ₗ[R] M) 0
      (by rw [LinearMap.exact_iff]; simp [LinearMap.range_eq_top.mpr e.surjective])
      (by rw [LinearMap.exact_iff]; simp [LinearMap.ker_eq_bot.mpr e.injective])
      hM = determinantAutomorphism e hM := by
  classical
  have h0e := exact_zero_equiv e
  have he0 := exact_equiv_zero e
  let K := IsLocalRing.ResidueField R
  let DF := determinantFunctor.{u, v} R
  let mObj : FiniteLengthModuleIso.{u, v} R := ⟨⟨ModuleCat.of R M, hM⟩⟩
  let eMor : mObj ⟶ mObj := ⟨ObjectProperty.isoMk _ e.toModuleIso⟩
  let F := DF.mapLinearEquiv eMor
  have hdim := finrank_determinant_eq_one hM
  have hF := linearEquiv_eq_det_smul_id hdim F
  have hbridge := periodicGamma_compare_equiv_zero e hM h0e he0
  have hlen0 := moduleLength_range_zero (R := R) (M := M)
  have hExp :
      moduleLength R (LinearMap.range (e : M →ₗ[R] M)) *
        moduleLength R (LinearMap.range (0 : M →ₗ[R] M)) = 0 := by
    rw [hlen0]
    simp
  have hcomp :
      F.toLinearMap.comp (periodicGamma (e : M →ₗ[R] M) 0 h0e hM) =
        (determinantAutomorphism e hM : K) •
          periodicGamma (e : M →ₗ[R] M) 0 h0e hM := by
    rw [hF]
    have hd : (F.det : K) = (determinantAutomorphism e hM : K) := by
      simp [determinantAutomorphism, F, eMor, DF, mObj]
    rw [hd]
    ext x
    simp
  have hspec : IsPeriodicDeterminant
      (e : M →ₗ[R] M) 0 he0 h0e hM (determinantAutomorphism e hM) := by
    show (periodicGamma (0 : M →ₗ[R] M) e he0 hM).comp
        (TensorProduct.comm K
          (determinant R (LinearMap.range (0 : M →ₗ[R] M)))
          (determinant R (LinearMap.range (e : M →ₗ[R] M)))).toLinearMap =
      (((-1 : K) ^
          (moduleLength R (LinearMap.range (e : M →ₗ[R] M)) *
            moduleLength R (LinearMap.range (0 : M →ₗ[R] M)))) *
        (determinantAutomorphism e hM : K)) •
        periodicGamma (e : M →ₗ[R] M) 0 h0e hM
    calc
      _ = F.toLinearMap.comp
          (periodicGamma (e : M →ₗ[R] M) 0 h0e hM) := hbridge
      _ = (determinantAutomorphism e hM : K) •
          periodicGamma (e : M →ₗ[R] M) 0 h0e hM := hcomp
      _ = _ := by rw [hExp]; simp
  symm
  exact eq_periodicDeterminant (e : M →ₗ[R] M) 0 he0 h0e hM hspec

/-- **Stacks Project, Tag 02PN, part (2).** The periodic determinant of zero and an
automorphism is the inverse of its determinant. -/
@[stacks 02PN "part (2)"]
theorem periodicDeterminant_zero_equiv
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] M)
    (hM : IsFiniteLength R M) :
    periodicDeterminant 0 (e : M →ₗ[R] M)
      (by rw [LinearMap.exact_iff]; simp [LinearMap.ker_eq_bot.mpr e.injective])
      (by rw [LinearMap.exact_iff]; simp [LinearMap.range_eq_top.mpr e.surjective])
      hM = (determinantAutomorphism e hM)⁻¹ := by
  classical
  have h0e := exact_zero_equiv e
  have he0 := exact_equiv_zero e
  let K := IsLocalRing.ResidueField R
  let DF := determinantFunctor.{u, v} R
  let mObj : FiniteLengthModuleIso.{u, v} R := ⟨⟨ModuleCat.of R M, hM⟩⟩
  let eMor : mObj ⟶ mObj := ⟨ObjectProperty.isoMk _ e.toModuleIso⟩
  let F := DF.mapLinearEquiv eMor
  let A := determinant R (LinearMap.range (0 : M →ₗ[R] M))
  let B := determinant R (LinearMap.range (e : M →ₗ[R] M))
  let gamma01 := periodicGamma (0 : M →ₗ[R] M) e he0 hM
  let gamma10 := periodicGamma (e : M →ₗ[R] M) 0 h0e hM
  let commBA := (TensorProduct.comm K A B).toLinearMap
  let commAB := (TensorProduct.comm K B A).toLinearMap
  have hbridge := periodicGamma_compare_equiv_zero e hM h0e he0
  have hbridge0 : gamma01.comp commBA = F.toLinearMap.comp gamma10 := by
    simpa [gamma01, gamma10, commBA] using hbridge
  have hbridge' : gamma01 = F.toLinearMap.comp (gamma10.comp commAB) := by
    calc
      gamma01 = (gamma01.comp commBA).comp commAB := by
        rw [LinearMap.comp_assoc, TensorProduct.comm_comp_comm, LinearMap.comp_id]
      _ = (F.toLinearMap.comp gamma10).comp commAB := by rw [hbridge0]
      _ = F.toLinearMap.comp (gamma10.comp commAB) := LinearMap.comp_assoc _ _ _
  have hbridge2 : gamma10.comp commAB = F.symm.toLinearMap.comp gamma01 := by
    calc
      gamma10.comp commAB = F.symm.toLinearMap.comp
          (F.toLinearMap.comp (gamma10.comp commAB)) := by simp
      _ = F.symm.toLinearMap.comp gamma01 := by rw [hbridge']
  have hdim := finrank_determinant_eq_one hM
  have hF := linearEquiv_eq_det_smul_id hdim F.symm
  have hlen0 := moduleLength_range_zero (R := R) (M := M)
  have hExp :
      moduleLength R (LinearMap.range (0 : M →ₗ[R] M)) *
        moduleLength R (LinearMap.range (e : M →ₗ[R] M)) = 0 := by
    rw [hlen0]
    simp
  have hcomp :
      F.symm.toLinearMap.comp gamma01 =
        ((determinantAutomorphism e hM)⁻¹ : K) • gamma01 := by
    rw [hF]
    have hd : (F.symm.det : K) = ((determinantAutomorphism e hM)⁻¹ : K) := by
      simp [determinantAutomorphism, F, eMor, DF, mObj]
    rw [hd]
    ext x
    simp
  have hspec : IsPeriodicDeterminant
      0 (e : M →ₗ[R] M) h0e he0 hM ((determinantAutomorphism e hM)⁻¹) := by
    show gamma10.comp commAB =
      (((-1 : K) ^
          (moduleLength R (LinearMap.range (0 : M →ₗ[R] M)) *
            moduleLength R (LinearMap.range (e : M →ₗ[R] M)))) *
        (((determinantAutomorphism e hM)⁻¹ : Units K) : K)) • gamma01
    calc
      gamma10.comp commAB = F.symm.toLinearMap.comp gamma01 := hbridge2
      _ = ((determinantAutomorphism e hM)⁻¹ : K) • gamma01 := hcomp
      _ = _ := by rw [hExp]; simp
  symm
  exact eq_periodicDeterminant 0 (e : M →ₗ[R] M) h0e he0 hM hspec

end AlgebraicGeometry
