module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibres of a module at the closed points of the spectrum

Let `M` be a module over a commutative ring `R`. This file sets up the local data through which
Serre's splitting theorem is proved: the space of closed points of `Spec R`, the fibre
`M(x) = M / xM` of `M` at a closed point `x` together with the image `s(x)` of a section, and the
canonical quotient `V(x) = M(x) / B(x)`, where `B(x)` is the part of the fibre annihilated by
every functional coming from a global linear functional on `M`. The two facts that make `V(x)`
useful are proved here: a finite family of sections splits off a free summand on a principal
neighbourhood of `x` exactly when its images in `V(x)` are linearly independent, and prescribed
values in the canonical quotients at finitely many distinct closed points are attained
simultaneously by a single element of `M`.

## Main definitions

* `ClosedPointSpace`: the space of closed points of `Spec R`, with its induced topology.
* `ClosedPointResidueField`, `ClosedPointFiber`, `sectionAt`: the residue field at a closed point,
  the fibre of a module there, and the image of a module element in that fibre.
* `fiberFunctional`, `canonicalKernel`, `CanonicalQuotient`: the fibre functional induced by a
  global linear functional, the common kernel `B(x)` of all of them, and the canonical quotient
  `V(x) = M(x) / B(x)`.
* `SplitsAfterInverting`: a finite family of sections becomes the inclusion of a direct summand
  after inverting a single ring element.

## Main results

* `finiteDimensional_fiber`: the fibre of a finite module at a closed point is finite-dimensional
  over the residue field there.
* `canonical_exact_and_splits_iff_linearIndependent`: the sequence `0 → B(x) → M(x) → V(x) → 0` is
  short exact, and a finite family splits off a free summand near `x` exactly when its images in
  `V(x)` are linearly independent.
* `pi_canonicalQuotient_mkQ_sectionAt_surjective`: arbitrary values in the canonical quotients at
  finitely many distinct closed points are attained simultaneously by a single element of `M`.

## Implementation notes

The closed-point space is the subtype of Mathlib's `closedPoints`, so it carries the induced
topology; at such a point the corresponding prime ideal is maximal, hence its quotient ring is a
field. The submodule `xM` is represented by `x.asIdeal • ⊤`. The perpendicular subspace `B(x)` is
the infimum of the kernels of the induced fibre functionals, and "the localised family is the
inclusion of a direct summand" is represented by the existence of a linear retraction of its
linear-combination map.

Mathlib's `ResidueField` and `Fiber` are declared inside namespaces; to avoid introducing generic
root-level names of the same spelling, the two fibre abbreviations here are called
`ClosedPointResidueField` and `ClosedPointFiber`.

## References

* [Serre-projective]
* [Stacks, Tag 0GV8](https://stacks.math.columbia.edu/tag/0GV8)
* [Stacks, Tag 0GV9](https://stacks.math.columbia.edu/tag/0GV9)
* [Stacks, Tag 0GVA](https://stacks.math.columbia.edu/tag/0GVA)
-/

@[expose] public section

universe u v w

open scoped Pointwise

section ClosedPointFibres

/-- The space of closed points of the prime spectrum of `R`, with its induced topology. -/
@[stacks 0GV8]
abbrev ClosedPointSpace (R : Type u) [CommRing R] :=
  ↑(closedPoints (PrimeSpectrum R))

/-- The residue field at a closed point `x` of `Spec(R)`. -/
@[stacks 0GV8]
abbrev ClosedPointResidueField {R : Type u} [CommRing R] (x : ClosedPointSpace R) :=
  R ⧸ x.1.asIdeal

/-- The ideal of a closed point is maximal. -/
theorem ClosedPointSpace.isMaximal {R : Type u} [CommRing R] (x : ClosedPointSpace R) :
    x.1.asIdeal.IsMaximal :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal x.1).mp x.2

/-- The quotient by the ideal of a closed point is a field. -/
noncomputable instance ClosedPointResidueField.instField {R : Type u} [CommRing R]
    (x : ClosedPointSpace R) :
    Field (ClosedPointResidueField x) := by
  haveI := ClosedPointSpace.isMaximal x
  exact Ideal.Quotient.field x.1.asIdeal

/-- The fibre `M(x) = M / xM` of an `R`-module at a closed point `x`. -/
@[stacks 0GV8]
abbrev ClosedPointFiber {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : ClosedPointSpace R) :=
  M ⧸ (x.1.asIdeal • (⊤ : Submodule R M))

/-- The canonical image `s(x)` of a module element `s` in the fibre at `x`. -/
@[stacks 0GV8]
abbrev sectionAt {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (x : ClosedPointSpace R) (s : M) : ClosedPointFiber M x :=
  Submodule.Quotient.mk s

/-- The fibre of a finite module at a closed point is finite-dimensional over the
residue field at that point. -/
@[stacks 0GV8]
theorem finiteDimensional_fiber
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : ClosedPointSpace R) :
    FiniteDimensional (ClosedPointResidueField x) (ClosedPointFiber M x) :=
  inferInstance

end ClosedPointFibres

section CanonicalFibreQuotient

/-- The linear functional on the fibre at `x` induced by an `R`-linear functional
on `M`. -/
noncomputable def fiberFunctional {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : ClosedPointSpace R)
    (φ : Module.Dual R M) : Module.Dual (ClosedPointResidueField x) (ClosedPointFiber M x) :=
  let q : M →ₗ[R] ClosedPointResidueField x :=
    (Algebra.linearMap R (ClosedPointResidueField x)).comp φ
  let qbar : ClosedPointFiber M x →ₗ[R] ClosedPointResidueField x := Submodule.liftQ _ q (by
    refine Submodule.smul_le.mpr fun a ha m _ ↦ ?_
    rw [LinearMap.mem_ker, map_smul]
    change Ideal.Quotient.mk x.1.asIdeal (a * φ m) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact x.1.asIdeal.mul_mem_right (φ m) ha)
  qbar.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- Evaluation of an induced fibre functional on the image of an element of `M`. -/
@[simp]
theorem fiberFunctional_sectionAt {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : ClosedPointSpace R)
    (φ : Module.Dual R M) (m : M) :
    fiberFunctional x φ (sectionAt x m) = Ideal.Quotient.mk x.1.asIdeal (φ m) := by
  simp [fiberFunctional, sectionAt]

/-- The canonical subspace `B(x)` of the fibre: the common kernel of all fibre
functionals induced by `R`-linear maps `M → R`. -/
@[stacks 0GV9]
noncomputable def canonicalKernel {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) :
    Submodule (ClosedPointResidueField x) (ClosedPointFiber M x) :=
  ⨅ φ : Module.Dual R M, LinearMap.ker (fiberFunctional x φ)

/-- Membership in `B(x)` means vanishing under every functional induced from `M`. -/
@[simp]
theorem mem_canonicalKernel_iff {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : ClosedPointSpace R)
    (y : ClosedPointFiber M x) :
    y ∈ canonicalKernel M x ↔ ∀ φ : Module.Dual R M, fiberFunctional x φ y = 0 := by
  simp [canonicalKernel]

/-- The canonical quotient `V(x) = M(x) / B(x)`. -/
@[stacks 0GV9]
abbrev CanonicalQuotient {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) :=
  ClosedPointFiber M x ⧸ canonicalKernel M x

/-- A finite family becomes the inclusion of a direct summand after inverting `f`:
the localized linear-combination map admits a linear retraction. -/
abbrev SplitsAfterInverting {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {r : ℕ} (f : R) (s : Fin r → M) : Prop :=
  ∃ p : LocalizedModule (Submonoid.powers f) M →ₗ[Localization (Submonoid.powers f)]
      (Fin r → Localization (Submonoid.powers f)),
    p.comp (Fintype.linearCombination (Localization (Submonoid.powers f))
      (fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers f) M (s i))) = LinearMap.id

/-- Two functionals on the fibre at `x` agree if they agree on all images of elements of `M`. -/
private lemma fibre_dual_ext {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : ClosedPointSpace R)
    {f g : Module.Dual (ClosedPointResidueField x) (ClosedPointFiber M x)}
    (h : ∀ m, f (sectionAt x m) = g (sectionAt x m)) : f = g :=
  LinearMap.ext fun y ↦ Submodule.Quotient.induction_on _ y h

private lemma fiberFunctional_add {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : ClosedPointSpace R)
    (φ ψ : Module.Dual R M) :
    fiberFunctional x (φ + ψ) = fiberFunctional x φ + fiberFunctional x ψ :=
  fibre_dual_ext x fun _ ↦ by simp

private lemma fiberFunctional_smul {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : ClosedPointSpace R)
    (a : R) (φ : Module.Dual R M) :
    fiberFunctional x (a • φ) =
      Ideal.Quotient.mk x.1.asIdeal a • fiberFunctional x φ :=
  fibre_dual_ext x fun _ ↦ by simp

private lemma fiberFunctional_zero {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) :
    fiberFunctional x (0 : Module.Dual R M) = 0 :=
  fibre_dual_ext x fun _ ↦ by simp

private lemma exists_fiberFunctional_eq_of_le_ker
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (x : ClosedPointSpace R) [FiniteDimensional (ClosedPointResidueField x) (ClosedPointFiber M x)]
    (ψ : Module.Dual (ClosedPointResidueField x) (ClosedPointFiber M x))
    (hψ : canonicalKernel M x ≤ LinearMap.ker ψ) :
    ∃ φ : Module.Dual R M, fiberFunctional x φ = ψ := by
  have hmem : ψ ∈ Submodule.span (ClosedPointResidueField x)
      (Set.range (fiberFunctional x : Module.Dual R M →
        Module.Dual (ClosedPointResidueField x) (ClosedPointFiber M x))) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    simpa [canonicalKernel] using hψ
  refine Submodule.span_induction
    (p := fun y _ ↦ ∃ φ : Module.Dual R M, fiberFunctional x φ = y)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨φ, rfl⟩
    exact ⟨φ, rfl⟩
  · exact ⟨0, fiberFunctional_zero x⟩
  · rintro _ _ _ _ ⟨φ, hφ⟩ ⟨χ, hχ⟩
    exact ⟨φ + χ, by rw [fiberFunctional_add, hφ, hχ]⟩
  · intro a _ _ ⟨φ, hφ⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b • φ, by rw [fiberFunctional_smul, hφ]⟩

private lemma exists_coordinate_functionals {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) :
    ∃ g : Fin r → Module.Dual K V, ∀ i j, g i (v j) = if i = j then 1 else 0 := by
  let P := Submodule.span K (Set.range v)
  have hex (i : Fin r) : ∃ g : Module.Dual K V,
      g.comp P.subtype = (Finsupp.lapply i).comp hv.repr :=
    LinearMap.exists_extend _
  choose g hg using hex
  refine ⟨g, fun i j ↦ ?_⟩
  let y : P := ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  calc
    g i (v j) = (g i ∘ₗ P.subtype) y := rfl
    _ = ((Finsupp.lapply i).comp hv.repr) y := LinearMap.congr_fun (hg i) y
    _ = (if i = j then 1 else 0) := by
      rw [LinearMap.comp_apply, hv.repr_eq_single j y rfl]
      by_cases h : i = j <;> simp [h]

/-- A retraction of the linear-combination map of a finite family sends the `j`-th member of the
family to the `j`-th standard basis vector. -/
theorem apply_apply_of_comp_linearCombination_eq_id {L N : Type*} [CommRing L] [AddCommGroup N]
    [Module L N] {r : ℕ} {v : Fin r → N} {p : N →ₗ[L] (Fin r → L)}
    (hp : p ∘ₗ Fintype.linearCombination L v = LinearMap.id) (i j : Fin r) :
    p (v j) i = if i = j then 1 else 0 := by
  have h := congrFun (LinearMap.congr_fun hp (Pi.single j 1)) i
  by_cases hij : i = j
  · subst i
    simpa [Fintype.linearCombination_apply] using h
  · simpa [Fintype.linearCombination_apply, hij, Ne.symm hij] using h

/-- A finite family that splits off a free summand after inverting an element outside `x` has
linearly independent images in `V(x)`. -/
theorem linearIndependent_mkQ_sectionAt_of_splitsAfterInverting
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (x : ClosedPointSpace R) {r : ℕ} {s : Fin r → M} {f : R}
    (hfx : f ∉ x.1.asIdeal) (hs : SplitsAfterInverting f s) :
    LinearIndependent (ClosedPointResidueField x)
      (fun i ↦ (canonicalKernel M x).mkQ (sectionAt x (s i))) := by
  classical
  obtain ⟨p, hp⟩ := hs
  let S := Submonoid.powers f
  let L := Localization S
  let ℓ (i : Fin r) : LocalizedModule S M →ₗ[R] L :=
    ((LinearMap.proj i).comp p).restrictScalars R
  have hex (i : Fin r) : ∃ (φ : Module.Dual R M) (t : S),
      (Algebra.linearMap R L) ∘ₗ φ = t •
        (ℓ i ∘ₗ LocalizedModule.mkLinearMap S M) :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S
      (Algebra.linearMap R L) (ℓ i ∘ₗ LocalizedModule.mkLinearMap S M)
  choose φ t ht using hex
  let q : R →+* ClosedPointResidueField x := Ideal.Quotient.mk x.1.asIdeal
  have hSf : ∀ y : S, IsUnit (q y.1) := by
    rintro ⟨_, n, rfl⟩
    refine isUnit_iff_ne_zero.mpr fun hy ↦ hfx (x.1.isPrime.mem_of_pow_mem n ?_)
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hy
  let ρ : L →+* ClosedPointResidueField x := IsLocalization.lift hSf
  have hρ (a : R) : ρ (algebraMap R L a) = q a :=
    IsLocalization.lift_eq hSf a
  have ht_eval (i j : Fin r) :
      q (φ i (s j)) = q (t i).1 * (if i = j then 1 else 0) := by
    have h := congrArg ρ (LinearMap.congr_fun (ht i) (s j))
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, ℓ,
      LinearMap.coe_restrictScalars, LinearMap.proj_apply,
      LinearMap.smul_apply, Submonoid.smul_def] at h
    rw [Algebra.smul_def, map_mul, hρ (φ i (s j)), hρ (t i).1,
      apply_apply_of_comp_linearCombination_eq_id hp] at h
    simpa using h
  let d (i : Fin r) : Module.Dual (ClosedPointResidueField x) (CanonicalQuotient M x) :=
    (q (t i).1)⁻¹ • (canonicalKernel M x).liftQ (fiberFunctional x (φ i)) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact (mem_canonicalKernel_iff x y).mp hy (φ i))
  have hd (i j : Fin r) :
      d i ((canonicalKernel M x).mkQ (sectionAt x (s j))) = if i = j then 1 else 0 := by
    change (q (t i).1)⁻¹ * fiberFunctional x (φ i) (sectionAt x (s j)) = _
    rw [fiberFunctional_sectionAt, ht_eval i j]
    split_ifs <;> simp [(hSf (t i)).ne_zero]
  exact LinearIndependent.of_pairwise_dual_eq_zero_one _ d
    (fun i j hij ↦ by simpa [hij] using hd i j) fun i ↦ by simpa using hd i i

/-- A finite family with linearly independent images in `V(x)` splits off a free summand after
inverting an element outside `x`. -/
theorem exists_splitsAfterInverting_of_linearIndependent
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : ClosedPointSpace R) {r : ℕ} {s : Fin r → M}
    (hli : LinearIndependent (ClosedPointResidueField x)
      (fun i ↦ (canonicalKernel M x).mkQ (sectionAt x (s i)))) :
    ∃ f : R, f ∉ x.1.asIdeal ∧ SplitsAfterInverting f s := by
  classical
  let qv : Fin r → CanonicalQuotient M x :=
    fun i ↦ (canonicalKernel M x).mkQ (sectionAt x (s i))
  obtain ⟨g, hg⟩ := exists_coordinate_functionals (v := qv) hli
  choose φ hφ using fun i ↦ exists_fiberFunctional_eq_of_le_ker x
    (g i ∘ₗ (canonicalKernel M x).mkQ)
    ((Submodule.ker_mkQ _).ge.trans (LinearMap.ker_le_ker_comp _ _))
  let A : Matrix (Fin r) (Fin r) R := fun i j ↦ φ i (s j)
  let f : R := A.det
  have hmapA : A.map (Ideal.Quotient.mk x.1.asIdeal) = 1 := by
    ext i j
    change Ideal.Quotient.mk x.1.asIdeal (φ i (s j)) = _
    rw [← fiberFunctional_sectionAt x (φ i), hφ i]
    simpa only [LinearMap.comp_apply, qv, Matrix.one_apply] using hg i j
  have ho : Ideal.Quotient.mk x.1.asIdeal f = 1 := by
    change Ideal.Quotient.mk x.1.asIdeal A.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmapA, Matrix.det_one]
  refine ⟨f, fun hf ↦ zero_ne_one ((Ideal.Quotient.eq_zero_iff_mem.mpr hf).symm.trans ho), ?_⟩
  let S := Submonoid.powers f
  let L := Localization S
  let Φ : LocalizedModule S M →ₗ[L] (Fin r → L) :=
    LinearMap.pi fun i ↦ IsLocalizedModule.mapExtendScalars S
      (LocalizedModule.mkLinearMap S M) (Algebra.linearMap R L) L (φ i)
  let AL : Matrix (Fin r) (Fin r) L := A.map (algebraMap R L)
  have hdet : IsUnit AL.det := by
    change IsUnit ((algebraMap R L).mapMatrix A).det
    rw [← RingHom.map_det]
    exact IsLocalization.map_units L ⟨f, Submonoid.mem_powers f⟩
  refine ⟨AL⁻¹.mulVecLin.comp Φ, ?_⟩
  have hΦ : Φ.comp (Fintype.linearCombination L
      (fun i ↦ LocalizedModule.mkLinearMap S M (s i))) = AL.mulVecLin := by
    apply LinearMap.ext
    intro c
    funext i
    have hmap (j : Fin r) :
        ((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
          (Algebra.linearMap R L)) (φ i)) (LocalizedModule.mk (s j) 1) =
            algebraMap R L (φ i (s j)) :=
      IsLocalizedModule.map_apply S (LocalizedModule.mkLinearMap S M)
        (Algebra.linearMap R L) (φ i) (s j)
    simp [Fintype.linearCombination_apply, Φ, AL, A, Matrix.mulVec,
      dotProduct, mul_comm, Matrix.map, hmap]
  rw [LinearMap.comp_assoc, hΦ, ← Matrix.mulVecLin_mul,
    Matrix.nonsing_inv_mul AL hdet, Matrix.mulVecLin_one]

/-- The canonical sequence `0 → B(x) → M(x) → V(x) → 0` is short exact.
Moreover, a finite family of elements of `M` splits off a free direct summand after
inverting an element outside `x` if and only if its images in `V(x)` are linearly
independent. -/
@[stacks 0GV9, ega "0 5.5.5" "affine case, closed pt"]
theorem canonical_exact_and_splits_iff_linearIndependent
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (x : ClosedPointSpace R) :
    Function.Injective (canonicalKernel M x).subtype ∧
      Function.Exact (canonicalKernel M x).subtype (canonicalKernel M x).mkQ ∧
      Function.Surjective (canonicalKernel M x).mkQ ∧
      ∀ (r : ℕ) (s : Fin r → M),
        (∃ f : R, f ∉ x.1.asIdeal ∧ SplitsAfterInverting f s) ↔
          LinearIndependent (ClosedPointResidueField x)
            (fun i ↦ (canonicalKernel M x).mkQ (sectionAt x (s i))) :=
  ⟨(canonicalKernel M x).injective_subtype, LinearMap.exact_subtype_mkQ _,
    Submodule.mkQ_surjective _, fun _ _ ↦
      ⟨fun ⟨_, hfx, hs⟩ ↦ linearIndependent_mkQ_sectionAt_of_splitsAfterInverting x hfx hs,
        exists_splitsAfterInverting_of_linearIndependent x⟩⟩

end CanonicalFibreQuotient

section SimultaneousValues

/-- At finitely many distinct closed points, every family of values in the canonical quotients
`V(x)` is induced by a single element of the module. -/
@[stacks 0GVA]
theorem pi_canonicalQuotient_mkQ_sectionAt_surjective
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Finite ι] (x : ι → ClosedPointSpace R) (hx : Function.Injective x) :
    Function.Surjective fun s : M ↦
      fun i ↦ (canonicalKernel M (x i)).mkQ (sectionAt (x i) s) := by
  classical
  let _ := Fintype.ofFinite ι
  intro values
  choose fibers hfibers using fun i ↦
    (canonicalKernel M (x i)).mkQ_surjective (values i)
  choose lifts hlifts using fun i ↦
    Submodule.mkQ_surjective ((x i).1.asIdeal • (⊤ : Submodule R M)) (fibers i)
  have hcoprime : Pairwise fun i j ↦ IsCoprime (x i).1.asIdeal (x j).1.asIdeal := by
    intro i j hij
    have := ClosedPointSpace.isMaximal (x i)
    have := ClosedPointSpace.isMaximal (x j)
    exact Ideal.isCoprime_of_isMaximal (fun h ↦
      hij (hx (Subtype.ext (PrimeSpectrum.ext h))))
  choose coefficient hcoefficient using fun i ↦
    Ideal.pi_quotient_surjective hcoprime
      (fun j ↦ if i = j then (1 : R ⧸ (x j).1.asIdeal) else 0)
  have hsection (i j : ι) :
      sectionAt (x j) (coefficient i • lifts i) = if i = j then fibers j else 0 := by
    by_cases hij : i = j
    · subst i
      simp only [← hlifts j, sectionAt]
      apply (Submodule.Quotient.eq _).mpr
      have hc : coefficient j - 1 ∈ (x j).1.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hcoefficient]
        simp
      simpa [sub_smul] using
        (Submodule.smul_mem_smul (N := (⊤ : Submodule R M)) hc Submodule.mem_top)
    · simp only [hij, ↓reduceIte, sectionAt, Submodule.Quotient.mk_eq_zero]
      refine Submodule.smul_mem_smul ?_ trivial
      rw [← Ideal.Quotient.eq_zero_iff_mem, hcoefficient]
      simp [hij]
  refine ⟨∑ i, coefficient i • lifts i, funext fun j ↦ ?_⟩
  have hsum : sectionAt (x j) (∑ i, coefficient i • lifts i) = fibers j := by
    change Submodule.Quotient.mk (∑ i, coefficient i • lifts i) = fibers j
    rw [← Submodule.mkQ_apply, map_sum]
    simp_rw [Submodule.mkQ_apply, hsection]
    simp
  exact (congrArg (canonicalKernel M (x j)).mkQ hsum).trans (hfibers j)

end SimultaneousValues
