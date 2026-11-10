module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.PrimePowerAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCubeAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Tower
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeWeakNormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Ring
public import StacksFrontier.AlgebraicGeometry.Seminormalization.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.WeaklyNormalScheme

/-!
# Weak normality of an affine scheme

An affine scheme `Spec A` with finitely many irreducible components is weakly normal exactly
when `A` is seminormal and, for every prime number `p` and every pair `z, w ∈ A` with `z` a
nonzerodivisor, `z ^ p ∣ w ^ p` and `z ∣ p * w`, already `z ∣ w`.

## Main definitions

* `AlgebraicGeometry.IsWeaklyNormalRing` is the conjunction of those two ring conditions.

## Main results

* `AlgebraicGeometry.isWeaklyNormal_spec_iff` characterizes weak normality of an affine
  scheme by `AlgebraicGeometry.IsWeaklyNormalRing` of its coordinate ring.

## Implementation notes

Both halves of the characterization run through the same mechanism. A weakly normal scheme is
initial among the factorizations of its normalization morphism through a universal
homeomorphism, so every universal homeomorphism `Spec C ⟶ Spec A` receiving a map from the
normalization is split by a ring retraction `C ⟶ A`; conversely the relative weak
normalization of `A` in the integral closure of its total ring of fractions is a union of
square-cube and prime-power towers, and the two ring conditions make every such tower
collapse into `A`.

Seminormality of `A` is obtained by the same device rather than through the seminormalization
of `Spec A`: for `x ^ 3 = y ^ 2` the square-cube algebra `A[t]/(t ^ 2 - x, t ^ 3 - y)` is a
universal homeomorphism over `Spec A`, and it receives a morphism from the spectra of the
generic-point residue fields because in a field a square-cube pair always has a common root.
Relative normalization turns that into a factorization of the normalization morphism, which
weak normality retracts. This produces only the existence of the common root; reducedness of
`A` — and hence uniqueness — follows from existence alone.

The finiteness hypothesis is stated for every quasi-compact open, matching the form in which
the normalization of a scheme is available; for an affine scheme it is equivalent to
finiteness of the irreducible components.

## References

* [Stacks Project, Tag 0H3T](https://stacks.math.columbia.edu/tag/0H3T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The affine criterion for weak normality: seminormality together with the prime-power
divisibility condition for nonzerodivisors. -/
abbrev IsWeaklyNormalRing (A : Type*) [CommRing A] : Prop :=
  IsSeminormalRing A ∧
    ∀ (p : ℕ) (_hp : p.Prime) (z w : A),
      IsRegular z → z ^ p ∣ w ^ p → z ∣ (p : A) * w → z ∣ w

/-! ### Ring maps underlying morphisms of affine spectra -/

/-- The ring map underlying a morphism between the spectra of two rings. -/
private def specHomRingHom {A B : Type u} [CommRing A] [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of A)) : A →+* B :=
  (Spec.preimage f).hom

private theorem specMap_specHomRingHom {A B : Type u} [CommRing A] [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of A)) :
    Scheme.Spec.map (CommRingCat.ofHom (specHomRingHom f)).op = f := by
  simp [specHomRingHom]

private theorem specHomRingHom_specMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : specHomRingHom (Spec.map (CommRingCat.ofHom f)) = f := by
  change specHomRingHom (Scheme.Spec.map (CommRingCat.ofHom f).op) = f
  simp [specHomRingHom]

private theorem specHomRingHom_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : Spec (.of C) ⟶ Spec (.of B)) (g : Spec (.of B) ⟶ Spec (.of A)) :
    (specHomRingHom f).comp (specHomRingHom g) = specHomRingHom (f ≫ g) := by
  simp [specHomRingHom]

/-- A ring map whose values all come from an injective structure map factors through the
base ring. -/
private def rangeFactorRingHom {A B D : Type u} [CommRing A] [CommRing B]
    [CommRing D] [Algebra A B] (f : D →+* B) (hinj : Function.Injective (algebraMap A B))
    (hrange : ∀ d : D, f d ∈ Set.range (algebraMap A B)) : D →+* A :=
  (RingEquiv.ofBijective (algebraMap A B).rangeRestrict
    ⟨fun _ _ hh => hinj (congrArg Subtype.val hh),
      (algebraMap A B).rangeRestrict_surjective⟩).symm.toRingHom.comp
    (f.codRestrict (algebraMap A B).range hrange)

private theorem algebraMap_comp_rangeFactorRingHom {A B D : Type u} [CommRing A] [CommRing B]
    [CommRing D] [Algebra A B] (f : D →+* B) (hinj : Function.Injective (algebraMap A B))
    (hrange : ∀ d : D, f d ∈ Set.range (algebraMap A B)) :
    (algebraMap A B).comp (rangeFactorRingHom f hinj hrange) = f := by
  ext d
  exact congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap A B).rangeRestrict
    ⟨fun _ _ hh => hinj (congrArg Subtype.val hh),
      (algebraMap A B).rangeRestrict_surjective⟩).apply_symm_apply
        ((f.codRestrict (algebraMap A B).range hrange) d))

/-! ### Square-cube pairs -/

/-- In a field a pair with `x ^ 3 = y ^ 2` is the square and cube of a common element. -/
private theorem exists_sq_cube_of_field {K : Type u} [Field K] {x y : K}
    (h : x ^ 3 = y ^ 2) : ∃ a : K, x = a ^ 2 ∧ y = a ^ 3 := by
  by_cases hx : x = 0
  · refine ⟨0, by simp [hx], ?_⟩
    have hy : y ^ 2 = 0 := by rw [← h, hx]; ring
    simp [pow_eq_zero_iff (two_ne_zero) |>.mp hy]
  · have hy : y ≠ 0 := by
      intro hy0
      exact hx (pow_eq_zero_iff (three_ne_zero) |>.mp (by rw [h, hy0]; ring))
    refine ⟨y / x, ?_, ?_⟩
    · field_simp
      linear_combination h
    · field_simp
      linear_combination h

/-- A morphism from the spectrum of a field to `Spec A` lifts through the square-cube
algebra of a pair with `x ^ 3 = y ^ 2`. -/
private theorem exists_comp_squareCubeSpecMap {A : Type u} [CommRing A] (x y : A)
    (h : x ^ 3 = y ^ 2) {K : Type u} [Field K] (g : Spec (.of K) ⟶ Spec (.of A)) :
    ∃ l : Spec (.of K) ⟶ Spec (.of (SquareCubeAlgebra A x y)),
      l ≫ squareCubeSpecMap A x y = g := by
  classical
  let ψ : A →+* K := specHomRingHom g
  let : Algebra A K := ψ.toAlgebra
  obtain ⟨a, ha2, ha3⟩ := exists_sq_cube_of_field
    (x := algebraMap A K x) (y := algebraMap A K y) (by rw [← map_pow, ← map_pow, h])
  have hker : Ideal.span ({Polynomial.X ^ 2 - Polynomial.C x,
      Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A)) ≤
      RingHom.ker (Polynomial.aeval (R := A) a).toRingHom := by
    rw [Ideal.span_le]
    rintro r (hr | hr)
    · subst r
      simp [RingHom.mem_ker, ← ha2]
    · subst r
      simp [RingHom.mem_ker, ← ha3]
  let φ : SquareCubeAlgebra A x y →ₐ[A] K :=
    Ideal.Quotient.liftₐ _ (Polynomial.aeval a) fun r hr => RingHom.mem_ker.mp (hker hr)
  have hcomp : CommRingCat.ofHom (algebraMap A (SquareCubeAlgebra A x y)) ≫
      CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom ψ := by
    ext b
    exact φ.commutes b
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (SquareCubeAlgebra A x y))) = g
  rw [← Spec.map_comp, hcomp]
  exact specMap_specHomRingHom g

/-! ### The normalization of a reduced affine scheme -/

/-- The identification of the normalization of a reduced affine scheme with the spectrum of
the integral closure of its coordinate ring in its total ring of fractions. -/
private def affineNormalizationIso (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    [IsReduced (Spec (.of A))] :
    Scheme.normalizationScheme (Spec (.of A)) hA ≅
      Spec (.of (integralClosure A (FractionRing A))) := by
  let X := Spec (CommRingCat.of A)
  let N := Scheme.normalizationScheme X hA
  let U : X.Opens := ⊤
  let e0 := preimageNormalizationIsoSpecIntegralClosure hA U X.topIso.symm
  let epre : (Scheme.normalization X hA ⁻¹ᵁ U).toScheme ≅ N :=
    Scheme.isoOfEq N (Scheme.Hom.preimage_top (Scheme.normalization X hA)) ≪≫ N.topIso
  exact epre.symm ≪≫ e0

private theorem affineNormalizationIso_hom_map (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    [IsReduced (Spec (.of A))] :
    (affineNormalizationIso A hA).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap A (integralClosure A (FractionRing A)))) =
      Scheme.normalization (Spec (.of A)) hA := by
  let X := Spec (CommRingCat.of A)
  let N := Scheme.normalizationScheme X hA
  let U : X.Opens := ⊤
  let f := Scheme.normalization X hA
  let epre : (f ⁻¹ᵁ U).toScheme ≅ N :=
    Scheme.isoOfEq N (Scheme.Hom.preimage_top f) ≪≫ N.topIso
  change (epre.symm ≪≫ preimageNormalizationIsoSpecIntegralClosure hA U X.topIso.symm).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) = f
  rw [Iso.trans_hom, Category.assoc,
    preimageNormalizationIsoSpecIntegralClosure_hom_comp hA U X.topIso.symm,
    ← Scheme.Hom.resLE_eq_morphismRestrict (f := f) (U := U)]
  change epre.inv ≫ f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ U.ι = f
  rw [Scheme.Hom.resLE_comp_ι]
  simp [epre, f, U]

/-- The spectrum of the prime-power algebra attached to a pair of divisibility witnesses maps
to the integral closure, sending the adjoined root to the quotient `w / z`. -/
private def pPowerAlgebraToIntegralClosure
    (A : Type u) [CommRing A] {p : ℕ} (hp : 0 < p) (x y z w : A)
    (hz : IsRegular z) (hx : z ^ p * x = w ^ p) (hy : z * y = (p : A) * w) :
    let C := Polynomial A ⧸ Ideal.span
      {Polynomial.X ^ p - Polynomial.C x,
        Polynomial.C (p : A) * Polynomial.X - Polynomial.C y}
    C →ₐ[A] integralClosure A (FractionRing A) := by
  classical
  let K := FractionRing A
  let B := integralClosure A K
  let q : K := IsLocalization.mk' K w ⟨z, isRegular_iff_mem_nonZeroDivisors.mp hz⟩
  have hzU : IsUnit (algebraMap A K z) :=
    IsLocalization.map_units K ⟨z, isRegular_iff_mem_nonZeroDivisors.mp hz⟩
  have hspec : q * algebraMap A K z = algebraMap A K w :=
    IsLocalization.mk'_spec K w ⟨z, isRegular_iff_mem_nonZeroDivisors.mp hz⟩
  have hqpow : q ^ p = algebraMap A K x := by
    apply (hzU.pow p).mul_right_cancel
    calc
      q ^ p * (algebraMap A K z) ^ p = (q * algebraMap A K z) ^ p := by ring
      _ = (algebraMap A K w) ^ p := by rw [hspec]
      _ = algebraMap A K (w ^ p) := (map_pow (algebraMap A K) w p).symm
      _ = algebraMap A K (z ^ p * x) := by rw [hx]
      _ = algebraMap A K x * (algebraMap A K z) ^ p := by rw [map_mul, map_pow]; ring
  have hqlin : (p : K) * q = algebraMap A K y := by
    apply hzU.mul_right_cancel
    calc
      (p : K) * q * algebraMap A K z = (p : K) * (q * algebraMap A K z) := by ring
      _ = (p : K) * algebraMap A K w := by rw [hspec]
      _ = algebraMap A K ((p : A) * w) := by simp
      _ = algebraMap A K (z * y) := by rw [← hy]
      _ = algebraMap A K y * algebraMap A K z := by rw [map_mul]; ring
  have hInt : _root_.IsIntegral A q :=
    ⟨Polynomial.X ^ p - Polynomial.C x, Polynomial.monic_X_pow_sub_C x (Nat.ne_of_gt hp), by
      simp [hqpow]⟩
  let a : B := ⟨q, hInt⟩
  let I : Ideal (Polynomial A) := Ideal.span
    {Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C (p : A) * Polynomial.X - Polynomial.C y}
  let ev : Polynomial A →+* B := Polynomial.eval₂RingHom (algebraMap A B) a
  have hker : I ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro r (hr | hr)
    · subst r
      have hpa : a ^ p = algebraMap A B x := Subtype.ext hqpow
      simp [ev, hpa]
    · subst r
      have hpa : (p : B) * a = algebraMap A B y := Subtype.ext hqlin
      simp [ev, hpa]
  exact
    { toRingHom := Ideal.Quotient.lift I ev fun r hr => RingHom.mem_ker.mp (hker hr)
      commutes' := by
        intro a0
        change Ideal.Quotient.lift I ev (fun r hr => RingHom.mem_ker.mp (hker hr))
          (Ideal.Quotient.mk I (Polynomial.C a0)) = algebraMap A B a0
        rw [Ideal.Quotient.lift_mk]
        simp [ev] }

private theorem pPowerAlgebraToIntegralClosure_X (A : Type u) [CommRing A] {p : ℕ}
    (hp : 0 < p) (x y z w : A) (hz : IsRegular z)
    (hx : z ^ p * x = w ^ p) (hy : z * y = (p : A) * w) :
    ((pPowerAlgebraToIntegralClosure A hp x y z w hz hx hy
      (Ideal.Quotient.mk _ Polynomial.X) : integralClosure A (FractionRing A)) :
        FractionRing A) =
      IsLocalization.mk' (FractionRing A) w
        ⟨z, isRegular_iff_mem_nonZeroDivisors.mp hz⟩ := by
  classical
  simp [pPowerAlgebraToIntegralClosure, Ideal.Quotient.lift_mk]

/-! ### Seminormality of a weakly normal affine scheme -/

/-- The normalization morphism of an affine scheme with finitely many irreducible components is
dominant. -/
private theorem isDominant_normalization_spec (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite) :
    IsDominant (Scheme.normalization (Spec (.of A)) hA) := by
  let : QuasiCompact (Spec (CommRingCat.of A)).fromGenericPointResidueFields :=
    Scheme.quasiCompactFromGenericPointResidueFields _ hA
  let : QuasiSeparated (Spec (CommRingCat.of A)).fromGenericPointResidueFields :=
    Scheme.quasiSeparatedFromGenericPointResidueFields _
  exact Scheme.normalization_isDominant _ hA

/-- On a weakly normal affine scheme, every factorization of the normalization morphism
through a universal homeomorphism is split by a section. -/
private theorem exists_section_of_isWeaklyNormal (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    (hWN : Scheme.IsWeaklyNormal (Spec (.of A)) hA) {Y : Scheme.{u}}
    (n : Scheme.normalizationScheme (Spec (.of A)) hA ⟶ Y) (c : Y ⟶ Spec (.of A))
    (hc : UniversalHomeomorphism c) (hfac : n ≫ c = Scheme.normalization (Spec (.of A)) hA) :
    ∃ k : Spec (.of A) ⟶ Y, k ≫ c = 𝟙 _ ∧ Scheme.normalization (Spec (.of A)) hA ≫ k = n := by
  have := isDominant_normalization_spec A hA
  let F : UniversalHomeomorphismFactorization (Scheme.normalization (Spec (.of A)) hA) :=
    ⟨Y, n, c, hfac, hc⟩
  let W := Scheme.weakNormalizationFactorization (Spec (.of A)) hA
  let hWinit := weakNormalizationFactorizationIsInitial (Scheme.normalization (Spec (.of A)) hA)
  have hWiso : IsIso W.toBase := hWN
  let α := hWinit.to F
  refine ⟨inv W.toBase ≫ α.hom, ?_, ?_⟩
  · calc
      (inv W.toBase ≫ α.hom) ≫ c = inv W.toBase ≫ α.hom ≫ F.toBase := Category.assoc _ _ _
      _ = inv W.toBase ≫ W.toBase := by rw [α.hom_toBase]
      _ = 𝟙 _ := IsIso.inv_hom_id _
  · calc
      Scheme.normalization (Spec (.of A)) hA ≫ inv W.toBase ≫ α.hom =
          (W.toMiddle ≫ W.toBase) ≫ inv W.toBase ≫ α.hom := by rw [W.fac]
      _ = W.toMiddle ≫ α.hom := by simp [Category.assoc]
      _ = n := α.toMiddle_hom

/-- A section of the square-cube algebra over `A` produces a common square and cube root. -/
private theorem exists_sq_cube_of_section {A : Type u} [CommRing A] {x y : A}
    (k : Spec (.of A) ⟶ Spec (.of (SquareCubeAlgebra A x y)))
    (hk : k ≫ squareCubeSpecMap A x y = 𝟙 _) : ∃ a : A, x = a ^ 2 ∧ y = a ^ 3 := by
  classical
  let I : Ideal (Polynomial A) := Ideal.span
    ({Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} :
      Set (Polynomial A))
  let C := SquareCubeAlgebra A x y
  let ρ : C →+* A := specHomRingHom k
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 (Spec (CommRingCat.of A)) := by
    simp
  have hρ : ρ.comp (algebraMap A C) = RingHom.id A := by
    have hkring := congrArg specHomRingHom hk
    rw [← specHomRingHom_comp, ← hid] at hkring
    have hcX : specHomRingHom (squareCubeSpecMap A x y) = algebraMap A C :=
      specHomRingHom_specMap (algebraMap A C)
    rwa [hcX, specHomRingHom_specMap] at hkring
  have hρmap : ∀ b : A, ρ (algebraMap A C b) = b := fun b => RingHom.congr_fun hρ b
  have halg : ∀ b : A, Ideal.Quotient.mk I (Polynomial.C b) = algebraMap A C b := fun b => by
    simpa [Ideal.Quotient.mkₐ_eq_mk, Polynomial.algebraMap_eq] using
      (Ideal.Quotient.mkₐ A I).commutes b
  let t : C := Ideal.Quotient.mk I Polynomial.X
  have htpow (m : ℕ) (c : A) (hm : Polynomial.X ^ m - Polynomial.C c ∈ I) :
      ρ t ^ m = c := by
    rw [← map_pow, ← hρmap c, ← halg c]
    simpa [t] using congrArg ρ (Ideal.Quotient.eq.mpr hm)
  exact ⟨ρ t, (htpow 2 x (Ideal.subset_span (by simp))).symm,
    (htpow 3 y (Ideal.subset_span (by simp))).symm⟩

/-- A weakly normal affine scheme has a common square and cube root for every compatible
pair in its coordinate ring. -/
private theorem exists_sq_cube_of_isWeaklyNormal (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    (hWN : Scheme.IsWeaklyNormal (Spec (.of A)) hA) (x y : A) (h : x ^ 3 = y ^ 2) :
    ∃ a : A, x = a ^ 2 ∧ y = a ^ 3 := by
  classical
  let C := SquareCubeAlgebra A x y
  let cX : Spec (.of C) ⟶ Spec (.of A) := squareCubeSpecMap A x y
  have hC : UniversalHomeomorphism cX := squareCubeSpecMap_universalHomeomorphism A x y h
  have : IsIntegralHom cX :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective cX).mp hC |>.1
  let f := (Spec (CommRingCat.of A)).fromGenericPointResidueFields
  let : QuasiCompact f := Scheme.quasiCompactFromGenericPointResidueFields _ hA
  let : QuasiSeparated f := Scheme.quasiSeparatedFromGenericPointResidueFields _
  let D := fun η : genericPoints (Spec (CommRingCat.of A)) =>
    Spec (.of ((Spec (CommRingCat.of A)).residueField η.1))
  let lift : (∐ D) ⟶ Spec (.of C) := Sigma.desc fun η => Classical.choose
    (exists_comp_squareCubeSpecMap x y h
      ((Spec (CommRingCat.of A)).fromSpecResidueField η.1))
  have hlift : lift ≫ cX = f := by
    apply Sigma.hom_ext
    intro η
    rw [← Category.assoc, Sigma.ι_comp_desc]
    refine (Classical.choose_spec (exists_comp_squareCubeSpecMap x y h
      ((Spec (CommRingCat.of A)).fromSpecResidueField η.1))).trans ?_
    exact ((Spec (CommRingCat.of A)).genericPointResidueSpectrum_ι_fromGenericPointResidueFields
      η).symm
  let lift' : (Spec (CommRingCat.of A)).genericPointResidueSpectrum ⟶ Spec (.of C) := lift
  have hlift' : lift' ≫ cX = f := hlift
  obtain ⟨k, hk, -⟩ := exists_section_of_isWeaklyNormal A hA hWN
    (f.normalizationDesc lift' cX hlift'.symm) cX hC (f.normalizationDesc_comp lift' cX hlift'.symm)
  exact exists_sq_cube_of_section k hk

/-! ### Collapsing the towers of the relative weak normalization -/

/-- The image of an element of an adjoined algebra lies in the algebra generated by the
image of the generators. -/
private theorem algHom_mem_adjoin {A R S : Type u} [CommRing A] [CommRing R]
    [Algebra A R] [CommRing S] [Algebra A S] (φ : R →ₐ[A] S) (s : Set R) {z : R}
    (hz : z ∈ Algebra.adjoin A s) : φ z ∈ Algebra.adjoin A (φ '' s) := by
  rw [Algebra.adjoin_image]
  exact Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩

/-- A seminormal ring contains every element of a reduced extension whose square and cube
come from the ring. -/
private theorem seminormal_mem_range {A K : Type u} [CommRing A] [CommRing K]
    [Algebra A K] [_root_.IsReduced K] (hinj : Function.Injective (algebraMap A K))
    (hA : IsSeminormalRing A) {z : K} {a b : A}
    (h2 : z ^ 2 = algebraMap A K a) (h3 : z ^ 3 = algebraMap A K b) :
    ∃ c : A, algebraMap A K c = z := by
  have hrel : a ^ 3 = b ^ 2 := by
    apply hinj
    rw [map_pow, map_pow, ← h2, ← h3]
    ring
  obtain ⟨c, hc, -⟩ := hA a b hrel
  refine ⟨c, Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq ?_ ?_⟩
  · rw [← map_pow, ← hc.1, ← h2]
  · rw [← map_pow, ← hc.2, ← h3]

/-- The prime-power divisibility condition makes an element of the total ring of fractions
whose `p`-th power and `p`-fold multiple come from the ring already come from the ring. -/
private theorem prime_mem_range {A K : Type u} [CommRing A] [CommRing K]
    [Algebra A K] [IsFractionRing A K] {p : ℕ}
    (hcrit : ∀ z w : A, IsRegular z → z ^ p ∣ w ^ p → z ∣ (p : A) * w → z ∣ w)
    {q : K} {a b : A} (hpow : q ^ p = algebraMap A K a)
    (hlin : (p : K) * q = algebraMap A K b) :
    ∃ c : A, algebraMap A K c = q := by
  obtain ⟨w, z, hq⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) q
  have hspec : q * algebraMap A K (z : A) = algebraMap A K w := by
    rw [← hq]
    exact IsLocalization.mk'_spec K w z
  have hpow' : algebraMap A K ((z : A) ^ p * a) = algebraMap A K (w ^ p) := by
    rw [map_mul, map_pow, map_pow]
    calc
      algebraMap A K (z : A) ^ p * algebraMap A K a =
          algebraMap A K (z : A) ^ p * q ^ p := by rw [hpow]
      _ = (q * algebraMap A K (z : A)) ^ p := by ring
      _ = algebraMap A K w ^ p := by rw [hspec]
  have hpowA : (z : A) ^ p * a = w ^ p := (IsFractionRing.injective A K) hpow'
  have hlin' : algebraMap A K ((p : A) * w) = algebraMap A K (b * (z : A)) := by
    calc
      algebraMap A K ((p : A) * w) = (p : K) * algebraMap A K w := by simp
      _ = (p : K) * (q * algebraMap A K (z : A)) := by rw [hspec]
      _ = (algebraMap A K b) * algebraMap A K (z : A) := by rw [← mul_assoc, hlin]
      _ = algebraMap A K (b * (z : A)) := (map_mul _ _ _).symm
  have hlinA : (p : A) * w = b * (z : A) := (IsFractionRing.injective A K) hlin'
  obtain ⟨c, hc⟩ := hcrit (z : A) w ((isRegular_iff_mem_nonZeroDivisors).2 z.property)
    ⟨a, hpowA.symm⟩ ⟨b, by simpa [mul_comm] using hlinA⟩
  refine ⟨c, ?_⟩
  have hmul : q * algebraMap A K (z : A) = algebraMap A K c * algebraMap A K (z : A) := by
    calc
      q * algebraMap A K (z : A) = algebraMap A K w := hspec
      _ = algebraMap A K ((z : A) * c) := by rw [← hc]
      _ = algebraMap A K c * algebraMap A K (z : A) := by rw [map_mul]; ring
  exact (IsUnit.mul_right_cancel (IsLocalization.map_units K z) hmul).symm

/-- Under the two ring conditions every member of a square-cube/prime-power tower in the
integral closure already lies in the ring. -/
private theorem tower_mem_range (A : Type u) [CommRing A] (hA : IsSeminormalRing A)
    (hcrit : ∀ (p : ℕ), p.Prime → ∀ z w : A,
      IsRegular z → z ^ p ∣ w ^ p → z ∣ (p : A) * w → z ∣ w)
    [_root_.IsReduced A] {n : ℕ} (b : Fin n → integralClosure A (FractionRing A))
    (ht : ∀ i : Fin n,
      (((b i) ^ 2 ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ b j)) ∧
        ((b i) ^ 3 ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ b j))) ∨
      (∃ p : ℕ, p.Prime ∧
        (((p : integralClosure A (FractionRing A)) * b i ∈
          Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ b j)) ∧
          ((b i) ^ p ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ b j))))) :
    ∀ i : Fin n, ∃ a : A,
      algebraMap A (integralClosure A (FractionRing A)) a = b i := by
  classical
  let K := FractionRing A
  let B := integralClosure A K
  have hrec : ∀ m : ℕ, ∀ i : Fin n, i.val < m → ∃ a : A, algebraMap A B a = b i := by
    intro m
    induction m with
    | zero => exact fun _ hi => absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i him
      by_cases him' : i.val < m
      · exact ih i him'
      · have hle : Algebra.adjoin A
            (Set.range fun j : {j : Fin n // j < i} ↦ b j) ≤ ⊥ := Algebra.adjoin_le (by
          rintro w ⟨j, rfl⟩
          obtain ⟨a, ha⟩ := ih j.1 (by omega)
          exact Algebra.mem_bot.mpr ⟨a, ha⟩)
        have hK : ∀ {v : B}, v ∈ Algebra.adjoin A
            (Set.range fun j : {j : Fin n // j < i} ↦ b j) → ∃ a : A, (v : K) = algebraMap A K a :=
          fun hv => by
            obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hle hv)
            exact ⟨a, by rw [← ha]; rfl⟩
        rcases ht i with hcube | ⟨p, hp, hlin, hpow⟩
        · obtain ⟨a, h2a⟩ := hK hcube.1
          obtain ⟨a3, h3a⟩ := hK hcube.2
          obtain ⟨c, hc⟩ := seminormal_mem_range (IsFractionRing.injective A K) hA
            (by simpa using h2a) (by simpa using h3a)
          exact ⟨c, Subtype.ext (by simpa using hc)⟩
        · obtain ⟨a1, h1a⟩ := hK hlin
          obtain ⟨a2, h2a⟩ := hK hpow
          obtain ⟨c, hc⟩ := prime_mem_range (hcrit p hp) (by simpa using h2a) (by simpa using h1a)
          exact ⟨c, Subtype.ext (by simpa using hc)⟩
  exact fun i => hrec (i.val + 1) i (by omega)

/-- A ring embeds into its integral closure in its total ring of fractions. -/
private theorem algebraMap_integralClosure_injective (A : Type u) [CommRing A] :
    Function.Injective (algebraMap A (integralClosure A (FractionRing A))) := fun _ _ h =>
  IsFractionRing.injective A (FractionRing A)
    (congrArg (fun v : integralClosure A (FractionRing A) => (v : FractionRing A)) h)

/-- Under the two ring conditions the relative weak normalization of `A` in the integral
closure of its total ring of fractions is `A` itself. -/
private theorem relativeWeakNormalization_le_bot {A : Type u} [CommRing A]
    (hA : IsSeminormalRing A)
    (hcrit : ∀ (p : ℕ), p.Prime → ∀ z w : A,
      IsRegular z → z ^ p ∣ w ^ p → z ∣ (p : A) * w → z ∣ w)
    [_root_.IsReduced A]
    (hdom : IsDominant (Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))).op)) :
    relativeWeakNormalization A (integralClosure A (FractionRing A)) ≤ ⊥ := by
  classical
  let B := integralClosure A (FractionRing A)
  let R := relativeWeakNormalization A B
  let incl : R →ₐ[A] B := Subalgebra.val R
  have hAR : Function.Injective (algebraMap A R) := fun a a' haa' =>
    algebraMap_integralClosure_injective A (congrArg Subtype.val haa')
  have hTowers := (universalHomeomorphism_spec_iff_finite_adjoin_tower A R hAR).mp
    (relativeWeakNormalization_isUniversalHomeomorphism A B hdom)
  intro r hr
  let rR : R := ⟨r, hr⟩
  obtain ⟨n, b, hmem, hsteps⟩ := hTowers ({rR} : Finset R)
  let bB : Fin n → B := fun i => incl (b i)
  have hrange (i : Fin n) :
      incl '' Set.range (fun j : {j : Fin n // j < i} ↦ b j) =
        Set.range (fun j : {j : Fin n // j < i} ↦ bB j) :=
    (Set.range_comp' incl _).symm
  have hmap (i : Fin n) {z : R}
      (hz : z ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ b j)) :
      incl z ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ bB j) := by
    have hh := algHom_mem_adjoin incl _ hz
    rwa [hrange i] at hh
  have hstepsB : ∀ i : Fin n,
      (((bB i) ^ 2 ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ bB j)) ∧
        ((bB i) ^ 3 ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ bB j))) ∨
      (∃ p : ℕ, p.Prime ∧
        (((p : B) * bB i ∈ Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ bB j)) ∧
          ((bB i) ^ p ∈
            Algebra.adjoin A (Set.range fun j : {j : Fin n // j < i} ↦ bB j)))) := by
    intro i
    rcases hsteps i with hcube | ⟨p, hp, hmul, hpow⟩
    · exact Or.inl ⟨by simpa [bB, map_pow] using hmap i hcube.1,
        by simpa [bB, map_pow] using hmap i hcube.2⟩
    · exact Or.inr ⟨p, hp, by simpa [bB] using hmap i hmul,
        by simpa [bB, map_pow] using hmap i hpow⟩
  have hrAdjoin : incl rR ∈ Algebra.adjoin A (Set.range bB) := by
    have hh := algHom_mem_adjoin incl (Set.range b)
      (hmem (Finset.mem_coe.mpr (Finset.mem_singleton_self rR)))
    rwa [(Set.range_comp' incl b).symm] at hh
  have hle : Algebra.adjoin A (Set.range bB) ≤ ⊥ := Algebra.adjoin_le (by
    rintro v ⟨i, rfl⟩
    exact Algebra.mem_bot.mpr (tower_mem_range A hA hcrit bB hstepsB i))
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hle hrAdjoin)
  exact Algebra.mem_bot.mpr ⟨a, by simpa [rR, incl] using ha⟩

/-! ### The ring conditions from weak normality -/

/-- A ring in which every square-cube pair has a common root is seminormal. -/
private theorem isSeminormalRing_of_exists_sq_cube {A : Type u} [CommRing A]
    (hex : ∀ x y : A, x ^ 3 = y ^ 2 → ∃ a : A, x = a ^ 2 ∧ y = a ^ 3) :
    IsSeminormalRing A := by
  have : _root_.IsReduced A := Stacks.RingTheory.Seminormal.isReduced_of_exists_sq_cube hex
  intro x y hxy
  obtain ⟨a, ha⟩ := hex x y hxy
  refine ⟨a, ha, fun c hc => Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq ?_ ?_⟩
  · rw [← hc.1, ← ha.1]
  · rw [← hc.2, ← ha.2]

/-- Divisibility witnesses for `z ^ p ∣ w ^ p` and `z ∣ p * w` with `z` regular satisfy the
prime-power relation of the prime-power algebra. -/
private theorem natCast_pow_mul_eq_pow_of_isRegular {A : Type u} [CommRing A] {p : ℕ}
    {x y z w : A} (hz : IsRegular z) (hx : w ^ p = z ^ p * x) (hy : (p : A) * w = z * y) :
    (p : A) ^ p * x = y ^ p := by
  have hscaled : z ^ p * ((p : A) ^ p * x) = z ^ p * y ^ p := by
    calc
      z ^ p * ((p : A) ^ p * x) = (p : A) ^ p * (z ^ p * x) := by ring
      _ = (p : A) ^ p * w ^ p := by rw [hx]
      _ = ((p : A) * w) ^ p := by rw [mul_pow]
      _ = (z * y) ^ p := by rw [hy]
      _ = z ^ p * y ^ p := by rw [mul_pow]
  refine sub_eq_zero.mp ((isRegular_iff_eq_zero_of_mul.mp (hz.pow p)).1 _ ?_)
  rw [mul_sub]
  exact sub_eq_zero.mpr hscaled

/-- A regular element divides every element whose quotient by it comes from the ring. -/
private theorem dvd_of_algebraMap_eq_mk' {A : Type u} [CommRing A] {z w c : A}
    (hz : IsRegular z)
    (hc : algebraMap A (FractionRing A) c =
      IsLocalization.mk' (FractionRing A) w ⟨z, isRegular_iff_mem_nonZeroDivisors.mp hz⟩) :
    z ∣ w := by
  have hcz : algebraMap A (FractionRing A) c * algebraMap A (FractionRing A) z =
      algebraMap A (FractionRing A) w := by
    rw [hc]
    exact IsLocalization.mk'_spec (FractionRing A) w
      ⟨z, isRegular_iff_mem_nonZeroDivisors.mp hz⟩
  have hczA : c * z = w :=
    IsFractionRing.injective A (FractionRing A) (by simpa only [map_mul] using hcz)
  exact ⟨c, by rw [← hczA, mul_comm]⟩

/-- The coordinate ring of a weakly normal affine scheme satisfies the prime-power
divisibility condition for nonzerodivisors. -/
private theorem dvd_of_isWeaklyNormal (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    (hWN : Scheme.IsWeaklyNormal (Spec (.of A)) hA) {p : ℕ} (hp : p.Prime) {z w : A}
    (hz : IsRegular z) (hpow : z ^ p ∣ w ^ p) (hlin : z ∣ (p : A) * w) : z ∣ w := by
  classical
  have : _root_.IsReduced ↥(CommRingCat.of A) :=
    Stacks.RingTheory.Seminormal.isReduced_of_exists_sq_cube
      (exists_sq_cube_of_isWeaklyNormal A hA hWN)
  have hredX : IsReduced (Spec (CommRingCat.of A)) := inferInstance
  obtain ⟨x, hx⟩ := hpow
  obtain ⟨y, hy⟩ := hlin
  let C := Polynomial A ⧸ Ideal.span
    {Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C (p : A) * Polynomial.X - Polynomial.C y}
  let B := integralClosure A (FractionRing A)
  let qMap := pPowerAlgebraToIntegralClosure A hp.pos x y z w hz hx.symm hy.symm
  let cX : Spec (.of C) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A C))
  have hC : UniversalHomeomorphism cX := by
    simpa [cX, C] using universalHomeomorphism_spec_quotient_of_pPower_mul x y p hp
      (natCast_pow_mul_eq_pow_of_isRegular hz hx hy)
  let eNorm := affineNormalizationIso A hA
  let fNorm := Scheme.normalization (Spec (.of A)) hA
  have hNormMap : eNorm.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = fNorm :=
    affineNormalizationIso_hom_map A hA
  let nC : Scheme.normalizationScheme (Spec (.of A)) hA ⟶ Spec (.of C) :=
    eNorm.hom ≫ Spec.map (CommRingCat.ofHom qMap.toRingHom)
  have hcompRing : CommRingCat.ofHom (algebraMap A C) ≫
      CommRingCat.ofHom qMap.toRingHom = CommRingCat.ofHom (algebraMap A B) := by
    ext a
    exact congrArg (fun v : B => (v : FractionRing A)) (qMap.commutes a)
  have hfac : nC ≫ cX = fNorm := by
    dsimp only [nC, cX]
    rw [Category.assoc, ← Spec.map_comp, hcompRing]
    exact hNormMap
  obtain ⟨k, -, hNk⟩ := exists_section_of_isWeaklyNormal A hA hWN nC cX hC hfac
  have hNk' : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ k =
      Spec.map (CommRingCat.ofHom qMap.toRingHom) := by
    apply (cancel_epi eNorm.hom).mp
    rw [← Category.assoc, hNormMap]
    exact hNk
  have hkRing : (algebraMap A B).comp (specHomRingHom k) = qMap.toRingHom := by
    have hh := congrArg specHomRingHom hNk'
    rwa [← specHomRingHom_comp, specHomRingHom_specMap, specHomRingHom_specMap] at hh
  let c := specHomRingHom k (Ideal.Quotient.mk _ Polynomial.X)
  have hcB : algebraMap A B c = qMap (Ideal.Quotient.mk _ Polynomial.X) := by
    simpa [c, RingHom.comp_apply] using
      congrArg (fun φ : C →+* B => φ (Ideal.Quotient.mk _ Polynomial.X)) hkRing
  have hcK : algebraMap A (FractionRing A) c =
      IsLocalization.mk' (FractionRing A) w ⟨z, isRegular_iff_mem_nonZeroDivisors.mp hz⟩ := by
    have hh := congrArg (fun v : B => (v : FractionRing A)) hcB
    rwa [pPowerAlgebraToIntegralClosure_X] at hh
  exact dvd_of_algebraMap_eq_mk' hz hcK

/-! ### Weak normality from the ring conditions -/

/-- A ring map landing in the image of an injective structure map, compatible with a map out
of the base, is split by the induced retraction. -/
private theorem exists_retraction_of_range {A D B : Type u} [CommRing A] [CommRing D]
    [CommRing B] [Algebra A B] (f : A →+* D) (g : D →+* B)
    (hinj : Function.Injective (algebraMap A B))
    (hrange : ∀ d : D, g d ∈ Set.range (algebraMap A B)) (hgf : g.comp f = algebraMap A B) :
    ∃ r : D →+* A, r.comp f = RingHom.id A ∧ (algebraMap A B).comp r = g := by
  refine ⟨rangeFactorRingHom g hinj hrange, ?_, algebraMap_comp_rangeFactorRingHom g hinj hrange⟩
  ext a
  apply hinj
  calc
    algebraMap A B (rangeFactorRingHom g hinj hrange (f a)) = g (f a) :=
      RingHom.congr_fun (algebraMap_comp_rangeFactorRingHom g hinj hrange) (f a)
    _ = algebraMap A B a := RingHom.congr_fun hgf a

/-- For a reduced affine scheme `Spec A`, the map to it from the spectrum of the integral closure
of `A` in its total ring of fractions is dominant. -/
private theorem isDominant_specMap_integralClosure (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    [IsReduced (Spec (.of A))] :
    IsDominant (Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))).op) := by
  have := isDominant_normalization_spec A hA
  have hcomp : IsDominant ((affineNormalizationIso A hA).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))) := by
    rw [affineNormalizationIso_hom_map A hA]
    infer_instance
  exact IsDominant.of_comp (affineNormalizationIso A hA).hom
    (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))))
    (H := hcomp)

/-- If the relative weak normalization of `A` in its integral closure is trivial, every affine
factorization of the normalization morphism through a universal homeomorphism admits a ring
retraction. -/
private theorem exists_retraction_of_relativeWeakNormalization_le_bot (A : Type u)
    [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    [IsReduced (Spec (.of A))]
    (hdom : IsDominant (Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))).op))
    (hRbot : relativeWeakNormalization A (integralClosure A (FractionRing A)) ≤ ⊥)
    {D : Type u} [CommRing D] (m : Scheme.normalizationScheme (Spec (.of A)) hA ⟶ Spec (.of D))
    (t : Spec (.of D) ⟶ Spec (.of A)) (ht : UniversalHomeomorphism t)
    (hfac : m ≫ t = Scheme.normalization (Spec (.of A)) hA) :
    ∃ g : D →+* A, g.comp (specHomRingHom t) = RingHom.id A ∧
      (algebraMap A (integralClosure A (FractionRing A))).comp g =
        specHomRingHom ((affineNormalizationIso A hA).inv ≫ m) := by
  let B := integralClosure A (FractionRing A)
  let fAD : A →+* D := specHomRingHom t
  let : Algebra A D := fAD.toAlgebra
  have hFmap : Spec.map (CommRingCat.ofHom (algebraMap A D)) = t := specMap_specHomRingHom t
  have hADuh : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A D)).op) := by
    change UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A D)))
    rwa [hFmap]
  let gDB : D →+* B := specHomRingHom ((affineNormalizationIso A hA).inv ≫ m)
  have hMapComp : ((affineNormalizationIso A hA).inv ≫ m) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) := by
    rw [Category.assoc, hfac, ← affineNormalizationIso_hom_map A hA, Iso.inv_hom_id_assoc]
  have hRingComp : gDB.comp fAD = algebraMap A B := by
    have hh := congrArg specHomRingHom hMapComp
    rwa [← specHomRingHom_comp, specHomRingHom_specMap] at hh
  let gAlg : D →ₐ[A] B :=
    { toRingHom := gDB
      commutes' := fun a => RingHom.congr_fun hRingComp a }
  exact exists_retraction_of_range fAD gDB (algebraMap_integralClosure_injective A) (fun d =>
    hRbot (range_le_relativeWeakNormalization A B D gAlg hdom hADuh ⟨d, rfl⟩)) hRingComp

/-- If the relative weak normalization of `A` in its integral closure is trivial, every
factorization of the normalization morphism through a universal homeomorphism with affine
middle is split by a section. -/
private theorem exists_section_of_relativeWeakNormalization_le_bot (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    [IsReduced (Spec (.of A))]
    (hdom : IsDominant (Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))).op))
    (hRbot : relativeWeakNormalization A (integralClosure A (FractionRing A)) ≤ ⊥)
    {M : Scheme.{u}} [IsAffine M] (m : Scheme.normalizationScheme (Spec (.of A)) hA ⟶ M)
    (t : M ⟶ Spec (.of A)) (ht : UniversalHomeomorphism t)
    (hfac : m ≫ t = Scheme.normalization (Spec (.of A)) hA) :
    ∃ β : Spec (.of A) ⟶ M, Scheme.normalization (Spec (.of A)) hA ≫ β = m ∧ β ≫ t = 𝟙 _ := by
  let eW : Spec (.of Γ(M, ⊤)) ≅ M := M.isoSpec.symm
  obtain ⟨g, hg, hgB⟩ := exists_retraction_of_relativeWeakNormalization_le_bot A hA hdom hRbot
    (m ≫ eW.inv) (eW.hom ≫ t)
    (universalHomeomorphism_hasTwoOutOfThreeProperty.toIsStableUnderComposition.comp_mem
      eW.hom t (universalHomeomorphism_of_isIso eW.hom) ht)
    (by rw [Category.assoc, Iso.inv_hom_id_assoc, hfac])
  have hFmap : Spec.map (CommRingCat.ofHom (specHomRingHom (eW.hom ≫ t))) = eW.hom ≫ t :=
    specMap_specHomRingHom _
  have hgm : Spec.map (CommRingCat.ofHom
      (specHomRingHom ((affineNormalizationIso A hA).inv ≫ m ≫ eW.inv))) =
      (affineNormalizationIso A hA).inv ≫ m ≫ eW.inv :=
    specMap_specHomRingHom _
  refine ⟨Spec.map (CommRingCat.ofHom g) ≫ eW.hom, ?_, ?_⟩
  · rw [← affineNormalizationIso_hom_map A hA]
    calc
      ((affineNormalizationIso A hA).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))) ≫
          Spec.map (CommRingCat.ofHom g) ≫ eW.hom =
          (affineNormalizationIso A hA).hom ≫
            (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) ≫
              Spec.map (CommRingCat.ofHom g)) ≫ eW.hom := by simp [Category.assoc]
      _ = (affineNormalizationIso A hA).hom ≫ Spec.map (CommRingCat.ofHom g ≫
          CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A)))) ≫ eW.hom := by
        rw [← Spec.map_comp]
      _ = (affineNormalizationIso A hA).hom ≫
          ((affineNormalizationIso A hA).inv ≫ m ≫ eW.inv) ≫ eW.hom := by
        rw [← CommRingCat.ofHom_comp, hgB, hgm]
      _ = m := by simp
  · rw [Category.assoc, ← hFmap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
    simp

/-- An affine scheme whose coordinate ring satisfies the two ring conditions is weakly
normal. -/
private theorem isWeaklyNormal_spec_of_isWeaklyNormalRing (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens,
      IsCompact (U : Set (Spec (.of A))) → (irreducibleComponents U).Finite)
    (hR : IsWeaklyNormalRing A) : Scheme.IsWeaklyNormal (Spec (.of A)) hA := by
  obtain ⟨hSemiA, hcrit⟩ := hR
  have hredA : _root_.IsReduced A := seminormalRing_isReduced hSemiA
  have : _root_.IsReduced ↥(CommRingCat.of A) := hredA
  have hredX : IsReduced (Spec (CommRingCat.of A)) := inferInstance
  let fNorm := Scheme.normalization (Spec (.of A)) hA
  have : IsDominant fNorm := isDominant_normalization_spec A hA
  have hdom := isDominant_specMap_integralClosure A hA
  let W := Scheme.weakNormalizationFactorization (Spec (.of A)) hA
  let hWinit := weakNormalizationFactorizationIsInitial fNorm
  have : IsIntegralHom W.toBase :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective
      W.toBase).mp W.universalHomeomorphism |>.1
  have : IsAffine W.middle := isAffine_of_isAffineHom W.toBase
  obtain ⟨βhom, hβMiddle, hβBase⟩ := exists_section_of_relativeWeakNormalization_le_bot A hA
    hdom (relativeWeakNormalization_le_bot hSemiA hcrit hdom) W.toMiddle W.toBase
    W.universalHomeomorphism W.fac
  let Fid : UniversalHomeomorphismFactorization fNorm :=
    ⟨Spec (CommRingCat.of A), fNorm, 𝟙 _, by simp,
      universalHomeomorphism_of_isIso (𝟙 (Spec (CommRingCat.of A)))⟩
  let α := hWinit.to Fid
  let β : Fid ⟶ W := ⟨βhom, hβMiddle, hβBase⟩
  have hαbase : α.hom = W.toBase := by simpa [Fid] using α.hom_toBase
  have hαβ : α.hom ≫ β.hom = 𝟙 W.middle :=
    congrArg (fun m : UniversalHomeomorphismFactorization.Hom W W => m.hom)
      (hWinit.hom_ext (α ≫ β) (𝟙 W))
  change IsIso W.toBase
  exact Iso.isIso_hom
    { hom := W.toBase, inv := β.hom, hom_inv_id := by rw [← hαbase]; exact hαβ,
      inv_hom_id := hβBase }

/-! ### The characterization -/

/-- **Stacks Project, Tag 0H3T.** An affine scheme with finitely many irreducible components
is weakly normal exactly when its coordinate ring is seminormal and satisfies the prime-power
divisibility condition for nonzerodivisors. -/
@[stacks 0H3T]
theorem isWeaklyNormal_spec_iff (A : Type u) [CommRing A]
    (hA : ∀ U : (Spec (.of A)).Opens, IsCompact (U : Set (Spec (.of A))) →
      (irreducibleComponents U).Finite) :
    Scheme.IsWeaklyNormal (Spec (.of A)) hA ↔ IsWeaklyNormalRing A :=
  ⟨fun hWN => ⟨isSeminormalRing_of_exists_sq_cube (exists_sq_cube_of_isWeaklyNormal A hA hWN),
      fun _ hp _ _ hz => dvd_of_isWeaklyNormal A hA hWN hp hz⟩,
    isWeaklyNormal_spec_of_isWeaklyNormalRing A hA⟩

end AlgebraicGeometry

end
