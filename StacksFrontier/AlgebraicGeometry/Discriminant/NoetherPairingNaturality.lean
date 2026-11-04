module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Pairing
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleProduct
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationRefinement
public import StacksFrontier.AlgebraicGeometry.Discriminant.LocalAnnihilation

/-!
# The canonical pairing does not depend on the finite-open factorization

Let `A → B` be a quasi-finite map with `A` Noetherian. Two finite-open factorizations of `A → B`
have canonically isomorphic relative dualizing modules, by Tag 0BT1, and this file proves that the
canonical pairing of Tag 0BVP against the diagonal annihilator is carried to the canonical pairing
by that isomorphism.

## Main results

* `Stacks.Discriminant.mem_diagonalAnnihilator_of_mul_tmul_sub_eq_zero`: membership in the
  diagonal annihilator is tested on the differences `1 ⊗ c - c ⊗ 1`.
* `Stacks.Discriminant.tensorContract_mul_one_tmul`,
  `Stacks.Discriminant.tensorContract_mul_tmul_one` and `Stacks.Discriminant.tensorContract_map`:
  the contraction of a functional against the enveloping algebra is compatible with the two
  tensor factors and with a map of the algebra.
* `Stacks.Discriminant.noetherPairing_naturality`: the canonical pairing is independent of the
  finite-open factorization.

## Implementation notes

Two finite-open factorizations are compared through a common refinement whose intermediate
algebra injects into the target, as in Tag 0BT1, so it suffices to compare a factorization with
one that refines it. There the pairings are computed from two different decompositions of the
diagonal annihilator of the target, one over each intermediate algebra, and the two are related
by the conductor of the refinement: an element of the coarser intermediate algebra carrying the
finer one into it also carries the diagonal annihilator of the coarser one into that of the finer
one, by `Stacks.Discriminant.mul_map_mem_diagonalAnnihilator`.

The conductor elements generate the unit ideal of the target: near every prime the intermediate
algebra of a finite-open factorization agrees with the target, so a power of a suitable away
element lies in the conductor, uniformly in the finer algebra because it is a finite module. The
two pairings therefore agree on an ideal of the target containing `1`.

## References

* [Stacks Project, Tag 0BVP](https://stacks.math.columbia.edu/tag/0BVP)
* [Stacks Project, Tag 0BVR](https://stacks.math.columbia.edu/tag/0BVR)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w x

attribute [local instance] algebraDualModule

/-- An element of the diagonal annihilator kills the differences `1 ⊗ c - c ⊗ 1`. -/
private theorem mul_tmul_sub_eq_zero_of_mem_diagonalAnnihilator
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    {z : C ⊗[A] C} (hz : z ∈ diagonalAnnihilator A C) (c : C) :
    z * ((1 : C) ⊗ₜ[A] c - c ⊗ₜ[A] (1 : C)) = 0 := by
  have hmem : (1 : C) ⊗ₜ[A] c - c ⊗ₜ[A] (1 : C) ∈
      RingHom.ker (Algebra.TensorProduct.lmul' (R := A) (S := C)).toRingHom := by
    rw [RingHom.mem_ker]
    change (Algebra.TensorProduct.lmul' A) _ = 0
    simp [Algebra.TensorProduct.lmul'_apply_tmul]
  simpa only [smul_eq_mul] using (Submodule.mem_annihilator.mp hz) _ hmem

/-- On the diagonal annihilator the two tensor factors act in the same way. -/
theorem diagonalAnnihilator_mul_tmul_one_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) {z : B ⊗[A] B} (hz : z ∈ diagonalAnnihilator A B) :
    z * (b ⊗ₜ[A] (1 : B)) = z * ((1 : B) ⊗ₜ[A] b) := by
  exact (sub_eq_zero.mp (by simpa [mul_sub] using
    mul_tmul_sub_eq_zero_of_mem_diagonalAnnihilator hz b)).symm

/-- Multiplying by a scalar in the second tensor factor scales the contraction. -/
theorem tensorContract_mul_one_tmul
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    (f : Module.Dual A C) (c : C) (z : C ⊗[A] C) :
    tensorContract A C f (((1 : C) ⊗ₜ[A] c) * z) = c * tensorContract A C f z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [tensorContract]
  | tmul x y => simp [tensorContract, TensorProduct.lift.tmul]
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]

/-- Multiplying by a scalar in the first tensor factor acts on the functional. -/
theorem tensorContract_mul_tmul_one
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    (f : Module.Dual A C) (c : C) (z : C ⊗[A] C) :
    tensorContract A C f ((c ⊗ₜ[A] (1 : C)) * z) = tensorContract A C (c • f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [tensorContract]
  | tmul x y =>
      simp [tensorContract, TensorProduct.lift.tmul, algebraDualModule_smul_apply]
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add]

/-- Contraction is compatible with a map of the algebra: restricting the functional and
contracting over the smaller algebra agrees with mapping the tensor and contracting over the
larger one. -/
theorem tensorContract_map
    {A : Type u} {C : Type v} {D : Type w}
    [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (r : C →ₐ[A] D) (φ : Module.Dual A D) (z : C ⊗[A] C) :
    tensorContract A D φ (Algebra.TensorProduct.map r r z) =
      r (tensorContract A C (φ.comp r.toLinearMap) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [tensorContract]
  | tmul x y =>
      simp [tensorContract, TensorProduct.lift.tmul, Algebra.smul_def, r.commutes]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← map_add r,
        ← map_add (tensorContract A C (φ.comp r.toLinearMap))]

/-- The kernel of the multiplication map is generated by the differences `1 ⊗ c - c ⊗ 1`, so an
element of the enveloping algebra killing all of them lies in the diagonal annihilator. -/
theorem mem_diagonalAnnihilator_of_mul_tmul_sub_eq_zero
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    {z : C ⊗[A] C}
    (hz : ∀ c : C, z * ((1 : C) ⊗ₜ[A] c - c ⊗ₜ[A] (1 : C)) = 0) :
    z ∈ diagonalAnnihilator A C := by
  rw [diagonalAnnihilator, Submodule.mem_annihilator]
  intro x hx
  have hx' : x ∈ Ideal.span
      (Set.range fun c : C => (1 : C) ⊗ₜ[A] c - c ⊗ₜ[A] (1 : C)) := by
    rw [KaehlerDifferential.span_range_eq_ideal]
    have hx0 : (Algebra.TensorProduct.lmul' (R := A) (S := C)) x = 0 := RingHom.mem_ker.mp hx
    exact RingHom.mem_ker.mpr hx0
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      simpa only [smul_eq_mul] using hz c
  | zero => simp
  | add y₁ y₂ _ _ h₁ h₂ =>
      simp only [smul_eq_mul] at h₁ h₂ ⊢
      rw [mul_add, h₁, h₂, add_zero]
  | smul a y _ h =>
      simp only [smul_eq_mul] at h ⊢
      rw [mul_comm a y, ← mul_assoc, h, zero_mul]

/-- Multiplying the image of an element of the diagonal annihilator by a conductor element lands
back in the diagonal annihilator. A conductor element is one that carries the whole larger
algebra into the image of the smaller one, where the annihilator property is available. -/
private theorem mul_map_mem_diagonalAnnihilator
    {A : Type u} {C : Type v} {D : Type w}
    [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (r : C →ₐ[A] D) (g : C) (hg : ∀ d : D, ∃ c : C, r g * d = r c)
    {z : C ⊗[A] C} (hz : z ∈ diagonalAnnihilator A C) :
    (r g ⊗ₜ[A] (1 : D)) * Algebra.TensorProduct.map r r z ∈ diagonalAnnihilator A D := by
  set ζ := Algebra.TensorProduct.map r r z with hζdef
  have hkill : ∀ c : C, ζ * ((1 : D) ⊗ₜ[A] r c - r c ⊗ₜ[A] (1 : D)) = 0 := by
    intro c
    have h0 := mul_tmul_sub_eq_zero_of_mem_diagonalAnnihilator hz c
    have hζ := congrArg (Algebra.TensorProduct.map r r) h0
    rw [map_mul, map_zero, map_sub] at hζ
    simpa only [hζdef, Algebra.TensorProduct.map_tmul, map_one] using hζ
  have hg0 : ζ * (r g ⊗ₜ[A] (1 : D) - (1 : D) ⊗ₜ[A] r g) = 0 := by
    rw [show r g ⊗ₜ[A] (1 : D) - (1 : D) ⊗ₜ[A] r g =
      -(((1 : D) ⊗ₜ[A] r g) - r g ⊗ₜ[A] (1 : D)) by abel, mul_neg, hkill g, neg_zero]
  apply mem_diagonalAnnihilator_of_mul_tmul_sub_eq_zero
  intro d
  obtain ⟨c, hc⟩ := hg d
  have hc' : d * r g = r c := by rwa [mul_comm]
  have hsplit : (r g ⊗ₜ[A] (1 : D)) * ((1 : D) ⊗ₜ[A] d - d ⊗ₜ[A] (1 : D)) =
      ((1 : D) ⊗ₜ[A] d) * (r g ⊗ₜ[A] (1 : D) - (1 : D) ⊗ₜ[A] r g) +
        ((1 : D) ⊗ₜ[A] r c - r c ⊗ₜ[A] (1 : D)) := by
    simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hc, hc']
    abel
  calc (r g ⊗ₜ[A] (1 : D)) * ζ * ((1 : D) ⊗ₜ[A] d - d ⊗ₜ[A] (1 : D))
      = ζ * ((r g ⊗ₜ[A] (1 : D)) * ((1 : D) ⊗ₜ[A] d - d ⊗ₜ[A] (1 : D))) := by ring
    _ = ((1 : D) ⊗ₜ[A] d) * (ζ * (r g ⊗ₜ[A] (1 : D) - (1 : D) ⊗ₜ[A] r g)) +
          ζ * ((1 : D) ⊗ₜ[A] r c - r c ⊗ₜ[A] (1 : D)) := by
      rw [hsplit]
      ring
    _ = 0 := by
      rw [hg0, hkill c]
      ring

/-- On a finite module, pointwise membership in a submodule after multiplication by some power of
a scalar is membership after multiplication by one power of it. -/
private theorem exists_uniform_pow_smul_mem
    {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (g : R) (h : ∀ m : M, ∃ n : ℕ, g ^ n • m ∈ N) :
    ∃ n : ℕ, ∀ m : M, g ^ n • m ∈ N := by
  have hker : ∀ m : M, N.mkQ m = 0 ↔ m ∈ N := by
    intro m
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  obtain ⟨n, hn⟩ := Submodule.exists_uniform_pow_annihilator
    (⊤ : Submodule R (M ⧸ N)) (Module.finite_def.mp inferInstance) g (by
      intro q _
      obtain ⟨m, rfl⟩ := N.mkQ_surjective q
      obtain ⟨k, hk⟩ := h m
      exact ⟨k, by rwa [← map_smul, hker]⟩)
  refine ⟨n, fun m => ?_⟩
  have hq := hn (N.mkQ m) Submodule.mem_top
  rwa [← map_smul, hker] at hq

/-- Over a basic open contained in the image of the spectrum of the target, an element of a
refinement of the intermediate algebra comes from the intermediate algebra after multiplication
by a power of the localizing element. -/
private theorem exists_pow_mul_eq_map
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {D : Type x} [CommRing D] [Algebra A D] [Algebra D B]
    (r : F.middle →ₐ[A] D)
    (hr : ∀ c, algebraMap D B (r c) = algebraMap F.middle B c)
    (hD : Function.Injective (algebraMap D B))
    (g : F.middle)
    (haway : Function.Bijective (Localization.awayMap (algebraMap F.middle B) g))
    (d : D) : ∃ (n : ℕ) (c : F.middle), r (g ^ n) * d = r c := by
  classical
  let K := Localization.Away g
  let L := Localization.Away (algebraMap F.middle B g)
  have hmap : ∀ a : F.middle, Localization.awayMap (algebraMap F.middle B) g
      (algebraMap F.middle K a) = algebraMap B L (algebraMap F.middle B a) := by
    intro a
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  obtain ⟨z, hz⟩ := haway.2 (algebraMap B L (algebraMap D B d))
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj (S := K) g z
  have hpush := congrArg (Localization.awayMap (algebraMap F.middle B) g) hna
  rw [map_mul, map_pow, hz, hmap, hmap] at hpush
  have heq : algebraMap B L (algebraMap D B d * algebraMap F.middle B g ^ n) =
      algebraMap B L (algebraMap F.middle B a) := by
    rwa [map_mul, map_pow]
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := L)
    (algebraMap F.middle B g) heq
  refine ⟨m + n, g ^ m * a, hD ?_⟩
  have hL : algebraMap D B (r (g ^ (m + n)) * d) =
      algebraMap F.middle B g ^ (m + n) * algebraMap D B d := by
    rw [map_mul, hr, map_pow]
  have hR : algebraMap D B (r (g ^ m * a)) =
      algebraMap F.middle B g ^ m * algebraMap F.middle B a := by
    rw [hr, map_mul, map_pow]
  rw [hL, hR, pow_add]
  calc algebraMap F.middle B g ^ m * algebraMap F.middle B g ^ n * algebraMap D B d
      = algebraMap F.middle B g ^ m *
          (algebraMap D B d * algebraMap F.middle B g ^ n) := by ring
    _ = algebraMap F.middle B g ^ m * algebraMap F.middle B a := hm

/-- A refinement of the intermediate algebra of a finite-open factorization is carried into the
intermediate algebra by a single power of an admissible localizing element: the conductor of the
refinement contains a power of every element whose basic open lies in the image of the spectrum
of the target. -/
private theorem exists_pow_conductor
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (hH : Function.Injective (algebraMap H.middle B))
    (g : F.middle)
    (haway : Function.Bijective (Localization.awayMap (algebraMap F.middle B) g)) :
    ∃ n : ℕ, ∀ d : H.middle, ∃ c : F.middle, r (g ^ n) * d = r c := by
  let : Algebra F.middle H.middle := r.toRingHom.toAlgebra
  have hmapeq : (algebraMap F.middle H.middle) = r.toRingHom :=
    RingHom.algebraMap_toAlgebra r.toRingHom
  have : IsScalarTower A F.middle H.middle := IsScalarTower.of_algebraMap_eq' (by
    rw [hmapeq]
    ext a
    exact (r.commutes a).symm)
  have : Module.Finite F.middle H.middle :=
    Module.Finite.of_restrictScalars_finite A F.middle H.middle
  obtain ⟨n, hn⟩ := exists_uniform_pow_smul_mem
    (LinearMap.range (Algebra.linearMap F.middle H.middle)) g (by
      intro d
      obtain ⟨n, c, hc⟩ := exists_pow_mul_eq_map F r hr hH g haway d
      refine ⟨n, c, ?_⟩
      show algebraMap F.middle H.middle c = g ^ n • d
      rw [Algebra.smul_def, hmapeq]
      exact hc.symm)
  refine ⟨n, fun d => ?_⟩
  obtain ⟨c, hc⟩ := hn d
  refine ⟨c, ?_⟩
  have hc' : algebraMap F.middle H.middle c = g ^ n • d := hc
  rw [Algebra.smul_def, hmapeq] at hc'
  exact hc'.symm

/-- The canonical map from the base change of the diagonal annihilator, evaluated on a pure
tensor: it multiplies the image of the diagonal annihilator by the coefficient. -/
lemma diagonalAnnihilatorBaseChange_tmul_eq (A : Type u) (B' : Type v) (B : Type w)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (b : B) (j : ↑(diagonalAnnihilator A B')) :
    diagonalAnnihilatorBaseChange A B' B (b ⊗ₜ[B'] j) =
      (b ⊗ₜ[A] (1 : B)) *
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B' B)
          (IsScalarTower.toAlgHom A B' B) j.1 := by
  simp [diagonalAnnihilatorBaseChange, LinearMap.toSpanSingleton_apply, Algebra.smul_def]

/-- The action of the target on its enveloping algebra is multiplication by a pure tensor. -/
private lemma smul_eq_tmul_one_mul (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (x : B) (z : B ⊗[A] B) : x • z = (x ⊗ₜ[A] (1 : B)) * z := by
  rw [Algebra.smul_def]
  congr 1

/-- Contracting a functional on a refinement of the intermediate algebra against the image of an
element of the diagonal annihilator, scaled by a conductor element, is the contraction of the
restricted functional scaled by that element. -/
private theorem algebraMap_tensorContract_mul_map
    {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra C B] [Algebra D B]
    (r : C →ₐ[A] D) (hr : ∀ c, algebraMap D B (r c) = algebraMap C B c)
    (φ : Module.Dual A D) (g : C)
    {z : C ⊗[A] C} (hz : z ∈ diagonalAnnihilator A C) :
    algebraMap D B (tensorContract A D φ
        ((r g ⊗ₜ[A] (1 : D)) * Algebra.TensorProduct.map r r z)) =
      algebraMap C B g *
        algebraMap C B (tensorContract A C (φ.comp r.toLinearMap) z) := by
  have hfun : (r g • φ).comp r.toLinearMap = g • (φ.comp r.toLinearMap) := by
    ext y
    show φ (r g * r y) = φ (r (g * y))
    rw [map_mul r g y]
  have hstep : tensorContract A D φ
      ((r g ⊗ₜ[A] (1 : D)) * Algebra.TensorProduct.map r r z) =
      r (tensorContract A C (g • (φ.comp r.toLinearMap)) z) := by
    rw [tensorContract_mul_tmul_one, tensorContract_map, hfun]
  have hswap : (g ⊗ₜ[A] (1 : C)) * z = ((1 : C) ⊗ₜ[A] g) * z := by
    rw [mul_comm, diagonalAnnihilator_mul_tmul_one_eq g hz, mul_comm]
  have hcomm : tensorContract A C (g • (φ.comp r.toLinearMap)) z =
      g * tensorContract A C (φ.comp r.toLinearMap) z := by
    rw [← tensorContract_mul_tmul_one, hswap, tensorContract_mul_one_tmul]
  rw [hstep, hcomm, hr, map_mul]

/-- The pairing of a refinement and the pairing of the intermediate algebra agree on the
multiples of the image of a conductor element. This is the one place the conductor is used: it
converts the decomposition of an element of the diagonal annihilator over the intermediate
algebra into one over the refinement. -/
private theorem noetherPairing_conductor_smul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (g : F.middle) (hg : ∀ d : H.middle, ∃ c : F.middle, r g * d = r c)
    (φ : Module.Dual A H.middle) (b : B) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing H (dualizingModule.tmul H φ b)
        (algebraMap F.middle B g • j) =
      noetherPairing F (dualizingModule.tmul F (φ.comp r.toLinearMap) b)
        (algebraMap F.middle B g • j) := by
  classical
  have hcomp : (IsScalarTower.toAlgHom A H.middle B).comp r =
      IsScalarTower.toAlgHom A F.middle B := AlgHom.ext hr
  have hmapcomp : ∀ t : F.middle ⊗[A] F.middle,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A H.middle B)
          (IsScalarTower.toAlgHom A H.middle B) (Algebra.TensorProduct.map r r t) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom A F.middle B)
          (IsScalarTower.toAlgHom A F.middle B) t := by
    intro t
    rw [← hcomp, Algebra.TensorProduct.map_comp]
    rfl
  have hopen := specMap_ulift_isOpenImmersion (algebraMap F.middle B)
    F.isOpenEmbedding_comap F.awayMap_bijective
  have hRange := range_diagonalAnnihilatorBaseChange A F.middle B hopen
  let ψ := diagonalAnnihilatorBaseChange A F.middle B
  let ψJ : B ⊗[F.middle] (↑(diagonalAnnihilator A F.middle)) →ₗ[B]
      (↑(diagonalAnnihilator A B)) :=
    ψ.codRestrict ((diagonalAnnihilator A B).restrictScalars B) (by
      intro z
      show ψ z ∈ (diagonalAnnihilator A B).restrictScalars B
      rw [← hRange]
      exact ⟨z, rfl⟩)
  have hsurj : Function.Surjective ψJ := by
    intro j₀
    obtain ⟨z, hz⟩ : j₀.1 ∈ LinearMap.range ψ := by
      rw [hRange]
      exact j₀.2
    exact ⟨z, Subtype.ext hz⟩
  obtain ⟨w, rfl⟩ := hsurj j
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero, map_zero, map_zero]
  | add w₁ w₂ h₁ h₂ => rw [map_add, smul_add, map_add, map_add, h₁, h₂]
  | tmul y j' =>
      have hζ : (r g ⊗ₜ[A] (1 : H.middle)) * Algebra.TensorProduct.map r r j'.1 ∈
          diagonalAnnihilator A H.middle :=
        mul_map_mem_diagonalAnnihilator r g hg j'.2
      have hbase : (algebraMap F.middle B g • ψJ (y ⊗ₜ[F.middle] j')).1 =
          (algebraMap F.middle B g ⊗ₜ[A] (1 : B)) * ((y ⊗ₜ[A] (1 : B)) *
            Algebra.TensorProduct.map (IsScalarTower.toAlgHom A F.middle B)
              (IsScalarTower.toAlgHom A F.middle B) j'.1) := by
        show algebraMap F.middle B g • (ψ (y ⊗ₜ[F.middle] j')) = _
        rw [show ψ (y ⊗ₜ[F.middle] j') = diagonalAnnihilatorBaseChange A F.middle B
          (y ⊗ₜ[F.middle] j') from rfl, diagonalAnnihilatorBaseChange_tmul_eq,
          smul_eq_tmul_one_mul]
      have hjF : (algebraMap F.middle B g • ψJ (y ⊗ₜ[F.middle] j')).1 =
          diagonalAnnihilatorBaseChange A F.middle B
            ((algebraMap F.middle B g * y) ⊗ₜ[F.middle] j') := by
        rw [hbase, diagonalAnnihilatorBaseChange_tmul_eq,
          show (algebraMap F.middle B g * y) ⊗ₜ[A] (1 : B) =
            (algebraMap F.middle B g ⊗ₜ[A] (1 : B)) * (y ⊗ₜ[A] (1 : B)) by
              rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
        ring
      have hjH : (algebraMap F.middle B g • ψJ (y ⊗ₜ[F.middle] j')).1 =
          diagonalAnnihilatorBaseChange A H.middle B
            (y ⊗ₜ[H.middle] (⟨_, hζ⟩ : ↑(diagonalAnnihilator A H.middle))) := by
        rw [hbase, diagonalAnnihilatorBaseChange_tmul_eq]
        show _ = (y ⊗ₜ[A] (1 : B)) *
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom A H.middle B)
            (IsScalarTower.toAlgHom A H.middle B)
            ((r g ⊗ₜ[A] (1 : H.middle)) * Algebra.TensorProduct.map r r j'.1)
        rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, hmapcomp,
          show (IsScalarTower.toAlgHom A H.middle B) (r g) =
            algebraMap F.middle B g from hr g]
        ring
      rw [noetherPairing_apply_of_eq_baseChange H φ b y ⟨_, hζ⟩ _ hjH,
        noetherPairing_apply_of_eq_baseChange F (φ.comp r.toLinearMap) b
          (algebraMap F.middle B g * y) j' _ hjF,
        show (⟨_, hζ⟩ : ↑(diagonalAnnihilator A H.middle)).1 =
          (r g ⊗ₜ[A] (1 : H.middle)) * Algebra.TensorProduct.map r r j'.1 from rfl,
        algebraMap_tensorContract_mul_map r hr φ g j'.2]
      ring

/-- The pairing of a refinement of the intermediate algebra agrees with the pairing of the
intermediate algebra on a pure tensor of the dualizing module. The conductor elements of the
refinement generate the unit ideal of the target, because near every prime the intermediate
algebra agrees with the target. -/
private theorem noetherPairing_refinement_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (hH : Function.Injective (algebraMap H.middle B))
    (φ : Module.Dual A H.middle) (b : B) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing H (dualizingModule.tmul H φ b) j =
      noetherPairing F (dualizingModule.tmul F (φ.comp r.toLinearMap) b) j := by
  classical
  let t : B := noetherPairing H (dualizingModule.tmul H φ b) j -
    noetherPairing F (dualizingModule.tmul F (φ.comp r.toLinearMap) b) j
  let D : Ideal B := (Submodule.span B {t}).annihilator
  have hmem : ∀ g : F.middle, (∀ d : H.middle, ∃ c : F.middle, r g * d = r c) →
      algebraMap F.middle B g ∈ D := by
    intro g hg
    rw [Submodule.mem_annihilator_span_singleton]
    have h := noetherPairing_conductor_smul F H r hr g hg φ b j
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    rw [smul_eq_mul, mul_sub, h, sub_self]
  have htop : D = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal D hne
    let q : PrimeSpectrum B := ⟨M, hM.isPrime⟩
    let p := PrimeSpectrum.comap (algebraMap F.middle B) q
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hg⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
        (show p ∈ Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) from ⟨q, rfl⟩)
        F.isOpenEmbedding_comap.isOpen_range
    have hfg : algebraMap F.middle B g ∉ q.asIdeal := by
      simpa [p, PrimeSpectrum.comap_asIdeal] using hpg
    obtain ⟨n, hn⟩ := exists_pow_conductor F H r hr hH g (F.awayMap_bijective g hg)
    have hpow : algebraMap F.middle B g ^ n ∈ M := by
      simpa only [map_pow] using hle (hmem (g ^ n) hn)
    exact hfg (hM.isPrime.mem_of_pow_mem n hpow)
  have h1 : (1 : B) ∈ D := htop ▸ Submodule.mem_top
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, one_mul] at h1
  exact sub_eq_zero.mp h1

/-- The pairing of a refinement of the intermediate algebra is carried to the pairing of the
intermediate algebra by the canonical comparison of relative dualizing modules. -/
private theorem noetherPairing_refinement
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (hH : Function.Injective (algebraMap H.middle B))
    (ω : dualizingModule H) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing F (dualizingModuleEquiv H F ω) j = noetherPairing H ω j := by
  induction ω using dualizingModule.induction_on with
  | zero => rw [map_zero (dualizingModuleEquiv H F), map_zero, map_zero]
  | tmul φ b =>
      rw [dualizingModuleEquiv_from_injective H F hH r hr φ b]
      exact (noetherPairing_refinement_tmul F H r hr hH φ b j).symm
  | add ω₁ ω₂ h₁ h₂ =>
      rw [map_add (dualizingModuleEquiv H F), map_add, map_add,
        LinearMap.add_apply, LinearMap.add_apply, h₁, h₂]

/-- **Stacks Project, Tag 0BVP (independence of factorization).** The canonical pairing between
the relative dualizing module and the diagonal annihilator does not depend on the finite-open
factorization: the comparison of dualizing modules of Tag 0BT1 carries one pairing to the
other. -/
@[stacks 0BVP "independence of factorization"]
theorem noetherPairing_naturality
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (ω : dualizingModule F) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing G (dualizingModuleEquiv F G ω) j = noetherPairing F ω j := by
  obtain ⟨H, rF, rG, hinj, hF, hG⟩ := exists_common_finite_open_factorization F G
  obtain ⟨η, rfl⟩ := (dualizingModuleEquiv H F).surjective ω
  rw [show dualizingModuleEquiv F G (dualizingModuleEquiv H F η) =
      dualizingModuleEquiv H G η from
    DFunLike.congr_fun (dualizingModuleEquiv_trans H F G) η,
    noetherPairing_refinement G H rG hG hinj η j,
    noetherPairing_refinement F H rF hF hinj η j]

end Stacks.Discriminant
