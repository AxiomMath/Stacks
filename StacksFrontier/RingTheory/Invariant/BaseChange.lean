module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.RingTheory.Invariant.Quotient
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples

/-!
# Invariants and extension of scalars

Let a finite group `G` act on a commutative ring `R` and let `A` be an algebra over the
invariant ring `R^G`.  Acting on the second factor of the scalar extension `A ⊗[R^G] R`, the
canonical ring map

  `ι : A → (A ⊗[R^G] R)^G`

is the object of study.  Every invariant tensor satisfies a monic polynomial of degree `|G|`
over `A`, and every element of `ker ι` satisfies `(X - C a) ^ |G| = X ^ |G|`; consequently `ι`
is integral, a homeomorphism on prime spectra, and purely inseparable on residue fields.  When
`A` is flat over `R^G`, `ι` is an isomorphism — the invariants commute with flat base change.

## Main results

* `FixedPoints.exists_monic_polynomial_and_pow_eq_of_invariant_tensorProduct` (Stacks 0BRG):
  the monic polynomial for every invariant tensor, and the polynomial identity for every
  element of `ker ι`.
* `FixedPoints.canonicalMap_to_invariants_bijective_of_flat_and_isIntegral_isHomeomorph`
  (Stacks 0BRH): bijectivity of `ι` in the flat case, and integrality, the homeomorphism on
  spectra and purely inseparable residue extensions in general.

## Implementation notes

The action on the tensor product is left abstract: any `MulSemiringAction G (A ⊗[R^G] R)`
satisfying the canonical formula `g • (a ⊗ₜ r) = a ⊗ₜ (g • r)` on pure tensors is allowed.
This pins the action used in the source without committing to an implementation.  The order of
the finite group is written `Nat.card G`, and an isomorphism of commutative rings is expressed
as bijectivity of the canonical ring homomorphism.

Stacks 0BRG is deduced from the corresponding statement for a quotient
(`StacksFrontier.RingTheory.Invariant.Quotient`) by presenting `A` as a quotient of a polynomial
algebra `MvPolynomial A R^G`: base change along `R^G → R` turns that presentation into a
presentation of `A ⊗[R^G] R`, and the fixed subring of `MvPolynomial A R` is
`MvPolynomial A R^G`, so the kernel of the presentation is an extended ideal `JR`.

## References

* [Stacks Project, Tag 0BRG](https://stacks.math.columbia.edu/tag/0BRG)
* [Stacks Project, Tag 0BRH](https://stacks.math.columbia.edu/tag/0BRH)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace FixedPoints

section Presentation

/-- The canonical presentation of an `S`-algebra `A` as a quotient of `MvPolynomial A S`. -/
private noncomputable def presentation
    (S A : Type*) [CommRing S] [CommRing A] [Algebra S A] :
    MvPolynomial A S →ₐ[S] A :=
  MvPolynomial.aeval id

private lemma presentation_surjective
    (S A : Type*) [CommRing S] [CommRing A] [Algebra S A] :
    Function.Surjective (presentation S A) := by
  intro a
  exact ⟨MvPolynomial.X a, by simp [presentation]⟩

/-- The base change of `presentation S A` along `S → R`, as a map to `A ⊗[S] R`. -/
private noncomputable def baseChangePresentation
    (S R A : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] :
    MvPolynomial A R →+* A ⊗[S] R :=
  MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : R →ₐ[S] A ⊗[S] R)
    fun a ↦ (a ⊗ₜ[S] (1 : R))

private lemma baseChangePresentation_surjective
    (S R A : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] :
    Function.Surjective (baseChangePresentation S R A) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨p + q, map_add _ _ _⟩
  | tmul a r =>
      refine ⟨MvPolynomial.X a * MvPolynomial.C r, ?_⟩
      simp [baseChangePresentation, Algebra.TensorProduct.includeRight_apply]

private lemma baseChangePresentation_map_smul
    (S R A G : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] [Group G] [MulSemiringAction G R]
    [MulSemiringAction G (A ⊗[S] R)]
    (smul_tmul : ∀ (g : G) (a : A) (r : R),
      g • (a ⊗ₜ[S] r) = a ⊗ₜ[S] (g • r))
    (g : G) (p : MvPolynomial A R) :
    baseChangePresentation S R A (g • p) =
      g • baseChangePresentation S R A p := by
  have action_eq_map (q : MvPolynomial A R) :
      g • q = MvPolynomial.map (MulSemiringAction.toRingHom G R g) q := rfl
  induction p using MvPolynomial.induction_on with
  | C r =>
      have hC : g • (MvPolynomial.C r : MvPolynomial A R) = MvPolynomial.C (g • r) := by
        rw [action_eq_map, MvPolynomial.map_C]
        rfl
      rw [hC]
      simp [baseChangePresentation, smul_tmul]
  | add p q hp hq => simp [map_add, hp, hq, smul_add]
  | mul_X p a hp =>
      have hX : g • (MvPolynomial.X a : MvPolynomial A R) = MvPolynomial.X a := by
        rw [action_eq_map, MvPolynomial.map_X]
      rw [action_eq_map, map_mul, ← action_eq_map, ← action_eq_map, hX,
        map_mul, hp]
      simp [baseChangePresentation, smul_tmul]

/-- The action of `G` on `MvPolynomial σ R` obtained by acting on the coefficients. -/
noncomputable local instance mvPolynomialAction
    (R G σ : Type*) [CommRing R] [Group G] [MulSemiringAction G R] :
    MulSemiringAction G (MvPolynomial σ R) :=
  { (inferInstance : DistribMulAction G (MvPolynomial σ R)) with
    smul_one := by
      intro g
      change MvPolynomial.map (MulSemiringAction.toRingHom G R g) 1 = 1
      exact map_one _
    smul_mul := by
      intro g p q
      change MvPolynomial.map (MulSemiringAction.toRingHom G R g) (p * q) =
        MvPolynomial.map (MulSemiringAction.toRingHom G R g) p *
        MvPolynomial.map (MulSemiringAction.toRingHom G R g) q
      exact map_mul _ _ _ }

/-- Coefficientwise inclusion `MvPolynomial σ R^G → (MvPolynomial σ R)^G`. -/
private noncomputable def fixedPolynomialMap
    (R G σ : Type*) [CommRing R] [Group G] [MulSemiringAction G R] :
    MvPolynomial σ (FixedPoints.subring R G) →+*
      FixedPoints.subring (MvPolynomial σ R) G :=
  RingHom.codRestrict (MvPolynomial.map (FixedPoints.subring R G).subtype)
    (FixedPoints.subring (MvPolynomial σ R) G) (by
      intro p g
      change MvPolynomial.map (MulSemiringAction.toRingHom G R g)
        (MvPolynomial.map (FixedPoints.subring R G).subtype p) =
        MvPolynomial.map (FixedPoints.subring R G).subtype p
      ext m
      simp only [MvPolynomial.coeff_map]
      exact (p.coeff m).2 g)

private lemma fixedPolynomialMap_surjective
    (R G σ : Type*) [CommRing R] [Group G] [MulSemiringAction G R] :
    Function.Surjective (fixedPolynomialMap R G σ) := by
  intro p
  have hp : (p.1.coeffs : Set R) ⊆ Set.range (FixedPoints.subring R G).subtype := by
    intro c hc
    rw [Finset.mem_coe] at hc
    rw [MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    refine ⟨⟨p.1.coeff m, ?_⟩, rfl⟩
    intro g
    have h := p.2 g
    change MvPolynomial.map (MulSemiringAction.toRingHom G R g) p.1 = p.1 at h
    have h' := congrArg (fun q : MvPolynomial σ R => q.coeff m) h
    simpa only [MvPolynomial.coeff_map, MulSemiringAction.toRingHom_apply] using h'
  obtain ⟨q, hq⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hp
  refine ⟨q, Subtype.ext ?_⟩
  exact hq

/-- The invariants of `MvPolynomial σ R` are the polynomials over `R^G`. -/
private noncomputable def fixedPolynomialEquiv
    (R G σ : Type*) [CommRing R] [Group G] [MulSemiringAction G R] :
    MvPolynomial σ (FixedPoints.subring R G) ≃+*
      FixedPoints.subring (MvPolynomial σ R) G :=
  RingEquiv.ofBijective (fixedPolynomialMap R G σ)
    ⟨fun _ _ h ↦ MvPolynomial.map_injective _ (FixedPoints.subring R G).subtype_injective
      (congrArg Subtype.val h), fixedPolynomialMap_surjective R G σ⟩

private lemma fixedPolynomialEquiv_apply
    (R G σ : Type*) [CommRing R] [Group G] [MulSemiringAction G R]
    (p : MvPolynomial σ (FixedPoints.subring R G)) :
    (fixedPolynomialEquiv R G σ p : MvPolynomial σ R) =
      MvPolynomial.map (FixedPoints.subring R G).subtype p := rfl

/-- Base change of the polynomial algebra: `MvPolynomial A S ⊗[S] R ≃+* MvPolynomial A R`. -/
private noncomputable def polyBaseChangeEquiv
    (S R A : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] :
    (MvPolynomial A S ⊗[S] R) ≃+* MvPolynomial A R :=
  (Algebra.TensorProduct.comm S (MvPolynomial A S) R).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv S R).toRingEquiv

private lemma polyBaseChangeEquiv_tmul
    (S R A : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] (p : MvPolynomial A S) (r : R) :
    polyBaseChangeEquiv S R A (p ⊗ₜ[S] r) =
      r • MvPolynomial.map (algebraMap S R) p := by
  simp [polyBaseChangeEquiv]

private lemma baseChangePresentation_map
    (S R A : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] (p : MvPolynomial A S) :
    baseChangePresentation S R A (MvPolynomial.map (algebraMap S R) p) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] R) (presentation S A p) := by
  induction p using MvPolynomial.induction_on with
  | C s =>
      simp [baseChangePresentation, presentation]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p a hp =>
      rw [map_mul, MvPolynomial.map_X, map_mul, hp, map_mul]
      simp [baseChangePresentation, presentation]

private lemma baseChangePresentation_tensorMap
    (S R A : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] (z : MvPolynomial A S ⊗[S] R) :
    baseChangePresentation S R A (polyBaseChangeEquiv S R A z) =
      Algebra.TensorProduct.map (presentation S A) (AlgHom.id S R) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul p r =>
      rw [polyBaseChangeEquiv_tmul, MvPolynomial.smul_eq_C_mul, map_mul,
        baseChangePresentation_map]
      simp [baseChangePresentation, Algebra.TensorProduct.tmul_mul_tmul]

/-- The kernel of `f` is the image under `e` of the kernel of `g`, when `f ∘ e = g`. -/
private lemma ker_eq_map_of_equiv_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : S →+* T) (g : R →+* T) (h : ∀ x, f (e x) = g x) :
    RingHom.ker f = Ideal.map e.toRingHom (RingHom.ker g) := by
  rw [show g = f.comp e.toRingHom from RingHom.ext fun x ↦ (h x).symm, ← RingHom.comap_ker]
  exact (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm

private lemma baseChangePresentation_ker
    (S R A : Type*) [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] :
    RingHom.ker (baseChangePresentation S R A) =
      Ideal.map (MvPolynomial.map (algebraMap S R))
        (RingHom.ker (presentation S A)) := by
  let e := polyBaseChangeEquiv S R A
  let f := presentation S A
  let t := Algebra.TensorProduct.map f (AlgHom.id S R)
  have ht :
      RingHom.ker t =
        Ideal.map (Algebra.TensorProduct.includeLeft :
          MvPolynomial A S →ₐ[S] MvPolynomial A S ⊗[S] R) (RingHom.ker f) :=
    Algebra.TensorProduct.rTensor_ker f (presentation_surjective S A)
  calc
    RingHom.ker (baseChangePresentation S R A) = Ideal.map e.toRingHom (RingHom.ker t) :=
      ker_eq_map_of_equiv_comp e _ _ (baseChangePresentation_tensorMap S R A)
    _ = Ideal.map e.toRingHom
        (Ideal.map (Algebra.TensorProduct.includeLeft :
          MvPolynomial A S →ₐ[S] MvPolynomial A S ⊗[S] R)
          (RingHom.ker f)) := by rw [ht]
    _ = Ideal.map (MvPolynomial.map (algebraMap S R)) (RingHom.ker f) := by
      show Ideal.map e.toRingHom
        (Ideal.map ((Algebra.TensorProduct.includeLeft :
          MvPolynomial A S →ₐ[S] MvPolynomial A S ⊗[S] R).toRingHom)
          (RingHom.ker f)) =
        Ideal.map (MvPolynomial.map (algebraMap S R)) (RingHom.ker f)
      rw [Ideal.map_map]
      apply congrArg (fun h : MvPolynomial A S →+* MvPolynomial A R =>
        Ideal.map h (RingHom.ker f))
      apply MvPolynomial.ringHom_ext
      · intro s
        show e (MvPolynomial.C s ⊗ₜ[S] (1 : R)) =
          MvPolynomial.map (algebraMap S R) (MvPolynomial.C s)
        rw [show e = polyBaseChangeEquiv S R A from rfl, polyBaseChangeEquiv_tmul]
        simp
      · intro a
        show e (MvPolynomial.X a ⊗ₜ[S] (1 : R)) =
          MvPolynomial.map (algebraMap S R) (MvPolynomial.X a)
        rw [show e = polyBaseChangeEquiv S R A from rfl, polyBaseChangeEquiv_tmul]
        simp

/-- The presentation of `A` read off from the invariants of `MvPolynomial A R`. -/
private noncomputable def fixedPolynomialEval
    (R G A : Type*) [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A] :
    FixedPoints.subring (MvPolynomial A R) G →+* A :=
  (presentation (FixedPoints.subring R G) A).toRingHom.comp
    (fixedPolynomialEquiv R G A).symm.toRingHom

private lemma fixedPolynomialEval_equiv
    (R G A : Type*) [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A]
    (p : MvPolynomial A (FixedPoints.subring R G)) :
    fixedPolynomialEval R G A (fixedPolynomialEquiv R G A p) =
      presentation (FixedPoints.subring R G) A p := by
  simp [fixedPolynomialEval]

private lemma fixedPolynomialEval_surjective
    (R G A : Type*) [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A] :
    Function.Surjective (fixedPolynomialEval R G A) := by
  intro a
  obtain ⟨p, hp⟩ := presentation_surjective (FixedPoints.subring R G) A a
  exact ⟨fixedPolynomialEquiv R G A p, (fixedPolynomialEval_equiv R G A p).trans hp⟩

private lemma fixedPolynomialEval_ker
    (R G A : Type*) [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A] :
    RingHom.ker (fixedPolynomialEval R G A) =
      Ideal.map (fixedPolynomialEquiv R G A).toRingHom
        (RingHom.ker (presentation (FixedPoints.subring R G) A)) := by
  exact ker_eq_map_of_equiv_comp _ _ _ (fixedPolynomialEval_equiv R G A)

private lemma baseChangePresentation_ker_eq_JRideal
    (R G A : Type*) [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A] :
    RingHom.ker (baseChangePresentation (FixedPoints.subring R G) R A) =
      Stacks.Invariant.QuotientComparison.JRideal (RingHom.ker (fixedPolynomialEval R G A)) := by
  rw [baseChangePresentation_ker, fixedPolynomialEval_ker]
  unfold Stacks.Invariant.QuotientComparison.JRideal
  show Ideal.map (MvPolynomial.map (algebraMap (FixedPoints.subring R G) R))
      (RingHom.ker (presentation (FixedPoints.subring R G) A)) =
    Ideal.map (FixedPoints.subring (MvPolynomial A R) G).subtype
      (Ideal.map (fixedPolynomialEquiv R G A).toRingHom
        (RingHom.ker (presentation (FixedPoints.subring R G) A)))
  rw [Ideal.map_map]
  apply congrArg (fun h : MvPolynomial A (FixedPoints.subring R G) →+*
      MvPolynomial A R =>
    Ideal.map h (RingHom.ker (presentation (FixedPoints.subring R G) A)))
  apply MvPolynomial.ringHom_ext
  · intro s
    simp only [RingHom.comp_apply, MvPolynomial.map_C]
    rw [show (fixedPolynomialEquiv R G A).toRingHom (MvPolynomial.C s) =
      fixedPolynomialEquiv R G A (MvPolynomial.C s) from rfl,
      show (FixedPoints.subring (MvPolynomial A R) G).subtype
        (fixedPolynomialEquiv R G A (MvPolynomial.C s)) =
        MvPolynomial.map (FixedPoints.subring R G).subtype (MvPolynomial.C s) from
          fixedPolynomialEquiv_apply R G A (MvPolynomial.C s),
      MvPolynomial.map_C]
    congr 1
  · intro a
    simp [fixedPolynomialEquiv_apply]

private lemma baseChangePresentation_fixed
    (R G A : Type*) [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A]
    (p : FixedPoints.subring (MvPolynomial A R) G) :
    baseChangePresentation (FixedPoints.subring R G) R A p.1 =
      (Algebra.TensorProduct.includeLeft :
        A →ₐ[(FixedPoints.subring R G)] A ⊗[(FixedPoints.subring R G)] R)
        (fixedPolynomialEval R G A p) := by
  obtain ⟨q, rfl⟩ := (fixedPolynomialEquiv R G A).surjective p
  rw [fixedPolynomialEquiv_apply, fixedPolynomialEval_equiv]
  exact baseChangePresentation_map (FixedPoints.subring R G) R A q

private lemma charpolyFixed_map_fixedPolynomialEval_of_mem
    (R G A : Type*) [CommRing R] [Group G] [Fintype G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A]
    (x : MvPolynomial A R)
    (hx : x ∈ Stacks.Invariant.QuotientComparison.JRideal
      (RingHom.ker (fixedPolynomialEval R G A))) :
    Polynomial.map (fixedPolynomialEval R G A) (Stacks.Invariant.QuotientComparison.charpolyFixed G
      x) =
      (Polynomial.X : Polynomial A) ^ Nat.card G := by
  classical
  let J := RingHom.ker (fixedPolynomialEval R G A)
  let e := (fixedPolynomialEval R G A).quotientKerEquivOfSurjective
    (fixedPolynomialEval_surjective R G A)
  have he : e.toRingHom.comp (Ideal.Quotient.mk J) =
      fixedPolynomialEval R G A := by
    ext p
    exact RingHom.quotientKerEquivOfSurjective_apply_mk
      (fixedPolynomialEval_surjective R G A) p
  have h := Stacks.Invariant.QuotientComparison.charpolyFixed_map_mk_of_mem J x hx
  calc
    Polynomial.map (fixedPolynomialEval R G A) (Stacks.Invariant.QuotientComparison.charpolyFixed G
      x) =
        Polynomial.map e.toRingHom
          (Polynomial.map (Ideal.Quotient.mk J) (Stacks.Invariant.QuotientComparison.charpolyFixed G
            x)) := by
            rw [Polynomial.map_map, he]
    _ = Polynomial.map e.toRingHom
        ((Polynomial.X : Polynomial (FixedPoints.subring (MvPolynomial A R) G ⧸ J)) ^
          Fintype.card G) := by rw [h]
    _ = (Polynomial.X : Polynomial A) ^ Nat.card G := by
      rw [Polynomial.map_pow, Polynomial.map_X, Nat.card_eq_fintype_card]

/-- **Stacks 0BRG.** Invariants in `A ⊗[R^G] R` lift to monic degree-`|G|` polynomial
relations over `A`; moreover, an element in the kernel of the canonical map from `A` to those
invariants satisfies `(X - C a) ^ |G| = X ^ |G|`.

Present `A` as a quotient of `MvPolynomial A R^G`.  Base change along `R^G → R` presents
`A ⊗[R^G] R` as the corresponding quotient of `MvPolynomial A R`, whose invariant subring is
`MvPolynomial A R^G` (`fixedPolynomialEquiv`), and the kernel of the base-changed presentation
is the extension `JR` of the kernel `J` of the original one
(`baseChangePresentation_ker_eq_JRideal`).  Both assertions are therefore the corresponding
assertions of Stacks 0H35 for `J`, transported along the presentation. -/
@[stacks 0BRG]
theorem exists_monic_polynomial_and_pow_eq_of_invariant_tensorProduct
    (R : Type u) [CommRing R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]
    (A : Type w) [CommRing A] [Algebra (FixedPoints.subring R G) A]
    [MulSemiringAction G (A ⊗[(FixedPoints.subring R G)] R)]
    (smul_tmul : ∀ (g : G) (a : A) (r : R),
      g • (a ⊗ₜ[(FixedPoints.subring R G)] r) = a ⊗ₜ[(FixedPoints.subring R G)] (g • r)) :
    let ι : A →+* FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G :=
      RingHom.codRestrict
        (Algebra.TensorProduct.includeLeftRingHom (R := FixedPoints.subring R G))
        (FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G)
        (fun a g => by
          simpa [Algebra.TensorProduct.includeLeftRingHom_apply] using smul_tmul g a 1)
    (∀ b : FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G,
      ∃ P : Polynomial A, P.Monic ∧
        Polynomial.map ι P = (Polynomial.X - Polynomial.C b) ^ Nat.card G) ∧
    ∀ a : A, a ∈ RingHom.ker ι →
      (Polynomial.X - Polynomial.C a) ^ Nat.card G =
        (Polynomial.X : Polynomial A) ^ Nat.card G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  intro ι
  have hcomm :
      ((FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G).subtype.comp ι).comp
        (fixedPolynomialEval R G A) =
      (baseChangePresentation (FixedPoints.subring R G) R A).comp
        (FixedPoints.subring (MvPolynomial A R) G).subtype := by
    ext p
    exact (baseChangePresentation_fixed R G A p).symm
  constructor
  · intro b
    obtain ⟨x, hx⟩ :=
      baseChangePresentation_surjective (FixedPoints.subring R G) R A b.1
    let Q := Stacks.Invariant.QuotientComparison.charpolyFixed G x
    refine ⟨Polynomial.map (fixedPolynomialEval R G A) Q,
      (Stacks.Invariant.QuotientComparison.charpolyFixed_monic x).map _, ?_⟩
    apply Polynomial.map_injective _
      (FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G).subtype_injective
    have hfix (g : G) :
        baseChangePresentation (FixedPoints.subring R G) R A (g • x) =
          (b : A ⊗[(FixedPoints.subring R G)] R) := by
      rw [baseChangePresentation_map_smul (FixedPoints.subring R G) R A G
        smul_tmul g x, hx]
      exact b.2 g
    calc
      Polynomial.map (FixedPoints.subring
          (A ⊗[(FixedPoints.subring R G)] R) G).subtype
          (Polynomial.map ι (Polynomial.map (fixedPolynomialEval R G A) Q)) =
        Polynomial.map (baseChangePresentation (FixedPoints.subring R G) R A)
          (Polynomial.map (FixedPoints.subring (MvPolynomial A R) G).subtype Q) := by
            simp only [Polynomial.map_map]
            rw [← RingHom.comp_assoc, hcomm]
      _ = Polynomial.map (baseChangePresentation (FixedPoints.subring R G) R A)
          (MulSemiringAction.charpoly G x) := by
            rw [Stacks.Invariant.QuotientComparison.charpolyFixed_map_subtype]
      _ = (Polynomial.X - Polynomial.C (b : A ⊗[(FixedPoints.subring R G)] R)) ^
          Nat.card G := by
            rw [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
            simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
            calc
              ∏ g : G, (Polynomial.X - Polynomial.C
                  (baseChangePresentation (FixedPoints.subring R G) R A (g • x))) =
                ∏ _g : G, (Polynomial.X - Polynomial.C
                  (b : A ⊗[(FixedPoints.subring R G)] R)) := by
                    apply Finset.prod_congr rfl
                    intro g _
                    rw [hfix g]
              _ = (Polynomial.X - Polynomial.C
                  (b : A ⊗[(FixedPoints.subring R G)] R)) ^ Nat.card G := by
                    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
      _ = Polynomial.map (FixedPoints.subring
          (A ⊗[(FixedPoints.subring R G)] R) G).subtype
          ((Polynomial.X - Polynomial.C b) ^ Nat.card G) := by
            simp
  · intro a ha
    obtain ⟨p, hp⟩ := fixedPolynomialEval_surjective R G A a
    have hx : (p : MvPolynomial A R) ∈
        Stacks.Invariant.QuotientComparison.JRideal (RingHom.ker (fixedPolynomialEval R G A)) := by
      rw [← baseChangePresentation_ker_eq_JRideal, RingHom.mem_ker,
        baseChangePresentation_fixed, hp]
      have hzero : ι a = 0 := RingHom.mem_ker.mp ha
      exact congrArg Subtype.val hzero
    have hcp := charpolyFixed_map_fixedPolynomialEval_of_mem R G A (p : MvPolynomial A R) hx
    rw [Stacks.Invariant.QuotientComparison.charpolyFixed_of_coe p, Polynomial.map_pow,
      Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, hp] at hcp
    simpa only [Nat.card_eq_fintype_card] using hcp

end Presentation

/-- **Stacks 0BRH.** The canonical map from a flat algebra over an invariant ring to the
invariants after extension of scalars is bijective.  In general, the map is integral, is a
homeomorphism on prime spectra, and induces purely inseparable residue field extensions.

The unconditional half follows from Stacks 0BRG: the monic witnesses generate the target over
`A`, and the kernel is nil, so
`PrimeSpectrum.isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_eq_top`
applies.  In the flat case `A ⊗[R^G] R → ∏_{g ∈ G} (A ⊗[R^G] R)` has `A` as the equalizer of
the two maps `r ↦ (g • r)` and `r ↦ r`, because taking equalizers commutes with a flat base
change. -/
@[stacks 0BRH]
theorem canonicalMap_to_invariants_bijective_of_flat_and_isIntegral_isHomeomorph
    (R : Type u) [CommRing R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]
    (A : Type w) [CommRing A] [Algebra (FixedPoints.subring R G) A]
    [MulSemiringAction G (A ⊗[(FixedPoints.subring R G)] R)]
    (smul_tmul : ∀ (g : G) (a : A) (r : R),
      g • (a ⊗ₜ[(FixedPoints.subring R G)] r) =
        a ⊗ₜ[(FixedPoints.subring R G)] (g • r)) :
    let ι : A →+* FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G :=
      RingHom.codRestrict
        (Algebra.TensorProduct.includeLeftRingHom (R := FixedPoints.subring R G))
        (FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G)
        (fun a g => by
          simpa [Algebra.TensorProduct.includeLeftRingHom_apply] using smul_tmul g a 1)
    (Module.Flat (FixedPoints.subring R G) A → Function.Bijective ι) ∧
      ι.IsIntegral ∧
      IsHomeomorph (PrimeSpectrum.comap ι) ∧
      ∀ (p : Ideal A) [p.IsPrime]
        (q : Ideal (FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G)) [q.IsPrime]
        (hpq : p = q.comap ι),
        (Ideal.ResidueField.map p q ι hpq).IsPurelyInseparable := by
  classical
  intro ι
  have hpoly :=
    exists_monic_polynomial_and_pow_eq_of_invariant_tensorProduct R G A smul_tmul
  let : Algebra A (FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G) := ι.toAlgebra
  have hker : RingHom.ker ι ≤ nilradical A := by
    intro a ha
    rw [mem_nilradical]
    refine ⟨2 * Nat.card G, ?_⟩
    have h := hpoly.2 a ha
    have he := congrArg (Polynomial.eval (0 : A)) h
    have he' : (-a) ^ Nat.card G = 0 := by
      simpa [zero_pow (Nat.card_pos (α := G)).ne'] using he
    have hsq : (-a) ^ (2 * Nat.card G) = 0 := by
      rw [mul_comm, pow_mul, he']; simp
    rwa [(even_two_mul (Nat.card G)).neg_pow] at hsq
  have hgen : Algebra.adjoin A
      {b : FixedPoints.subring (A ⊗[(FixedPoints.subring R G)] R) G |
        ∃ n > 0, ((Polynomial.X : Polynomial _) - Polynomial.C b) ^ n ∈
          Polynomial.lifts ι} = ⊤ := by
    rw [eq_top_iff]
    intro b _
    apply Algebra.subset_adjoin
    obtain ⟨P, hP, hmap⟩ := hpoly.1 b
    refine ⟨Nat.card G, Nat.card_pos, ?_⟩
    exact ⟨P, hmap⟩
  have hhome :=
    (PrimeSpectrum.isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_eq_top.{w,
      max u w, w, max u w}
      hker hgen).1
  have hpure :=
    (PrimeSpectrum.isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_eq_top.{w,
      max u w, w, max u w}
      hker hgen).2.1
  have hint : ι.IsIntegral := algebraMap_isIntegral_iff.mpr ⟨fun b => by
      obtain ⟨P, hP, hmap⟩ := hpoly.1 b
      refine ⟨P, hP, ?_⟩
      rw [show algebraMap A (FixedPoints.subring (A ⊗[FixedPoints.subring R G] R) G) = ι
        from rfl, ← Polynomial.eval_map, hmap]
      simp [zero_pow (Nat.card_pos (α := G)).ne']⟩
  refine ⟨?_, hint, hhome, hpure⟩
  intro hflat
  let : Module.Flat (FixedPoints.subring R G) A := hflat
  let f : R →ₗ[FixedPoints.subring R G] G → R :=
    { toFun := fun r g => g • r
      map_add' := fun x y => by ext g; simp
      map_smul' := fun s r => by
        ext g
        show g • ((s : R) * r) = (s : R) * (g • r)
        show (MulSemiringAction.toRingHom G R g) ((s : R) * r) = _
        rw [map_mul]
        show (g • (s : R)) * (g • r) = _
        rw [s.property g] }
  let d : R →ₗ[FixedPoints.subring R G] G → R :=
    { toFun := fun r _ => r
      map_add' := fun x y => rfl
      map_smul' := fun s r => rfl }
  let e : FixedPoints.subring R G ≃ₗ[FixedPoints.subring R G]
      LinearMap.eqLocus f d :=
    LinearEquiv.ofBijective
      ({ toFun := fun r : FixedPoints.subring R G =>
            (⟨r, by ext g; exact r.property g⟩ : LinearMap.eqLocus f d)
         map_add' := fun x y => by ext; simp
         map_smul' := fun s r => by ext; change ((s * r : FixedPoints.subring R G) : R) = _; rfl } :
        FixedPoints.subring R G →ₗ[FixedPoints.subring R G] LinearMap.eqLocus f d)
      ⟨fun x y h => Subtype.ext (by
          simpa using congrArg (fun z : LinearMap.eqLocus f d => (z : R)) h), fun x => by
        refine ⟨⟨x.1, fun g => ?_⟩, Subtype.ext rfl⟩
        exact congrFun x.property g⟩
  constructor
  · intro a₁ a₂ h
    apply (Algebra.TensorProduct.includeLeft_injective (R := FixedPoints.subring R G)
      (S := FixedPoints.subring R G) (A := A) (B := R)
      (fun _ _ h => Subtype.ext h))
    exact congrArg Subtype.val h
  · intro b
    have hb : (b : A ⊗[FixedPoints.subring R G] R) ∈
        LinearMap.eqLocus
          (TensorProduct.AlgebraTensorModule.lTensor A A f)
          (TensorProduct.AlgebraTensorModule.lTensor A A d) := by
      rw [LinearMap.mem_eqLocus]
      have := Fintype.ofFinite G
      refine (TensorProduct.piRight (R := FixedPoints.subring R G) (S := A) A
        (fun _ : G => R)).injective ?_
      ext g
      have hf : (TensorProduct.piRight (R := FixedPoints.subring R G) (S := A) A
          (fun _ : G => R)) ((TensorProduct.AlgebraTensorModule.lTensor A A f) b.1) g =
          g • b.1 := by
        induction b.1 using TensorProduct.induction_on with
        | zero => simp
        | tmul a r => simpa [f] using (smul_tmul g a r).symm
        | add x y hx hy => simpa [smul_add] using congrArg₂ (fun x y => x + y) hx hy
      have hd : (TensorProduct.piRight (R := FixedPoints.subring R G) (S := A) A
          (fun _ : G => R)) ((TensorProduct.AlgebraTensorModule.lTensor A A d) b.1) g =
          b.1 := by
        induction b.1 using TensorProduct.induction_on with
        | zero => simp
        | tmul a r => simp [d]
        | add x y hx hy => simpa using congrArg₂ (fun x y => x + y) hx hy
      rw [hf, hd]
      exact b.property g
    let z : A ⊗[FixedPoints.subring R G] LinearMap.eqLocus f d :=
      (LinearMap.tensorEqLocusEquiv A A f d).symm ⟨(b : A ⊗[FixedPoints.subring R G] R), hb⟩
    let a : A := TensorProduct.rid (FixedPoints.subring R G) A
      ((e.symm.lTensor A) z)
    refine ⟨a, Subtype.ext ?_⟩
    show Algebra.TensorProduct.includeLeftRingHom a =
      (b : A ⊗[FixedPoints.subring R G] R)
    have hz : (LinearMap.eqLocus f d).subtype.lTensor A z =
        (b : A ⊗[FixedPoints.subring R G] R) := by
      simp [z]
    rw [← hz]
    have ht (t : A ⊗[FixedPoints.subring R G] FixedPoints.subring R G) :
        Algebra.TensorProduct.includeLeftRingHom
            (TensorProduct.rid (FixedPoints.subring R G) A t) =
          (Algebra.linearMap (FixedPoints.subring R G) R).lTensor A t := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x r =>
          simp only [TensorProduct.rid_tmul, Algebra.TensorProduct.includeLeftRingHom_apply,
            LinearMap.lTensor_tmul, Algebra.linearMap_apply]
          simpa only [Algebra.smul_def, map_one, mul_one] using
            (TensorProduct.smul_tmul (R := FixedPoints.subring R G)
              (R' := FixedPoints.subring R G) (M := A) (N := R) r x (1 : R))
      | add x y hx hy =>
          simpa only [map_add, TensorProduct.add_tmul] using
            congrArg₂ (fun x y => x + y) hx hy
    rw [show a = TensorProduct.rid (FixedPoints.subring R G) A ((e.symm.lTensor A) z) from rfl,
      ht]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x r =>
        show x ⊗ₜ[FixedPoints.subring R G] ((e.symm r : FixedPoints.subring R G) : R) =
          x ⊗ₜ[FixedPoints.subring R G] (r : R)
        congr 1
        exact congrArg Subtype.val (e.apply_symm_apply r)
    | add x y hx hy => simpa using congrArg₂ (fun x y => x + y) hx hy

end FixedPoints
