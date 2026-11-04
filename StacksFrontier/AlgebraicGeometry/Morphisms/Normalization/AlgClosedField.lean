module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

/-!
# The normalization of an affine scheme in the spectrum of an algebraically closed field

Let `S'` be an affine scheme and `g : Spec K ⟶ S'` a morphism from the spectrum of an
algebraically closed field. Write `A = Γ(S', ⊤)` and `φ : A ⟶ K` for the ring map of `g`. The
normalization of `S'` in `Spec K` is `S'' = Spec B` where `B ⊆ K` is the integral closure of `A`
in `K`. It has the properties [Stacks, Tag 0F08] asks of the base it replaces `S'` by:

* `S''` is affine and integral, `B` being a subring of a field;
* `Γ(S'', ⊤) ≅ B` is a normal domain, the integral closure of a ring in a field being integrally
  closed;
* the function field `Frac(B)` of `S''` is algebraically closed: it is the algebraic closure in
  `K` of the fraction field of the image of `A`, because an element of `K` algebraic over
  `Frac(B)` has a nonzero multiple in `B`;
* `S'' ⟶ S'` is integral and `g` factors through it by a dominant morphism `Spec K ⟶ S''`,
  the inclusion `B ⊆ K` being injective.

## Main results

* `IsFractionRing.isAlgClosed_of_integrallyClosedIn` — a domain integrally closed in an
  algebraically closed field has an algebraically closed fraction field.
* `AlgebraicGeometry.exists_normalization_of_isAlgClosed` — the normalization of an affine scheme
  in the spectrum of an algebraically closed field, with the properties listed above.

## References

* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open CategoryTheory

universe u

/-- **A domain integrally closed in an algebraically closed field has an algebraically closed
fraction field.** Let `R ⟶ K` be injective with `K` algebraically closed, and suppose every
element of `K` integral over `R` comes from `R`. Then the fraction field `L` of `R` is
algebraically closed: a root `x ∈ K` of a polynomial over `L` is algebraic over `R`, so some
nonzero `r ∈ R` makes `r • x` integral over `R`, hence the image of some `s ∈ R`, and `x` is the
image of `s / r ∈ L`. -/
theorem IsFractionRing.isAlgClosed_of_integrallyClosedIn (R K L : Type*) [CommRing R]
    [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (hcl : ∀ x : K, _root_.IsIntegral R x → ∃ r : R, algebraMap R K r = x)
    [Field L] [Algebra R L] [IsFractionRing R L] : IsAlgClosed L := by
  let ι : L →+* K := IsFractionRing.lift (A := R) (K := L) hinj
  have hι : ∀ r : R, ι (algebraMap R L r) = algebraMap R K r := fun r ↦
    IsFractionRing.lift_algebraMap (A := R) (K := L) hinj r
  refine IsAlgClosed.of_exists_root L fun p hmon hirr ↦ ?_
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map ι)
    (by simpa using (Polynomial.degree_pos_of_irreducible hirr).ne')
  let : Algebra L K := ι.toAlgebra
  have : IsScalarTower R L K := IsScalarTower.of_algebraMap_eq fun r ↦ (hι r).symm
  have hxL : IsAlgebraic L x := ⟨p, hmon.ne_zero, by
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map]⟩
  have : Algebra.IsAlgebraic R L := IsLocalization.isAlgebraic L (nonZeroDivisors R)
  obtain ⟨r, hr0, hrint⟩ := (hxL.restrictScalars R).exists_integral_multiple
  obtain ⟨s, hs⟩ := hcl _ hrint
  refine ⟨algebraMap R L s / algebraMap R L r, ?_⟩
  apply ι.injective
  rwa [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_div₀, hι, hι, hs,
    Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).2 hr0)]

namespace AlgebraicGeometry

/-- **The normalization of an affine scheme in the spectrum of an algebraically closed field.**
Let `S'` be affine and `g : Spec K ⟶ S'` with `K` algebraically closed. There are an affine,
integral scheme `S''` whose ring of global sections is a normal domain and whose function field
is algebraically closed, an integral morphism `π : S'' ⟶ S'` and a dominant morphism
`g' : Spec K ⟶ S''` with `g' ≫ π = g`. The scheme `S''` is the spectrum of the integral closure
of `Γ(S', ⊤)` in `K`. -/
theorem exists_normalization_of_isAlgClosed {S' : Scheme.{u}} [IsAffine S'] (K : Type u)
    [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S') :
    ∃ (S'' : Scheme.{u}) (_ : IsAffine S'') (_ : IsIntegral S'')
      (_ : IsNormalDomain Γ(S'', ⊤)) (_ : IsAlgClosed S''.functionField)
      (π : S'' ⟶ S') (_ : IsIntegralHom π) (g' : Spec (.of K) ⟶ S'') (_ : IsDominant g'),
      g' ≫ π = g := by
  let φ : Γ(S', ⊤) ⟶ CommRingCat.of K := g.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  let : Algebra Γ(S', ⊤) K := φ.hom.toAlgebra
  let B := integralClosure Γ(S', ⊤) K
  let ιB : CommRingCat.of B ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap B K)
  let α : Γ(S', ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap Γ(S', ⊤) B)
  have hφ : α ≫ ιB = φ := rfl
  have hg : g = Spec.map φ ≫ S'.isoSpec.inv := by
    rw [Iso.eq_comp_inv, ← Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp]
  have : IsIntegrallyClosed B :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (R := B) (S := K)
  refine ⟨Spec (.of B), inferInstance, inferInstance, ?_, ?_, Spec.map α ≫ S'.isoSpec.inv, ?_,
    Spec.map ιB, ?_, ?_⟩
  · let e : B ≃+* Γ(Spec (.of B), ⊤) := (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
    have : IsDomain Γ(Spec (.of B), ⊤) := e.symm.toMulEquiv.isDomain
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩
  · have hcl : ∀ x : K, _root_.IsIntegral (integralClosure Γ(S', ⊤) K) x →
        _root_.IsIntegral Γ(S', ⊤) x := fun x hx ↦ isIntegral_trans x hx
    have : IsDomain (CommRingCat.of B) := inferInstanceAs (IsDomain B)
    let : Algebra (CommRingCat.of B) (Spec (CommRingCat.of B)).functionField :=
      instAlgebraCarrierFunctionFieldSpec _
    have := functionField_isFractionRing_of_affine (CommRingCat.of B)
    let : Algebra (CommRingCat.of B) K := ιB.hom.toAlgebra
    exact IsFractionRing.isAlgClosed_of_integrallyClosedIn (CommRingCat.of B) K
      (Spec (CommRingCat.of B)).functionField Subtype.val_injective
      fun x hx ↦ ⟨⟨x, hcl x hx⟩, rfl⟩
  · have : IsIntegralHom (Spec.map α) := by
      rw [IsIntegralHom.SpecMap_iff]
      exact integralClosure.AlgebraIsIntegral.isIntegral
    infer_instance
  · constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap B K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B K)]
    exact bot_le
  · rw [← Category.assoc, ← Spec.map_comp, hφ, hg]

end AlgebraicGeometry
