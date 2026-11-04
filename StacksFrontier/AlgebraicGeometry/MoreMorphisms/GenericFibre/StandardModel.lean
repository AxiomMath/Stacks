module

public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.KernelPolynomial
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.SeparatingBasis
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.LastVariable
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ModelPresentation

/-!
# The standard hypersurface model of a geometrically integral function field

Steps B, C and D(i) of the proof of Stacks Tag 0559, joined. Let `L/K` be a finitely generated
field extension which is geometrically reduced over `K` and such that `L ⊗[K] K̄` is a domain
for a field extension `K̄` of `K`. Then `L` is the function field of a hypersurface over `K`:
there are `n`, a family `v : Fin n → L` generating `L` over `K` and a polynomial
`Q : MvPolynomial (Fin n) K` generating the kernel of evaluation at `v`, with `Q` irreducible
even after coefficientwise extension to `K̄`, and with `L` a field of fractions of
`MvPolynomial (Fin n) K ⧸ (Q)`.

This is the join of the three steps. Step B
(`Algebra.exists_trdeg_primitive_separating_transcendence_basis`) produces a transcendence basis
`v ∘ Fin.castSucc` together with a primitive element `v (Fin.last r)`. Step C
(`IsFractionRing.exists_isPrimitive_irreducible_aeval_eq_zero_iff_dvd`) produces the generator
of the kernel of the one-variable evaluation over the polynomial ring in the basis. Step D(i)
transports it to the multivariate ring
(`MvPolynomial.ker_aeval_eq_span_finLastEquiv_symm`) and reads off the two properties of the
presentation (`MvPolynomial.irreducible_map_and_isFractionRing_of_ker_eq_span`).

## Main results

* `Algebra.exists_mvPolynomial_model_of_isDomain_tensor`: the model, with its absolute
  irreducibility and the identification of `L` as the fraction field of the quotient.

## Implementation notes

The base of Step C is the polynomial ring `MvPolynomial (Fin r) K` in the transcendence basis,
whose field of fractions is `FractionRing (MvPolynomial (Fin r) K)`. Rather than the
intermediate field `IntermediateField.adjoin K (Set.range (v ∘ Fin.castSucc))` over which Step B
states separability, the canonical `FractionRing` is used: the two are `K`-isomorphic
(`AlgebraicIndependent.aevalEquivField`), and the canonical one carries `IsFractionRing` by
instance, so only algebraicity of the primitive element — which comes from the transcendence
basis directly, by `IsTranscendenceBasis.isAlgebraic` — has to be transported.

Separability of the primitive element, which is the extra content Step B provides over a plain
primitive element, is not used: absolute irreducibility of `Q` is obtained in Step D from the
hypothesis that `L ⊗[K] K̄` is a domain, not from separability.

`NormalizedGCDMonoid (MvPolynomial (Fin r) K)` is supplied as a local instance, through
`UniqueFactorizationMonoid.toNormalizedGCDMonoid`: a polynomial ring over a field is a unique
factorization domain, and that is how `Polynomial.content` and `Polynomial.primPart`, on which
Step C rests, become available.

No Stacks tag is attached: Steps B, C and D are not themselves tags of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Steps B, C and D of the
  first proof
-/

@[expose] public section

open scoped TensorProduct

open MvPolynomial

universe u v w

namespace Algebra

/-- **Steps B, C and D(i) of Stacks Tag 0559.** Let `L` be a finitely generated field extension
of `K` which is geometrically reduced over `K`, and let `K̄` be a field extension of `K` such
that `L ⊗[K] K̄` is a domain. Then there are a natural number `n`, a family `v : Fin n → L`
generating `L` over `K`, and a nonzero `Q : MvPolynomial (Fin n) K` generating the kernel of
evaluation at `v`, such that the coefficientwise image of `Q` in `K̄[xᵢ]` is irreducible and `L`
is a field of fractions of `MvPolynomial (Fin n) K ⧸ (Q)`. -/
theorem exists_mvPolynomial_model_of_isDomain_tensor (K : Type u) [Field K] (L : Type v)
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L] [Algebra.IsGeometricallyReduced K L]
    (Kbar : Type w) [Field Kbar] [Algebra K Kbar] (hL : IsDomain (L ⊗[K] Kbar)) :
    ∃ (n : ℕ) (v : Fin n → L) (Q : MvPolynomial (Fin n) K),
      IntermediateField.adjoin K (Set.range v) = ⊤ ∧
      RingHom.ker (aeval v : MvPolynomial (Fin n) K →ₐ[K] L).toRingHom = Ideal.span {Q} ∧
      Q ≠ 0 ∧ Irreducible (Q.map (algebraMap K Kbar)) ∧
      ∀ φ : (MvPolynomial (Fin n) K ⧸ Ideal.span {Q}) →ₐ[K] L,
        φ.comp (Ideal.Quotient.mkₐ K (Ideal.span {Q})) =
            (aeval v : MvPolynomial (Fin n) K →ₐ[K] L) →
          letI := φ.toRingHom.toAlgebra
          IsFractionRing (MvPolynomial (Fin n) K ⧸ Ideal.span {Q}) L := by
  classical
  obtain ⟨r, v, -, htr, hadj, -⟩ :=
    Algebra.exists_trdeg_primitive_separating_transcendence_basis K L
  have hind : AlgebraicIndependent K (fun i : Fin r ↦ v i.castSucc) := htr.1
  have hinj : Function.Injective (aeval (fun i : Fin r ↦ v i.castSucc) :
      MvPolynomial (Fin r) K →ₐ[K] L) := algebraicIndependent_iff_injective_aeval.2 hind
  let : Algebra (MvPolynomial (Fin r) K) L :=
    (aeval (fun i : Fin r ↦ v i.castSucc) :
      MvPolynomial (Fin r) K →ₐ[K] L).toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin r) K) L :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      show algebraMap K L c = aeval (fun i : Fin r ↦ v i.castSucc) (C c)
      simp
  have : FaithfulSMul (MvPolynomial (Fin r) K) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let : Algebra (FractionRing (MvPolynomial (Fin r) K)) L :=
    (IsFractionRing.lift (g := (aeval (fun i : Fin r ↦ v i.castSucc) :
      MvPolynomial (Fin r) K →ₐ[K] L).toRingHom) hinj).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) L :=
    IsScalarTower.of_algebraMap_eq fun p ↦ (IsFractionRing.lift_algebraMap hinj p).symm
  -- The primitive element is algebraic over the polynomial ring in the transcendence basis.
  have halgR : IsAlgebraic (MvPolynomial (Fin r) K) (v (Fin.last r)) := by
    obtain ⟨p, hp0, hp⟩ := htr.isAlgebraic.isAlgebraic (v (Fin.last r))
    refine ⟨p.map (hind.aevalEquiv.symm : _ →+* MvPolynomial (Fin r) K), ?_, ?_⟩
    · exact Polynomial.map_ne_zero_iff hind.aevalEquiv.symm.injective |>.mpr hp0
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hp, Polynomial.aeval_def]
      congr 1
      refine RingHom.ext fun y ↦ ?_
      have h2 := hind.algebraMap_aevalEquiv (hind.aevalEquiv.symm y)
      rw [AlgEquiv.apply_symm_apply] at h2
      exact h2.symm
  have : IsIntegral (FractionRing (MvPolynomial (Fin r) K)) (v (Fin.last r)) :=
    (halgR.extendScalars
      (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin r) K)
        (FractionRing (MvPolynomial (Fin r) K)))).isIntegral
  let : StrongNormalizationMonoid (MvPolynomial (Fin r) K) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let : NormalizedGCDMonoid (MvPolynomial (Fin r) K) :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  -- Step C over that polynomial ring.
  obtain ⟨q, -, hqirr, -, -, hqker⟩ :=
    IsFractionRing.exists_isPrimitive_irreducible_aeval_eq_zero_iff_dvd
      (R := MvPolynomial (Fin r) K) (F := FractionRing (MvPolynomial (Fin r) K)) (L := L)
      ‹IsIntegral (FractionRing (MvPolynomial (Fin r) K)) (v (Fin.last r))›
  -- Step D(i): transport it to the multivariate polynomial ring.
  have hv : ∀ i : Fin r, algebraMap (MvPolynomial (Fin r) K) L (X i) = v i.castSucc := by
    intro i
    show aeval (fun j : Fin r ↦ v j.castSucc) (X i) = v i.castSucc
    simp
  have hker := MvPolynomial.ker_aeval_eq_span_finLastEquiv_symm v hv hqker
  have hQ0 : (finLastEquiv K r).symm q ≠ 0 := fun h ↦ hqirr.ne_zero (by
    have := congrArg (finLastEquiv K r) h
    simpa using this)
  have key := fun φ hφ ↦ MvPolynomial.irreducible_map_and_isFractionRing_of_ker_eq_span
    (Kbar := Kbar) v hadj hL hQ0 φ hφ hker
  refine ⟨r + 1, v, (finLastEquiv K r).symm q, hadj, hker, hQ0, ?_, fun φ hφ ↦ (key φ hφ).2⟩
  exact (key (Ideal.Quotient.liftₐ _ (aeval v) fun a ha ↦ by
    rw [← hker, RingHom.mem_ker] at ha; exact ha) (Ideal.Quotient.liftₐ_comp _ _ _)).1

end Algebra

end
