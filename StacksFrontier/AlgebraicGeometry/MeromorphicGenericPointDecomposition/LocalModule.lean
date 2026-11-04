module

public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Local
public import StacksFrontier.RingTheory.Localization.PiOfSubmonoids

/-!
# The affine computation for a module at the generic points

Let `A` be a commutative ring all of whose zerodivisors lie in a minimal prime, with only
finitely many minimal primes. Tag 02LX, in the form
`isLocalization_pi_of_bijOn_minimalPrimes`, says that the product of the localizations of `A` at
its minimal primes is the total ring of fractions `Q(A)`. This file records the module-valued
form of that statement: for any `A`-module `M`, the product of the localizations of `M` at those
same primes is a localization of `M` at the nonzerodivisors, that is, `Q(A) ⊗_A M = ∏_i M_{𝔮_i}`.

This is the local input for part (2) of [Stacks, Tag 0EMF]: on an affine open `U = Spec A` of a
scheme whose weakly associated points are generic points of irreducible components, the minimal
primes of `A` are the generic points lying in `U`, the localizations of `A` at them are the local
rings there, and the displayed identity is the affine case of
`K_X(F)|_U = ∏_{η ∈ U} j_{η, *} F_η`.

## Main results

* `isLocalizedModule_pi_of_bijOn_minimalPrimes`: the module-valued form of Tag 02LX.

## Implementation notes

The statement mirrors `isLocalization_pi_of_bijOn_minimalPrimes` argument for argument: an
arbitrary finite indexing `q` of the minimal primes without repetition, an arbitrary choice `B i`
of localization of `A` at each of them, and here additionally an arbitrary choice `N i` of
localization of `M` at each of them. The reduction to the ring statement is
`isLocalizedModule_pi_of_isLocalization_pi`, whose hypothesis is exactly the ring statement.

The `B i` appear in the statement even though the conclusion does not mention them, because each
`N i` has to be a module over *some* localization of `A` at `q i` for the base-change argument to
run; in the geometric application that module is the stalk `𝒪_{X, η}` and the scalar tower is the
one supplied by `TopCat.Presheaf.algebra_section_stalk`.

## References

* [Stacks Project, Tag 02LX](https://stacks.math.columbia.edu/tag/02LX)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

universe u v w

variable {A : Type u} [CommRing A] {ι : Type v}
  {B : ι → Type w} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  {M : Type*} [AddCommGroup M] [Module A M]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
  [∀ i, Module (B i) (N i)] [∀ i, IsScalarTower A (B i) (N i)]

/-- **Stacks 02LX for a module.** Let `A` be a commutative ring whose zerodivisors all lie in
minimal primes, let `q : ι → Ideal A` be a finite enumeration without repetition of all the
minimal primes of `A`, and let `M` be an `A`-module. Then any family of localizations of `M` at
those primes has product a localization of `M` at the nonzerodivisors of `A`; equivalently
`Q(A) ⊗_A M = ∏_i M_{q i}`. -/
theorem isLocalizedModule_pi_of_bijOn_minimalPrimes
    (hzd : ∀ x : A, x ∉ nonZeroDivisors A → ∃ p ∈ minimalPrimes A, x ∈ p)
    [Finite ι] (q : ι → Ideal A) [∀ i, (q i).IsPrime]
    (hmem : ∀ i, q i ∈ minimalPrimes A) (hinj : Function.Injective q)
    (hsurj : ∀ p ∈ minimalPrimes A, ∃ i, q i = p)
    [∀ i, IsLocalization (q i).primeCompl (B i)]
    (f : ∀ i, M →ₗ[A] N i) [∀ i, IsLocalizedModule (q i).primeCompl (f i)] :
    IsLocalizedModule (nonZeroDivisors A) (LinearMap.pi f) :=
  isLocalizedModule_pi_of_isLocalization_pi (B := B) _ (fun i ↦ (q i).primeCompl)
    (isLocalization_pi_of_bijOn_minimalPrimes hzd q hmem hinj hsurj B) f
