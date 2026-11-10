module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.ProjPrincipalCodimOne
public import StacksFrontier.AlgebraicGeometry.Meromorphic.NoEmbeddedPoints

/-!
# A codimension-one closed subscheme is cut out by one equation on every affine open

Let `i : Z ⟶ X` be a closed immersion of schemes with `Z` locally Noetherian. Assume `Z` has no
embedded points and that every irreducible component of `Z` has codimension one in `X`. This file
shows that on every affine open `U` of `X` the ideal `I = Ker(Γ(X, U) ⟶ Γ(Z, i⁻¹U))` cutting out
`Z` has the property that **all of its associated primes have height one**, and consequently that
`I` is principal as soon as `Γ(X, U)` is a Noetherian unique factorization domain.

The height statement is the geometric half of the dictionary the source uses: "no embedded
points" says that every associated prime of `I` is minimal over it, and "every irreducible
component has codimension one" says that those minimal primes have height one. Both halves are
read off in the chart at once by going through the point of `Z` that an associated prime of `I`
names.

## Main results

* `Stacks.RingTheory.AssociatedPrimes.comap_colon_bot_singleton`: the colon ideal of the kernel
  of a ring homomorphism is the contraction of the annihilator of the image.
* `Stacks.RingTheory.AssociatedPrimes.associatedPrime_map_of_surjective`: along a surjection, an
  associated prime of the kernel pushes forward to an associated prime of the target and pulls
  back to itself.
* `AlgebraicGeometry.height_eq_one_of_mem_associatedPrimes_ker_app`: **the height statement.**
* `AlgebraicGeometry.isPrincipal_ker_app_of_codimension_one`: over a Noetherian unique
  factorization domain of sections, the ideal of `Z` on the chart is principal.

## Implementation notes

An associated prime `p` of `I = Ker(φ)`, `φ = Γ(X, U) ⟶ Γ(Z, i⁻¹U)`, is handled by pushing it
forward to `q = p·Γ(Z, i⁻¹U)`, which is an associated prime of `Γ(Z, i⁻¹U)` as a module over
itself; `i⁻¹U` is affine because a closed immersion is affine. The point of `Z` named by `q` is
`hV.fromSpec q`, it is an associated point of `Z` by Tag 02OK part (1), hence — there being no
embedded points — the generic point of an irreducible component, and the codimension hypothesis
applies to it. The codimension of the closure of its image is the height of `p` by
`AlgebraicGeometry.codimension_closureSingleton_base`, the compatibility of the two charts being
Mathlib's `IsAffineOpen.comap_primeIdealOf_appLE`.

The instance `Module Γ(X, U) Γ(F, U)` is not found when `F` is written out as
`SheafOfModules.unit Z.ringCatSheaf`, only when it is a variable of type `Z.Modules`; the unit
sheaf is therefore introduced by `let`, which keeps the body available for zeta reduction so that
the associated-prime statement for `Γ(Z, i⁻¹U)` is accepted verbatim for `Γ(F, i⁻¹U)`.

## References

* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.RingTheory.AssociatedPrimes

/-- The colon ideal of the kernel of a ring homomorphism at an element is the contraction of the
annihilator of the image of that element. -/
theorem comap_colon_bot_singleton {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (x : A) :
    Ideal.comap φ (Submodule.colon (⊥ : Submodule B B) {φ x})
      = Submodule.colon (RingHom.ker φ : Submodule A A) {x} := by
  ext r
  simp only [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot,
    RingHom.mem_ker, map_mul]

/-- **Associated primes of a kernel, pushed along the surjection.** If `φ : A → B` is surjective
and `p` is an associated prime of `Ker φ`, then `p·B` is an associated prime of `B` as a module
over itself, and its contraction along `φ` is again `p`. -/
theorem associatedPrime_map_of_surjective {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : Function.Surjective φ) {p : Ideal A}
    (hp : p ∈ Submodule.associatedPrimes (RingHom.ker φ : Submodule A A)) :
    IsAssociatedPrime (p.map φ) B ∧ (p.map φ).comap φ = p := by
  obtain ⟨hpp, x, hx⟩ := hp
  have hker : RingHom.ker φ ≤ p := by
    intro r hr
    rw [hx]
    exact Ideal.le_radical (Submodule.mem_colon_singleton.mpr
      (by simpa [smul_eq_mul] using (RingHom.ker φ).mul_mem_right x hr))
  have hcomap : (p.map φ).comap φ = p := by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  refine ⟨⟨Ideal.map_isPrime_of_surjective hφ hker, φ x, ?_⟩, hcomap⟩
  have h1 : Ideal.comap φ ((Submodule.colon (⊥ : Submodule B B) {φ x}).radical) = p := by
    rw [Ideal.comap_radical, comap_colon_bot_singleton, ← hx]
  rw [← h1, Ideal.map_comap_of_surjective φ hφ]

end Stacks.RingTheory.AssociatedPrimes

namespace AlgebraicGeometry

open Stacks.RingTheory.AssociatedPrimes

/-- **The height statement for a codimension-one closed subscheme, read on an affine chart.**
If `Z` is a locally Noetherian closed subscheme of `X` without embedded points, all of whose
irreducible components have codimension one in `X`, then every associated prime of the ideal
`Ker(Γ(X, U) ⟶ Γ(Z, i⁻¹U))` cutting `Z` out over an affine open `U` has height one. -/
theorem height_eq_one_of_mem_associatedPrimes_ker_app
    {X Z : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z)
    (hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1)
    {U : X.Opens} (hU : IsAffineOpen U)
    {p : Ideal Γ(X, U)} (hp : p ∈ Submodule.associatedPrimes
      (RingHom.ker (i.app U).hom : Submodule Γ(X, U) Γ(X, U))) :
    p.height = 1 := by
  have hV : IsAffineOpen (i ⁻¹ᵁ U) := IsAffineHom.isAffine_preimage U hU
  have hNB : IsNoetherianRing Γ(Z, i ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨i ⁻¹ᵁ U, hV⟩
  have hφ : Function.Surjective (i.app U).hom := Scheme.Hom.app_surjective i U hU
  obtain ⟨hq, hcomap⟩ := associatedPrime_map_of_surjective hφ hp
  -- the point of `Z` named by the associated prime pushed into `Γ(Z, i⁻¹U)`
  set q : PrimeSpectrum Γ(Z, i ⁻¹ᵁ U) := ⟨p.map (i.app U).hom, hq.1⟩
  set x : Z := hV.fromSpec.base q with hxdef
  have hxV : x ∈ i ⁻¹ᵁ U := by
    change hV.fromSpec.base q ∈ ((i ⁻¹ᵁ U : Z.Opens) : Set Z)
    rw [← hV.range_fromSpec]
    exact ⟨q, rfl⟩
  have hprime : hV.primeIdealOf ⟨x, hxV⟩ = q := by
    apply hV.fromSpec.isOpenEmbedding.injective
    simpa [hxdef] using hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  -- it is an associated point of `Z`
  have hassoc : x ∈ Stacks.Divisors.schemeAssociatedPoints Z := by
    let F : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
    have hFp : IsAssociatedPrimeStacks (Γ(Z, i ⁻¹ᵁ U) : Type u) (Γ(F, i ⁻¹ᵁ U) : Type u)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
      rw [hprime]
      exact (isAssociatedPrimeStacks_iff_mem_associatedPrimes _).2 hq
    exact isAssociatedPoint_of_isAssociatedPrime_sections F (i ⁻¹ᵁ U) hV hxV hFp
  -- hence, there being no embedded points, the generic point of an irreducible component
  have hgen : closure ({x} : Set Z) ∈ irreducibleComponents Z :=
    (schemeAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints Z hno).le hassoc
  -- and the codimension of the closure of its image is the height of `p`
  have hpU : hU.primeIdealOf ⟨i.base x, hxV⟩ = ⟨p, hp.1⟩ := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE U hU (i ⁻¹ᵁ U) hV le_rfl hxV,
      Scheme.Hom.appLE_eq_app, hprime]
    exact PrimeSpectrum.ext hcomap
  have hfs : hU.fromSpec.base ⟨p, hp.1⟩ = i.base x := by
    rw [← hpU]
    exact hU.fromSpec_primeIdealOf ⟨i.base x, hxV⟩
  rw [← codimension_closureSingleton_base hU.fromSpec ⟨p, hp.1⟩, hfs]
  exact hcodim _ hgen x rfl

/-- **One equation for a codimension-one closed subscheme on an affine chart.** If `Z` is a
locally Noetherian closed subscheme of `X` without embedded points, all of whose irreducible
components have codimension one in `X`, and the sections of `X` over an affine open `U` form a
Noetherian unique factorization domain, then `Z` is cut out over `U` by a single equation. -/
theorem isPrincipal_ker_app_of_codimension_one
    {X Z : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z)
    (hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1)
    {U : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)] [IsNoetherianRing Γ(X, U)]
    [UniqueFactorizationMonoid Γ(X, U)] :
    (RingHom.ker (i.app U).hom).IsPrincipal :=
  Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one
    fun _ hp => height_eq_one_of_mem_associatedPrimes_ker_app i hno hcodim hU hp

end AlgebraicGeometry

end
