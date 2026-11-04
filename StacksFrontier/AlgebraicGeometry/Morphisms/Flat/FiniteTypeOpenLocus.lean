module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.WeaklyAssociatedLocallyFinite

/-!
# The pointwise flat locus of a morphism of finite type

For a morphism of schemes locally of finite presentation the set of points at which it is flat
is open (`AlgebraicGeometry.isOpen_setOf_isFlatAt`). For a morphism only locally of finite type
this can fail, and openness becomes a condition on the base: it holds when the weakly associated
points of the base are locally finite.

This file reduces that statement to its affine form, a question about rings. On compatible
affine opens `x ∈ V ⊆ f⁻¹(U)` the morphism is flat at `x` exactly when the localization of
`Γ(X, V)` at the prime of `x` is flat over `Γ(S, U)`, and `Γ(S, U)` has finitely many weakly
associated primes as soon as `U` sits inside an open meeting the weakly associated points of the
base in a finite set. So openness of the flat locus on each such chart, which is openness of a
relative flat locus in the spectrum of a finite type algebra, gives openness on all of `X`.

Flatness of the restriction to an open subscheme of the flat locus needs no hypothesis at all
and is `AlgebraicGeometry.flat_of_subset_setOf_isFlatAt`.

## Main results

* `AlgebraicGeometry.isOpen_setOf_isFlatAt_of_locallyOfFiniteType`: openness of the pointwise
  flat locus of a morphism locally of finite type, reduced to the affine case.
* `AlgebraicGeometry.isOpen_setOf_isFlatAt_of_locallyOfFiniteType_of_isIntegral`: the same over
  an integral base, whose single weakly associated point makes the local finiteness hypothesis
  automatic.

## Implementation notes

The affine hypothesis is stated for a ring map of finite type whose source has finitely many
weakly associated primes, and about the algebra viewed as a module over itself, since the
morphism's flat locus is the flat locus of the structure sheaf. The translation to the charts is
`AlgebraicGeometry.isFlatAt_iff_flat_localizedModule_appLE`, the finiteness of the weakly
associated primes of `Γ(S, U)` is `AlgebraicGeometry.weaklyAssociatedPrimes_sections_finite`
applied to the structure sheaf, and the open set produced on `X` is the image under the open
embedding `V → X` of the preimage of the affine flat locus under the homeomorphism
`V ≃ Spec Γ(X, V)`.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- **Openness of the pointwise flat locus of a morphism locally of finite type, reduced to the
affine case.** Suppose that for every ring map `A → B` of finite type with `A` having finitely
many weakly associated primes the locus of primes `q` of `B` at which `B_q` is flat over `A` is
open in `Spec B`. Then for every morphism `f : X ⟶ S` locally of finite type whose base has
locally finite weakly associated points, the set of points at which `f` is flat is open. -/
theorem isOpen_setOf_isFlatAt_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f]
    (hS : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      (schemeWeaklyAssociatedPoints S ∩ (V : Set S)).Finite)
    (hring : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
      (weaklyAssociatedPrimes A A).Finite →
      IsOpen {q : PrimeSpectrum B | Module.Flat A (LocalizedModule.AtPrime q.asIdeal B)}) :
    IsOpen {x : X | IsFlatAt f.toLRSHom.toShHom x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hxW, hWfin⟩ := hS (f x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  have hxPreU : x ∈ f ⁻¹ᵁ U := by simpa using hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxPreU (f ⁻¹ᵁ U).2
  have hWA : (weaklyAssociatedPrimes (Γ(S, U) : Type u) (Γ(S, U) : Type u)).Finite :=
    weaklyAssociatedPrimes_sections_finite (SheafOfModules.unit S.ringCatSheaf) hU hUW hWfin
  let _ : Algebra (Γ(S, U) : Type u) (Γ(X, V) : Type u) := (f.appLE U V hVU).hom.toAlgebra
  have hft : Algebra.FiniteType (Γ(S, U) : Type u) (Γ(X, V) : Type u) :=
    f.finiteType_appLE hU hV hVU
  let T : Set (PrimeSpectrum (Γ(X, V) : Type u)) :=
    {q | Module.Flat (Γ(S, U) : Type u) (LocalizedModule.AtPrime q.asIdeal (Γ(X, V) : Type u))}
  have hT : IsOpen T := hring _ _ hWA
  let e : V ≃ₜ PrimeSpectrum (Γ(X, V) : Type u) := hV.isoSpec.hom.homeomorph
  have hOrel : IsOpen (e ⁻¹' T) := hT.preimage e.continuous
  refine ⟨Subtype.val '' (e ⁻¹' T), ?_, ?_, ?_⟩
  · rintro y ⟨yV, hyT, rfl⟩
    exact (isFlatAt_iff_flat_localizedModule_appLE f hU hV hVU yV.2).mpr hyT
  · exact V.2.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp hOrel
  · exact Set.mem_image_of_mem (f := (Subtype.val : V → X))
      (show (⟨x, hxV⟩ : V) ∈ e ⁻¹' T from
        (isFlatAt_iff_flat_localizedModule_appLE f hU hV hVU hxV).mp hx)

/-- **Openness of the pointwise flat locus over an integral base, reduced to the affine case.**
An integral scheme has a single weakly associated point, so the local finiteness hypothesis of
`AlgebraicGeometry.isOpen_setOf_isFlatAt_of_locallyOfFiniteType` is automatic. -/
theorem isOpen_setOf_isFlatAt_of_locallyOfFiniteType_of_isIntegral {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsIntegral S]
    (hring : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
      (weaklyAssociatedPrimes A A).Finite →
      IsOpen {q : PrimeSpectrum B | Module.Flat A (LocalizedModule.AtPrime q.asIdeal B)}) :
    IsOpen {x : X | IsFlatAt f.toLRSHom.toShHom x} :=
  isOpen_setOf_isFlatAt_of_locallyOfFiniteType f
    (fun _ => ⟨⊤, trivial,
      (schemeWeaklyAssociatedPoints_finite_of_isIntegral S).inter_of_left _⟩) hring

end AlgebraicGeometry
