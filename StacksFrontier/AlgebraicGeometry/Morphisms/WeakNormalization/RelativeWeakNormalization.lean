module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative weak normalization of an algebra

For a dominant map of affine schemes, there is a largest intermediate algebra whose spectrum
is a universal homeomorphism over the base.

## Main definitions

* `AlgebraicGeometry.relativeWeakNormalization` is the largest subalgebra inducing a
  universal homeomorphism on spectra.

## Main results

* `AlgebraicGeometry.relativeWeakNormalization_isUniversalHomeomorphism` says that its
  spectrum is a universal homeomorphism over the base when the original map is dominant.
* `AlgebraicGeometry.range_le_relativeWeakNormalization` gives its maximality among
  intermediate algebras with this property.

## Implementation notes

The algebra is chosen canonically as the supremum of all subalgebras with the required
property. Thus the containment of the image in part (2) is expressed directly as an
inequality of subalgebras. This choice makes the formation of the algebra available to later
results.

## References

* [Stacks Project, Tag 0H3J](https://stacks.math.columbia.edu/tag/0H3J)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Two ring maps to a field out of the target of a universal homeomorphism of spectra agree
as soon as they agree on the source. -/
public lemma ringHom_eq_of_universalHomeomorphism
    {A C K : Type u} [CommRing A] [CommRing C] [Field K]
    (f : A →+* C)
    (h : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op))
    (φ ψ : C →+* K) (hA : ∀ a, φ (f a) = ψ (f a)) : φ = ψ := by
  let q := Scheme.Spec.map (CommRingCat.ofHom f).op
  have hUI : UniversallyInjective q :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective q).mp h |>.2.1
  have huniq := ((tfae_universallyInjective q).out 1 2).mp hUI
  let φS : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C) :=
    (Spec.homEquiv).symm (CommRingCat.ofHom φ)
  let ψS : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C) :=
    (Spec.homEquiv).symm (CommRingCat.ofHom ψ)
  have hcompRing : Spec.homEquiv (φS ≫ q) = Spec.homEquiv (ψS ≫ q) := by
    ext a
    simpa [Spec.homEquiv, φS, ψS, q] using hA a
  have hS : φS = ψS := huniq K (Spec.homEquiv.injective hcompRing)
  have hring : CommRingCat.ofHom φ = CommRingCat.ofHom ψ := by
    simpa [φS, ψS] using congrArg Spec.homEquiv hS
  exact congrArg CommRingCat.Hom.hom hring

/-- A ring map through which any two maps to a field factor uniquely has universally
injective spectrum map. -/
public lemma universallyInjective_specMap_of_ringHom_unique
    {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
    (hunique : ∀ (K : Type u) [Field K] (φ ψ : C →+* K),
      φ.comp f = ψ.comp f → φ = ψ) :
    UniversallyInjective (Scheme.Spec.map (CommRingCat.ofHom f).op) := by
  let q := Scheme.Spec.map (CommRingCat.ofHom f).op
  apply ((tfae_universallyInjective q).out 1 2).mpr
  intro K _ φ ψ hcomp
  have hcompRing := congrArg CommRingCat.Hom.hom (congrArg Spec.homEquiv hcomp)
  have hring : (Spec.preimage φ).hom.comp f = (Spec.preimage ψ).hom.comp f := by
    simpa [q, Spec.homEquiv, Spec.preimage_comp, CommRingCat.hom_comp] using hcompRing
  exact Spec.homEquiv.injective (CommRingCat.hom_ext_iff.mpr (hunique K _ _ hring))

/-- An algebra whose spectrum map is a universal homeomorphism is integral. -/
private lemma algebraIsIntegral_of_universalHomeomorphism
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (h : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)) :
    Algebra.IsIntegral A C :=
  algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp h).1)

/-- An integral algebra map whose kernel consists of nilpotents has surjective spectrum
map. -/
public lemma specMap_surjective_of_integral_of_ker_le_nilradical
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (hi : IsIntegralHom
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hker : RingHom.ker (algebraMap A C) ≤ nilradical A) :
    Function.Surjective
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
  have : Algebra.IsIntegral A C := algebraMap_isIntegral_iff.mp <|
    IsIntegralHom.SpecMap_iff.mp hi
  change Function.Surjective (PrimeSpectrum.comap (algebraMap A C))
  intro p
  have : p.asIdeal.IsPrime := p.2
  obtain ⟨q, hq, hqprime, hqp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal C) (by
      intro x hx
      apply hker.trans (nilradical_le_prime p.asIdeal)
      simpa [RingHom.mem_ker] using hx)
  exact ⟨⟨q, hqprime⟩, PrimeSpectrum.ext hqp⟩

/-- An integral, universally injective and surjective spectrum map of an algebra is a
universal homeomorphism. -/
@[ega "IV 18.12.11" "special case"]
public lemma universalHomeomorphism_of_integral_universallyInjective_surjective
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (hi : IsIntegralHom
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hUI : UniversallyInjective
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hsurj : Function.Surjective
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) :=
  (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
    ⟨hi, hUI, (surjective_iff _).2 hsurj⟩

/-- A dominant spectrum map comes from an algebra map whose kernel consists of nilpotents. -/
private lemma dominant_algebraMap_kernel_le_nilradical
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hB : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    RingHom.ker (algebraMap A B) ≤ nilradical A :=
  (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap A B)).mp (by exact hB.denseRange)

/-- The structure map of a subalgebra inherits the nilpotency of the kernel of the ambient
structure map. -/
private lemma subalgebra_algebraMap_kernel_le_nilradical
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (C : Subalgebra A B) (hkerB : RingHom.ker (algebraMap A B) ≤ nilradical A) :
    RingHom.ker (algebraMap A C) ≤ nilradical A := by
  intro a ha
  apply hkerB
  simpa [RingHom.mem_ker] using
    congrArg (fun z : C => (z : B)) (RingHom.mem_ker.mp ha)

/-- An integral subalgebra with unique extensions of maps to fields and nilpotent kernel has
universally homeomorphic spectrum. -/
private lemma universalHomeomorphism_of_isIntegral_of_unique
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B)
    [Algebra.IsIntegral A C]
    (hUnique : ∀ (K : Type u) [Field K] (φ ψ : C →+* K),
      φ.comp (algebraMap A C) = ψ.comp (algebraMap A C) → φ = ψ)
    (hkerB : RingHom.ker (algebraMap A B) ≤ nilradical A) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
  have hIntSpec : IsIntegralHom (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr ‹_›)
  exact universalHomeomorphism_of_integral_universallyInjective_surjective hIntSpec
    (universallyInjective_specMap_of_ringHom_unique _ hUnique)
    (specMap_surjective_of_integral_of_ker_le_nilradical hIntSpec
      (subalgebra_algebraMap_kernel_le_nilradical C hkerB))

/-- The supremum of a family of subalgebras with universally homeomorphic spectra again has
universally homeomorphic spectrum. -/
private lemma universalHomeomorphism_sSup
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (S : Set (Subalgebra A B))
    (hS : ∀ C ∈ S, UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hkerB : RingHom.ker (algebraMap A B) ≤ nilradical A) :
    UniversalHomeomorphism
      (Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap A (sSup S : Subalgebra A B))).op) := by
  let I := {C : Subalgebra A B // C ∈ S}
  let U : Subalgebra A B := ⨆ i : I, i.1
  have hEq : U = sSup S := by
    simpa [U, I] using (sSup_eq_iSup' S).symm
  have : Algebra.IsIntegral A U := by
    refine ⟨fun x => ?_⟩
    have hxB : _root_.IsIntegral A (x.1 : B) := by
      refine Algebra.iSup_induction (S := fun i : I => i.1)
        (motive := fun y : B => _root_.IsIntegral A y) x.2 ?_ (fun _ _ => IsIntegral.add)
        (fun _ _ => IsIntegral.mul) fun _ => isIntegral_algebraMap
      intro i y hy
      exact IsIntegral.map i.1.val
        ((algebraIsIntegral_of_universalHomeomorphism (hS i.1 i.2)).isIntegral ⟨y, hy⟩)
    exact (isIntegral_algHom_iff U.val Subtype.val_injective).mp (by simpa using hxB)
  have hUnique : ∀ (K : Type u) [Field K] (φ ψ : U →+* K),
      φ.comp (algebraMap A U) = ψ.comp (algebraMap A U) → φ = ψ := by
    intro K _ φ ψ hcomp
    refine RingHom.ext fun x => ?_
    apply Algebra.iSup_induction' (fun i : I => i.1) x.property
      (motive := fun y hy => φ ⟨y, hy⟩ = ψ ⟨y, hy⟩)
    · intro i y hy
      let inc := i.1.inclusion (le_iSup (fun j : I => j.1) i)
      let φC := φ.comp inc.toRingHom
      let ψC := ψ.comp inc.toRingHom
      have hA : ∀ a : A, φC (algebraMap A i.1 a) = ψC (algebraMap A i.1 a) := fun a => by
        simpa [φC, ψC, inc, U] using congrArg (fun q : A →+* K => q a) hcomp
      simpa [φC, ψC, inc, U] using congrArg (fun q : i.1 →+* K => q ⟨y, hy⟩)
        (ringHom_eq_of_universalHomeomorphism _ (hS i.1 i.2) φC ψC hA)
    · intro x y hx hy hfx hfy
      change φ ((⟨x, hx⟩ : U) + ⟨y, hy⟩) = ψ ((⟨x, hx⟩ : U) + ⟨y, hy⟩)
      rw [map_add, map_add, hfx, hfy]
    · intro x y hx hy hfx hfy
      change φ ((⟨x, hx⟩ : U) * ⟨y, hy⟩) = ψ ((⟨x, hx⟩ : U) * ⟨y, hy⟩)
      rw [map_mul, map_mul, hfx, hfy]
    · intro a
      change φ (algebraMap A U a) = ψ (algebraMap A U a)
      exact congrArg (fun q : A →+* K => q a) hcomp
  rw [← hEq]
  exact universalHomeomorphism_of_isIntegral_of_unique U hUnique hkerB

/-- The image of an algebra with universally homeomorphic spectrum again has universally
homeomorphic spectrum. -/
private lemma range_universalHomeomorphism
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (g : C →ₐ[A] B)
    (hC : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hkerB : RingHom.ker (algebraMap A B) ≤ nilradical A) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A g.range)).op) := by
  have hIntegralC := algebraIsIntegral_of_universalHomeomorphism hC
  have : Algebra.IsIntegral A g.range := ⟨fun x => by
    obtain ⟨c, rfl⟩ := g.rangeRestrict_surjective x
    exact IsIntegral.map g.rangeRestrict (hIntegralC.isIntegral c)⟩
  have hUnique : ∀ (K : Type u) [Field K] (φ ψ : g.range →+* K),
      φ.comp (algebraMap A g.range) = ψ.comp (algebraMap A g.range) → φ = ψ := by
    intro K _ φ ψ hcomp
    let φC := φ.comp g.rangeRestrict.toRingHom
    let ψC := ψ.comp g.rangeRestrict.toRingHom
    have hA : ∀ a : A, φC (algebraMap A C a) = ψC (algebraMap A C a) := fun a => by
      simpa [φC, ψC] using congrArg (fun q : A →+* K => q a) hcomp
    refine RingHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := g.rangeRestrict_surjective x
    exact congrArg (fun q : C →+* K => q c)
      (ringHom_eq_of_universalHomeomorphism (algebraMap A C) hC φC ψC hA)
  exact universalHomeomorphism_of_isIntegral_of_unique g.range hUnique hkerB

/-- The relative weak normalization of `A` in `B`: the largest `A`-subalgebra of `B` whose
spectrum is a universal homeomorphism over `Spec(A)`. -/
@[stacks 0H3J "the algebra"]
def relativeWeakNormalization (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Subalgebra A B :=
  sSup { C : Subalgebra A B |
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) }

/-- If `Spec(B) → Spec(A)` is dominant, the relative weak normalization has spectrum
universally homeomorphic to `Spec(A)`. -/
@[stacks 0H3J "part (1)"]
theorem relativeWeakNormalization_isUniversalHomeomorphism
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (_h : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap A (relativeWeakNormalization A B))).op) :=
  universalHomeomorphism_sSup A B _ (by simp) (dominant_algebraMap_kernel_le_nilradical _h)

/-- The image of every intermediate `A`-algebra universally homeomorphic over `Spec(A)` is
contained in the relative weak normalization. -/
@[stacks 0H3J "part (2)"]
theorem range_le_relativeWeakNormalization
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (g : C →ₐ[A] B)
    (_hB : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hC : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)) :
    g.range ≤ relativeWeakNormalization A B :=
  le_sSup (range_universalHomeomorphism g hC (dominant_algebraMap_kernel_le_nilradical _hB))

end AlgebraicGeometry

end
