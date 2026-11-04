module

public import StacksFrontier.RingTheory.PrincipalCodimOne.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Codimension-one closed subschemes of projective space: reduction to associated primes

Tag 0BXL asserts that a closed subscheme `Z` of projective space over a Noetherian unique
factorization domain `R`, having no embedded points and with every irreducible component of
codimension one, has a principal homogeneous ideal.

This file proves the algebraic half of that assertion and reduces the tag to a single
ring-theoretic input, stated as the hypothesis `hassoc` of the last theorem.

## Main results

* `isPrincipal_of_isUnmixed_of_minimalPrimes_height_eq_one`: an ideal of a Noetherian unique
  factorization domain whose associated primes are all minimal over it, and whose minimal
  primes all have height one, is principal. This is the ring-theoretic form of the pair of
  geometric hypotheses "no embedded points" and "every component has codimension one".
* `isPrincipal_of_forall_associatedPrimes_height_eq_one_mvPolynomial` and
  `isPrincipal_of_isUnmixed_of_minimalPrimes_height_eq_one_mvPolynomial`: the same two
  conclusions for the projective coordinate ring `R[x_0, …, x_n]` itself.
* `codimension_closureSingleton_eq_coheight`: on a scheme, the codimension of the closure of a
  point is the coheight of that point in the specialization order.
* `ringKrullDim_stalk_eq_codimension_closureSingleton` and
  `codimension_closureSingleton_eq_one_iff`: consequently that codimension is the Krull
  dimension of the local ring at the point, and the codimension-one condition on a point says
  exactly that its local ring has Krull dimension one.
* `isPrincipal_of_codimension_one_of_associatedPrimes_height_eq_one`: the statement of tag
  0BXL carrying one extra hypothesis, that every associated prime of the homogeneous ideal
  has height one.

## Route

The algebraic engine is already available as
`Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one`:
in a Noetherian unique factorization domain, an ideal all of whose associated primes have
height one is principal. Two steps are added. First, the hypothesis is split into the two
halves the geometry supplies: "every associated prime is minimal over the ideal" is the
absence of embedded points, and "every minimal prime has height one" is the codimension-one
condition on the components. Second, the three ring hypotheses are checked to transfer from
`R` to `MvPolynomial (Fin (n + 1)) R`, through `MvPolynomial.uniqueFactorizationMonoid`,
`MvPolynomial.isNoetherianRing` and the `IsDomain` instance for `MvPolynomial`; the point of
stating this separately is that the transfer is what makes the engine applicable to a
projective coordinate ring at all.

The notion of associated prime used throughout is `Submodule.associatedPrimes I`, the primes
of the form `(I : x).radical` for `x` in the ring, which is the set of associated primes of
the quotient by `I` and hence the algebraic counterpart of the associated points of `Z`.

Separately, the topological hypothesis of the tag is converted into a condition on local
rings. Mathlib compares the coheight of a *point* of a scheme with the Krull dimension of its
local ring (`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, tag 02IZ) but says nothing
about the codimension of an irreducible closed *subset*; the order isomorphism
`irreducibleSetEquivPoints`, available because a scheme is sober and `T0`, identifies the two
and so transfers the comparison to `codimension`.

## What is not done

The geometric half of tag 0BXL is not proved here, and the hypothesis `hassoc` of the final
theorem is exactly what is missing: that the statement's two geometric hypotheses imply that every
associated prime of the homogeneous ideal of `Z` has height one. Its two geometric hypotheses
are therefore not consumed by that proof, and appear there with underscored names.

Of the three comparisons needed to derive `hassoc`, the third is supplied above — the
codimension of the closure of a point is the Krull dimension of its local ring. The other two
are absent from both Mathlib and this repository. They are the correspondence between closed
subschemes of `Proj S` and saturated homogeneous ideals of `S`, whose own prerequisite is a
graded ring structure on a quotient by a homogeneous ideal, so that `Proj (S ⧸ I)` can be
written at all; and the identification of the associated points of a scheme with the
associated primes of its rings of functions, for which nothing relates
`Stacks.AlgebraicGeometry.AssociatedPointsMono.IsAssociatedPoint` to any ring-level notion of
associated prime.

Tags 0BXK and 05AK are themselves not formalized elsewhere in this repository. The definitions
`idealOfClosedSubscheme`, `IsEmbeddedPoint` and `HasNoEmbeddedPoints` below are transcriptions
of those two tags, assembled from existing material only, recorded here so that the statement of
tag 0BXL can be written down and machine-checked; they should be replaced by general
definitions once those exist. Nothing below weakens or strengthens them.

Also not done is the refinement that the generator may be taken homogeneous, which is the form
in which tag 0BXL is usually read ("cut out by one equation"). The algebraic engine yields a
generator with no control on its degrees, and the additivity of lowest and highest degree in a
graded domain, which is what upgrades it, is not available here.

## References

* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.AssociatedPointsMono
open Stacks.AlgebraicGeometry.ProjTwistSections

universe u w

namespace Stacks.AlgebraicGeometry.CodimensionOneDivisor

-- The grading of a polynomial ring by homogeneous degree is a definition in Mathlib rather
-- than an instance, so it is supplied here exactly as tag 0BXL's own statement supplies it.
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The algebraic reduction -/

/-- An ideal of a Noetherian unique factorization domain whose associated primes are all
minimal over it, and all of whose minimal primes have height one, is principal.

The two hypotheses are the ring-theoretic readings of the two geometric hypotheses of tag
0BXL: the first says that the ideal has no embedded primes, the second that its components
have codimension one. -/
theorem isPrincipal_of_isUnmixed_of_minimalPrimes_height_eq_one {A : Type u} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A] {I : Ideal A}
    (hunmixed : ∀ p ∈ Submodule.associatedPrimes I, p ∈ I.minimalPrimes)
    (hheight : ∀ p ∈ I.minimalPrimes, p.height = 1) :
    I.IsPrincipal :=
  Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one
    fun p hp => hheight p (hunmixed p hp)

/-- The engine of tag 0BXL, applied to a projective coordinate ring: an ideal of
`R[x_0, …, x_{m-1}]` over a Noetherian unique factorization domain `R`, all of whose
associated primes have height one, is principal.

The content is that `IsDomain`, `IsNoetherianRing` and `UniqueFactorizationMonoid` all pass
from `R` to the polynomial ring in finitely many variables. -/
@[ega "IV 21.12.9" "special case"]
theorem isPrincipal_of_forall_associatedPrimes_height_eq_one_mvPolynomial (R : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (m : ℕ)
    {I : Ideal (MvPolynomial (Fin m) R)}
    (h : ∀ p ∈ Submodule.associatedPrimes I, p.height = 1) :
    I.IsPrincipal :=
  Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one h

/-- The same for a projective coordinate ring, with the hypothesis split into its two
geometric halves. -/
theorem isPrincipal_of_isUnmixed_of_minimalPrimes_height_eq_one_mvPolynomial (R : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (m : ℕ)
    {I : Ideal (MvPolynomial (Fin m) R)}
    (hunmixed : ∀ p ∈ Submodule.associatedPrimes I, p ∈ I.minimalPrimes)
    (hheight : ∀ p ∈ I.minimalPrimes, p.height = 1) :
    I.IsPrincipal :=
  isPrincipal_of_isUnmixed_of_minimalPrimes_height_eq_one hunmixed hheight

/-! ### Translating the codimension hypothesis

The codimension hypothesis of tag 0BXL is topological. These three results convert it into a
statement about the local rings of projective space, which is the form the algebraic engine can
eventually consume. -/

/-- On a scheme, the codimension of the closure of a point is the coheight of that point in the
specialization order.

Mathlib has this comparison only for points (`Order.coheight`), not for irreducible closed
subsets; the order isomorphism `irreducibleSetEquivPoints` between the two, available because a
scheme is sober and `T0`, is what identifies them. -/
theorem codimension_closureSingleton_eq_coheight {X : Scheme.{u}} (x : X) :
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  have h : IrreducibleCloseds.closureSingleton x = irreducibleSetEquivPoints.symm x :=
    IrreducibleCloseds.ext (by
      rw [IrreducibleCloseds.coe_closureSingleton, coe_irreducibleEquivPoints_symm_apply])
  rw [codimension_eq_coheight, h]
  exact Order.coheight_orderIso irreducibleSetEquivPoints.symm x

/-- On a scheme, the codimension of the closure of a point is the Krull dimension of the local
ring at that point. -/
@[ega "IV 21.6.2" "partial", sga "1 II 5.9" "partial"]
theorem ringKrullDim_stalk_eq_codimension_closureSingleton {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) =
      (codimension (IrreducibleCloseds.closureSingleton x) : WithBot ℕ∞) := by
  rw [ringKrullDim_stalk_eq_coheight, codimension_closureSingleton_eq_coheight]

/-- The codimension-one condition on a point of a scheme says exactly that its local ring has
Krull dimension one. This is the ring-theoretic reading of the hypothesis `hcodim` of tag
0BXL. -/
theorem codimension_closureSingleton_eq_one_iff {X : Scheme.{u}} (x : X) :
    codimension (IrreducibleCloseds.closureSingleton x) = 1 ↔
      ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_codimension_closureSingleton]
  exact ⟨fun h => by rw [h]; rfl, fun h => by exact_mod_cast h⟩

/-! ### Transcribed vocabulary

The three definitions in this section are the definitions of tags 0BXK and 05AK, neither of
which is formalized elsewhere in this repository. They are written here out of existing material so
that the statement of tag 0BXL can be written down, and are to be replaced by general versions. -/

section Vocabulary

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Tag 0BXK: the homogeneous ideal of a closed subscheme of `Proj 𝒮`, spanned by the
homogeneous elements whose canonical twisted global section pulls back to zero on the
subscheme. -/
def idealOfClosedSubscheme {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.Proj 𝒮)
    [IsClosedImmersion i] : Ideal S :=
  Ideal.span {a : S | ∃ (n : ℕ) (b : 𝒮 n), (b : S) = a ∧
    pullbackGlobalSections i (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n b) = 0}

/-- Tag 05AK, part (2): a point of a scheme is embedded when it is an associated point of the
structure sheaf which is a proper specialization of another associated point. -/
abbrev IsEmbeddedPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x ∧
    ∃ x' : X, IsAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x' ∧ x' ⤳ x ∧ x' ≠ x

/-- Tag 05AK: a scheme has no embedded points. -/
abbrev HasNoEmbeddedPoints (X : Scheme.{u}) : Prop := ∀ x : X, ¬ IsEmbeddedPoint X x

end Vocabulary

/-! ### Tag 0BXL, modulo one input -/

/-- **Tag 0BXL, with one added hypothesis.** A closed subscheme of projective space over a
Noetherian unique factorization domain, with no embedded points and with every irreducible
component of codimension one, has a principal homogeneous ideal — *provided* every associated
prime of that ideal has height one.

The hypothesis `hassoc` is the whole geometric content of the tag and is not proved here; the
two geometric hypotheses of the tag are what should imply it, and are accordingly not used by
this proof. See the "what is not done" section of the module docstring. -/
theorem isPrincipal_of_codimension_one_of_associatedPrimes_height_eq_one (R : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (n : ℕ)
    {Z : Scheme.{u}}
    (i : Z ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion i] (_hno : HasNoEmbeddedPoints Z)
    (_hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1)
    (hassoc : ∀ p ∈ Submodule.associatedPrimes
        (idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i),
      p.height = 1) :
    (idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).IsPrincipal :=
  isPrincipal_of_forall_associatedPrimes_height_eq_one_mvPolynomial R (n + 1) hassoc

end Stacks.AlgebraicGeometry.CodimensionOneDivisor

end
