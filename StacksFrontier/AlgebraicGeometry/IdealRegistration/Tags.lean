module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-!
# Tag 03GL's two ideal assertions, registered on the Tag 0BXK declarations

Tag 03GL states three labelled assertions about a closed subscheme `Z` of projective space.
Two of them are assertions about the homogeneous ideal of `Z` inside the graded ring, and they
are registered — by the `add_to_stacks` command, not by an attribute — on two
declarations belonging to Tag 0BXK.  Both of those declarations are proved over an
arbitrary nonnegatively graded ring rather than a polynomial ring, and this file registers
them.  It attaches no attribute of its own and edits no file belonging
to another development: the two registrations below are `add_to_stacks` commands over existing
declarations, writing the same environment extension an attribute writes, and either one is
removed by deleting one line here.

## The three assertions, and which two these are

1. `"the ideal is graded"` — registered here on
   `Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme_isHomogeneous`.
2. `"the degreewise kernels"` — registered here on
   `Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.mem_idealOfClosedSubscheme_iff`.
3. `"the closed subscheme is the Proj of the quotient"` — **registered elsewhere, not here.** It
   asserts that a closed subscheme of projective space is the `Proj` of the quotient by its
   ideal, compatibly with the immersion into the ambient space.  That is the saturated-ideal half
   of Tag 0BXK, named `Stacks.ClosedSubschemeProjQuotient.SaturationIdentification`;
   `StacksFrontier/AlgebraicGeometry/ClosedSubschemeProjQuotient/Basic.lean` records which of its
   neighbouring clauses are discharged there.  It is a theorem, not a corollary of the two below,
   and nothing here bears on it: it is carried by
   `Stacks.ClosedSubschemeProjectiveSpace.closedSubscheme_iso_projQuotient` in
   `StacksFrontier/AlgebraicGeometry/ClosedSubschemeProjectiveSpace/Basic.lean`, over an arbitrary
   coefficient ring.

## Why these declarations state the assertions

Each of assertions 1 and 2 is a *single* assertion of Tag 03GL, so each is stated by a
single declaration.  Binder for binder the two declarations named above match the reference
statement: the
same implicit graded ring `{S} {σ} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]`,
`(𝒮 : ℕ → σ) [GradedRing 𝒮]`, the same `{Z : Scheme} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i]`,
and for the second the same trailing element `(a : S)`.  Neither carries a hypothesis the reference
statement lacks, and neither conclusion is weaker than its conclusion.

The reference statement writes its conclusions over three auxiliary definitions — the pullback
of global sections (Tag 0EUA), the twisting sheaf (Tag 01MN) and the degree section (Tag 01MP).
Each of them has a library counterpart with the *same body*:
`AlgebraicGeometry.pullbackGlobalSections`,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`.  The two `example`s below are the
reference statements in their binder order with those counterparts substituted, and the
second writes the ideal out as the span the reference defines it to be rather than naming it, so a
declaration that happened to share the name `idealOfClosedSubscheme` while meaning something
else could not satisfy it.

## References

* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public section

open CategoryTheory Opposite DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.Tag03GLIdealRegistration

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Tag 03GL's assertion `"the ideal is graded"`, in the binder order of the reference statement. -/
example {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    (idealOfClosedSubscheme 𝒮 i).IsHomogeneous 𝒮 :=
  idealOfClosedSubscheme_isHomogeneous 𝒮 i

/-- Tag 03GL's assertion `"the degreewise kernels"`, in the binder order of the reference statement and with the
ideal written out as the span of the homogeneous equations. -/
example {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] (a : S) :
    a ∈ Ideal.span {b : S | ∃ (n : ℕ) (c : 𝒮 n), (c : S) = b ∧
        pullbackGlobalSections i (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n c) = 0} ↔
      ∀ n : ℕ, pullbackGlobalSections i (twistingSheaf 𝒮 (n : ℤ))
        (degreeSection 𝒮 n ((DirectSum.decompose 𝒮 a) n)) = 0 :=
  mem_idealOfClosedSubscheme_iff 𝒮 i a

end Stacks.Tag03GLIdealRegistration

add_to_stacks 03GL "the ideal is graded"
  Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme_isHomogeneous

add_to_stacks 03GL "the degreewise kernels"
  Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.mem_idealOfClosedSubscheme_iff

end
