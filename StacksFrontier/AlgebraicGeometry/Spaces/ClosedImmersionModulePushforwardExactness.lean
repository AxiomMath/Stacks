module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact

/-!
# Exactness of the direct image of modules along a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `ℐ = ker(i♯) ⊆ 𝒪_X` be the ideal cutting out `Z`. The space-level
analogue of [Stacks, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS) — which the source
states for a morphism of ringed spaces that is a homeomorphism onto a closed subset with
surjective comorphism — asserts three things about the direct image
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` of `AlgebraicGeometry.Space.modulePushforward`:

1. `i_*` is exact;
2. `i_*` is fully faithful;
3. the essential image of `i_*` is the class of `𝒪_X`-modules `𝒢` with `ℐ𝒢 = 0`.

Clause (2) is `AlgebraicGeometry.Space.fullyFaithfulModulePushforward` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean`, where it carries
the `@[stacks 08KS]` attribute. This file supplies the **left-exactness half of clause (1)
unconditionally**, the **inclusion `essImage i_* ⊆ {𝒢 | ℐ𝒢 = 0}` of clause (3)
unconditionally** — the containment form of
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`, which carries the
Stacks 04CJ tag for the same content — and assembles **full exactness** from the one input the
development is missing, namely the essential surjectivity of the Stacks 03D1 direct image
`Mod(𝒪_Z) ⥤ Mod(i_*𝒪_Z)`.

Neither half supplied here carries the `@[stacks 08KS]` attribute, because each is half of a
clause that is now stated whole elsewhere: clause (1) is
`AlgebraicGeometry.Space.exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity`
of `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`, and
clause (3) is `AlgebraicGeometry.Space.essImage_modulePushforward_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`. Those two carry
the tag, so the space-level tag registration is one statement per clause.

## How the space-level statement reduces to the scheme-level one

It does not reduce to it, and this file does not try to: the direct image of
`AlgebraicGeometry.Space.modulePushforward` is restriction of scalars along the structure map
`i♯` of Stacks 03G8 applied to the Stacks 03D1 direct image on the *small étale* sites, and
nothing in this development compares `AlgebraicGeometry.Scheme.Modules` of a scheme with
`AlgebraicGeometry.Space.Modules` of the algebraic space it represents — the missing input being
Descent, Proposition 03DX (2), as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardExactSequence.lean` already record.
So the étale presentation is used, as it is throughout this part of the tree, only through the
statements that are already proved space-level: full faithfulness of the small étale direct image
on sheaves of sets (Stacks 04E5, part (1)) and local surjectivity of `i♯` (Stacks 03MB).

Left exactness needs none of that: `AlgebraicGeometry.Space.modulePushforward` is a right adjoint
by `AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`, so it preserves all limits, for an
arbitrary morphism of algebraic spaces and with no closed-immersion hypothesis. This is the exact
analogue of the scheme-level
`Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward`, which carries the same clause of
the same tag.

Right exactness is where the closed immersion has to be spent, and in this development it is spent
through clause (3): a fully faithful functor into `Mod(𝒪_X)` whose essential image is exactly the
`ℐ`-annihilated modules is a *left* adjoint
(`Stacks.SheafOfModules.isLeftAdjoint_of_essImage_eq_annihilated`, the step of Stacks 08M3 that
makes the direct image right exact), hence preserves all colimits. That is the route taken below,
with clause (3) supplied by
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward`: the left-exactness half of
  the exactness clause of Tag 08KS, for an arbitrary morphism of algebraic spaces.
* `AlgebraicGeometry.Space.essImage_modulePushforward_le_annihilatedByKerIdeal`: one inclusion of
  the essential-image clause of Tag 08KS, also for an arbitrary morphism.
* `AlgebraicGeometry.Space.isLeftAdjoint_modulePushforward_of_essSurj`,
  `AlgebraicGeometry.Space.preservesFiniteColimits_modulePushforward_of_essSurj` and
  `AlgebraicGeometry.Space.exactFunctor_modulePushforward_of_essSurj`: right exactness and hence
  full exactness of the direct image along a closed immersion, granted `hsurj`.
* `AlgebraicGeometry.Space.preservesEpimorphisms_modulePushforward_of_essSurj` and
  `AlgebraicGeometry.Space.preservesColimitsOfShape_modulePushforward_of_essSurj`: the two forms
  in which right exactness is consumed — preservation of surjections, and of cokernels and other
  colimits of a fixed shape.

## Implementation notes

**The one input the exactness clause still carries, and why no tag is on it.** The hypothesis
`hsurj` of the statements below is the one of
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`: every sheaf of
`i_*𝒪_Z`-modules on the small étale site of `X` is a Stacks 03D1 direct image. It is the
essential-image assertion of Stacks 04E5, part (1) in the form the argument consumes —
equivalently the closed-subtopos clause of `MorphismOfTopoi.IsClosedImmersion` (Stacks 08M0) for
`AlgebraicGeometry.Space.smallToposMorphismTypeU`, which needs the subterminal sheaf cut out by
the open complement `X ∖ Z` together with Étale Cohomology 04CA and 03LR. `hsurj` holds the whole
remaining content of right exactness, so **no `@[stacks 08KS]` attribute is carried by any
statement that mentions it**; and since the unconditional halves below are each half of a clause
stated whole elsewhere, no statement in this file carries the attribute at all.

The commutativity hypothesis of
`Stacks.SheafOfModules.isLeftAdjoint_of_essImage_eq_annihilated` is discharged by
`AlgebraicGeometry.Space.ringSheaf_mul_comm_smallEtaleRingedSite`, and its ideal is
`SheafOfModules.kerIdeal (AlgebraicGeometry.Space.structureSharp B S hS i)`, which is the ideal
`AlgebraicGeometry.Space.AnnihilatedByKerIdeal` is phrased with; so the essential-image
characterization transfers with no reformulation beyond unfolding that definition.

`AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward` is stated as an `instance`
proved by `inferInstance`: the content is
`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`, and the declaration exists so that
instance search finds `PreservesFiniteLimits` at the direct image without unfolding it to a right
adjoint first. There is no circularity — an instance is added to the environment only after its
own body has been elaborated.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-! ### Left exactness, unconditionally -/

/-- The left-exactness half of the exactness clause of the space-level [Stacks, Tag 08KS]. The
direct image `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` of Stacks 03LU along a morphism of algebraic spaces
preserves finite limits.

It preserves *all* limits, being a right adjoint
(`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`); no closed-immersion hypothesis
enters, exactly as at the scheme level, where
`Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward` is the statement for an
arbitrary morphism of ringed spaces.

The tag itself is carried, for the exactness clause as a whole and unconditionally, by
`AlgebraicGeometry.Space.exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity`
of `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`, which
takes this statement as its left-exactness input. -/
instance preservesFiniteLimits_modulePushforward (f : Z ⟶ X) :
    PreservesFiniteLimits (modulePushforward B S hS f) := by
  infer_instance

/-! ### One inclusion of the essential-image clause -/

/-- One inclusion of the essential-image clause of the space-level [Stacks, Tag 08KS]. The
essential image of the direct image `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` of Stacks 03LU is contained
in the class of `𝒪_Y`-modules annihilated by the kernel ideal `𝓘 = ker(f♯)`, as object
properties of `Mod(𝒪_Y)`.

This is the containment form of
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`, which is the
statement about a single module and carries the Stacks 04CJ tag for the same content. No
hypothesis on `f` is used: restriction of scalars along `f♯` makes a section killed by `f♯` act
as zero on every direct image.

The reverse containment is the remaining half of the clause and is proved, unconditionally, in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`; the whole clause
is `AlgebraicGeometry.Space.essImage_modulePushforward_iff` there, and that is what carries the
tag. -/
theorem essImage_modulePushforward_le_annihilatedByKerIdeal (f : Z ⟶ X) :
    (modulePushforward B S hS f).essImage ≤ annihilatedByKerIdeal B S hS f :=
  fun _ hG ↦ annihilatedByKerIdeal_of_essImage_modulePushforward B S hS f hG

/-! ### Right exactness from the essential-image clause -/

section RightExactness

variable (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (hsurj : ∀ M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS i),
      (moduleDirectImage B S hS i).essImage M)

include hi hsurj in
/-- **The direct image along a closed immersion of algebraic spaces is a left adjoint, granted
`hsurj`.** It is fully faithful by Stacks 04CJ, part (2)
(`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`) and its essential image is exactly the
`𝒪_X`-modules annihilated by the ideal cutting out `Z`
(`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`), so
`Stacks.SheafOfModules.isLeftAdjoint_of_essImage_eq_annihilated` applies: the right adjoint sends
an `𝒪_X`-module to the largest subsheaf of it annihilated by that ideal.

`hsurj` carries the whole content of the essential-image clause, so no `@[stacks]` attribute is
carried here; see the implementation notes. -/
theorem isLeftAdjoint_modulePushforward_of_essSurj :
    (modulePushforward B S hS i).IsLeftAdjoint :=
  Stacks.SheafOfModules.isLeftAdjoint_of_essImage_eq_annihilated
    (ringSheaf_mul_comm_smallEtaleRingedSite B S hS X)
    (SheafOfModules.kerIdeal (structureSharp B S hS i))
    (modulePushforward B S hS i) (fullyFaithfulModulePushforward B S hS i hi)
    fun G ↦ essImage_modulePushforward_iff_of_essSurj B S hS i hi hsurj G

include hi hsurj in
/-- **The direct image along a closed immersion of algebraic spaces is right exact, granted
`hsurj`.** It is a left adjoint by
`AlgebraicGeometry.Space.isLeftAdjoint_modulePushforward_of_essSurj`, hence preserves all
colimits. -/
theorem preservesFiniteColimits_modulePushforward_of_essSurj :
    PreservesFiniteColimits (modulePushforward B S hS i) :=
  have := isLeftAdjoint_modulePushforward_of_essSurj B S hS i hi hsurj
  inferInstance

include hi hsurj in
/-- **The direct image along a closed immersion of algebraic spaces preserves colimits of any
fixed shape, granted `hsurj`.** This is the form in which right exactness is used to compute a
cokernel — for instance a strict transform — on a closed subspace. -/
theorem preservesColimitsOfShape_modulePushforward_of_essSurj
    (K : Type*) [Category* K] :
    PreservesColimitsOfShape K (modulePushforward B S hS i) :=
  have := isLeftAdjoint_modulePushforward_of_essSurj B S hS i hi hsurj
  inferInstance

include hi hsurj in
/-- **The direct image along a closed immersion of algebraic spaces preserves surjections,
granted `hsurj`.** A left adjoint preserves epimorphisms. -/
theorem preservesEpimorphisms_modulePushforward_of_essSurj :
    (modulePushforward B S hS i).PreservesEpimorphisms :=
  have := isLeftAdjoint_modulePushforward_of_essSurj B S hS i hi hsurj
  Functor.preservesEpimorphisms_of_adjunction
    (Adjunction.ofIsLeftAdjoint (modulePushforward B S hS i))

include hi hsurj in
/-- **The exactness clause of the space-level [Stacks, Tag 08KS], granted `hsurj`.** The direct
image `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` along a closed immersion of algebraic spaces is exact.

Left exactness is `AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward` and is
unconditional; right exactness is
`AlgebraicGeometry.Space.preservesFiniteColimits_modulePushforward_of_essSurj` and is where
`hsurj` is spent. **No `@[stacks 08KS]` attribute is carried here**: `hsurj` is the
essential-image assertion of Stacks 04E5, part (1) and holds the remaining content. -/
theorem exactFunctor_modulePushforward_of_essSurj :
    exactFunctor (Modules.{u, u} B S hS Z.1 Z.2) (Modules.{u, u} B S hS X.1 X.2)
      (modulePushforward B S hS i) := by
  rw [exactFunctor_iff]
  exact ⟨preservesFiniteLimits_modulePushforward B S hS i,
    preservesFiniteColimits_modulePushforward_of_essSurj B S hS i hi hsurj⟩

end RightExactness

end AlgebraicGeometry.Space

end
