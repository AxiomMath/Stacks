module

public import StacksFrontier.AlgebraicGeometry.Spaces.SummandSubspaceConormal

/-!
# Splitting a short exact sequence of modules on the small étale site of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
```
  0 ⟶ ℰ ⟶ ℱ ⟶ 𝒢 ⟶ 0
```
be a short exact sequence of `𝒪_F`-modules, that is, a `CategoryTheory.ShortComplex` in
`AlgebraicGeometry.Space.Modules` which is `CategoryTheory.ShortComplex.ShortExact`.  A
`CategoryTheory.ShortComplex.Splitting` of it is a retraction of the first arrow and a section of
the second whose two composites decompose the identity of `ℱ`.  This file produces one from
*either* half: from a section of the second arrow, and from a retraction of the first.

The category of `𝒪_F`-modules is abelian, so Mathlib's
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection` and
`CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction` apply to it verbatim; the content
below is that they do, stated once at `AlgebraicGeometry.Space.Modules` with the short exactness
of the sequence as the single hypothesis rather than its three clauses separately, and with the
produced half recorded.  Recording it is the point: the half supplied is the splitting's own
`s`, respectively `r`, field *on the nose*, so a consumer that prescribes which section a
splitting must have — as the two statements of
`StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceConormal.lean` do — is discharged by `rfl`.

That is what makes these the producers the configuration of [Stacks Project, Tag 06D8] needs.
Both statements of `SummandSubspaceConormal.lean` ask for a splitting of the pair
`A ⟶ 𝒞_{Z/X} ⟶ i^*𝓘_Y` *whose section is* the inverse image along `i : Z ⟶ X` of the inclusion
`𝓘_Y ⊆ 𝓘_Z` of defining ideal sheaves, so a caller holding the short exactness of that pair and
the single identity saying that inverse image is a section of `γ` supplies both arguments at
once: the splitting is `AlgebraicGeometry.Space.splittingOfSection`, and the equation pinning its
section is `rfl`.  A bare `≫ _ = 𝟙 _` identity is the form in which every splitting this
development produces at the level of algebraic spaces is delivered — see
`AlgebraicGeometry.Space.exists_retraction_modulePullback_conormalMap_universalThickening` and
`AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_retraction` — never as a
structure, which is why the gap was a producer and not the structure.

Nothing is restated here: the two statements of `SummandSubspaceConormal.lean` are used as they
stand, and the hypothesis set just described is interderivable with theirs, since a splitting of
a short complex makes it short exact
(`CategoryTheory.ShortComplex.Splitting.shortExact`) and carries its own section.

## Main definitions

* `AlgebraicGeometry.Space.splittingOfSection`: the splitting of a short exact sequence of
  `𝒪_F`-modules determined by a section of its second arrow, and
  `AlgebraicGeometry.Space.splittingOfRetraction`: the one determined by a retraction of its
  first arrow.

## Main results

* `AlgebraicGeometry.Space.splittingOfSection_s` and
  `AlgebraicGeometry.Space.splittingOfRetraction_r`: the half supplied is the corresponding field
  of the splitting produced.
* `AlgebraicGeometry.Space.nonempty_splitting_of_shortExact_of_exists_section` and
  `AlgebraicGeometry.Space.nonempty_splitting_of_shortExact_of_exists_retraction`: a short exact
  sequence of `𝒪_F`-modules one of whose arrows is split carries a
  `CategoryTheory.ShortComplex.Splitting`.

## What is not proved

**Finite local freeness is not an input anywhere below**, and that is the gap this file does not
close.  At the level of schemes the corresponding producer is
`AlgebraicGeometry.Scheme.Modules.nonempty_splitting_of_shortExact_of_isFiniteLocallyFree` of
`StacksFrontier/AlgebraicGeometry/Modules/AffineGlobalSplitShortExact.lean`, which needs no section
supplied: on an *affine* scheme the module of global sections of a finite locally free
quasi-coherent module is finitely generated projective, so the surjection admits a section.  The
space-level analogue of that statement — a short exact sequence of `𝒪_F`-modules with
`SheafOfModules.IsFiniteLocallyFreeOnSite` third term over an
`AlgebraicGeometry.Space.IsAffineSpace` splits — is **not** proved here, and two links are
missing for it:

* **Finite local freeness does not descend from the small étale site to the representing
  scheme.**  For a representable space the transport runs
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedQuasicoherentSchemeEquivalence`,
  and that is the scheme-to-space direction only; its two steps are
  `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule` (Zariski site of the
  scheme to its small étale site), also one-directional, and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff`, which is
  an iff.  So the missing step is precisely étale descent of finite local freeness onto the
  Zariski site of the representing scheme.  What *is* available on the site is
  `SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`, the passage from the
  covering-family form of Stacks 03DL (2) to the local-generators form of Stacks 01C6 (2), which
  is generic in the site and so applies to `AlgebraicGeometry.Space.Modules` — but it stays on
  the small étale site of the space.
* **There is no projectivity in the category of `𝒪_F`-modules.**  Nothing in this development
  produces a section of an epimorphism of `𝒪_F`-modules: an epimorphism of sheaves of modules is
  only locally surjective on sections, which is what the docstring of
  `AlgebraicGeometry.Space.surjective_val_app_of_isSplitEpi` records, and the category of
  `𝒪_F`-modules is Grothendieck abelian by
  `AlgebraicGeometry.Space.isGrothendieckAbelian_modules`, so it carries enough injectives, not
  enough projectives.

Consequently the section or retraction that the producers below take is still owed, at the
configuration of [Stacks Project, Tag 06D8], by that tag itself: it obtains it from the conormal
sequence of [Stacks Project, Tag 06CC] over an affine `Z` with the conormal module finite locally
free by [Stacks Project, Tag 06CB].

**No `@[stacks]` attribute is placed.**  Nothing below is a clause of a tag: these are the
abelian-category facts at this category, stated where the geometry can reach them.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The producers -/

section Producer

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (T : CategoryTheory.ShortComplex (Modules.{u, u} B S hS F hF))
    (hT : T.ShortExact)

/-- **A section of the second arrow of a short exact sequence of modules on the small étale site
of an algebraic space splits it.**  The category of `𝒪_F`-modules is abelian, hence balanced, so
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection` applies: the retraction of the first
arrow is the factorization of `𝟙 - g ≫ s` through it, which exactness in the middle supplies and
the monomorphy of the first arrow pins down. -/
noncomputable def splittingOfSection (s : T.X₃ ⟶ T.X₂) (hs : s ≫ T.g = 𝟙 T.X₃) :
    T.Splitting :=
  CategoryTheory.ShortComplex.Splitting.ofExactOfSection T hT.exact s hs hT.mono_f

/-- The section of `AlgebraicGeometry.Space.splittingOfSection` is the section supplied, on the
nose.  This is what lets a consumer prescribing the section of a splitting be discharged by
`rfl`. -/
@[simp]
theorem splittingOfSection_s (s : T.X₃ ⟶ T.X₂) (hs : s ≫ T.g = 𝟙 T.X₃) :
    (splittingOfSection B S hS T hT s hs).s = s := rfl

/-- **A retraction of the first arrow of a short exact sequence of modules on the small étale
site of an algebraic space splits it.**  The dual of
`AlgebraicGeometry.Space.splittingOfSection`, through
`CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction`: the section of the second arrow is
the factorization of `𝟙 - r ≫ f` through it, which exactness in the middle supplies and the
epimorphy of the second arrow pins down.  This is the half that the étale-local arguments of this
development deliver:
`AlgebraicGeometry.Space.exists_retraction_modulePullback_conormalMap_universalThickening` is of
exactly this shape. -/
noncomputable def splittingOfRetraction (r : T.X₂ ⟶ T.X₁) (hr : T.f ≫ r = 𝟙 T.X₁) :
    T.Splitting :=
  CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction T hT.exact r hr hT.epi_g

/-- The retraction of `AlgebraicGeometry.Space.splittingOfRetraction` is the retraction supplied,
on the nose. -/
@[simp]
theorem splittingOfRetraction_r (r : T.X₂ ⟶ T.X₁) (hr : T.f ≫ r = 𝟙 T.X₁) :
    (splittingOfRetraction B S hS T hT r hr).r = r := rfl

include hT in
/-- **A short exact sequence of modules on the small étale site of an algebraic space whose
second arrow admits a section is split.**  The existence form of
`AlgebraicGeometry.Space.splittingOfSection`; this is the shape in which the splitting is
consumed when which section it is does not matter. -/
theorem nonempty_splitting_of_shortExact_of_exists_section
    (hs : ∃ s : T.X₃ ⟶ T.X₂, s ≫ T.g = 𝟙 T.X₃) : Nonempty T.Splitting :=
  ⟨splittingOfSection B S hS T hT hs.choose hs.choose_spec⟩

include hT in
/-- **A short exact sequence of modules on the small étale site of an algebraic space whose first
arrow admits a retraction is split.**  The existence form of
`AlgebraicGeometry.Space.splittingOfRetraction`. -/
theorem nonempty_splitting_of_shortExact_of_exists_retraction
    (hr : ∃ r : T.X₂ ⟶ T.X₁, T.f ≫ r = 𝟙 T.X₁) : Nonempty T.Splitting :=
  ⟨splittingOfRetraction B S hS T hT hr.choose hr.choose_spec⟩

end Producer

end AlgebraicGeometry.Space

end
