module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A modification of the spectrum of a normal local domain with an isolated point in the closed
fibre

Let `A` be a normal local domain, let `S = Spec(A)` with closed point `s`, and let
`f : X ⟶ S` be a modification — proper and birational, with `X` integral. If some point of the
fibre `X_s` is isolated in `X_s`, then `f` is an isomorphism, and so `X_s` is that single point.

This is the step by which a zero-dimensional piece of a fibre of a modification is ruled out
without knowing in advance that the fibre is connected: an isolated point of a fibre is a
quasi-finite point of `f`, and over a local base the quasi-finite locus of a modification is
forced to be the whole of `X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_fiberι`: a point which is open in the
  scheme-theoretic fibre containing it is a quasi-finite point of the morphism.
* `AlgebraicGeometry.IsModification.isIso_of_isOpen_singleton_fiber`: a modification of the
  spectrum of a normal local domain with an isolated point in the fibre over the closed point is
  an isomorphism.
* `AlgebraicGeometry.IsModification.subsingleton_fiber_of_isOpen_singleton_fiber`: consequently
  that fibre is a single point.

## Implementation notes

The argument runs through Grothendieck's form of Zariski's main theorem, in Mathlib as
`AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus` together with the instance making
`f.quasiFiniteLocus.ι ≫ f.toNormalization` an open immersion: the quasi-finite locus `Q` of a
separated morphism of finite type is an open subscheme of the relative normalization `X'` of the
target in `X`. For a modification of the spectrum of a normal domain the second factor
`X' ⟶ S` of the Stein factorization is an isomorphism
(`Stacks.SteinFactorization.isIso_fromNormalization_of_isIso_appTop` applied to
`AlgebraicGeometry.IsModification.isIso_appTop`, which is `f_*𝒪_X = 𝒪_S`), so `Q ⟶ S` is an
open immersion. Three steps finish the proof.

* The image of `Q ⟶ S` is open and, by hypothesis, contains the closed point; in the spectrum of
  a local ring every point specializes to the closed point, so that image is everything and
  `Q ⟶ S` is an open immersion onto `S`, hence an isomorphism.
* Therefore `Q ⟶ X` is universally closed, `f` being separated, so `Q` is closed in `X` as well
  as open; `X` is irreducible, hence connected, so `Q` is all of `X`.
* A morphism whose quasi-finite locus is everything is locally quasi-finite, and a proper locally
  quasi-finite morphism is finite ([Stacks, Tag 02LS]), so `f` is finite and birational onto a
  normal integral scheme, hence an isomorphism ([Stacks, Tag 0AB1]).

No `@[stacks]` attribute is attached: the statement is the observation that Section 54.7 of the
source makes in passing about Situation [Stacks, Tag 0AX8] — that a zero-dimensional special
fibre makes the modification finite and hence an isomorphism — and not the assertion of a tag of
its own.

## References

* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1): an integral birational
  morphism onto a normal integral scheme is an isomorphism.
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS): a morphism is finite if
  and only if it is proper and locally quasi-finite.
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8): the first conclusion,
  `f_*𝒪_X = 𝒪_S`, which is what makes the relative normalization trivial.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A point which is open in its fibre is a quasi-finite point.** If `p` is a point of the
scheme-theoretic fibre `f.fiber y` whose singleton is open there, then `f` is quasi-finite at the
corresponding point of `X`.

The singleton `{p}` is cut out of the fibre by an open `W` of `X`, the fibre being embedded in
`X`; and then `W` cuts the fibre through `f (f.fiberι y p)` — the same subset of `X`, because
`f` sends `f.fiberι y p` to `y` — in the single point `f.asFiber (f.fiberι y p)`. -/
@[sga "3 V 7.3" "partial", sga "3 V 7.4" "partial"]
theorem Scheme.Hom.quasiFiniteAt_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (p : f.fiber y) (hp : IsOpen ({p} : Set (f.fiber y))) :
    f.QuasiFiniteAt (f.fiberι y p) := by
  obtain ⟨W, hWopen, hWp⟩ := (f.fiberι y).isEmbedding.isInducing.isOpen_iff.mp hp
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hsingleton :
      ({f.asFiber (f.fiberι y p)} : Set (f.fiber (f (f.fiberι y p)))) =
        (f.fiberι (f (f.fiberι y p))) ⁻¹' W := by
    refine Set.eq_of_subset_of_subset (Set.singleton_subset_iff.mpr ?_) (fun q hq ↦ ?_)
    · rw [Set.mem_preimage, f.fiberι_asFiber]
      exact hWp.ge rfl
    · have hrange : f.fiberι (f (f.fiberι y p)) q ∈ f ⁻¹' {y} :=
        (f.apply_fiberι _ q).trans (f.apply_fiberι y p)
      obtain ⟨q', hq'⟩ := (f.range_fiberι y).ge hrange
      have hq'p : q' = p := hWp.le (show f.fiberι y q' ∈ W by rwa [hq'])
      rw [Set.mem_singleton_iff]
      refine (f.fiberι (f (f.fiberι y p))).isEmbedding.injective ?_
      rw [f.fiberι_asFiber, ← hq', hq'p]
  rw [hsingleton]
  exact hWopen.preimage (f.fiberι _).continuous

namespace IsModification

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNormalDomain A] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)}

/-- **A modification of the spectrum of a normal local domain with an isolated point in the
closed fibre is an isomorphism.** If some point of the fibre of a modification
`f : X ⟶ Spec(A)` over the closed point is open in that fibre, then `f` is an isomorphism.

Such a point is a quasi-finite point of `f`, so the quasi-finite locus `Q` of `f` meets the
closed fibre; `Q ⟶ Spec(A)` is an open immersion because the relative normalization of
`Spec(A)` in `X` is `Spec(A)` itself, and its image, being open and containing the closed point,
is everything; so `Q` is clopen in the irreducible space `X`, hence all of it, and `f` is a
finite birational morphism onto a normal integral scheme. -/
@[ega "III 4.4.9" "special case", ega "IV 8.12.12" "special case"]
theorem isIso_of_isOpen_singleton_fiber (hf : IsModification f)
    (p : f.fiber (IsLocalRing.closedPoint A))
    (hp : IsOpen ({p} : Set (f.fiber (IsLocalRing.closedPoint A)))) :
    IsIso f := by
  have hX : IsIntegral X := hf.source_isIntegral
  have hP : IsProper f := hf.isProper
  have hN : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  -- the relative normalization of `Spec(A)` in `X` is `Spec(A)`, because `f_*𝒪_X = 𝒪_S`
  have hfrom : IsIso f.fromNormalization :=
    Stacks.SteinFactorization.isIso_fromNormalization_of_isIso_appTop f hf.isIso_appTop
  -- the quasi-finite locus contains a point of the closed fibre
  have hqf : f.QuasiFiniteAt (f.fiberι _ p) :=
    f.quasiFiniteAt_fiberι (IsLocalRing.closedPoint A) p hp
  -- Zariski's main theorem makes it an open subscheme of `Spec(A)`
  have hfactor : f.quasiFiniteLocus.ι ≫ f =
      (f.quasiFiniteLocus.ι ≫ f.toNormalization) ≫ f.fromNormalization := by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
  have hoi : IsOpenImmersion (f.quasiFiniteLocus.ι ≫ f) := by
    rw [hfactor]
    infer_instance
  have hopen : IsOpen (Set.range (f.quasiFiniteLocus.ι ≫ f).base) :=
    (f.quasiFiniteLocus.ι ≫ f).isOpenEmbedding.isOpen_range
  have hmem : IsLocalRing.closedPoint A ∈ Set.range (f.quasiFiniteLocus.ι ≫ f).base :=
    ⟨⟨f.fiberι (IsLocalRing.closedPoint A) p, hqf⟩, f.apply_fiberι _ p⟩
  -- over a local base an open containing the closed point is everything
  have hsurj : Function.Surjective (f.quasiFiniteLocus.ι ≫ f).base := fun z ↦
    (IsLocalRing.specializes_closedPoint z).mem_open hopen hmem
  have hiso : IsIso (f.quasiFiniteLocus.ι ≫ f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hoi, ⟨hsurj⟩⟩
  -- so the quasi-finite locus is closed as well as open, hence all of `X`
  have huc : UniversallyClosed f.quasiFiniteLocus.ι :=
    UniversallyClosed.of_comp_of_isSeparated f.quasiFiniteLocus.ι f
  have hclosed : IsClosed (f.quasiFiniteLocus : Set X) :=
    Scheme.Opens.range_ι _ ▸ f.quasiFiniteLocus.ι.isClosedMap.isClosed_range
  have hQtop : f.quasiFiniteLocus = ⊤ :=
    SetLike.coe_injective (IsClopen.eq_univ ⟨hclosed, f.quasiFiniteLocus.isOpen⟩ ⟨_, hqf⟩)
  -- a proper morphism with everywhere quasi-finite fibres is finite, hence an isomorphism
  have : LocallyQuasiFinite f := f.quasiFiniteLocus_eq_top_iff.mp hQtop
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal f hf.isBirational

/-- **The fibre of a modification of the spectrum of a normal local domain over the closed point
has at most one point as soon as one of its points is isolated.** The modification is then an
isomorphism, by
`AlgebraicGeometry.IsModification.isIso_of_isOpen_singleton_fiber`, so it is injective. -/
theorem subsingleton_fiber_of_isOpen_singleton_fiber (hf : IsModification f)
    (p : f.fiber (IsLocalRing.closedPoint A))
    (hp : IsOpen ({p} : Set (f.fiber (IsLocalRing.closedPoint A)))) :
    Subsingleton (f.fiber (IsLocalRing.closedPoint A)) := by
  have := hf.isIso_of_isOpen_singleton_fiber p hp
  have hinj : Function.Injective f.base := (Scheme.homeoOfIso (asIso f)).injective
  have : Subsingleton (f ⁻¹' {IsLocalRing.closedPoint A} : Set X) :=
    (Set.subsingleton_singleton.preimage hinj).coe_sort
  exact (f.fiberHomeo (IsLocalRing.closedPoint A)).injective.subsingleton

end IsModification

end AlgebraicGeometry

end
