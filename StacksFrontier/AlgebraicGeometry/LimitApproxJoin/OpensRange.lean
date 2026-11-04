module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The range of the map to the spectrum of the global sections

Let `X` be a quasi-affine scheme and let `f : ι → Γ(X, ⊤)` be a family of global sections whose
basic opens are affine and cover `X`.  This file identifies the image of the canonical open
immersion `X ⟶ Spec Γ(X, ⊤)`: it is exactly the union of the standard opens `D(f l)`.

This is the geometric join of step (ii) of the one-affine-open step of Tag 07RN.  There `X` is
the model `V j` of the overlap at a finite stage, the `f l` are lifts of the finitely many
elements of the sections of the overlap cutting it out of the affine open being added, and the
union of standard opens is the open of `Spec Γ(V j, ⊤)` that
`AlgebraicGeometry.isOpenImmersion_spec_fibreProduct_of_app_eq` — Tag 01Z9 — maps by an open
immersion into the spectrum of the fibre product ring.  Without this identification that open
immersion is of an unidentified union rather than of the model of the overlap, and the glueing of
step (iii) has nothing to glue along.

## What is built, and the route

* `AlgebraicGeometry.Scheme.range_SpecMap_res_basicOpen` is the affine input: the spectrum of
  the restriction `Γ(X, ⊤) ⟶ Γ(X, X.basicOpen r)` has image the standard open `D(r)`.  It is
  Mathlib's `PrimeSpectrum.localization_away_comap_range` fed with the qcqs lemma, Tag 01P7, in
  the form `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`.

* `AlgebraicGeometry.Scheme.basicOpen_le_opensRange_toSpecΓ` is the one inclusion with content:
  a standard open `D(r)` of `Spec Γ(X, ⊤)` lies inside the image of `X` as soon as the basic
  open `X.basicOpen r` is affine.  The route is `AlgebraicGeometry.IsAffineOpen.fromSpec_toSpecΓ`:
  the map from `Spec Γ(X, X.basicOpen r)` into `Spec Γ(X, ⊤)` factors through `X`, and by the
  previous statement it already hits all of `D(r)`.

  The affineness hypothesis is not a convenience; it is equivalent to the conclusion, and the
  converse is `AlgebraicGeometry.Scheme.isAffineOpen_basicOpen_of_basicOpen_le_opensRange`: when
  `D(r)` lies inside the image, the basic open is carried isomorphically onto the affine `D(r)`.

* `AlgebraicGeometry.Scheme.isQuasiAffine_of_iSup_basicOpen_eq_top` records that the two
  hypotheses of the equality below already force quasi-affineness of a quasi-compact scheme; it
  is Mathlib's `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` in the
  indexed-family form the rest of the file uses.

* `AlgebraicGeometry.Scheme.opensRange_toSpecΓ_eq_iSup_basicOpen` is the equality of opens
  itself.  One inclusion is the previous statement applied to each `f l`; the other is the
  observation that the preimage of `D(f l)` under the map to the spectrum is `X.basicOpen (f l)`
  (`AlgebraicGeometry.Scheme.toSpecΓ_preimage_basicOpen`), so a covering family of basic opens
  confines the image to the union of the `D(f l)`.

* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp_of_opensRange_eq` and
  `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp` turn the equality into the statement a
  consumer wants: if the inclusion of the union of the `D(f l)` into the spectrum becomes an
  open immersion after composing with some morphism, then so does the map out of `X` itself.
  The map out of `X` factors through its image by
  `AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`, and the equality of opens transports the
  hypothesis onto that image.  The first form takes the equality of opens as a hypothesis, which
  is what the shrinking argument
  `AlgebraicGeometry.exists_map_opensRange_toSpecΓ_eq_iSup_basicOpen` delivers; the second
  derives it from the affine covering family.

## Implementation notes

The index type of the family is left in its own universe; nothing here indexes a ring or a
colimit by it, so the restriction that the restated Tag 06AC carries — `CommRingCat` in one
universe has no colimits over a larger index universe — does not bite.  The scheme
universe is single, as everywhere in this part of the development.

On the shrinking argument.  The two hypotheses of the equality — the basic opens are affine and
they cover — are statements at a *single* stage, and in the application they are known at the
*limit*, where the finitely many standard opens of the affine open being added can be chosen to
lie inside the overlap, which makes them affine and makes them cover it.  Moving them down to a
finite stage is `AlgebraicGeometry.exists_stage_affine_basicOpen_cover`, which transports the
*equality of opens*
rather than the two hypotheses separately, by one application of Tag 01Z4 in the form
`AlgebraicGeometry.exists_map_preimage_eq_map_preimage` — and that rests on
`AlgebraicGeometry.exists_map_preimage_le_map_preimage`.  The two hypotheses are then recovered
at the stage by the converse direction recorded above.

Transparency gotchas:

* `AlgebraicGeometry.Scheme.range_SpecMap_res_basicOpen` is stated for `Set.range` of the
  underlying continuous map and not for `AlgebraicGeometry.Scheme.Hom.opensRange`, deliberately:
  `opensRange` demands an `AlgebraicGeometry.IsOpenImmersion` instance for the morphism, and the
  restriction map carries one only after the localization instance has been introduced, which
  cannot be done inside a statement without making the statement depend on a chosen instance.

* The carrier of `Spec Γ(X, ⊤)` and `PrimeSpectrum Γ(X, ⊤)` are the same type but not the same
  expression.  Membership facts move between them by `exact` and not by `rw`; a rewrite of a
  standard open into a `Set.range` fails on the ascription even though the two sides are
  definitionally equal.

* The algebra structure that Mathlib puts on `Γ(X, X.basicOpen r)` goes through
  `AlgebraicGeometry.Scheme.basicOpen_le`, while the factorization lemma spells the same
  restriction with `le_top`.  The two `homOfLE` morphisms agree, since the homs of a poset of
  opens are a subsingleton, but a statement written with one and used with the other relies on
  that and will not match syntactically.

## What is NOT done here

Nothing in this directory constructs an inhabitant of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`; the functor on the disjoint union of the
stage indices and the induction over the finitely many affine opens — gaps (b) and (c) of
Tag 07RN — are untouched.  Tag 07RN is not proved and no tag attribute is attached to anything
in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-- **The spectrum of a restriction to a basic open covers the standard open.**  For a
quasi-compact quasi-separated scheme `X` and `r : Γ(X, ⊤)`, the image of
`Spec Γ(X, X.basicOpen r) ⟶ Spec Γ(X, ⊤)` is the standard open `D(r)`.

This is Mathlib's `PrimeSpectrum.localization_away_comap_range` applied to the qcqs lemma,
Tag 01P7. -/
lemma Scheme.range_SpecMap_res_basicOpen (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (r : Γ(X, ⊤)) :
    Set.range (Spec.map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op)).base =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(X, ⊤))) :=
  have := isLocalization_basicOpen_of_qcqs (X := X) isCompact_univ isQuasiSeparated_univ r
  PrimeSpectrum.localization_away_comap_range (Γ(X, X.basicOpen r)) r

/-- **A standard open with affine basic open lies in the image of a quasi-affine scheme.**  Let
`X` be quasi-affine and let `r : Γ(X, ⊤)` be such that `X.basicOpen r` is affine.  Then the
standard open `D(r)` of `Spec Γ(X, ⊤)` is contained in the image of `X`.

The affineness of `X.basicOpen r` is what makes this true: the map `X ⟶ Spec Γ(X, ⊤)` factors
the map out of `Spec Γ(X, X.basicOpen r)`, whose image is all of `D(r)`. -/
lemma Scheme.basicOpen_le_opensRange_toSpecΓ (X : Scheme.{u}) [X.IsQuasiAffine] (r : Γ(X, ⊤))
    (hr : IsAffineOpen (X.basicOpen r)) :
    PrimeSpectrum.basicOpen r ≤ X.toSpecΓ.opensRange := by
  intro x hx
  have hx' : x ∈ Set.range (Spec.map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op)).base := by
    rw [X.range_SpecMap_res_basicOpen r]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  refine ⟨hr.fromSpec.base y, ?_⟩
  exact congrFun (congrArg (fun g : Spec Γ(X, X.basicOpen r) ⟶ Spec Γ(X, ⊤) ↦
    (g.base : _ → _)) hr.fromSpec_toSpecΓ) y

/-- **A basic open whose standard open lies in the image is affine.**  The converse of
`AlgebraicGeometry.Scheme.basicOpen_le_opensRange_toSpecΓ`: the map to the spectrum of the global
sections carries `X.basicOpen r` onto `D(r)`, which is affine. -/
lemma Scheme.isAffineOpen_basicOpen_of_basicOpen_le_opensRange (X : Scheme.{u})
    [X.IsQuasiAffine] (r : Γ(X, ⊤)) (hr : PrimeSpectrum.basicOpen r ≤ X.toSpecΓ.opensRange) :
    IsAffineOpen (X.basicOpen r) := by
  rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion X.toSpecΓ]
  have himg : X.toSpecΓ ''ᵁ X.basicOpen r = PrimeSpectrum.basicOpen r := by
    rw [← X.toSpecΓ_preimage_basicOpen r]
    exact Opens.ext (Set.image_preimage_eq_of_subset fun x hx ↦ hr hx)
  rw [himg]
  exact IsAffineOpen.Spec_basicOpen r

/-- **A quasi-compact scheme covered by affine basic opens of global sections is quasi-affine.**
This is Mathlib's `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` in the
form of an indexed covering family. -/
lemma Scheme.isQuasiAffine_of_iSup_basicOpen_eq_top (X : Scheme.{u}) [CompactSpace X]
    {ι : Type v} (f : ι → Γ(X, ⊤)) (haff : ∀ l, IsAffineOpen (X.basicOpen (f l)))
    (hcov : ⨆ l, X.basicOpen (f l) = ⊤) : X.IsQuasiAffine :=
  .of_forall_exists_mem_basicOpen X fun x ↦ by
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (hcov.ge (show x ∈ (⊤ : X.Opens) from trivial))
    exact ⟨f l, haff l, hl⟩

/-- **The image of a quasi-affine scheme in the spectrum of its global sections is the union of
the standard opens of a covering family of affine basic opens.**

This is the equality of opens that identifies the model of the overlap at a finite stage with
the union of standard opens appearing in Tag 01Z9, in step (ii) of the one-affine-open step of
Tag 07RN. -/
lemma Scheme.opensRange_toSpecΓ_eq_iSup_basicOpen (X : Scheme.{u}) [X.IsQuasiAffine]
    {ι : Type v} (f : ι → Γ(X, ⊤)) (haff : ∀ l, IsAffineOpen (X.basicOpen (f l)))
    (hcov : ⨆ l, X.basicOpen (f l) = ⊤) :
    X.toSpecΓ.opensRange = ⨆ l, PrimeSpectrum.basicOpen (f l) := by
  refine le_antisymm ?_ (iSup_le fun l ↦ X.basicOpen_le_opensRange_toSpecΓ (f l) (haff l))
  rintro x ⟨y, rfl⟩
  obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (hcov.ge (show y ∈ (⊤ : X.Opens) from trivial))
  exact Opens.mem_iSup.mpr ⟨l, (X.toSpecΓ_preimage_basicOpen (f l)).ge hl⟩

/-- **An open immersion of the image is an open immersion of the scheme.**  If the image of
`X ⟶ Spec Γ(X, ⊤)` is `⨆ l, D(f l)` and the inclusion of that open becomes an open immersion
after composing with `h`, then `X ⟶ Spec Γ(X, ⊤) ⟶ _` is an open immersion.

In step (ii) of Tag 07RN the morphism `h` is the spectrum of the second projection of the fibre
product ring and the hypothesis is
`AlgebraicGeometry.isOpenImmersion_spec_fibreProduct_of_app_eq`. -/
lemma isOpenImmersion_toSpecΓ_comp_of_opensRange_eq {X : Scheme.{u}} [X.IsQuasiAffine]
    {ι : Type v} (f : ι → Γ(X, ⊤))
    (heq : X.toSpecΓ.opensRange = ⨆ l, PrimeSpectrum.basicOpen (f l))
    {Z : Scheme.{u}} (h : Spec Γ(X, ⊤) ⟶ Z)
    (hoi : IsOpenImmersion
      ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec Γ(X, ⊤)).Opens).ι ≫ h)) :
    IsOpenImmersion (X.toSpecΓ ≫ h) := by
  rw [← Scheme.Hom.isoOpensRange_hom_ι X.toSpecΓ, Category.assoc]
  have : IsOpenImmersion (X.toSpecΓ.opensRange.ι ≫ h) := heq ▸ hoi
  infer_instance

/-- **An open immersion of the union of standard opens is an open immersion of the scheme.**  If
the affine basic opens `X.basicOpen (f l)` cover the quasi-affine scheme `X`, and the inclusion
of `⨆ l, D(f l)` into `Spec Γ(X, ⊤)` becomes an open immersion after composing with `h`, then
`X ⟶ Spec Γ(X, ⊤) ⟶ _` is an open immersion. -/
lemma isOpenImmersion_toSpecΓ_comp {X : Scheme.{u}} [X.IsQuasiAffine] {ι : Type v}
    (f : ι → Γ(X, ⊤)) (haff : ∀ l, IsAffineOpen (X.basicOpen (f l)))
    (hcov : ⨆ l, X.basicOpen (f l) = ⊤) {Z : Scheme.{u}} (h : Spec Γ(X, ⊤) ⟶ Z)
    (hoi : IsOpenImmersion
      ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec Γ(X, ⊤)).Opens).ι ≫ h)) :
    IsOpenImmersion (X.toSpecΓ ≫ h) :=
  isOpenImmersion_toSpecΓ_comp_of_opensRange_eq f
    (X.opensRange_toSpecΓ_eq_iSup_basicOpen f haff hcov) h hoi

end AlgebraicGeometry
