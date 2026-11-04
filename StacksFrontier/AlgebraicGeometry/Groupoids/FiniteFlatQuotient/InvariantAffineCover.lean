module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.RankDecomposition

/-!
# Invariant affine coverings of a finite locally free groupoid scheme

Let a groupoid scheme have finite locally free source and target maps.  Say that a point of its
object scheme *has affine orbit* when its orbit under the arrows is contained in an affine open.
Such a point has an invariant affine open neighbourhood (Stacks 03JE), so the invariant affine
opens cover the locus of points with affine orbit.  They cover the whole object scheme as soon
as every nonempty closed subset contains a point with affine orbit.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.HasAffineOrbit`: the orbit of the point is contained in an
  affine open.
* `AlgebraicGeometry.GroupoidScheme.HasAffineOrbitInEveryClosed`: every nonempty closed subset
  of the object scheme contains a point with affine orbit.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_invariantAffineOpen_iSup_eq_top`: under
  `HasAffineOrbitInEveryClosed` the object scheme is covered by invariant affine opens, one for
  each point with affine orbit.
* `AlgebraicGeometry.GroupoidScheme.isAffine_restrictionArrows_of_isInvariantOpen`: the arrow
  scheme of the restriction of the groupoid to an invariant affine open is affine, when the
  source map is an affine morphism.
* `AlgebraicGeometry.GroupoidScheme.property_restrict_source_target_of_isInvariantOpen`: the
  source and target maps of the restriction to an invariant open inherit every property of
  morphisms of schemes stable under base change, and
  `AlgebraicGeometry.GroupoidScheme.property_target_of_property_source`: the target map of any
  groupoid scheme inherits every isomorphism-invariant property of its source map.
* `AlgebraicGeometry.GroupoidScheme.hasAffineOrbitInEveryClosed_of_forall`: the condition holds
  when every point has affine orbit, and
  `AlgebraicGeometry.GroupoidScheme.hasAffineOrbitInEveryClosed_of_specializes`: it holds when
  every point specializes to a point with affine orbit.

## Implementation notes

The covering family is indexed by the subtype of points with affine orbit rather than by a set
of opens, so that its cardinality is bounded by that of the point set of the object scheme;
that bound is what a size-restricted site asks of a covering family.

## References

* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- A point of the object scheme of a groupoid scheme *has affine orbit* when the orbit of the
point under the arrows of the groupoid is contained in an affine open of the object scheme. -/
@[sga "3 V 4.1"]
def HasAffineOrbit (G : GroupoidScheme S) (x : G.objects.left) : Prop :=
  ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
    ∀ r : G.arrows.left, G.source.left.base r = x → G.target.left.base r ∈ W

/-- The locus of points with affine orbit meets every nonempty closed subset of the object
scheme.  This is hypothesis (3) of Stacks 07S6. -/
def HasAffineOrbitInEveryClosed (G : GroupoidScheme S) : Prop :=
  ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty → ∃ x ∈ Z, HasAffineOrbit G x

/-- If every point of the object scheme has affine orbit, then every nonempty closed subset
contains such a point. -/
theorem hasAffineOrbitInEveryClosed_of_forall {G : GroupoidScheme S}
    (h : ∀ x : G.objects.left, HasAffineOrbit G x) : HasAffineOrbitInEveryClosed G :=
  fun _ _ ⟨x, hx⟩ => ⟨x, hx, h x⟩

/-- If every point of the object scheme specializes to a point with affine orbit, then every
nonempty closed subset contains a point with affine orbit. -/
theorem hasAffineOrbitInEveryClosed_of_specializes {G : GroupoidScheme S}
    (h : ∀ x : G.objects.left, ∃ y, x ⤳ y ∧ HasAffineOrbit G y) :
    HasAffineOrbitInEveryClosed G := by
  intro Z hZ ⟨x, hx⟩
  obtain ⟨y, hxy, hy⟩ := h x
  exact ⟨y, hZ.stableUnderSpecialization hxy hx, hy⟩

/-- **Stacks 07S6, the invariant affine covering.** Let a groupoid scheme have finite locally
free source and target maps and assume every nonempty closed subset of the object scheme
contains a point whose orbit lies in an affine open.  Then the object scheme is covered by
invariant affine opens, one containing each point with affine orbit. -/
@[sga "1 V 1.8" "partial"]
theorem exists_invariantAffineOpen_iSup_eq_top (G : GroupoidScheme S)
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    (h3 : HasAffineOrbitInEveryClosed G) :
    ∃ V : {x : G.objects.left // HasAffineOrbit G x} → G.objects.left.Opens,
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, IsInvariantOpen G (V i)) ∧
        (∀ i, (i : G.objects.left) ∈ V i) ∧ ⨆ i, V i = ⊤ := by
  classical
  choose V hVaff hVmem hVinv using fun i : {x : G.objects.left // HasAffineOrbit G x} =>
    exists_invariant_affine_open_of_orbit_subset_affine G i.1 i.2
  refine ⟨V, hVaff, hVinv, hVmem, ?_⟩
  by_contra hne
  obtain ⟨x, hx⟩ : ((⨆ i, V i : G.objects.left.Opens) : Set G.objects.left)ᶜ.Nonempty := by
    rwa [Set.nonempty_compl, ne_eq, Opens.coe_eq_univ]
  obtain ⟨y, hyZ, hy⟩ := h3 _ (isClosed_compl_iff.2 (⨆ i, V i).2) ⟨x, hx⟩
  exact hyZ (Opens.mem_iSup.2 ⟨⟨y, hy⟩, hVmem ⟨y, hy⟩⟩)

/-! ### The restriction to an invariant affine open is an affine groupoid -/

/-- **The restriction of a groupoid scheme with affine source map to an invariant affine open
is affine.** For an invariant open `V` of the object scheme, the arrow scheme of the restriction
of the groupoid to `V` is the preimage of `V` under the source map; when the source map is an
affine morphism and `V` is an affine open, that preimage is affine. -/
theorem isAffine_restrictionArrows_of_isInvariantOpen (G : GroupoidScheme S)
    [IsAffineHom G.source.left] (V : G.objects.left.Opens) (hV : IsInvariantOpen G V)
    (hVaff : IsAffineOpen V) (g : Over.mk (V.ι ≫ G.objects.hom) ⟶ G.objects)
    (hg : g.left = V.ι) :
    IsAffine (restrictionArrows G g).left := by
  obtain ⟨e, -⟩ := restriction_arrows_iso_source_open G V hV g hg
  have _ : IsAffine V.toScheme := hVaff
  exact IsAffine.of_isIso e.hom

/-- Every property of morphisms of schemes invariant under isomorphism which holds for the
source map of a groupoid scheme holds for its target map. -/
theorem property_target_of_property_source (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (G : GroupoidScheme S) (hP : P G.source.left) : P G.target.left := by
  have _ : IsIso G.inverse.left := groupoidInverse_left_isIso G
  have heq : G.inverse.left ≫ G.source.left = G.target.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left G.source_inverse
  rw [← heq]
  exact MorphismProperty.RespectsIso.precomp P G.inverse.left G.source.left hP

/-- For an invariant open of the object scheme, the source map of the restriction of a groupoid
scheme is, up to isomorphism, the base change of the source map along the inclusion of that
open.  So it inherits every property of morphisms of schemes which is stable under base
change. -/
theorem property_restrictionSource_of_isInvariantOpen (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (G : GroupoidScheme S) (V : G.objects.left.Opens)
    (hV : IsInvariantOpen G V) (hP : P G.source.left)
    (g : Over.mk (V.ι ≫ G.objects.hom) ⟶ G.objects) (hg : g.left = V.ι) :
    P (restrictionSource G g).left := by
  obtain ⟨e, he⟩ := restriction_arrows_iso_source_open G V hV g hg
  have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hbc : P (pullback.snd G.source.left V.ι) := MorphismProperty.pullback_snd _ _ hP
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp P e.hom _ hbc

/-- The source and target maps of the restriction of a groupoid scheme to an invariant open of
its object scheme inherit every property of morphisms of schemes which is stable under base
change from the source map of the groupoid. -/
theorem property_restrict_source_target_of_isInvariantOpen (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (G : GroupoidScheme S) (V : G.objects.left.Opens)
    (hV : IsInvariantOpen G V) (hP : P G.source.left)
    (g : Over.mk (V.ι ≫ G.objects.hom) ⟶ G.objects) (hg : g.left = V.ι) :
    P (restrict G g).groupoid.source.left ∧ P (restrict G g).groupoid.target.left := by
  have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsrc : P (restrict G g).groupoid.source.left := by
    have hleft : (restrict G g).groupoid.source.left =
        eqToHom (congrArg Over.left (restrict G g).arrows_eq) ≫
          (restrictionSource G g).left ≫
            eqToHom (congrArg Over.left (restrict G g).objects_eq.symm) := by
      rw [(restrict G g).source_eq]
      simp [Over.eqToHom_left]
    rw [hleft]
    exact MorphismProperty.RespectsIso.precomp P _ _
      (MorphismProperty.RespectsIso.postcomp P _ _
        (property_restrictionSource_of_isInvariantOpen P G V hV hP g hg))
  exact ⟨hsrc, property_target_of_property_source P (restrict G g).groupoid hsrc⟩

end AlgebraicGeometry.GroupoidScheme

end
