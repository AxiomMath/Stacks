module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientRepresents
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The finite flat quotient of an affine groupoid, and of a restriction to an invariant affine

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` and `R` affine, with `s` and `t`
finite locally free, and with `(t, s)` an equivalence relation. The invariant spectrum, with its
canonical projection, is a finite flat quotient in the sense of
`Stacks.Groupoids.FiniteFlatQuotient`. The same holds for the restriction of such a groupoid to
an invariant open with affine source, and the quotient can be chosen of size at most that of the
open.

## Main definitions

* `AlgebraicGeometry.affineFiniteFlatQuotient` is the finite flat quotient of a groupoid
  scheme with affine object and arrow schemes, built from the invariant spectrum.

## Main results

* `AlgebraicGeometry.nonempty_finiteFlatQuotient_of_isAffine`: a groupoid scheme with affine
  object and arrow schemes, finite locally free source and target maps and an equivalence
  relation for its pre-relation has a finite flat quotient.
* `AlgebraicGeometry.nonempty_finiteFlatQuotient_restriction` and
  `AlgebraicGeometry.nonempty_finiteFlatQuotient_restriction_of_isInvariantOpen`: the
  restriction of such a groupoid along an open immersion with invariant image whose source is
  affine has a finite flat quotient, in the second form with invariance read off an `R`-invariant
  open.
* `AlgebraicGeometry.Space.isField_invariantRing`: the invariant ring is a field when the
  object scheme has at most one point and its global functions form a domain.
* `AlgebraicGeometry.size_quotientOver_le` and `AlgebraicGeometry.contains_quotientOver`: the
  affine quotient has size at most that of the object scheme, so it belongs to a big fppf site
  whenever the object scheme does.
* `AlgebraicGeometry.exists_finiteFlatQuotient_restriction_size_le`: the finite flat quotient of
  such a restriction can be chosen with quotient scheme of size at most that of the source of
  the open immersion.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms AlgebraicGeometry.GroupoidScheme

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The finite flat quotient of an affine groupoid scheme: for a groupoid scheme over `S` with
affine object and arrow schemes, finite locally free source and target maps and an equivalence
relation for its pre-relation, the invariant spectrum, with its canonical projection, as a
finite flat quotient in the sense of `Stacks.Groupoids.FiniteFlatQuotient`. -/
@[sga "3 V 4.1" "special case"]
def affineFiniteFlatQuotient {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] : FiniteFlatQuotient G where
  space := quotientOver G
  quotientMap := quotientProjection G
  finiteLocallyFree := objectsToInvariantSpectrum_isFiniteLocallyFree G
  surjective := by
    change Surjective (objectsToInvariantSpectrum G)
    exact (surjective_iff _).2 (surjective_objectsToInvariantSpectrum G)
  kernelPair :=
    (isPullback_objectsToInvariantSpectrum G).of_map (Over.forget S)
      (Over.OverMorphism.ext (isPullback_objectsToInvariantSpectrum G).w)
  represents := by
    intro B hS _hU _hR _hM
    have _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
      BigFppfOver.hasSheafify_type B S hS
    obtain ⟨hM, q, hq, hfac⟩ := quotientSheaf_isRepresented G B hS
    exact exists_iso_sheafifyUlift_quotientPresheaf _ _ _ _ hM q hq hfac

/-- A groupoid scheme with affine object and arrow schemes, finite locally free source and
target maps and an equivalence relation for its pre-relation has a finite flat quotient. -/
@[sga "3 V 4.1" "special case"]
theorem nonempty_finiteFlatQuotient_of_isAffine {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] : Nonempty (FiniteFlatQuotient G) :=
  ⟨affineFiniteFlatQuotient G⟩

/-- The size of the affine quotient `AlgebraicGeometry.quotientOver G` is at most the size of
the object scheme. -/
theorem size_quotientOver_le {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    (quotientOver G).left.size ≤ G.objects.left.size := by
  rw [show (quotientOver G).left = Spec (.of (invariantRing G)) from rfl,
    Scheme.size_of_isAffine, Scheme.size_of_isAffine G.objects.left]
  refine max_le_max le_rfl ?_
  calc Cardinal.mk Γ(Spec (.of (invariantRing G)), ⊤) = Cardinal.mk (invariantRing G) :=
        Cardinal.mk_congr
          ((Scheme.ΓSpecIso (.of (invariantRing G))).commRingCatIsoToRingEquiv).toEquiv
    _ ≤ Cardinal.mk Γ(G.objects.left, ⊤) := Cardinal.mk_le_of_injective Subtype.val_injective

/-- If the object scheme belongs to a big fppf site, so does the affine quotient. -/
theorem contains_quotientOver {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] (B : BigFppfSite.{u})
    (hU : B.Contains G.objects.left) : B.Contains (quotientOver G).left :=
  lt_of_le_of_lt (size_quotientOver_le G) hU

namespace Space

/-- The ring of invariant functions of a finite locally free equivalence relation on an affine
scheme with at most one point whose functions form a domain is a field. -/
theorem isField_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (hdom : IsDomain Γ(G.objects.left, ⊤)) (hsub : Subsingleton ↥G.objects.left) :
    IsField (invariantRing G) := by
  have _ : IsDomain Γ(G.objects.left, ⊤) := hdom
  have h2 : Subsingleton ↥(Spec (CommRingCat.of (invariantRing G))) :=
    (surjective_objectsToInvariantSpectrum G).subsingleton
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp ⟨fun a b ↦ h2.elim a b⟩

end Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)

/-- The restriction of `G` along an open immersion with affine source and invariant image has a
finite flat quotient whose quotient scheme has size at most that of the source. -/
private theorem exists_finiteFlatQuotient_size_le_of_restriction
    (R : GroupoidScheme.Restriction G g)
    [IsOpenImmersion g.left] [IsAffine U'.left] [IsFiniteLocallyFree G.source.left]
    [IsEquivalenceRelation G.target G.source]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    ∃ Q : FiniteFlatQuotient R.groupoid, Q.space.left.size ≤ U'.left.size := by
  have hobj : R.groupoid.objects.left = U'.left := congrArg Over.left R.objects_eq
  have _ : IsAffine R.groupoid.objects.left := by rw [hobj]; infer_instance
  have _ : IsAffine R.groupoid.arrows.left := restriction_isAffine_arrows G g R hinv
  have _ : IsFiniteLocallyFree R.groupoid.source.left :=
    restriction_source_isFiniteLocallyFree G g R hinv
  have _ : IsFiniteLocallyFree R.groupoid.target.left :=
    restriction_target_isFiniteLocallyFree G g R hinv
  have _ : IsEquivalenceRelation R.groupoid.target R.groupoid.source :=
    restriction_isEquivalenceRelation G g R
  exact ⟨affineFiniteFlatQuotient R.groupoid, hobj ▸ size_quotientOver_le R.groupoid⟩

/-- Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `s` finite locally free and with
`(t, s)` an equivalence relation, and let `g : U' ⟶ U` be an open immersion with affine source
whose image is invariant: every arrow whose source lies in the image has its target there too.
Then any groupoid scheme realizing the restriction of `G` along `g` has a finite flat
quotient. -/
theorem nonempty_finiteFlatQuotient_restriction (R : GroupoidScheme.Restriction G g)
    [IsOpenImmersion g.left] [IsAffine U'.left] [IsFiniteLocallyFree G.source.left]
    [IsEquivalenceRelation G.target G.source]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    Nonempty (FiniteFlatQuotient R.groupoid) :=
  (exists_finiteFlatQuotient_size_le_of_restriction G g R hinv).elim fun Q _ ↦ ⟨Q⟩

/-- The conclusion of `AlgebraicGeometry.nonempty_finiteFlatQuotient_restriction` for an open
immersion with affine source whose image is an `R`-invariant open `V` of `U`. -/
theorem nonempty_finiteFlatQuotient_restriction_of_isInvariantOpen
    (R : GroupoidScheme.Restriction G g) [IsOpenImmersion g.left] [IsAffine U'.left]
    [IsFiniteLocallyFree G.source.left] [IsEquivalenceRelation G.target G.source]
    {V : G.objects.left.Opens} (hV : IsInvariantOpen G V)
    (hg : Set.range g.left.base = (V : Set G.objects.left)) :
    Nonempty (FiniteFlatQuotient R.groupoid) :=
  nonempty_finiteFlatQuotient_restriction G g R
    (forall_mem_range_of_isInvariantOpen G g hV hg)

/-- Under the hypotheses of `AlgebraicGeometry.nonempty_finiteFlatQuotient_restriction`, the
finite flat quotient of the restriction can be chosen with quotient scheme of size at most that
of `U'`. -/
theorem exists_finiteFlatQuotient_restriction_size_le (R : GroupoidScheme.Restriction G g)
    [IsOpenImmersion g.left] [IsAffine U'.left] [IsFiniteLocallyFree G.source.left]
    [IsEquivalenceRelation G.target G.source]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    ∃ Q : FiniteFlatQuotient R.groupoid, Q.space.left.size ≤ U'.left.size :=
  exists_finiteFlatQuotient_size_le_of_restriction G g R hinv

end AlgebraicGeometry

end

end
