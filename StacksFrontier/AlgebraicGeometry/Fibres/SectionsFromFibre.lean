module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Sections

/-!
# Extending a function on a fibre to a neighbourhood of the base point

Let `f : X ⟶ S` be a morphism of schemes and let `s : S`.  Stacks Tag 0G7X asserts that for `f`
*proper* every **idempotent** `e ∈ Γ(X_s, 𝒪_{X_s})` lies in the image of the canonical map
`(f_*𝒪_X)_s → Γ(X_s, 𝒪_{X_s})`;  since that stalk is the colimit of the `Γ(X, f ⁻¹ᵁ U)` over the
open neighbourhoods `U` of `s`, the assertion is that `e` is the restriction to the fibre of a
section of `𝒪_X` over `f ⁻¹ᵁ U` for some `U ∋ s`.  That is the predicate
`ExtendsOverNeighbourhood` below.

Tag 0G7X **is not proved here**;  see the implementation notes.  What is proved is a group of
unconditional special cases, in each of which the extension exists for *every* function on the
fibre, not merely for the idempotents:

* if the fibre is preconnected there is nothing to prove, because then the only idempotents of
  `Γ(X_s, 𝒪_{X_s})` are `0` and `1`;
* if `{s}` is closed then `X_s` is a *closed subscheme* of `X`, so a function on `X_s` extends to
  any affine open of `X` containing it.  This settles Tag 0G7X at a closed point whenever such an
  affine open can be reached by sections coming from the base:  for an affine morphism, where
  `f ⁻¹ᵁ U` is affine as soon as `U` is;  and for a closed morphism whose fibre happens to lie in
  an affine open of `X`, where closedness is what shrinks `U` until `f ⁻¹ᵁ U` lies inside that
  affine open.

In particular Tag 0G7X holds at closed points for *finite* morphisms, which are exactly the
proper affine ones.

## Main results

* `Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood`: the conclusion of
  Tag 0G7X for a single function on the fibre.
* `Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι`: at a closed point the
  fibre is a closed subscheme of `X`.
* `Stacks.AlgebraicGeometry.Fibres.surjective_fiberι_appLE`: at a closed point,
  restriction `Γ(X, W) → Γ(X_s, 𝒪_{X_s})` is surjective for every affine open `W` containing the
  fibre.
* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isAffineHom` and
  `..._of_isFinite`: Tag 0G7X for an affine, hence for a finite, morphism at a closed point.
* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isClosedMap` and
  `..._of_universallyClosed`: Tag 0G7X at a closed point for a closed morphism whose fibre lies
  in an affine open.
* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isIdempotentElem`:
  Tag 0G7X for an arbitrary morphism with preconnected fibre.

## Implementation notes

**What the general case needs and why it is not reached.**  The Stacks proof of Tag 0G7X runs the
theorem on formal functions (Tag 02OD) at `p = 0`:  for `S` Noetherian it identifies the
completion `(f_*𝒪_X)_s^∧` with `lim_n Γ(X_n, 𝒪_{X_n})` over the infinitesimal neighbourhoods
`X_n` of `X_s`, each of which has the same underlying space as `X_s` and therefore carries the
same idempotent;  the limit idempotent is then pushed back down through
`(f_*𝒪_X)_s^∧ / 𝔪_s (f_*𝒪_X)_s^∧ = (f_*𝒪_X)_s / 𝔪_s (f_*𝒪_X)_s`, and the general case follows by
Noetherian approximation (Tags 0A0P, 0CUG, 01Z0).  Tag 02OD rests on Tag 02OC, whose proof is an
Artin–Rees/Mittag-Leffler argument using the connecting maps `H^0 → H^1` of the sequences
`0 → I^n ℱ → ℱ → ℱ/I^n ℱ → 0`.  Those connecting maps ARE available: Mathlib has `Sheaf.H` and
`Sheaf.H'` in every degree, the covariant `Ext` long exact sequence supplies the connecting
homomorphism, and `Stacks.Cohomology.Scheme.δ`
(`StacksFrontier/AlgebraicGeometry/FormalFunctions/SchemeCohomologySequence.lean`)
is that map in the
groups Tag 071L is stated in.  The chain is blocked further up instead.  Tag 02O5 — coherence of
the higher direct images of a proper morphism — IS proved here, unconditionally, as
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent` and
`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward` in
`StacksFrontier/AlgebraicGeometry/ProperCoherenceWitness/ChowStalk.lean`, as is Tag 02O6;
what has no
unconditional form here is the rest of `02O8 → 02OA → 02OB → 02OC`, each step of which takes the
one below it as a hypothesis, down to Tag 0897 part (1).  So Tag 02OC, and with it Tag 02OD and the
general case of Tag 0G7X, is out of reach.  Nothing below is conditional on any of that.

The cases proved here exploit `AlgebraicGeometry.Scheme.Hom.app_surjective` instead:  a closed
immersion is surjective on sections over an *affine* open of the target.  The fibre inclusion
`f.fiberι s` is a base change of `S.fromSpecResidueField s`, which is a closed immersion exactly
when `{s}` is closed (`AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion`).  At a
non-closed point this fails, and the fibre is a closed subscheme only of the base change of `X`
to `Spec 𝒪_{S,s}`;  relating the sections of that base change to the sections over the
`f ⁻¹ᵁ U` is a localisation argument not carried out here.  For `f` proper but not affine the
obstruction is different and genuine:  `Γ(X, f ⁻¹ᵁ U) → Γ(X_s, 𝒪_{X_s})` need not be surjective
at all, which is why Tag 0G7X claims only that the idempotents lift.

## References

* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Fibres

variable {X S : Scheme.{u}}

/-- The fibre inclusion pulls an open `W` of `X` back to all of the scheme-theoretic fibre as
soon as `W` contains the set-theoretic fibre.  This is the elementary fact behind the shape of
the conclusion of Stacks Tag 0G7X, which speaks about sections over `f ⁻¹ᵁ U`. -/
lemma fiberι_preimage_eq_top_of_preimage_subset (f : X ⟶ S) (s : S) {W : X.Opens}
    (h : f ⁻¹' {s} ⊆ (W : Set X)) : f.fiberι s ⁻¹ᵁ W = ⊤ := by
  ext x
  constructor
  · intro; trivial
  · intro
    exact h ((f.range_fiberι s).le ⟨x, rfl⟩)

/-- Every point of the scheme-theoretic fibre `X_s` lies over `s`, so the fibre is carried into
`f ⁻¹ᵁ U` for every open `U` of `S` containing `s`.  Stacks Tag 0G7X. -/
lemma fiberι_preimage_preimage_eq_top (f : X ⟶ S) {s : S} {U : S.Opens} (hs : s ∈ U) :
    f.fiberι s ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ :=
  fiberι_preimage_eq_top_of_preimage_subset f s fun x (hx : f x = s) => show f x ∈ U from hx ▸ hs

/-- `ExtendsOverNeighbourhood f s e` says that the function `e` on the scheme-theoretic fibre
`X_s` of `f : X ⟶ S` over `s` is the restriction of a section of `𝒪_X` over `f ⁻¹ᵁ U` for some
open neighbourhood `U` of `s`.  Equivalently, `e` lies in the image of the canonical map
`(f_*𝒪_X)_s → Γ(X_s, 𝒪_{X_s})`, that stalk being the colimit of the `Γ(X, f ⁻¹ᵁ U)`.  This is
the conclusion of Stacks Tag 0G7X, which asserts it for `f` proper and `e` idempotent. -/
def ExtendsOverNeighbourhood (f : X ⟶ S) (s : S) (e : Γ(f.fiber s, ⊤)) : Prop :=
  ∃ (U : S.Opens) (hs : s ∈ U) (a : Γ(X, f ⁻¹ᵁ U)),
    (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ (fiberι_preimage_preimage_eq_top f hs).ge a = e

/-- A morphism surjective on the sections over `W` is surjective on the sections over any open
that the preimage of `W` exhausts. -/
private lemma surjective_appLE_of_surjective_app {Y Z : Scheme.{u}} (g : Y ⟶ Z) {W : Z.Opens}
    {V : Y.Opens} (hV : g ⁻¹ᵁ W = V) (h : Function.Surjective (g.app W)) :
    Function.Surjective (g.appLE W V hV.ge) := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  exact h

/-- At a closed point the scheme-theoretic fibre is a closed subscheme of `X`:  the fibre
inclusion `f.fiberι s` is a base change of the closed immersion `S.fromSpecResidueField s`.
This is the one geometric input to the cases of Stacks Tag 0G7X proved below. -/
lemma isClosedImmersion_fiberι (f : X ⟶ S) {s : S} (hs : IsClosed ({s} : Set S)) :
    IsClosedImmersion (f.fiberι s) := by
  have : IsClosedImmersion (S.fromSpecResidueField s) :=
    isClosed_singleton_iff_isClosedImmersion.mp hs
  exact inferInstanceAs (IsClosedImmersion (Limits.pullback.fst f (S.fromSpecResidueField s)))

/-- **Stacks Tag 0G7X at a closed point, over an affine open containing the fibre.**  If `{s}` is
closed and `W` is an affine open of `X` whose preimage exhausts the fibre, then every function on
`X_s` — not merely every idempotent — is the restriction of a section of `𝒪_X` over `W`. -/
theorem surjective_fiberι_appLE (f : X ⟶ S) {s : S} (hs : IsClosed ({s} : Set S))
    {W : X.Opens} (hW : IsAffineOpen W) (htop : f.fiberι s ⁻¹ᵁ W = ⊤) :
    Function.Surjective ((f.fiberι s).appLE W ⊤ htop.ge) :=
  have := isClosedImmersion_fiberι f hs
  surjective_appLE_of_surjective_app _ htop ((f.fiberι s).app_surjective W hW)

/-- **Stacks Tag 0G7X for an affine morphism at a closed point.**  This is a special case of
Tag 0G7X, which asserts the same conclusion for every proper morphism and every point;  the
general case is not proved in this repository, see the module documentation. -/
theorem extendsOverNeighbourhood_of_isAffineHom (f : X ⟶ S) [IsAffineHom f] {s : S}
    (hs : IsClosed ({s} : Set S)) (e : Γ(f.fiber s, ⊤)) : ExtendsOverNeighbourhood f s e := by
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top s)
  obtain ⟨a, ha⟩ :=
    surjective_fiberι_appLE f hs (hU.preimage f) (fiberι_preimage_preimage_eq_top f hsU) e
  exact ⟨U, hsU, a, ha⟩

/-- **Stacks Tag 0G7X for a finite morphism at a closed point.**  Finite morphisms are exactly
the proper affine ones, so this is the proper case of Tag 0G7X for an affine morphism;  the
general proper case is not proved in this repository, see the module documentation. -/
theorem extendsOverNeighbourhood_of_isFinite (f : X ⟶ S) [IsFinite f] {s : S}
    (hs : IsClosed ({s} : Set S)) (e : Γ(f.fiber s, ⊤)) : ExtendsOverNeighbourhood f s e :=
  extendsOverNeighbourhood_of_isAffineHom f hs e

/-- If `f` is a closed map and the set-theoretic fibre over `s` is contained in an open `W`, then
`f ⁻¹ᵁ U ≤ W` already for some open neighbourhood `U` of `s`, namely the complement of the closed
set `f '' Wᶜ`.  For `f` proper this is how a neighbourhood of `s` is shrunk until its preimage
lies inside a chosen affine open, as in Stacks Tag 0G7X. -/
lemma exists_mem_and_preimage_le (f : X ⟶ S) (hf : IsClosedMap f) (s : S) {W : X.Opens}
    (h : f ⁻¹' {s} ⊆ (W : Set X)) : ∃ U : S.Opens, s ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  refine ⟨⟨(f '' (W : Set X)ᶜ)ᶜ, (hf _ (isClosed_compl_iff.mpr W.isOpen)).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨x, hx, hxs⟩
    exact hx (h hxs)
  · intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩

/-- **Stacks Tag 0G7X at a closed point for a closed morphism whose fibre lies in an affine
open.**  The conclusion holds for every function on the fibre, not merely for the idempotents.
The general case of Tag 0G7X, where no affine open of `X` contains the fibre, is not proved in
this repository, see the module documentation. -/
theorem extendsOverNeighbourhood_of_isClosedMap (f : X ⟶ S) (hf : IsClosedMap f) {s : S}
    (hs : IsClosed ({s} : Set S)) {W : X.Opens} (hW : IsAffineOpen W)
    (hfib : f ⁻¹' {s} ⊆ (W : Set X)) (e : Γ(f.fiber s, ⊤)) : ExtendsOverNeighbourhood f s e := by
  obtain ⟨U, hsU, hle⟩ := exists_mem_and_preimage_le f hf s hfib
  obtain ⟨a, ha⟩ :=
    surjective_fiberι_appLE f hs hW (fiberι_preimage_eq_top_of_preimage_subset f s hfib) e
  refine ⟨U, hsU, X.presheaf.map (homOfLE hle).op a, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact ha

/-- **Stacks Tag 0G7X at a closed point for a universally closed — in particular a proper —
morphism whose fibre lies in an affine open.**  The general case of Tag 0G7X is not proved in
this repository, see the module documentation. -/
theorem extendsOverNeighbourhood_of_universallyClosed (f : X ⟶ S) [UniversallyClosed f] {s : S}
    (hs : IsClosed ({s} : Set S)) {W : X.Opens} (hW : IsAffineOpen W)
    (hfib : f ⁻¹' {s} ⊆ (W : Set X)) (e : Γ(f.fiber s, ⊤)) : ExtendsOverNeighbourhood f s e :=
  extendsOverNeighbourhood_of_isClosedMap f f.isClosedMap hs hW hfib e

/-- **Stacks Tag 0G7X for a preconnected fibre.**  Over a preconnected fibre the only idempotents
of `Γ(X_s, 𝒪_{X_s})` are `0` and `1`, and those are restrictions of the global constants;  no
properness is needed.  This is the degenerate case of Tag 0G7X, in which the disjoint union
decomposition of the fibre attached to the idempotent is the trivial one. -/
theorem extendsOverNeighbourhood_of_isIdempotentElem (f : X ⟶ S) (s : S)
    [PreconnectedSpace (f.fiber s)] {e : Γ(f.fiber s, ⊤)} (he : IsIdempotentElem e) :
    ExtendsOverNeighbourhood f s e := by
  have hconn : _root_.IsPreconnected ((⊤ : (f.fiber s).Opens) : Set (f.fiber s)) := by
    simpa only [Opens.coe_top] using isPreconnected_univ
  obtain h | h := ProperGeomConnected.isIdempotentElem_eq_zero_or_one hconn he
  · exact ⟨⊤, Opens.mem_top s, 0, by rw [map_zero, h]⟩
  · exact ⟨⊤, Opens.mem_top s, 1, by rw [map_one, h]⟩

end Stacks.AlgebraicGeometry.Fibres
