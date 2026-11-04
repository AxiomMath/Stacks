module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings

/-!
# The groupoid of the étale local structure of a quasi-DM stack (Stacks 0DU3, clause (3))

**Stacks 0DU3** says that an algebraic stack `𝒳` which is quasi-DM with separated diagonal has,
near every point `x ∈ |𝒳|`, an étale chart by a quotient stack of a very restricted shape: there
is a 1-morphism `𝒰 ⟶ 𝒳` with (1) a point of `|𝒰|` over `x`, (2) `𝒰 ⟶ 𝒳` representable by
algebraic spaces and étale, and (3) `𝒰 = [U/R]` for a groupoid scheme `(U, R, s, t, c)` with `U`
and `R` affine and `s` and `t` finite, flat and locally of finite presentation.

The groupoid of clause (3) is not an extra choice: the source's proof produces it as a
*quasi-splitting* of the self-intersection groupoid of an affine flat locally finitely presented
locally quasi-finite chart, in the sense of **Stacks 04RK**, part (3) — an open subgroupoid
`P ⊆ R` on the same object scheme whose restricted source and target are finite and which
contains the identity arrow at the chosen point.  This file proves that such a quasi-splitting
*is* a groupoid of the shape clause (3) demands, which is the only step of the proof of
Stacks 0DU3 that checks the properties clause (3) asserts.

Nothing here asserts clause (1) or clause (2), and nothing here mentions `𝒳`; see the
implementation notes for the precise obstructions.

## Main results

* `Stacks.Groupoids.GroupoidScheme.exists_quasiSplitting_isAffine_isFinite_flat`:
  **Stacks 0DU3, the groupoid of clause (3).**  For a groupoid scheme with affine object scheme
  and with flat, locally finitely presented source and target, a quasi-splitting over a point of
  the object scheme is, as a groupoid scheme in its own right, one with *both* structure schemes
  affine and with source and target finite, flat and locally of finite presentation.

## The argument

Let `P ⊆ R` be the quasi-splitting, `ι : P ⟶ R` its inclusion and `U` the common object scheme.

*Affineness of the object scheme.*  The object scheme of the subgroupoid is recorded as being
*equal* to `U`, so it is affine because `U` is.

*Flatness and local finite presentation of `s|_P` and `t|_P`.*  The compatibility of `ι` with the
source maps says `s|_P = ι ≫ s` up to the transport along that equality of object schemes.  An
open immersion is flat and locally of finite presentation, a transport along an equality is an
isomorphism, and both properties are stable under composition.

*Affineness of the arrow scheme.*  This is where finiteness of the splitting is used, and it is
the one assertion of clause (3) that is not local on the arrow scheme: `s|_P` is finite, hence
affine, and the object scheme is affine, so the arrow scheme is affine.  Note that `P` is merely
an *open* subscheme of `R`, so its affineness is not inherited from affineness of `R` — it is
genuinely a consequence of finiteness of `s|_P`.

## Implementation notes

Clause (3) of the tag also asserts the identification `𝒰 = [U/P]`, and clauses (1) and (2) are
about the 1-morphism `𝒰 ⟶ 𝒳`.  None of the three is stated here, and the obstructions are named
rather than assumed:

* The quotient stack `[U/P]` is defined in this library only for a groupoid in *algebraic
  spaces*, `AlgebraicGeometry.Stack.quotientStack`.  A groupoid scheme can be realized as one,
  by `Stacks.Groupoids.GroupoidScheme.realization`, but that comparison is defined on groupoid
  schemes only and not on their morphisms, so the 1-morphism `[U/P] ⟶ [U/R]` that clause (2) is
  about cannot be formed from a morphism of groupoid schemes at all.
* Étaleness of `[U/P] ⟶ [U/R]`, which is the substance of clause (2), is **Stacks 0DU2**,
  `AlgebraicGeometry.Stack.isAlgebraicStack_representable_surjective_etale_quotientStackMap`,
  which is stated for a morphism of groupoids in algebraic spaces and so does not reach a
  morphism of groupoid schemes, for the reason of the previous point.
* The chart `U ⟶ 𝒳` that the source's proof starts from comes from **Stacks 06MF**, whose
  substantial direction this library carries as the hypothesis
  `AlgebraicGeometry.Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM`, and the groupoid
  `R = U ×_𝒳 U` needs part (1) of **Stacks 04T4**, which the docstring of
  `StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection` records as blocked on the
  equivalences of Stacks 045G.

Two private lemmas of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingAffineLocalization` —
`openFiniteSubgroupoid_source_eq` and `openFiniteSubgroupoid_target_eq` — say exactly what the
two source compatibilities of the inclusion amount to.  They are `private` there, so they are
reproved here, privately, rather than imported.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 0DU2](https://stacks.math.columbia.edu/tag/0DU2)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {G : GroupoidScheme S}

/-- The source morphism of an open finite subgroupoid is the ambient source morphism restricted
along the open immersion of arrow schemes, transported along the equality of object schemes.

This is `private` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingAffineLocalization` and so is
reproved here. -/
private theorem openFiniteSubgroupoid_source_eq' (P : OpenFiniteSubgroupoid G) :
    P.subgroupoid.source = P.inclusion.mapArrows ≫ G.source ≫ eqToHom P.objects_eq.symm := by
  rw [← Category.assoc, P.inclusion.map_source, P.mapObjects_eq, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- The target morphism of an open finite subgroupoid is the ambient target morphism restricted
along the open immersion of arrow schemes, transported along the equality of object schemes.

This is `private` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingAffineLocalization` and so is
reproved here. -/
private theorem openFiniteSubgroupoid_target_eq' (P : OpenFiniteSubgroupoid G) :
    P.subgroupoid.target = P.inclusion.mapArrows ≫ G.target ≫ eqToHom P.objects_eq.symm := by
  rw [← Category.assoc, P.inclusion.map_target, P.mapObjects_eq, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- Flatness and local finite presentation pass from an ambient structure map to its restriction
to an open finite subgroupoid. -/
private theorem flat_and_lfp_of_eq_comp (P : OpenFiniteSubgroupoid G)
    {f : G.arrows ⟶ G.objects} {g : P.subgroupoid.arrows ⟶ P.subgroupoid.objects}
    [Flat f.left] [LocallyOfFinitePresentation f.left]
    (hg : g = P.inclusion.mapArrows ≫ f ≫ eqToHom P.objects_eq.symm) :
    Flat g.left ∧ LocallyOfFinitePresentation g.left := by
  have hopen := P.arrows_open
  have hiso : IsIso (eqToHom P.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom P.objects_eq.symm)))
  have : g.left = P.inclusion.mapArrows.left ≫ f.left ≫ (eqToHom P.objects_eq.symm).left := by
    rw [hg]
    rfl
  rw [this]
  exact ⟨inferInstance, inferInstance⟩

/-- **Stacks 0DU3, the groupoid of clause (3).**

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` affine and with `s` and `t` flat and
locally of finite presentation, and let `u` be a point of `U` over which the groupoid is
quasi-split in the sense of **Stacks 04RK**, part (3).  Then there is a groupoid scheme
`(U, P, s|_P, t|_P, c|_P)` together with a morphism into `(U, R, s, t, c)` which is an open
immersion on arrow schemes and the identity on object schemes, carrying the identity arrow at
`u`, whose *both* structure schemes are affine and whose source and target are finite, flat and
locally of finite presentation.

This is the groupoid scheme of clause (3) of **Stacks 0DU3**, with every property that clause
asserts of it: the source's proof takes `𝒰 = [U/P]` for exactly this `P`.  The properties are
asserted of one single groupoid scheme, as the tag asserts them.

The three conjuncts that are not re-derivations are the equality of object schemes, the open
immersion and the identity arrow: these are the three pieces of data a quasi-splitting *is*
(conditions (a) and (c) of Stacks 04RK), and they are listed so that the groupoid produced is
pinned to be the quasi-splitting at `u` rather than an unrelated groupoid.  Everything else is
derived: affineness of the object scheme from the equality, flatness and local finite
presentation of `s|_P` and `t|_P` from the open immersion composed with `s` and `t`, and
affineness of the arrow scheme from finiteness of `s|_P` over the affine object scheme — the
last being the step where an *open* subscheme of `R` is shown affine without `R` being used at
all. -/
@[stacks 0DU3 "the groupoid scheme of clause (3), with U and its arrow scheme affine and source \
and target finite, flat and locally of finite presentation, built from a quasi-splitting of \
Stacks 04RK. Clause (1), clause (2) and the identification of the stack with [U/R] in clause \
(3) are NOT covered: see the implementation notes for the three named obstructions"]
theorem exists_quasiSplitting_isAffine_isFinite_flat [IsAffine G.objects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    {u : G.objects.left} (h : IsQuasiSplitAt G u) :
    ∃ (G' : GroupoidScheme S) (φ : Hom G' G),
      G'.objects = G.objects ∧
      IsOpenImmersion φ.mapArrows.left ∧
      (∃ p : G'.arrows.left, φ.mapArrows.left.base p = G.identity.left.base u) ∧
      IsAffine G'.objects.left ∧ IsAffine G'.arrows.left ∧
      IsFinite G'.source.left ∧
      Flat G'.source.left ∧ LocallyOfFinitePresentation G'.source.left ∧
      IsFinite G'.target.left ∧
      Flat G'.target.left ∧ LocallyOfFinitePresentation G'.target.left := by
  obtain ⟨P⟩ := h
  have hobj : IsAffine P.subgroupoid.objects.left := by
    rw [P.objects_eq]
    infer_instance
  obtain ⟨hsflat, hslfp⟩ := flat_and_lfp_of_eq_comp P.toOpenFiniteSubgroupoid
    (openFiniteSubgroupoid_source_eq' P.toOpenFiniteSubgroupoid)
  obtain ⟨htflat, htlfp⟩ := flat_and_lfp_of_eq_comp P.toOpenFiniteSubgroupoid
    (openFiniteSubgroupoid_target_eq' P.toOpenFiniteSubgroupoid)
  have hsfin : IsFinite P.subgroupoid.source.left := P.source_finite
  have htfin : IsFinite P.subgroupoid.target.left := P.target_finite
  exact ⟨P.subgroupoid, P.inclusion, P.objects_eq, P.arrows_open, P.contains_identity, hobj,
    isAffine_of_isAffineHom P.subgroupoid.source.left, hsfin, hsflat, hslfp, htfin, htflat,
    htlfp⟩

end Stacks.Groupoids.GroupoidScheme

end
