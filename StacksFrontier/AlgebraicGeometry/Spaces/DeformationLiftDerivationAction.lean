module

public import Mathlib.Algebra.Category.Grp.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf
public import StacksFrontier.Deformation.LiftsOfObjects.Action.PairTorsor

/-!
# The simply transitive action of local derivations on infinitesimal lifts

Let `X ⊂ X'` and `Y ⊂ Y'` be thickenings of algebraic spaces over a base algebraic space `T`
and let `a : X ⟶ Y` be a morphism. For an algebraic space `U'` étale over `X'` the lifts of `a`
over `U'` are the morphisms `a' : U' ⟶ Y'` over `T` restricting to `a` on `U = X ×_{X'} U'`;
they form the sheaf `AlgebraicGeometry.Space.liftSubfunctor` of
[Stacks Project, Tag 061A], the sheaf (061B) of the source.

This file equips that sheaf with the action of local derivations. The acting object is a sheaf
of abelian groups `Θ` on the spaces-étale site of `X'`, standing for the sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` of the source but carried abstractly, together with the
difference of two lifts as a section of it; the implementation notes say what that datum is and
why it is a hypothesis here. The action is the one of the source's notation `θ · a'`: the
translate of a lift `a'` by `θ` is the unique lift whose difference from `a'` is `θ`, which
through Equation (0619) is the unique lift whose comorphism differs from that of `a'` by the
derivation `D = d_{Y/B} ∘ θ`. Over an object carrying a lift it is simply transitive. The
compatibility of the action of Stacks 061C with restriction is proved, for the acting sheaf of
the source, as `AlgebraicGeometry.Space.conormalLiftAction_map` in
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftActionNaturality.lean`.

## Main definitions

* `AlgebraicGeometry.Space.liftSections`: the lifts of `a` over an object of the spaces-étale
  site of `X'`, that is the sections there of the sheaf (061B).
* `AlgebraicGeometry.Space.LiftDerivationAction`: the datum, for every object of the site, of
  the difference of two lifts as a section of `Θ`, in the form of a bijection replacing the
  second member of a pair of lifts by that difference. This is what
  [Stacks Project, Tag 0618], Equation (0619) and [Stacks Project, Tag 04D0] provide; see the
  implementation notes.
* `AlgebraicGeometry.Space.LiftDerivationAction.diff`: the derivation attached to an ordered
  pair of lifts, the `θ` of Equation (0619).
* `AlgebraicGeometry.Space.LiftDerivationAction.addAction`: the action itself, so that
  `θ +ᵥ a'` is the source's `θ · a'`.

## Main results

* `AlgebraicGeometry.Space.LiftDerivationAction.diff_vadd`: **the characterising equation of
  [Stacks Project, Tag 0CK6]**. The derivation attached to the pair `(a', θ · a')` is `θ`; by
  Equation (0619) this says that the comorphisms of `a'` and of `θ · a'` differ by the
  derivation `D` related to `θ` by that equation, which is what the source's notation means.
* `AlgebraicGeometry.Space.LiftDerivationAction.vadd_bijective`: **simple transitivity**. Over
  an object of the site carrying a lift `a'`, translation `θ ↦ θ · a'` is a bijection from the
  sections of `Θ` onto the lifts; equivalently the action is free and transitive there.

## Implementation notes

**What is hypothesised and what is proved.** The datum of
`AlgebraicGeometry.Space.LiftDerivationAction` is the conjunction of three results of the
source, carried as a hypothesis rather than reproved:

* that two lifts over `U'` which agree on `U` and induce the same map of conormal modules
  differ by an `𝒪_B`-derivation — [Stacks Project, Tag 0618], available on the small étale
  site as `AlgebraicGeometry.Space.liftDifference`;
* that such a derivation is `d_{Y/B} ∘ θ` for a unique `θ : a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` —
  Equation (0619), available in both directions as
  `AlgebraicGeometry.Space.derivationDirectImageEquiv`;
* that conversely every `θ` is realised by a unique lift — [Stacks Project, Tag 04D0].

Together these say exactly that `a' ↦ (the θ of the pair (a₀', a'))` is a bijection from the
lifts over `U'` onto the sections of `Θ` for each base lift `a₀'`, which is how the datum is
packaged: as a bijection on pairs fixing the first coordinate, vanishing on the diagonal and
satisfying the cocycle identity. The vanishing and the cocycle identity are the additivity of
the difference, so they too come from Tag 0618: for the sectionwise difference
`AlgebraicGeometry.Space.liftDifference` they are immediate.

What is proved here is everything the two tags add on top of that datum: the action, the
characterising equation that fixes it, and its simple transitivity.

**Why the datum is not derived from the library's form of Tag 0618.** The difference of the
comorphisms of two lifts cannot presently be formed in the spelling used here. The two
comorphisms have different targets `(a')_*𝒪_{X'}` and `(b')_*𝒪_{X'}`, and identifying them is
the structure-sheaf half of [Stacks Project, Tag 05ZM], which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleTopos.lean` record as unavailable; this
is the same gap that the "Partial coverage" section of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDerivation.lean` records for Tag 0618
itself. For the same reason `Θ` is left as an abstract sheaf of abelian groups on the
spaces-étale site of `X'` and is not identified with `SheafHom(a^*Ω_{Y/B}, 𝒞_{X/X'})`: that
sheaf lives on the small étale site of `X`, and reading it on `X'` is Equation (05ZL) for
sheaves of abelian groups together with the functoriality of the conormal module under étale
restriction, which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` record as not
proved.

**No sheaf condition on `Θ`, and none on the lifts.** Neither the action nor its simple
transitivity uses that `Θ` is a sheaf, and the sheaf property of the lifts is used nowhere
either: it is `AlgebraicGeometry.Space.isSheaf_liftSubfunctor`, Tag 061A, and what it
contributes to Tag 061C is that the object being acted on is a sheaf. Omitting both
hypotheses strengthens the statements.

**Reuse.** The reconstruction of an action from a difference bijection, and the derivation of
simple transitivity and of equivariance from it, are `Deformation.addActionOfPairEquiv`,
`Deformation.addActionOfPairEquiv_pointwiseBijective`,
`Deformation.pairEquiv_inverse_difference` and
`Deformation.map_vadd_of_natural_difference`, already in the library for
[Stacks Project, Tag 06JI], the same statement for lifts of objects of a deformation category.
That tag's assembly in `StacksFrontier/Deformation/LiftsOfObjects/Action/FreeTransitive.lean` is
the shape followed here.

## References

* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

section Setup

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
  (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)

/-- The lifts of `a` over an algebraic space `U'` étale over `X'`: the morphisms
`a' : U' ⟶ Y'` over `T` whose restriction to `U = X ×_{X'} U'` is the restriction of `a`.
These are the sections over `U'` of the sheaf (061B) of [Stacks Project, Tag 061A]. -/
noncomputable abbrev liftSections (U' : (SpacesEtale C S hS X')ᵒᵖ) : Type (u + 1) :=
  (liftSubfunctor C S hS hG hH pX' pY' a).toFunctor.obj U'

/-- The restriction of a lift along a morphism of the spaces-étale site of `X'`, that is the
restriction map of the sheaf (061B). -/
noncomputable abbrev liftSectionsRestrict {U' V' : (SpacesEtale C S hS X')ᵒᵖ} (k : U' ⟶ V')
    (x : liftSections C S hS hG hH pX' pY' a U') :
    liftSections C S hS hG hH pX' pY' a V' :=
  (liftSubfunctor C S hS hG hH pX' pY' a).toFunctor.map k x

variable (Θ : (SpacesEtale C S hS X')ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The difference of two lifts, as a section of a sheaf of abelian groups `Θ` on the
spaces-étale site of `X'`, in the form which reconstructs an action: for each object `U'` a
bijection replacing the second member of a pair of lifts by the difference of the two, fixing
the first member, vanishing on the diagonal, satisfying the cocycle identity and commuting
with restriction.

In the situation of [Stacks Project, Tag 061C] the sections of `Θ` over `U'` are the
`𝒪_X`-linear maps `θ : a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` over `U'`, and the difference of two lifts is
the `θ` attached by Equation (0619) to the `𝒪_B`-derivation by which their comorphisms differ.
That the difference is defined is [Stacks Project, Tag 0618] together with Equation (0619),
that the bijection is surjective is [Stacks Project, Tag 04D0], and the diagonal and cocycle
identities are the additivity of a difference. -/
structure LiftDerivationAction where
  /-- The bijection replacing the second member of a pair of lifts by the difference of the
  two. -/
  equiv : ∀ U' : (SpacesEtale C S hS X')ᵒᵖ,
    (liftSections C S hS hG hH pX' pY' a U' × liftSections C S hS hG hH pX' pY' a U') ≃
      (liftSections C S hS hG hH pX' pY' a U' × Θ.obj U')
  /-- The bijection fixes the first member of the pair. -/
  fst_equiv : ∀ (U' : (SpacesEtale C S hS X')ᵒᵖ)
    (x y : liftSections C S hS hG hH pX' pY' a U'), (equiv U' (x, y)).1 = x
  /-- A lift does not differ from itself. -/
  equiv_self : ∀ (U' : (SpacesEtale C S hS X')ᵒᵖ)
    (x : liftSections C S hS hG hH pX' pY' a U'), (equiv U' (x, x)).2 = 0
  /-- The differences of three lifts add up: the cocycle identity. -/
  equiv_add_equiv : ∀ (U' : (SpacesEtale C S hS X')ᵒᵖ)
    (x y z : liftSections C S hS hG hH pX' pY' a U'),
    (equiv U' (x, y)).2 + (equiv U' (y, z)).2 = (equiv U' (x, z)).2
  /-- The difference commutes with the restriction maps of the site. -/
  map_equiv : ∀ {U' V' : (SpacesEtale C S hS X')ᵒᵖ} (k : U' ⟶ V')
    (x y : liftSections C S hS hG hH pX' pY' a U'),
    (Θ.map k).hom (equiv U' (x, y)).2 =
      (equiv V' (liftSectionsRestrict C S hS hG hH pX' pY' a k x,
        liftSectionsRestrict C S hS hG hH pX' pY' a k y)).2

end Setup

namespace LiftDerivationAction

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
  {hG : IsThickening C S hS X' G} {hH : IsThickening C S hS Y' H}
  {pX' : X' ⟶ T} {pY' : Y' ⟶ T}
  {a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH}
  {Θ : (SpacesEtale C S hS X')ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
  (h : LiftDerivationAction C S hS hG hH pX' pY' a Θ)

/-- The derivation by which two lifts differ, as a section of `Θ`: the `θ` attached by
Equation (0619) to the `𝒪_B`-derivation of [Stacks Project, Tag 0618]. -/
abbrev diff (U' : (SpacesEtale C S hS X')ᵒᵖ)
    (x y : liftSections C S hS hG hH pX' pY' a U') : Θ.obj U' :=
  (h.equiv U' (x, y)).2

/-- **The action of local derivations on lifts.** The sections of `Θ` over `U'` act additively
on the lifts of `a` over `U'`: the translate `θ +ᵥ a'` is the source's `θ · a'`, the unique
lift whose derivation from `a'` is `θ`.

This is the action of [Stacks Project, Tag 061C] and the notation of
[Stacks Project, Tag 0CK6]. -/
@[instance_reducible]
noncomputable def addAction (U' : (SpacesEtale C S hS X')ᵒᵖ) :
    AddAction (Θ.obj U') (liftSections C S hS hG hH pX' pY' a U') :=
  Deformation.addActionOfPairEquiv (h.equiv U') (h.fst_equiv U') (h.equiv_self U')
    (h.equiv_add_equiv U')

/-- **The characterising equation of [Stacks Project, Tag 0CK6].** The derivation by which
`a'` and `θ · a'` differ is `θ`.

Through Equation (0619), which attaches to `θ` the `𝒪_B`-derivation `D = d_{Y/B} ∘ θ`, this
says what the source's notation means: the comorphisms `(a')^♯` and `(θ · a')^♯` differ by the
derivation `D` related to `θ` by that equation. -/
theorem diff_vadd (U' : (SpacesEtale C S hS X')ᵒᵖ)
    (x : liftSections C S hS hG hH pX' pY' a U') (θ : Θ.obj U') :
    letI := h.addAction U'
    h.diff U' x (θ +ᵥ x) = θ :=
  Deformation.pairEquiv_inverse_difference (h.equiv U') (h.fst_equiv U') x θ

/-- **Simple transitivity, [Stacks Project, Tag 061C].** Over an object of the spaces-étale
site of `X'` carrying a lift `a'`, translation `θ ↦ θ · a'` is a bijection from the sections
of `Θ` onto the lifts; equivalently the action is free and transitive there. -/
theorem vadd_bijective (U' : (SpacesEtale C S hS X')ᵒᵖ)
    (x : liftSections C S hS hG hH pX' pY' a U') :
    letI := h.addAction U'
    Function.Bijective (fun θ : Θ.obj U' => θ +ᵥ x) :=
  Deformation.addActionOfPairEquiv_pointwiseBijective (h.equiv U') (h.fst_equiv U') x

end LiftDerivationAction

end AlgebraicGeometry.Space

end
