module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# Regular functions on an affine object of the spaces-étale site of a thickening

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, so `X` is the ambient space
and `G` the closed subspace, which have the same points. Let `U` be an object of the
spaces-étale site of `X` and let `G ×_X U` be its base change along the inclusion, an object of
the spaces-étale site of `G`. This file proves a form of **Stacks 05ZQ** conditional on the
hypotheses of the library's Stacks 07VS: if `G ×_X U` is affine then the
restriction map
`Γ(U, 𝒪_U) → Γ(G ×_X U, 𝒪_{G ×_X U})`
along the cartesian projection `G ×_X U ⟶ U` is surjective.

When the thickening is in addition of **first order**, base change along the inclusion is
essentially surjective on spaces-étale sites (Stacks 05ZH), and the statement is upgraded to
the source's own quantifier: an *arbitrary* object `V` of the spaces-étale site of `G` with
affine underlying algebraic space is isomorphic to such a base change `G ×_X U`, and
restriction of regular functions along the resulting closed immersion `V ≅ G ×_X U ⟶ U` is
surjective.

The unconditional statement, registered as Stacks 05ZQ, is
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isThickening` in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineSectionsSpacesEtale`: a thickening of
arbitrary order, an arbitrary affine object of the spaces-étale site of `G`, and nothing granted.
It uses the unconditional closed-immersion case of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`, in place of the
granted Stacks 07VS used here, and essential surjectivity of base change at a thickening of
arbitrary order, `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`. The
conditional statements below are kept as they are, without a registration.

The route is the one of the source. The cartesian projection is a base change of the inclusion,
hence a closed immersion, and it is surjective on points because the inclusion of a thickening
is. So Stacks 07VS applies and `U` is affine as well; and a closed immersion of algebraic spaces
with affine target is surjective on global regular functions, which is the general statement
proved first below.

## Main results

* `AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isClosedImmersion`: a closed
  immersion of algebraic spaces whose target is affine is surjective on global regular
  functions.
* `AlgebraicGeometry.Space.isAffineSpace_of_isThickening_of_isAffineSpace_baseChange`: in a
  thickening `G ⊂ X`, an object of the spaces-étale site of `X` whose base change to `G` is
  affine is itself affine.
* `AlgebraicGeometry.Space.surjective_globalFunctionsMap_projection_of_isThickening`:
  surjectivity of the restriction map, granted the hypotheses of the library's Stacks 07VS.
* `AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isFirstOrderThickening`:
  the same at a first-order thickening, with the source's own quantifier over an
  arbitrary affine object of the spaces-étale site of the closed subspace.

## Implementation notes

*The shape of the statement, and why the structure sheaf of the ambient space is not
transported.* The source states Stacks 05ZQ as surjectivity of
`Γ(U, 𝒪_{X'}) → Γ(U, 𝒪_X)` for `U` an affine object of `X_{spaces,étale}`, where `𝒪_{X'}` is
read as a sheaf on `X_{spaces,étale}` through the equivalence of *locally ringed* topoi of
Stacks 05ZM. In this library only the equivalence of topoi of Stacks 05ZM is available
(`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening`), and its docstring records
that the identification of the two structure sheaves, which is what upgrades it to an
equivalence of locally ringed topoi, is not part of that statement. So the transported sheaf
`𝒪_{X'}` on `G_{spaces,étale}` does not exist here and cannot be written down.

The statement is therefore made at the level of the sites, which is what the source's own proof
uses: it is parametrised by the object `U` of the spaces-étale site of the *ambient* space, and
the object of the spaces-étale site of `G` is its base change `G ×_X U` along the inclusion,
`AlgebraicGeometry.Space.spacesBaseChange`. The transported section ring `Γ(U, 𝒪_{X'})` *is*
`Γ(U, 𝒪_U)` by construction, so no content is lost, and the restriction map is pullback of
regular functions along the cartesian projection `G ×_X U ⟶ U`, which is the closed immersion
of the source's proof. The statement does not assert any part of Stacks 05ZM.

What the parametrisation by `U` costs, and what buys it back, is *essential surjectivity* of the
base-change functor
`AlgebraicGeometry.Space.spacesBaseChange B S hS (AlgebraicGeometry.Space.IsThickening.inclusion
B S hS hG) |>.functor`, half of the equivalence of spaces-étale sites of Stacks 05ZH: every
object of `G_{spaces,étale}` being isomorphic to some base change `G ×_X U` turns the
hypothesis "the base change of `U` is affine" into "`V` is affine" for an *arbitrary* object
`V` of `G_{spaces,étale}`, which is the source's own quantifier.

*The first-order case.* The first-order statement here uses essential surjectivity for the
inclusion of a **first-order** thickening,
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening`; full faithfulness
is `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening` and the
equivalence `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening`.
Essential surjectivity at a thickening of arbitrary order is also in the library,
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`, and the source's quantifier
at an arbitrary thickening is
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isThickening`.

The ambient object is named with the essential-surjectivity API,
`CategoryTheory.Functor.objPreimage` and `CategoryTheory.Functor.objObjPreimageIso`, rather than
by choosing out of the existential, and the instance they need is discharged inside the
statement itself by the theorem above, so nothing about Stacks 05ZH is granted. The map whose
surjectivity is asserted is pullback of regular functions along the composite of that
isomorphism with the cartesian projection, a morphism `V ⟶ U` of algebraic spaces, so it is a
genuine map `Γ(U, 𝒪_U) → Γ(V, 𝒪_V)`.

*Affineness of the ambient object.* This is Stacks 07VS, and it is used rather than granted,
through its conditional form `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite`,
whose three hypotheses — the conclusions of Stacks 07VR and Stacks 07SQ, and its own
finite-presentation special case — are threaded through unchanged, so nothing is granted here
beyond what that declaration grants. Stacks 07VS itself is proved with no hypothesis as
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`,
so these hypotheses could be dropped by applying that theorem instead. The two facts the
cartesian projection has to supply are proved: it is a closed immersion because closed
immersions of algebraic spaces are stable under base change in the sense of
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, hence finite by Stacks
081Y; and it is surjective on points by
`AlgebraicGeometry.Space.bijective_pointsMap_spacesBaseChange_projection_of_isThickening`.

*The general surjectivity statement.* Global regular functions on an algebraic space are its
morphisms to the affine line, `AlgebraicGeometry.Space.globalFunctionsHomEquiv`, so lifting a
function along `p : Z ⟶ W` is extending a morphism `Z ⟶ 𝔸¹_S` along `p`. Choosing an
isomorphism of `W` with a representable affine `T`, the representability of the closed immersion
`p` produces a cartesian square whose projection to `Z` is an isomorphism — the other leg of the
square being one — and whose projection to `T` is a closed immersion of schemes. Mathlib's
`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine` lifts the corresponding
regular function along it, and `AlgebraicGeometry.Space.affineLineChartPoints` with its
naturality turns the lifted function back into the required morphism to the affine line. Only
affineness of the target is needed, not of the source.

**The three granted hypotheses, and the unconditional route that was not taken.** `h07VR`,
`h07SQ` and `hFinitePresentation` are not new assumptions: they are passed unchanged into
the conditional form of Stacks 07VS,
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite`, so the results here are
exactly as conditional as that theorem and nothing is granted beyond it. Stacks 07VS is proved
with nothing granted as
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`,
which these results do not yet use.

The scheme-level route, with nothing granted, does not apply directly. The
implication *is* proved unconditionally for schemes, as
`Stacks.Thickenings.isAffine_of_isThickening` and its quantified form
`Stacks.Thickenings.forall_isAffine_of_isThickening` (Stacks 06AD), resting on
`Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective` (Stacks 01ZT), with a
first-order variant `Stacks.Thickenings.isAffine_of_isFirstOrderThickening`. But those
are statements about `AlgebraicGeometry.Scheme`, and the objects of the spaces-étale site are
not schemes: `AlgebraicGeometry.Space.SpacesEtale` is the full subcategory of `Over X` on the
objects whose structure morphism is étale, for `X` an *algebraic space*, so an object of the
site is an algebraic space étale over `X`. That is the content of Stacks 03G0, in contrast with
the small étale site, whose objects are schemes. The cartesian projection `G ×_X U ⟶ U` is
therefore a thickening of algebraic spaces rather than of schemes, and transferring affineness
along it is exactly Stacks 07VS, whose algebraic-space form with nothing granted is
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`;
the granted-free statements nearby —
`AlgebraicGeometry.Space.IsFinite.isAffineSpace_source` and
`AlgebraicGeometry.Space.IsAffineHom.isAffineSpace_source` — run the other way, from an affine
target to an affine source. The algebraic-space-level transfer along a surjective closed
immersion is also proved with nothing granted, as
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective` (the thickening
case of Stacks 07VT) in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace`, which this file
does not import; it is what the unconditional Stacks 05ZQ uses.

Conditional forms of Stacks 07VT and 07VS, with the granted hypotheses described above, are in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineOfUniversallyClosedSurjection.lean`. Both tags are
also proved with nothing granted, as
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`
and `AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed immersions with affine target -/

/-- **A closed immersion of algebraic spaces with affine target is surjective on global regular
functions.** For a closed immersion `p : Z ⟶ W` of algebraic spaces over `S` with `W` affine,
every global regular function on `Z` is the pullback of one on `W`.

Affineness of the source is not assumed: it follows from that of the target. Global regular
functions are morphisms to the affine line, so the claim is that a morphism `Z ⟶ 𝔸¹_S` extends
along `p`. An isomorphism of `W` with a representable affine `T` turns `p`, by representability,
into a closed immersion of schemes over `T` whose source is isomorphic to `Z`, and Mathlib's
`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine` extends the corresponding
regular function over `T`. -/
theorem surjective_globalFunctionsMap_of_isClosedImmersion
    {Z W : AlgebraicSpaces B S hS} (p : Z ⟶ W)
    (hp : IsClosedImmersion B S hS p.hom) (hW : IsAffineSpace B S hS W.obj) :
    Function.Surjective (globalFunctionsMap B S hS p) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hW
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  have hsq : IsPullback (hp.rep.fst e.inv) (yoneda.map (hp.rep.snd e.inv)) p.hom e.inv :=
    hp.rep.isPullback e.inv
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hp.rep.snd e.inv)) := hp.property_snd e.inv
  have : IsIso (hp.rep.fst e.inv) := hsq.isIso_fst_of_isIso
  have : Epi (hp.rep.fst e.inv) := IsIso.epi_of_iso _
  have hsurj : Function.Surjective
      ((BigFppfOver.toScheme B S hS).map (hp.rep.snd e.inv)).appTop :=
    (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B S hS).map (hp.rep.snd e.inv))).2
  intro s
  set u := hp.rep.fst e.inv ≫ (globalFunctionsHomEquiv B S hS Z s).hom with hu
  obtain ⟨t, ht⟩ := hsurj ((affineLineChartPoints B S hS (hp.rep.pullback e.inv)).symm
    (yoneda.preimage u))
  have hkn : hp.rep.snd e.inv ≫ affineLineChartPoints B S hS T t = yoneda.preimage u := by
    rw [← affineLineChartPoints_natural B S hS (hp.rep.snd e.inv) t]
    exact (congrArg _ ht).trans
      ((affineLineChartPoints B S hS (hp.rep.pullback e.inv)).apply_symm_apply _)
  let q : W ⟶ affineLineSpace B S hS :=
    ObjectProperty.homMk (e.hom ≫ yoneda.map (affineLineChartPoints B S hS T t))
  have key : hp.rep.fst e.inv ≫ (p ≫ q).hom = u :=
    calc hp.rep.fst e.inv ≫ (p ≫ q).hom
        = (hp.rep.fst e.inv ≫ p.hom) ≫
            e.hom ≫ yoneda.map (affineLineChartPoints B S hS T t) := by
          simp [q, Category.assoc]
      _ = (yoneda.map (hp.rep.snd e.inv) ≫ e.inv) ≫
            e.hom ≫ yoneda.map (affineLineChartPoints B S hS T t) := by rw [hsq.w]
      _ = yoneda.map (hp.rep.snd e.inv) ≫
            yoneda.map (affineLineChartPoints B S hS T t) := by
          rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp]
      _ = yoneda.map (hp.rep.snd e.inv ≫ affineLineChartPoints B S hS T t) :=
          (yoneda.map_comp _ _).symm
      _ = yoneda.map (yoneda.preimage u) := by rw [hkn]
      _ = u := yoneda.map_preimage _
  refine ⟨(globalFunctionsHomEquiv B S hS W).symm q, ?_⟩
  refine (globalFunctionsHomEquiv B S hS Z).injective ?_
  rw [globalFunctionsHomEquiv_natural, Equiv.apply_symm_apply]
  exact ObjectProperty.hom_ext _ ((cancel_epi (hp.rep.fst e.inv)).1 key)

/-! ### The cartesian projection of a thickening -/

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- **The cartesian projection from the base change along the inclusion of a thickening is a
closed immersion.** The inclusion of a thickening `G ⊂ X` is a closed immersion by the
definition of a closed subspace, and closed immersions of algebraic spaces are stable under
base change. -/
theorem isClosedImmersion_spacesBaseChange_projection_of_isThickening
    (hG : IsThickening B S hS X G) (U : SpacesEtale B S hS X) :
    IsClosedImmersion B S hS
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U).hom :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).isPullback U).flip)
    hG.1.2

/-- **An object of the spaces-étale site of the ambient space of a thickening whose base change
is affine is itself affine.** For a thickening `G ⊂ X` and an object `U` of the spaces-étale
site of `X`, the cartesian projection `G ×_X U ⟶ U` is a closed immersion, hence finite by
Stacks 081Y, and it is surjective on points because the inclusion of a thickening is. So
Stacks 07VS applies.

The three hypotheses are exactly those of
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite`, passed on unchanged: the
conclusion of Stacks 07VR that a finite morphism over a quasi-compact quasi-separated algebraic
space is a directed limit of finite morphisms of finite presentation, the conclusion of
Stacks 07SQ that a directed system with affine transition morphisms and affine limit has an
affine stage, and the special case of Stacks 07VS in which the morphism is in addition of finite
presentation. -/
theorem isAffineSpace_of_isThickening_of_isAffineSpace_baseChange
    (hG : IsThickening B S hS X G) (U : SpacesEtale B S hS X)
    (hU : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U)).obj)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    IsAffineSpace B S hS ((SpacesEtale.toSpaces B S hS X).obj U).obj :=
  isAffineSpace_of_isSurjective_of_isFinite B S hS
    ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U).hom
    ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U)).property
    ((SpacesEtale.toSpaces B S hS X).obj U).property
    (bijective_pointsMap_spacesBaseChange_projection_of_isThickening B S hS hG U).2
    (isFinite_of_isClosedImmersion B S hS _
      (isClosedImmersion_spacesBaseChange_projection_of_isThickening B S hS hG U))
    hU h07VR h07SQ hFinitePresentation

/-- **Stacks 05ZQ, granted the hypotheses of Stacks 07VS.** Let `G ⊂ X` be a thickening of
algebraic spaces over `S` and let `U` be an object of the spaces-étale site of `X` whose base
change `G ×_X U` along the inclusion is affine. Then restriction of global regular functions
along the cartesian projection `G ×_X U ⟶ U`, that is `Γ(U, 𝒪_U) → Γ(G ×_X U, 𝒪_{G ×_X U})`, is surjective.

The ambient object `U` is affine by
`AlgebraicGeometry.Space.isAffineSpace_of_isThickening_of_isAffineSpace_baseChange`, which is
Stacks 07VS, and the projection is a closed immersion, so
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isClosedImmersion` applies.

The unconditional form, with the source's quantifier, is
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isThickening`, which carries the
Stacks 05ZQ registration. -/
theorem surjective_globalFunctionsMap_projection_of_isThickening
    (hG : IsThickening B S hS X G) (U : SpacesEtale B S hS X)
    (hU : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U)).obj)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    Function.Surjective (globalFunctionsMap B S hS
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U)) :=
  surjective_globalFunctionsMap_of_isClosedImmersion B S hS _
    (isClosedImmersion_spacesBaseChange_projection_of_isThickening B S hS hG U)
    (isAffineSpace_of_isThickening_of_isAffineSpace_baseChange B S hS hG U hU
      h07VR h07SQ hFinitePresentation)

/-! ### The first-order case, with the source's quantifier -/

/-- **Stacks 05ZQ at a first-order thickening, granted the hypotheses of Stacks 07VS.** Let
`G ⊂ X` be a *first-order* thickening of algebraic spaces over `S` and let `V` be an
*arbitrary* object of the spaces-étale site of `G` whose underlying algebraic space is affine.
Then restriction of global regular functions `Γ(U, 𝒪_U) → Γ(V, 𝒪_V)` is surjective, where `U`
is the object of the spaces-étale site of `X` whose base change along the inclusion is
isomorphic to `V`, and the map is pullback along the composite `V ≅ G ×_X U ⟶ U` of that
isomorphism with the cartesian projection.

Base change along the inclusion of a first-order thickening is essentially surjective by
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening`, which is
Stacks 05ZH in the only generality the library has it; the instance is discharged in the
statement, so no part of Stacks 05ZH is granted. The object `U` and the isomorphism are the
`CategoryTheory.Functor.objPreimage` and `CategoryTheory.Functor.objObjPreimageIso` of that
essential surjectivity. Transporting affineness of `V` across the isomorphism makes
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_projection_of_isThickening` apply at
`U`, and pullback along an isomorphism is bijective on global regular functions, so the
composite is surjective.

The three hypotheses are threaded unchanged into
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_projection_of_isThickening`. The
unconditional statement at a thickening of arbitrary order is
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isThickening`, which carries the
Stacks 05ZQ registration. -/
theorem surjective_globalFunctionsMap_of_isFirstOrderThickening
    (hG : IsFirstOrderThickening B S hS X G)
    (V : SpacesEtale B S hS (IsThickening.space B S hS (hG.isThickening B S hS)))
    (hV : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS
        (IsThickening.space B S hS (hG.isThickening B S hS))).obj V).obj)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    letI : (spacesBaseChange B S hS
        (IsThickening.inclusion B S hS (hG.isThickening B S hS))).functor.EssSurj :=
      @essSurj_spacesBaseChange_of_isFirstOrderThickening B S hS _ X
        (IsThickening.inclusion B S hS (hG.isThickening B S hS)) (inferInstanceAs (Mono G.ι))
        (Eq.mpr (congrArg (IsFirstOrderThickening B S hS X) (Subfunctor.range_ι G)) hG)
    Function.Surjective (globalFunctionsMap B S hS
      ((SpacesEtale.toSpaces B S hS
            (IsThickening.space B S hS (hG.isThickening B S hS))).map
          ((spacesBaseChange B S hS (IsThickening.inclusion B S hS
            (hG.isThickening B S hS))).functor.objObjPreimageIso V).inv ≫
        (spacesBaseChange B S hS (IsThickening.inclusion B S hS
            (hG.isThickening B S hS))).projection.app
          ((spacesBaseChange B S hS (IsThickening.inclusion B S hS
            (hG.isThickening B S hS))).functor.objPreimage V))) := by
  have hGt : IsThickening B S hS X G := hG.isThickening B S hS
  have key : ∀ (U : SpacesEtale B S hS X)
      (e : (spacesBaseChange B S hS (IsThickening.inclusion B S hS hGt)).functor.obj U ≅ V),
      Function.Surjective (globalFunctionsMap B S hS
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hGt)).map e.inv ≫
          (spacesBaseChange B S hS (IsThickening.inclusion B S hS hGt)).projection.app U)) := by
    intro U e
    have hproj := surjective_globalFunctionsMap_projection_of_isThickening B S hS hGt U
      (hV.of_iso ((ObjectProperty.ι _).mapIso
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hGt)).mapIso e.symm)))
      h07VR h07SQ hFinitePresentation
    have hid : (globalFunctionsMap B S hS
          ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hGt)).map e.inv)).comp
        (globalFunctionsMap B S hS
          ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hGt)).map e.hom)) =
        RingHom.id _ := by
      rw [← globalFunctionsMap_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, globalFunctionsMap_id]
    have hiso : Function.Surjective (globalFunctionsMap B S hS
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hGt)).map e.inv)) :=
      fun s => ⟨globalFunctionsMap B S hS
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hGt)).map e.hom) s, by
          rw [← RingHom.comp_apply, hid, RingHom.id_apply]⟩
    rw [globalFunctionsMap_comp, RingHom.coe_comp]
    exact hiso.comp hproj
  exact key _ _

end AlgebraicGeometry.Space

end
