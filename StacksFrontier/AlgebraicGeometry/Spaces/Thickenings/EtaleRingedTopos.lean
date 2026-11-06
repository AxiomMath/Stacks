module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.RingedTopos

/-!
# The structure sheaf of a thickening of algebraic spaces on the smaller site

Let `G ⊂ X` be a thickening of algebraic spaces over `S`.  Base change of étale scheme charts
along the inclusion exhibits the small étale site of `X` as a dense subsite of the small étale
site of `G`, so restriction along it is an equivalence of sheaf categories for *any* coefficient
category with the limits needed to form the restriction — in particular for sheaves of rings,
not only for sheaves of sets.

Carrying the structure sheaf `𝒪_X` of the ambient space through that equivalence produces a
sheaf of rings on the site of the thickening whose sections over the base change `G ×_X V` of an
étale chart `V` are the global regular functions of `V`.  So the pair (sheaves on the site of
`G`, that sheaf of rings) is the right hand side of the fundamental equivalence of a thickening.

The second half of the file assembles that right hand side as a **ringed topos** and proves the
comparison to be an equivalence of *locally* ringed topoi, which is what the equation of
[Stacks Project, Tag 05ZM] asserts.  There the structure sheaf of the ambient space is carried
to the smaller site not by restriction along chart base change but as the inverse image
`i^{-1}𝒪_X` along the inclusion `i : G ⟶ X`, which is the presentation the morphisms of ringed
topoi of Stacks 03G8 are written in: the right hand pair is the inverse-image ringed topos of
[Stacks Project, Tag 04KR], the comparison is its canonical morphism, and the structure map of
that morphism is the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`.  Both of the equation's claims are then
available: the unit is an isomorphism, which is the identification of the two structure sheaves,
and the direct image is an equivalence of topoi, so the comparison is invertible — in both
directions as a morphism of locally ringed topoi.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingSheafEquiv_of_isThickening` and
  `AlgebraicGeometry.Space.spacesEtaleRingSheafEquiv_of_isThickening`: the equivalence of the
  categories of sheaves of commutative rings on the two sites, on scheme charts and on the
  spaces-étale sites.
* `AlgebraicGeometry.Space.thickeningStructureSheaf`: the structure sheaf of the ambient space
  read as a sheaf of rings on the spaces-étale site of the thickening.
* `AlgebraicGeometry.Space.thickeningInverseImageRingedTopos`: the right hand side
  `(Sh(G_étale), 𝒪_X)` of the fundamental equivalence, as a ringed topos, with `𝒪_X` read on the
  site of `G` as its inverse image along the inclusion.
* `AlgebraicGeometry.Space.thickeningFundamentalHom` and
  `AlgebraicGeometry.Space.thickeningFundamentalHomInverse`: the canonical morphism of ringed
  topoi from that pair to `(Sh(X_étale), 𝒪_X)`, and its inverse.

## Main results

* `AlgebraicGeometry.Space.thickeningStructureSheaf_restrictIso`: restricting
  `thickeningStructureSheaf` back along base change returns `𝒪_X`.
* `AlgebraicGeometry.Space.thickeningStructureSheaf_obj_iso`: its sections over the base change
  of an object of the spaces-étale site of `X` are the sections of `𝒪_X` over that object.
* `AlgebraicGeometry.Space.isEquivalence_smallEtalePushforward_of_isThickening`: the direct image
  of sheaves of sets along the inclusion of a thickening is an equivalence of categories.
* `AlgebraicGeometry.Space.isIso_thickeningFundamentalHom_fSharp`: **the structure-sheaf half of
  Stacks 05ZM** — the structure map of the canonical morphism, the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`, is
  an isomorphism of sheaves of commutative rings.
* `AlgebraicGeometry.Space.thickeningFundamentalHom_isLocallyRinged` and
  `AlgebraicGeometry.Space.thickeningFundamentalHomInverse_isLocallyRinged`: the comparison and
  its inverse are morphisms of *locally* ringed topoi.
* `AlgebraicGeometry.Space.isIso_smallEtalePushforwardUnit_of_isThickening` and
  `AlgebraicGeometry.Space.smallEtalePushforwardUnitIso`: the unit `η : 𝟭 ⟶ i^{-1} ⋙ i_*` of a
  thickening is invertible at every sheaf of sets, and so is a natural isomorphism.
* `AlgebraicGeometry.Space.agreeingPushforwardIso`: **two morphisms agreeing on a thickening have
  isomorphic small étale direct images**, for an arbitrary thickening — the inclusion cancelled
  from the comparison `AlgebraicGeometry.Space.agreeingPushforwardWhiskerIso`.  This is the
  geometric field of a 2-isomorphism of their morphisms of small étale ringed topoi, with
  `AlgebraicGeometry.Space.agreeingPushforwardIso_hom_app` computing its components.

## Implementation notes

The coefficient category enters only through the hypothesis that the comma categories indexing
the right Kan extension have limits in it.  Those comma categories are essentially small at `u`,
the universe of the étale charts, so the hypothesis holds for the categories of rings at every
universe level, and both the ring-valued equivalence here and the set-valued one of
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` are instances of one statement.

**Why the ringed-topos half is stated in the inverse-image presentation.**  The two ways of
reading `𝒪_X` on the site of `G` — restriction along chart base change, and the inverse image
along `i` — agree, because by Stacks 03G8 the direct image along `i` *is* that restriction
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`).  Only the inverse-image form
is used below, for two reasons.  It is the form in which the structure sheaf of the ambient space
already occurs in this development, so no second transport of `𝒪_X` to the smaller site is
coined: the invertibility of the unit is
`AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`, whose module documentation already
names it as this half of Stacks 05ZM, and the conormal module of a first order thickening is
defined as a submodule of `i^{-1}𝒪_X` rather than of a restriction
(`AlgebraicGeometry.Space.conormalInverseImageι`).  And it is the form that
`AlgebraicGeometry.RingedToposHom` takes, so the comparison composes with the morphisms of small
étale ringed topoi of Stacks 03G8 without a change of presentation.

**What the invertibility of the unit is proved from.**  Not from the ring-level statement, which
is stated at `RingCat` and would have to be transported to `CommRingCat` anyway, but from the
same two inputs: the direct image of sheaves of sets along the inclusion is fully faithful
because the inclusion is a closed immersion (Stacks 04E5, part (1)) and essentially surjective
because `G ⊂ X` is a thickening
(`AlgebraicGeometry.Space.essSurj_smallEtalePushforward_of_isThickening`), so the set-level unit
is invertible at every sheaf; and the forgetful functor of a ringed topos carries the unit of the
adjunction on sheaves of commutative rings to the set-level unit
(`Stacks.Sheaves.ToposPushforward.forgetRing_map_commRingImageAdjunction_unit_app`) and reflects
isomorphisms.

**Local ringedness here is a statement about the morphism, not about the two sites.**  That the
comparison is a morphism of locally ringed topoi needs no hypothesis at all: the inverse-image
form of its structure map is the identity, by
`AlgebraicGeometry.inverseImageRingedToposHom_fSharpInverseImage`, and a morphism of ringed topoi
whose inverse-image structure map is invertible is locally ringed (Stacks 04H9).  That each of
the two *sites* is a locally ringed site is a different assertion; the ambient one is Stacks 04KH
(`AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`), and transporting it along the
comparison is out of reach of `AlgebraicGeometry.RingedTopos.isLocallyRinged_iff_of_equivalence`,
which inherits from Stacks 04H7, part (2) the restriction that the three universes of each ringed
topos agree — the small étale ringed topos of an algebraic space is a
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`.

**The components of `AlgebraicGeometry.Space.agreeingPushforwardIso` are reachable only through
`AlgebraicGeometry.Space.agreeingPushforwardIso_hom`, and this is necessary, not a precaution.**
The equation at the level of natural transformations holds by `rfl` and is checked in under a
second.  The *same* equation read at an object — the three factors applied to a sheaf `M`, which
is `CategoryTheory.NatTrans.comp_app` twice and therefore also `rfl` — is a
`(kernel) deterministic timeout` at 50 s, whether it is written as `rfl`, reached by `rw`, or
reached by a `congrArg` chain: unfolding `agreeingPushforwardIso` past `CategoryTheory.Iso.trans`
drags in `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` twice, and with it the transport
of the cartesian composition through the two comparison equivalences.  What does work, in 0.3 s,
is to prove the equation of natural transformations and then descend to the object with
`congrArg (fun t => CategoryTheory.NatTrans.app t M)` followed by
`CategoryTheory.NatTrans.comp_app` as *propositional* steps — the motive is then the small term
`· .app M` rather than the whole composite.  That is how
`AlgebraicGeometry.Space.agreeingPushforwardIso_hom_app` is proved, and any further computation
with the components should be reached the same way.

**What the 2-isomorphism still lacks, and why it is not a formality.**  The `commutes` field of
`AlgebraicGeometry.RingedToposHom.TwoIso` asks that the component of
`AlgebraicGeometry.Space.agreeingPushforwardIso` at the structure sheaf carry
`AlgebraicGeometry.RingedToposHom.forgetFSharp` of `c` to that of `c'`.  By
`AlgebraicGeometry.Space.agreeingPushforwardIso_hom_app` that component is `c_*η` followed by the
whiskered comparison, which are exactly the first two factors of
`AlgebraicGeometry.Space.structureSharpThroughThickening` — so the hypothesis that two morphisms
have equal comorphisms read through the thickening is the right input, and no further geometry is
needed.  What is missing is a reconciliation of three presentations of the structure map, which
this corner carries in parallel and nowhere identifies: `forgetFSharp` is at sheaves of sets
obtained from `CommRingCat` by `AlgebraicGeometry.RingedTopos.forgetRing`;
`AlgebraicGeometry.Space.structureSharpThroughThickening` is at `RingCat`; and
`AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp` connects `CommRingCat` to `RingCat` but
not either to `Type u`.  Closing it means identifying
`CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)` with
`CategoryTheory.sheafCompose _ (CategoryTheory.forget₂ CommRingCat RingCat)` followed by
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`, and then reading the two
remaining factors of `AlgebraicGeometry.Space.structureSharpThroughThickening` at the set level,
for which `AlgebraicGeometry.Space.structureSharp_comp` is the worked precedent.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1).
* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR), the inverse-image ringed
  topos and its canonical morphism.
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9), an isomorphism of ringed
  topoi is locally ringed.
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH), the small étale site of
  an algebraic space is a locally ringed site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w' w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- The comma categories indexing the right Kan extension along base change of étale scheme
charts along the inclusion of a thickening have limits in any category with limits of
`u`-small shapes. -/
theorem hasLimitsOfShape_structuredArrow_thickeningChartBaseChange
    (hG : IsThickening B S hS X G) (A : Type w) [Category.{w'} A] [HasLimitsOfSize.{u, u} A]
    (W : (SmallEtale B S hS (IsThickening.space B S hS hG).1)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (thickeningChartBaseChange B S hS hG).op) A :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (thickeningChartBaseChange B S hS hG).op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Restriction along base change of étale scheme charts along the inclusion of a thickening is
an equivalence of categories of sheaves with values in any category with limits of `u`-small
shapes. -/
theorem thickeningChartBaseChange_sheafEquivalence (hG : IsThickening B S hS X G)
    (A : Type w) [Category.{w'} A] [HasLimitsOfSize.{u, u} A] :
    letI := thickeningChartBaseChange_isDenseSubsite B S hS hG
    ((thickeningChartBaseChange B S hS hG).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)).IsEquivalence := by
  let := thickeningChartBaseChange_isDenseSubsite B S hS hG
  let := hasLimitsOfShape_structuredArrow_thickeningChartBaseChange B S hS hG A
  infer_instance

/-- The sheaves of commutative rings on the small étale site of an algebraic space `X` and on
the small étale site of a thickening `G ⊂ X` of it are equivalent, by restriction along base
change of étale scheme charts. -/
def smallEtaleRingSheafEquiv_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u + 1} ≌
      Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) CommRingCat.{u + 1} :=
  letI := thickeningChartBaseChange_isDenseSubsite B S hS hG
  letI := thickeningChartBaseChange_sheafEquivalence B S hS hG CommRingCat.{u + 1}
  Functor.IsDenseSubsite.sheafEquiv (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (thickeningChartBaseChange B S hS hG) CommRingCat.{u + 1}

set_option synthInstance.maxHeartbeats 400000 in
/-- **The fundamental equivalence of a thickening, at sheaves of rings.**  For a thickening
`G ⊂ X` of algebraic spaces the sheaves of commutative rings on the spaces-étale site of `X`
and those on the spaces-étale site of `G` are canonically equivalent. -/
@[stacks 05ZM "the equivalence of the two spaces-étale topoi at sheaves of commutative rings, \
which is what carries the structure sheaf of the ambient space to the right hand side of the \
equation; neither pair is claimed to be a locally ringed topos"]
def spacesEtaleRingSheafEquiv_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u + 1} ≌
      Sheaf (SpacesEtale.topology B S hS (IsThickening.space B S hS hG))
        CommRingCat.{u + 1} :=
  ((comparisonFunctor B S hS X).sheafPushforwardContinuous CommRingCat.{u + 1}
        (SmallEtale.topology B S hS X.1)
        (SpacesEtale.topology B S hS X)).asEquivalence.trans
    ((smallEtaleRingSheafEquiv_of_isThickening B S hS hG).trans
      ((comparisonFunctor B S hS (IsThickening.space B S hS hG)).sheafPushforwardContinuous
          CommRingCat.{u + 1}
          (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
          (SpacesEtale.topology B S hS
            (IsThickening.space B S hS hG))).asEquivalence.symm)

/-- **The structure sheaf of the ambient space, on the site of the thickening.**  For a
thickening `G ⊂ X` this is `𝒪_X` carried through the equivalence of the two spaces-étale
topoi, the sheaf of rings of the right hand side of the fundamental equivalence. -/
@[stacks 05ZM "the sheaf of rings O_{X'} of the right hand side of the equation, the structure \
sheaf of the ambient space read on the spaces-étale site of the thickening"]
def thickeningStructureSheaf (hG : IsThickening B S hS X G) :
    Sheaf (SpacesEtale.topology B S hS (IsThickening.space B S hS hG)) CommRingCat.{u + 1} :=
  (spacesEtaleRingSheafEquiv_of_isThickening B S hS hG).functor.obj
    (SpacesEtale.structureSheaf B S hS X)

/-- Restricting the structure sheaf of the ambient space back along the equivalence of the two
spaces-étale topoi returns it. -/
def thickeningStructureSheaf_restrictIso (hG : IsThickening B S hS X G) :
    (spacesEtaleRingSheafEquiv_of_isThickening B S hS hG).inverse.obj
        (thickeningStructureSheaf B S hS hG) ≅
      SpacesEtale.structureSheaf B S hS X :=
  ((spacesEtaleRingSheafEquiv_of_isThickening B S hS hG).unitIso.app
    (SpacesEtale.structureSheaf B S hS X)).symm

/-- The equivalence of the two categories of sheaves of rings on scheme charts is restriction
along base change: the sections of a sheaf on the site of the thickening over the base change
of a chart `V` are the sections of its restriction over `V`. -/
theorem smallEtaleRingSheafEquiv_inverse_obj_obj (hG : IsThickening B S hS X G)
    (M : Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
      CommRingCat.{u + 1}) (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    ((smallEtaleRingSheafEquiv_of_isThickening B S hS hG).inverse.obj M).obj.obj V =
      M.obj.obj (op ((thickeningChartBaseChange B S hS hG).obj V.unop)) := rfl

/-- The sections over the base change of a chart `V` of a sheaf of rings carried from the small
étale site of the ambient space to that of the thickening are its sections over `V`. -/
def smallEtaleRingSheafEquiv_functor_obj_obj_iso (hG : IsThickening B S hS X G)
    (F : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u + 1})
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    ((smallEtaleRingSheafEquiv_of_isThickening B S hS hG).functor.obj F).obj.obj
        (op ((thickeningChartBaseChange B S hS hG).obj V.unop)) ≅ F.obj.obj V :=
  ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj V).mapIso
    ((smallEtaleRingSheafEquiv_of_isThickening B S hS hG).unitIso.app F).symm)

/-! ### The fundamental equivalence as a morphism of locally ringed topoi -/

/-- The direct image of sheaves of sets along the inclusion of a thickening is an equivalence. -/
private theorem isEquivalence_pushforward_subspaceInclusion (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsThickening B S hS X Z.1) :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.IsEquivalence := by
  let : (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS X Z)).pushforward.EssSurj :=
    essSurj_smallEtalePushforward_of_isThickening B S hS Z hZ
  let hff : (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS X Z)).pushforward.FullyFaithful :=
    fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
      (subspaceInclusion B S hS X Z) (isClosedImmersion_inclusion_of_isThickening B S hS hZ)
  let := hff.full
  let := hff.faithful
  exact { }

/-- **The direct image of sheaves of sets along the inclusion of a thickening is an equivalence
of categories.**  It is fully faithful because the inclusion `i : G ⟶ X` is a closed immersion,
which is Stacks 04E5, part (1), and essentially surjective because `G ⊂ X` is a thickening, which
is `AlgebraicGeometry.Space.essSurj_smallEtalePushforward_of_isThickening`.

This is the equivalence of topoi of Stacks 05ZM, read on the direct image rather than on
restriction along chart base change; the two agree by Stacks 03G8, and the registered form of
that half is `AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening`.  What this form
adds is that it is the geometric morphism carried by the morphisms of small étale ringed topoi,
so it is the one under which the structure sheaves below are compared. -/
theorem isEquivalence_smallEtalePushforward_of_isThickening
    (hG : IsThickening B S hS X G) :
    (smallToposMorphismTypeU B S hS
      (IsThickening.inclusion B S hS hG)).pushforward.IsEquivalence :=
  isEquivalence_pushforward_subspaceInclusion B S hS ⟨G, hG.1⟩ hG

/-- **The right hand side `(Sh(G_étale), 𝒪_X)` of the fundamental equivalence of a thickening.**
The small étale site of scheme charts of the closed subspace `G` of a thickening `G ⊂ X`,
equipped with the structure sheaf of the *ambient* space `X` read on it as the inverse image
`i^{-1}𝒪_X` along the inclusion.

This is the inverse-image ringed topos of Stacks 04KR at the morphism of small étale topoi of the
inclusion.  Its structure sheaf is not `𝒪_G`: the two are related by the surjection
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_G`, whose kernel is the conormal module of the thickening when the
thickening is of first order. -/
@[stacks 05ZM "the right hand pair of the equation, in the presentation of scheme charts and \
with the structure sheaf of the ambient space read on the smaller site as its inverse image"]
abbrev thickeningInverseImageRingedTopos (hG : IsThickening B S hS X G) :
    RingedTopos.{u, u + 1, u} :=
  inverseImageRingedTopos (SmallEtale B S hS (IsThickening.space B S hS hG).1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (smallEtaleRingedTopos B S hS X)
    (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG))

/-- **The canonical morphism of the fundamental equivalence of a thickening.**  Its underlying
geometric morphism is the direct image along the inclusion `i : G ⟶ X`, and its structure map is
the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` of the adjunction `i^{-1} ⊣ i_*` on sheaves of commutative rings.

Both of the equation's claims about it are below:
`AlgebraicGeometry.Space.isIso_thickeningFundamentalHom_fSharp` is that the structure map is an
isomorphism, and `AlgebraicGeometry.Space.isEquivalence_smallEtalePushforward_of_isThickening` is
that the geometric morphism is an equivalence — the latter is stated at the geometric morphism
itself, which is this morphism's `toToposHom` by
`AlgebraicGeometry.inverseImageRingedToposHom_toToposHom`, so it supplies that instance after an
ascription at this spelling, as in
`AlgebraicGeometry.Space.thickeningFundamentalHomInverse` below. -/
@[stacks 05ZM "the canonical morphism between the two pairs of the equation, in the \
presentation of scheme charts: its geometric morphism is the direct image along the \
inclusion, and its structure map is the unit of the adjunction at the ambient structure sheaf"]
def thickeningFundamentalHom (hG : IsThickening B S hS X G) :
    RingedToposHom (thickeningInverseImageRingedTopos B S hS hG)
      (smallEtaleRingedTopos B S hS X) :=
  inverseImageRingedToposHom (SmallEtale B S hS (IsThickening.space B S hS hG).1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (smallEtaleRingedTopos B S hS X)
    (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG))

/-- **The structure-sheaf half of Stacks 05ZM.**  The structure map of the canonical morphism —
the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` at the structure sheaf of the ambient space of a thickening — is an
isomorphism of sheaves of commutative rings.  So the two pairs of the equation carry one and the
same structure sheaf, and not merely equivalent topoi.

The direct image of sheaves of sets along the inclusion is fully faithful and essentially
surjective, so the set-level unit is invertible at every sheaf; forgetting the ring operations
carries the unit of the adjunction on sheaves of commutative rings to the set-level unit, and
reflects isomorphisms.  The same statement for sheaves of not necessarily commutative rings is
`AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`. -/
@[stacks 05ZM "the structure-sheaf half: the structure map of the canonical morphism between the \
two pairs is an isomorphism, so both pairs carry the structure sheaf of the ambient space"]
theorem isIso_thickeningFundamentalHom_fSharp (hG : IsThickening B S hS X G) :
    IsIso (thickeningFundamentalHom B S hS hG).fSharp := by
  have := isEquivalence_smallEtalePushforward_of_isThickening B S hS hG
  have hset : IsIso ((smallToposMorphismTypeU B S hS
      (IsThickening.inclusion B S hS hG)).adj.unit.app
      ((smallEtaleRingedTopos B S hS X).forgetRing.obj
        (smallEtaleRingedTopos B S hS X).O)) :=
    NatIso.isIso_app_of_isIso _ _
  have h := forgetRing_map_commRingImageAdjunction_unit_app
    (smallEtaleRingedTopos B S hS X)
    (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG))
  have : IsIso ((smallEtaleRingedTopos B S hS X).forgetRing.map
      (thickeningFundamentalHom B S hS hG).fSharp) := h ▸ hset
  exact isIso_of_reflects_iso _ (smallEtaleRingedTopos B S hS X).forgetRing

/-- The inverse-image form of the structure map of the canonical morphism is invertible. -/
private theorem isIso_thickeningFundamentalHom_fSharpInverseImage
    (hG : IsThickening B S hS X G) :
    IsIso (thickeningFundamentalHom B S hS hG).fSharpInverseImage := by
  rw [thickeningFundamentalHom, inverseImageRingedToposHom_fSharpInverseImage]
  exact IsIso.id _

/-- **The canonical morphism of the fundamental equivalence is a morphism of locally ringed
topoi.**  This is the clause that makes the equation of Stacks 05ZM an equivalence of *locally*
ringed topoi and not only of ringed topoi.

It needs no hypothesis on the thickening: the inverse-image form of the structure map of the
canonical morphism out of an inverse-image ringed topos is the identity, and a morphism of ringed
topoi whose inverse-image structure map is invertible is locally ringed, which is the step
Stacks 04H9 settles with the words "as it is an isomorphism this is clear".  The thickening
hypothesis is what makes the morphism *invertible*, through
`AlgebraicGeometry.Space.isIso_thickeningFundamentalHom_fSharp` and
`AlgebraicGeometry.Space.isEquivalence_smallEtalePushforward_of_isThickening`.

That the two ringed topoi are locally ringed *sites* is a different assertion, and is not
claimed; see the implementation notes. -/
@[stacks 05ZM "that the canonical morphism between the two pairs is a morphism of LOCALLY ringed \
topoi, which is the clause the equation adds to the equivalence of the two topoi; that either \
pair is a locally ringed SITE is not claimed"]
theorem thickeningFundamentalHom_isLocallyRinged (hG : IsThickening B S hS X G) :
    (thickeningFundamentalHom B S hS hG).IsLocallyRinged := by
  have := isIso_thickeningFundamentalHom_fSharpInverseImage B S hS hG
  exact RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage
    (thickeningFundamentalHom B S hS hG)

/-- **The inverse of the canonical morphism of the fundamental equivalence of a thickening.**  The
geometric morphism is `i^{-1}` read as a direct image, and the structure map is the inverse of the
inverse-image form `i^{-1}𝒪_X ⟶ i^{-1}𝒪_X` of the structure map of
`AlgebraicGeometry.Space.thickeningFundamentalHom`.

Its existence is the content of the word *equivalence* in the equation of Stacks 05ZM: the
canonical morphism is invertible because its geometric morphism is an equivalence of topoi and its
structure map is an isomorphism of sheaves of rings. -/
@[stacks 05ZM "that the canonical morphism between the two pairs is invertible as a morphism of \
ringed topoi, which is the word equivalence in the equation"]
def thickeningFundamentalHomInverse (hG : IsThickening B S hS X G) :
    RingedToposHom (smallEtaleRingedTopos B S hS X)
      (thickeningInverseImageRingedTopos B S hS hG) :=
  letI : (thickeningFundamentalHom B S hS hG).toToposHom.pushforward.IsEquivalence :=
    isEquivalence_smallEtalePushforward_of_isThickening B S hS hG
  letI := isIso_thickeningFundamentalHom_fSharp B S hS hG
  RingedToposHom.inverse (X := thickeningInverseImageRingedTopos B S hS hG)
    (Y := smallEtaleRingedTopos B S hS X) (thickeningFundamentalHom B S hS hG)

/-- **The inverse of the canonical morphism is again a morphism of locally ringed topoi.**
Together with `AlgebraicGeometry.Space.thickeningFundamentalHom_isLocallyRinged` this is the
equation of Stacks 05ZM in full: an invertible morphism of locally ringed topoi between the two
pairs, in both directions.

The inverse is an isomorphism of ringed topoi — its geometric morphism is the inverse image of an
equivalence and its structure map is the inverse of an isomorphism — and an isomorphism of ringed
topoi is locally ringed by Stacks 04H9. -/
@[stacks 05ZM "that the inverse of the canonical morphism is again a morphism of LOCALLY ringed \
topoi, so that the equation is an equivalence of locally ringed topoi in both directions"]
theorem thickeningFundamentalHomInverse_isLocallyRinged (hG : IsThickening B S hS X G) :
    (thickeningFundamentalHomInverse B S hS hG).IsLocallyRinged := by
  let : (thickeningFundamentalHom B S hS hG).toToposHom.pushforward.IsEquivalence :=
    isEquivalence_smallEtalePushforward_of_isThickening B S hS hG
  let := isIso_thickeningFundamentalHom_fSharp B S hS hG
  let : (thickeningFundamentalHomInverse B S hS hG).toToposHom.pushforward.IsEquivalence :=
    inferInstanceAs (thickeningFundamentalHom B S hS hG).toToposHom.inverseImage.IsEquivalence
  let := isIso_thickeningFundamentalHom_fSharpInverseImage B S hS hG
  let : IsIso (thickeningFundamentalHomInverse B S hS hG).fSharp :=
    inferInstanceAs (IsIso (inv (thickeningFundamentalHom B S hS hG).fSharpInverseImage))
  exact RingedToposHom.isLocallyRinged_of_isEquivalence_of_isIso_fSharp
    (thickeningFundamentalHomInverse B S hS hG)

/-! ### Cancelling the inclusion of a thickening

Two morphisms `c, c' : X ⟶ W` which agree on a thickening `Z ⊂ X` have, by Stacks 03G2 part (3),
2-isomorphic composites `i_* ⋙ c_* ≅ i_* ⋙ c'_*` of small étale direct images; and the equivalence
of topoi of Stacks 05ZM says that `i_*` may be cancelled from such a comparison.  The result is an
isomorphism `c_* ≅ c'_*` of the two direct image functors themselves, which is the *geometric*
field of a `AlgebraicGeometry.RingedToposHom.TwoIso` of the two morphisms of small étale ringed
topoi, and hence the first of the two inputs that
`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso` ([Stacks Project, Tag 04M6])
needs in order to conclude `c = c'` for an **arbitrary** thickening.

The cancellation is performed with the unit `η : 𝟭 ⟶ i^{-1} ⋙ i_*` of the adjunction rather than
with an abstract inverse of the equivalence, so that the components of the resulting isomorphism
are the units `η_M` themselves.  That is what makes it meet the comparison of the two readings of
the comorphism — `AlgebraicGeometry.Space.thickeningLiftComparison` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartProjection.lean`, whose
first factor is the direct image of the unit at the structure sheaf.

**No `@[stacks]` attribute is placed.**  Every clause of Stacks 05ZM is registered above; what is
proved here is an application of the equivalence half of it, internal to this development, and not
a further clause of the tag.

**The remaining field is not proved here.**  The `commutes` field of the 2-isomorphism — that the
isomorphism below carries the structure map of `c` to the structure map of `c'` — is a statement
about the component at the structure sheaf, and it is not reached: see the implementation notes. -/

section Agreement

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The unit of `i^{-1} ⊣ i_*` is invertible at every sheaf of sets, for a thickening.**  The
direct image along the inclusion of a thickening is fully faithful and essentially surjective, so
every sheaf lies in its essential image, and the unit of an adjunction is invertible exactly at
the objects in the essential image of the right adjoint.

This is the sheaf-of-sets form of `AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`, at
every sheaf rather than at the structure sheaf; the same step appears inside the proof of
`AlgebraicGeometry.Space.isIso_thickeningFundamentalHom_fSharp` at the structure sheaf alone. -/
theorem isIso_smallEtalePushforwardUnit_of_isThickening (hZ : IsThickening B S hS X Z.1)
    (M : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    IsIso ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app M) := by
  have := isEquivalence_pushforward_subspaceInclusion B S hS Z hZ
  exact NatIso.isIso_app_of_isIso _ _

/-- **The unit `η : 𝟭 ⟶ i^{-1} ⋙ i_*` of a thickening, as a natural isomorphism of functors on
sheaves of sets.**  This is the equivalence of the two small étale topoi of Stacks 05ZM in the
form which cancels the inclusion from a whiskered comparison, and it is the natural form of
`AlgebraicGeometry.Space.thickeningRingUnitIso`, which bundles the same unit at the structure
sheaf and at sheaves of rings. -/
def smallEtalePushforwardUnitIso (hZ : IsThickening B S hS X Z.1) :
    𝟭 (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) ≅
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage ⋙
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward :=
  NatIso.ofComponents
    (fun M => @asIso _ _ _ _
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app M)
      (isIso_smallEtalePushforwardUnit_of_isThickening B S hS Z hZ M))
    (fun f =>
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.naturality f)

/-- `AlgebraicGeometry.Space.smallEtalePushforwardUnitIso` is the unit. -/
theorem smallEtalePushforwardUnitIso_hom_app (hZ : IsThickening B S hS X Z.1)
    (M : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtalePushforwardUnitIso B S hS Z hZ).hom.app M =
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app M :=
  rfl

/-- **The comparison of the small étale direct images of two morphisms agreeing on a thickening,
after composing with the direct image along the inclusion.**  Both composites are the direct image
along the single morphism `e = i ≫ c = i ≫ c'`, by Stacks 03G2, part (3); so this needs no
hypothesis on the thickening, and the whole content of the agreement `h`, `h'` enters here.

The isomorphism is strictly weaker than an isomorphism `c_* ≅ c'_*`: it is
`AlgebraicGeometry.Space.agreeingPushforwardIso` which cancels the inclusion from it, and that
needs the thickening hypothesis. -/
def agreeingPushforwardWhiskerIso (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e) :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward ⋙
        (smallToposMorphismTypeU B S hS c).pushforward ≅
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward ⋙
        (smallToposMorphismTypeU B S hS c').pushforward :=
  smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c ≪≫
    eqToIso (congrArg
      (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W ↦
        (smallToposMorphismTypeU B S hS m).pushforward) (h.trans h'.symm)) ≪≫
    (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c').symm

/-- **Two morphisms agreeing on a thickening have isomorphic small étale direct images.**  The
inclusion is cancelled from `AlgebraicGeometry.Space.agreeingPushforwardWhiskerIso` by the
equivalence of topoi of Stacks 05ZM, in the shape

`c_* ≅ i^{-1} ⋙ (i_* ⋙ c_*) ≅ i^{-1} ⋙ (i_* ⋙ c'_*) ≅ c'_*`,

the two outer isomorphisms being the unit of `i^{-1} ⊣ i_*` whiskered with the direct image.

This is the geometric field of a `AlgebraicGeometry.RingedToposHom.TwoIso` of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` at `c` and at `c'`, for an **arbitrary**
thickening; the structure-map field is what remains, and the implementation notes say what blocks
it. -/
def agreeingPushforwardIso (hZ : IsThickening B S hS X Z.1) (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e) :
    (smallToposMorphismTypeU B S hS c).pushforward ≅
      (smallToposMorphismTypeU B S hS c').pushforward :=
  Functor.isoWhiskerRight (smallEtalePushforwardUnitIso B S hS Z hZ)
      (smallToposMorphismTypeU B S hS c).pushforward ≪≫
    Functor.isoWhiskerLeft
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage
      (agreeingPushforwardWhiskerIso B S hS Z c c' e h h') ≪≫
    (Functor.isoWhiskerRight (smallEtalePushforwardUnitIso B S hS Z hZ)
      (smallToposMorphismTypeU B S hS c').pushforward).symm

/-- The defining factorisation of `AlgebraicGeometry.Space.agreeingPushforwardIso`, stated so that
consumers rewrite with it rather than unfold the definition.  **It is the only route to the
components**: the same equation read at an object is a kernel timeout, as the implementation notes
record. -/
theorem agreeingPushforwardIso_hom (hZ : IsThickening B S hS X Z.1) (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e) :
    (agreeingPushforwardIso B S hS Z hZ c c' e h h').hom =
      (Functor.isoWhiskerRight (smallEtalePushforwardUnitIso B S hS Z hZ)
          (smallToposMorphismTypeU B S hS c).pushforward).hom ≫
        (Functor.isoWhiskerLeft
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage
          (agreeingPushforwardWhiskerIso B S hS Z c c' e h h')).hom ≫
        (Functor.isoWhiskerRight (smallEtalePushforwardUnitIso B S hS Z hZ)
          (smallToposMorphismTypeU B S hS c').pushforward).inv :=
  rfl

/-- **The component of `AlgebraicGeometry.Space.agreeingPushforwardIso` at a sheaf**: the direct
image along `c` of the unit, the whiskered comparison at the inverse image, and the inverse of the
direct image along `c'` of the unit.  At the structure sheaf the first two factors are the two
factors of `AlgebraicGeometry.Space.structureSharpThroughThickening`, which is why the comorphism
read through the thickening is what feeds the structure-map field of the 2-isomorphism. -/
theorem agreeingPushforwardIso_hom_app (hZ : IsThickening B S hS X Z.1) (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e)
    (M : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (agreeingPushforwardIso B S hS Z hZ c c' e h h').hom.app M =
      (smallToposMorphismTypeU B S hS c).pushforward.map
          ((smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z)).adj.unit.app M) ≫
        (agreeingPushforwardWhiskerIso B S hS Z c c' e h h').hom.app
          ((smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z)).inverseImage.obj M) ≫
        (Functor.isoWhiskerRight (smallEtalePushforwardUnitIso B S hS Z hZ)
          (smallToposMorphismTypeU B S hS c').pushforward).inv.app M :=
  (congrArg (fun t => NatTrans.app t M)
      (agreeingPushforwardIso_hom B S hS Z hZ c c' e h h')).trans
    ((NatTrans.comp_app _ _ M).trans
      (congrArg
        (fun q => (Functor.isoWhiskerRight (smallEtalePushforwardUnitIso B S hS Z hZ)
          (smallToposMorphismTypeU B S hS c).pushforward).hom.app M ≫ q)
        (NatTrans.comp_app _ _ M)))

end Agreement

end AlgebraicGeometry.Space

end
