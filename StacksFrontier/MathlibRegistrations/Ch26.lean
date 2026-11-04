module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
public import Mathlib.Topology.Spectral.Prespectral
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Stacks tags of Chapter 26 (Schemes) covered by Mathlib

This file records Stacks Project tags from Chapter 26 (Schemes) whose statements are already
available in Mathlib, by attaching each tag to the Mathlib declarations that state it. When a
tag is covered by several declarations, each registration names the part it covers.

Mathlib models the open subspace of a locally ringed space associated to an open subset as the
restriction along an open embedding, and the category of affine schemes as a full subcategory of
schemes; morphisms of schemes are morphisms of locally ringed spaces.

* Tag 01JX (schemes over a base, base change): items (1), (3), (4), (5) and (6); items (2) and (7)
  are the special cases of (1) and (5) over affine schemes.
* Tag 01K0 (the scheme-theoretic fibre).
* Tag 01K1 (fibres are homeomorphic onto their image): the first diagram only. The second
  diagram, `Spec(𝒪_{S,s}) ×_S X → X`, is not stated in Mathlib.
* Tag 01K3 (quasi-compact morphisms).
* Tag 01K4 (quasi-compactness on affine opens): the equivalence (1) ⇔ (2) only. The equivalence
  with (3), an affine open covering of the target, is not stated for quasi-compact morphisms.
* Tags 01K5 and 01K6 (base change and composition of quasi-compact morphisms).
* Tag 01K7 (closed immersions are quasi-compact), as the composite of two instances.
* Tags 01KB and 01KC (universally closed morphisms, and lifting of specializations).

## References

* [Stacks: Schemes](https://stacks.math.columbia.edu/tag/01H8)
-/

@[expose] public section

open AlgebraicGeometry

add_to_stacks 03GI AlgebraicGeometry.QuasiCompact.of_comp

add_to_stacks 01HG "open subspace, as the restriction along an open embedding"
  LocallyRingedSpace.restrict
add_to_stacks 01HG "the inclusion of the open subspace" LocallyRingedSpace.ofRestrict

add_to_stacks 01HH "existence of the isomorphism with the open subspace on the image"
  LocallyRingedSpace.IsOpenImmersion.isoRestrict
add_to_stacks 01HH "the factorization f = j ∘ f'"
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
add_to_stacks 01HH "uniqueness, as j is a monomorphism" LocallyRingedSpace.IsOpenImmersion.mono

add_to_stacks 01HI "existence of the restriction, through the open immersion V → Y"
  LocallyRingedSpace.IsOpenImmersion.lift
add_to_stacks 01HI "the square commutes" LocallyRingedSpace.IsOpenImmersion.lift_fac
add_to_stacks 01HI "uniqueness" LocallyRingedSpace.IsOpenImmersion.lift_uniq

add_to_stacks 01HU "(1) the structure sheaf" Spec.structureSheaf
add_to_stacks 01HU "(1) its sections over a standard open D(f) are the localization R_f"
  StructureSheaf.IsLocalization.to_basicOpen
add_to_stacks 01HU "(2) the spectrum as a locally ringed space" Spec.locallyRingedSpaceObj
add_to_stacks 01HU "(3) the sheaf of modules associated to a module" tilde

add_to_stacks 01HW "the category of affine schemes, schemes isomorphic to some Spec R"
  AffineScheme
add_to_stacks 01HW "being isomorphic to some Spec R is being affine" essImage_Spec
add_to_stacks 01HW "morphisms of schemes are the morphisms of locally ringed spaces"
  Scheme.fullyFaithfulForgetToLocallyRingedSpace

add_to_stacks 01HZ "D(f), the locus where the germ of f is a unit, is open" RingedSpace.basicOpen
add_to_stacks 01HZ "membership in D(f) for a global section" RingedSpace.mem_top_basicOpen
add_to_stacks 01HZ "f is invertible on D(f)" RingedSpace.isUnit_res_basicOpen

add_to_stacks 01I0 "for X = Spec R" basicOpen_eq_of_affine
add_to_stacks 01I0 "for X affine, through X ≅ Spec Γ(X)" Scheme.toSpecΓ_preimage_basicOpen

add_to_stacks 01I2 "the equivalence with the opposite of rings" AffineScheme.equivCommRingCat
add_to_stacks 01I2 "it is given by global sections" AffineScheme.ΓIsEquiv

add_to_stacks 01I3 IsAffineOpen.basicOpen

add_to_stacks 01HB "Part 1: a locally ringed space is a topological space with a sheaf of rings all
  of whose stalks are local rings." AlgebraicGeometry.LocallyRingedSpace

add_to_stacks 01HB "Part 2: the local ring O_{X,x} of X at x is the stalk, which is local (the
  maximal ideal m_x is `IsLocalRing.maximalIdeal` of the stalk)."
  AlgebraicGeometry.LocallyRingedSpace.isLocalRing

add_to_stacks 01HB "Part 2: the residue field kappa(x) = O_{X,x}/m_x of X at x."
  AlgebraicGeometry.LocallyRingedSpace.residueField

add_to_stacks 01HB "Part 3: a morphism of locally ringed spaces is a morphism of ringed spaces whose
  stalk maps are local ring maps." AlgebraicGeometry.LocallyRingedSpace.Hom

add_to_stacks 01HC "An isomorphism of ringed spaces between locally ringed spaces is an isomorphism
  of locally ringed spaces." AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso

-- Stacks 02O0 and 02V0: finite discrete schemes are affine; composites of immersions.
add_to_stacks 02O0 "the statement"
  AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCommRingCat
add_to_stacks 02V0 "composition of immersions" AlgebraicGeometry.IsImmersion.comp
add_to_stacks 02V0 "composition of closed immersions" AlgebraicGeometry.IsClosedImmersion.comp
add_to_stacks 02V0 "composition of open immersions" AlgebraicGeometry.IsOpenImmersion.comp

add_to_stacks 01HC "The lift of the isomorphism of ringed spaces has the same underlying morphism."
  AlgebraicGeometry.LocallyRingedSpace.homOfSheafedSpaceHomOfIsIso

add_to_stacks 01HE AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

add_to_stacks 01HF "The stalk of the restriction O_X|_U at u is the stalk of O_X at u."
  AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso

add_to_stacks 01HF "(U, O_X|_U) is a locally ringed space."
  AlgebraicGeometry.LocallyRingedSpace.restrict

add_to_stacks 01HF "The morphism j : (U, O_U) → (X, O_X)."
  AlgebraicGeometry.LocallyRingedSpace.ofRestrict

add_to_stacks 01HF "j is an open immersion."
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.ofRestrict

/- Stacks 01ID (direct sums and colimits of quasi-coherent modules on an affine scheme are
quasi-coherent) is not stated in Mathlib; it is registered in
`StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits`. -/

/- Stacks 01IA: a quasi-coherent module on `Spec R` is `Γ(M)^~`, through `fromTildeΓ`. -/
add_to_stacks 01IA AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent

/- Stacks 01IB: `M ↦ M^~` and `F ↦ Γ(Spec R, F)` are quasi-inverse equivalences between
`R`-modules and quasi-coherent modules on `Spec R`. -/
add_to_stacks 02YC CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms

add_to_stacks 01IB AlgebraicGeometry.tildeEquiv

add_to_stacks 01IJ "a scheme: a locally ringed space locally isomorphic to an affine scheme"
  AlgebraicGeometry.Scheme
add_to_stacks 01IJ "a morphism of schemes: a morphism of locally ringed spaces"
  AlgebraicGeometry.Scheme.Hom
add_to_stacks 01IJ "the category of schemes" AlgebraicGeometry.Scheme.instCategory

add_to_stacks 01IK "the source of an open immersion into a scheme is a scheme"
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toScheme
add_to_stacks 01IK "an open subspace of a scheme is a scheme"
  AlgebraicGeometry.Scheme.Opens.toScheme

add_to_stacks 01IS "existence of generic points of irreducible closed subsets (quasi-sober)"
  AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat
add_to_stacks 01IS "uniqueness of generic points (T0)"
  AlgebraicGeometry.instT0SpaceCarrierCarrierCommRingCat

add_to_stacks 01IT AlgebraicGeometry.Scheme.isBasis_affineOpens

add_to_stacks 01IV "the underlying space of a scheme is prespectral"
  AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat
add_to_stacks 01IV "a prespectral space is locally quasi-compact"
  instLocallyCompactSpaceOfPrespectralSpace

add_to_stacks 01J0 "reduced scheme; Mathlib's definition asks all rings of sections to be reduced"
  AlgebraicGeometry.IsReduced
add_to_stacks 01J0 "a scheme all of whose local rings are reduced is reduced"
  AlgebraicGeometry.isReduced_of_isReduced_stalk
add_to_stacks 01J0 "the local rings of a reduced scheme are reduced"
  AlgebraicGeometry.isReduced_stalk_of_isReduced

add_to_stacks 01J1 "local rings reduced implies all rings of sections reduced"
  AlgebraicGeometry.isReduced_of_isReduced_stalk
add_to_stacks 01J1 "all rings of sections reduced implies local rings reduced"
  AlgebraicGeometry.isReduced_stalk_of_isReduced

add_to_stacks 01JX "(1) a scheme over S; (2) is the case S = Spec R"
  AlgebraicGeometry.Scheme.Over
add_to_stacks 01JX "(3) a morphism of schemes over S" AlgebraicGeometry.Scheme.Hom.IsOver
add_to_stacks 01JX "(3) the defining condition of a morphism over S"
  AlgebraicGeometry.Scheme.Hom.isOver_iff
add_to_stacks 01JX "(4) Mor_S(X, Y) as the hom-set from X.asOver S to Y.asOver S in Over S"
  AlgebraicGeometry.Scheme.asOver
add_to_stacks 01JX "(5) the base change of X as a scheme over S'; (7) is the affine case"
  AlgebraicGeometry.Scheme.canonicallyOverPullback
add_to_stacks 01JX "(5) and (6) base change of schemes and morphisms over S, as a functor"
  CategoryTheory.Over.pullback
add_to_stacks 01K0 "the scheme theoretic fibre" AlgebraicGeometry.Scheme.Hom.fiber
add_to_stacks 01K0 "the projection from the fibre to Spec κ(s)"
  AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_stacks 01K0 "the fibre as a scheme over κ(s)"
  AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_stacks 01K1 "first diagram: X_s → X is a preimmersion, so an embedding"
  AlgebraicGeometry.instIsPreimmersionFiberι
add_to_stacks 01K1 "first diagram: X_s is homeomorphic to its image, the set-theoretic fibre"
  AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_stacks 01K3 AlgebraicGeometry.QuasiCompact
add_to_stacks 01K4 "(1) ⇔ (2)" AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen
add_to_stacks 01K5 AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_stacks 01K6 AlgebraicGeometry.quasiCompact_comp
add_to_stacks 01K7 "step 1: a closed immersion is universally closed"
  AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion
add_to_stacks 01K7 "step 2: a universally closed morphism is quasi-compact"
  AlgebraicGeometry.instQuasiCompactOfUniversallyClosed
add_to_stacks 01KB AlgebraicGeometry.UniversallyClosed
add_to_stacks 01KC "(1) and (2)" AlgebraicGeometry.universallyClosed_eq_universallySpecializing

/-! ### Further tags of this chapter covered by Mathlib

Where a Mathlib declaration is more general than the tag, the note says how the tag is the
special case.

Not recorded here: Tag 01KR. Mathlib states that `X ×_T Y ⟶ X ×_S Y` is an immersion
(`AlgebraicGeometry.IsImmersion.instMapDescScheme`) and a closed immersion when `T ⟶ S` is
separated (`AlgebraicGeometry.IsSeparated.instIsClosedImmersionMapDescScheme`), but no
declaration states that it is quasi-compact when `T ⟶ S` is quasi-separated. -/

add_to_stacks 01L3 CategoryTheory.Limits.pullback.isIso_diagonal_iff
add_to_stacks 01L4 AlgebraicGeometry.IsSeparated.isSeparated_of_mono
add_to_stacks 01L5 CategoryTheory.mono_comp
add_to_stacks 01L6 AlgebraicGeometry.SurjectiveOnStalks.mono_of_injective
add_to_stacks 01L7 "an immersion is a monomorphism: `IsImmersion` extends `IsPreimmersion`, and \
  preimmersions are monomorphisms" AlgebraicGeometry.IsPreimmersion.instMonoScheme
add_to_stacks 01L7 "in particular any immersion is separated (monomorphisms are separated)"
  AlgebraicGeometry.IsSeparated.isSeparated_of_mono
add_to_stacks 01L9 "the general statement: Spec(O_{S,s}) → S is a preimmersion, hence a \
  monomorphism" AlgebraicGeometry.instIsPreimmersionFromSpecStalk
add_to_stacks 01L9 "Spec(Q) → Spec(Z), and Spec of any localization: a preimmersion, hence a \
  monomorphism" AlgebraicGeometry.IsPreimmersion.of_isLocalization

add_to_stacks 01KD "existence part of the valuative criterion"
  AlgebraicGeometry.ValuativeCriterion.Existence
add_to_stacks 01KD "uniqueness part of the valuative criterion"
  AlgebraicGeometry.ValuativeCriterion.Uniqueness

add_to_stacks 01KI "the diagonal of Spec S ⟶ Spec R is a closed immersion"
  AlgebraicGeometry.IsSeparated.instMap

add_to_stacks 01KK "(1) separated morphism: the diagonal is a closed immersion"
  AlgebraicGeometry.IsSeparated
add_to_stacks 01KK "(2) quasi-separated morphism: the diagonal is quasi-compact"
  AlgebraicGeometry.QuasiSeparated
add_to_stacks 01KK "(3) separated scheme: separated over the terminal scheme Spec ℤ"
  AlgebraicGeometry.Scheme.IsSeparated
add_to_stacks 01KK "(4) quasi-separated scheme: QuasiSeparatedSpace X is equivalent to X ⟶ Spec ℤ \
  being quasi-separated"
  AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated

add_to_stacks 01KN "an affine scheme is separated"
  AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine
add_to_stacks 01KN "a morphism from an affine scheme is separated: more general, every morphism \
  out of a separated scheme is separated"
  AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated

add_to_stacks 01KS "the graph X ⟶ X ×_S Y is an immersion: more general, cancellation for \
  immersions, applied to the graph followed by the first projection, which is 𝟙 X"
  AlgebraicGeometry.IsImmersion.of_comp
add_to_stacks 01KS "the graph is a closed immersion if Y is separated over S"
  AlgebraicGeometry.IsSeparated.instIsClosedImmersionLiftSchemeId
add_to_stacks 01KS "the graph is quasi-compact if Y is quasi-separated over S: more general, \
  cancellation of quasi-compactness against a quasi-separated map, applied to the graph followed \
  by the first projection (quasi-separated as a base change of Y ⟶ S)"
  AlgebraicGeometry.QuasiCompact.of_comp

add_to_stacks 01KT "a section s of f is an immersion: more general, cancellation for \
  immersions, applied to s ≫ f = 𝟙 S"
  AlgebraicGeometry.IsImmersion.of_comp
add_to_stacks 01KT "s is a closed immersion if f is separated: more general, cancellation for \
  closed immersions against a separated map, applied to s ≫ f = 𝟙 S"
  AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_stacks 01KT "s is quasi-compact if f is quasi-separated: more general, cancellation of \
  quasi-compactness against a quasi-separated map, applied to s ≫ f = 𝟙 S"
  AlgebraicGeometry.QuasiCompact.of_comp

add_to_stacks 01KU "(1) a composition of separated morphisms is separated"
  AlgebraicGeometry.IsSeparated.stableUnderComposition
add_to_stacks 01KU "(2) a composition of quasi-separated morphisms is quasi-separated"
  AlgebraicGeometry.quasiSeparated_isStableUnderComposition
add_to_stacks 01KU "(3) the base change of a separated morphism is separated"
  AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_stacks 01KU "(4) the base change of a quasi-separated morphism is quasi-separated"
  AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
add_to_stacks 01KU "(5), (6) a fibre product of (quasi-)separated morphisms is (quasi-)separated: \
  more general, for any morphism property stable under base change and composition"
  CategoryTheory.MorphismProperty.pullbackMap

add_to_stacks 01KV "if g ∘ f is separated then so is f"
  AlgebraicGeometry.IsSeparated.of_comp
add_to_stacks 01KV "if g ∘ f is quasi-separated then so is f"
  AlgebraicGeometry.QuasiSeparated.of_comp

add_to_stacks 01L2 "a monomorphism of schemes is a monomorphism in the category of schemes"
  CategoryTheory.Mono

add_to_stacks 01J2 AlgebraicGeometry.affine_isReduced_iff

/- Stacks 01J6: the inverse map is `xφ ↦ Spec.map φ ≫ X.fromSpecStalk x`, the construction of
the tag. -/
add_to_stacks 01J6 AlgebraicGeometry.SpecToEquivOfLocalRing

add_to_stacks 01JC "the glued scheme" AlgebraicGeometry.Scheme.GlueData.glued
add_to_stacks 01JC "its locally ringed space is the gluing of locally ringed spaces of \
  Stacks 01JB"
  AlgebraicGeometry.Scheme.GlueData.isoLocallyRingedSpace

add_to_stacks 01JG "representable presheaf, on any category; here the category of schemes"
  CategoryTheory.Functor.IsRepresentable

add_to_stacks 01JH "for `n = Unit`, `Spec ℤ[x]` represents `T ↦ Γ(T, 𝒪_T)`; \
  the universal family is the image of `x`" AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv
add_to_stacks 01JH "naturality of the identification in `T`"
  AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp

add_to_stacks 01JM "finite limits" AlgebraicGeometry.instHasFiniteLimitsScheme
add_to_stacks 01JM "the final object `Spec ℤ`" AlgebraicGeometry.specZIsTerminal
add_to_stacks 01JM "fibre products" AlgebraicGeometry.Scheme.Pullback.instHasPullbacks

add_to_stacks 01JP "the fibre product `X ×_S Y`" CategoryTheory.Limits.pullback
add_to_stacks 01JP "the projection `p`" CategoryTheory.Limits.pullback.fst
add_to_stacks 01JP "the projection `q`" CategoryTheory.Limits.pullback.snd
add_to_stacks 01JP "the square is universal" CategoryTheory.Limits.pullbackIsPullback

add_to_stacks 01JQ AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine

add_to_stacks 01JR "the canonical morphism `V ×_U W ⟶ X ×_S Y` is an open immersion"
  AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion
add_to_stacks 01JR "its image is `p⁻¹(V) ∩ q⁻¹(W)`" AlgebraicGeometry.Scheme.Pullback.range_map

add_to_stacks 01JV "the inverse image of a closed subscheme, as an ideal sheaf"
  AlgebraicGeometry.Scheme.IdealSheafData.comap
add_to_stacks 01JV "the closed subscheme it cuts out is `Z ×_Y X`"
  AlgebraicGeometry.Scheme.IdealSheafData.comapIso
