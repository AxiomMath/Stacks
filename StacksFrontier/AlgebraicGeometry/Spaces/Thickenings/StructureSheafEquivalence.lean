module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSummandModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# The structure sheaf across the equivalence of étale topoi of a thickening

Let `G ⊂ X'` be a thickening of algebraic spaces over a scheme `S`, with inclusion
`i : X ⟶ X'`, where `X` is the closed subspace.  The equivalence of sheaf topoi of
[Stacks Project, Tag 05ZM] is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleTopos.lean` for sheaves of sets on the
spaces-étale sites, as
`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening`.  This file carries the
*structure sheaf* across it, in the form the consumers of the tag need.

The consumers need this.  For two morphisms `a', b' : X' ⟶ Y'` which agree on `X`, that is two
*lifts* of one morphism `X ⟶ Y'`, the structure maps `(a')^♯` and `(b')^♯` are homomorphisms
`𝒪_{Y'} ⟶ (a')_*𝒪_{X'}` and `𝒪_{Y'} ⟶ (b')_*𝒪_{X'}` into two *different* sheaves of rings on
the small étale site of `Y'`, so their difference cannot be formed until the two targets are
identified.  That identification is
`AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfRestrictEq`, and it is what
[Stacks Project, Tag 0618] needs in order to speak of the difference of two lifts, hence what
the simply transitive action of [Stacks Project, Tag 061C] and step (II) of
[Stacks Project, Tag 04AM] need.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleToposEquivOfIsThickening`: the equivalence of small étale
  sheaf topoi of a thickening, at the universe of the structure rings, presented as the direct
  image of the morphism of topoi of the inclusion.
* `AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq` and
  `AlgebraicGeometry.Space.smallEtaleInverseImageIsoOfRestrictEq`: for two morphisms agreeing
  on the closed subspace, the comparison of the two direct images, and of the two inverse
  images, of sheaves of sets.
* `AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfRestrictEq`: **the structure-sheaf
  half of [Stacks Project, Tag 05ZM]** — the two direct images `(a')_*𝒪_{X'}` and
  `(b')_*𝒪_{X'}` of the structure sheaf of `X'` along two morphisms agreeing on the closed
  subspace are canonically isomorphic as sheaves of rings.
* `AlgebraicGeometry.Space.pushforwardCommRingFunctorIsoOfRestrictEq`: the same comparison for
  sheaves of *commutative* rings, which is the spelling in which the structure map `fSharp` of
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom` takes its values.
* `AlgebraicGeometry.Space.structureSharpOfRestrictEq`: the structure map `(a')^♯` read, through
  that identification, as a homomorphism `𝒪_{Y'} ⟶ (b')_*𝒪_{X'}`, parallel to `(b')^♯`.  These
  are the two homomorphisms whose difference [Stacks Project, Tag 0618] forms.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_smallEtaleDirectImage_of_isThickening`: the direct
  image of sheaves of sets along the inclusion of a thickening is an equivalence of categories,
  at the universe of the structure rings.
* `AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward`: **the
  characterising property of the comparison** — on a direct image `i_*F` it is functoriality of
  the direct image, so the isomorphism is described and not merely produced.
* `AlgebraicGeometry.Space.forget_structureRingSheafDirectImageIsoOfRestrictEq` and
  `AlgebraicGeometry.Space.forget_pushforwardCommRingFunctorIsoOfRestrictEq`: both ring-level
  comparisons are, on underlying sheaves of sets, the one comparison of sheaves of sets.

## Implementation notes

The equivalence is obtained at the universe `u` of the structure rings, not at the universe
`u + 1` of the sites at which
`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening` is stated, because a ringed
topos in the sense of [Stacks Project, Tag 01D3] declares its underlying topos at the universe
of its structure sheaf.  Nothing has to be re-proved for that: the dense subsite
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite` is universe-agnostic, and
the comma categories indexing the comparison lemma's right Kan extension have limits of sets in
universe `u` by
`AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_smallBaseChange_op`, the small étale
sites being essentially small at `u`.  Restriction along chart base change is then an
equivalence, and it is the direct image of the morphism of small étale topoi by Stacks 03G8,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` — the inclusion of a closed
subspace being representable.  This repeats, for the direct image itself, the argument by which
`AlgebraicGeometry.Space.essSurj_smallEtalePushforward_of_isThickening` gets essential
surjectivity.

The comparison of the two direct images is the only place where the thickening hypothesis is
used, and it is used exactly once: `(a')_*` and `(b')_*` become isomorphic after precomposition
with `i_*`, because `i ≫ a' = i ≫ b'` and the direct image is functorial
(`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, Stacks 03G2 part (3)); and `i_*` is an
equivalence, so it may be cancelled.  Cancelling it is
`CategoryTheory.Equivalence.cancelCompLeft`, and the comparison it produces is *described*, not
merely produced: `CategoryTheory.Equivalence.cancelCompLeft_hom_app` says that on an object in
the image of `i_*` the cancelled isomorphism is the one it was cancelled from, which here is
functoriality of the direct image, and `i_*` being an equivalence every object is of that form.
That is what keeps the comparison from being an opaque isomorphism assembled from a universal
property which cannot say what its own values are.

Both the inverse image comparison and the two ring-level comparisons are deduced from the
direct image comparison and nothing else.  The inverse images are compared by uniqueness of
left adjoints, `CategoryTheory.Adjunction.leftAdjointUniq`, after transporting the adjunction of
`b'` along the comparison.  The ring-level comparisons are transports of ring operations along
the comparison of sheaves of sets, `Stacks.Sheaves.ToposPullback.pullbackRingSheafIsoOfNatIso`
and `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorIsoOfNatIso`; both direct-image
sheaves of rings are *defined* as such transports, so no choice enters and the two agree on
underlying sheaves of sets by construction.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace CategoryTheory.Equivalence

universe ve ue vf uf vg ug

variable {E : Type ue} [Category.{ve} E] {F : Type uf} [Category.{vf} F]
  {Gr : Type ug} [Category.{vg} Gr]

/-- **Cancelling an equivalence from the left of a composite.**  If `e : E ≌ F` and two functors
`P, Q : F ⥤ Gr` become isomorphic after precomposition with `e.functor`, then they are
isomorphic: precompose with `e.inverse` and cancel `e.inverse ⋙ e.functor`.

The resulting isomorphism is pinned down by
`CategoryTheory.Equivalence.cancelCompLeft_hom_app`: at an object in the image of `e.functor` it
is the given isomorphism. -/
noncomputable def cancelCompLeft (e : E ≌ F) {P Q : F ⥤ Gr}
    (c : e.functor ⋙ P ≅ e.functor ⋙ Q) : P ≅ Q :=
  (e.invFunIdAssoc P).symm ≪≫ Functor.isoWhiskerLeft e.inverse c ≪≫ e.invFunIdAssoc Q

/-- **The cancellation recovers the given isomorphism.**  At an object `e.functor.obj X` the
isomorphism `CategoryTheory.Equivalence.cancelCompLeft` is the one it was cancelled from.

The two counits which cancellation introduces are the image under `e.functor` of the unit, by
the triangle identity `CategoryTheory.Equivalence.functor_unit_comp`, so naturality of `c` along
that unit removes them. -/
theorem cancelCompLeft_hom_app (e : E ≌ F) {P Q : F ⥤ Gr}
    (c : e.functor ⋙ P ≅ e.functor ⋙ Q) (X : E) :
    (e.cancelCompLeft c).hom.app (e.functor.obj X) = c.hom.app X := by
  have hunit : e.functor.map (e.unit.app X) = e.counitInv.app (e.functor.obj X) :=
    (e.counitInv_app_functor X).symm
  have hnat := c.hom.naturality (e.unit.app X)
  dsimp only [Functor.comp_map] at hnat
  simp only [cancelCompLeft, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, invFunIdAssoc_inv_app,
    invFunIdAssoc_hom_app]
  rw [← hunit, reassoc_of% hnat, ← Functor.map_comp, e.functor_unit_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]

end CategoryTheory.Equivalence

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
  (O : Sheaf K RingCat.{ww'})

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The forward map of `pullbackRingSheafIsoOfNatIso J O e` is the map of inverse images of `O`
induced by the natural transformation `e.hom`. -/
@[simp]
lemma pullbackRingSheafIsoOfNatIso_hom (e : Φ ≅ Φ') :
    (pullbackRingSheafIsoOfNatIso J O e).hom = pullbackRingSheafMapOfNatTrans J O e.hom := rfl

end Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}

/-! ### The equivalence of small étale topoi at the universe of the structure rings -/

/-- **The direct image of sheaves of sets along the inclusion of a thickening is an equivalence
of categories**, at the universe of the structure rings.  This is the sheaf-of-sets half of
[Stacks Project, Tag 05ZM] in the form a ringed topos needs it: the morphism of small étale
topoi of [Stacks Project, Tag 03G2] part (3) attached to the inclusion `i : X ⟶ X'` of a
thickening has an equivalence of categories for its direct image.

Base change of étale scheme charts along `i` exhibits the small étale site of `X'` as a dense
subsite of that of `X` (`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`), so
restriction along it is an equivalence by the comparison lemma; and that restriction *is* the
direct image, by Stacks 03G8 for a representable morphism
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`). -/
theorem isEquivalence_smallEtaleDirectImage_of_isThickening (hG : IsThickening B S hS X' G) :
    (smallToposMorphismTypeU B S hS
      (IsThickening.inclusion B S hS hG)).pushforward.IsEquivalence := by
  let := isContinuous_smallBaseChange B S hS (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep
  let := thickeningChartBaseChange_isDenseSubsite B S hS hG
  let : ∀ W : (SmallEtale B S hS (IsThickening.space B S hS hG).1)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W (thickeningChartBaseChange B S hS hG).op) (Type u) :=
    fun W => hasLimitsOfShape_structuredArrow_smallBaseChange_op B S hS
      (IsThickening.inclusion B S hS hG)
      (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep W
  have hE : ((thickeningChartBaseChange B S hS hG).sheafPushforwardContinuous (Type u)
      (SmallEtale.topology B S hS X'.1)
      (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)).IsEquivalence :=
    inferInstance
  exact Functor.isEquivalence_of_iso
    (smallEtaleRingedToposHom_representable B S hS (IsThickening.inclusion B S hS hG)
      (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep).symm

/-- **The equivalence of small étale sheaf topoi of a thickening**, at the universe of the
structure rings: the sheaves of sets on the small étale site of the closed subspace `X` of a
thickening `G ⊂ X'` and those on the small étale site of `X'` are equivalent, by the direct
image of the inclusion.

This is `AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening` presented so that the
equivalence is the geometric direct image itself, which is what lets it be cancelled from a
composite of direct images. -/
noncomputable def smallEtaleToposEquivOfIsThickening (hG : IsThickening B S hS X' G) :
    Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) (Type u) ≌
      Sheaf (SmallEtale.topology B S hS X'.1) (Type u) :=
  letI := isEquivalence_smallEtaleDirectImage_of_isThickening B S hS hG
  (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG)).pushforward.asEquivalence

/-- The functor of `AlgebraicGeometry.Space.smallEtaleToposEquivOfIsThickening` is the direct
image of sheaves of sets along the inclusion of the thickening. -/
@[simp]
lemma smallEtaleToposEquivOfIsThickening_functor (hG : IsThickening B S hS X' G) :
    (smallEtaleToposEquivOfIsThickening B S hS hG).functor =
      (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG)).pushforward := rfl

/-! ### Two morphisms agreeing on the closed subspace -/

section Restrict

variable {Y' : AlgebraicSpaces B S hS} (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')
  (h : IsThickening.inclusion B S hS hG ≫ a' = IsThickening.inclusion B S hS hG ≫ b')

/-- The two direct images `(a')_*` and `(b')_*` become isomorphic after precomposition with the
direct image of the inclusion `i : X ⟶ X'` of the thickening: by functoriality of the direct
image (`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, Stacks 03G2 part (3)) both
composites are the direct image of `i ≫ a' = i ≫ b'`.

No thickening hypothesis is used here; what the thickening supplies is that `i_*` is an
equivalence, so that this precomposition may be cancelled. -/
noncomputable def smallEtaleCompPushforwardIsoOfRestrictEq :
    (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG)).pushforward ⋙
        (smallToposMorphismTypeU B S hS a').pushforward ≅
      (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG)).pushforward ⋙
        (smallToposMorphismTypeU B S hS b').pushforward :=
  smallToposMorphismTypeU_comp B S hS (IsThickening.inclusion B S hS hG) a' ≪≫
    eqToIso (congrArg (fun k => (smallToposMorphismTypeU B S hS k).pushforward) h) ≪≫
    (smallToposMorphismTypeU_comp B S hS (IsThickening.inclusion B S hS hG) b').symm

/-- **Two morphisms out of a thickening which agree on its closed subspace have isomorphic
direct images of sheaves of sets.**  For a thickening `G ⊂ X'` with inclusion `i : X ⟶ X'` and
two morphisms `a', b' : X' ⟶ Y'` with `i ≫ a' = i ≫ b'`, the two direct images `(a')_*` and
`(b')_*` on the small étale topoi are isomorphic functors.

The comparison is pinned down by
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward`: on a direct
image `i_*F` it is `AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfRestrictEq`, which is
nothing but functoriality of the direct image and the hypothesis.  Since `i_*` is an
equivalence, that determines it. -/
noncomputable def smallEtalePushforwardIsoOfRestrictEq :
    (smallToposMorphismTypeU B S hS a').pushforward ≅
      (smallToposMorphismTypeU B S hS b').pushforward :=
  (smallEtaleToposEquivOfIsThickening B S hS hG).cancelCompLeft
    (smallEtaleCompPushforwardIsoOfRestrictEq B S hS hG a' b' h)

/-- **The comparison of the two direct images is functoriality of the direct image.**  On a
sheaf of the form `i_*F`, for `i` the inclusion of the thickening, the comparison
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq` is
`AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfRestrictEq`, that is the composition
isomorphism of Stacks 03G2 part (3) followed by the hypothesis `i ≫ a' = i ≫ b'`.

This is the characterising property of the comparison: it says what the isomorphism *is*, and
since `i_*` is an equivalence every sheaf is of that form, so nothing is left unsaid.  It is
`CategoryTheory.Equivalence.cancelCompLeft_hom_app`. -/
theorem smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward
    (F : Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) (Type u)) :
    (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
        ((smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG)).pushforward.obj F) =
      (smallEtaleCompPushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app F :=
  (smallEtaleToposEquivOfIsThickening B S hS hG).cancelCompLeft_hom_app
    (smallEtaleCompPushforwardIsoOfRestrictEq B S hS hG a' b' h) F

/-- **The same comparison for the inverse images.**  Two morphisms out of a thickening agreeing
on its closed subspace have isomorphic inverse images of sheaves of sets.

This is uniqueness of left adjoints: `(a')^{-1}` and `(b')^{-1}` are both left adjoint to
`(a')_*`, the second after transporting its adjunction along
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq`. -/
noncomputable def smallEtaleInverseImageIsoOfRestrictEq :
    (smallToposMorphismTypeU B S hS a').inverseImage ≅
      (smallToposMorphismTypeU B S hS b').inverseImage :=
  Adjunction.leftAdjointUniq (smallToposMorphismTypeU B S hS a').adj
    ((smallToposMorphismTypeU B S hS b').adj.ofNatIsoRight
      (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).symm)

/-! ### The structure sheaf -/

/-- **The structure-sheaf half of [Stacks Project, Tag 05ZM].**  Let `G ⊂ X'` be a thickening of
algebraic spaces over `S`, with inclusion `i : X ⟶ X'`, and let `a', b' : X' ⟶ Y'` be two
morphisms which agree on `X`.  Then the two direct images `(a')_*𝒪_{X'}` and `(b')_*𝒪_{X'}` of
the structure sheaf of `X'` are canonically isomorphic as sheaves of rings on the small étale
site of `Y'`.

This is the sense in which the structure sheaf of `X'` is carried across the equivalence of
étale topoi of the thickening: the direct image of `𝒪_{X'}` depends only on the restriction of
the morphism to the closed subspace, because the direct image of sheaves of sets does and the
ring operations are transported along it.

It is what lets the structure maps `(a')^♯` and `(b')^♯` be compared, and so what
[Stacks Project, Tag 0618] needs in order to speak of the difference of two lifts; see
`AlgebraicGeometry.Space.structureSharpOfRestrictEq`. -/
@[stacks 05ZM "the structure sheaf transported across the equivalence of étale topoi of a \
thickening: the direct image of the structure sheaf of the ambient space depends only on the \
restriction of the morphism to the closed subspace"]
noncomputable def structureRingSheafDirectImageIsoOfRestrictEq :
    structureRingSheafDirectImage B S hS a' ≅ structureRingSheafDirectImage B S hS b' :=
  pullbackRingSheafIsoOfNatIso.{u, u, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS Y'.1) (structureRingSheaf B S hS X')
    (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h)

/-- **The structure-sheaf half of [Stacks Project, Tag 05ZM] for sheaves of commutative
rings.**  This is the spelling in which the structure map `fSharp` of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` takes its values. -/
@[stacks 05ZM "the structure sheaf transported across the equivalence of étale topoi of a \
thickening, for sheaves of commutative rings: the direct image functor of sheaves of \
commutative rings depends only on the restriction of the morphism to the closed subspace"]
noncomputable def pushforwardCommRingFunctorIsoOfRestrictEq :
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS a') ≅
      pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS b') :=
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS Y'.1)
    (Φ := (smallToposMorphismTypeU B S hS a').pushforward)
    (Φ' := (smallToposMorphismTypeU B S hS b').pushforward)
    (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h)

/-- **On underlying sheaves of sets the ring comparison is the set comparison.**  Forgetting the
ring structure in `AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfRestrictEq` gives
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq` at the structure sheaf of `X'`.

So the ring-level identification is not a second construction: it is the one comparison of
sheaves of sets, with the ring operations carried along.  In particular whatever is known about
the values of the comparison of sheaves of sets — notably
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward` — is known
about it. -/
theorem forget_structureRingSheafDirectImageIsoOfRestrictEq :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (structureRingSheafDirectImageIsoOfRestrictEq B S hS hG a' b' h).hom =
      (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
        ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget RingCat.{u})).obj
          (structureRingSheaf B S hS X')) :=
  ringSheafMap_pullbackRingSheafMapOfNatTrans.{u, u, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS Y'.1) (structureRingSheaf B S hS X')
    (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom

/-- The same for the comparison of sheaves of commutative rings: on underlying sheaves of sets
`AlgebraicGeometry.Space.pushforwardCommRingFunctorIsoOfRestrictEq` is again
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq`.  So the commutative and the
non-commutative comparisons are the same comparison. -/
theorem forget_pushforwardCommRingFunctorIsoOfRestrictEq :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget CommRingCat.{u})).map
        ((pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (smallEtaleRingedTopos B S hS X').O) =
      (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
        ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X').O) :=
  pullbackCommRingSheafIsoOfNatIso_hom_forget.{u, u, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS Y'.1)
    (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h)
    (smallEtaleRingedTopos B S hS X').O

/-- **The structure map of `a'`, read into the direct image along `b'`.**  Through
`AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfRestrictEq` the structure map
`(a')^♯ : 𝒪_{Y'} ⟶ (a')_*𝒪_{X'}` becomes a homomorphism `𝒪_{Y'} ⟶ (b')_*𝒪_{X'}`, parallel to
`(b')^♯` itself.

This pair of parallel homomorphisms of sheaves of rings on the small étale site of `Y'` is what
[Stacks Project, Tag 0618] takes the difference of, and the identification which puts them in
parallel is the structure-sheaf half of [Stacks Project, Tag 05ZM]. -/
noncomputable def structureSharpOfRestrictEq :
    structureRingSheaf B S hS Y' ⟶ structureRingSheafDirectImage B S hS b' :=
  structureSharp B S hS a' ≫
    (structureRingSheafDirectImageIsoOfRestrictEq B S hS hG a' b' h).hom

end Restrict

end AlgebraicGeometry.Space

end
