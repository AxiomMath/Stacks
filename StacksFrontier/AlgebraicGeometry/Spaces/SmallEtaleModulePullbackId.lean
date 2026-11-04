module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The unit law of Stacks 03LU

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` contained
in a big fppf site `B` the adjoint pair `(f^*, f_*)` on `𝒪`-modules of the small étale sites.
This file proves its **unit law**: along an identity both halves of the pair are the identity
functor,

`(𝟙 X)_* ≅ 𝟭 Mod(𝒪_X)` and `(𝟙 X)^* ≅ 𝟭 Mod(𝒪_X)`.

The direct-image half is proved and the inverse-image half is its transpose: the inverse image
is a left adjoint of the direct image by `AlgebraicGeometry.Space.modulePullbackAdjunction`, and
a left adjoint of the identity functor is the identity functor.

The direct-image half splits in two, and the second half is the content of this file.

*On sheaves of sets.* Base change of the spaces-étale site along an identity is the identity
functor — `AlgebraicGeometry.Space.spacesBaseChange_id`, the restriction of
`CategoryTheory.Over.pullbackId` to the objects étale over the base — and the direct image of
sheaves of sets on the small étale sites is the spaces-étale direct image conjugated by the
comparison equivalence of Stacks 03G1. So the direct image along an identity is the composite
of the right Kan extension along the comparison functor with restriction along it, and the
counit of that adjunction identifies the composite with the identity functor. That is
`AlgebraicGeometry.Space.smallEtaleDirectImageIdIso`.

*On the structure map.* What the module statement needs in addition is that
`AlgebraicGeometry.Space.structureSharp B S hS (𝟙 X) : 𝒪_X ⟶ (𝟙 X)_*𝒪_X` is exactly that
identification, and this is where the work is. The structure map is built chartwise, as a lift
into a pointwise right Kan extension, so it is pinned down by its chart projections
(`AlgebraicGeometry.Space.chartProjection_structureMapApp` and
`AlgebraicGeometry.Space.chartProjection_ext`); and the identification above, read on sections
over an étale chart `V` of `X`, is itself a chart projection — the one at the structured arrow
whose morphism is the inverse of the identity base-change comparison at `V`. Both sides are
therefore pullback of regular functions along a single morphism of schemes, and that morphism is
the identity of `V`, because the cartesian projection of base change along `𝟙 X` *is* the
identity base-change comparison
(`AlgebraicGeometry.Space.toSpaces_map_spacesBaseChange_id_hom`). No covering argument and no
refinement of charts intervenes.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDirectImageIdIso`: the direct image of sheaves of sets on
  the small étale sites along an identity is the identity functor.
* `AlgebraicGeometry.Space.modulePushforwardIdIso`: **the unit law for the direct image of
  `𝒪`-modules**, `(𝟙 X)_* ≅ 𝟭`.
* `AlgebraicGeometry.Space.modulePullbackIdIso`: **the unit law of Stacks 03LU**,
  `(𝟙 X)^* ≅ 𝟭`.

## Main results

* `AlgebraicGeometry.Space.chartBaseChangeMap_id` and
  `AlgebraicGeometry.Space.chartPullback_id`: the chart morphism of an identity at the
  structured arrow given by the identity base-change comparison is the identity, so pullback of
  regular functions along it does nothing.
* `AlgebraicGeometry.Space.structureSharpSet_id`: **the structure map of an identity is the
  canonical identification of `𝒪_X` with `(𝟙 X)_*𝒪_X`** on underlying sheaves of sets.
* `AlgebraicGeometry.Space.isIso_structureSharp_id`: consequently the structure map of an
  identity is invertible as a morphism of sheaves of rings.
* `AlgebraicGeometry.Space.isEquivalence_smallEtaleDirectImage_id` and
  `AlgebraicGeometry.Space.isEquivalence_modulePullback_id`: the direct image of sheaves of sets
  and the inverse image of modules along an identity are equivalences.
* `AlgebraicGeometry.Space.reflectsIsomorphisms_modulePullback_id`: the inverse image of modules
  along an identity reflects isomorphisms, which is the form consumers of the unit law use.

## Implementation notes

The identification of the direct image of sheaves of sets with the identity functor is built
against the right Kan extension form
`AlgebraicGeometry.Space.smallEtaleDirectImageRan` of the direct image rather than against
`AlgebraicGeometry.Space.smallEtaleDirectImage` itself, for the reason recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean`: the
chartwise description of the sections, which is what computes the structure map, is available
only in the Kan extension form. The two are transported into each other by
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` at the very end, exactly as the structure
map itself is.

Because of that choice, `AlgebraicGeometry.Space.smallEtaleDirectImageRanIdIso_hom_app_apply`
holds by `rfl`: the chart projection of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean` is, on an element, the counit of
the Kan-extension adjunction applied after a restriction, and that is literally what the
identification is. Keeping the identification a composite of a whiskering with that counit —
rather than assembling it by `CategoryTheory.NatIso.ofComponents` — is what makes the chart
computation a definitional unfolding instead of a calculation.

The counit of the Kan-extension adjunction is invertible because restriction along the
comparison functor is an equivalence and the Kan extension is its quasi-inverse; the
factorization that exhibits this is
`AlgebraicGeometry.Space.restriction_map_ranIso_inv_comp_counitIso`, already available.

What this file does *not* give is the rest of the pseudofunctoriality of Stacks 03LU. The
associativity coherence of the composition comparison and the two coherences relating it to the
unit law are assertions about the geometric comparison of Stacks 03G2, part (3), and remain
unavailable; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The direct image of sheaves of sets along an identity -/

/-- The direct image of spaces-étale sheaves of sets at the universe of the structure rings
along an identity morphism of algebraic spaces is the identity functor: base change of the
spaces-étale site along an identity is the identity functor. -/
def spacesDirectImageIdIso (X : AlgebraicSpaces B S hS) :
    spacesDirectImage B S hS (𝟙 X) ≅ 𝟭 (Sheaf (SpacesEtale.topology B S hS X) (Type u)) :=
  Functor.sheafPushforwardContinuousId' (spacesBaseChange_id B S hS X) (Type u)
    (SpacesEtale.topology B S hS X)

/-- The counit of the Kan-extension adjunction along the comparison functor of Stacks 03G1 is
invertible: restriction along the comparison functor is an equivalence and the Kan extension is
its quasi-inverse. -/
instance isIso_comparisonCounit_app (X : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    IsIso ((comparisonAdjunction B S hS X).counit.app F) := by
  rw [← restriction_map_ranIso_inv_comp_counitIso B S hS X F]
  exact IsIso.comp_isIso' (((smallEtaleComparisonRestriction B S hS X).mapIso
      ((smallEtaleComparisonRanIso B S hS X).app F).symm).isIso_hom)
    (((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app F).isIso_hom)

/-- The right Kan extension along the comparison functor of Stacks 03G1, followed by restriction
along it, is the identity functor on sheaves of sets on the small étale site: the comparison is
the counit of the Kan-extension adjunction. -/
def comparisonRanRestrictionIso (X : AlgebraicSpaces B S hS) :
    smallEtaleComparisonRan B S hS X ⋙ smallEtaleComparisonRestriction B S hS X ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :=
  NatIso.ofComponents (fun F ↦ asIso ((comparisonAdjunction B S hS X).counit.app F))
    (fun φ ↦ (comparisonAdjunction B S hS X).counit.naturality φ)

/-- The Kan-extension form of the direct image of sheaves of sets along an identity morphism of
algebraic spaces is the identity functor. -/
def smallEtaleDirectImageRanIdIso (X : AlgebraicSpaces B S hS) :
    smallEtaleDirectImageRan B S hS (𝟙 X) ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :=
  Functor.isoWhiskerLeft (smallEtaleComparisonRan B S hS X)
      (Functor.isoWhiskerRight (spacesDirectImageIdIso B S hS X)
        (smallEtaleComparisonRestriction B S hS X)) ≪≫
    comparisonRanRestrictionIso B S hS X

/-- **The direct image of sheaves of sets on the small étale sites along an identity morphism of
algebraic spaces is the identity functor.** -/
def smallEtaleDirectImageIdIso (X : AlgebraicSpaces B S hS) :
    smallEtaleDirectImage B S hS (𝟙 X) ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :=
  smallEtaleDirectImageRanIso B S hS (𝟙 X) ≪≫ smallEtaleDirectImageRanIdIso B S hS X

/-- The identification of the Kan-extension form of the direct image along an identity with the
identity functor, read on sections over an étale scheme chart, is the chart projection at the
structured arrow given by the identity base-change comparison.

This holds by definitional unfolding: both are the counit of the Kan-extension adjunction
applied after restriction along that morphism. -/
theorem smallEtaleDirectImageRanIdIso_hom_app_apply (X : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS X.1)
    (a : ((smallEtaleDirectImageRan B S hS (𝟙 X)).obj F).obj.obj (op V)) :
    ((smallEtaleDirectImageRanIdIso B S hS X).hom.app F).hom.app (op V) a =
      (chartProjection B S hS (𝟙 X) V
        (StructuredArrow.mk ((spacesBaseChange_id B S hS X).inv.app
          ((comparisonFunctor B S hS X).obj V)).op)).app F a :=
  rfl

/-- The direct image of sheaves of sets along an identity is an equivalence. -/
instance isEquivalence_smallEtaleDirectImage_id (X : AlgebraicSpaces B S hS) :
    (smallEtaleDirectImage B S hS (𝟙 X)).IsEquivalence :=
  Functor.isEquivalence_of_iso (smallEtaleDirectImageIdIso B S hS X).symm

/-! ### The structure map of an identity -/

/-- The cartesian projection of base change along an identity morphism of algebraic spaces is
the identity base-change comparison of
`AlgebraicGeometry.Space.spacesBaseChange_id`. Both are
`CategoryTheory.Limits.pullback.fst` of the structure morphism against the identity. -/
theorem toSpaces_map_spacesBaseChange_id_hom (X : AlgebraicSpaces B S hS)
    (W : SpacesEtale B S hS X) :
    (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange_id B S hS X).hom.app W) =
      (spacesBaseChange B S hS (𝟙 X)).projection.app W := by
  dsimp only [spacesBaseChange_id, spacesBaseChange, SpacesEtale.toSpaces]
  simp [Over.pullbackId, SpacesEtale.inclusion, ObjectProperty.lift]

/-- The inverse of the identity base-change comparison, followed by the cartesian projection of
base change along the identity, is the identity. -/
theorem toSpaces_map_spacesBaseChange_id_inv_comp_projection (X : AlgebraicSpaces B S hS)
    (W : SpacesEtale B S hS X) :
    (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange_id B S hS X).inv.app W) ≫
        (spacesBaseChange B S hS (𝟙 X)).projection.app W =
      𝟙 ((SpacesEtale.toSpaces B S hS X).obj W) := by
  rw [← toSpaces_map_spacesBaseChange_id_hom, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

/-- **The chart morphism of an identity is an identity.** For an étale scheme chart `V` of `X`,
the morphism of schemes induced by the chart of `X` above `X ×_X V` given by the inverse of the
identity base-change comparison at `V` is the identity of `V`. -/
theorem chartBaseChangeMap_id (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1) :
    chartBaseChangeMap B S hS (𝟙 X) V
        (StructuredArrow.mk ((spacesBaseChange_id B S hS X).inv.app
          ((comparisonFunctor B S hS X).obj V)).op) =
      𝟙 ((SmallEtale.toOver B S hS X.1).obj V) := by
  apply yoneda.map_injective
  rw [yoneda_map_chartBaseChangeMap]
  refine Eq.trans (congrArg (fun m ↦ m.hom)
    (toSpaces_map_spacesBaseChange_id_inv_comp_projection B S hS X
      ((comparisonFunctor B S hS X).obj V))) ?_
  exact (CategoryTheory.Functor.map_id yoneda _).symm

/-- Pullback of regular functions along the chart morphism of an identity does nothing. -/
theorem chartPullback_id (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1)
    (x : (structureSetSheaf B S hS X).obj.obj (op V)) :
    chartPullback B S hS (𝟙 X) V
        (StructuredArrow.mk ((spacesBaseChange_id B S hS X).inv.app
          ((comparisonFunctor B S hS X).obj V)).op) x = x := by
  unfold chartPullback
  rw [chartBaseChangeMap_id]
  rfl

/-- **The structure map of an identity is the identity**, in the Kan-extension form of the
direct image: composed with the identification of that direct image with the identity functor
it is the identity of `𝒪_X`.

Both sides are determined by their chart projections, and on the chart given by the inverse of
the identity base-change comparison both are pullback of regular functions along the identity. -/
theorem structureSharpRanSet_id (X : AlgebraicSpaces B S hS) :
    structureSharpRanSet B S hS (𝟙 X) ≫
        (smallEtaleDirectImageRanIdIso B S hS X).hom.app (structureSetSheaf B S hS X) =
      𝟙 (structureSetSheaf B S hS X) := by
  refine Sheaf.hom_ext_sections (fun W x ↦ ?_)
  obtain ⟨V⟩ := W
  exact (smallEtaleDirectImageRanIdIso_hom_app_apply B S hS X (structureSetSheaf B S hS X) V
      (structureMapApp B S hS (𝟙 X) V x)).trans
    ((chartProjection_structureMapApp B S hS (𝟙 X) V _ x).trans
      (chartPullback_id B S hS X V x))

/-- The structure map of an identity, composed with the identification of the direct image along
an identity with the identity functor, is the identity of `𝒪_X`. -/
theorem structureSharpSet_comp_idIso (X : AlgebraicSpaces B S hS) :
    structureSharpSet B S hS (𝟙 X) ≫
        (smallEtaleDirectImageIdIso B S hS X).hom.app (structureSetSheaf B S hS X) =
      𝟙 (structureSetSheaf B S hS X) := by
  have h : (smallEtaleDirectImageIdIso B S hS X).hom.app (structureSetSheaf B S hS X) =
      (smallEtaleDirectImageRanIso B S hS (𝟙 X)).hom.app (structureSetSheaf B S hS X) ≫
        (smallEtaleDirectImageRanIdIso B S hS X).hom.app (structureSetSheaf B S hS X) := rfl
  rw [h, ← Category.assoc, structureSharpSet_comp_ranIso, structureSharpRanSet_id]

/-- **The structure map of an identity is the canonical identification of `𝒪_X` with
`(𝟙 X)_*𝒪_X`**, on underlying sheaves of sets. -/
theorem structureSharpSet_id (X : AlgebraicSpaces B S hS) :
    structureSharpSet B S hS (𝟙 X) =
      (smallEtaleDirectImageIdIso B S hS X).inv.app (structureSetSheaf B S hS X) :=
  (Iso.comp_hom_eq_id
    ((smallEtaleDirectImageIdIso B S hS X).app (structureSetSheaf B S hS X))).mp
    (structureSharpSet_comp_idIso B S hS X)

/-- **The structure map `(𝟙 X)♯ : 𝒪_X ⟶ (𝟙 X)_*𝒪_X` of an identity is invertible.** It is the
canonical identification of the two sheaves of rings; a morphism of sheaves of rings whose
underlying morphism of sheaves of sets is invertible is invertible. -/
instance isIso_structureSharp_id (X : AlgebraicSpaces B S hS) :
    IsIso (structureSharp B S hS (𝟙 X)) := by
  have h : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      (structureSharp B S hS (𝟙 X))) := by
    rw [show (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (structureSharp B S hS (𝟙 X)) =
        (smallEtaleDirectImageIdIso B S hS X).inv.app (structureSetSheaf B S hS X) from
      structureSharpSet_id B S hS X]
    exact ((smallEtaleDirectImageIdIso B S hS X).app
      (structureSetSheaf B S hS X)).isIso_inv
  exact isIso_of_reflects_iso (structureSharp B S hS (𝟙 X))
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u}))

/-! ### The unit law -/

/-- **The unit law of Stacks 03LU for the direct image**: the direct image of `𝒪`-modules along
an identity morphism of algebraic spaces is the identity functor.

The direct image of sheaves of sets along an identity is the identity functor, and the structure
map of the identity is the corresponding identification of the structure sheaves
(`AlgebraicGeometry.Space.structureSharpSet_id`), which is exactly the input
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoId` asks for.

This is the datum that the `idIso` field of
`AlgebraicGeometry.Space.ModulePushforwardCoherence` assumes. -/
@[stacks 03LU "the unit law for the direct image"]
def modulePushforwardIdIso (X : AlgebraicSpaces B S hS) :
    modulePushforward B S hS (𝟙 X) ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  eqToIso (pushforwardModules_eq_modulePushforward B S hS (𝟙 X)).symm ≪≫
    (RingedToposHom.pushforwardModulesIsoId (smallEtaleRingedToposHom B S hS (𝟙 X))
      (smallEtaleDirectImageIdIso B S hS X).symm
      ((forgetRing_map_fSharp B S hS (𝟙 X)).trans (structureSharpSet_id B S hS X))).symm

/-- **The unit law of Stacks 03LU**: the inverse image of `𝒪`-modules along an identity morphism
of algebraic spaces is the identity functor.

The inverse image is a left adjoint of the direct image by
`AlgebraicGeometry.Space.modulePullbackAdjunction`, the direct image along an identity is the
identity functor by `AlgebraicGeometry.Space.modulePushforwardIdIso`, and a left adjoint of the
identity functor is the identity functor. -/
@[stacks 03LU
  "the unit law: the inverse image of modules along an identity is the identity functor"]
def modulePullbackIdIso (X : AlgebraicSpaces B S hS) :
    modulePullback B S hS (𝟙 X) ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  Adjunction.leftAdjointIdIso (modulePullbackAdjunction B S hS (𝟙 X))
    (modulePushforwardIdIso B S hS X)

/-- The inverse image of `𝒪`-modules along an identity morphism of algebraic spaces is an
equivalence, being isomorphic to the identity functor. -/
instance isEquivalence_modulePullback_id (X : AlgebraicSpaces B S hS) :
    (modulePullback B S hS (𝟙 X)).IsEquivalence :=
  Functor.isEquivalence_of_iso (modulePullbackIdIso B S hS X).symm

/-- **The inverse image of `𝒪`-modules along an identity morphism of algebraic spaces reflects
isomorphisms.** This is the form in which the unit law is used: a morphism of `𝒪_X`-modules
whose inverse image along `𝟙 X` is invertible is itself invertible. -/
instance reflectsIsomorphisms_modulePullback_id (X : AlgebraicSpaces B S hS) :
    (modulePullback B S hS (𝟙 X)).ReflectsIsomorphisms :=
  inferInstance

end AlgebraicGeometry.Space

end
