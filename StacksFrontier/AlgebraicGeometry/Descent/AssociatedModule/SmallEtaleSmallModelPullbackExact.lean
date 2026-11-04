module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePullbackExact
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral

/-!
# Stacks 08H8 for `ε` read on the `Type u`-presented model

Let `S` be a scheme and let `ε : S_étale ⟶ S_Zar` be the comparison morphism of ringed topoi of
Stacks 08H7.  Stacks 08H8 asserts that the pullback `ε^*` of sheaves of modules is exact and
that it detects the zero sheaf.  Both are proved on the *small étale site* —
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule` and
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback` — and this module
carries them across to `AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom`, which is `ε` read
on the `Type u`-presented model of the small étale ringed topos, and to its
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`.  That is the shape in which the
Stacks 06YY / 08H5 chain, and so the converse direction of Stacks 08HF, consumes them.

The transport is a single factorization, and nothing in it is new mathematics:

`ε_model^* ≅ ε^* ⋙ (transport to the model)`,

the second factor being an *equivalence* of categories of sheaves of modules.

## Main definitions

* `Stacks.SheafOfModules.SiteEquivalence.restrictEquivalence`: restriction of sheaves of modules
  along an equivalence of sites is an equivalence of categories.
* `AlgebraicGeometry.SmallEtale.modelModulesEquiv`: that equivalence for the comparison of the
  small étale site with its model, `Mod(𝒪) ≌ Mod(𝒪_model)`.
* `AlgebraicGeometry.SmallEtale.assocIso`: `ε^*` as the pullback of the modules development is
  the associated-module functor of Stacks 03DU (4).
* `AlgebraicGeometry.SmallEtale.pushCompIso`: `ε_model_*` is transport to the small étale site
  followed by `ε_*`.
* `AlgebraicGeometry.SmallEtale.pullbackToposIsoAssociatedModel`: **the factorization**
  `ε_model^* ≅ ε^* ⋙ (transport to the model)`.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`: the zero-detection
  assertion of Stacks 08H8 at the associated-module spelling of `ε^*`.
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullbackTopos_toZariskiSmallModelHom`:
  **the exactness assertion of Stacks 08H8 for `ε` read on the model**, left exactness.
* `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_pullbackTopos_toZariskiSmallModelHom`:
  right exactness, which needs nothing — `ε_model^*` is a left adjoint.
* `AlgebraicGeometry.SmallEtale.isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom`:
  **the zero-detection assertion of Stacks 08H8 for `ε` read on the model.**

## Implementation notes

**The factorization is obtained from the direct images, not the inverse images.**  The pullback
of sheaves of modules is an abstract left adjoint, so there is nothing to compare on it
directly; what is compared is the *pushforward*, where everything is restriction of sections.
`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom` is by definition
`(toZariskiRingedToposHom).comp (toEtaleHom)`, so `CategoryTheory.SheafOfModules.pushforwardComp`
splits `ε_model_*` as `(toEtaleHom)_* ⋙ ε_*` with no hypothesis at all; `(toEtaleHom)_*` is the
inverse of `modelModulesEquiv`; and `ε_*` has `ε^*` as a left adjoint at the independent
universes the small étale site needs
(`AlgebraicGeometry.RingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral`, identified
with the associated-module functor by
`AlgebraicGeometry.SmallEtale.pullbackToposGeneral_toZariskiRingedToposHom`).  Uniqueness of
left adjoints does the rest.

**Why `restrictEquivalence` is stated for a bare equivalence of sites.**  Mathlib's
`CategoryTheory.SheafOfModules.pushforwardPushforwardEquivalence` asks for two structure maps and
two compatibilities; for restriction along an equivalence the structure map in one direction is
the identity and in the other the counit, and then both compatibilities are the triangle
identities.  Stated at a variable equivalence, the two proofs are three lines; stated at the
comparison of the small étale site with its model they are not, because the projections of the
two ringed topoi do not reduce at the transparency `simp` and `rw` work at.  The hypotheses are
discharged at the comparison by `rfl`, which is what
`AlgebraicGeometry.SmallEtale.modelModulesEquiv_functor` and `modelModulesEquiv_inverse` record.

**The two continuity instances are restated.**  `CategoryTheory.Functor.IsContinuous` of the
comparison is demanded at the `(ringedTopos B S hS).J`, `(smallModelRingedTopos B S hS).J` and
`(smallModelEquiv B S hS).symm.functor` spellings, none of which reduces at instance
transparency; the four `instance`s below are those restatements and nothing more.

**No `@[stacks 08H8]` attribute is claimed.**  The tag's four assertions are registered on the
small étale site, at
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`,
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule`,
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback` and
`AlgebraicGeometry.SmallEtale.isRightAdjoint_toZariskiModulePushforward`; what is here is their
transport to a second presentation of the same morphism, so a tag would double-count.

## References

* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules.SiteEquivalence

universe v w u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
  (R : Sheaf K RingCat.{w})

/-- **Restriction of sheaves of modules along an equivalence of sites is an equivalence.**  For
`e : C ≌ D` continuous in both directions and a sheaf of rings `R` on `D`, restriction along
`e.functor` carries `Mod(R)` to `Mod(R|_C)` and is an equivalence, the inverse being restriction
back along `e.inverse` with the counit of `e` for its structure map.

The two compatibility conditions of
`CategoryTheory.SheafOfModules.pushforwardPushforwardEquivalence` are the two triangle
identities of `e`. -/
public def restrictEquivalence :
    _root_.SheafOfModules.{v} R ≌
      _root_.SheafOfModules.{v} ((e.functor.sheafPushforwardContinuous RingCat.{w} J K).obj R) := by
  refine _root_.SheafOfModules.pushforwardPushforwardEquivalence e (𝟙 _)
    ⟨Functor.whiskerRight (NatTrans.op e.counit) R.obj⟩ ?_ ?_
  · change _ = _ ≫ 𝟙 _
    exact (Category.comp_id _).symm
  · apply NatTrans.ext
    funext U
    change 𝟙 _ ≫ R.obj.map (e.counit.app (e.functor.obj U.unop)).op ≫
      R.obj.map (e.functor.map (e.unit.app U.unop)).op = 𝟙 _
    rw [Category.id_comp, ← Functor.map_comp, ← op_comp]
    change R.obj.map (e.functor.map (e.unitIso.hom.app U.unop) ≫
      e.counitIso.hom.app (e.functor.obj U.unop)).op = 𝟙 _
    exact (congrArg (fun a : e.functor.obj U.unop ⟶ e.functor.obj U.unop =>
      R.obj.map a.op) (e.functor_unitIso_comp U.unop)).trans (R.obj.map_id _)

end Stacks.SheafOfModules.SiteEquivalence

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of the small étale site with its model, on sheaves of modules -/

/-- The comparison of sites is continuous for the two topologies read through the ringed
topoi. -/
public instance isContinuous_smallModelEquiv_functor_ringedTopos :
    (smallModelEquiv B S hS).functor.IsContinuous
      (ringedTopos B S hS).J (smallModelRingedTopos B S hS).J :=
  inferInstanceAs ((smallModelEquiv B S hS).functor.IsContinuous
    (topology B S hS) (smallModelTopology B S hS))

/-- The comparison of sites, read backwards, is continuous for the two topologies read through
the ringed topoi. -/
public instance isContinuous_smallModelEquiv_inverse_ringedTopos :
    (smallModelEquiv B S hS).inverse.IsContinuous
      (smallModelRingedTopos B S hS).J (ringedTopos B S hS).J :=
  inferInstanceAs ((smallModelEquiv B S hS).inverse.IsContinuous
    (smallModelTopology B S hS) (topology B S hS))

/-- Continuity of the comparison at the `symm` spelling, which
`Stacks.SheafOfModules.SiteEquivalence.restrictEquivalence` demands. -/
public instance isContinuous_smallModelEquiv_symm_functor :
    (smallModelEquiv B S hS).symm.functor.IsContinuous
      (smallModelRingedTopos B S hS).J (ringedTopos B S hS).J :=
  isContinuous_smallModelEquiv_inverse_ringedTopos B S hS

/-- Continuity of the comparison, read backwards, at the `symm` spelling. -/
public instance isContinuous_smallModelEquiv_symm_inverse :
    (smallModelEquiv B S hS).symm.inverse.IsContinuous
      (ringedTopos B S hS).J (smallModelRingedTopos B S hS).J :=
  isContinuous_smallModelEquiv_functor_ringedTopos B S hS

/-- **Transport of sheaves of modules to the model is an equivalence** `Mod(𝒪) ≌ Mod(𝒪_model)`.
Its functor is the pushforward along `AlgebraicGeometry.SmallEtale.fromEtaleHom` — restriction of
sections to the model — and its inverse the pushforward along
`AlgebraicGeometry.SmallEtale.toEtaleHom`. -/
public def modelModulesEquiv :
    _root_.SheafOfModules.{u} (structureSheaf B S hS) ≌
      _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelRingedTopos B S hS).O) :=
  Stacks.SheafOfModules.SiteEquivalence.restrictEquivalence (smallModelEquiv B S hS).symm
    (smallModelRingedTopos B S hS).J (ringedTopos B S hS).J
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos B S hS).O)

/-- The functor of `AlgebraicGeometry.SmallEtale.modelModulesEquiv` is the pushforward of sheaves
of modules along `AlgebraicGeometry.SmallEtale.fromEtaleHom`, whose structure map is the
identity. -/
@[simp]
public theorem modelModulesEquiv_functor :
    (modelModulesEquiv B S hS).functor = (fromEtaleHom B S hS).pushforwardTopos := rfl

/-- The inverse of `AlgebraicGeometry.SmallEtale.modelModulesEquiv` is the pushforward of sheaves
of modules along `AlgebraicGeometry.SmallEtale.toEtaleHom`. -/
@[simp]
public theorem modelModulesEquiv_inverse :
    (modelModulesEquiv B S hS).inverse = (toEtaleHom B S hS).pushforwardTopos := rfl

/-! ### `ε^*` on the small étale site, at the two spellings -/

/-- **`ε^*` of the modules development is the associated-module functor.**  Both are left
adjoints of the direct image along `ε`; this is
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` read at `ε`, exactly as
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule` reads it. -/
public def assocIso : toZariskiModulePullback B S hS ≅ associatedModule B S hS :=
  RingedSite.HomGeneral.pullbackModulesToposIsoGeneral (toZariskiRingedSiteHom B S hS)

/-- **The zero-detection assertion of Stacks 08H8, at the associated-module spelling of `ε^*`.**
If `𝓕^a = 0` then `𝓕 = 0`, for an arbitrary sheaf of `𝒪_S`-modules `𝓕`.

This is
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback` read through
`AlgebraicGeometry.SmallEtale.assocIso`. -/
public theorem isZero_of_isZero_associatedModule_general
    (F : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))
    (h : IsZero ((associatedModule B S hS).obj F)) : IsZero F :=
  isZero_of_isZero_toZariskiModulePullback B S hS F (h.of_iso ((assocIso B S hS).app F))

/-! ### `ε` read on the model -/

/-- **`ε_model_*` is transport to the small étale site followed by `ε_*`.**  `ε_model` is by
definition the composite of `ε` with the comparison of the model, and the pushforward of sheaves
of modules along a composite is the composite of the pushforwards. -/
public def pushCompIso :
    (toEtaleHom B S hS).pushforwardTopos ⋙ (toZariskiRingedToposHom B S hS).pushforwardTopos ≅
      (toZariskiSmallModelHom B S hS).pushforwardTopos :=
  _root_.SheafOfModules.pushforwardComp (toZariskiRingedToposHom B S hS).fSharpRing
    (toEtaleHom B S hS).fSharpRing

/-- **The factorization `ε_model^* ≅ ε^* ⋙ (transport to the model)`.**

`ε_model^*` is left adjoint to `ε_model_*`, which is `(toEtaleHom)_* ⋙ ε_*` by
`AlgebraicGeometry.SmallEtale.pushCompIso`; `ε^*` is left adjoint to `ε_*` and transport to the
model is left adjoint to `(toEtaleHom)_*`, being the inverse of an equivalence.  So the two
composites are left adjoints of isomorphic functors. -/
public def pullbackToposIsoAssociatedModel :
    (toZariskiSmallModelHom B S hS).pullbackTopos ≅
      associatedModule B S hS ⋙ (modelModulesEquiv B S hS).functor :=
  Adjunction.leftAdjointUniq
    ((toZariskiSmallModelHom B S hS).pullbackPushforwardAdjunctionTopos)
    ((((toZariskiRingedToposHom B S hS).pullbackPushforwardAdjunctionToposGeneral).comp
      (modelModulesEquiv B S hS).toAdjunction).ofNatIsoRight (pushCompIso B S hS))

/-- **The exactness assertion of Stacks 08H8 for `ε` read on the model**, left exactness: the
pullback of sheaves of modules along `ε_model` preserves finite limits.

`ε^*` is left exact by `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule` and
transport to the model is an equivalence. -/
public instance preservesFiniteLimits_pullbackTopos_toZariskiSmallModelHom :
    PreservesFiniteLimits (toZariskiSmallModelHom B S hS).pullbackTopos := by
  have h1 : PreservesFiniteLimits (associatedModule B S hS) :=
    preservesFiniteLimits_associatedModule B S hS
  have h2 : PreservesLimitsOfSize.{0, 0} (modelModulesEquiv B S hS).functor :=
    Adjunction.rightAdjoint_preservesLimits (modelModulesEquiv B S hS).symm.toAdjunction
  have h2' : PreservesFiniteLimits (modelModulesEquiv B S hS).functor :=
    @PreservesLimitsOfSize.preservesFiniteLimits _ _ _ _ _ h2
  have hcomp : PreservesFiniteLimits
      (associatedModule B S hS ⋙ (modelModulesEquiv B S hS).functor) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h1 h2'
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (pullbackToposIsoAssociatedModel B S hS).symm hcomp

/-- Right exactness of `ε_model^*`, which needs no input: it is a left adjoint. -/
public instance preservesFiniteColimits_pullbackTopos_toZariskiSmallModelHom :
    PreservesFiniteColimits (toZariskiSmallModelHom B S hS).pullbackTopos :=
  have : PreservesColimitsOfSize.{0, 0} (toZariskiSmallModelHom B S hS).pullbackTopos :=
    Adjunction.leftAdjoint_preservesColimits
      (toZariskiSmallModelHom B S hS).pullbackPushforwardAdjunctionTopos
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **The zero-detection assertion of Stacks 08H8 for `ε` read on the model.**  If the pullback
of a sheaf of `𝒪_S`-modules along `ε_model` vanishes then the sheaf vanishes.

Along the factorization, that pullback is `𝓕^a` transported to the model; transport is an
equivalence, so it reflects the zero object, and `𝓕^a = 0` forces `𝓕 = 0` by
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`. -/
public theorem isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))
    (h : IsZero ((toZariskiSmallModelHom B S hS).pullbackTopos.obj F)) : IsZero F := by
  refine isZero_of_isZero_associatedModule_general B S hS F ?_
  have h' : IsZero ((modelModulesEquiv B S hS).functor.obj
      ((associatedModule B S hS).obj F)) :=
    h.of_iso ((pullbackToposIsoAssociatedModel B S hS).app F).symm
  exact (Functor.map_isZero (modelModulesEquiv B S hS).inverse h').of_iso
    ((modelModulesEquiv B S hS).unitIso.app _)

end AlgebraicGeometry.SmallEtale

end
