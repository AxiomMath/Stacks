module

public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageThickeningRemark
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentPullbackMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryExtOne
public import StacksFrontier.Topology.Sheaves.Functors.Module.HomSheaf
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# The classes of the two extensions of Stacks 0GQ2

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces and
`0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` an extension of `g⁻¹f⁻¹𝒪_S`-algebras with square-zero ideal, with
class `ζ ∈ Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢)` (**Stacks 0GPZ**). **Stacks 0GQ2** observes that the class
of the pullback `𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g⁻¹𝒪_X`, an extension of `g⁻¹𝒪_X` by `𝒢` over the ringed
space `(Y, g⁻¹𝒪_X)` (`inverseImageRingedSpace g`), is the image of `ζ` under the canonical map
`Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢) ⟶ Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`.

That map (`inverseImageExtMap`) restricts scalars along `g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` (the exact functor
`ι_*` for the morphism `ι : (Y, 𝒪_Y) ⟶ (Y, g⁻¹𝒪_X)` of ringed spaces, `inverseImageLift g`) and
precomposes with the canonical map `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} ⟶ ι_*𝖭𝖫_{Y/S}` of naive cotangent
complexes (`inverseImageNaiveCotangentMap`).

## Main results

* `extClass_inverseImagePullback`: the class of `𝒪'₂` is the image of the class of `𝒪_{Y'}`.
* `isomorphismClassesEquivExt_inverseImagePullback`: the same, in terms of the bijections of
  **Stacks 0GPZ**.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sites.SqZeroPullback
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (f : X ⟶ S) (g : Y ⟶ X)

/-- The morphism of ringed spaces `ι : (Y, 𝒪_Y) ⟶ (Y, g⁻¹𝒪_X)`: the identity of `Y` with
`g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`. -/
def inverseImageLift : Y ⟶ inverseImageRingedSpace g :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (ringedSpaceStructureMap g).hom }

/-- The ring map `g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`, forgetting commutativity. -/
abbrev inverseImageComorphismRing :
    structureSheafRing (inverseImageRingedSpace g) ⟶ structureSheafRing Y :=
  (sheafCompose (Opens.grothendieckTopology Y.carrier) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (ringedSpaceStructureMap g)

/-- `ι_*` is restriction of scalars along `g^♯`. -/
def modulePushforwardInverseImageLiftIso :
    modulePushforward (inverseImageLift g) ≅
      SheafOfModules.restrictScalars.{u} (inverseImageComorphismRing g) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

/-- `ι_*` preserves finite colimits. -/
instance : PreservesFiniteColimits (modulePushforward (inverseImageLift g)) :=
  letI : (SheafOfModules.restrictScalars.{u} (inverseImageComorphismRing g)).IsLeftAdjoint :=
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction
      (inverseImageComorphismRing g)).isLeftAdjoint
  preservesFiniteColimits_of_natIso (modulePushforwardInverseImageLiftIso g).symm

/-- `ι_*` preserves finite limits. -/
instance : PreservesFiniteLimits (modulePushforward (inverseImageLift g)) :=
  letI := (modulePullbackPushforwardAdjunction (inverseImageLift g)).rightAdjoint_preservesLimits
  inferInstance

/-- `ρ`: the identity of `g⁻¹f⁻¹𝒪_S`, read as a map into its pushforward along `ι`. -/
abbrev inverseImageBaseRingId : inverseImageBaseRing (inverseImageSpaceHom f g) ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageLift g).hom.base).obj
      (inverseImageBaseRing (g ≫ f)) :=
  ObjectProperty.homMk (𝟙 _)

/-- `b`: `g^♯ : g⁻¹𝒪_X ⟶ ι_*𝒪_Y`, the comorphism of `ι`. -/
abbrev inverseImageComorphismPush : (inverseImageRingedSpace g).sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageLift g).hom.base).obj Y.sheaf :=
  ObjectProperty.homMk (inverseImageLift g).hom.c

/-- The structure map of `g⁻¹𝒪_X` over `g⁻¹f⁻¹𝒪_S` followed by `g^♯` is the identity of
`g⁻¹f⁻¹𝒪_S` followed by the pushforward of the structure map of `𝒪_Y` over `g⁻¹f⁻¹𝒪_S`. -/
theorem structureRingMap_comp_inverseImageComorphismPush :
    structureRingMap (inverseImageSpaceHom f g) ≫ inverseImageComorphismPush g =
      inverseImageBaseRingId f g ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageLift g).hom.base).map
          (structureRingMap (g ≫ f)) := by
  apply Sheaf.hom_ext
  exact congrArg (fun t => t.hom) (ringedSpaceStructureMap_comp_eq f g).symm

/-- The canonical map `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} ⟶ ι_*𝖭𝖫_{Y/S}` of naive cotangent complexes along
`ι : (Y, 𝒪_Y) ⟶ (Y, g⁻¹𝒪_X)`: the map of canonical presentations given by `g^♯` on variables and
the identity of `g⁻¹f⁻¹𝒪_S` on coefficients. -/
def inverseImageNaiveCotangentMap :=
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
    (structureRingMap (inverseImageSpaceHom f g))
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f))
    Y.sheaf (structureRingMap (g ≫ f))
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap (inverseImageLift g).hom.base
    (E₁ := Stacks.Sites.FreeAlgebra.underlyingPresheaf
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf)
    (α₁ := 𝟙 _)
    (E₂ := Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
      Y.sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_inverseImageComorphismPush f g) (ε := Functor.whiskerRight
      (inverseImageComorphismPush g).hom (forget CommRingCat.{u})) rfl

/-- `ι_*`, restriction of scalars along `g^♯`, in the spelling of the push maps. -/
abbrev inverseImageRestriction :
    SheafOfModules.{u} (structureSheafRing Y) ⥤ SheafOfModules.{u} (structureSheafRing
      (inverseImageRingedSpace g)) :=
  SheafOfModules.pushforward
    (Stacks.Sites.Conormal.pushforwardRingHom (inverseImageLift g).hom.base
      (inverseImageComorphismPush g))

/-- `inverseImageRestriction g` is `ι_*`. -/
theorem inverseImageRestriction_eq :
    inverseImageRestriction g = modulePushforward (inverseImageLift g) :=
  rfl

/-- Restriction of scalars along `g^♯` preserves finite limits. -/
instance : PreservesFiniteLimits (inverseImageRestriction g) :=
  inferInstanceAs (PreservesFiniteLimits (modulePushforward (inverseImageLift g)))

/-- Restriction of scalars along `g^♯` preserves finite colimits. -/
instance : PreservesFiniteColimits (inverseImageRestriction g) :=
  inferInstanceAs (PreservesFiniteColimits (modulePushforward (inverseImageLift g)))

/-- Restriction of scalars along `g^♯` is additive. -/
instance : (inverseImageRestriction g).Additive :=
  inferInstanceAs (modulePushforward (inverseImageLift g)).Additive

attribute [local instance 10000] HasDerivedCategory.standard

variable {f g} in
/-- **The image of `ζ`**: the map
`Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢) ⟶ Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`: restrict scalars along
`g^♯` and precompose with the canonical map of naive cotangent complexes. -/
def inverseImageExtMap {G : SheafOfModules.{u} (structureSheafRing Y)}
    (z : extOneNaiveCotangent (g ≫ f) G) :
    extOneNaiveCotangent (inverseImageSpaceHom f g) (restrictedModule g G) :=
  DerivedCategory.Q.map (inverseImageNaiveCotangentMap f g) ≫
    (inverseImageRestriction g).mapExtOne z

section PullbackClass

variable {f g} {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)}
  (Q : SquareZeroAlgebraExtension (g ≫ f) G)

/-- The first projection `𝒪'₂ ⟶ 𝒪_{Y'}`, as a map into the pushforward along `ι`. -/
abbrev pullbackFstPush : (inverseImagePullback Q).sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageLift g).hom.base).obj Q.sheaf :=
  ObjectProperty.homMk (fibreFst Q.reduction (inverseImageComorphism (Y := Y) (g := g))).hom

/-- The presentation of `𝒪'₂` by its own underlying sheaf of sets maps to that of `𝒪_{Y'}`
along the first projection `𝒪'₂ ⟶ 𝒪_{Y'}`: compatibility with the generators. -/
theorem pullbackGenerators_comm :
    Functor.whiskerRight (pullbackFstPush Q).hom (forget CommRingCat.{u}) ≫
        Functor.whiskerLeft (Opens.map (inverseImageLift g).hom.base).op Q.generatorsMap =
      (inverseImagePullback Q).generatorsMap ≫
        Functor.whiskerRight (inverseImageComorphismPush g).hom (forget CommRingCat.{u}) := by
  refine NatTrans.ext (funext fun U => ?_)
  ext x
  exact fibreVal_mem Q.reduction _ U x

/-- The chain map `𝖭𝖫(α₂) ⟶ ι_*𝖭𝖫(β)` from the presentation of `𝒪'₂` by its own sections to
that of `𝒪_{Y'}`, along the first projection `𝒪'₂ ⟶ 𝒪_{Y'}`: the map of the source induced by
`φ`. -/
def pullbackPresentationMap :=
  letI := (inverseImagePullback Q).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  letI := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap (inverseImageLift g).hom.base
    (E₁ := (inverseImagePullback Q).generators) (α₁ := (inverseImagePullback Q).generatorsMap)
    (E₂ := Q.generators) (α₂ := Q.generatorsMap)
    (structureRingMap_comp_inverseImageComorphismPush f g) (pullbackGenerators_comm Q)

/-- The comparison `𝖭𝖫(β) ⟶ 𝖭𝖫_{Y/S}` of Stacks 08TL for the presentation of `𝒪_Y` by the
sections of `𝒪_{Y'}`. -/
abbrev extensionPresentationComparison :=
  letI := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap

/-- The comparison `𝖭𝖫(α₂) ⟶ 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` of Stacks 08TL for the presentation of
`g⁻¹𝒪_X` by the sections of `𝒪'₂`. -/
abbrev pullbackPresentationComparison :=
  letI := (inverseImagePullback Q).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
    (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePullback Q).generators
    (inverseImagePullback Q).generatorsMap

/-- `pullbackPresentationComparison Q` followed by `inverseImageNaiveCotangentMap f g` equals
`pullbackPresentationMap Q` followed by `ι_*` of `extensionPresentationComparison Q`. -/
theorem pullbackPresentationComparison_comp :
    pullbackPresentationComparison Q ≫ inverseImageNaiveCotangentMap f g =
      pullbackPresentationMap Q ≫ ((inverseImageRestriction g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (extensionPresentationComparison Q) :=
  let := (inverseImagePullback Q).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  let := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
    (structureRingMap (inverseImageSpaceHom f g))
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f))
    Y.sheaf (structureRingMap (g ≫ f))
  (Stacks.SheafOfModules.presentationNaiveCotangentPushMap_naturality
      (inverseImageLift g).hom.base
      (α₁' := 𝟙 _) (α₂' := 𝟙 _)
      (inverseImagePullback Q).generatorsMap Q.generatorsMap (pullbackGenerators_comm Q)
      (Category.comp_id _) (Category.comp_id _)
      (structureRingMap_comp_inverseImageComorphismPush f g)
      (pullbackGenerators_comm Q) rfl).symm

/-- On the ideal, the first projection `𝒪'₂ ⟶ 𝒪_{Y'}` is the identity of `𝒢`. -/
theorem inverseImagePullback_ideal_fibreFst (U : (Opens Y.carrier)ᵒᵖ)
    (z : kernelIdeal (fibreSnd Q.reduction (inverseImageComorphism (Y := Y) (g := g))).hom U) :
    Q.ideal.app U ⟨((fibreFst Q.reduction (inverseImageComorphism (Y := Y) (g := g))).hom.app
        U).hom z.1, ((fibreSnd_app_eq_zero_iff _ _ U z.1).1 z.2).1⟩ =
      (inverseImagePullback Q).ideal.app U z := by
  obtain ⟨n, rfl⟩ := (pullbackIdealEquivOf (T := inverseImageRingedSpace g)
    (G := restrictedModule g G) Q.reduction (inverseImageComorphism (Y := Y) (g := g))
    (idealInclusion Q) U).surjective z
  change _ = (pullbackIdealEquivOf (T := inverseImageRingedSpace g) (G := restrictedModule g G)
    Q.reduction (inverseImageComorphism (Y := Y) (g := g)) (idealInclusion Q) U).symm _
  rw [AddEquiv.symm_apply_apply]
  exact Q.ideal_incl U n

/-- The polynomial presentation of `𝒪'₂` maps to that of `𝒪_{Y'}` compatibly with the lifts:
`α'` for `𝒪'₂` followed by the first projection is `α'` for `𝒪_{Y'}` after the map of
presentations. -/
theorem pullbackFreeAlgebraPushMap_comp_lift :
    Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageLift g).hom.base
        (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImagePullback Q).generators
        (inverseImageBaseRing (g ≫ f)) Q.generators (inverseImageBaseRingId f g)
        (Functor.whiskerRight (pullbackFstPush Q).hom (forget CommRingCat.{u})) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageLift g).hom.base).map Q.lift =
      (inverseImagePullback Q).lift ≫ pullbackFstPush Q := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · have e1 := Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap
      (inverseImageLift g).hom.base (inverseImageBaseRing (inverseImageSpaceHom f g))
      (inverseImagePullback Q).generators (inverseImageBaseRing (g ≫ f)) Q.generators
      (inverseImageBaseRingId f g)
      (Functor.whiskerRight (pullbackFstPush Q).hom (forget CommRingCat.{u}))
    have e2 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.sheaf Q.generators
      Q.base (𝟙 _)
    have e3 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (inverseImageSpaceHom f g))
      (inverseImagePullback Q).sheaf (inverseImagePullback Q).generators
      (inverseImagePullback Q).base (𝟙 _)
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (inverseImageLift g).hom.base).map Q.lift) e1).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (inverseImageBaseRingId f g ≫ ·) ((Functor.map_comp _ _ _).symm.trans
      (congrArg _ e2))).trans ?_
    refine Eq.trans ?_
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullbackFstPush Q) e3)).symm
    apply Sheaf.hom_ext
    exact (congrArg (fun t => t.hom) (fibreLift_comp_fst (K := Opens.grothendieckTopology Y.carrier)
      Q.reduction (inverseImageComorphism (Y := Y) (g := g)) Q.base (baseToMid f g)
      (base_comp_reduction_eq Q))).symm
  · have hv1 := Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap
      (inverseImageLift g).hom.base (inverseImageBaseRing (inverseImageSpaceHom f g))
      (inverseImagePullback Q).generators (inverseImageBaseRing (g ≫ f)) Q.generators
      (inverseImageBaseRingId f g)
      (Functor.whiskerRight (pullbackFstPush Q).hom (forget CommRingCat.{u}))
    have hv2 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.sheaf Q.generators
      Q.base (𝟙 _)
    have hv3 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (inverseImageSpaceHom f g))
      (inverseImagePullback Q).sheaf (inverseImagePullback Q).generators
      (inverseImagePullback Q).base (𝟙 _)
    refine NatTrans.ext (funext fun U => ?_)
    ext x
    have a1 := congrArg (fun t => t x) (NatTrans.congr_app hv1 U)
    have a2 := congrArg (fun t => t ((fibreFst Q.reduction
      (inverseImageComorphism (Y := Y) (g := g))).hom.app U x)) (NatTrans.congr_app hv2 U)
    have a3 := congrArg (fun t => t x) (NatTrans.congr_app hv3 U)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, types_comp_apply, NatTrans.id_app,
      types_id_apply] at a1 a2 a3
    exact (congrArg (Q.lift.hom.app U).hom a1).trans (a2.trans
      (congrArg ((fibreFst Q.reduction (inverseImageComorphism (Y := Y) (g := g))).hom.app U).hom
        a3).symm)

/-- The conormal homomorphism `𝒦/𝒦² ⟶ 𝒢` of `𝒪_{Y'}`, typed on the conormal sequence. -/
abbrev extensionPresentationConormal :
    (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
      (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap).X₁ ⟶ G :=
  Stacks.Sites.Conormal.conormalDesc.{u, u, u, u} _ G
    Q.toAlgebraSquareZeroExtension.idealRestriction

/-- The conormal homomorphism `𝒥/𝒥² ⟶ 𝒢` of `𝒪'₂`, typed on the conormal sequence. -/
abbrev pullbackPresentationConormal :
    letI := (inverseImagePullback Q).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
    (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
      (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePullback Q).generators
      (inverseImagePullback Q).generatorsMap).X₁ ⟶ restrictedModule g G :=
  Stacks.Sites.Conormal.conormalDesc.{u, u, u, u} _ (restrictedModule g G)
    (inverseImagePullback Q).toAlgebraSquareZeroExtension.idealRestriction

/-- The map `φ̄ : 𝒥/𝒥² ⟶ ι_*(𝒦/𝒦²)` of conormal sheaves along the first projection. -/
abbrev pullbackConormalMap :=
  letI := (inverseImagePullback Q).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  letI := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.presentationConormalPushMap (inverseImageLift g).hom.base
    (E₁ := (inverseImagePullback Q).generators) (α₁ := (inverseImagePullback Q).generatorsMap)
    (E₂ := Q.generators) (α₂ := Q.generatorsMap)
    (structureRingMap_comp_inverseImageComorphismPush f g) (pullbackGenerators_comm Q)

/-- The degree `-1` component of `pullbackPresentationMap`. -/
theorem pullbackPresentationMap_f_negOne :
    letI := (inverseImagePullback Q).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
    letI := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
    (pullbackPresentationMap Q).f (-1) =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
          (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePullback Q).generators
          (inverseImagePullback Q).generatorsMap) ≫
        pullbackConormalMap Q ≫
        (inverseImageRestriction g).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
            (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap).symm) :=
  let := (inverseImagePullback Q).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  let := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne (inverseImageLift g).hom.base
    (E₁ := (inverseImagePullback Q).generators) (α₁ := (inverseImagePullback Q).generatorsMap)
    (E₂ := Q.generators) (α₂ := Q.generatorsMap)
    (structureRingMap_comp_inverseImageComorphismPush f g) (pullbackGenerators_comm Q)

/-- **The conormal homomorphism of `𝒪'₂` is that of `𝒪_{Y'}` composed with the map of conormal
sheaves `φ̄ : 𝒥/𝒥² ⟶ 𝒦/𝒦²`** of the presentations along the first projection: the last step of
the proof of Stacks 0GQ2. -/
theorem pullbackConormalMap_comp :
    pullbackConormalMap Q ≫ (inverseImageRestriction g).map (extensionPresentationConormal Q) =
      pullbackPresentationConormal Q := by
  refine Stacks.Sites.Conormal.conormal_hom_ext.{u, u, u, u} _ _ (fun U x => ?_)
  change ((inverseImageRestriction g).map (extensionPresentationConormal Q)).val.app U
    ((pullbackConormalMap Q).val.app U _) = _
  let ψ := Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageLift g).hom.base
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImagePullback Q).generators
    (inverseImageBaseRing (g ≫ f)) Q.generators (inverseImageBaseRingId f g)
    (Functor.whiskerRight (pullbackFstPush Q).hom (forget CommRingCat.{u}))
  have h1 := Stacks.Sites.Conormal.conormalSheafMapPush_toAssociatedModule
    (inverseImageLift g).hom.base (inverseImageRingedSpace g).sheaf Y.sheaf
    (inverseImageComorphismPush g) (inverseImagePullback Q).presentation Q.presentation ψ
    (Stacks.SheafOfModules.freeAlgebraPushMap_comp_presentation (inverseImageLift g).hom.base
      (structureRingMap_comp_inverseImageComorphismPush f g) (pullbackGenerators_comm Q)) U
    ((kernelIdeal (inverseImagePullback Q).presentation.hom U).toCotangent x)
  refine (congrArg (((inverseImageRestriction g).map
    (extensionPresentationConormal Q)).val.app U).hom h1).trans ?_
  have hψ := Stacks.Sites.Conormal.kernelIdeal_le_comap_sectionsMapPush
    (inverseImageLift g).hom.base (inverseImageRingedSpace g).sheaf Y.sheaf
    (inverseImageComorphismPush g) (inverseImagePullback Q).presentation Q.presentation ψ
    (Stacks.SheafOfModules.freeAlgebraPushMap_comp_presentation (inverseImageLift g).hom.base
      (structureRingMap_comp_inverseImageComorphismPush f g) (pullbackGenerators_comm Q)) U x.2
  have h2 := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule Q.presentation G
    Q.toAlgebraSquareZeroExtension.idealRestriction
    ((Opens.map (inverseImageLift g).hom.base).op.obj U) ⟨_, hψ⟩
  have h3 := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule
    (inverseImagePullback Q).presentation (restrictedModule g G)
    (inverseImagePullback Q).toAlgebraSquareZeroExtension.idealRestriction U x
  refine h2.trans (Eq.trans ?_ h3.symm)
  have h4 := congrArg (fun t => (t.hom.app U).hom x.1) (pullbackFreeAlgebraPushMap_comp_lift Q)
  exact (congrArg (Q.ideal.app _) (Subtype.ext h4)).trans (inverseImagePullback_ideal_fibreFst Q U
    ⟨_, (inverseImagePullback Q).toAlgebraSquareZeroExtension.lift_mem_kernelIdeal U x⟩)

end PullbackClass

end AlgebraicGeometry.RingedSpaceThickening

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} {g : Y ⟶ X}

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The class of `𝒪'₂` is the image of `ζ`.** The class of the pullback
`𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g⁻¹𝒪_X` of an extension `𝒪_{Y'}` of `𝒪_Y` by `𝒢` along `g^♯` is the image of
the class of `𝒪_{Y'}` under `inverseImageExtMap`. -/
theorem extClass_inverseImagePullback
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)}
    (Q : SquareZeroAlgebraExtension (g ≫ f) G) :
    (inverseImagePullback Q).extClass = inverseImageExtMap Q.extClass :=
  (Functor.Q_map_comp_mapExtOne_conormalExtClass (inverseImageRestriction g) _ _
    (extensionPresentationComparison Q) (pullbackPresentationComparison Q)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison _ _ _ _ _))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison _ _ _ _ _))
    (pullbackPresentationMap Q) (inverseImageNaiveCotangentMap f g)
    (pullbackPresentationComparison_comp Q)
    (extensionPresentationConormal Q) (pullbackPresentationConormal Q)
    (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
      (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap) _
    ((congrArg (· ≫ _) (pullbackPresentationMap_f_negOne Q)).trans
      (Functor.eqToHom_comp_comp_map_eqToHom_comp_map _ _ _ _ _ _ _
        (pullbackConormalMap_comp Q)))).symm

/-- **The class of `𝒪'₂`.** The class, under the bijection of **Stacks 0GPZ** for the ringed
space `(Y, g⁻¹𝒪_X)` over `S`, of the pullback `𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g⁻¹𝒪_X` is the image of the
class `ζ` of `𝒪_{Y'}` (under the bijection of **Stacks 0GPZ** for `Y` over `S`) by the canonical
map `Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢) ⟶ Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`. -/
@[stacks 0GQ2]
theorem isomorphismClassesEquivExt_inverseImagePullback
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)}
    (Q : SquareZeroAlgebraExtension (g ≫ f) G) :
    SquareZeroAlgebraExtension.isomorphismClassesEquivExt (inverseImageSpaceHom f g)
        (restrictedModule g G) (Quotient.mk _ (inverseImagePullback Q)) =
      inverseImageExtMap
        (SquareZeroAlgebraExtension.isomorphismClassesEquivExt (g ≫ f) G (Quotient.mk _ Q)) :=
  extClass_inverseImagePullback Q

end AlgebraicGeometry.RingedSpaceThickening
