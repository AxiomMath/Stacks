module

public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageNaiveCotangentIso
public import StacksFrontier.CategoryTheory.Sites.Modules.CorepresentingConormalSequence

/-!
# The canonical maps of naive cotangent complexes along `g = π ∘ ι`

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces. The
morphism `g` factors as `ι : (Y, 𝒪_Y) ⟶ (Y, g⁻¹𝒪_X)` followed by `π : (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)`
(`inverseImageLift_comp_proj`), and the canonical map `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}` is the canonical map
`𝖭𝖫_{X/S} ⟶ π_*𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` followed by `π_*` of the canonical map
`𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} ⟶ ι_*𝖭𝖫_{Y/S}` (`naiveCotangentPushMap_comp`).

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sites.FreeAlgebra

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (f : X ⟶ S) (g : Y ⟶ X)

/-- **`g` factors as `(Y, 𝒪_Y) ⟶ (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)`**: `g = π ∘ ι`. -/
theorem inverseImageLift_comp_proj : inverseImageLift g ≫ inverseImageProj g = g := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext _ _ (Category.id_comp _) ?_
  refine NatTrans.ext (funext fun U => ?_)
  refine (NatTrans.comp_app _ _ U).trans ?_
  refine (congrArg (_ ≫ ·) ((Functor.whiskerRight_app _ _ U).trans
    ((congrArg Y.presheaf.map (eqToHom_app _ U)).trans (eqToHom_map _ _)))).trans ?_
  refine (Category.comp_id _).trans ?_
  exact (congrArg (fun t => t.app U) (c_eq_unit_comp g)).symm

/-- `π_*ι_*𝒢 = g_*𝒢`: the two pushforwards of an `𝒪_Y`-module along `ι` then `π` and along `g` have
the same sections, and the same `𝒪_X`-module structure since `g^♯ = π^♯ ∘ ι^♯`. -/
def pushforwardLiftProjIso (M : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePushforward (inverseImageProj g)).obj ((modulePushforward (inverseImageLift g)).obj M) ≅
      (modulePushforward g).obj M where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r m =>
    (congrArg (fun (s : (structureSheafRing Y).obj.obj (op ((Opens.map g.hom.base).obj
      U.unop))) => s • (show M.val.obj (op ((Opens.map g.hom.base).obj
      U.unop)) from m)) (c_app_eq g U.unop r)).symm)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r m =>
    (congrArg (fun (s : (structureSheafRing Y).obj.obj (op ((Opens.map g.hom.base).obj
      U.unop))) => s • (show M.val.obj (op ((Opens.map g.hom.base).obj
      U.unop)) from m)) (c_app_eq g U.unop r)))⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- The forward map of `pushforwardLiftProjIso` is the identity on sections. -/
@[simp]
theorem pushforwardLiftProjIso_hom_val_app (M : SheafOfModules.{u} (structureSheafRing Y)) U x :
    ((pushforwardLiftProjIso g M).hom.val.app U) x = x := rfl

/-- The inverse map of `pushforwardLiftProjIso` is the identity on sections. -/
@[simp]
theorem pushforwardLiftProjIso_inv_val_app (M : SheafOfModules.{u} (structureSheafRing Y)) U x :
    ((pushforwardLiftProjIso g M).inv.val.app U) x = x := rfl

/-- `ι_* ⋙ π_* ≅ g_*`, with identity components on sections. -/
def pushforwardLiftProjNatIso :
    modulePushforward (inverseImageLift g) ⋙ modulePushforward (inverseImageProj g) ≅
      modulePushforward g :=
  NatIso.ofComponents (pushforwardLiftProjIso g) (fun _ => by ext; rfl)

/-! ### The maps of canonical presentations compose -/

/-- The map `(g ∘ f)⁻¹𝒪_S[g⁻¹𝒪_X] ⟶ ι_*((g ∘ f)⁻¹𝒪_S[𝒪_Y])` of canonical presentations along
`ι`. -/
abbrev liftPushMap :=
  Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageLift g).hom.base
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf)
    (inverseImageBaseRing (g ≫ f))
    (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)
    (inverseImageBaseRingId f g)
    (Functor.whiskerRight (inverseImageComorphismPush g).hom (forget CommRingCat.{u}))

/-- The map `f⁻¹𝒪_S[𝒪_X] ⟶ g_*((g ∘ f)⁻¹𝒪_S[𝒪_Y])` of canonical presentations along `g`. -/
abbrev structurePushMap :=
  Stacks.SheafOfModules.freeAlgebraPushMap g.hom.base (inverseImageBaseRing f)
    (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    (inverseImageBaseRing (g ≫ f))
    (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)
    (baseRingPushMap g f)
    (Functor.whiskerRight (structureComorphism g).hom (forget CommRingCat.{u}))

/-- The map of base rings along `π` agrees with the one along `g`. -/
theorem baseRingPushMap_proj_eq :
    baseRingPushMap (inverseImageProj g) f = baseRingPushMap g f :=
  rfl

/-- **The map of canonical presentations along `g` is the one along `π` followed by the one
along `ι`.** -/
theorem structurePushMap_eq :
    structurePushMap f g = canonicalPushMap f g ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (liftPushMap f g) := by
  have h1 : _ ≫ structurePushMap f g = _ ≫ _ :=
    Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap _ _ _ _ _ _ _
  have h2 := canonicalPushMap_coefficient f g
  have h3 : _ ≫ liftPushMap f g = _ ≫ _ :=
    Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap _ _ _ _ _ _ _
  refine freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · refine h1.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
      (liftPushMap f g)) h2).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (baseRingPushMap g f ≫ ·) ?_
    exact (congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map h3).symm.trans
      (Functor.map_comp _ _ _)
  · have v1 : _ ≫ Functor.whiskerRight ((sheafToPresheaf _ CommRingCat.{u}).map
        (structurePushMap f g)) (forget CommRingCat.{u}) = _ :=
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap _ _ _ _ _ _ _
    have v2 : _ ≫ Functor.whiskerRight ((sheafToPresheaf _ CommRingCat.{u}).map
        (canonicalPushMap f g)) (forget CommRingCat.{u}) = _ :=
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap _ _ _ _ _ _ _
    have v3 : _ ≫ Functor.whiskerRight ((sheafToPresheaf _ CommRingCat.{u}).map
        (liftPushMap f g)) (forget CommRingCat.{u}) = _ :=
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap _ _ _ _ _ _ _
    refine NatTrans.ext (funext fun U => ?_)
    ext x
    have a1 := congrArg (fun t => t x) (NatTrans.congr_app v1 U)
    have a2 := congrArg (fun t => t x) (NatTrans.congr_app v2 U)
    have a3 := congrArg (fun t => t (((structureComorphism (inverseImageProj g)).hom.app U).hom x))
      (NatTrans.congr_app v3 ((Opens.map g.hom.base).op.obj U))
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, types_comp_apply] at a1 a2 a3
    refine a1.trans (Eq.trans ?_ ((congrArg ((liftPushMap f g).hom.app _).hom a2).trans a3).symm)
    exact congrArg (fun t => ((freeAlgebraSheafVariable (Opens.grothendieckTopology Y.carrier)
      (inverseImageBaseRing (g ≫ f))
      (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)).app _) t)
      (c_app_eq g U.unop x)

/-- The canonical presentation of `𝒪_Y` over `(g ∘ f)⁻¹𝒪_S`. -/
abbrev yCanonicalPresentation :=
  Stacks.SheafOfModules.presentation (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) Y.sheaf (structureRingMap (g ≫ f))
    (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (𝟙 _)

/-- The canonical presentation of `𝒪_Y` over `(g ∘ f)⁻¹𝒪_S` is locally surjective. -/
theorem isLocallySurjective_yCanonicalPresentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      (yCanonicalPresentation f g).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

/-- The canonical presentation of `g⁻¹𝒪_X` over `(g ∘ f)⁻¹𝒪_S`, as a presentation of the
structure sheaf of `(Y, g⁻¹𝒪_X)`. -/
abbrev midCanonicalPresentation :=
  Stacks.SheafOfModules.presentation
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
    (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (𝟙 _)

/-- The canonical presentation of `g⁻¹𝒪_X` over `(g ∘ f)⁻¹𝒪_S` is locally surjective. -/
theorem isLocallySurjective_midCanonicalPresentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (midCanonicalPresentation f g).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

/-- The map of canonical presentations along `ι` is compatible with the presentations and the
comorphism `g⁻¹𝒪_X ⟶ ι_*𝒪_Y`. -/
theorem liftPushMap_comp_presentation :
    liftPushMap f g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageLift g).hom.base).map
        (yCanonicalPresentation f g) =
      midCanonicalPresentation f g ≫ inverseImageComorphismPush g :=
  Stacks.SheafOfModules.freeAlgebraPushMap_comp_presentation (inverseImageLift g).hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_inverseImageComorphismPush f g)
    (ε := Functor.whiskerRight (inverseImageComorphismPush g).hom (forget CommRingCat.{u})) rfl

/-- The map of canonical presentations along `g` is compatible with the presentations and the
comorphism `𝒪_X ⟶ g_*𝒪_Y`. -/
theorem structurePushMap_comp_presentation :
    structurePushMap f g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        (yCanonicalPresentation f g) =
      sourceCanonicalPresentation f ≫ structureComorphism g :=
  Stacks.SheafOfModules.freeAlgebraPushMap_comp_presentation g.hom.base
    (structureRingMap_comp_structureComorphism g f) (underlyingPresheafMap_comp g)

/-- The map of conormal sheaves `𝒥_X/𝒥_X² ⟶ g_*(𝒥_Y/𝒥_Y²)` of the canonical presentations. -/
abbrev structureConormalPushMap :=
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f))
  Stacks.SheafOfModules.presentationConormalPushMap g.hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_structureComorphism g f) (underlyingPresheafMap_comp g)

/-- The map of conormal sheaves `𝒥_T/𝒥_T² ⟶ ι_*(𝒥_Y/𝒥_Y²)` of the canonical presentations. -/
abbrev liftConormalPushMap :=
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f))
  Stacks.SheafOfModules.presentationConormalPushMap (inverseImageLift g).hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_inverseImageComorphismPush f g) (ε := Functor.whiskerRight
      (inverseImageComorphismPush g).hom (forget CommRingCat.{u})) rfl

/-- **The maps of conormal sheaves compose**: along `g` it is the one along `π` followed by the
one along `ι`. -/
theorem structureConormalPushMap_comp :
    structureConormalPushMap f g ≫ (pushforwardLiftProjIso g _).inv =
      conormalPushMap f g ≫ (modulePushforward (inverseImageProj g)).map
        (liftConormalPushMap f g) := by
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f))
  refine Stacks.Sites.Conormal.conormal_hom_ext.{u, u, u, u} _ _ (fun U x => ?_)
  show ((structureConormalPushMap f g).val.app U) _ =
    ((liftConormalPushMap f g).val.app _) (((conormalPushMap f g).val.app U) _)
  have h1 := Stacks.Sites.Conormal.conormalSheafMapPush_toAssociatedModule g.hom.base X.sheaf
    Y.sheaf (structureComorphism g) (sourceCanonicalPresentation f) (yCanonicalPresentation f g)
    (structurePushMap f g) (structurePushMap_comp_presentation f g) U
    ((Stacks.Sites.Conormal.kernelIdeal (sourceCanonicalPresentation f).hom U).toCotangent x)
  have h2 := Stacks.Sites.Conormal.conormalSheafMapPush_toAssociatedModule
    (inverseImageProj g).hom.base X.sheaf (inverseImageRingedSpace g).sheaf
    (structureComorphism (inverseImageProj g)) (sourceCanonicalPresentation f)
    (targetCanonicalPresentation f g) (canonicalPushMap f g)
    (canonicalPushMap_comp_presentation f g) U
    ((Stacks.Sites.Conormal.kernelIdeal (sourceCanonicalPresentation f).hom U).toCotangent x)
  have hx := Stacks.Sites.Conormal.kernelIdeal_le_comap_sectionsMapPush
    (inverseImageProj g).hom.base X.sheaf (inverseImageRingedSpace g).sheaf
    (structureComorphism (inverseImageProj g)) (sourceCanonicalPresentation f)
    (targetCanonicalPresentation f g) (canonicalPushMap f g)
    (canonicalPushMap_comp_presentation f g) U x.2
  have h3 := Stacks.Sites.Conormal.conormalSheafMapPush_toAssociatedModule
    (inverseImageLift g).hom.base (inverseImageRingedSpace g).sheaf Y.sheaf
    (inverseImageComorphismPush g) (midCanonicalPresentation f g) (yCanonicalPresentation f g)
    (liftPushMap f g) (liftPushMap_comp_presentation f g)
    ((Opens.map (inverseImageProj g).hom.base).op.obj U)
    ((Stacks.Sites.Conormal.kernelIdeal _ _).toCotangent ⟨_, hx⟩)
  refine h1.trans (Eq.trans ?_ ((congrArg ((liftConormalPushMap f g).val.app _).hom h2).trans
    h3).symm)
  have h4 := congrArg (fun t => (t.hom.app U).hom x.1) (structurePushMap_eq f g)
  exact congrArg _ (congrArg _ (Subtype.ext h4))

/-- The map `𝒪_X ⊗ Ω ⟶ g_*(𝒪_Y ⊗ Ω)` of the canonical presentations. -/
abbrev structureTensorPushMap :=
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f))
  Stacks.SheafOfModules.presentationTensorPushMap g.hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_structureComorphism g f) (underlyingPresheafMap_comp g)

/-- The map `g⁻¹𝒪_X ⊗ Ω ⟶ ι_*(𝒪_Y ⊗ Ω)` of the canonical presentations. -/
abbrev liftTensorPushMap :=
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f))
  Stacks.SheafOfModules.presentationTensorPushMap (inverseImageLift g).hom.base
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) (α₁ := 𝟙 _)
    (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (α₂ := 𝟙 _)
    (structureRingMap_comp_inverseImageComorphismPush f g) (ε := Functor.whiskerRight
      (inverseImageComorphismPush g).hom (forget CommRingCat.{u})) rfl

/-- The map of canonical presentations along `g` restricts on coefficients to the map of base
rings `f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S`. -/
theorem structurePushMap_coefficient :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
        (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) ≫ structurePushMap f g =
      baseRingPushMap g f ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y.carrier)
          (inverseImageBaseRing (g ≫ f))
          (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)) :=
  Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap _ _ _ _ _ _ _

/-- The map of canonical presentations along `ι` restricts on coefficients to the identification
of base rings `(g ∘ f)⁻¹𝒪_S ⟶ ι_*(g ∘ f)⁻¹𝒪_S`. -/
theorem liftPushMap_coefficient :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
        (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
          (inverseImageRingedSpace g).sheaf) ≫ liftPushMap f g =
      inverseImageBaseRingId f g ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageLift g).hom.base).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y.carrier)
          (inverseImageBaseRing (g ≫ f))
          (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)) :=
  Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap _ _ _ _ _ _ _

/-- **The maps of the scalar extensions of the differentials compose.** -/
theorem structureTensorPushMap_comp :
    structureTensorPushMap f g ≫ (pushforwardLiftProjIso g _).inv =
      tensorPushMap f g ≫ (modulePushforward (inverseImageProj g)).map
        (liftTensorPushMap f g) := by
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
    (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f))
  refine Stacks.Sites.Conormal.tensorSheaf_hom_ext.{u, u, u, u} _ _ _ _ _ _ _ (fun U x => ?_)
  show ((structureTensorPushMap f g).val.app U) _ =
    ((liftTensorPushMap f g).val.app _) (((tensorPushMap f g).val.app U) _)
  have h1 := Stacks.Sites.Conormal.tensorSheafMapPush_tensorDifferential g.hom.base X.sheaf
    Y.sheaf (structureComorphism g) (sourceCanonicalPresentation f) (yCanonicalPresentation f g)
    (structurePushMap f g) (structurePushMap_comp_presentation f g) _ _ _ _
    (baseRingPushMap g f) (structurePushMap_coefficient f g) U x
  have h2 := Stacks.Sites.Conormal.tensorSheafMapPush_tensorDifferential
    (inverseImageProj g).hom.base X.sheaf (inverseImageRingedSpace g).sheaf
    (structureComorphism (inverseImageProj g)) (sourceCanonicalPresentation f)
    (targetCanonicalPresentation f g) (canonicalPushMap f g)
    (canonicalPushMap_comp_presentation f g) _ _ _ _ (baseRingPushMap (inverseImageProj g) f)
    (canonicalPushMap_coefficient f g) U x
  have h3 := Stacks.Sites.Conormal.tensorSheafMapPush_tensorDifferential
    (inverseImageLift g).hom.base (inverseImageRingedSpace g).sheaf Y.sheaf
    (inverseImageComorphismPush g) (midCanonicalPresentation f g) (yCanonicalPresentation f g)
    (liftPushMap f g) (liftPushMap_comp_presentation f g) _ _ _ _ (inverseImageBaseRingId f g)
    (liftPushMap_coefficient f g)
    ((Opens.map (inverseImageProj g).hom.base).op.obj U)
    ((Stacks.Sites.Conormal.sectionsMapAlong (inverseImageProj g).hom.base (canonicalPushMap f g)
      U).hom x)
  refine h1.trans (Eq.trans ?_ ((congrArg ((liftTensorPushMap f g).val.app _).hom h2).trans
    h3).symm)
  have h4 := congrArg (fun t => (t.hom.app U).hom x) (structurePushMap_eq f g)
  exact congrArg _ h4

/-- In degree `-1`, the canonical map `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}` is `structureConormalPushMap`,
up to the identifications of the degree `-1` terms with the conormal sheaves. -/
theorem structureNaiveCotangentPushMap_f_negOne :
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
      (structureRingMap (g ≫ f))
    (naiveCotangentPushMap g f).f (-1) =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (X.sheaf)
            (structureRingMap f) (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
            (𝟙 _)) ≫
        structureConormalPushMap f g ≫
        (modulePushforward g).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Y.sheaf)
            (structureRingMap (g ≫ f))
            (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (𝟙 _)).symm) :=
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne _
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
      (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (α₂ := 𝟙 _)
      (structureRingMap_comp_structureComorphism g f) (underlyingPresheafMap_comp g)

/-- In degree `0`, the canonical map `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}` is `structureTensorPushMap`, up
to the identifications of the degree `0` terms. -/
theorem structureNaiveCotangentPushMap_f_zero :
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
      (structureRingMap (g ≫ f))
    (naiveCotangentPushMap g f).f 0 =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (X.sheaf)
            (structureRingMap f) (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
            (𝟙 _)) ≫
        structureTensorPushMap f g ≫
        (modulePushforward g).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Y.sheaf)
            (structureRingMap (g ≫ f))
            (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (𝟙 _)).symm) :=
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_zero _
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (α₁ := 𝟙 _)
      (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (α₂ := 𝟙 _)
      (structureRingMap_comp_structureComorphism g f) (underlyingPresheafMap_comp g)

/-- In degree `-1`, the canonical map `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} ⟶ ι_*𝖭𝖫_{Y/S}` is
`liftConormalPushMap`, up to the identifications of the degree `-1` terms with the conormal
sheaves. -/
theorem inverseImageNaiveCotangentMap_f_negOne :
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
      (structureRingMap (g ≫ f))
    (inverseImageNaiveCotangentMap f g).f (-1) =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
            (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
            ((inverseImageRingedSpace g).sheaf) (structureRingMap (inverseImageSpaceHom f g))
            (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
              (inverseImageRingedSpace g).sheaf)
            (𝟙 _)) ≫
        liftConormalPushMap f g ≫
        (modulePushforward (inverseImageLift g)).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Y.sheaf)
            (structureRingMap (g ≫ f))
            (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (𝟙 _)).symm) :=
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne _
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageRingedSpace g).sheaf)
      (α₁ := 𝟙 _) (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)
      (α₂ := 𝟙 _)
      (ε := Functor.whiskerRight (inverseImageComorphismPush g).hom (forget CommRingCat.{u}))
      (structureRingMap_comp_inverseImageComorphismPush f g) (rfl)

/-- In degree `0`, the canonical map `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} ⟶ ι_*𝖭𝖫_{Y/S}` is
`liftTensorPushMap`, up to the identifications of the degree `0` terms. -/
theorem inverseImageNaiveCotangentMap_f_zero :
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
      (inverseImageRingedSpace g).sheaf (structureRingMap (inverseImageSpaceHom f g))
    letI := Stacks.SheafOfModules.presentation_id_isLocallySurjective
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
      (structureRingMap (g ≫ f))
    (inverseImageNaiveCotangentMap f g).f 0 =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
            (inverseImageBaseRing (X := inverseImageRingedSpace g) (inverseImageSpaceHom f g))
            ((inverseImageRingedSpace g).sheaf) (structureRingMap (inverseImageSpaceHom f g))
            (underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
              (inverseImageRingedSpace g).sheaf)
            (𝟙 _)) ≫
        liftTensorPushMap f g ≫
        (modulePushforward (inverseImageLift g)).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Y.sheaf)
            (structureRingMap (g ≫ f))
            (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf) (𝟙 _)).symm) :=
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_zero _
    (E₁ := underlyingPresheaf (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
        (inverseImageRingedSpace g).sheaf)
      (α₁ := 𝟙 _) (E₂ := underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)
      (α₂ := 𝟙 _)
      (ε := Functor.whiskerRight (inverseImageComorphismPush g).hom (forget CommRingCat.{u}))
      (structureRingMap_comp_inverseImageComorphismPush f g) (rfl)

/-- Composing two maps framed by transport isomorphisms. -/
theorem comp_eqToHom_framed {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Gg : E ⥤ C) (Gπ : D ⥤ C) (Gι : E ⥤ D) (φ : Gg ⟶ Gι ⋙ Gπ) {A A' : C} {B B' : D}
    {Z Z' : E} (e₁ : A' = A) (e₂ : Z = Z') (e₃ : B = B') (e₃' : B' = B)
    (Mg : A ⟶ Gg.obj Z) (Mπ : A ⟶ Gπ.obj B) (Mι : B ⟶ Gι.obj Z)
    (key : Mg ≫ φ.app Z = Mπ ≫ Gπ.map Mι) :
    (eqToHom e₁ ≫ Mg ≫ Gg.map (eqToHom e₂)) ≫ φ.app Z' =
      (eqToHom e₁ ≫ Mπ ≫ Gπ.map (eqToHom e₃)) ≫
        Gπ.map (eqToHom e₃' ≫ Mι ≫ Gι.map (eqToHom e₂)) := by
  subst e₂ e₃
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
    Category.assoc, key]

/-- `comp_eqToHom_framed`, with the three maps given by equations rather than explicit forms. -/
private theorem comp_eq_framed {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Gg : E ⥤ C) (Gπ : D ⥤ C) (Gι : E ⥤ D) (φ : Gg ⟶ Gι ⋙ Gπ) {A A' : C} {B B' : D}
    {Z Z' : E} (e₁ : A' = A) (e₂ : Z = Z') (e₃ : B = B') (e₃' : B' = B)
    (Mg : A ⟶ Gg.obj Z) (Mπ : A ⟶ Gπ.obj B) (Mι : B ⟶ Gι.obj Z)
    (key : Mg ≫ φ.app Z = Mπ ≫ Gπ.map Mι) {F₁ : A' ⟶ Gg.obj Z'} {F₂ : A' ⟶ Gπ.obj B'}
    {F₃ : B' ⟶ Gι.obj Z'} (h₁ : F₁ = eqToHom e₁ ≫ Mg ≫ Gg.map (eqToHom e₂))
    (h₂ : F₂ = eqToHom e₁ ≫ Mπ ≫ Gπ.map (eqToHom e₃))
    (h₃ : F₃ = eqToHom e₃' ≫ Mι ≫ Gι.map (eqToHom e₂)) : F₁ ≫ φ.app Z' = F₂ ≫ Gπ.map F₃ := by
  subst h₁ h₂ h₃
  exact comp_eqToHom_framed Gg Gπ Gι φ e₁ e₂ e₃ e₃' Mg Mπ Mι key

/-- **The canonical maps of naive cotangent complexes compose**: `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}` is
`𝖭𝖫_{X/S} ⟶ π_*𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} ⟶ π_*ι_*𝖭𝖫_{Y/S}`. -/
theorem naiveCotangentPushMap_comp :
    naiveCotangentPushMap g f ≫ (NatTrans.mapHomologicalComplex
        (pushforwardLiftProjNatIso g).inv (ComplexShape.up ℤ)).app _ =
      naiveCotangentPushMap (inverseImageProj g) f ≫
        ((modulePushforward (inverseImageProj g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (inverseImageNaiveCotangentMap f g) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h₁ : i = -1
  · subst h₁
    refine (HomologicalComplex.comp_f _ _ _).trans
      (Eq.trans ?_ (HomologicalComplex.comp_f _ _ _).symm)
    exact comp_eq_framed (modulePushforward g) (modulePushforward (inverseImageProj g))
      (modulePushforward (inverseImageLift g)) (pushforwardLiftProjNatIso g).inv _ _ _ _ _ _ _
      (structureConormalPushMap_comp f g) (structureNaiveCotangentPushMap_f_negOne f g)
      (naiveCotangentPushMap_f_negOne f g) (inverseImageNaiveCotangentMap_f_negOne f g)
  by_cases h₀ : i = 0
  · subst h₀
    refine (HomologicalComplex.comp_f _ _ _).trans
      (Eq.trans ?_ (HomologicalComplex.comp_f _ _ _).symm)
    exact comp_eq_framed (modulePushforward g) (modulePushforward (inverseImageProj g))
      (modulePushforward (inverseImageLift g)) (pushforwardLiftProjNatIso g).inv _ _ _ _ _ _ _
      (structureTensorPushMap_comp f g) (structureNaiveCotangentPushMap_f_zero f g)
      (naiveCotangentPushMap_f_zero f g) (inverseImageNaiveCotangentMap_f_zero f g)
  exact (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
    (structureRingMap f) i h₁ h₀).eq_of_src _ _

end AlgebraicGeometry.RingedSpaceThickening
