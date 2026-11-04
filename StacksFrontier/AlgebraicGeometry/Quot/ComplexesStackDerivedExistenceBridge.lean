module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFormalEffectiveness
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFiniteTypeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjectionCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeSubalgebraModel

/-!
# The change of base from `X_T ⟶ T` to Situation 0DIK

Let `D` be the standing situation of Stacks 0DLE over `S` and `L` a tower `T_n ≅ Spec R_n` with
limit `T ≅ Spec (lim R_n)` (`AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower`).  This
file relocates `X_T` to an algebraic space over `Spec (lim R_n)` (Stacks 04SG), proper, flat and
of finite presentation there, identifies its infinitesimal base changes `X_n` of Situation 0DIK
with the `X_{T_n}`, and builds the system of Situation 0DIK
(`AlgebraicGeometry.Space.DerivedExistenceSystem`) carrying given `K_n`, `φ_n` on the `X_{T_n}`.
This is the bridge by which Stacks 0DIQ (not yet proved here) discharges the hypothesis
`h0DIQ` of `AlgebraicGeometry.Space.ComplexesSituation.exists_realization_of_specLimitTower`.

The derived categories over the smaller base (B3–B5) enter through the structure
`AlgebraicGeometry.Space.ComplexesSituation.SmallerBaseDerivedComparison`, which
`AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`
(`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackSmallerBaseComparison.lean`) fills.  Nothing
here is registered.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.limitSpaceOver`: `X_T` over
  `Spec (lim R_n)`.
* `AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.stageSpaceRelocalizeIso`: the
  extension of `X_n` to `S` is `X_{T_n}`.
* `AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.derivedExistenceSystem`: the system
  of Situation 0DIK at `X_T ⟶ T`.

## Main results

* `SpecLimitTower.isProper_isFlat_isFinitePresentation_limitSpaceOver`: `X_T` is proper, flat and
  of finite presentation over `Spec (lim R_n)`.
* `SpecLimitTower.stageSpaceRelocalizeIso_hom_relativeMap_toLimit`
  and `..._relativeMap_transition`: the identifications carry the maps of Situation 0DIK to the
  base changes of `T_n ⟶ T` and `T_n ⟶ T_{n+1}`.
* `AlgebraicGeometry.Space.ComplexesSituation.fibreComp_compComparison_eq`: the compatibility of
  Stacks 0DIQ at `X_T ⟶ T` from the one over the smaller base.
* `SpecLimitTower.exists_restriction_of_derivedExistence`:
  Stacks 0DIQ gives the hypothesis `h0DIQ` at `X_T ⟶ T`.
* `AlgebraicGeometry.Space.ComplexesSituation.isEffective_formalObject_of_derivedExistence` and
  `isStronglyFormallyEffective_complexes_of_derivedExistence`: Stacks 0DLM with Stacks 0DIQ.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt baseProjection baseTransition)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian


universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory

/-- `D(𝒪_Y)` in the spelling of the ringed topos of `Y`, the one
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is stated at. -/
abbrev toposDerived {B : BigFppfSite.{u}} {W : Scheme.{u}} {hW : B.Contains W}
    (Y : AlgebraicSpaces B W hW) :=
  @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B W hW Y)) _ _
    (HasDerivedCategory.standard _)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : ComplexesSituation B S hS}

namespace SpecLimitTower

variable {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
  (L : D.SpecLimitTower level transition)

/-! ### The limit base -/

/-- The limit cone of the tower and the chosen limit of `(R_n)` have isomorphic points. -/
def limitRingIso : L.cR.pt ≅ limit L.R :=
  L.isLimit.conePointUniqueUpToIso (limit.isLimit _)

/-- The test scheme `T` over the limit is the chosen limit base `Spec (lim R_n)`. -/
def limitBaseIso : (BigFppfOver.toScheme B S hS).obj L.T.left ≅ limitBase L.R :=
  L.eLimit ≪≫ Scheme.Spec.mapIso L.limitRingIso.symm.op

/-- The limit base `Spec (lim R_n)` lies in the site, being isomorphic to `T`. -/
theorem contains_limitBase : B.Contains (limitBase L.R) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact L.limitBaseIso.inv) L.T.left.left.2

/-- Every level `Spec R_n` lies in the site, being isomorphic to `T_n`. -/
theorem contains_baseAt (n : ℕ) : B.Contains (baseAt L.R n) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (L.e n).inv) (level n).left.left.2

/-- The structure morphism `Spec (lim R_n) ⟶ S`, through `T`. -/
def limitBaseHom : B.obj L.contains_limitBase ⟶ B.obj hS :=
  ObjectProperty.homMk (L.limitBaseIso.inv ≫ B.inclusion.map L.T.left.hom)

/-- `T`, as an object of the site over `S`, is `Spec (lim R_n)` with the structure morphism
`AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.limitBaseHom`. -/
def limitTestSchemeIso : L.T.left ≅ Over.mk L.limitBaseHom :=
  Over.isoMk ((ObjectProperty.fullyFaithfulι _).preimageIso L.limitBaseIso) (by
    apply ObjectProperty.hom_ext
    change L.limitBaseIso.hom ≫ L.limitBaseIso.inv ≫ B.inclusion.map L.T.left.hom = _
    rw [Iso.hom_inv_id_assoc]
    rfl)

/-- The morphism `X_U ⟶ Spec (lim R_n)` of the base change along a test scheme `U` over `T`. -/
def spaceToLimitBase {U : SchemesOver D.Y} (u : U ⟶ L.T) :
    (D.space U).1 ⟶ yoneda.obj (Over.mk L.limitBaseHom) :=
  (D.projection U).hom ≫ yoneda.map (u.left ≫ L.limitTestSchemeIso.hom)

/-- **`X_T`, read over `Spec (lim R_n)`.**  The algebraic space over the limit base that Stacks
04SG attaches to `X_T` with its morphism to `T ≅ Spec (lim R_n)`. -/
def limitSpace : AlgebraicSpaces B (limitBase L.R) L.contains_limitBase :=
  spaceOverSmallerBase B (limitBase L.R) S L.contains_limitBase hS L.limitBaseHom (D.space L.T)
    (L.spaceToLimitBase (𝟙 L.T))

/-- `X_T` read over `Spec (lim R_n)`, as an object over the limit base. -/
def limitSpaceOver :
    Over (schemeSpace (limitBaseObject L.R B L.contains_limitBase)) :=
  Over.mk (ObjectProperty.homMk (toYonedaId B (limitBase L.R) L.contains_limitBase
    L.limitSpace.obj))

/-- The morphism `X_T ⟶ Spec (lim R_n)` is proper, flat and of finite presentation. -/
theorem isProper_isFlat_isFinitePresentation_spaceToLimitBase {U : SchemesOver D.Y}
    (u : U ⟶ L.T) (hU : IsIso u.left) :
    IsProper B S hS (L.spaceToLimitBase u) ∧ IsFlat B S hS (L.spaceToLimitBase u) ∧
      IsFinitePresentation B S hS (L.spaceToLimitBase u) := by
  let e := yoneda.mapIso (@asIso _ _ _ _ u.left hU ≪≫ L.limitTestSchemeIso)
  show IsProper B S hS ((D.projection U).hom ≫ e.hom) ∧
    IsFlat B S hS ((D.projection U).hom ≫ e.hom) ∧
    IsFinitePresentation B S hS ((D.projection U).hom ≫ e.hom)
  refine (@isProper_isFlat_isFinitePresentation_comp_isIso_iff B S hS _ _ _ (D.projection U).hom
    e.hom e.isIso_hom).2
    ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f U.hom) D.proper,
    D.projection_isFlat U,
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f U.hom) D.finitePresentation⟩

/-- **`X_T` read over `Spec (lim R_n)` is proper, flat and of finite presentation over it.** -/
theorem isProper_isFlat_isFinitePresentation_limitSpaceOver :
    IsProper B (limitBase L.R) L.contains_limitBase L.limitSpaceOver.hom.hom ∧
      IsFlat B (limitBase L.R) L.contains_limitBase L.limitSpaceOver.hom.hom ∧
      IsFinitePresentation B (limitBase L.R) L.contains_limitBase
        L.limitSpaceOver.hom.hom := by
  let F := spacesOverSmallerBaseEquivalence B (limitBase L.R) S L.contains_limitBase hS
    L.limitBaseHom
  let c := (ObjectProperty.ι _).mapIso
    (F.counitIso.app ⟨Over.mk (L.spaceToLimitBase (𝟙 L.T)), (D.space L.T).2⟩)
  have : IsIso c.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso c).hom)
  have hc : c.hom.left ≫ L.spaceToLimitBase (𝟙 L.T) =
      ((spacesOverSmallerBaseFunctor B (limitBase L.R) S L.contains_limitBase hS
        L.limitBaseHom).obj L.limitSpace).1.hom :=
    Over.w c.hom
  have h₁ := (isProper_isFlat_isFinitePresentation_isIso_comp_iff B S hS c.hom.left _).2
    (L.isProper_isFlat_isFinitePresentation_spaceToLimitBase (𝟙 L.T) inferInstance)
  rw [hc] at h₁
  exact ⟨(isProper_spacesOverSmallerBaseFunctor_obj_hom_iff B _ hS _ _).1 h₁.1,
    (holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_obj_hom_iff B _ hS _ _ _).1 h₁.2.1,
    (isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff B _ hS _ _).1 h₁.2.2⟩

/-! ### The levels -/

/-- **The level maps are the maps induced by the limit projections**, read on the chosen limit
base: `T_n ≅ Spec R_n ⟶ Spec (lim R_n)` is `T_n ⟶ T ≅ Spec (lim R_n)`. -/
theorem e_hom_baseProjection (n : ℕ) :
    (L.e n).hom ≫ baseProjection L.R n =
      (BigFppfOver.toScheme B S hS).map (L.toLimit n).left ≫ L.limitBaseIso.hom := by
  have hπ : L.limitRingIso.hom ≫ limit.π L.R (op n) = L.cR.π.app (op n) :=
    L.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op n)
  rw [limitBaseIso, Iso.trans_hom, ← Category.assoc, L.toLimit_e, Category.assoc]
  congr 1
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  rw [← hπ, ← Category.assoc]
  show _ = (L.limitRingIso.inv ≫ L.limitRingIso.hom) ≫ _
  rw [Iso.inv_hom_id, Category.id_comp]

/-- **The transitions are the maps induced by the rings**, read on the chosen levels. -/
theorem e_hom_baseTransition (n : ℕ) :
    (L.e n).hom ≫ baseTransition L.R n =
      (BigFppfOver.toScheme B S hS).map (transition n).left ≫ (L.e (n + 1)).hom :=
  (L.transition_e n).symm

/-- The level `T_n`, as an object of the site over `S`, is `Spec R_n` over `S` through
`Spec R_n ⟶ Spec (lim R_n) ⟶ S`. -/
def levelIso (n : ℕ) :
    (level n).left ≅ (Over.map L.limitBaseHom).obj
      (baseObjectAt L.R B L.contains_limitBase L.contains_baseAt n) :=
  Over.isoMk ((ObjectProperty.fullyFaithfulι _).preimageIso (L.e n)) (by
    apply ObjectProperty.hom_ext
    change (L.e n).hom ≫ baseProjection L.R n ≫ L.limitBaseIso.inv ≫
      B.inclusion.map L.T.left.hom = B.inclusion.map (level n).left.hom
    rw [← Category.assoc, e_hom_baseProjection, Category.assoc, Iso.hom_inv_id_assoc]
    exact (B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map (Over.w (L.toLimit n).left)))

/-- The limit base over itself, read over `S`, is `T`. -/
def limitObjectIso :
    (Over.map L.limitBaseHom).obj (limitBaseObject L.R B L.contains_limitBase) ≅ L.T.left :=
  Over.isoMk (Iso.refl _) (by simp) ≪≫ L.limitTestSchemeIso.symm

/-- The lower-shriek extension of `Spec R_n`, the level `n` base over the limit base, is `T_n`,
at the spelling of the representable presheaves. -/
def relocalizeBaseYonedaIso (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).obj
        (yoneda.obj (baseObjectAt L.R B L.contains_limitBase L.contains_baseAt n)) ≅
      yoneda.obj (level n).left :=
  relocalizedYonedaIso B (B.obj L.contains_limitBase) (B.obj hS) L.limitBaseHom _ ≪≫
    yoneda.mapIso (L.levelIso n).symm

/-- The lower-shriek extension of the limit base over itself is `T`, at the spelling of the
representable presheaves. -/
def relocalizeLimitYonedaIso :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).obj
        (yoneda.obj (limitBaseObject L.R B L.contains_limitBase)) ≅
      yoneda.obj L.T.left :=
  relocalizedYonedaIso B (B.obj L.contains_limitBase) (B.obj hS) L.limitBaseHom _ ≪≫
    yoneda.mapIso L.limitObjectIso

/-- The identifications `relocalizeBaseYonedaIso` and `relocalizeLimitYonedaIso` carry the
lower-shriek extension of the projection to level `n` to the map `T_n ⟶ T`. -/
theorem relocalize_yonedaMap_baseObjectProjection (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
        (yoneda.map (baseObjectProjection L.R B L.contains_limitBase L.contains_baseAt n)) ≫
      L.relocalizeLimitYonedaIso.hom =
    (L.relocalizeBaseYonedaIso n).hom ≫ yoneda.map (L.toLimit n).left := by
  simp only [relocalizeLimitYonedaIso, relocalizeBaseYonedaIso, Iso.trans_hom,
    Functor.mapIso_hom, ← Category.assoc, relocalizedYonedaIso_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  rw [Iso.symm_hom, Iso.eq_inv_comp]
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show (L.e n).hom ≫ baseProjection L.R n ≫ L.limitBaseIso.inv = _
  rw [← Category.assoc, e_hom_baseProjection, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The identification `relocalizeBaseYonedaIso` carries the lower-shriek extension of the
transition at level `n` to the map `T_n ⟶ T_{n+1}`. -/
theorem relocalize_yonedaMap_baseObjectTransition (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
        (yoneda.map (baseObjectTransition L.R B L.contains_limitBase L.contains_baseAt n)) ≫
      (L.relocalizeBaseYonedaIso (n + 1)).hom =
    (L.relocalizeBaseYonedaIso n).hom ≫ yoneda.map (transition n).left := by
  simp only [relocalizeBaseYonedaIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, relocalizedYonedaIso_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp]
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show (L.e n).hom ≫ baseTransition L.R n ≫ (L.e (n + 1)).inv = _
  rw [← Category.assoc, e_hom_baseTransition, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The lower-shriek extension of `toYonedaId` at a presheaf `F` over the limit base, followed
by `relocalizeLimitYonedaIso`, is `OverShriek.relocalizeToYoneda` followed by the inverse of
`limitTestSchemeIso`. -/
theorem relocalize_toYonedaId_comp_relocalizeLimitYonedaIso
    (F : (BigFppfOver B (limitBase L.R) L.contains_limitBase)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
        (toYonedaId B (limitBase L.R) L.contains_limitBase F) ≫ L.relocalizeLimitYonedaIso.hom =
      OverShriek.relocalizeToYoneda L.limitBaseHom F ≫
        yoneda.map L.limitTestSchemeIso.inv := by
  simp only [relocalizeLimitYonedaIso, limitObjectIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc]
  congr 1

/-- **The lower-shriek extension of `Spec R_n`, the level `n` base over the limit base, is
`T_n`.** -/
def relocalizeBaseIso (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).obj
        (schemeSpace (baseObjectAt L.R B L.contains_limitBase L.contains_baseAt n)).obj ≅
      ((schemeSpaceFunctor B S hS).obj (level n).left).obj :=
  L.relocalizeBaseYonedaIso n

/-- **The lower-shriek extension of the limit base over itself is `T`.** -/
def relocalizeLimitIso :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).obj
        (schemeSpace (limitBaseObject L.R B L.contains_limitBase)).obj ≅
      ((schemeSpaceFunctor B S hS).obj L.T.left).obj :=
  L.relocalizeLimitYonedaIso

/-- The structure morphism of `Spec R_n` to the limit base, extended to `S`, is `T_n ⟶ T`. -/
theorem relocalize_baseSpaceProjection (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
        (baseSpaceProjection L.R B L.contains_limitBase L.contains_baseAt n).hom ≫
      L.relocalizeLimitIso.hom =
    (L.relocalizeBaseIso n).hom ≫ ((schemeSpaceFunctor B S hS).map (L.toLimit n).left).hom :=
  L.relocalize_yonedaMap_baseObjectProjection n

/-- The transition `Spec R_n ⟶ Spec R_{n+1}`, extended to `S`, is `T_n ⟶ T_{n+1}`. -/
theorem relocalize_baseSpaceTransition (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
        (baseSpaceTransition L.R B L.contains_limitBase L.contains_baseAt n).hom ≫
      (L.relocalizeBaseIso (n + 1)).hom =
    (L.relocalizeBaseIso n).hom ≫ ((schemeSpaceFunctor B S hS).map (transition n).left).hom :=
  L.relocalize_yonedaMap_baseObjectTransition n

/-! ### The infinitesimal base changes are the base changes along the levels -/

/-- The level `n` infinitesimal base change `X_n = X ×_{Spec (lim R_n)} Spec R_n` of Situation
0DIK, for `X = X_T` read over `Spec (lim R_n)`. -/
abbrev stageSpace (n : ℕ) : AlgebraicSpaces B (limitBase L.R) L.contains_limitBase :=
  spaceAt L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver n

/-- **`X_T` read over `Spec (lim R_n)` extends back to `X_T`**: the identification
`Λ X_T' ≅ X_T` of Stacks 04SG. -/
def limitSpaceRelocalizeIso :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).obj L.limitSpaceOver.left.1 ≅
      (D.space L.T).1 :=
  relocalizeSpaceOverSmallerBaseIso B (limitBase L.R) S L.contains_limitBase hS L.limitBaseHom
    (D.space L.T) (L.spaceToLimitBase (𝟙 L.T))

/-- `X_T ⟶ Spec (lim R_n)`, read through `T ≅ Spec (lim R_n)`, is the projection `X_T ⟶ T`. -/
theorem spaceToLimitBase_id_comp :
    L.spaceToLimitBase (𝟙 L.T) ≫ yoneda.map L.limitTestSchemeIso.inv = (D.projection L.T).hom := by
  have h : yoneda.map (CommaMorphism.left (𝟙 L.T) ≫ L.limitTestSchemeIso.hom) ≫
      yoneda.map L.limitTestSchemeIso.inv = 𝟙 _ := by
    rw [← Functor.map_comp, CostructuredArrow.id_left, Category.id_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  exact (congrArg (fun x => (D.projection L.T).hom ≫ x) h).trans (Category.comp_id _)

/-- The structure morphism of `X_T` read over `Spec (lim R_n)`, extended to `S`, is the
projection `X_T ⟶ T`. -/
theorem relocalize_limitSpaceOver_hom :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map L.limitSpaceOver.hom.hom ≫
        L.relocalizeLimitIso.hom =
      L.limitSpaceRelocalizeIso.hom ≫ (D.projection L.T).hom :=
  calc _ = OverShriek.relocalizeToYoneda L.limitBaseHom
          (spaceOverSmallerBase B (limitBase L.R) S L.contains_limitBase hS L.limitBaseHom
            (D.space L.T) (L.spaceToLimitBase (𝟙 L.T))).1 ≫
        yoneda.map L.limitTestSchemeIso.inv :=
        L.relocalize_toYonedaId_comp_relocalizeLimitYonedaIso _
    _ = ((relocalizeSpaceOverSmallerBaseIso B (limitBase L.R) S L.contains_limitBase hS
            L.limitBaseHom (D.space L.T) (L.spaceToLimitBase (𝟙 L.T))).hom ≫
          L.spaceToLimitBase (𝟙 L.T)) ≫ yoneda.map L.limitTestSchemeIso.inv := by
        rw [relocalizeSpaceOverSmallerBaseIso_hom_comp]
    _ = _ := by
        rw [Category.assoc, spaceToLimitBase_id_comp]
        rfl

/-- The cartesian square of `X_n`, extended to `S` and read through the identifications of the
extended bases with `T_n` and `T` and of the extended `X_T'` with `X_T`. -/
theorem isPullback_relocalize_stageSpace (n : ℕ) :
    IsPullback
      ((OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
          (spaceBaseProjection L.R B L.contains_limitBase L.contains_baseAt
            L.limitSpaceOver n).hom ≫ (L.relocalizeBaseIso n).hom)
      ((OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
          (spaceProjection L.R B L.contains_limitBase L.contains_baseAt
            L.limitSpaceOver n).hom ≫ L.limitSpaceRelocalizeIso.hom)
      ((schemeSpaceFunctor B S hS).map (L.toLimit n).left).hom (D.projection L.T).hom := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (OverShriek.relocalizePresheafFunctor L.limitBaseHom) :=
    relocalizePresheaf_preservesConnectedLimits L.limitBaseHom
  exact ((AlgebraicSpaces.isPullback_hom B _ _ (isPullback_spaceAt L.R B L.contains_limitBase
      L.contains_baseAt L.limitSpaceOver n)).map
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom)).of_iso (Iso.refl _)
    (L.relocalizeBaseIso n) L.limitSpaceRelocalizeIso L.relocalizeLimitIso
    (by simp) (by simp) (L.relocalize_baseSpaceProjection n) L.relocalize_limitSpaceOver_hom

/-- The cartesian square of the base change `X_{T_n}` of `X_T` along `T_n ⟶ T`, in presheaves. -/
theorem isPullback_space_level (n : ℕ) :
    IsPullback (D.projection (level n)).hom (D.relativeMap (L.toLimit n)).hom
      ((schemeSpaceFunctor B S hS).map (L.toLimit n).left).hom (D.projection L.T).hom :=
  (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f (L.toLimit n))).flip

/-- **B2: the infinitesimal base change `X_n` of Situation 0DIK, extended to `S`, is `X_{T_n}`.**
Both are fibre products of `X_T ⟶ T ⟵ T_n`. -/
def stageSpaceRelocalizeIso (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor L.limitBaseHom).obj (L.stageSpace n).1 ≅
      (D.space (level n)).1 :=
  (L.isPullback_relocalize_stageSpace n).isoIsPullback _ _ (L.isPullback_space_level n)

/-- The identification `Λ X_n ≅ X_{T_n}` lies over `T_n`. -/
@[reassoc]
theorem stageSpaceRelocalizeIso_hom_projection (n : ℕ) :
    (L.stageSpaceRelocalizeIso n).hom ≫ (D.projection (level n)).hom =
      (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
          (spaceBaseProjection L.R B L.contains_limitBase L.contains_baseAt
            L.limitSpaceOver n).hom ≫ (L.relocalizeBaseIso n).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The identification `Λ X_n ≅ X_{T_n}` carries `X_n ⟶ X` to `X_{T_n} ⟶ X_T`**: the square
of Situation 0DIK's `spaceProjection` and the base change of `T_n ⟶ T`. -/
@[reassoc]
theorem stageSpaceRelocalizeIso_hom_relativeMap_toLimit (n : ℕ) :
    (L.stageSpaceRelocalizeIso n).hom ≫ (D.relativeMap (L.toLimit n)).hom =
      (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
          (spaceProjection L.R B L.contains_limitBase L.contains_baseAt
            L.limitSpaceOver n).hom ≫ L.limitSpaceRelocalizeIso.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The base changes along `T_n ⟶ T_{n+1}` and `T_{n+1} ⟶ T` compose to that along `T_n ⟶ T`. -/
private theorem relativeMap_transition_comp_toLimit (n : ℕ) :
    D.relativeMap (transition n) ≫ D.relativeMap (L.toLimit (n + 1)) =
      D.relativeMap (L.toLimit n) := by
  rw [← baseChangeMap_comp, L.transition_toLimit]

/-- **The identifications `Λ X_n ≅ X_{T_n}` carry `X_n ⟶ X_{n+1}` to `X_{T_n} ⟶ X_{T_{n+1}}`**:
the square of Situation 0DIK's `transitionSpace` and the base change of `T_n ⟶ T_{n+1}`. -/
theorem stageSpaceRelocalizeIso_hom_relativeMap_transition (n : ℕ) :
    (L.stageSpaceRelocalizeIso n).hom ≫ (D.relativeMap (transition n)).hom =
      (OverShriek.relocalizePresheafFunctor L.limitBaseHom).map
          (transitionSpace L.R B L.contains_limitBase L.contains_baseAt
            L.limitSpaceOver n).hom ≫ (L.stageSpaceRelocalizeIso (n + 1)).hom := by
  refine (L.isPullback_space_level (n + 1)).hom_ext ?_ ?_
  · have h₁ := congrArg (fun k => k.hom) (baseChangeMap_comp_inclusion D.f (transition n))
    have h₂ := congrArg (fun k => k.hom)
      (transitionSpace_spaceBaseProjection L.R B L.contains_limitBase L.contains_baseAt
        L.limitSpaceOver n)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h₁ h₂
    rw [Category.assoc, h₁, stageSpaceRelocalizeIso_hom_projection_assoc, Category.assoc,
      stageSpaceRelocalizeIso_hom_projection, ← L.relocalize_baseSpaceTransition n,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h₂]
  · have h₁ := congrArg (fun k => k.hom) (L.relativeMap_transition_comp_toLimit n)
    have h₂ := congrArg (fun k => k.hom)
      (transitionSpace_spaceProjection L.R B L.contains_limitBase L.contains_baseAt
        L.limitSpaceOver n)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h₁ h₂
    rw [Category.assoc, h₁, stageSpaceRelocalizeIso_hom_relativeMap_toLimit, Category.assoc,
      stageSpaceRelocalizeIso_hom_relativeMap_toLimit, ← Category.assoc, ← Functor.map_comp, h₂]

/-- The morphism `X_U ⟶ X_{U'}` of base changes induced by a morphism of test schemes is
representable: it is the base change of the morphism of representable presheaves `U ⟶ U'`. -/
theorem relativelyRepresentable_relativeMap {U U' : SchemesOver D.Y} (k : U ⟶ U') :
    yoneda.relativelyRepresentable (D.relativeMap k).hom := by
  exact MorphismProperty.of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f k).flip)
    (Functor.relativelyRepresentable.map yoneda k.left)

/-- The projection `X_n ⟶ X` is representable: it is the base change of the morphism of
representable presheaves `Spec R_n ⟶ Spec (lim R_n)`. -/
theorem relativelyRepresentable_spaceProjection (n : ℕ) :
    yoneda.relativelyRepresentable
      (spaceProjection L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver n).hom := by
  exact MorphismProperty.of_isPullback (AlgebraicSpaces.isPullback_hom B _ L.contains_limitBase
    (isPullback_spaceAt L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver n))
    (Functor.relativelyRepresentable.map yoneda _)

/-- The transition `X_n ⟶ X_{n+1}` is representable: it is the base change of the morphism of
representable presheaves `Spec R_n ⟶ Spec R_{n+1}`. -/
theorem relativelyRepresentable_transitionSpace (n : ℕ) :
    yoneda.relativelyRepresentable
      (transitionSpace L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver n).hom := by
  exact MorphismProperty.of_isPullback (AlgebraicSpaces.isPullback_hom B _ L.contains_limitBase
    (isPullback_transitionSpace L.R B L.contains_limitBase L.contains_baseAt
      L.limitSpaceOver n)) (Functor.relativelyRepresentable.map yoneda _)

end SpecLimitTower

/-- **The derived categories over a smaller base, internal, B3–B5, filled by
`AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`**
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseDerived.lean`; not a Stacks
tag).  For `h : W ⟶ S` and an algebraic space `Z` over `W` whose lower-shriek extension is
identified with an algebraic space `Y` over `S` by `ε`, the data and facts the change of base of
Stacks 0DIQ uses:

* `equivalence` (`smallerBaseDerivedEquivalence h ε`): `D(𝒪_Y) ≌ D(𝒪_Z)`;
* `pullbackIso` (`smallerBaseDerivedPullbackIso`): it commutes with derived pullback along a
  representable morphism `g : Y₁ ⟶ Y₂` lying over `f : Z₁ ⟶ Z₂`;
* `pullbackIso_comp` (`smallerBaseDerivedPullbackIso_comp`): compatibly with the composition
  isomorphisms of Stacks 0D6D on both sides;
* `isPseudoCoherent_iff` (`isPseudoCoherent_smallerBaseDerivedEquivalence_iff`): it preserves and
  reflects pseudo-coherence;
* `compIso_eq` (`smallEtaleDerivedPullbackData_compIso_eq`): the composition
  comparison of the pullback datum `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` is the
  composition isomorphism `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`.

They are all proved, and
`AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison` fills the structure
from them. -/
structure SmallerBaseDerivedComparison (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) where
  /-- `D(𝒪_Y) ≌ D(𝒪_Z)` (B3). -/
  equivalence {W : Scheme.{u}} {hW : B.Contains W} (h : B.obj hW ⟶ B.obj hS)
    {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1) :
    toposDerived Y ≌ toposDerived Z
  /-- The equivalence commutes with derived pullback (B4). -/
  pullbackIso {W : Scheme.{u}} {hW : B.Contains W} (h : B.obj hW ⟶ B.obj hS)
    {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
    (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
    (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1) (f : Z₁ ⟶ Z₂) (g : Y₁ ⟶ Y₂)
    (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom) :
    smallEtaleDerivedModulePullback B S hS g ⋙ (equivalence h ε₁).functor ≅
      (equivalence h ε₂).functor ⋙ smallEtaleDerivedModulePullback B W hW f
  /-- The commutation with derived pullback is compatible with composition (B4). -/
  pullbackIso_comp {W : Scheme.{u}} {hW : B.Contains W} (h : B.obj hW ⟶ B.obj hS)
    {Z₁ Z₂ Z₃ : AlgebraicSpaces B W hW} {Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}
    (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
    (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
    (ε₃ : (OverShriek.relocalizePresheafFunctor h).obj Z₃.1 ≅ Y₃.1)
    (f : Z₁ ⟶ Z₂) (g : Y₁ ⟶ Y₂) (f' : Z₂ ⟶ Z₃) (g' : Y₂ ⟶ Y₃)
    (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg' : ε₂.hom ≫ g'.hom = (OverShriek.relocalizePresheafFunctor h).map f'.hom ≫ ε₃.hom)
    (hf' : yoneda.relativelyRepresentable f'.hom) (hg' : yoneda.relativelyRepresentable g'.hom)
    (hfg'' : ε₁.hom ≫ (g ≫ g').hom =
      (OverShriek.relocalizePresheafFunctor h).map (f ≫ f').hom ≫ ε₃.hom)
    (hf'' : yoneda.relativelyRepresentable (f ≫ f').hom)
    (hg'' : yoneda.relativelyRepresentable (g ≫ g').hom) (K : toposDerived Y₃) :
    (equivalence h ε₁).functor.map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g g').hom.app K) ≫
      (pullbackIso h ε₁ ε₃ (f ≫ f') (g ≫ g') hfg'' hf'' hg'').hom.app K =
    (pullbackIso h ε₁ ε₂ f g hfg hf hg).hom.app
        ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
      (smallEtaleDerivedModulePullback B W hW f).map
        ((pullbackIso h ε₂ ε₃ f' g' hfg' hf' hg').hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompIso B W hW f f').hom.app
        ((equivalence h ε₃).functor.obj K)
  /-- The equivalence preserves and reflects pseudo-coherence (B5). -/
  isPseudoCoherent_iff {W : Scheme.{u}} {hW : B.Contains W} (h : B.obj hW ⟶ B.obj hS)
    {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1) (K : toposDerived Y) :
    (smallEtaleRingedSite B W hW Z.1 Z.2).IsPseudoCoherent ((equivalence h ε).functor.obj K) ↔
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent K
  /-- The composition comparison of the pullback datum is that of Stacks 0D6D (B4). -/
  compIso_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleDerivedPullbackData B S hS).compIso f g =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).symm

namespace SmallerBaseDerivedComparison

variable (P : SmallerBaseDerivedComparison B S hS) {W : Scheme.{u}} {hW : B.Contains W}
  (h : B.obj hW ⟶ B.obj hS) {Z₁ Z₂ Z₃ : AlgebraicSpaces B W hW}
  {Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}
  {ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1}
  {ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1}
  {ε₃ : (OverShriek.relocalizePresheafFunctor h).obj Z₃.1 ≅ Y₃.1}

include P in
/-- The comparison `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of the pullback datum, at a composite
`g₁ ≫ g₂ = k`, is the inverse of the composition isomorphism of Stacks 0D6D. -/
theorem triangle_hom_app_eq {X₁ X₂ X₃ : AlgebraicSpaces B S hS} {g₁ : X₁ ⟶ X₂} {g₂ : X₂ ⟶ X₃}
    {k : X₁ ⟶ X₃} (hk : g₁ ≫ g₂ = k) (E : derivedModules B S hS X₃) :
    ((smallEtaleDerivedPullbackData B S hS).triangle hk).hom.app E =
      eqToHom (congrArg (fun m => ((smallEtaleDerivedPullbackData B S hS).pull m).obj E)
        hk.symm) ≫ (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂).inv.app E := by
  subst hk
  rw [PullbackData.triangle_eq, Iso.trans_hom, NatTrans.comp_app, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, P.compIso_eq]
  rfl

include P in
/-- A composite along the comparison `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of the pullback datum, read
through the composition isomorphism of Stacks 0D6D. -/
theorem fibreComp_triangle_eq_of {X₁ X₂ X₃ : AlgebraicSpaces B S hS} {g₁ : X₁ ⟶ X₂}
    {g₂ : X₂ ⟶ X₃} {k g₃ : X₁ ⟶ X₃} (hk : g₁ ≫ g₂ = k) (he : k = g₃)
    {E : derivedModules B S hS X₃} {A : derivedModules B S hS X₂}
    {B' : derivedModules B S hS X₁}
    (a : ((smallEtaleDerivedPullbackData B S hS).pull g₂).obj E ⟶ A)
    (b : ((smallEtaleDerivedPullbackData B S hS).pull g₁).obj A ⟶ B')
    (c : ((smallEtaleDerivedPullbackData B S hS).pull g₃).obj E ⟶ B')
    (h : (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂).inv.app E ≫
        (smallEtaleDerivedModulePullback B S hS g₁).map a ≫ b =
      eqToHom (congrArg (fun m => (smallEtaleDerivedModulePullback B S hS m).obj E)
        (hk.trans he)) ≫ c) :
    Functor.fibreComp ((smallEtaleDerivedPullbackData B S hS).triangle hk) b a =
      eqToHom (congrArg (fun m => ((smallEtaleDerivedPullbackData B S hS).pull m).obj E) he) ≫
        c := by
  subst he hk
  rw [Functor.fibreComp, P.triangle_hom_app_eq, eqToHom_refl, Category.id_comp]
  refine Eq.trans ?_ (h.trans ((congrArg (· ≫ c) (eqToHom_refl _ _)).trans (Category.id_comp c)))
  exact congrArg (· ≫ _) (Category.id_comp _)

/-- **Transport of a compatibility along the equivalences.**  Given maps over the two bases
`f₁ ≫ f₂ = f₃` and `g₁ ≫ g₂ = g₃' = g₃`, a map `a : Lg₂^* E ⟶ A`, a map `b : Lg₁^* A ⟶ B'` and a
map `c : Lg₃^* E ⟶ B'`, whose images under the equivalences factor as
`a ↦ α₂ ≫ Lf₂^* u ≫ a'`, `c ↦ α₃ ≫ Lf₃^* u ≫ c'` through a map `u` out of the image of `E`, with
`c' = (Lf₃^* ≅ Lf₁^* Lf₂^*) ≫ Lf₁^* a' ≫ α₁⁻¹ ≫ (image of b)` the compatibility over the smaller
base: then `a` and `b` compose to `c` along the composition comparison over `S`.

The composition isomorphism `Lf₃^* ≅ Lf₁^* Lf₂^*` enters as a variable `τ` with its value given
by an equation of isomorphisms `hτ`, so that a compatibility stated through another definition of
it (`AlgebraicGeometry.Space.DerivedExistenceSystem.stageDerivedPullbackCompIso`) is passed
as `hcc` as it stands: the kernel then compares the two definitions as isomorphisms, and not their
components at an object, which exhausts it. -/
theorem compIso_inv_comp_map_eq {f₁ : Z₁ ⟶ Z₂} {f₂ : Z₂ ⟶ Z₃} {f₃ : Z₁ ⟶ Z₃}
    (hf : f₁ ≫ f₂ = f₃) {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {g₃ : Y₁ ⟶ Y₃} (hk : g₁ ≫ g₂ = g₃)
    (hfg₁ : ε₁.hom ≫ g₁.hom = (OverShriek.relocalizePresheafFunctor h).map f₁.hom ≫ ε₂.hom)
    (hf₁ : yoneda.relativelyRepresentable f₁.hom)
    (hg₁ : yoneda.relativelyRepresentable g₁.hom)
    (hfg₂ : ε₂.hom ≫ g₂.hom = (OverShriek.relocalizePresheafFunctor h).map f₂.hom ≫ ε₃.hom)
    (hf₂ : yoneda.relativelyRepresentable f₂.hom)
    (hg₂ : yoneda.relativelyRepresentable g₂.hom)
    (hfg₃ : ε₁.hom ≫ g₃.hom = (OverShriek.relocalizePresheafFunctor h).map f₃.hom ≫ ε₃.hom)
    (hf₃ : yoneda.relativelyRepresentable f₃.hom)
    (hg₃ : yoneda.relativelyRepresentable g₃.hom)
    {E : toposDerived Y₃} {A : toposDerived Y₂} {B' : toposDerived Y₁} {K'' : toposDerived Z₃}
    (a : (smallEtaleDerivedModulePullback B S hS g₂).obj E ⟶ A)
    (b : (smallEtaleDerivedModulePullback B S hS g₁).obj A ⟶ B')
    (c : (smallEtaleDerivedModulePullback B S hS g₃).obj E ⟶ B')
    (u : (P.equivalence h ε₃).functor.obj E ⟶ K'')
    (a' : (smallEtaleDerivedModulePullback B W hW f₂).obj K'' ⟶ (P.equivalence h ε₂).functor.obj A)
    (c' : (smallEtaleDerivedModulePullback B W hW f₃).obj K'' ⟶
      (P.equivalence h ε₁).functor.obj B')
    (ha : (P.equivalence h ε₂).functor.map a =
      (P.pullbackIso h ε₂ ε₃ f₂ g₂ hfg₂ hf₂ hg₂).hom.app E ≫
        (smallEtaleDerivedModulePullback B W hW f₂).map u ≫ a')
    (hc : (P.equivalence h ε₁).functor.map c =
      (P.pullbackIso h ε₁ ε₃ f₃ g₃ hfg₃ hf₃ hg₃).hom.app E ≫
        (smallEtaleDerivedModulePullback B W hW f₃).map u ≫ c')
    (τ : smallEtaleDerivedModulePullback B W hW f₂ ⋙ smallEtaleDerivedModulePullback B W hW f₁ ≅
      smallEtaleDerivedModulePullback B W hW f₃)
    (hτ : τ = smallEtaleDerivedModulePullbackCompIso B W hW f₁ f₂ ≪≫
        smallEtaleDerivedModulePullbackCongr B W hW hf)
    (hcc : c' = τ.inv.app K'' ≫ (smallEtaleDerivedModulePullback B W hW f₁).map a' ≫
      (P.pullbackIso h ε₁ ε₂ f₁ g₁ hfg₁ hf₁ hg₁).inv.app A ≫ (P.equivalence h ε₁).functor.map b) :
    (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂).inv.app E ≫
        (smallEtaleDerivedModulePullback B S hS g₁).map a ≫ b =
      eqToHom (congrArg (fun m => (smallEtaleDerivedModulePullback B S hS m).obj E) hk) ≫ c := by
  subst hτ hcc
  subst hk hf
  apply (P.equivalence h ε₁).functor.map_injective
  have key₁ : (P.pullbackIso h ε₁ ε₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hfg₃ hf₃ hg₃).hom.app E =
      (P.equivalence h ε₁).functor.map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂).inv.app E) ≫
        (P.pullbackIso h ε₁ ε₂ f₁ g₁ hfg₁ hf₁ hg₁).hom.app
          ((smallEtaleDerivedModulePullback B S hS g₂).obj E) ≫
        (smallEtaleDerivedModulePullback B W hW f₁).map
          ((P.pullbackIso h ε₂ ε₃ f₂ g₂ hfg₂ hf₂ hg₂).hom.app E) ≫
        (smallEtaleDerivedModulePullbackCompIso B W hW f₁ f₂).hom.app
          ((P.equivalence h ε₃).functor.obj E) := by
    rw [← P.pullbackIso_comp h ε₁ ε₂ ε₃ f₁ g₁ f₂ g₂ hfg₁ hf₁ hg₁ hfg₂ hf₂ hg₂ hfg₃ hf₃ hg₃ E,
      ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have keyW : (smallEtaleDerivedModulePullbackCompIso B W hW f₁ f₂).hom.app
        ((P.equivalence h ε₃).functor.obj E) ≫
      (smallEtaleDerivedModulePullback B W hW (f₁ ≫ f₂)).map u ≫
        (smallEtaleDerivedModulePullbackCompIso B W hW f₁ f₂ ≪≫
          smallEtaleDerivedModulePullbackCongr B W hW rfl).inv.app K'' =
      (smallEtaleDerivedModulePullback B W hW f₁).map
        ((smallEtaleDerivedModulePullback B W hW f₂).map u) := by
    rw [← Category.assoc, ← (smallEtaleDerivedModulePullbackCompIso B W hW f₁ f₂).hom.naturality u,
      Iso.trans_inv, smallEtaleDerivedModulePullbackCongr, eqToIso_refl, Iso.refl_inv,
      Category.id_comp, Functor.comp_map, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have nat₁ := ((P.pullbackIso h ε₁ ε₂ f₁ g₁ hfg₁ hf₁ hg₁).hom.naturality a).symm
  simp only [Functor.comp_map] at nat₁
  rw [eqToHom_refl, Category.id_comp, hc, key₁, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% keyW, ← Functor.map_comp_assoc (smallEtaleDerivedModulePullback B W hW f₁),
    ← Functor.map_comp_assoc (smallEtaleDerivedModulePullback B W hW f₁),
    Category.assoc ((P.pullbackIso h ε₂ ε₃ f₂ g₂ hfg₂ hf₂ hg₂).hom.app E), ← ha,
    reassoc_of% nat₁, Iso.hom_inv_id_app_assoc]

end SmallerBaseDerivedComparison

/-- A composite of fibre morphisms along the composition comparison of
`AlgebraicGeometry.Space.ComplexesSituation`, read through the composition isomorphism of
Stacks 0D6D: the form in which the compatibility of Stacks 0DIQ at `X_T ⟶ T` is checked. -/
theorem fibreComp_compComparison_eq (P : SmallerBaseDerivedComparison B S hS)
    {T₁ T₂ T₃ : SchemesOver D.Y} (k : T₁ ⟶ T₂) (k' : T₂ ⟶ T₃) {k₃ : T₁ ⟶ T₃}
    (e : k ≫ k' = k₃) (hk : D.relativeMap k ≫ D.relativeMap k' = D.relativeMap k₃)
    {E : derivedModules B S hS (D.space T₃)} {A : derivedModules B S hS (D.space T₂)}
    {B' : derivedModules B S hS (D.space T₁)}
    (a : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k')).obj E ⟶ A)
    (b : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj A ⟶ B')
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k₃)).obj E ⟶ B')
    (h : (smallEtaleDerivedModulePullbackCompIso B S hS (D.relativeMap k)
          (D.relativeMap k')).inv.app E ≫
        (smallEtaleDerivedModulePullback B S hS (D.relativeMap k)).map a ≫ b =
      eqToHom (congrArg (fun m => (smallEtaleDerivedModulePullback B S hS m).obj E) hk) ≫ c) :
    Functor.fibreComp (D.compComparison k k') b a =
      (D.relativeMapComparison e).hom.app E ≫ c := by
  subst e
  refine (P.fibreComp_triangle_eq_of (baseChangeMap_comp D.f k k').symm rfl a b c h).trans ?_
  rw [relativeMapComparison_hom_app]

namespace SpecLimitTower

variable {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
  (L : D.SpecLimitTower level transition) (P : SmallerBaseDerivedComparison B S hS)

/-- `D(𝒪_{X_{T_n}}) ≌ D(𝒪_{X_n})`, through `Λ X_n ≅ X_{T_n}`. -/
abbrev stageEquivalence (n : ℕ) :
    toposDerived (D.space (level n)) ≌ toposDerived (L.stageSpace n) :=
  P.equivalence L.limitBaseHom (L.stageSpaceRelocalizeIso n)

/-- `D(𝒪_{X_T}) ≌ D(𝒪_X)`, through `Λ X ≅ X_T`. -/
abbrev limitEquivalence :
    toposDerived (D.space L.T) ≌ toposDerived L.limitSpaceOver.left :=
  P.equivalence L.limitBaseHom L.limitSpaceRelocalizeIso

/-- The equivalences commute with derived pullback along `X_n ⟶ X_{n+1}`. -/
abbrev transitionPullbackIso (n : ℕ) :=
  P.pullbackIso L.limitBaseHom (L.stageSpaceRelocalizeIso n) (L.stageSpaceRelocalizeIso (n + 1))
    (transitionSpace L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver n)
    (D.relativeMap (transition n)) (L.stageSpaceRelocalizeIso_hom_relativeMap_transition n)
    (L.relativelyRepresentable_transitionSpace n)
    (relativelyRepresentable_relativeMap (transition n))

/-- The equivalences commute with derived pullback along `X_n ⟶ X`. -/
abbrev projectionPullbackIso (n : ℕ) :=
  P.pullbackIso L.limitBaseHom (L.stageSpaceRelocalizeIso n) L.limitSpaceRelocalizeIso
    (spaceProjection L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver n)
    (D.relativeMap (L.toLimit n)) (L.stageSpaceRelocalizeIso_hom_relativeMap_toLimit n)
    (L.relativelyRepresentable_spaceProjection n)
    (relativelyRepresentable_relativeMap (L.toLimit n))

/-- **B6, the system: Situation 0DIK at `X_T ⟶ T`.**  For pseudo-coherent `K_n` on `X_{T_n}`
with isomorphisms `φ_n : L(X_{T_n} ⟶ X_{T_{n+1}})^* K_{n+1} ⟶ K_n`, the system of Situation
0DIK over `lim R_n` with `X = X_T` read over `Spec (lim R_n)`, and the `K_n`, `φ_n` carried to its
infinitesimal base changes. -/
abbrev derivedExistenceSystem (K : ∀ n, derivedModules B S hS (D.space (level n)))
    (hK : ∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
      (D.space (level n)).2).IsPseudoCoherent (K n))
    (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n) (hφ : ∀ n, IsIso (φ n)) :
    DerivedExistenceSystem.{u} where
  system := L.R
  transition_surjective := L.surjective
  transition_locallyNilpotent := L.locallyNilpotent
  B := B
  containsLimitBase := L.contains_limitBase
  containsBaseAt := L.contains_baseAt
  X := L.limitSpaceOver
  proper := L.isProper_isFlat_isFinitePresentation_limitSpaceOver.1
  flat := L.isProper_isFlat_isFinitePresentation_limitSpaceOver.2.1
  finitePresentation := L.isProper_isFlat_isFinitePresentation_limitSpaceOver.2.2
  K n := (L.stageEquivalence P n).functor.obj (K n)
  pseudoCoherent n := (P.isPseudoCoherent_iff _ _ _).2 (hK n)
  φ n := (L.transitionPullbackIso P n).inv.app (K (n + 1)) ≫
    (L.stageEquivalence P n).functor.map (φ n)
  φ_isIso n :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ ((L.transitionPullbackIso P n).app (K (n + 1))).isIso_inv
      ((L.stageEquivalence P n).functor.mapIso (@asIso _ _ _ _ (φ n) (hφ n))).isIso_hom

/-- The composition isomorphism `Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` of the system at `X_T ⟶ T`
(`AlgebraicGeometry.Space.DerivedExistenceSystem.stageDerivedPullbackCompIso`) is, by definition,
the composition isomorphism of Stacks 0D6D followed by `iₙ ≫ jₙ₊₁ = jₙ`, at `X_n ⟶ X_{n+1} ⟶ X`. -/
theorem stageDerivedPullbackCompIso_eq (K : ∀ n, derivedModules B S hS (D.space (level n)))
    (hK : ∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
      (D.space (level n)).2).IsPseudoCoherent (K n))
    (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n) (hφ : ∀ n, IsIso (φ n)) (n : ℕ) :
    (L.derivedExistenceSystem P K hK φ hφ).stageDerivedPullbackCompIso n =
      smallEtaleDerivedModulePullbackCompIso B (limitBase L.R) L.contains_limitBase
          (transitionSpace L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver n)
          (spaceProjection L.R B L.contains_limitBase L.contains_baseAt L.limitSpaceOver
            (n + 1)) ≪≫
        smallEtaleDerivedModulePullbackCongr B (limitBase L.R) L.contains_limitBase
          (transitionSpace_spaceProjection L.R B L.contains_limitBase L.contains_baseAt
            L.limitSpaceOver n) :=
  rfl

include P in
/-- **B6: Stacks 0DIQ for systems gives Stacks 0DIQ at `X_T ⟶ T`.**  Let `h0DIQ` be the
conclusion of Stacks 0DIQ for every system of Situation 0DIK, in the form stated for
`AlgebraicGeometry.Space.DerivedExistenceSystem`: a pseudo-coherent `K` on `X` with isomorphisms
`ψ_n : Lj_n^* K ≅ K_n`, `ψ_n = (Lj_n^* ≅ Li_n^* Lj_{n+1}^*) ≫ Li_n^* ψ_{n+1} ≫ φ_n`).
Then for pseudo-coherent `K_n` on `X_{T_n}` with isomorphisms
`φ_n : L(X_{T_n} ⟶ X_{T_{n+1}})^* K_{n+1} ⟶ K_n` there is a pseudo-coherent `E` on `X_T` with
isomorphisms `ψ_n : L(X_{T_n} ⟶ X_T)^* E ⟶ K_n` compatible with the `φ_n`: the hypothesis `h0DIQ`
of `AlgebraicGeometry.Space.ComplexesSituation.exists_realization_of_specLimitTower` at `L`.

* `h0DIQ`: Stacks 0DIQ, not yet proved here.  Stated inline
  (its `IsPseudoCoherentOnLimit` and `IsCompatibleRestriction` unfolded, these not being on the
  library yet), so that a proof of Stacks 0DIQ discharges this hypothesis directly.
* `P`: internal, B3–B5
  (`AlgebraicGeometry.Space.ComplexesSituation.SmallerBaseDerivedComparison`), filled by
  `AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`.

The system is `AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.derivedExistenceSystem`:
`X_T` read over `Spec (lim R_n)` (B1), whose infinitesimal base changes are the `X_{T_n}` (B2),
with the `K_n` and `φ_n` carried along the equivalences of `P`.  The `E` is the object of
`D(𝒪_{X_T})` corresponding to the `K` of `h0DIQ`, and the `ψ_n` are those of `h0DIQ`, carried
back. -/
theorem exists_restriction_of_derivedExistence
    (h0DIQ : ∀ DS : DerivedExistenceSystem.{u},
      ∃ (K : DS.limitDerivedCategory) (ψ : ∀ n : ℕ, (DS.stageDerivedPullback n).obj K ≅ DS.K n),
        (letI : HasDerivedCategory.{u + 1} (DS.toposModules DS.X.left) :=
            HasDerivedCategory.standard _;
          RingedSite.IsPseudoCoherent.{u + 1, u, u, u, u + 1}
            (RingedTopos.toRingedSite
              (smallEtaleRingedTopos DS.B (limitBase DS.system) DS.containsLimitBase DS.X.left))
            K) ∧
        ∀ n : ℕ, (ψ n).hom = (DS.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback DS.system DS.B DS.containsLimitBase DS.containsBaseAt DS.X
            n).map (ψ (n + 1)).hom ≫ DS.φ n)
    (K : ∀ n, derivedModules B S hS (D.space (level n)))
    (hK : ∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
      (D.space (level n)).2).IsPseudoCoherent (K n))
    (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n) (hφ : ∀ n, IsIso (φ n)) :
    ∃ (E : derivedModules B S hS (D.space L.T)),
      (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
      ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
        ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
            (ψ (n + 1)) =
          (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n := by
  obtain ⟨K', ψ', hpc, hc⟩ := h0DIQ (L.derivedExistenceSystem P K hK φ hφ)
  let θ : ∀ n, (L.stageEquivalence P n).functor.obj
      ((smallEtaleDerivedModulePullback B S hS (D.relativeMap (L.toLimit n))).obj
        ((L.limitEquivalence P).inverse.obj K')) ≅ (L.stageEquivalence P n).functor.obj (K n) :=
    fun n => (L.projectionPullbackIso P n).app ((L.limitEquivalence P).inverse.obj K') ≪≫
      (smallEtaleDerivedModulePullback B _ _ (spaceProjection L.R B L.contains_limitBase
        L.contains_baseAt L.limitSpaceOver n)).mapIso ((L.limitEquivalence P).counitIso.app K') ≪≫
      ψ' n
  obtain ⟨ψ, hψ, hψi⟩ : ∃ ψ : ∀ n, (smallEtaleDerivedModulePullback B S hS
      (D.relativeMap (L.toLimit n))).obj ((L.limitEquivalence P).inverse.obj K') ⟶ K n,
      (∀ n, (L.stageEquivalence P n).functor.map (ψ n) = (θ n).hom) ∧ ∀ n, IsIso (ψ n) :=
    ⟨fun n => ((L.stageEquivalence P n).fullyFaithfulFunctor.preimageIso (θ n)).hom,
      fun n => (L.stageEquivalence P n).fullyFaithfulFunctor.map_preimage _,
      fun n => ((L.stageEquivalence P n).fullyFaithfulFunctor.preimageIso (θ n)).isIso_hom⟩
  refine ⟨(L.limitEquivalence P).inverse.obj K', ?_, ψ, hψi, fun n => ?_⟩
  · refine (P.isPseudoCoherent_iff L.limitBaseHom L.limitSpaceRelocalizeIso _).1 ?_
    obtain ⟨M, hM, ⟨e⟩⟩ := hpc
    exact ⟨M, hM, ⟨Iso.trans (C := toposDerived L.limitSpaceOver.left) e
      ((L.limitEquivalence P).counitIso.app K').symm⟩⟩
  · have hk := L.relativeMap_transition_comp_toLimit n
    have L1 := P.compIso_inv_comp_map_eq (K'' := K') L.limitBaseHom
      (transitionSpace_spaceProjection L.R B L.contains_limitBase L.contains_baseAt
        L.limitSpaceOver n) hk
      (L.stageSpaceRelocalizeIso_hom_relativeMap_transition n)
      (L.relativelyRepresentable_transitionSpace n)
      (relativelyRepresentable_relativeMap (transition n))
      (L.stageSpaceRelocalizeIso_hom_relativeMap_toLimit (n + 1))
      (L.relativelyRepresentable_spaceProjection (n + 1))
      (relativelyRepresentable_relativeMap (L.toLimit (n + 1)))
      (L.stageSpaceRelocalizeIso_hom_relativeMap_toLimit n)
      (L.relativelyRepresentable_spaceProjection n)
      (relativelyRepresentable_relativeMap (L.toLimit n))
      (ψ (n + 1)) (φ n) (ψ n)
      ((L.limitEquivalence P).counitIso.hom.app K') (ψ' (n + 1)).hom (ψ' n).hom
      (hψ (n + 1)) (hψ n) _ (L.stageDerivedPullbackCompIso_eq P K hK φ hφ n)
      (hc n)
    exact fibreComp_compComparison_eq P (transition n) (L.toLimit (n + 1))
      (L.transition_toLimit n) hk (ψ (n + 1)) (φ n) (ψ n) L1


end SpecLimitTower


/-! ### Stacks 0DLM from Stacks 0DIQ -/

section Formal

open Deformation.Artin

attribute [local instance] complexesCategory

variable (D) in
/-- **Stacks 0DLM, condition (3) of Stacks 07Y4, with Stacks 0DIQ**:
`AlgebraicGeometry.Space.ComplexesSituation.isEffective_formalObject_of` with its hypothesis
`h0DIQ` at `X_T ⟶ T` discharged by
`AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.exists_restriction_of_derivedExistence`.
For `Y = S`, every formal object of `Complexes_{X/S}` is effective.

* `h0DIQ`: Stacks 0DIQ, not yet proved here.  Stated inline
  (`AlgebraicGeometry.Space.DerivedExistenceSystem.IsPseudoCoherentOnLimit` and
  `IsCompatibleRestriction` unfolded, these not being on the base yet).
* `P`: internal, B3–B5
  (`AlgebraicGeometry.Space.ComplexesSituation.SmallerBaseDerivedComparison`), filled by
  `AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`.
* `h0DLC`: Stacks 0DLC, clause (1), pending with 0DLC (needs Stacks 0DKY and 0DKX, not yet proved
  here). -/
theorem isEffective_formalObject_of_derivedExistence
    (h0DIQ : ∀ DS : DerivedExistenceSystem.{u},
      ∃ (K : DS.limitDerivedCategory) (ψ : ∀ n : ℕ, (DS.stageDerivedPullback n).obj K ≅ DS.K n),
        (letI : HasDerivedCategory.{u + 1} (DS.toposModules DS.X.left) :=
            HasDerivedCategory.standard _;
          RingedSite.IsPseudoCoherent.{u + 1, u, u, u, u + 1}
            (RingedTopos.toRingedSite
              (smallEtaleRingedTopos DS.B (limitBase DS.system) DS.containsLimitBase DS.X.left))
            K) ∧
        ∀ n : ℕ, (ψ n).hom = (DS.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback DS.system DS.B DS.containsLimitBase DS.containsBaseAt DS.X
            n).map (ψ (n + 1)).hom ≫ DS.φ n)
    (P : SmallerBaseDerivedComparison B S hS) (h0DLC : ExistsNegativeExtLocus B S hS)
    (hY : IsTerminal D.Y) (ξ : FormalObject B S hS (complexesFunctor D)) :
    FormalObject.IsEffective B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D)
      ξ :=
  D.isEffective_formalObject_of
    (fun L K hK φ hφ => L.exists_restriction_of_derivedExistence P h0DIQ K hK φ hφ) h0DLC hY ξ

variable (D) in
/-- **Stacks 0DLM: `Complexes_{X/S}` is strongly formally effective (Stacks 0CXT), with Stacks
0DIQ**:
`AlgebraicGeometry.Space.ComplexesSituation.isStronglyFormallyEffective_complexes_of` with its
hypothesis `h0DIQ` at `X_T ⟶ T` discharged by
`AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.exists_restriction_of_derivedExistence`.

* `h0DIQ`: Stacks 0DIQ, not yet proved here.  Stated inline
  (`AlgebraicGeometry.Space.DerivedExistenceSystem.IsPseudoCoherentOnLimit` and
  `IsCompatibleRestriction` unfolded, these not being on the base yet).
* `P`: internal, B3–B5
  (`AlgebraicGeometry.Space.ComplexesSituation.SmallerBaseDerivedComparison`), filled by
  `AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`.
* `h0DLC`: Stacks 0DLC, clause (1), pending with 0DLC (needs Stacks 0DKY and 0DKX, not yet proved
  here). -/
theorem isStronglyFormallyEffective_complexes_of_derivedExistence
    (h0DIQ : ∀ DS : DerivedExistenceSystem.{u},
      ∃ (K : DS.limitDerivedCategory) (ψ : ∀ n : ℕ, (DS.stageDerivedPullback n).obj K ≅ DS.K n),
        (letI : HasDerivedCategory.{u + 1} (DS.toposModules DS.X.left) :=
            HasDerivedCategory.standard _;
          RingedSite.IsPseudoCoherent.{u + 1, u, u, u, u + 1}
            (RingedTopos.toRingedSite
              (smallEtaleRingedTopos DS.B (limitBase DS.system) DS.containsLimitBase DS.X.left))
            K) ∧
        ∀ n : ℕ, (ψ n).hom = (DS.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback DS.system DS.B DS.containsLimitBase DS.containsBaseAt DS.X
            n).map (ψ (n + 1)).hom ≫ DS.φ n)
    (P : SmallerBaseDerivedComparison B S hS) (h0DLC : ExistsNegativeExtLocus B S hS)
    [IsLocallyNoetherian S] (hY : IsTerminal D.Y) :
    IsStronglyFormallyEffective B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  D.isStronglyFormallyEffective_complexes_of
    (fun L K hK φ hφ => L.exists_restriction_of_derivedExistence P h0DIQ K hK φ hφ) h0DLC hY

end Formal

end AlgebraicGeometry.Space.ComplexesSituation

end
