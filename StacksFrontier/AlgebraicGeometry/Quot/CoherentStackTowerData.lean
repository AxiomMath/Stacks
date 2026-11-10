module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSquareZeroEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeSiteChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Existence
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The data of a tower of thickenings in `Coh_{X/Y}`

The hypotheses of `AlgebraicGeometry.Space.CoherentSituation.TowerExistence` — an inverse system
`Aₙ` of algebras with surjective square-zero transitions, a test scheme `T` over `Y` identified
with `Spec (lim Aₙ)`, and a system `ξₙ` of objects of `Coh_{X/Y}` over the `Spec Aₙ` mapping to
`T` — bundled, together with the first constructions towards Grothendieck's existence theorem
(Stacks 0CXB): the inverse-limit base `Spec (lim Aₙ)` as an object of the site, its morphism to
`S`, and the base change `X_T` as an algebraic space over it (Stacks 04SG).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- `Coh_{X/Y}` as a category, the category structure of
`AlgebraicGeometry.Space.CoherentSituation.TowerExistence`. -/
abbrev towerCategory : Category.{u + 1} (CoherentObject D) := D.categoryData.category

attribute [local instance] towerCategory

/-- **The data of a tower of thickenings in `Coh_{X/Y}`**, the hypotheses of
`AlgebraicGeometry.Space.CoherentSituation.TowerExistence`. -/
structure TowerData where
  /-- The base ring. -/
  Λ : Type u
  [commRing : CommRing Λ]
  /-- The inverse system of algebras. -/
  R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ
  /-- Its limit cone. -/
  cR : Cone R
  /-- It is a limit. -/
  hcR : IsLimit cR
  /-- The transitions are surjective. -/
  hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom
  /-- The transitions have square-zero kernels. -/
  hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (RingHom.ker (R.map f).hom.toRingHom) ^ 2 = ⊥
  /-- The test scheme over the limit. -/
  T : SchemesOver D.Y
  /-- Its identification with the spectrum of the limit. -/
  eT : (BigFppfOver.toScheme B S hS).obj T.left ≅ Spec (.of cR.pt)
  /-- The system of objects. -/
  ξ : ℕ ⥤ CoherentObject D
  /-- Their maps to the test scheme over the limit. -/
  b : ∀ n, (ξ.obj n).T ⟶ T
  /-- The maps are compatible with the transitions. -/
  hb : ∀ n, (show CoherentHom (ξ.obj n) (ξ.obj (n + 1)) from
    ξ.map (homOfLE (n.le_add_right 1))).base ≫ b (n + 1) = b n
  /-- The identifications of the test schemes with the spectra. -/
  e : ∀ n, (BigFppfOver.toScheme B S hS).obj (ξ.obj n).T.left ≅ Spec (.of (R.obj (op n)))
  /-- The transitions are the transitions of the system. -/
  he : ∀ n, (BigFppfOver.toScheme B S hS).map
      (show CoherentHom (ξ.obj n) (ξ.obj (n + 1)) from
        ξ.map (homOfLE (n.le_add_right 1))).base.left ≫ (e (n + 1)).hom =
    (e n).hom ≫ Spec.map (CommRingCat.ofHom (R.map (homOfLE (n.le_add_right 1)).op).hom.toRingHom)
  /-- The maps are the thickenings. -/
  hbT : ∀ n, (BigFppfOver.toScheme B S hS).map (b n).left ≫ eT.hom =
    (e n).hom ≫ Spec.map (CommRingCat.ofHom (cR.π.app (op n)).hom.toRingHom)

namespace TowerData

variable {D} (τ : TowerData D)

attribute [instance] commRing

/-- The inverse system of rings underlying the system of algebras. -/
abbrev ringSystem : ℕᵒᵖ ⥤ CommRingCat.{u} := τ.R ⋙ forget₂ (CommAlgCat.{u} τ.Λ) CommRingCat.{u}

/-- The categorical limit of the inverse system of rings is the limit of the algebras. -/
def limitIso : limit τ.ringSystem ≅ CommRingCat.of τ.cR.pt :=
  (limit.isLimit _).conePointUniqueUpToIso (CommAlgCat.isLimitForget₂CommRingCat τ.hcR)

/-- The inverse-limit base is the scheme of the test scheme over the limit. -/
def specLimitIso : limitBase τ.ringSystem ≅ (BigFppfOver.toScheme B S hS).obj τ.T.left :=
  (asIso (Spec.map τ.limitIso.hom)).symm ≪≫ τ.eT.symm

/-- The inverse-limit base `Spec (lim Aₙ)` lies in the site. -/
theorem contains_limitBase : B.Contains (limitBase τ.ringSystem) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact τ.specLimitIso.hom) τ.T.left.left.2

/-- The affine base `Spec Aₙ` at level `n` lies in the site. -/
theorem contains_baseAt (n : ℕ) : B.Contains (baseAt τ.ringSystem n) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (τ.e n).inv) (τ.ξ.obj n).T.left.left.2

/-- The morphism of the site from the inverse-limit base to `S`. -/
def baseMor : B.obj τ.contains_limitBase ⟶ B.obj hS :=
  ObjectProperty.homMk (τ.specLimitIso.hom ≫ B.inclusion.map τ.T.left.hom)

/-- The inverse-limit base, as an object of the site over `S`, is the test scheme over the
limit. -/
def testIso : (Over.mk τ.baseMor : BigFppfOver B S hS) ≅ τ.T.left :=
  Over.isoMk (ObjectProperty.isoMk _ τ.specLimitIso) (ObjectProperty.hom_ext _ rfl)

/-- The base change `X_T`, with its morphism to the inverse-limit base. -/
def toBase : D.space τ.T ⟶ schemeSpace (Over.mk τ.baseMor) :=
  D.projection τ.T ≫ (schemeSpaceFunctor B S hS).map τ.testIso.inv

/-- `X_T` is the base change of `f` along the inverse-limit base, with `toBase` as projection. -/
theorem isPullback_toBase :
    IsPullback (baseChangeProjection D.f τ.T) τ.toBase D.f
      ((schemeSpaceFunctor B S hS).map τ.testIso.hom ≫ τ.T.hom) := by
  refine IsPullback.of_iso (isPullback_baseChangeSpace D.f τ.T) (Iso.refl _) (Iso.refl _)
    ((schemeSpaceFunctor B S hS).mapIso τ.testIso.symm) (Iso.refl _) (by simp) ?_ ?_ ?_
  · simp [toBase]
  · simp
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact (((schemeSpaceFunctor B S hS).mapIso τ.testIso).inv_hom_id_assoc _).symm

/-- If `f` is separated, then so is `X_T ⟶ Spec (lim Aₙ)`. -/
theorem isSeparated_toBase (hsep : IsSeparated B S hS D.f.hom) :
    IsSeparated B S hS τ.toBase.hom :=
  isSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS τ.isPullback_toBase) hsep

/-- The morphism `X_T ⟶ Spec (lim Aₙ)` is of finite presentation. -/
theorem isFinitePresentation_toBase : IsFinitePresentation B S hS τ.toBase.hom :=
  IsFinitePresentation.of_isPullback B S hS (D.space τ.T).2 D.X.2
    (schemeSpace (Over.mk τ.baseMor)).2 D.Y.2
    (AlgebraicSpaces.isPullback_hom B S hS τ.isPullback_toBase) D.finitePresentation

/-! ### The affine bases -/

/-- `limitIso` followed by the projection of the limit cone to level `n` is the limit projection
of the inverse system of rings. -/
theorem limitIso_hom_π (n : ℕ) :
    τ.limitIso.hom ≫ CommRingCat.ofHom (τ.cR.π.app (op n)).hom.toRingHom =
      limit.π τ.ringSystem (op n) :=
  (limit.isLimit _).conePointUniqueUpToIso_hom_comp
    (CommAlgCat.isLimitForget₂CommRingCat τ.hcR) (op n)

/-- The affine base at level `n`, mapped to the inverse-limit base and read on the test scheme,
is the map of test schemes `b n`. -/
theorem baseProjection_specLimitIso_hom (n : ℕ) :
    GrothendieckExistence.baseProjection τ.ringSystem n ≫ τ.specLimitIso.hom =
      (τ.e n).inv ≫ (BigFppfOver.toScheme B S hS).map (τ.b n).left := by
  have h1 : (τ.e n).inv ≫ (BigFppfOver.toScheme B S hS).map (τ.b n).left =
      Spec.map (CommRingCat.ofHom (τ.cR.π.app (op n)).hom.toRingHom) ≫ τ.eT.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← τ.hbT n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [h1]
  change Spec.map (limit.π τ.ringSystem (op n)) ≫ inv (Spec.map τ.limitIso.hom) ≫ τ.eT.inv = _
  rw [← τ.limitIso_hom_π n, Spec.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]

/-- The transitions of the affine bases are the transitions of the test schemes. -/
theorem baseTransition_e_inv (n : ℕ) :
    GrothendieckExistence.baseTransition τ.ringSystem n ≫ (τ.e (n + 1)).inv =
      (τ.e n).inv ≫ (BigFppfOver.toScheme B S hS).map
        (show CoherentHom (τ.ξ.obj n) (τ.ξ.obj (n + 1)) from
          τ.ξ.map (homOfLE (n.le_add_right 1))).base.left := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (τ.he n).symm

/-- **The affine base at level `n`, read over `S`, is the test scheme of `ξ n`.** -/
def baseObjectIso (n : ℕ) :
    (Over.map τ.baseMor).obj
        (baseObjectAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n) ≅
      (τ.ξ.obj n).T.left :=
  Over.isoMk (ObjectProperty.isoMk _ (τ.e n).symm) (by
    apply ObjectProperty.hom_ext
    have hw : ((τ.b n).left.left ≫ τ.T.left.hom).hom = (τ.ξ.obj n).T.left.hom.hom :=
      congrArg (fun m => m.hom) (Over.w (τ.b n).left)
    change (τ.e n).inv ≫ (τ.ξ.obj n).T.left.hom.hom =
      GrothendieckExistence.baseProjection τ.ringSystem n ≫ τ.specLimitIso.hom ≫ τ.T.left.hom.hom
    rw [← hw, ← Category.assoc, τ.baseProjection_specLimitIso_hom]
    rfl)

/-- The map of the test scheme of `ξ n` to the inverse-limit base. -/
abbrev testMap (n : ℕ) : (τ.ξ.obj n).T.left ⟶ Over.mk τ.baseMor := (τ.b n).left ≫ τ.testIso.inv

/-- Under `baseObjectIso`, the map of the test scheme of `ξ n` to the inverse-limit base is the
structure morphism of the affine base at level `n`. -/
theorem baseObjectIso_hom_testMap (n : ℕ) :
    (τ.baseObjectIso n).hom ≫ τ.testMap n =
      (Over.homMk (baseObjectAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n).hom rfl :
        (Over.map τ.baseMor).obj
          (baseObjectAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n) ⟶
            Over.mk τ.baseMor) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change (τ.e n).inv ≫ (τ.b n).left.left.hom ≫ τ.specLimitIso.inv =
    GrothendieckExistence.baseProjection τ.ringSystem n
  rw [← Category.assoc]
  change (τ.e n).inv ≫ (BigFppfOver.toScheme B S hS).map (τ.b n).left ≫ τ.specLimitIso.inv = _
  rw [← Category.assoc, ← τ.baseProjection_specLimitIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- `baseObjectIso` intertwines the transitions of the affine bases with the transitions of the
test schemes of `ξ`. -/
theorem baseObjectIso_hom_transition (n : ℕ) :
    (τ.baseObjectIso n).hom ≫
        (show CoherentHom (τ.ξ.obj n) (τ.ξ.obj (n + 1)) from
          τ.ξ.map (homOfLE (n.le_add_right 1))).base.left =
      (Over.map τ.baseMor).map
          (baseObjectTransition τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n) ≫
        (τ.baseObjectIso (n + 1)).hom :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (τ.baseTransition_e_inv n).symm)

/-! ### `X_T` as an algebraic space over the inverse-limit base -/

/-- **`X_T` as an algebraic space over the inverse-limit base** (Stacks 04SG). -/
abbrev siteSpace : AlgebraicSpaces B (limitBase τ.ringSystem) τ.contains_limitBase :=
  siteChangeSpace B (D.space τ.T) τ.toBase

/-- The structure morphism of `X_T` over the inverse-limit base. -/
def siteStructure :
    τ.siteSpace ⟶ schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase) :=
  (terminalSpace_unique B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteSpace).default

/-- `X_T` as an object over the inverse-limit base, the space of Stacks 0CX4. -/
abbrev siteOver : Over (schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase)) :=
  Over.mk τ.siteStructure

/-- The structure morphism `Λ (Spec A) ⟶ Spec A`, read over `S`. -/
abbrev limitTargetMap :
    (OverShriek.relocalizePresheafFunctor τ.baseMor).obj
        (schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase)).1 ⟶
      yoneda.obj (Over.mk τ.baseMor) :=
  OverShriek.relocalizeToYoneda τ.baseMor
    (schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase)).1

/-- The structure morphism `limitTargetMap` is an isomorphism. -/
theorem isIso_limitTargetMap : IsIso τ.limitTargetMap :=
  isIso_relocalizeToYoneda_yonedaId B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor

/-- **The structure morphism of `X_T` over `Spec A`, extended back to `S`, is `X_T ⟶ Spec A`.** -/
theorem relocalize_siteStructure_comp :
    (OverShriek.relocalizePresheafFunctor τ.baseMor).map τ.siteStructure.hom ≫ τ.limitTargetMap =
      (siteChangeIso B (D.space τ.T) τ.toBase).hom.hom ≫ τ.toBase.hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, siteChangeIso_hom_comp]
  exact relocalizeToYoneda_naturality B (limitBase τ.ringSystem) S τ.contains_limitBase hS
    τ.baseMor _

/-- If `f` is separated, then `X_T` is separated over the inverse-limit base. -/
theorem isSeparatedOver_siteSpace (hsep : IsSeparated B S hS D.f.hom) :
    IsSeparatedOver B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteOver.left.1 := by
  have := τ.isIso_limitTargetMap
  have h2 : IsSeparated B S hS
      ((OverShriek.relocalizePresheafFunctor τ.baseMor).map τ.siteStructure.hom ≫
        τ.limitTargetMap) := by
    rw [τ.relocalize_siteStructure_comp]
    exact (isSeparated_isIso_comp_iff B S hS _ _).2 (τ.isSeparated_toBase hsep)
  exact (isSeparatedOver_iff_isSeparated_of_isTerminal B (limitBase τ.ringSystem)
    τ.contains_limitBase
    (baseTerminal_yonedaIsTerminal B (limitBase τ.ringSystem) τ.contains_limitBase)
    τ.siteStructure.hom).2
    (isSeparated_of_relocalizeMap B (limitBase τ.ringSystem) S τ.contains_limitBase hS
      τ.baseMor _ ((isSeparated_comp_isIso_iff B S hS _ τ.limitTargetMap).1 h2))

/-- The extended structure morphism of `X_T` over the inverse-limit base is `X_T ⟶ Spec A`. -/
theorem isPullback_relocalize_siteStructure :
    IsPullback (siteChangeIso B (D.space τ.T) τ.toBase).hom.hom
      ((OverShriek.relocalizePresheafFunctor τ.baseMor).map τ.siteStructure.hom)
      τ.toBase.hom τ.limitTargetMap :=
  have := τ.isIso_limitTargetMap
  IsPullback.of_horiz_isIso (CommSq.mk τ.relocalize_siteStructure_comp.symm)

/-- The structure morphism of `X_T` over the inverse-limit base is of finite presentation. -/
theorem isFinitePresentation_siteStructure :
    IsFinitePresentation B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteStructure.hom := by
  have h := IsFinitePresentation.of_isPullback B S hS
    (relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
      τ.siteSpace).2 (D.space τ.T).2
    (relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
      (schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase))).2
    (schemeSpace (Over.mk τ.baseMor)).2 τ.isPullback_relocalize_siteStructure
    τ.isFinitePresentation_toBase
  exact ⟨(Space.holdsOnEveryEtaleChart_relocalizeMap_iff B (limitBase τ.ringSystem) S
      τ.contains_limitBase hS τ.baseMor _ τ.siteStructure.hom).1 h.1,
    (isQuasiCompact_relocalize_iff B (limitBase τ.ringSystem) τ.contains_limitBase S hS
      τ.baseMor _).1 h.2.1,
    (isQuasiSeparated_relocalize_iff B (limitBase τ.ringSystem) τ.contains_limitBase S hS
      τ.baseMor _).1 h.2.2⟩

/-! ### The infinitesimal base changes of `X_T`, read over `S` -/

/-- `Λ` of the affine base at level `n` is the test scheme of `ξ n`. -/
def basePresheafIso (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor τ.baseMor).obj
        (yoneda.obj (baseObjectAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n)) ≅
      yoneda.obj (τ.ξ.obj n).T.left :=
  (OverShriek.relocalizeYonedaIso τ.baseMor).app _ ≪≫ yoneda.mapIso (τ.baseObjectIso n)

/-- The projection of the affine base at level `n` to the inverse-limit base, extended back to
`S`, is the map of the test scheme of `ξ n` to the inverse-limit base, under `basePresheafIso`. -/
theorem relocalize_baseSpaceProjection_comp (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor τ.baseMor).map
        (baseSpaceProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n).hom ≫
        τ.limitTargetMap = (τ.basePresheafIso n).hom ≫ yoneda.map (τ.testMap n) := by
  refine (relocalizeToYoneda_naturality B (limitBase τ.ringSystem) S τ.contains_limitBase hS
    τ.baseMor _).trans ?_
  refine (AlgebraicGeometry.Stack.relocalizeToYoneda_yoneda τ.baseMor _).symm.trans ?_
  rw [basePresheafIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp,
    baseObjectIso_hom_testMap]

/-- `basePresheafIso` intertwines the extended transitions of the affine bases with the transitions
of the test schemes of `ξ`. -/
theorem relocalize_baseSpaceTransition_comp (n : ℕ) :
    (OverShriek.relocalizePresheafFunctor τ.baseMor).map
        (baseSpaceTransition τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n).hom ≫
        (τ.basePresheafIso (n + 1)).hom =
      (τ.basePresheafIso n).hom ≫ yoneda.map
        (show CoherentHom (τ.ξ.obj n) (τ.ξ.obj (n + 1)) from
          τ.ξ.map (homOfLE (n.le_add_right 1))).base.left := by
  have hn := (OverShriek.relocalizeYonedaIso τ.baseMor).hom.naturality
    (baseObjectTransition τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [basePresheafIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  change (OverShriek.relocalizePresheafFunctor τ.baseMor).map (yoneda.map
      (baseObjectTransition τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n)) ≫ _ ≫ _ = _
  rw [reassoc_of% hn, ← Functor.map_comp, ← baseObjectIso_hom_transition, Functor.map_comp,
    Category.assoc]

/-- **`Λ` of the infinitesimal base change `Xₙ` of `X_T` sits over `ξ n`**: the square of `Λ Xₙ`
over `X_T` and the test scheme of `ξ n` is cartesian. -/
theorem isPullback_relocalize_spaceAt (n : ℕ) :
    IsPullback
      ((OverShriek.relocalizePresheafFunctor τ.baseMor).map
          (spaceProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n).hom ≫
        (siteChangeIso B (D.space τ.T) τ.toBase).hom.hom)
      ((OverShriek.relocalizePresheafFunctor τ.baseMor).map
          (spaceBaseProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
            τ.siteOver n).hom ≫ (τ.basePresheafIso n).hom)
      τ.toBase.hom (yoneda.map (τ.testMap n)) := by
  have : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor τ.baseMor) :=
    relocalizePresheaf_preservesConnectedLimits τ.baseMor
  have h0 := (AlgebraicSpaces.isPullback_hom B (limitBase τ.ringSystem) τ.contains_limitBase
    (isPullback_spaceAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
      τ.siteOver n).flip).map (OverShriek.relocalizePresheafFunctor τ.baseMor)
  exact h0.of_iso (Iso.refl _)
    ((ObjectProperty.ι _).mapIso (siteChangeIso B (D.space τ.T) τ.toBase))
    (τ.basePresheafIso n)
    (@asIso _ _ _ _ τ.limitTargetMap τ.isIso_limitTargetMap) (by simp) (by simp)
    τ.relocalize_siteStructure_comp (τ.relocalize_baseSpaceProjection_comp n)

/-- The base change `X_{T_n}` sits over `X_T` and the test scheme of `ξ n` in a cartesian
square. -/
theorem isPullback_relativeMap_testMap (n : ℕ) :
    IsPullback (D.relativeMap (τ.b n)).hom (D.projection (τ.ξ.obj n).T).hom τ.toBase.hom
      (yoneda.map (τ.testMap n)) := by
  refine (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f (τ.b n))).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (yoneda.mapIso τ.testIso.symm)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) ?_ ?_
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, testMap, Functor.map_comp]
    rfl

/-- **`Λ Xₙ ≅ X_{T_n}`**: `Λ` of the infinitesimal base change of `X_T` at level `n` is the base
change of `X` to the test scheme of `ξ n`. -/
def levelIso (n : ℕ) :
    relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
        (spaceAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n) ≅
      D.space (τ.ξ.obj n).T :=
  ObjectProperty.isoMk _ ((τ.isPullback_relocalize_spaceAt n).isoIsPullback _ _
    (τ.isPullback_relativeMap_testMap n))

/-- `levelIso` followed by `X_{T_n} ⟶ X_T` is the extended projection of `Xₙ` to `X_T`. -/
theorem levelIso_hom_relativeMap (n : ℕ) :
    (τ.levelIso n).hom ≫ D.relativeMap (τ.b n) =
      relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
          (spaceProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n) ≫
        (siteChangeIso B (D.space τ.T) τ.toBase).hom :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- `levelIso` followed by the projection `X_{T_n} ⟶ T_n` is the extended projection of `Xₙ` to
the affine base at level `n`, read on the test scheme of `ξ n`. -/
theorem levelIso_hom_projection (n : ℕ) :
    (τ.levelIso n).hom ≫ D.projection (τ.ξ.obj n).T =
      relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
          (spaceBaseProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
            τ.siteOver n) ≫
        (ObjectProperty.homMk (τ.basePresheafIso n).hom :
          relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
              (schemeSpace (baseObjectAt τ.ringSystem B τ.contains_limitBase
                τ.contains_baseAt n)) ⟶
            (schemeSpaceFunctor B S hS).obj (τ.ξ.obj n).T.left) :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_snd _ _ _ _)

/-- **The transitions of the infinitesimal base changes are the morphisms of base changes of the
transitions of `ξ`.** -/
theorem relocalize_transitionSpace_levelIso (n : ℕ) :
    relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
        (transitionSpace τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n) ≫
        (τ.levelIso (n + 1)).hom =
      (τ.levelIso n).hom ≫ D.relativeMap
        (show CoherentHom (τ.ξ.obj n) (τ.ξ.obj (n + 1)) from
          τ.ξ.map (homOfLE (n.le_add_right 1))).base := by
  apply (isPullback_baseChangeMap D.f (τ.b (n + 1))).hom_ext
  · rw [Category.assoc, levelIso_hom_relativeMap, ← Category.assoc, ← relocalizeHom_comp,
      transitionSpace_spaceProjection, Category.assoc, ← baseChangeMap_comp, τ.hb n,
      levelIso_hom_relativeMap]
  · have h5 : relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
          (baseSpaceTransition τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n) ≫
          (ObjectProperty.homMk (τ.basePresheafIso (n + 1)).hom :
            relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
                (schemeSpace (baseObjectAt τ.ringSystem B τ.contains_limitBase
                  τ.contains_baseAt (n + 1))) ⟶
              (schemeSpaceFunctor B S hS).obj (τ.ξ.obj (n + 1)).T.left) =
        (ObjectProperty.homMk (τ.basePresheafIso n).hom :
            relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
                (schemeSpace (baseObjectAt τ.ringSystem B τ.contains_limitBase
                  τ.contains_baseAt n)) ⟶
              (schemeSpaceFunctor B S hS).obj (τ.ξ.obj n).T.left) ≫
          (schemeSpaceFunctor B S hS).map
            (show CoherentHom (τ.ξ.obj n) (τ.ξ.obj (n + 1)) from
              τ.ξ.map (homOfLE (n.le_add_right 1))).base.left :=
      ObjectProperty.hom_ext _ (τ.relocalize_baseSpaceTransition_comp n)
    rw [Category.assoc, levelIso_hom_projection, ← Category.assoc, ← relocalizeHom_comp,
      transitionSpace_spaceBaseProjection, relocalizeHom_comp, Category.assoc, h5, Category.assoc,
      baseChangeMap_comp_inclusion, ← Category.assoc]
    exact congrArg (· ≫ _) (τ.levelIso_hom_projection n).symm

end TowerData

end AlgebraicGeometry.Space.CoherentSituation

end
