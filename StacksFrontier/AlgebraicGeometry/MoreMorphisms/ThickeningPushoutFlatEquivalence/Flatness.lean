module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsRingEquivSquare
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutModules
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatEquivalence.GluingFunctor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatEquivalence.ChartRings

/-!
# Sections and relative flatness of the glued module

The sections over an open of a fibre product of modules are the compatible pairs of sections
(`Stacks.Pushout.sectionsPullbackIso`); over an affine chart the sections of the glued module of
a triple are the compatible pairs of a relative Milnor patching situation, and the glued module
of a triple of relatively flat quasi-coherent modules is quasi-coherent and flat over `Y'`
(`Stacks.Pushout.flatQuasicoherent_tripleGluingFunctor_obj`).
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.Pushout

variable {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
  (g : V' ⟶ pushout i f)

variable (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]

/-! ### Sections over an open, and the sections of the glued module -/

/-- Sections over an open, as a functor to modules over the ring of functions on that open. -/
noncomputable abbrev moduleSections (Z : Scheme.{u}) (U : Z.Opens) :
    Z.Modules ⥤ ModuleCat.{u} Γ(Z, U) :=
  _root_.SheafOfModules.evaluation Z.ringCatSheaf (op U)

/-- Sections over an open preserve finite limits. -/
instance moduleSections_preservesFiniteLimits (Z : Scheme.{u}) (U : Z.Opens) :
    PreservesFiniteLimits (moduleSections Z U) := by
  change PreservesFiniteLimits (_root_.SheafOfModules.evaluation Z.ringCatSheaf (op U))
  infer_instance

section SectionsPullback

variable {Z : Scheme.{u}} {P Q S : Z.Modules} (u : P ⟶ S) (v : Q ⟶ S) (U : Z.Opens)

/-- The compatible pairs of sections over `U`: the pairs of sections of `P` and `Q` with the same
image in `S`. -/
noncomputable def compatibleSections : Submodule Γ(Z, U) (Γ(P, U) × Γ(Q, U)) :=
  LinearMap.ker ((Scheme.Modules.sectionsLinearMap u U).comp (LinearMap.fst _ _ _) -
    (Scheme.Modules.sectionsLinearMap v U).comp (LinearMap.snd _ _ _))

/-- A pair of sections is compatible exactly when its two images in `S` agree. -/
theorem mem_compatibleSections (p : Γ(P, U) × Γ(Q, U)) :
    p ∈ compatibleSections u v U ↔ u.app U p.1 = v.app U p.2 := by
  rw [compatibleSections, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Scheme.Modules.sectionsLinearMap_apply, sub_eq_zero]

/-- The first projection of the compatible pairs of sections, as a linear map. -/
noncomputable def compatibleSectionsFstMap :
    compatibleSections u v U →ₗ[Γ(Z, U)] Γ(P, U) :=
  (LinearMap.fst Γ(Z, U) Γ(P, U) Γ(Q, U)).comp (compatibleSections u v U).subtype

/-- The second projection of the compatible pairs of sections, as a linear map. -/
noncomputable def compatibleSectionsSndMap :
    compatibleSections u v U →ₗ[Γ(Z, U)] Γ(Q, U) :=
  (LinearMap.snd Γ(Z, U) Γ(P, U) Γ(Q, U)).comp (compatibleSections u v U).subtype

/-- The first projection of the compatible pairs of sections. -/
noncomputable def compatibleSectionsFst :
    ModuleCat.of Γ(Z, U) (compatibleSections u v U) ⟶ (moduleSections Z U).obj P :=
  (ModuleCat.ofHom (compatibleSectionsFstMap u v U) :
    ModuleCat.of Γ(Z, U) (compatibleSections u v U) ⟶ ModuleCat.of Γ(Z, U) Γ(P, U))

/-- The second projection of the compatible pairs of sections. -/
noncomputable def compatibleSectionsSnd :
    ModuleCat.of Γ(Z, U) (compatibleSections u v U) ⟶ (moduleSections Z U).obj Q :=
  (ModuleCat.ofHom (compatibleSectionsSndMap u v U) :
    ModuleCat.of Γ(Z, U) (compatibleSections u v U) ⟶ ModuleCat.of Γ(Z, U) Γ(Q, U))

/-- The two projections of the compatible pairs agree after mapping into the sections of `S`. -/
theorem compatibleSections_condition :
    compatibleSectionsFst u v U ≫ (moduleSections Z U).map u =
      compatibleSectionsSnd u v U ≫ (moduleSections Z U).map v :=
  ModuleCat.hom_ext (LinearMap.ext fun p ↦ (mem_compatibleSections u v U p.1).mp p.2)

/-- The compatible pairs of sections are the fibre product of the sections. -/
noncomputable def compatibleSectionsIsLimit :
    IsLimit (PullbackCone.mk (compatibleSectionsFst u v U) (compatibleSectionsSnd u v U)
      (compatibleSections_condition u v U)) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦ ModuleCat.ofHom
      ((LinearMap.prod (ModuleCat.Hom.hom s.fst) (ModuleCat.Hom.hom s.snd)).codRestrict
        (compatibleSections u v U) (fun t ↦ by
          rw [mem_compatibleSections]
          exact congrArg (fun k : s.pt ⟶ (moduleSections Z U).obj S ↦
            ModuleCat.Hom.hom k t) s.condition)))
    (fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))
    (fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))
    (fun s m h₁ h₂ ↦ ModuleCat.hom_ext (LinearMap.ext fun t ↦ Subtype.ext (Prod.ext
      (congrArg (fun k : s.pt ⟶ (moduleSections Z U).obj P ↦ ModuleCat.Hom.hom k t) h₁)
      (congrArg (fun k : s.pt ⟶ (moduleSections Z U).obj Q ↦ ModuleCat.Hom.hom k t) h₂))))

/-- The sections over `U` of the fibre product of `u` and `v` are the compatible pairs of
sections. -/
noncomputable def sectionsPullbackIso :
    (moduleSections Z U).obj (pullback u v) ≅
      ModuleCat.of Γ(Z, U) (compatibleSections u v U) :=
  IsLimit.conePointUniqueUpToIso
    (isLimitOfHasPullbackOfPreservesLimit (moduleSections Z U) u v)
    (compatibleSectionsIsLimit u v U)

/-- `Stacks.Pushout.sectionsPullbackIso` followed by the first projection is the first projection
of the fibre product on sections. -/
theorem sectionsPullbackIso_hom_fst :
    (sectionsPullbackIso u v U).hom ≫ compatibleSectionsFst u v U =
      (moduleSections Z U).map (pullback.fst u v) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

/-- `Stacks.Pushout.sectionsPullbackIso` followed by the second projection is the second
projection of the fibre product on sections. -/
theorem sectionsPullbackIso_hom_snd :
    (sectionsPullbackIso u v U).hom ≫ compatibleSectionsSnd u v U =
      (moduleSections Z U).map (pullback.snd u v) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

end SectionsPullback

section Translation

/-! ### Transport along a bijection -/

/-- A bijection that preserves addition has an inverse that preserves addition. -/
theorem equivSymm_add {α β : Type*} [Add α] [Add β] (e : α ≃ β)
    (h : ∀ x y : α, e (x + y) = e x + e y) (y y' : β) :
    e.symm (y + y') = e.symm y + e.symm y' :=
  e.injective (by rw [e.apply_symm_apply, h, e.apply_symm_apply, e.apply_symm_apply])

/-- A bijection carrying the action of `z` to the action of `w` has an inverse carrying the
action of `w` to the action of `z`. -/
theorem equivSymm_smul {R S α β : Type*} [SMul R α] [SMul S β] (e : α ≃ β)
    {z : R} {w : S} (h : ∀ x : α, e (z • x) = w • e x) (y : β) :
    e.symm (w • y) = z • e.symm y :=
  e.injective (by rw [e.apply_symm_apply, h, e.apply_symm_apply])

/-- A bijection carrying the action of `z` to the action of `k z` carries the action of `f b` to
the action of `φ b`, when `k (f b) = φ b`. -/
private theorem equiv_smul_of_map_eq {D B S α β : Type*} [SMul D α] [SMul S β] (e : α ≃ β)
    {f : B → D} {k : D → S} {φ : B → S} (hsmul : ∀ (z : D) (x : α), e (z • x) = k z • e x)
    (h : ∀ b, k (f b) = φ b) (b : B) (x : α) : e (f b • x) = φ b • e x :=
  (hsmul _ x).trans (congrArg (· • e x) (h b))

/-- Flatness over `R` transports along a bijection `e` that is additive and carries the action of
`R` through `φ₁` to the action of `R` through `φ₂`. -/
theorem flat_of_equiv_semilinear {R S₁ S₂ M₁ M₂ : Type u} [CommRing R] [CommRing S₁]
    [CommRing S₂] [AddCommGroup M₁] [Module S₁ M₁] [AddCommGroup M₂] [Module S₂ M₂]
    (φ₁ : R →+* S₁) (φ₂ : R →+* S₂) (e : M₁ ≃ M₂)
    (hadd : ∀ x y : M₁, e (x + y) = e x + e y)
    (hsmul : ∀ (r : R) (x : M₁), e (φ₁ r • x) = φ₂ r • e x)
    (h : @Module.Flat R M₂ _ _ (Module.compHom M₂ φ₂)) :
    @Module.Flat R M₁ _ _ (Module.compHom M₁ φ₁) := by
  let : Module R M₁ := Module.compHom M₁ φ₁
  let : Module R M₂ := Module.compHom M₂ φ₂
  let := h
  exact Module.Flat.of_linearEquiv
    ({ toFun := e, map_add' := hadd, map_smul' := hsmul, invFun := e.symm,
        left_inv := e.left_inv, right_inv := e.right_inv } : M₁ ≃ₗ[R] M₂)

/-- A module flat over `R'` through `φ` is flat over `R` through `φ ∘ eR`, for a ring isomorphism
`eR : R ≃+* R'`. -/
theorem flat_of_ringEquiv_base {R R' S M : Type u} [CommRing R] [CommRing R'] [CommRing S]
    [AddCommGroup M] [Module S M] (eR : R ≃+* R') (φ : R' →+* S)
    (h : @Module.Flat R' M _ _ (Module.compHom M φ)) :
    @Module.Flat R M _ _ (Module.compHom M (φ.comp eR.toRingHom)) := by
  let : Algebra R R' := eR.toRingHom.toAlgebra
  let : Module R' M := Module.compHom M φ
  let : Module R M := Module.compHom M (φ.comp eR.toRingHom)
  let : IsScalarTower R R' M := ⟨fun r r' m ↦ by
    show (φ ((eR r) * r')) • m = φ (eR r) • (φ r' • m)
    rw [map_mul, mul_smul]⟩
  let : Module.Flat R R' :=
    Module.Flat.of_linearEquiv
      (LinearEquiv.ofBijective (Algebra.linearMap R R') eR.bijective).symm
  let := h
  exact Module.Flat.trans R R' M

/-- `AlgebraicGeometry.Scheme.Modules.pullbackSection` is the unit of the pullback-pushforward
adjunction on sections, followed by restriction. -/
theorem pullbackSection_eq {A B : Scheme.{u}} (p : A ⟶ B) (F : B.Modules) (W : B.Opens)
    (W' : A.Opens) (h : W' ≤ p ⁻¹ᵁ W) (a : Γ(F, W)) :
    Scheme.Modules.pullbackSection p F W W' h a =
      ((Scheme.Modules.pullback p).obj F).presheaf.map (homOfLE h).op
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app W a) := rfl

omit [IsAffineHom f] in
/-- `Stacks.Pushout.targetUnitNat` acts on sections by pulling a section back to the common
chart. -/
theorem targetUnitNat_app_app (N : (pullback (pushout.inr i f) g).Modules) (U : V'.Opens)
    (a : Γ(N, targetRestriction i f g ⁻¹ᵁ U)) :
    ((targetUnitNat i f g).app N).app U a =
      Scheme.Modules.pullbackSection (commonToTarget i f g) N
        (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
        (commonChart_le_targetChart i f g U) a :=
  rfl

omit [IsAffineHom f] in
/-- `Stacks.Pushout.ambientUnitNat` acts on sections by pulling a section back to the common
chart. -/
theorem ambientUnitNat_app_app (N : (pullback (pushout.inl i f) g).Modules) (U : V'.Opens)
    (b : Γ(N, ambientRestriction i f g ⁻¹ᵁ U)) :
    ((ambientUnitNat i f g).app N).app U b =
      Scheme.Modules.pullbackSection (commonToAmbient i f g) N
        (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
        (commonChart_le_ambientChart i f g U) b :=
  rfl

omit [IsAffineHom f] in
/-- `Stacks.Pushout.glueTargetNat` acts on sections by pulling a section back to the common chart
and applying the triple's isomorphism. -/
theorem glueTargetNat_app_app (T : GluingTriple i f g) (U : V'.Opens)
    (a : Γ(T.target, targetRestriction i f g ⁻¹ᵁ U)) :
    ((glueTargetNat i f g).app T).app U a =
      T.comparison.hom.app (commonRestriction i f g ⁻¹ᵁ U)
        (Scheme.Modules.pullbackSection (commonToTarget i f g) T.target
          (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
          (commonChart_le_targetChart i f g U) a) :=
  rfl

omit [IsAffineHom f] in
/-- `Stacks.Pushout.glueAmbientNat` acts on sections by pulling a section back to the common
chart. -/
theorem glueAmbientNat_app_app (T : GluingTriple i f g) (U : V'.Opens)
    (b : Γ(T.ambient, ambientRestriction i f g ⁻¹ᵁ U)) :
    ((glueAmbientNat i f g).app T).app U b =
      Scheme.Modules.pullbackSection (commonToAmbient i f g) T.ambient
        (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
        (commonChart_le_ambientChart i f g U) b :=
  rfl

omit [IsAffineHom f] in
/-- A pair of sections of a triple's components is compatible for the glued module exactly when
their pullbacks to the common chart agree through the triple's isomorphism. -/
theorem mem_compatibleSections_glue (T : GluingTriple i f g) (U : V'.Opens)
    (p : Γ(T.target, targetRestriction i f g ⁻¹ᵁ U) ×
      Γ(T.ambient, ambientRestriction i f g ⁻¹ᵁ U)) :
    p ∈ compatibleSections ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) U ↔
      T.comparison.hom.app (commonRestriction i f g ⁻¹ᵁ U)
          (Scheme.Modules.pullbackSection (commonToTarget i f g) T.target
            (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
            (commonChart_le_targetChart i f g U) p.1) =
        Scheme.Modules.pullbackSection (commonToAmbient i f g) T.ambient
          (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
          (commonChart_le_ambientChart i f g U) p.2 :=
  mem_compatibleSections ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) U p

/-- The sections of the glued module over an open are the compatible pairs of sections. -/
noncomputable def tripleGluingSectionsEquiv (T : GluingTriple i f g) (U : V'.Opens) :
    Γ((tripleGluingFunctor i f g).obj T, U) ≃ₗ[Γ(V', U)]
      compatibleSections ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) U :=
  (sectionsPullbackIso ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) U
    ).toLinearEquiv

omit [IsAffineHom f] in
/-- The first component of `Stacks.Pushout.tripleGluingSectionsEquiv` is the first projection of
the glued module. -/
theorem tripleGluingSectionsEquiv_fst (T : GluingTriple i f g) (U : V'.Opens)
    (z : Γ((tripleGluingFunctor i f g).obj T, U)) :
    (tripleGluingSectionsEquiv i f g T U z).val.1 =
      (pullback.fst ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T)).app U z :=
  congrArg (fun k : (moduleSections V' U).obj ((tripleGluingFunctor i f g).obj T) ⟶
    (moduleSections V' U).obj ((glueTargetFunctor i f g).obj T) ↦ ModuleCat.Hom.hom k z)
    (sectionsPullbackIso_hom_fst _ _ U)

omit [IsAffineHom f] in
/-- The second component of `Stacks.Pushout.tripleGluingSectionsEquiv` is the second projection
of the glued module. -/
theorem tripleGluingSectionsEquiv_snd (T : GluingTriple i f g) (U : V'.Opens)
    (z : Γ((tripleGluingFunctor i f g).obj T, U)) :
    (tripleGluingSectionsEquiv i f g T U z).val.2 =
      (pullback.snd ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T)).app U z :=
  congrArg (fun k : (moduleSections V' U).obj ((tripleGluingFunctor i f g).obj T) ⟶
    (moduleSections V' U).obj ((glueAmbientFunctor i f g).obj T) ↦ ModuleCat.Hom.hom k z)
    (sectionsPullbackIso_hom_snd _ _ U)

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- The chart in `V` of an affine open of `V'` is affine. -/
theorem isAffineOpen_targetChart (hi : IsThickening i) [IsAffineHom f] {U : V'.Opens}
    (hU : IsAffineOpen U) : IsAffineOpen (targetRestriction i f g ⁻¹ᵁ U) :=
  have := isAffineHom_targetRestriction i f g hi
  hU.preimage (targetRestriction i f g)

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- The chart in `U'` of an affine open of `V'` is affine. -/
theorem isAffineOpen_ambientChart (hi : IsThickening i) [IsAffineHom f] {U : V'.Opens}
    (hU : IsAffineOpen U) : IsAffineOpen (ambientRestriction i f g ⁻¹ᵁ U) :=
  have := isAffineHom_ambientRestriction i f g hi
  hU.preimage (ambientRestriction i f g)

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- The chart in `U` of an affine open of `V'` is affine. -/
theorem isAffineOpen_commonChart (hi : IsThickening i) [IsAffineHom f] {U : V'.Opens}
    (hU : IsAffineOpen U) : IsAffineOpen (commonRestriction i f g ⁻¹ᵁ U) :=
  have := isAffineHom_commonRestriction i f g hi
  hU.preimage (commonRestriction i f g)

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- For a quasi-coherent module `N` on `V` and an affine open `U` of `V'`, the sections over the
common chart of the restriction of `N` to `U` are the base change of the sections of `N` over the
chart of `V` along restriction along `U ⟶ V`, by an isomorphism sending `1 ⊗ a` to the pullback
of the section `a`. -/
theorem exists_targetChartSectionsBaseChangeIso (hi : IsThickening i) [IsAffineHom f]
    (N : (pullback (pushout.inr i f) g).Modules) [N.IsQuasicoherent] {U : V'.Opens}
    (hU : IsAffineOpen U) :
    ∃ e : (ModuleCat.extendScalars ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
          (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom).obj
          (ModuleCat.of Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U)
            Γ(N, targetRestriction i f g ⁻¹ᵁ U)) ≅
        ModuleCat.of Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)
          Γ((Scheme.Modules.pullback (commonToTarget i f g)).obj N,
            commonRestriction i f g ⁻¹ᵁ U),
      ∀ a : Γ(N, targetRestriction i f g ⁻¹ᵁ U),
        e.hom ((1 : Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)) ⊗ₜ[
            Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U),
            ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
              (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom] a) =
          Scheme.Modules.pullbackSection (commonToTarget i f g) N
            (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
            (commonChart_le_targetChart i f g U) a :=
  ⟨affinePullbackSectionsBaseChangeIso (commonToTarget i f g) N
      (isAffineOpen_targetChart i f g hi hU) (isAffineOpen_commonChart i f g hi hU)
      (commonChart_le_targetChart i f g U),
    affinePullbackSectionsBaseChangeIso_one_tmul (commonToTarget i f g) N
      (isAffineOpen_targetChart i f g hi hU) (isAffineOpen_commonChart i f g hi hU)
      (commonChart_le_targetChart i f g U)⟩

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- For a quasi-coherent module `N` on `U'` and an affine open `U` of `V'`, the sections over the
common chart of the restriction of `N` to `U` are the base change of the sections of `N` over the
chart of `U'` along restriction along `U ⟶ U'`, by an isomorphism sending `1 ⊗ b` to the pullback
of the section `b`. -/
theorem exists_ambientChartSectionsBaseChangeIso (hi : IsThickening i) [IsAffineHom f]
    (N : (pullback (pushout.inl i f) g).Modules) [N.IsQuasicoherent] {U : V'.Opens}
    (hU : IsAffineOpen U) :
    ∃ e : (ModuleCat.extendScalars ((commonToAmbient i f g).appLE
          (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
          (commonChart_le_ambientChart i f g U)).hom).obj
          (ModuleCat.of Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U)
            Γ(N, ambientRestriction i f g ⁻¹ᵁ U)) ≅
        ModuleCat.of Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)
          Γ((Scheme.Modules.pullback (commonToAmbient i f g)).obj N,
            commonRestriction i f g ⁻¹ᵁ U),
      ∀ b : Γ(N, ambientRestriction i f g ⁻¹ᵁ U),
        e.hom ((1 : Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)) ⊗ₜ[
            Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U),
            ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
              (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom] b) =
          Scheme.Modules.pullbackSection (commonToAmbient i f g) N
            (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
            (commonChart_le_ambientChart i f g U) b :=
  ⟨affinePullbackSectionsBaseChangeIso (commonToAmbient i f g) N
      (isAffineOpen_ambientChart i f g hi hU) (isAffineOpen_commonChart i f g hi hU)
      (commonChart_le_ambientChart i f g U),
    affinePullbackSectionsBaseChangeIso_one_tmul (commonToAmbient i f g) N
      (isAffineOpen_ambientChart i f g hi hU) (isAffineOpen_commonChart i f g hi hU)
      (commonChart_le_ambientChart i f g U)⟩

/-! ### The chart translation of the gluing problem -/

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- For a triple of quasi-coherent modules and an affine open `U` of `V'`, there is an isomorphism
between the base changes to the common chart of the sections of the triple's two components over
the charts of `V` and of `U'`, under which `1 ⊗ x` corresponds to `1 ⊗ y` exactly when the
pullbacks of `x` and `y` to the common chart agree through the triple's isomorphism. -/
theorem exists_chartComparisonBaseChangeIso (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) [T.target.IsQuasicoherent] [T.ambient.IsQuasicoherent]
    {U : V'.Opens} (hU : IsAffineOpen U) :
    ∃ γ : (ModuleCat.extendScalars ((commonToTarget i f g).appLE
          (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
          (commonChart_le_targetChart i f g U)).hom).obj
          (ModuleCat.of Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U)
            Γ(T.target, targetRestriction i f g ⁻¹ᵁ U)) ≅
        (ModuleCat.extendScalars ((commonToAmbient i f g).appLE
          (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
          (commonChart_le_ambientChart i f g U)).hom).obj
          (ModuleCat.of Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U)
            Γ(T.ambient, ambientRestriction i f g ⁻¹ᵁ U)),
      ∀ (x : Γ(T.target, targetRestriction i f g ⁻¹ᵁ U))
        (y : Γ(T.ambient, ambientRestriction i f g ⁻¹ᵁ U)),
        (γ.hom ((1 : Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)) ⊗ₜ[
            Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U),
            ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
              (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom] x) =
          (1 : Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)) ⊗ₜ[
            Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U),
            ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
              (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom] y) ↔
          T.comparison.hom.app (commonRestriction i f g ⁻¹ᵁ U)
              (Scheme.Modules.pullbackSection (commonToTarget i f g) T.target
                (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
                (commonChart_le_targetChart i f g U) x) =
            Scheme.Modules.pullbackSection (commonToAmbient i f g) T.ambient
              (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
              (commonChart_le_ambientChart i f g U) y := by
  refine Exists.elim (exists_targetChartSectionsBaseChangeIso i f g hi T.target hU)
    fun cT hcT => Exists.elim (exists_ambientChartSectionsBaseChangeIso i f g hi T.ambient hU)
    fun cA hcA => ⟨cT ≪≫ (moduleSections (pullback (i ≫ pushout.inl i f) g)
      (commonRestriction i f g ⁻¹ᵁ U)).mapIso T.comparison ≪≫ cA.symm, fun x y => ?_⟩
  have hcAhi : ∀ z, cA.hom (cA.inv z) = z := fun z =>
    DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp cA.inv_hom_id) z
  have hcAih : ∀ z, cA.inv (cA.hom z) = z := fun z =>
    DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp cA.hom_inv_id) z
  have h1 : (cT ≪≫ (moduleSections (pullback (i ≫ pushout.inl i f) g)
        (commonRestriction i f g ⁻¹ᵁ U)).mapIso T.comparison ≪≫ cA.symm).hom
      ((1 : Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)) ⊗ₜ[
        Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U),
        ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
          (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom] x) =
      cA.inv (T.comparison.hom.app (commonRestriction i f g ⁻¹ᵁ U)
        (Scheme.Modules.pullbackSection (commonToTarget i f g) T.target
          (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
          (commonChart_le_targetChart i f g U) x)) :=
    congrArg (fun z => cA.inv (T.comparison.hom.app (commonRestriction i f g ⁻¹ᵁ U) z)) (hcT x)
  exact ⟨fun h => ((hcAhi _).symm.trans
      (congrArg (fun z => cA.hom z) (h1.symm.trans h))).trans (hcA y),
    fun h => h1.trans ((congrArg (fun z => cA.inv z) h).trans
      ((congrArg (fun z => cA.inv z) (hcA y)).symm.trans (hcAih _)))⟩

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- Given ring isomorphisms `kD`, `kC'`, `kC` from the base-change rings of a relative Milnor
patching situation to the three chart section rings, compatible with `D ⟶ C` and `C' ⟶ C`, a
triple of quasi-coherent modules gives an object of
`MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules` whose two components are,
additively and semilinearly along `kD` and `kC'`, the sections of the triple's components over
the two charts, and whose compatible pairs are the pairs compatible for the triple. -/
theorem exists_chartCompatibleModules (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) [T.target.IsQuasicoherent] [T.ambient.IsQuasicoherent]
    {W : (pushout i f).Opens} {U : V'.Opens} (hU : IsAffineOpen U)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U))
    (kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U))
    (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U))
    (hD : ∀ z : s.D, kC (s.DtoC z) =
      ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom (kD z))
    (hC' : ∀ z : s.C', kC (s.C'toC z) =
      ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom (kC' z)) :
    ∃ (Xc : MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules.{u, u, u, u, u} s)
      (eD : Xc.fst ≃ Γ(T.target, targetRestriction i f g ⁻¹ᵁ U))
      (eA : Xc.snd ≃ Γ(T.ambient, ambientRestriction i f g ⁻¹ᵁ U)),
      (∀ n n' : Xc.fst, eD (n + n') = eD n + eD n') ∧
        (∀ (z : s.D) (n : Xc.fst), eD (z • n) = kD z • eD n) ∧
        (∀ m m' : Xc.snd, eA (m + m') = eA m + eA m') ∧
        (∀ (z : s.C') (m : Xc.snd), eA (z • m) = kC' z • eA m) ∧
        ∀ (n : Xc.fst) (m : Xc.snd),
          (Xc.iso.hom ((1 : s.C) ⊗ₜ[s.D,s.DtoC] n) = (1 : s.C) ⊗ₜ[s.C',s.C'toC] m) ↔
            T.comparison.hom.app (commonRestriction i f g ⁻¹ᵁ U)
                (Scheme.Modules.pullbackSection (commonToTarget i f g) T.target
                  (targetRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
                  (commonChart_le_targetChart i f g U) (eD n)) =
              Scheme.Modules.pullbackSection (commonToAmbient i f g) T.ambient
                (ambientRestriction i f g ⁻¹ᵁ U) (commonRestriction i f g ⁻¹ᵁ U)
                (commonChart_le_ambientChart i f g U) (eA m) :=
  Exists.elim (exists_chartComparisonBaseChangeIso i f g hi T hU) fun γ hγ =>
    Exists.elim (Stacks.ModuleCat.exists_categoricalPullback_of_ringEquivSquare
        kD kC' kC s.DtoC s.C'toC
        ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
          (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom
        ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
          (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom
        hD hC' _ _ γ) fun Xc h2 =>
      Exists.elim h2 fun eD h3 => Exists.elim h3 fun eA hXc =>
        ⟨Xc, eD, eA, hXc.1, hXc.2.1, hXc.2.2.1, hXc.2.2.2.1,
          fun n m => (hXc.2.2.2.2 n m).trans (hγ (eD n) (eA m))⟩

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- Under the hypotheses of `Stacks.Pushout.exists_chartCompatibleModules`, and when `kD` and
`kC'` carry the maps out of `Γ(V', U)` to restriction, the sections over `U` of the glued module
of a triple are `Γ(V', U)`-linearly the compatible pairs of the resulting object of
`MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules`, by an equivalence given by
the two projections of the glued module. -/
theorem exists_chartGluingSectionsCompatiblePairsLinearEquiv (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) [T.target.IsQuasicoherent] [T.ambient.IsQuasicoherent]
    {W : (pushout i f).Opens} {U : V'.Opens} (hU : IsAffineOpen U)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U))
    (kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U))
    (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U))
    (hD : ∀ z : s.D, kC (s.DtoC z) =
      ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom (kD z))
    (hC' : ∀ z : s.C', kC (s.C'toC z) =
      ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom (kC' z))
    (hkD : ∀ d : Γ(V', U), kD (s.toD d) = ((targetRestriction i f g).app U).hom d)
    (hkC' : ∀ d : Γ(V', U), kC' (s.toC' d) = ((ambientRestriction i f g).app U).hom d) :
    ∃ (Xc : MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules.{u, u, u, u, u} s)
      (E : Γ((tripleGluingFunctor i f g).obj T, U) ≃ₗ[Γ(V', U)]
        MilnorPatching.compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC
          s.relativeSquare_comm Xc)
      (eD : Xc.fst ≃ Γ(T.target, targetRestriction i f g ⁻¹ᵁ U))
      (eA : Xc.snd ≃ Γ(T.ambient, ambientRestriction i f g ⁻¹ᵁ U)),
      (∀ n n' : Xc.fst, eD (n + n') = eD n + eD n') ∧
        (∀ (z : s.D) (n : Xc.fst), eD (z • n) = kD z • eD n) ∧
        (∀ m m' : Xc.snd, eA (m + m') = eA m + eA m') ∧
        (∀ (z : s.C') (m : Xc.snd), eA (z • m) = kC' z • eA m) ∧
        (∀ z, eD (E z).1.1 = (pullback.fst ((glueTargetNat i f g).app T)
            ((glueAmbientNat i f g).app T)).app U z) ∧
          (∀ z, eA (E z).1.2 = (pullback.snd ((glueTargetNat i f g).app T)
            ((glueAmbientNat i f g).app T)).app U z) := by
  refine Exists.elim (exists_chartCompatibleModules i f g hi T hU s kD kC' kC hD hC')
    fun Xc h2 => Exists.elim h2 fun eD h3 => Exists.elim h3 fun eA hXc => ?_
  obtain ⟨hDadd, hDsmul, hAadd, hAsmul, hiff⟩ := hXc
  let Φ : compatibleSections ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) U ≃
      MilnorPatching.CompatiblePairs s.DtoC s.C'toC Xc :=
    (Equiv.subtypeEquiv (eD.prodCongr eA) fun b =>
      (hiff b.1 b.2).trans
        (mem_compatibleSections_glue i f g T U ((eD.prodCongr eA) b)).symm).symm
  let Ψ : compatibleSections ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) U
      ≃ₗ[Γ(V', U)] MilnorPatching.compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC
        s.relativeSquare_comm Xc :=
    { toFun := Φ
      map_add' := fun p p' => Subtype.ext (Prod.ext
        (equivSymm_add eD hDadd _ _) (equivSymm_add eA hAadd _ _))
      map_smul' := fun d p => Subtype.ext (Prod.ext
        (equivSymm_smul eD (equiv_smul_of_map_eq eD hDsmul hkD d) _)
        (equivSymm_smul eA (equiv_smul_of_map_eq eA hAsmul hkC' d) _))
      invFun := Φ.symm
      left_inv := Φ.left_inv
      right_inv := Φ.right_inv }
  refine ⟨Xc, (tripleGluingSectionsEquiv i f g T U) ≪≫ₗ Ψ, eD, eA, hDadd, hDsmul, hAadd, hAsmul,
    fun z => ?_, fun z => ?_⟩
  · exact (eD.apply_symm_apply _).trans (tripleGluingSectionsEquiv_fst i f g T U z)
  · exact (eA.apply_symm_apply _).trans (tripleGluingSectionsEquiv_snd i f g T U z)

/-! ### Relative flatness of the glued module -/

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- For an affine open `U` of `V'` lying above an affine open `W` of `Y'`, the sections over `U`
of the glued module of a triple of quasi-coherent modules flat over `Y` and over `X'` are flat
over `Γ(Y', W)`. -/
theorem flat_chartSections_tripleGluingFunctor_obj (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) [T.target.IsQuasicoherent] [T.ambient.IsQuasicoherent]
    (hTt : AlgebraicGeometry.IsFlatOver (targetBase i f g).toLRSHom.toShHom T.target)
    (hTa : AlgebraicGeometry.IsFlatOver (ambientBase i f g).toLRSHom.toShHom T.ambient)
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W) :
    letI : Module Γ(pushout i f, W) Γ((tripleGluingFunctor i f g).obj T, U) :=
      Module.compHom _ (g.appLE W U hUW).hom
    Module.Flat Γ(pushout i f, W) Γ((tripleGluingFunctor i f g).obj T, U) := by
  have : IsClosedImmersion i := hi.1
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  have hBaff : IsAffineOpen (pushout.inr i f ⁻¹ᵁ W) := hW.preimage (pushout.inr i f)
  have hA'aff : IsAffineOpen (pushout.inl i f ⁻¹ᵁ W) := hW.preimage (pushout.inl i f)
  refine Exists.elim (exists_chartSituation i f g hi hW hUW) fun I h1 =>
    Exists.elim h1 fun base h2 => Exists.elim h2 fun s h3 =>
    Exists.elim h3 fun eB hB => ?_
  obtain ⟨hD', heB, heA'⟩ := hB
  refine Exists.elim (exists_targetChartRingEquiv i f g hi hW hU hUW base s eB hD' heB)
    fun kD hkD => Exists.elim
      (exists_ambientChartRingEquiv i f g hi hW hU hUW base s eB hD' heA') fun kC' hkC' =>
      Exists.elim (exists_commonChartRingEquiv i f g hi hW hU hUW base s eB hD' heB)
        fun kC hkC => ?_
  obtain ⟨hkD1, hkD2⟩ := hkD
  obtain ⟨hkC'1, hkC'2⟩ := hkC'
  obtain ⟨hkC1, hkC2⟩ := hkC
  have hDC := chartRingEquiv_DtoC i f g hUW s kD kC hkD1 hkD2 hkC1 hkC2
  have hkC1' : ∀ d : Γ(V', U), kC (s.C'toC (s.toC' d)) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl d := fun d =>
    (congrArg kC (DFunLike.congr_fun s.relativeSquare_comm d).symm).trans (hkC1 d)
  have hC'C := chartRingEquiv_C'toC i f g hUW s kC' kC hkC'1 hkC'2 hkC1' hkC2
  have hkDapp : ∀ d : Γ(V', U), kD (s.toD d) = ((targetRestriction i f g).app U).hom d := by
    intro d
    rw [hkD1 d, Scheme.Hom.appLE_eq_app]
  have hkC'app : ∀ d : Γ(V', U), kC' (s.toC' d) = ((ambientRestriction i f g).app U).hom d := by
    intro d
    rw [hkC'1 d, Scheme.Hom.appLE_eq_app]
  refine Exists.elim (exists_chartGluingSectionsCompatiblePairsLinearEquiv i f g hi T hU s
      kD kC' kC hDC hC'C hkDapp hkC'app) fun Xc h4 =>
    Exists.elim h4 fun E h5 => Exists.elim h5 fun eD h6 => Exists.elim h6 fun eA h7 => ?_
  obtain ⟨hDadd, hDsmul, hAadd, hAsmul, -, -⟩ := h7
  have hXfst : Module.Flat Γ(Y, pushout.inr i f ⁻¹ᵁ W)
      ((ModuleCat.restrictScalars s.BtoD).obj Xc.fst) :=
    flat_of_equiv_semilinear s.BtoD _ eD hDadd
      (equiv_smul_of_map_eq eD hDsmul hkD2)
      (((AlgebraicGeometry.isFlatOver_tfae (targetBase i f g) T.target).out 1 2 rfl rfl).mp hTt
        (targetRestriction i f g ⁻¹ᵁ U) (isAffineOpen_targetChart i f g hi hU)
        (pushout.inr i f ⁻¹ᵁ W) hBaff (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW))
  have hXsnd : Module.Flat Γ(X', pushout.inl i f ⁻¹ᵁ W)
      ((ModuleCat.restrictScalars s.A'toC').obj Xc.snd) :=
    flat_of_equiv_semilinear s.A'toC' _ eA hAadd
      (equiv_smul_of_map_eq eA hAsmul hkC'2)
      (((AlgebraicGeometry.isFlatOver_tfae (ambientBase i f g) T.ambient).out 1 2 rfl rfl).mp hTa
        (ambientRestriction i f g ⁻¹ᵁ U) (isAffineOpen_ambientChart i f g hi hU)
        (pushout.inl i f ⁻¹ᵁ W) hA'aff (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW))
  obtain ⟨F, e07, adj, form, -, -, hflat07, hunit07, -⟩ :=
    MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct s
  have hFflat := hflat07 Xc ⟨hXfst, hXsnd⟩
  have h1 : @Module.Flat Γ(pushout i f, W) (F.obj Xc) _ _
      (Module.compHom _ (s.toD'.comp eB.toRingHom)) := flat_of_ringEquiv_base eB s.toD' hFflat
  rw [hD'] at h1
  exact flat_of_equiv_semilinear (g.appLE W U hUW).hom (g.appLE W U hUW).hom
    (E ≪≫ₗ (e07 Xc).symm).toEquiv (fun x y => map_add (E ≪≫ₗ (e07 Xc).symm) x y)
    (fun r x => (E ≪≫ₗ (e07 Xc).symm).map_smul _ x) h1

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- The glued module of a triple of relatively flat quasi-coherent modules is flat over `Y'`. -/
theorem isFlatOver_tripleGluingFunctor_obj (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) (hT : IsFlatQuasicoherentTriple i f g T) :
    AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom ((tripleGluingFunctor i f g).obj T) := by
  have := hT.1.1
  have := hT.2.1
  have : ((tripleGluingFunctor i f g).obj T).IsQuasicoherent :=
    isQuasicoherent_tripleGluingFunctor_obj i f g hi T hT.1.1 hT.2.1
  refine ((AlgebraicGeometry.isFlatOver_tfae g
    ((tripleGluingFunctor i f g).obj T)).out 2 1 rfl rfl).mp ?_
  intro U hU W hW hUW
  exact flat_chartSections_tripleGluingFunctor_obj i f g hi T hT.1.2 hT.2.2 hW hU hUW

omit [IsAffineHom f] in
open Stacks.Thickenings in
/-- The glued module of a triple of relatively flat quasi-coherent modules is quasi-coherent and
flat over `Y'`. -/
theorem flatQuasicoherent_tripleGluingFunctor_obj (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) (hT : IsFlatQuasicoherentTriple i f g T) :
    FlatQuasicoherent g ((tripleGluingFunctor i f g).obj T) :=
  ⟨isQuasicoherent_tripleGluingFunctor_obj i f g hi T hT.1.1 hT.2.1,
    isFlatOver_tripleGluingFunctor_obj i f g hi T hT⟩

end Translation

end Stacks.Pushout

end
