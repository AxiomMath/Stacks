module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine models of a morphism over a base of finite type over the integers

An *affine finite-type model* of a morphism `f : X ⟶ S` of affine schemes consists of a
morphism `f₀ : X₀ ⟶ S₀` of affine schemes, with `S₀` of finite type over `Spec ℤ` and `f₀` of
finite type, together with a cartesian square exhibiting `f` as a base change of `f₀`. A model
may also be asked to satisfy a prescribed property `P`, recorded in its `property` field.

Two results are proved. The first combines two models: if `f` carries a model for `P` and a
model for `Q`, and both properties are stable under base change, then it carries a single model
for `P ⊓ Q`. The second refines a model so that a fibrewise condition which holds at every point
of `S` holds at every point of the base of the model.

## Main definitions

* `AlgebraicGeometry.FiniteTypeAffineModel` packages an affine finite-type model of an affine
  morphism.

## Main results

* `AlgebraicGeometry.exists_finiteTypeAffineModel_inf` combines models for two properties
  stable under base change.
* `AlgebraicGeometry.exists_finiteTypeAffineModel_fiberwise` refines a model so that a
  base-change-compatible, constructible fibrewise condition holds over its whole base.

## References

* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 05FL](https://stacks.math.columbia.edu/tag/05FL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An affine finite-type model of a morphism `f`: a morphism `f₀ : X₀ ⟶ S₀` of finite type
between affine schemes, with `S₀` of finite type over `Spec ℤ`, satisfying `P`, together with a
pullback square exhibiting `f` as the base change of `f₀`. -/
structure FiniteTypeAffineModel (P : MorphismProperty Scheme.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The source of the model. -/
  X₀ : Scheme.{u}
  /-- The base of the model. -/
  S₀ : Scheme.{u}
  /-- The modeled morphism. -/
  f₀ : X₀ ⟶ S₀
  /-- The comparison map on sources. -/
  toSource : X ⟶ X₀
  /-- The comparison map on bases. -/
  toBase : S ⟶ S₀
  /-- The comparison maps exhibit `f` as the base change of `f₀`. -/
  isPullback : IsPullback toSource f f₀ toBase
  /-- The source of the model is affine. -/
  source_affine : IsAffine X₀
  /-- The base of the model is affine. -/
  base_affine : IsAffine S₀
  /-- The base of the model is locally of finite type over `Spec ℤ`. -/
  base_locallyOfFiniteType : LocallyOfFiniteType (terminal.from S₀)
  /-- The base of the model is quasi-compact over `Spec ℤ`. -/
  base_quasiCompact : QuasiCompact (terminal.from S₀)
  /-- The modeled morphism is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType f₀
  /-- The modeled morphism is quasi-compact. -/
  quasiCompact : QuasiCompact f₀
  /-- The modeled morphism has the prescribed property. -/
  property : P f₀

private theorem model_base_finiteType
    {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} {f : X ⟶ S}
    (h : FiniteTypeAffineModel P f) : Algebra.FiniteType ℤ Γ(h.S₀, ⊤) := by
  let : IsAffine h.S₀ := h.base_affine
  let : LocallyOfFiniteType (terminal.from h.S₀) := h.base_locallyOfFiniteType
  let e : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  let g : h.S₀ ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from h.S₀ ≫ e.inv
  let : LocallyOfFiniteType g := by dsimp [g]; infer_instance
  let : IsAffine (Spec (.of (ULift.{u} ℤ))) := inferInstance
  have hftBase : (g.appTop).hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) g inferInstance
  let αEquiv : ULift.{u} ℤ ≃+* Γ(Spec (.of (ULift.{u} ℤ)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv.symm
  let βEquiv : ℤ ≃+* ULift.{u} ℤ := (ULift.ringEquiv (R := ℤ)).symm
  let α := αEquiv.toRingHom
  let β := βEquiv.toRingHom
  have hft : (g.appTop.hom.comp (α.comp β)).FiniteType :=
    hftBase.comp
      ((RingHom.FiniteType.of_surjective _ αEquiv.surjective).comp
        (RingHom.FiniteType.of_surjective _ βEquiv.surjective))
  have heq : g.appTop.hom.comp (α.comp β) = algebraMap ℤ Γ(h.S₀, ⊤) :=
    RingHom.ext_int _ _
  exact (RingHom.finiteType_algebraMap).mp (heq ▸ hft)

private theorem model_finitePresentation
    {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} {f : X ⟶ S}
    (h : FiniteTypeAffineModel P f) : FinitePresentation h.f₀ := by
  let : IsAffine h.X₀ := h.source_affine
  let : IsAffine h.S₀ := h.base_affine
  let : LocallyOfFiniteType h.f₀ := h.locallyOfFiniteType
  let : Algebra Γ(h.S₀, ⊤) Γ(h.X₀, ⊤) := h.f₀.appTop.hom.toAlgebra
  have hft : (h.f₀.appTop).hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) h.f₀ inferInstance
  let : Algebra.FiniteType Γ(h.S₀, ⊤) Γ(h.X₀, ⊤) :=
    (RingHom.finiteType_algebraMap).mp hft
  let : Algebra.FiniteType ℤ Γ(h.S₀, ⊤) := model_base_finiteType h
  let : IsNoetherianRing Γ(h.S₀, ⊤) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hfp : (h.f₀.appTop).hom.FinitePresentation :=
    (Algebra.FinitePresentation.of_finiteType (R := Γ(h.S₀, ⊤))
      (A := Γ(h.X₀, ⊤))).mp hft
  exact ⟨(HasRingHomProperty.iff_of_isAffine
    (P := @LocallyOfFinitePresentation) (f := h.f₀)).mpr hfp,
    h.quasiCompact, inferInstance⟩

private theorem model_base_finitePresentation
    {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} {f : X ⟶ S}
    (h : FiniteTypeAffineModel P f) :
    LocallyOfFinitePresentation (terminal.from h.S₀) := by
  let : IsAffine h.S₀ := h.base_affine
  let : LocallyOfFiniteType (terminal.from h.S₀) := h.base_locallyOfFiniteType
  let e : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  let g : h.S₀ ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from h.S₀ ≫ e.inv
  let : LocallyOfFiniteType g := by dsimp [g]; infer_instance
  let : IsAffine (Spec (.of (ULift.{u} ℤ))) := inferInstance
  have hft : (g.appTop).hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) g inferInstance
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  let : IsNoetherianRing Γ(Spec (.of (ULift.{u} ℤ)), ⊤) :=
    isNoetherianRing_of_ringEquiv (ULift.{u} ℤ)
      (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv.symm
  have hfp : (g.appTop).hom.FinitePresentation :=
    (RingHom.FinitePresentation.of_finiteType).mp hft
  let : LocallyOfFinitePresentation g :=
    (HasRingHomProperty.iff_of_isAffine
      (P := @LocallyOfFinitePresentation) (f := g)).mpr hfp
  simpa only [Subsingleton.elim (g ≫ e.hom) (terminal.from h.S₀)] using
    (inferInstance : LocallyOfFinitePresentation (g ≫ e.hom))

private def baseDiagram {R : Type u} [CommRing R] (R₀ : Subring R) :
    Algebra.FiniteTypeSystem.Index R₀ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (Algebra.FiniteTypeSystem.Base R₀ i)
  map f := CommRingCat.ofHom
    (Algebra.FiniteTypeSystem.baseMap R₀ (leOfHom f)).toRingHom
  map_id i := by ext x; rfl
  map_comp f g := by ext x; rfl

private theorem bottom_finiteType (R : Type u) [CommRing R] :
    Algebra.FiniteType ℤ (⊥ : Subring R) := by
  apply (RingHom.finiteType_algebraMap).mp
  apply RingHom.FiniteType.of_surjective
  intro x
  obtain ⟨n, hn⟩ := Subring.mem_bot.mp x.2
  exact ⟨n, Subtype.ext hn⟩

/-- The spectrum of a ring of finite type over `ℤ` is locally of finite type over the terminal
scheme. -/
theorem finiteType_spec_terminal (R : Type u) [CommRing R]
    [Algebra.FiniteType ℤ R] :
    LocallyOfFiniteType (terminal.from (Spec (.of R) : Scheme.{u})) := by
  let zMap : ULift.{u} ℤ →+* R :=
    (algebraMap ℤ R).comp ULift.ringEquiv.toRingHom
  let g : Spec (.of R) ⟶ Spec (.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom zMap)
  have hzMap : zMap.FiniteType :=
    (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ ULift.down_surjective)
  have : LocallyOfFiniteType g :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hzMap
  let e : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  simpa only [Subsingleton.elim (g ≫ e.hom)
    (terminal.from (Spec (.of R) : Scheme.{u}))] using
      (inferInstance : LocallyOfFiniteType (g ≫ e.hom))

private def baseCocone {A : CommRingCat.{u}} (R₀ : Subring A) :
    Cocone ((baseDiagram R₀).op.leftOp) where
  pt := A
  ι := {
    app i := CommRingCat.ofHom
      (Algebra.FiniteTypeSystem.baseToRing R₀ i.unop.unop).toRingHom
    naturality := by intro i j f; ext x; rfl }

private noncomputable def baseIsColimit {A : CommRingCat.{u}} (R₀ : Subring A)
    [Algebra.FiniteType ℤ R₀] : IsColimit (baseCocone R₀) := by
  classical
  let D := (baseDiagram R₀).op.leftOp
  let := reflectsColimit_of_reflectsIsomorphisms D (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro r
    change (A : Type u) at r
    obtain ⟨i, x, hx⟩ := Algebra.FiniteTypeSystem.base_jointly_surjective R₀ r
    refine ⟨.op (.op i), x, ?_⟩
    change r = (Algebra.FiniteTypeSystem.baseToRing R₀ i) x
    exact hx.symm
  · intro i x y h
    refine ⟨i, 𝟙 i, ?_⟩
    change Algebra.FiniteTypeSystem.Base R₀ i.unop.unop at x y
    change x.1 = y.1 at h
    change x = y
    exact Subtype.ext h

private noncomputable def baseSchemeDiagram {R : Type u} [CommRing R] (R₀ : Subring R) :
    (Algebra.FiniteTypeSystem.Index R₀)ᵒᵖ ⥤ Scheme.{u} :=
  (baseDiagram R₀).op ⋙ Scheme.Spec

private noncomputable def baseSchemeCone {A : CommRingCat.{u}} (R₀ : Subring A) :
    Cone (baseSchemeDiagram R₀) where
  pt := Spec A
  π := (Scheme.Spec.mapCone (coneOfCoconeLeftOp (baseCocone R₀))).π

@[simp] private lemma baseSchemeCone_pt {A : CommRingCat.{u}} (R₀ : Subring A) :
    (baseSchemeCone R₀).pt = Spec A := rfl

private noncomputable def baseSchemeIsLimit {A : CommRingCat.{u}} (R₀ : Subring A)
    [Algebra.FiniteType ℤ R₀] : IsLimit (baseSchemeCone R₀) :=
  isLimitOfPreserves Scheme.Spec
    (isLimitConeOfCoconeLeftOp _ (baseIsColimit R₀))

private noncomputable abbrev baseSchemeConeAt (S : Scheme.{u}) [IsAffine S]
    (R₀ : Subring Γ(S, ⊤)) : Cone (baseSchemeDiagram R₀) :=
  (baseSchemeCone R₀).extend S.isoSpec.hom

private noncomputable def baseSchemeIsLimitAt (S : Scheme.{u}) [IsAffine S]
    (R₀ : Subring Γ(S, ⊤)) [Algebra.FiniteType ℤ R₀] :
    IsLimit (baseSchemeConeAt S R₀) :=
  IsLimit.ofIsoLimit (baseSchemeIsLimit R₀)
    (Cone.extendIso (baseSchemeCone R₀)
      (S.isoSpec.symm : (baseSchemeCone R₀).pt ≅ S))

private instance baseSchemeDiagram_isAffine {R : Type u} [CommRing R] (R₀ : Subring R)
    (t : (Algebra.FiniteTypeSystem.Index R₀)ᵒᵖ) : IsAffine ((baseSchemeDiagram R₀).obj t) :=
  inferInstanceAs (IsAffine (Spec (.of (Algebra.FiniteTypeSystem.Base R₀ t.unop))))

private instance baseSchemeDiagram_isAffineHom {R : Type u} [CommRing R] (R₀ : Subring R)
    {s t : (Algebra.FiniteTypeSystem.Index R₀)ᵒᵖ} (e : s ⟶ t) :
    IsAffineHom ((baseSchemeDiagram R₀).map e) :=
  inferInstanceAs (IsAffineHom (Spec.map _))

private instance baseSchemeDiagram_compactSpace {R : Type u} [CommRing R] (R₀ : Subring R)
    [Algebra.FiniteType ℤ R₀] (t : (Algebra.FiniteTypeSystem.Index R₀)ᵒᵖ) :
    CompactSpace ((baseSchemeDiagram R₀).obj t) :=
  inferInstanceAs (CompactSpace (Spec (.of (Algebra.FiniteTypeSystem.Base R₀ t.unop))))

private instance baseSchemeDiagram_quasiSeparatedSpace {R : Type u} [CommRing R]
    (R₀ : Subring R) [Algebra.FiniteType ℤ R₀] (t : (Algebra.FiniteTypeSystem.Index R₀)ᵒᵖ) :
    QuasiSeparatedSpace ((baseSchemeDiagram R₀).obj t) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec (.of (Algebra.FiniteTypeSystem.Base R₀ t.unop))))

private instance baseSchemeDiagram_locallyOfFiniteType {R : Type u} [CommRing R]
    (R₀ : Subring R) [Algebra.FiniteType ℤ R₀] (t : (Algebra.FiniteTypeSystem.Index R₀)ᵒᵖ) :
    LocallyOfFiniteType (terminal.from ((baseSchemeDiagram R₀).obj t)) :=
  finiteType_spec_terminal (Algebra.FiniteTypeSystem.Base R₀ t.unop)

private instance baseSchemeDiagram_isLocallyNoetherian {R : Type u} [CommRing R]
    (R₀ : Subring R) [Algebra.FiniteType ℤ R₀] (t : (Algebra.FiniteTypeSystem.Index R₀)ᵒᵖ) :
    IsLocallyNoetherian ((baseSchemeDiagram R₀).obj t) :=
  have : Algebra.FiniteType ℤ (Algebra.FiniteTypeSystem.Base R₀ t.unop) := inferInstance
  isLocallyNoetherian_Spec (R := .of (Algebra.FiniteTypeSystem.Base R₀ t.unop)) |>.mpr
    (Algebra.FiniteType.isNoetherianRing ℤ _)

private theorem model_base_factors
    {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} [IsAffine S]
    {f : X ⟶ S} (h : FiniteTypeAffineModel P f) :
    ∃ (i : (Algebra.FiniteTypeSystem.Index (⊥ : Subring Γ(S, ⊤)))ᵒᵖ)
      (g : (baseSchemeDiagram (⊥ : Subring Γ(S, ⊤))).obj i ⟶ h.S₀),
      (baseSchemeConeAt S (⊥ : Subring Γ(S, ⊤))).π.app i ≫ g =
        h.toBase := by
  classical
  let R₀ : Subring Γ(S, ⊤) := ⊥
  let : Algebra.FiniteType ℤ R₀ := bottom_finiteType _
  let D := baseSchemeDiagram R₀
  let c := baseSchemeConeAt S R₀
  let t : D ⟶ (Functor.const _).obj (⊤_ Scheme.{u}) :=
    { app _ := terminal.from _, naturality _ _ _ := terminal.hom_ext _ _ }
  let : LocallyOfFinitePresentation (terminal.from h.S₀) :=
    model_base_finitePresentation h
  obtain ⟨i, g, hg, -⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D t (terminal.from h.S₀) c (baseSchemeIsLimitAt S R₀)
    h.toBase (by ext i; exact terminal.hom_ext _ _)
  exact ⟨i, g, hg⟩

private noncomputable def model_baseChange
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X S T : Scheme.{u}} {f : X ⟶ S}
    (h : FiniteTypeAffineModel P f) (g : T ⟶ h.S₀) (b : S ⟶ T)
    (hb : b ≫ g = h.toBase) [IsAffine T]
    [LocallyOfFiniteType (terminal.from T)] [QuasiCompact (terminal.from T)] :
    FiniteTypeAffineModel P f := by
  classical
  letI : IsAffine h.X₀ := h.source_affine
  letI : IsAffine h.S₀ := h.base_affine
  let a : X ⟶ pullback h.f₀ g :=
    pullback.lift h.toSource (f ≫ b) (by simpa [hb, Category.assoc] using h.isPullback.w)
  have ha : a ≫ pullback.fst h.f₀ g = h.toSource := pullback.lift_fst _ _ _
  have hp : IsPullback a f (pullback.snd h.f₀ g) b := by
    have hs : IsPullback (a ≫ pullback.fst h.f₀ g) f h.f₀ (b ≫ g) := by
      rw [ha, hb]; exact h.isPullback
    exact hs.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback h.f₀ g)
  letI : LocallyOfFiniteType h.f₀ := h.locallyOfFiniteType
  letI : QuasiCompact h.f₀ := h.quasiCompact
  exact {
    X₀ := pullback h.f₀ g
    S₀ := T
    f₀ := pullback.snd h.f₀ g
    toSource := a
    toBase := b
    isPullback := hp
    source_affine := inferInstance
    base_affine := inferInstance
    base_locallyOfFiniteType := inferInstance
    base_quasiCompact := inferInstance
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    property := MorphismProperty.pullback_snd h.f₀ g h.property }

/-- The base of a base-changed model is the new base. -/
private lemma model_baseChange_S₀
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X S T : Scheme.{u}} {f : X ⟶ S}
    (h : FiniteTypeAffineModel P f) (g : T ⟶ h.S₀) (b : S ⟶ T)
    (hb : b ≫ g = h.toBase) [IsAffine T]
    [LocallyOfFiniteType (terminal.from T)] [QuasiCompact (terminal.from T)] :
    (model_baseChange h g b hb).S₀ = T := rfl

/-- The modeled morphism of a base-changed model is the base change of the modeled morphism. -/
private lemma model_baseChange_f₀
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X S T : Scheme.{u}} {f : X ⟶ S}
    (h : FiniteTypeAffineModel P f) (g : T ⟶ h.S₀) (b : S ⟶ T)
    (hb : b ≫ g = h.toBase) [IsAffine T]
    [LocallyOfFiniteType (terminal.from T)] [QuasiCompact (terminal.from T)] :
    (model_baseChange h g b hb).f₀ = pullback.snd h.f₀ g := rfl

private noncomputable def model_over_iso
    {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} {f : X ⟶ S}
    (h : FiniteTypeAffineModel P f) :
    Over.mk f ≅ (Over.pullback h.toBase).obj (Over.mk h.f₀) :=
  Over.isoMk h.isPullback.isoPullback (by simp)

private theorem finitePresentation_pullback_snd
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hf : FinitePresentation f) :
    FinitePresentation (pullback.snd f g) := by
  let : LocallyOfFinitePresentation f := hf.1
  let : QuasiCompact f := hf.2.1
  let : QuasiSeparated f := hf.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem over_pullback_map_fst {T S : Scheme.{u}} (b : S ⟶ T)
    {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback b).map g).left ≫ pullback.fst B.hom b =
      pullback.fst A.hom b ≫ g.left := by
  change pullback.lift (pullback.fst A.hom b ≫ g.left) (pullback.snd A.hom b)
    (by rw [Category.assoc, Over.w g, pullback.condition]) ≫ pullback.fst B.hom b = _
  exact pullback.lift_fst _ _ _

private theorem over_pullback_map_eq_of_further
    {T U V : Scheme.{u}} (e : U ⟶ T) (d : V ⟶ U)
    {A B : Over T} (f g : A ⟶ B)
    (h : (Over.pullback e).map f = (Over.pullback e).map g) :
    (Over.pullback (d ≫ e)).map f = (Over.pullback (d ≫ e)).map g := by
  let η := Over.pullbackComp d e
  rw [← cancel_mono (η.hom.app B), η.hom.naturality, η.hom.naturality,
    Functor.comp_map, Functor.comp_map, h]


/-- Suppose `G : X' ⟶ Y'` becomes the isomorphism `α` after transporting along the
isomorphisms `αA : X' ≅ X` and `αB : Y' ≅ Y`. Then `G` is itself an isomorphism, with inverse
the composite `αB ≪≫ α.symm ≪≫ αA.symm`. -/
private lemma comp_trans_symm_eq_id {C : Type*} [Category C] {X Y X' Y' : C}
    (α : X ≅ Y) (αA : X' ≅ X) (αB : Y' ≅ Y) (G : X' ⟶ Y')
    (hg : αA.hom ≫ α.hom = G ≫ αB.hom) :
    G ≫ (αB ≪≫ α.symm ≪≫ αA.symm).hom = 𝟙 X' ∧
      (αB ≪≫ α.symm ≪≫ αA.symm).hom ≫ G = 𝟙 Y' := by
  have hGβ : G ≫ (αB ≪≫ α.symm ≪≫ αA.symm).hom = 𝟙 X' := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Category.assoc, ← hg]
    simp
  have hβG : ((αB ≪≫ α.symm ≪≫ αA.symm).hom ≫ G) ≫ (αB ≪≫ α.symm ≪≫ αA.symm).hom =
      𝟙 Y' ≫ (αB ≪≫ α.symm ≪≫ αA.symm).hom := by
    rw [Category.assoc, hGβ, Category.comp_id, Category.id_comp]
  exact ⟨hGβ, (cancel_mono _).mp hβG⟩

/-- If `Gk` and `Hk` correspond to the mutually inverse morphisms `gj` and `β.hom` under the
isomorphisms `βA` and `βB`, then `Gk` and `Hk` are mutually inverse. -/
private lemma comp_eq_id_of_descent {C : Type*} [Category C] {Aj' Bj' Ak' Bk' : C}
    (gj : Aj' ⟶ Bj') (β : Bj' ≅ Aj') (βA : Ak' ≅ Aj') (βB : Bk' ≅ Bj')
    (Gk : Ak' ⟶ Bk') (Hk : Bk' ⟶ Ak')
    (hnat : βA.hom ≫ gj = Gk ≫ βB.hom)
    (hh : βB.hom ≫ β.hom = Hk ≫ βA.hom)
    (hgbeta : gj ≫ β.hom = 𝟙 Aj') (hbetag : β.hom ≫ gj = 𝟙 Bj') :
    Gk ≫ Hk = 𝟙 Ak' ∧ Hk ≫ Gk = 𝟙 Bk' := by
  constructor
  · rw [← cancel_mono βA.hom, Category.assoc, ← hh, ← Category.assoc, ← hnat, Category.assoc,
      hgbeta, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono βB.hom, Category.assoc, ← hnat, ← Category.assoc, ← hh, Category.assoc,
      hbetag, Category.comp_id, Category.id_comp]

/-- Comparison isomorphisms `βA` and `βB` between iterated and direct pullbacks over `T`,
compatible with the first projections, commute with the pullbacks of a morphism `g : Aj ⟶ Bj`. -/
private lemma over_pullback_map_naturality_of_descent
    {T T' Z : Scheme.{u}} (dk : T' ⟶ T) (cj : Z ⟶ T) (ck : Z ⟶ T')
    {Aj Bj : Over T} (g : Aj ⟶ Bj)
    (βA : (Over.pullback ck).obj ((Over.pullback dk).obj Aj) ≅ (Over.pullback cj).obj Aj)
    (βB : (Over.pullback ck).obj ((Over.pullback dk).obj Bj) ≅ (Over.pullback cj).obj Bj)
    (hβA : βA.hom.left ≫ pullback.fst Aj.hom cj =
      pullback.fst ((Over.pullback dk).obj Aj).hom ck ≫ pullback.fst Aj.hom dk)
    (hβB : βB.hom.left ≫ pullback.fst Bj.hom cj =
      pullback.fst ((Over.pullback dk).obj Bj).hom ck ≫ pullback.fst Bj.hom dk) :
    βA.hom ≫ (Over.pullback cj).map g =
      (Over.pullback ck).map ((Over.pullback dk).map g) ≫ βB.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, over_pullback_map_fst]
    conv_lhs => rw [← Category.assoc, hβA]
    conv_rhs => rw [hβB]
    conv_rhs => rw [← Category.assoc, over_pullback_map_fst]
    conv_rhs => rw [Category.assoc, over_pullback_map_fst]
    rfl
  · exact (Over.w (βA.hom ≫ (Over.pullback cj).map g)).trans
      (Over.w ((Over.pullback ck).map ((Over.pullback dk).map g) ≫ βB.hom)).symm

/-- Two finite-type affine models of an affine morphism of finite presentation, for properties
stable under base change, can be combined into one model on which both properties hold. -/
@[stacks 05FL]
theorem exists_finiteTypeAffineModel_inf
    (P Q : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [Q.IsStableUnderBaseChange] {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    (hP : FiniteTypeAffineModel P f) (hQ : FiniteTypeAffineModel Q f) :
    Nonempty (FiniteTypeAffineModel (P ⊓ Q) f) := by
  classical
  let R₀ : Subring Γ(S, ⊤) := ⊥
  let : Algebra.FiniteType ℤ R₀ := bottom_finiteType _
  let D := baseSchemeDiagram R₀
  let c := baseSchemeConeAt S R₀
  obtain ⟨iP, gP, hgP⟩ := model_base_factors hP
  obtain ⟨iQ, gQ, hgQ⟩ := model_base_factors hQ
  change c.π.app iP ≫ gP = hP.toBase at hgP
  change c.π.app iQ ≫ gQ = hQ.toBase at hgQ
  let i := IsCofiltered.min iP iQ
  let pTo : D.obj i ⟶ hP.S₀ := D.map (IsCofiltered.minToLeft iP iQ) ≫ gP
  let qTo : D.obj i ⟶ hQ.S₀ := D.map (IsCofiltered.minToRight iP iQ) ≫ gQ
  have hpTo : c.π.app i ≫ pTo = hP.toBase := by
    dsimp [pTo]
    rwa [← Category.assoc, c.w]
  have hqTo : c.π.app i ≫ qTo = hQ.toBase := by
    dsimp [qTo]
    rwa [← Category.assoc, c.w]
  let pModel := model_baseChange hP pTo (c.π.app i) hpTo
  let qModel := model_baseChange hQ qTo (c.π.app i) hqTo
  let A : Over (D.obj i) := Over.mk pModel.f₀
  let B : Over (D.obj i) := Over.mk qModel.f₀
  have hA : FinitePresentation A.hom := model_finitePresentation pModel
  have hB : FinitePresentation B.hom := model_finitePresentation qModel
  let α : (Over.pullback (c.π.app i)).obj A ≅
      (Over.pullback (c.π.app i)).obj B :=
    (model_over_iso pModel).symm ≪≫ model_over_iso qModel
  obtain ⟨j, e, g, αA, αB, hαA, hαB, hg⟩ :=
    exists_morphism_after_baseChange D c (baseSchemeIsLimitAt S R₀)
      i A B hA hB α.hom
  let Aj := (Over.pullback (D.map e)).obj A
  let Bj := (Over.pullback (D.map e)).obj B
  have hAj : FinitePresentation Aj.hom :=
    finitePresentation_pullback_snd A.hom (D.map e) hA
  have hBj : FinitePresentation Bj.hom :=
    finitePresentation_pullback_snd B.hom (D.map e) hB
  let β : (Over.pullback (c.π.app j)).obj Bj ≅
      (Over.pullback (c.π.app j)).obj Aj :=
    αB ≪≫ α.symm ≪≫ αA.symm
  obtain ⟨k, ek, h, βB, βA, hβB, hβA, hh⟩ :=
    exists_morphism_after_baseChange D c (baseSchemeIsLimitAt S R₀)
      j Bj Aj hBj hAj β.hom
  let Ak := (Over.pullback (D.map ek)).obj Aj
  let Bk := (Over.pullback (D.map ek)).obj Bj
  let G : Ak ⟶ Bk := (Over.pullback (D.map ek)).map g
  have hnat : βA.hom ≫ (Over.pullback (c.π.app j)).map g =
      (Over.pullback (c.π.app k)).map G ≫ βB.hom :=
    over_pullback_map_naturality_of_descent (D.map ek) (c.π.app j) (c.π.app k) g βA βB hβA hβB
  obtain ⟨hgbeta, hbetag⟩ :=
    comp_trans_symm_eq_id α αA αB ((Over.pullback (c.π.app j)).map g) hg
  obtain ⟨hkGH', hkHG'⟩ :=
    comp_eq_id_of_descent ((Over.pullback (c.π.app j)).map g) β βA βB
      ((Over.pullback (c.π.app k)).map G) ((Over.pullback (c.π.app k)).map h)
      hnat hh hgbeta hbetag
  have hkGH : (Over.pullback (c.π.app k)).map (G ≫ h) = 𝟙 _ := by
    rwa [Functor.map_comp]
  have hkHG : (Over.pullback (c.π.app k)).map (h ≫ G) = 𝟙 _ := by
    rwa [Functor.map_comp]
  have hAk : FinitePresentation Ak.hom :=
    finitePresentation_pullback_snd Aj.hom (D.map ek) hAj
  have hBk : FinitePresentation Bk.hom :=
    finitePresentation_pullback_snd Bj.hom (D.map ek) hBj
  obtain ⟨lA, elA, hEqA⟩ := eventually_eq_of_baseChange_eq
    D c (baseSchemeIsLimitAt S R₀) k Ak Ak hAk hAk (G ≫ h) (𝟙 Ak)
      (by simpa using hkGH)
  obtain ⟨lB, elB, hEqB⟩ := eventually_eq_of_baseChange_eq
    D c (baseSchemeIsLimitAt S R₀) k Bk Bk hBk hBk (h ≫ G) (𝟙 Bk)
      (by simpa using hkHG)
  let m := IsCofiltered.min lA lB
  let emA : m ⟶ k := IsCofiltered.minToLeft lA lB ≫ elA
  let emB : m ⟶ k := IsCofiltered.minToRight lA lB ≫ elB
  have hem : emA = emB := Subsingleton.elim _ _
  have hEqAm : (Over.pullback (D.map emA)).map (G ≫ h) =
      (Over.pullback (D.map emA)).map (𝟙 Ak) := by
    have hmap : D.map emA =
        D.map (IsCofiltered.minToLeft lA lB) ≫ D.map elA := by simp [emA]
    rw [hmap]
    exact over_pullback_map_eq_of_further (D.map elA)
      (D.map (IsCofiltered.minToLeft lA lB)) (G ≫ h) (𝟙 Ak) hEqA
  have hEqBm : (Over.pullback (D.map emA)).map (h ≫ G) =
      (Over.pullback (D.map emA)).map (𝟙 Bk) := by
    rw [hem]
    have hmap : D.map emB =
        D.map (IsCofiltered.minToRight lA lB) ≫ D.map elB := by simp [emB]
    rw [hmap]
    exact over_pullback_map_eq_of_further (D.map elB)
      (D.map (IsCofiltered.minToRight lA lB)) (h ≫ G) (𝟙 Bk) hEqB
  let Gm := (Over.pullback (D.map emA)).map G
  let Hm := (Over.pullback (D.map emA)).map h
  have hGH : Gm ≫ Hm = 𝟙 _ := by simpa [Gm, Hm] using hEqAm
  have hHG : Hm ≫ Gm = 𝟙 _ := by simpa [Gm, Hm] using hEqBm
  let iso : (Over.pullback (D.map emA)).obj Ak ≅
      (Over.pullback (D.map emA)).obj Bk :=
    ⟨Gm, Hm, hGH, hHG⟩
  let pJ := model_baseChange pModel (D.map e) (c.π.app j) (c.w e)
  let qJ := model_baseChange qModel (D.map e) (c.π.app j) (c.w e)
  let pK := model_baseChange pJ (D.map ek) (c.π.app k) (c.w ek)
  let qK := model_baseChange qJ (D.map ek) (c.π.app k) (c.w ek)
  let pM := model_baseChange pK (D.map emA) (c.π.app m) (c.w emA)
  let qM := model_baseChange qK (D.map emA) (c.π.app m) (c.w emA)
  have hQm : Q pM.f₀ := by
    change Q ((Over.pullback (D.map emA)).obj Ak).hom
    have : IsIso iso.hom := Iso.isIso_hom iso
    have : IsIso iso.hom.left := (Over.forget (D.obj m)).map_isIso iso.hom
    have hs : IsPullback iso.hom.left
        ((Over.pullback (D.map emA)).obj Ak).hom
        ((Over.pullback (D.map emA)).obj Bk).hom (𝟙 (D.obj m)) :=
      IsPullback.of_horiz_isIso
        (CommSq.mk (by simpa only [Category.comp_id] using (Over.w iso.hom)))
    exact MorphismProperty.of_isPullback hs qM.property
  exact ⟨{ pM with property := ⟨pM.property, hQm⟩ }⟩

/-- Let `Q g ⊆ S'` be, for every morphism `g : X' ⟶ S'`, the locus of points of the target where
some condition on the fibre of `g` holds. Assume that `Q` is compatible with base change and
that it is locally constructible for a morphism of finite presentation between affine schemes
over a Noetherian affine base. Then an affine finite-type model of a morphism `f` of affine
schemes of finite presentation all of whose fibres satisfy the condition can be refined, by a
further base change of its base, to one all of whose fibres satisfy the condition too. -/
theorem exists_finiteTypeAffineModel_fiberwise
    (Q : ∀ X' S' : Scheme.{u}, (X' ⟶ S') → Set S')
    (hbc : ∀ {X₁ S₁ X₂ S₂ : Scheme.{u}} {a : X₂ ⟶ X₁} {g₂ : X₂ ⟶ S₂} {g₁ : X₁ ⟶ S₁}
      {b : S₂ ⟶ S₁}, LocallyOfFiniteType g₁ → IsPullback a g₂ g₁ b →
      Q X₂ S₂ g₂ = b ⁻¹' Q X₁ S₁ g₁)
    (hloc : ∀ (X' S' : Scheme.{u}) (g : X' ⟶ S'), IsAffine X' → IsAffine S' →
      IsLocallyNoetherian S' → FinitePresentation g →
      Topology.IsLocallyConstructible (Q X' S' g))
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] {f : X ⟶ S}
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    (m : FiniteTypeAffineModel ⊤ f) (hf : ∀ s : S, s ∈ Q X S f) :
    ∃ m' : FiniteTypeAffineModel ⊤ f, ∀ s₀ : m'.S₀, s₀ ∈ Q m'.X₀ m'.S₀ m'.f₀ := by
  classical
  let R₀ : Subring Γ(S, ⊤) := ⊥
  let : Algebra.FiniteType ℤ R₀ := bottom_finiteType _
  let D := baseSchemeDiagram R₀
  let c := baseSchemeConeAt S R₀
  let : IsAffine m.X₀ := m.source_affine
  let : IsAffine m.S₀ := m.base_affine
  let : LocallyOfFiniteType m.f₀ := m.locallyOfFiniteType
  let : QuasiCompact m.f₀ := m.quasiCompact
  obtain ⟨i, g, hg⟩ := model_base_factors m
  let Dsit : DescentSituation.{u, u} (Algebra.FiniteTypeSystem.Index R₀) :=
    { system := D
      transition_affine := fun _ ↦ inferInstance
      quasiCompact := fun _ ↦ inferInstance
      quasiSeparated := fun _ ↦ inferInstance
      limitCone := c
      isLimit := baseSchemeIsLimitAt S R₀
      base := i.unop }
  let E : Set (D.obj i) := g ⁻¹' Q m.X₀ m.S₀ m.f₀
  have hE : Topology.IsLocallyConstructible E := by
    have h := hloc _ _ (pullback.snd m.f₀ g) inferInstance inferInstance inferInstance
      (finitePresentation_pullback_snd m.f₀ g (model_finitePresentation m))
    rwa [hbc m.locallyOfFiniteType (IsPullback.of_hasPullback m.f₀ g)] at h
  have hlim : Set.range (Dsit.limitCone.π.app (Opposite.op Dsit.base)).base ⊆ E := by
    rintro _ ⟨x, rfl⟩
    have hx := hf x
    rw [hbc m.locallyOfFiniteType m.isPullback] at hx
    change g (c.π.app i x) ∈ Q m.X₀ m.S₀ m.f₀
    rwa [← Scheme.Hom.comp_apply, hg]
  obtain ⟨j, hle, hsub⟩ :=
    (eventually_range_transition_subset_of_isLocallyConstructible Dsit E hE hlim).exists
  let t : D.obj (Opposite.op j) ⟶ D.obj i := D.map (homOfLE hle).op
  have hw : c.π.app (Opposite.op j) ≫ (t ≫ g) = m.toBase := by
    rw [← Category.assoc]
    change (c.π.app (Opposite.op j) ≫ D.map (homOfLE hle).op) ≫ g = m.toBase
    rwa [c.w (homOfLE hle).op]
  refine ⟨model_baseChange m (t ≫ g) (c.π.app (Opposite.op j)) hw, fun s₀ ↦ ?_⟩
  change s₀ ∈ Q (pullback m.f₀ (t ≫ g)) (D.obj (Opposite.op j)) (pullback.snd m.f₀ (t ≫ g))
  rw [hbc m.locallyOfFiniteType (IsPullback.of_hasPullback m.f₀ (t ≫ g))]
  exact hsub ⟨s₀, rfl⟩

end AlgebraicGeometry
