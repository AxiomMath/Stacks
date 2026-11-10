module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageStructureSheafSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGeometricallyConnectedGlobalFunctions

/-!
# Global functions of the fibre over an étale chart, formed over the chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces and let `v : V ⟶ Y` be an étale chart of `Y`,
given by a section `v` of `Y` over an object `T ⟶ S` of the big fppf site. The algebraic space
`X ×_Y V` over `S` and the fibre of `f` over `v` formed over the base `T`
(`AlgebraicGeometry.Space.restrictedFibre`) have the same scheme charts, so they have the same
global functions. For `T = Spec A` this reads the structure map `f♯ : 𝒪_Y(V) ⟶ (f_*𝒪_X)(V)` of
Stacks 03G8 as the algebra map from `A` to the global functions of the fibre.

## Main definitions

* `AlgebraicGeometry.Space.chartFunctionsFibreEquiv`: the ring isomorphism between the
  functions on the scheme charts of `X ×_Y V` and those of the fibre.

## Main results

* `AlgebraicGeometry.Space.bijective_structureSharp_app_iff_bijective_algebraMap`: for an étale
  chart with source `Spec A`, `f♯` is bijective on it exactly when the global functions of the
  fibre of `f` over it are `A`.
* `AlgebraicGeometry.Space.isIso_structureSharp_of_bijective_algebraMap`: `f♯` is an isomorphism
  as soon as this holds for every such chart.

## Implementation notes

A scheme chart `α : U ⟶ restrictedFibre f v` over `T` is a point of `X` over `U` viewed over
`S` whose image in `Y` is `v` pulled back along `U ⟶ T`; with the morphism `U ⟶ T = V` it is a
point of `X ×_Y V` (`AlgebraicGeometry.Space.fibrePointLift`). Conversely a scheme chart of
`X ×_Y V` over `U` comes with `U ⟶ V`, which presents `U` as an object over `T`
(`AlgebraicGeometry.Space.basePointToFibre`). The two constructions are inverse up to morphisms
of charts which are identities on underlying schemes, and the functions on all scheme charts are
compared through `AlgebraicGeometry.Space.globalFunctionsChartEquiv`, so that no étaleness of
charts has to be checked.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : Scheme.{u}} (hT : B.Contains T)
    (g : B.obj hT ⟶ B.obj hS) (v : Y.1.obj (op (Over.mk g)))
    (hv : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (yonedaEquiv.symm v)))

/-- The étale chart of `Y` given by a section `v` of `Y` over `T ⟶ S`. -/
abbrev etaleSectionChart : SmallEtale B S hS Y.1 :=
  ⟨CostructuredArrow.mk (yonedaEquiv.symm v), hv⟩

/-- The cartesian square exhibiting `X ×_Y V` as a fibre product of algebraic spaces. -/
theorem isPullback_etaleSectionChart :
    IsPullback ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hT g v hv)))
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom
      ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hT g v hv)).1.hom f :=
  (spacesBaseChange B S hS f).isPullback _

variable {B S hS f hT g v hv} in
/-- Two scheme points of `X ×_Y V` agree when their two projections agree. -/
theorem sectionChartBaseChange_hom_ext {U : BigFppfOver B S hS}
    {a b : yoneda.obj U ⟶ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1}
    (h₁ : a ≫ ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hT g v hv))).hom =
      b ≫ ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hT g v hv))).hom)
    (h₂ : a ≫ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom.hom =
      b ≫ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom.hom) :
    a = b := by
  let a' : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left :=
    ObjectProperty.homMk a
  let b' : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left :=
    ObjectProperty.homMk b
  have := (isPullback_etaleSectionChart B S hS f hT g v hv).hom_ext (k := a') (l := b')
    (ObjectProperty.hom_ext _ h₁) (ObjectProperty.hom_ext _ h₂)
  exact congrArg (fun m => m.hom) this

variable {B S hS} in
/-- Identifying sections of a restriction with sections of the original presheaf is natural in
the presheaf. -/
theorem restrictYonedaEquiv_comp_map {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : F ⟶ G)
    {U : BigFppfOver B T hT} (t : yoneda.obj U ⟶ (OverShriek.relocalizeRestrict g).obj F) :
    OverShriek.restrictYonedaEquiv g U G (t ≫ (OverShriek.relocalizeRestrict g).map φ) =
      OverShriek.restrictYonedaEquiv g U F t ≫ φ := by
  apply yonedaEquiv.injective
  simp only [OverShriek.restrictYonedaEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    yonedaEquiv_comp]
  rfl

variable {B S hS} in
/-- The tautological section of the restriction of `Y`, pulled back to an object `U` of the big
fppf site of `T` and read as a section of `Y`, is the section `v` pulled back along `U ⟶ T`. -/
theorem restrictYonedaEquiv_comp_restrictedSection (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (v : Y.obj (op (Over.mk g))) {U : BigFppfOver B T hT}
    (k : U ⟶ Over.mk (𝟙 (B.obj hT))) :
    OverShriek.restrictYonedaEquiv g U Y (yoneda.map k ≫ restrictedSection B S hS Y hT g v) =
      yoneda.map (Over.homMk U.hom rfl : (Over.map g).obj U ⟶ Over.mk g) ≫ yonedaEquiv.symm v := by
  apply yonedaEquiv.injective
  simp only [OverShriek.restrictYonedaEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    yonedaEquiv_comp, yonedaEquiv_yoneda_map, restrictedSection]
  change Y.map ((Over.map g).map k).op v = Y.map (Over.homMk U.hom rfl :
    (Over.map g).obj U ⟶ Over.mk g).op v
  have hk : (Over.map g).map k = (Over.homMk U.hom rfl : (Over.map g).obj U ⟶ Over.mk g) :=
    Over.OverMorphism.ext (by simpa using Over.w k)
  rw [hk]
  rfl

variable {B S hS} in
/-- The projection of the fibre of `f` over `v` to the restriction of `X`. -/
noncomputable abbrev restrictedFibreFst {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (v : Y.obj (op (Over.mk g))) :
    restrictedFibre B S hS f hT g v ⟶ (OverShriek.relocalizeRestrict g).obj X :=
  pullback.fst _ _

variable {B S hS} in
/-- The projection of the fibre of `f` over `v` to the final object. -/
noncomputable abbrev restrictedFibreSnd {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (v : Y.obj (op (Over.mk g))) :
    restrictedFibre B S hS f hT g v ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hT))) :=
  pullback.snd _ _

variable {B S hS} in
/-- The fibre of `f` over `v` is a fibre product. -/
theorem restrictedFibre_isPullback {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (v : Y.obj (op (Over.mk g))) :
    IsPullback (restrictedFibreFst hT g f v) (restrictedFibreSnd hT g f v)
      ((OverShriek.relocalizeRestrict g).map f) (restrictedSection B S hS Y hT g v) :=
  IsPullback.of_hasPullback _ _

/-- A scheme point of the fibre of `f` over `v`, read as a point of `X`, maps to the point of `Y`
given by `v`. -/
theorem restrictYonedaEquiv_fibrePoint_comp {U : BigFppfOver B T hT}
    (α : yoneda.obj U ⟶ restrictedFibre B S hS f.hom hT g v) :
    OverShriek.restrictYonedaEquiv g U X.1 (α ≫ restrictedFibreFst hT g f.hom v) ≫ f.hom =
      yoneda.map (Over.homMk U.hom rfl : (Over.map g).obj U ⟶ Over.mk g) ≫ yonedaEquiv.symm v := by
  have hc : (α ≫ restrictedFibreFst hT g f.hom v) ≫ (OverShriek.relocalizeRestrict g).map f.hom =
      yoneda.map (Yoneda.fullyFaithful.preimage (α ≫ restrictedFibreSnd hT g f.hom v)) ≫
        restrictedSection B S hS Y.1 hT g v := by
    rw [Yoneda.fullyFaithful.map_preimage, Category.assoc, Category.assoc,
      (restrictedFibre_isPullback hT g f.hom v).w]
  rw [← restrictYonedaEquiv_comp_map, hc, restrictYonedaEquiv_comp_restrictedSection]

/-- The square of presheaves underlying `X ×_Y V`. -/
theorem sectionChartProj_comp :
    ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hT g v hv))).hom ≫
        yonedaEquiv.symm v =
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom.hom ≫ f.hom :=
  congrArg InducedCategory.Hom.hom (isPullback_etaleSectionChart B S hS f hT g v hv).w

/-- The scheme point of `X ×_Y V` over `U`, viewed over `S`, attached to a scheme point of the
fibre of `f` over `v` formed over `T`, as a morphism of algebraic spaces. -/
noncomputable def fibrePointLift {U : BigFppfOver B T hT}
    (α : yoneda.obj U ⟶ restrictedFibre B S hS f.hom hT g v) :
    (⟨yoneda.obj ((Over.map g).obj U), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left :=
  (isPullback_etaleSectionChart B S hS f hT g v hv).lift
    (ObjectProperty.homMk (yoneda.map (Over.homMk U.hom rfl : (Over.map g).obj U ⟶ Over.mk g)))
    (ObjectProperty.homMk
      (OverShriek.restrictYonedaEquiv g U X.1 (α ≫ restrictedFibreFst hT g f.hom v)))
    (ObjectProperty.hom_ext _
      (restrictYonedaEquiv_fibrePoint_comp B S hS f hT g v α).symm)

/-- The scheme point of `X ×_Y V` attached to a scheme point of the fibre. -/
noncomputable abbrev fibrePointToBaseChange {U : BigFppfOver B T hT}
    (α : yoneda.obj U ⟶ restrictedFibre B S hS f.hom hT g v) :
    yoneda.obj ((Over.map g).obj U) ⟶
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1 :=
  (fibrePointLift B S hS f hT g v hv α).hom

/-- The point of `X ×_Y V` attached to a point of the fibre projects to `V` by the structure
morphism of the point. -/
theorem fibrePointToBaseChange_proj {U : BigFppfOver B T hT}
    (α : yoneda.obj U ⟶ restrictedFibre B S hS f.hom hT g v) :
    (fibrePointLift B S hS f hT g v hv α).hom ≫ ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hT g v hv))).hom =
      yoneda.map (Over.homMk U.hom rfl : (Over.map g).obj U ⟶ Over.mk g) :=
  congrArg InducedCategory.Hom.hom
    ((isPullback_etaleSectionChart B S hS f hT g v hv).lift_fst _ _ _)

/-- The point of `X ×_Y V` attached to a point of the fibre projects to `X` by the point of `X`
that the point of the fibre carries. -/
theorem fibrePointToBaseChange_toX {U : BigFppfOver B T hT}
    (α : yoneda.obj U ⟶ restrictedFibre B S hS f.hom hT g v) :
    (fibrePointLift B S hS f hT g v hv α).hom ≫
        (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom.hom =
      OverShriek.restrictYonedaEquiv g U X.1 (α ≫ restrictedFibreFst hT g f.hom v) :=
  congrArg InducedCategory.Hom.hom
    ((isPullback_etaleSectionChart B S hS f hT g v hv).lift_snd _ _ _)

/-- The point of `X ×_Y V` attached to a point of the fibre is natural in the point. -/
theorem fibrePointToBaseChange_naturality {U₁ U₂ : BigFppfOver B T hT} (k : U₁ ⟶ U₂)
    (α : yoneda.obj U₂ ⟶ restrictedFibre B S hS f.hom hT g v) :
    (fibrePointLift B S hS f hT g v hv (yoneda.map k ≫ α)).hom =
      yoneda.map ((Over.map g).map k) ≫ (fibrePointLift B S hS f hT g v hv α).hom := by
  refine sectionChartBaseChange_hom_ext ?_ ?_
  · rw [Category.assoc, fibrePointToBaseChange_proj, fibrePointToBaseChange_proj]
    exact (congrArg yoneda.map (Over.OverMorphism.ext (Over.w k).symm)).trans
      (yoneda.map_comp _ _)
  · rw [Category.assoc, fibrePointToBaseChange_toX, fibrePointToBaseChange_toX]
    exact restrictYonedaEquiv_yoneda_map_comp g X.1 k (α ≫ restrictedFibreFst hT g f.hom v)

section BasePoint

variable {U' : BigFppfOver B S hS}
    (β : yoneda.obj U' ⟶ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1)

/-- The morphism to `V` underlying a scheme point of `X ×_Y V`. -/
noncomputable abbrev basePointToV : U' ⟶ Over.mk g :=
  Yoneda.fullyFaithful.preimage (β ≫ ((spacesBaseChange B S hS f).projection.app
    ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hT g v hv))).hom)

/-- The object of the big fppf site of `T` underlying a scheme point of `X ×_Y V`. -/
noncomputable abbrev basePointBase : BigFppfOver B T hT :=
  Over.mk (basePointToV B S hS f hT g v hv β).left

/-- A scheme point of `X ×_Y V` lies over `T`. -/
noncomputable abbrev basePointIso :
    U' ⟶ (Over.map g).obj (basePointBase B S hS f hT g v hv β) :=
  relocalizeBaseHom B T S hT hS g (Over.w (basePointToV B S hS f hT g v hv β))

/-- Read over `T`, a scheme point of `X ×_Y V` maps to `V` by its structure morphism. -/
theorem inv_basePointIso_comp :
    inv (basePointIso B S hS f hT g v hv β) ≫ basePointToV B S hS f hT g v hv β =
      (Over.homMk (basePointBase B S hS f hT g v hv β).hom rfl :
        (Over.map g).obj (basePointBase B S hS f hT g v hv β) ⟶ Over.mk g) := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, inv_relocalizeBaseHom_left]
  exact Category.id_comp _

/-- The two images of a scheme point of `X ×_Y V` in `Y` agree. -/
theorem basePoint_comp_eq :
    β ≫ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom.hom ≫ f.hom =
      yoneda.map (basePointToV B S hS f hT g v hv β) ≫ yonedaEquiv.symm v :=
  (congrArg (β ≫ ·) (sectionChartProj_comp B S hS f hT g v hv).symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yonedaEquiv.symm v)
      (Yoneda.fullyFaithful.map_preimage _).symm))

/-- The scheme point of the fibre of `f` over `v`, formed over `T`, attached to a scheme point of
`X ×_Y V`. -/
noncomputable def basePointToFibre :
    yoneda.obj (basePointBase B S hS f hT g v hv β) ⟶ restrictedFibre B S hS f.hom hT g v :=
  (restrictedFibre_isPullback hT g f.hom v).lift
    ((OverShriek.restrictYonedaEquiv g _ X.1).symm
      (yoneda.map (inv (basePointIso B S hS f hT g v hv β)) ≫ β ≫
        (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom.hom))
    (yoneda.map (Over.homMk (basePointToV B S hS f hT g v hv β).left (by simp) :
      basePointBase B S hS f hT g v hv β ⟶ Over.mk (𝟙 (B.obj hT))))
    (by
      apply (OverShriek.restrictYonedaEquiv g _ Y.1).injective
      rw [restrictYonedaEquiv_comp_map, Equiv.apply_symm_apply,
        restrictYonedaEquiv_comp_restrictedSection, Category.assoc]
      exact (congrArg (yoneda.map (inv (basePointIso B S hS f hT g v hv β)) ≫ ·)
        (basePoint_comp_eq B S hS f hT g v hv β)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ yonedaEquiv.symm v) ((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map (inv_basePointIso_comp B S hS f hT g v hv β))))))

/-- The point of the fibre attached to a point of `X ×_Y V` projects to the point of `X` it
carries. -/
theorem basePointToFibre_fst :
    basePointToFibre B S hS f hT g v hv β ≫ restrictedFibreFst hT g f.hom v =
      (OverShriek.restrictYonedaEquiv g _ X.1).symm
        (yoneda.map (inv (basePointIso B S hS f hT g v hv β)) ≫ β ≫
          (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.hom.hom) :=
  (restrictedFibre_isPullback hT g f.hom v).lift_fst _ _ _

variable {B S hS f hT g v hv} in
/-- Two scheme points of the fibre of `f` over `v` agree once they agree in the restriction of
`X`. -/
theorem restrictedFibre_hom_ext {U : BigFppfOver B T hT}
    {a b : yoneda.obj U ⟶ restrictedFibre B S hS f.hom hT g v}
    (h : OverShriek.restrictYonedaEquiv g U X.1 (a ≫ restrictedFibreFst hT g f.hom v) =
      OverShriek.restrictYonedaEquiv g U X.1 (b ≫ restrictedFibreFst hT g f.hom v)) :
    a = b :=
  (restrictedFibre_isPullback hT g f.hom v).hom_ext
    ((OverShriek.restrictYonedaEquiv g U X.1).injective h)
    (((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hT)))).isTerminalObj yoneda _).hom_ext
      _ _)

/-- A morphism of scheme points of `X ×_Y V` induces a morphism of the objects of the big fppf
site of `T` underlying them. -/
noncomputable def basePointBaseMap {U₁ U₂ : BigFppfOver B S hS} (m : U₁ ⟶ U₂)
    {β₁ : yoneda.obj U₁ ⟶ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1}
    {β₂ : yoneda.obj U₂ ⟶ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1}
    (h : yoneda.map m ≫ β₂ = β₁) :
    basePointBase B S hS f hT g v hv β₁ ⟶ basePointBase B S hS f hT g v hv β₂ :=
  Over.homMk m.left (by
    change m.left ≫ (basePointToV B S hS f hT g v hv β₂).left =
      (basePointToV B S hS f hT g v hv β₁).left
    rw [← Over.comp_left]
    congr 1
    apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, Yoneda.fullyFaithful.map_preimage, Yoneda.fullyFaithful.map_preimage,
      ← h]
    exact (Category.assoc _ _ _).symm)

/-- The point of the fibre attached to a point of `X ×_Y V` is natural in the point. -/
theorem basePointToFibre_naturality {U₁ U₂ : BigFppfOver B S hS} (m : U₁ ⟶ U₂)
    {β₁ : yoneda.obj U₁ ⟶ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1}
    {β₂ : yoneda.obj U₂ ⟶ (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1}
    (h : yoneda.map m ≫ β₂ = β₁) :
    yoneda.map (basePointBaseMap B S hS f hT g v hv m h) ≫
        basePointToFibre B S hS f hT g v hv β₂ =
      basePointToFibre B S hS f hT g v hv β₁ := by
  subst h
  refine restrictedFibre_hom_ext ?_
  rw [Category.assoc, restrictYonedaEquiv_yoneda_map_comp, basePointToFibre_fst,
    basePointToFibre_fst, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hiso : (Over.map g).map (basePointBaseMap B S hS f hT g v hv m rfl) ≫
      inv (basePointIso B S hS f hT g v hv β₂) =
        inv (basePointIso B S hS f hT g v hv (yoneda.map m ≫ β₂)) ≫ m := by
    rw [← cancel_epi (basePointIso B S hS f hT g v hv (yoneda.map m ≫ β₂)),
      IsIso.hom_inv_id_assoc, ← Category.assoc, IsIso.comp_inv_eq]
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, relocalizeBaseHom_left, Category.id_comp, Category.comp_id]
    rfl
  rw [← Category.assoc, ← Functor.map_comp, hiso, Functor.map_comp, Category.assoc]
  rfl

/-- The comparison of a scheme point of `X ×_Y V` with its reading over `T` is the identity on
underlying schemes. -/
theorem inv_basePointIso_left :
    (inv (basePointIso B S hS f hT g v hv β)).left = 𝟙 U'.left :=
  inv_relocalizeBaseHom_left B T S hT hS g _

/-- The morphism to `V` of a scheme point of `X ×_Y V` factors through its reading over `T`. -/
theorem basePointToV_eq :
    basePointToV B S hS f hT g v hv β = basePointIso B S hS f hT g v hv β ≫
      (Over.homMk (basePointBase B S hS f hT g v hv β).hom rfl :
        (Over.map g).obj (basePointBase B S hS f hT g v hv β) ⟶ Over.mk g) := by
  rw [← inv_basePointIso_comp, IsIso.hom_inv_id_assoc]

end BasePoint

/-! ### Functions on the scheme charts -/

/-- The scheme chart of `X ×_Y V` attached to a scheme chart of the fibre of `f` over `v`. -/
noncomputable abbrev chartOfFibreChart
    (c : CostructuredArrow yoneda (restrictedFibre B S hS f.hom hT g v)) :
    CostructuredArrow yoneda
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1 :=
  CostructuredArrow.mk (fibrePointLift B S hS f hT g v hv c.hom).hom

/-- A morphism of scheme charts of the fibre gives a morphism of the attached charts of
`X ×_Y V`. -/
noncomputable def chartOfFibreChartMap
    {c c' : CostructuredArrow yoneda (restrictedFibre B S hS f.hom hT g v)} (m : c ⟶ c') :
    chartOfFibreChart B S hS f hT g v hv c ⟶ chartOfFibreChart B S hS f hT g v hv c' :=
  CostructuredArrow.homMk ((Over.map g).map m.left)
    ((fibrePointToBaseChange_naturality B S hS f hT g v hv m.left c'.hom).symm.trans
      (congrArg (fun a => (fibrePointLift B S hS f hT g v hv a).hom) (CostructuredArrow.w m)))

/-- Reading a family of functions on the scheme charts of `X ×_Y V` on the scheme charts of the
fibre of `f` over `v`, formed over `T`. -/
noncomputable def chartFunctionsToFibre :
    chartFunctions B S hS
        (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1 →+*
      chartFunctions B T hT (restrictedFibre B S hS f.hom hT g v) where
  toFun s := ⟨fun j => s.val (op (chartOfFibreChart B S hS f hT g v hv j.unop)), fun {_ _} m =>
    s.property (chartOfFibreChartMap B S hS f hT g v hv m.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The scheme chart of the fibre of `f` over `v` attached to a scheme chart of `X ×_Y V`. -/
noncomputable abbrev fibreChartOfChart
    (d : CostructuredArrow yoneda
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1) :
    CostructuredArrow yoneda (restrictedFibre B S hS f.hom hT g v) :=
  CostructuredArrow.mk (basePointToFibre B S hS f hT g v hv d.hom)

/-- A morphism of scheme charts of `X ×_Y V` gives a morphism of the attached charts of the
fibre. -/
noncomputable def fibreChartOfChartMap
    {d d' : CostructuredArrow yoneda
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1} (m : d ⟶ d') :
    fibreChartOfChart B S hS f hT g v hv d ⟶ fibreChartOfChart B S hS f hT g v hv d' :=
  CostructuredArrow.homMk (basePointBaseMap B S hS f hT g v hv m.left (CostructuredArrow.w m))
    (basePointToFibre_naturality B S hS f hT g v hv m.left (CostructuredArrow.w m))

/-- Reading a family of functions on the scheme charts of the fibre of `f` over `v`, formed over
`T`, on the scheme charts of `X ×_Y V`. -/
noncomputable def chartFunctionsFromFibre :
    chartFunctions B T hT (restrictedFibre B S hS f.hom hT g v) →+*
      chartFunctions B S hS
        (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1 where
  toFun t := ⟨fun j => t.val (op (fibreChartOfChart B S hS f hT g v hv j.unop)), fun {_ _} m =>
    t.property (fibreChartOfChartMap B S hS f hT g v hv m.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The comparison from a scheme chart of `X ×_Y V` to the chart rebuilt from the attached chart
of the fibre; its underlying morphism of schemes is the identity. -/
noncomputable def toChartOfFibreChart
    (d : CostructuredArrow yoneda
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1) :
    d ⟶ chartOfFibreChart B S hS f hT g v hv (fibreChartOfChart B S hS f hT g v hv d) :=
  CostructuredArrow.homMk (basePointIso B S hS f hT g v hv d.hom) (by
    refine sectionChartBaseChange_hom_ext ?_ ?_
    · refine ((Category.assoc _ _ _).trans (congrArg (yoneda.map _ ≫ ·)
        (fibrePointToBaseChange_proj B S hS f hT g v hv _))).trans ?_
      refine ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map
        (basePointToV_eq B S hS f hT g v hv d.hom).symm)).trans ?_
      exact Yoneda.fullyFaithful.map_preimage _
    · refine ((Category.assoc _ _ _).trans (congrArg (yoneda.map _ ≫ ·)
        (fibrePointToBaseChange_toX B S hS f hT g v hv _))).trans ?_
      rw [show (fibreChartOfChart B S hS f hT g v hv d).hom =
          basePointToFibre B S hS f hT g v hv d.hom from rfl,
        basePointToFibre_fst, Equiv.apply_symm_apply, ← Category.assoc, ← Functor.map_comp,
        IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp])

/-- Reading chart functions on the fibre and back gives them back. -/
theorem chartFunctionsFromFibre_chartFunctionsToFibre
    (s : chartFunctions B S hS
      (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1) :
    chartFunctionsFromFibre B S hS f hT g v hv (chartFunctionsToFibre B S hS f hT g v hv s) =
      s := by
  refine Subtype.ext (funext fun d => ?_)
  refine Eq.trans ?_ (s.property (toChartOfFibreChart B S hS f hT g v hv d.unop).op)
  change _ = (Scheme.Γ.map (B.inclusion.map (𝟙 d.unop.left.left)).op).hom _
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The point of `X ×_Y V` attached to a point of the fibre lies over `V` by the structure
morphism of the point. -/
theorem basePointToV_fibrePointLift {U : BigFppfOver B T hT}
    (α : yoneda.obj U ⟶ restrictedFibre B S hS f.hom hT g v) :
    basePointToV B S hS f hT g v hv (fibrePointLift B S hS f hT g v hv α).hom =
      (Over.homMk U.hom rfl : (Over.map g).obj U ⟶ Over.mk g) :=
  Yoneda.fullyFaithful.map_injective ((Yoneda.fullyFaithful.map_preimage _).trans
    (fibrePointToBaseChange_proj B S hS f hT g v hv α))

/-- The object of the big fppf site of `T` underlying a scheme chart of the fibre is the one
rebuilt from the attached chart of `X ×_Y V`. -/
noncomputable def toBasePointBase
    (c : CostructuredArrow yoneda (restrictedFibre B S hS f.hom hT g v)) :
    c.left ⟶ basePointBase B S hS f hT g v hv (fibrePointLift B S hS f hT g v hv c.hom).hom :=
  Over.homMk (𝟙 c.left.left) (by
    rw [Category.id_comp]
    change (basePointToV B S hS f hT g v hv
      (fibrePointLift B S hS f hT g v hv c.hom).hom).left = c.left.hom
    rw [basePointToV_fibrePointLift]
    rfl)

/-- The two comparisons of a chart of the fibre with its rebuilt chart are inverse to each
other. -/
theorem map_toBasePointBase_comp_inv
    (c : CostructuredArrow yoneda (restrictedFibre B S hS f.hom hT g v)) :
    (Over.map g).map (toBasePointBase B S hS f hT g v hv c) ≫
        inv (basePointIso B S hS f hT g v hv (fibrePointLift B S hS f hT g v hv c.hom).hom) =
      𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, inv_basePointIso_left]
  exact Category.comp_id _

/-- The comparison from a scheme chart of the fibre to the chart rebuilt from the attached chart
of `X ×_Y V`; its underlying morphism of schemes is the identity. -/
noncomputable def toFibreChartOfChart
    (c : CostructuredArrow yoneda (restrictedFibre B S hS f.hom hT g v)) :
    c ⟶ fibreChartOfChart B S hS f hT g v hv (chartOfFibreChart B S hS f hT g v hv c) :=
  CostructuredArrow.homMk (toBasePointBase B S hS f hT g v hv c) (by
    refine restrictedFibre_hom_ext ?_
    change OverShriek.restrictYonedaEquiv g _ X.1
      (yoneda.map (toBasePointBase B S hS f hT g v hv c) ≫
        basePointToFibre B S hS f hT g v hv (fibrePointLift B S hS f hT g v hv c.hom).hom ≫
          restrictedFibreFst hT g f.hom v) = _
    rw [restrictYonedaEquiv_yoneda_map_comp, basePointToFibre_fst, Equiv.apply_symm_apply,
      fibrePointToBaseChange_toX, ← Category.assoc, ← Functor.map_comp,
      map_toBasePointBase_comp_inv, CategoryTheory.Functor.map_id, Category.id_comp])

/-- Reading chart functions on `X ×_Y V` and back gives them back. -/
theorem chartFunctionsToFibre_chartFunctionsFromFibre
    (t : chartFunctions B T hT (restrictedFibre B S hS f.hom hT g v)) :
    chartFunctionsToFibre B S hS f hT g v hv (chartFunctionsFromFibre B S hS f hT g v hv t) =
      t := by
  refine Subtype.ext (funext fun c => ?_)
  refine Eq.trans ?_ (t.property (toFibreChartOfChart B S hS f hT g v hv c.unop).op)
  change _ = (Scheme.Γ.map (B.inclusion.map (𝟙 c.unop.left.left)).op).hom (t.val
    (op (fibreChartOfChart B S hS f hT g v hv (chartOfFibreChart B S hS f hT g v hv c.unop))))
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The functions on the scheme charts of `X ×_Y V` are the functions on the scheme charts of
the fibre of `f` over `v`, formed over `T`.** -/
noncomputable def chartFunctionsFibreEquiv :
    chartFunctions B S hS
        (chartBaseChange B S hS f (etaleSectionChart B S hS hT g v hv)).1.left.1 ≃+*
      chartFunctions B T hT (restrictedFibre B S hS f.hom hT g v) :=
  RingEquiv.ofRingHom (chartFunctionsToFibre B S hS f hT g v hv)
    (chartFunctionsFromFibre B S hS f hT g v hv)
    (RingHom.ext (chartFunctionsToFibre_chartFunctionsFromFibre B S hS f hT g v hv))
    (RingHom.ext (chartFunctionsFromFibre_chartFunctionsToFibre B S hS f hT g v hv))

/-! ### The base ring -/

section AffineBase

variable (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
    (g : B.obj hA ⟶ B.obj hS) (v : Y.1.obj (op (Over.mk g)))
    (hv : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (yonedaEquiv.symm v)))

/-- Under the identification of chart functions, the pullback of a constant `a` of `A` along
`X ×_Y V ⟶ V = Spec A` is the constant `a` on the fibre. -/
theorem chartFunctionsToFibre_chartPullbackFunctions (a : A) :
    chartFunctionsToFibre B S hS f hA g v hv (chartPullbackFunctions B S hS _ _
      ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hA g v hv))).hom
      ((Scheme.ΓSpecIso (.of A)).inv.hom a)) =
    chartFunctionsOfBase B A hA (restrictedFibre B S hS f.hom hA g v) a := by
  refine Subtype.ext (funext fun c => ?_)
  have hp : yoneda.preimage ((fibrePointLift B S hS f hA g v hv c.unop.hom).hom ≫
      ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hA g v hv))).hom) =
      (Over.homMk c.unop.left.hom rfl : (Over.map g).obj c.unop.left ⟶ Over.mk g) :=
    yoneda.map_injective ((yoneda.map_preimage _).trans
      (fibrePointToBaseChange_proj B S hS f hA g v hv c.unop.hom))
  exact (congrArg (fun k : (Over.map g).obj c.unop.left ⟶ Over.mk g =>
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom
      ((Scheme.ΓSpecIso (.of A)).inv.hom a)) hp).trans rfl

/-- **The structure map on an affine étale chart `Spec A ⟶ Y`, through the fibre over the
chart.** Let `v` be an étale chart of `Y` with source `Spec A`. Then `f♯ : 𝒪_Y ⟶ f_*𝒪_X` is
bijective on it exactly when the global functions of the fibre of `f` over `v`, formed over
`Spec A`, are `A`. -/
theorem bijective_structureSharp_app_iff_bijective_algebraMap :
    Function.Bijective ((structureSharp B S hS f).hom.app
        (op (etaleSectionChart B S hS hA g v hv))).hom ↔
      Function.Bijective (algebraMap A (globalFunctions B (Spec (.of A)) hA
        (restrictedFibre B S hS f.hom hA g v))) := by
  rw [bijective_structureSharp_app_iff]
  have hP := isAlgebraicSpace_restrictedFibre B S hS f.hom X.2 Y.2 hA g v
  let eW := (globalFunctionsChartEquiv B S hS
    (chartBaseChange B S hS f (etaleSectionChart B S hS hA g v hv)).1.left).val
  let eF := (globalFunctionsChartEquiv B (Spec (.of A)) hA ⟨_, hP⟩).val
  let E := (eW.trans (chartFunctionsFibreEquiv B S hS f hA g v hv)).trans eF.symm
  have key (a : A) : eF (algebraMap A _ a) = chartFunctionsToFibre B S hS f hA g v hv
      ((globalFunctionsChartEquiv B S hS
        (chartBaseChange B S hS f (etaleSectionChart B S hS hA g v hv)).1.left).val
        (pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f
          (etaleSectionChart B S hS hA g v hv)).1.left (Over.mk g)
          ((spacesBaseChange B S hS f).projection.app
            ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hA g v hv)))
          ((Scheme.ΓSpecIso (.of A)).inv.hom a))) := by
    refine (globalFunctionsChartEquiv_algebraMap B A hA ⟨_, hP⟩ a).trans
      ((chartFunctionsToFibre_chartPullbackFunctions B S hS f A hA g v hv a).symm.trans ?_)
    exact congrArg (chartFunctionsToFibre B S hS f hA g v hv)
      (globalFunctionsChartEquiv_pullbackToGlobalFunctions B S hS _ (Over.mk g)
        ((spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hA g v hv))) _).symm
  have hfun : ⇑(algebraMap A (globalFunctions B (Spec (.of A)) hA
      (restrictedFibre B S hS f.hom hA g v))) =
      E ∘ (pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f
        (etaleSectionChart B S hS hA g v hv)).1.left (Over.mk g)
        ((spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj (etaleSectionChart B S hS hA g v hv)))) ∘
        ⇑(Scheme.ΓSpecIso (.of A)).inv.hom := by
    funext a
    exact eF.injective ((key a).trans (eF.apply_symm_apply _).symm)
  rw [hfun]
  have hΓ : Function.Bijective ⇑(Scheme.ΓSpecIso (.of A)).inv.hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  rw [Function.Bijective.of_comp_iff' E.bijective, Function.Bijective.of_comp_iff _ hΓ]
  rfl

/-- **`f♯ : 𝒪_Y ⟶ f_*𝒪_X` is an isomorphism as soon as, for every étale chart `v` of `Y` with
source `Spec A`, the global functions of the fibre of `f` over `v`, formed over `Spec A`, are
`A`.** Every affine étale chart of `Y` is isomorphic to one whose source is literally `Spec A`,
and the affine charts are a dense subsite of the small étale site. -/
theorem isIso_structureSharp_of_bijective_algebraMap
    (h : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A))) (g : B.obj hA ⟶ B.obj hS)
      (v : Y.1.obj (op (Over.mk g)))
      (_ : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (yonedaEquiv.symm v))),
      Function.Bijective (algebraMap A (globalFunctions B (Spec (.of A)) hA
        (restrictedFibre B S hS f.hom hA g v)))) :
    IsIso (structureSharp B S hS f) := by
  refine isIso_structureSharp_of_isAffine B S hS f fun V hV => ?_
  rw [← bijective_structureSharp_app_iff]
  let T := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)
  let A : Type u := Γ(T, ⊤)
  have hA : B.Contains (Spec (.of A)) := by
    have hT : T.size < B.cutoff := V.obj.left.left.property
    rwa [Scheme.size_congr T.isoSpec] at hT
  let iI : B.obj hA ≅ V.obj.left.left := B.inclusion.preimageIso T.isoSpec.symm
  let g := iI.hom ≫ V.obj.left.hom
  let kI : (Over.mk g : BigFppfOver B S hS) ≅ V.obj.left := Over.isoMk iI rfl
  let v : Y.1.obj (op (Over.mk g)) := Y.1.map kI.hom.op (yonedaEquiv V.obj.hom)
  have hvv : yonedaEquiv.symm v = yoneda.map kI.hom ≫ V.obj.hom :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_naturality _ _)
  have hv : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (yonedaEquiv.symm v)) := by
    change (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yonedaEquiv.symm v)
    rw [hvv]
    exact MorphismProperty.RespectsIso.precomp _ (yoneda.map kI.hom) _ V.property
  let e : etaleSectionChart B S hS hA g v hv ≅ V :=
    (IsEtaleChart B S hS Y.1).fullyFaithfulι.preimageIso
      (CostructuredArrow.isoMk kI hvv.symm)
  exact (ConcreteCategory.isIso_iff_bijective _).1
    ((NatTrans.isIso_app_iff_of_iso (structureSharp B S hS f).hom e.op).2
      ((ConcreteCategory.isIso_iff_bijective _).2
        ((bijective_structureSharp_app_iff_bijective_algebraMap B S hS f A hA g v hv).2
          (h A hA g v hv))))

end AffineBase

end AlgebraicGeometry.Space

end
