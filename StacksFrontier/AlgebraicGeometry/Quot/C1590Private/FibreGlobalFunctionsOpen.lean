module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableGenusLociOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlobalFunctions

/-!
# The locus where the fibres of a family of curves have `H⁰ = κ` is open

Let `f : X ⟶ S` be a family of curves. The points `s ∈ S` with `κ(s) = H⁰(X_s, 𝒪_{X_s})` form an
open subset of `S`, and its formation commutes with arbitrary base change: this is Stacks 0E0R at
`i = 0` for `𝓕 = 𝒪_X`, in the form of condition (o) of Stacks 0E0E for the fibrewise condition
`AlgebraicGeometry.CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres`, given that the family
is étale locally on the base a scheme (Stacks 0E6F).

## Main results

* `AlgebraicGeometry.C1590Private.bijective_appTop_iff_of_isPullback_field`: `K = H⁰` is unchanged
  by extension of the ground field.
* `AlgebraicGeometry.C1590Private.bijective_globalFunctionsMap_fiberProduct_iff_of_presentation`:
  the fibrewise condition at a field-valued point, read on a presentation of the fibre.
* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of`:
  condition (o) of Stacks 0E0E for this condition, given Stacks 0E6F.

## References

* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Space.pointTopology

/-! ### Extension of the ground field -/

/-- **`K = H⁰` is unchanged by extension of the ground field.** For a proper morphism
`f : Y ⟶ Spec K` of finite presentation and a cartesian square along `Spec K' ⟶ Spec K`, the
base change `g` is bijective on global functions exactly when `f` is. -/
theorem bijective_appTop_iff_of_isPullback_field {K K' : Type u} [Field K] [Field K']
    {Y Y' : Scheme.{u}} (f : Y ⟶ Spec (.of K)) [IsProper f] (hf : FinitePresentation f)
    (p : Spec (.of K') ⟶ Spec (.of K)) (q : Y' ⟶ Y) (g : Y' ⟶ Spec (.of K'))
    (hsq : IsPullback q g f p) :
    Function.Bijective g.appTop ↔ Function.Bijective f.appTop := by
  rw [bijective_appTop_iff_derivedFiberBetti_zero_eq_one f hf K' p q g hsq
      (IsLocalRing.closedPoint K'),
    bijective_appTop_iff_derivedFiberBetti_zero_eq_one f hf K (𝟙 _) (𝟙 _) f
      (IsPullback.of_horiz_isIso ⟨by simp⟩) (IsLocalRing.closedPoint K)]
  constructor <;> intro h <;> convert h using 2 <;> exact Subsingleton.elim _ _

/-! ### Global functions of represented algebraic spaces -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullback of global regular functions is bijective along `e.hom ≫ π` exactly when it is along
`π`, for an isomorphism `e` of algebraic spaces. -/
theorem bijective_globalFunctionsMap_iso_comp_iff {X Y Z : AlgebraicSpaces B S hS} (e : X ≅ Y)
    (π : Y ⟶ Z) :
    Function.Bijective (Space.globalFunctionsMap B S hS (e.hom ≫ π)) ↔
      Function.Bijective (Space.globalFunctionsMap B S hS π) := by
  rw [Space.globalFunctionsMap_comp, RingHom.coe_comp]
  exact Function.Bijective.of_comp_iff' (Space.globalFunctionsMapEquiv B S hS e).bijective _

/-! ### The fibrewise condition on a presentation -/

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibrewise condition `κ = H⁰` read on a presentation of the fibre.** At a field-valued
point `P` of the base of a family of curves, pullback of global functions along the fibre
`X ×_S Spec κ(P) ⟶ Spec κ(P)` is bijective exactly when `Γ(V, 𝒪_V)` is the field, for any scheme
`V` presenting the fibre. -/
theorem bijective_globalFunctionsMap_fiberProduct_iff_of_presentation (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (r : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback r (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value)) :
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ
      (ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap P.value).hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap P.value) ⟶
          schemeSpace P.siteObject)) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map v).appTop := by
  rw [← Space.bijective_globalFunctionsMap_schemeSpaceMap_iff]
  rw [yonedaEquiv_symm_value P] at hV
  let e₀ : yoneda.obj V ≅ pullback X.toBase.hom (schemeSpaceMap P.value).hom := hV.isoPullback
  let e : schemeSpace V ≅
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap P.value) :=
    ObjectProperty.isoMk _ e₀
  have he : e.hom ≫ (ObjectProperty.homMk (pullback.snd X.toBase.hom
      (schemeSpaceMap P.value).hom) : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase
        (schemeSpaceMap P.value) ⟶ schemeSpace P.siteObject) = schemeSpaceMap v :=
    ObjectProperty.hom_ext _ hV.isoPullback_hom_snd
  rw [← he, bijective_globalFunctionsMap_iso_comp_iff]

/-- A scheme presenting the fibre of a family of curves at a field-valued point is of finite
presentation over the field of the point. -/
theorem finitePresentation_toScheme_map_of_presentation (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (r : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback r (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value)) :
    FinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map v) := by
  rw [yonedaEquiv_symm_value P] at hV
  exact finitePresentation_toScheme_map_of_isPullback X
    (isPullback_homMk_of_isPullback (show P.siteObject ⟶ X.base from P.value) v r hV)

/-- **`κ = H⁰` on the fibre is unchanged by extension of the field of the point.** Let `r` be a
field-valued point of the base of a family of curves which is the restriction of `p` along a
morphism `f` of field spectra. A scheme presenting the fibre at `r` has the field of `r` as its
ring of global functions exactly when a scheme presenting the fibre at `p` has the field of `p`. -/
theorem bijective_appTop_iff_of_dominates (X : CurveFamily B hZ)
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ r.siteObject) (q' : yoneda.obj W ⟶ X.total.obj)
    (hW : IsPullback q' (yoneda.map w) X.toBase.hom (yonedaEquiv.symm r.value)) :
    Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map w).appTop ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map v).appTop := by
  set F := BigFppfOver.toScheme B integerBase hZ
  have hr : yonedaEquiv.symm r.value = yoneda.map f ≫ yonedaEquiv.symm p.value := by
    rw [← hf, yonedaEquiv_symm_map]
    rfl
  let l : yoneda.obj W ⟶ yoneda.obj V :=
    hV.lift q' (yoneda.map (w ≫ f)) (by rw [hW.w, hr, Functor.map_comp, Category.assoc])
  have hl₁ : l ≫ q = q' := hV.lift_fst _ _ _
  have hl₂ : l ≫ yoneda.map v = yoneda.map (w ≫ f) := hV.lift_snd _ _ _
  have hsq : IsPullback l (yoneda.map w) (yoneda.map v) (yoneda.map f) := by
    refine IsPullback.of_right (h₁₂ := q) (h₂₂ := yonedaEquiv.symm p.value)
      (v₁₃ := X.toBase.hom) ?_ (by rw [hl₂, Functor.map_comp]) hV
    rwa [hl₁, ← hr]
  let l₀ : W ⟶ V := Yoneda.fullyFaithful.preimage l
  have hsq₀ : IsPullback l₀ w v f :=
    IsPullback.of_map_of_faithful yoneda (by rwa [Yoneda.fullyFaithful.map_preimage])
  have : PreservesLimitsOfShape WalkingCospan F :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  have := X.isProper_toScheme_map_of_isPullback _ v q hV
  exact bijective_appTop_iff_of_isPullback_field (F.map v)
    (finitePresentation_toScheme_map_of_presentation X p v q hV) (F.map f) (F.map l₀) (F.map w)
    (hsq₀.map F)

/-- The fibre of a family of curves at a field-valued point *has `H⁰` the field*: it is presented
by a scheme over the field of the point whose ring of global functions is that field. -/
abbrev HasGlobalFunctionsFieldAt (X : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) : Prop :=
  X.HasFibreSatisfying B hZ (fun _ _ _ f => Function.Bijective f.appTop) p

/-- The set of points of the base of a family of curves whose fibre has `H⁰` the residue field. -/
def globalFunctionsFieldLocus (X : CurveFamily B hZ) :
    Set ((BigFppfOver.toScheme B integerBase hZ).obj X.base) :=
  {x | HasGlobalFunctionsFieldAt X (X.residueFieldPoint x)}

/-- **`κ = H⁰` on a fibre depends only on the underlying point of the base.** For every
field-valued point `P` of the base and every scheme `V` presenting the fibre at `P`, the ring of
global functions of `V` is the field of `P` exactly when the image of `P` lies in the locus. -/
theorem bijective_appTop_iff_mem_globalFunctionsFieldLocus (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (r : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback r (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value)) :
    Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map v).appTop ↔
      Space.schemePoint B integerBase hZ X.base P ∈ globalFunctionsFieldLocus X := by
  set x := Space.schemePoint B integerBase hZ X.base P
  set R := X.residueFieldPoint x
  have hx : Space.schemePoint B integerBase hZ X.base R =
      Space.schemePoint B integerBase hZ X.base P :=
    CurveFamily.schemePoint_residueFieldPoint X x
  obtain ⟨s, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ :=
    Space.hasCommonExtension_of_schemePoint_eq B integerBase hZ X.base hx
  obtain ⟨W, w, q', hW⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ X s
  obtain ⟨V₁, v₁, r₁, hV₁⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ X R
  have h₁ := bijective_appTop_iff_of_dominates X f₁ hf₁ v₁ r₁ hV₁ w q' hW
  have h₂ := bijective_appTop_iff_of_dominates X f₂ hf₂ v r hV w q' hW
  constructor
  · exact fun hb ↦ ⟨V₁, v₁, r₁, hV₁, h₁.1 (h₂.2 hb)⟩
  · rintro ⟨V₂, v₂, r₂, hV₂, hb⟩
    have h₃ := bijective_appTop_iff_of_dominates X f₁ hf₁ v₂ r₂ hV₂ w q' hW
    exact h₂.1 (h₃.2 hb)

/-- The fibrewise condition `κ = H⁰` at a field-valued point holds exactly when the image of the
point lies in the locus. -/
theorem bijective_globalFunctionsMap_fiberProduct_iff_mem (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ
      (ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap P.value).hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap P.value) ⟶
          schemeSpace P.siteObject)) ↔
      Space.schemePoint B integerBase hZ X.base P ∈ globalFunctionsFieldLocus X := by
  obtain ⟨V, v, r, hV⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ X P
  rw [bijective_globalFunctionsMap_fiberProduct_iff_of_presentation X P v r hV]
  exact bijective_appTop_iff_mem_globalFunctionsFieldLocus X P v r hV

/-- The fibre at a field-valued point has `H⁰` the field exactly when the image of the point lies
in the locus. -/
theorem hasGlobalFunctionsFieldAt_iff_mem (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    HasGlobalFunctionsFieldAt X P ↔
      Space.schemePoint B integerBase hZ X.base P ∈ globalFunctionsFieldLocus X := by
  constructor
  · rintro ⟨V, v, r, hV, hb⟩
    exact (bijective_appTop_iff_mem_globalFunctionsFieldLocus X P v r hV).1 hb
  · intro h
    obtain ⟨V, v, r, hV⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ X P
    exact ⟨V, v, r, hV, (bijective_appTop_iff_mem_globalFunctionsFieldLocus X P v r hV).2 h⟩

/-- **The locus commutes with base change.** For a morphism of families of curves `φ : F ⟶ G`,
the locus of `F` is the inverse image of the locus of `G`. -/
theorem globalFunctionsFieldLocus_eq_preimage {F G : CurveFamily B hZ} (φ : F ⟶ G) :
    globalFunctionsFieldLocus F =
      (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap ⁻¹' globalFunctionsFieldLocus G := by
  ext x
  show HasGlobalFunctionsFieldAt F (F.residueFieldPoint x) ↔ _
  rw [HasGlobalFunctionsFieldAt, ← CurveFamily.hasFibreSatisfying_map_iff φ,
    ← HasGlobalFunctionsFieldAt, hasGlobalFunctionsFieldAt_iff_mem]
  have hpt := (Space.schemePoint_map_yoneda B integerBase hZ φ.baseMap _).trans
    (congrArg _ (CurveFamily.schemePoint_residueFieldPoint F x))
  exact Iff.of_eq (congrArg (· ∈ globalFunctionsFieldLocus G) hpt)

/-- A family of curves has `κ = H⁰` on all its fibres over fields exactly when its locus is the
whole base. -/
theorem hasBijectiveGlobalFunctionsOnFieldFibres_iff_eq_univ (X : CurveFamily B hZ) :
    CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X ↔
      globalFunctionsFieldLocus X = Set.univ := by
  refine ⟨fun h => Set.eq_univ_of_forall fun x => ?_, fun h P => ?_⟩
  · have := (bijective_globalFunctionsMap_fiberProduct_iff_mem X (X.residueFieldPoint x)).1
      (h _)
    rwa [CurveFamily.schemePoint_residueFieldPoint] at this
  · rw [bijective_globalFunctionsMap_fiberProduct_iff_mem, h]
    trivial

section Chart

open ProperFlatFibreEulerCharacteristic

attribute [local instance] HasDerivedCategory.standard

variable (X : CurveFamily B hZ) {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ X.base}
  {p : schemeSpace Z ⟶ X.total} {q : Z ⟶ U}
  (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))

include sq

/-- Over a scheme chart `q : Z ⟶ U`, a fibre `g` of `q` over a field-valued point `P₀` of `U` lying
over `u` has `K = H⁰` exactly when the zeroth derived-fibre Betti number of `Rq_*𝒪_Z` at `u` is
one. -/
private theorem bijective_appTop_iff_derivedFiberBetti_eq_one_of_isPullback
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U) {K : Type u} [Field K]
    {P₀ : Spec (.of K) ⟶ (BigFppfOver.toScheme B integerBase hZ).obj U} {Y : Scheme.{u}}
    {r₀ : Y ⟶ (BigFppfOver.toScheme B integerBase hZ).obj Z} {g : Y ⟶ Spec (.of K)}
    (hsq : IsPullback r₀ g ((BigFppfOver.toScheme B integerBase hZ).map q) P₀)
    (pt : Spec (.of K)) (hpt : P₀.base pt = u) :
    haveI := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
    haveI := CurveFamily.flat_toScheme_map_of_isPullback X sq
    Function.Bijective g.appTop ↔
      DerivedFibreBetti.derivedFiberBetti _
        (derivedPushforwardModule ((BigFppfOver.toScheme B integerBase hZ).map q)
          (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj Z).ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit _
          (finitePresentation_toScheme_map_of_isPullback X sq)) 0 u = 1 := by
  have := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
  have := CurveFamily.flat_toScheme_map_of_isPullback X sq
  subst hpt
  exact bijective_appTop_iff_derivedFiberBetti_zero_eq_one
    ((BigFppfOver.toScheme B integerBase hZ).map q)
    (finitePresentation_toScheme_map_of_isPullback X sq) _ _ _ _ hsq pt

/-- **The locus over a scheme chart is read on the zeroth derived-fibre Betti number.** Over a
chart on which the family is a morphism of schemes `q : Z ⟶ U`, a point of `U` lies in the locus
of the base change exactly when the zeroth derived-fibre Betti number of `Rq_*𝒪_Z` there is one. -/
theorem mem_globalFunctionsFieldLocus_curveFamilyOfIsPullback_iff
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U) :
    haveI := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
    haveI := CurveFamily.flat_toScheme_map_of_isPullback X sq
    u ∈ globalFunctionsFieldLocus (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq) ↔
      DerivedFibreBetti.derivedFiberBetti _
        (derivedPushforwardModule ((BigFppfOver.toScheme B integerBase hZ).map q)
          (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj Z).ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit _
          (finitePresentation_toScheme_map_of_isPullback X sq)) 0 u = 1 := by
  set XU := curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq
  set P := XU.residueFieldPoint u
  obtain ⟨V, v, r, hV⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ XU P
  obtain ⟨r₀, hsq⟩ := exists_isPullback_toScheme_of_presentation q P v r hV
  have h2 := bijective_appTop_iff_mem_globalFunctionsFieldLocus XU P v r hV
  rw [CurveFamily.schemePoint_residueFieldPoint XU u] at h2
  exact h2.symm.trans (bijective_appTop_iff_derivedFiberBetti_eq_one_of_isPullback X sq u hsq _
    (CurveFamily.schemePoint_residueFieldPoint XU u))

/-- **The locus over a scheme chart is the locus of the scheme fibres.** Over a chart on which the
family is a morphism of schemes `q : Z ⟶ U`, a point `u` of `U` lies in the locus of the base
change exactly when `κ(u) = H⁰(Z_u, 𝒪_{Z_u})` for the scheme-theoretic fibre `Z_u`. -/
theorem mem_globalFunctionsFieldLocus_curveFamilyOfIsPullback_iff_bijective
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U) :
    u ∈ globalFunctionsFieldLocus (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq) ↔
      Function.Bijective
        (((BigFppfOver.toScheme B integerBase hZ).map q).fiberToSpecResidueField u).appTop := by
  rw [mem_globalFunctionsFieldLocus_curveFamilyOfIsPullback_iff X sq u]
  exact (bijective_appTop_iff_derivedFiberBetti_eq_one_of_isPullback X sq u
    (isPullback_fiberι_fiberToSpecResidueField ((BigFppfOver.toScheme B integerBase hZ).map q) u)
    (IsLocalRing.closedPoint (((BigFppfOver.toScheme B integerBase hZ).obj U).residueField u))
    (Scheme.fromSpecResidueField_apply _ _)).symm

/-- **The locus is open over a scheme chart.** Over a chart on which the family is a morphism of
schemes `q : Z ⟶ U`, the locus of the base change is the set where the zeroth derived-fibre Betti
number of `Rq_*𝒪_Z` is one, which is open (the scheme case of Stacks 0E0R at `i = 0`). -/
theorem isOpen_globalFunctionsFieldLocus_curveFamilyOfIsPullback :
    IsOpen (globalFunctionsFieldLocus (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq)) := by
  have := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
  have := CurveFamily.flat_toScheme_map_of_isPullback X sq
  have := CurveFamily.locallyOfFinitePresentation_toScheme_map_of_isPullback X sq
  have hfp := finitePresentation_toScheme_map_of_isPullback X sq
  have key : globalFunctionsFieldLocus (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq) =
      {s | DerivedFibreBetti.derivedFiberBetti _
        (derivedPushforwardModule ((BigFppfOver.toScheme B integerBase hZ).map q)
          (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj Z).ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit _ hfp) 0 s = 1} :=
    Set.ext fun u => mem_globalFunctionsFieldLocus_curveFamilyOfIsPullback_iff X sq u
  rw [key]
  exact isOpen_setOf_derivedFiberBetti_zero_eq_one _ hfp

end Chart

/-- **The locus where the fibres have `H⁰` the residue field is open**, given the étale local
scheme charts of Stacks 0E6F. -/
theorem isOpen_globalFunctionsFieldLocus (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (X : CurveFamily B hZ) : IsOpen (globalFunctionsFieldLocus X) := by
  set T := BigFppfOver.toScheme B integerBase hZ
  rw [isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨U, Z, φ, q, p, hφ, ⟨u, hu⟩, sq⟩ := h0E6F X s
  have : Etale (T.map φ) := hφ
  have hpre : globalFunctionsFieldLocus (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq) =
      T.map φ ⁻¹' globalFunctionsFieldLocus X :=
    globalFunctionsFieldLocus_eq_preimage (curveFamilyOfIsPullbackHom X φ p (schemeSpaceMap q) sq)
  refine ⟨T.map φ '' globalFunctionsFieldLocus
    (curveFamilyOfIsPullback X φ p (schemeSpaceMap q) sq), ?_, ?_, ?_⟩
  · rw [hpre]
    exact Set.image_preimage_subset _ _
  · exact (T.map φ).isOpenMap _ (isOpen_globalFunctionsFieldLocus_curveFamilyOfIsPullback X sq)
  · refine ⟨u, ?_, hu⟩
    rwa [hpre, Set.mem_preimage, hu]

/-- **Condition (o) of Stacks 0E0E for `κ = H⁰` on the fibres** (Stacks 0E0R at `i = 0`), given
the étale local scheme charts of Stacks 0E6F. -/
theorem isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
    (h0E6F : HasEtaleLocalSchemeCharts B hZ) :
    IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ) := by
  refine IsOpenCurvesLocus.of_points fun G => ⟨Space.schemePointsHomeomorph B integerBase hZ
      G.base ⁻¹' globalFunctionsFieldLocus G, (isOpen_globalFunctionsFieldLocus h0E6F G).preimage
      (Space.schemePointsHomeomorph B integerBase hZ G.base).continuous, fun F a => ?_⟩
  refine Iff.trans ?_ (range_pointsMap_subset_preimage_iff a.baseMap _).symm
  rw [hasBijectiveGlobalFunctionsOnFieldFibres_iff_eq_univ, globalFunctionsFieldLocus_eq_preimage a,
    Set.range_subset_iff, Set.eq_univ_iff_forall]
  rfl

end AlgebraicGeometry.C1590Private

end
