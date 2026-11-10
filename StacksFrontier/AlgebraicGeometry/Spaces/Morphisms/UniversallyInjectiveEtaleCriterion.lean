module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedSetFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SinglePointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjectiveSchemeTests
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedFiniteSeparable

/-!
# An étale criterion for universal injectivity

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type. If for every étale morphism `V ⟶ Y` the map of point sets `|X ×_Y V| → |V|` is
injective, then `f` is universally injective. Injectivity on points alone is not enough: the
morphism `Spec ℂ ⟶ Spec ℝ` is injective on points but not universally injective, and the étale
base change along `Spec ℂ ⟶ Spec ℝ` detects this.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_of_injective_pointsMap_pullback_of_isEtale_yoneda`:
  the étale criterion, tested on étale morphisms from schemes; and
  `AlgebraicGeometry.Space.universallyInjective_of_injective_pointsMap_pullback_of_isEtale`, the
  same with étale morphisms from algebraic spaces.
* `AlgebraicGeometry.Space.universallyInjective_of_injective_pointsMap_pullback_yoneda`: the
  same criterion for a target which is a scheme of the site, with étale test schemes only.
* `AlgebraicGeometry.Space.isDecentSpace_of_isLocallyQuasiFinite_to_subsingleton`: an algebraic
  space locally quasi-finite over a scheme of the site with at most one point is decent.
* `AlgebraicGeometry.universallyInjective_of_locallyQuasiFinite_of_geometricallyConnected`: a
  morphism of schemes which is locally quasi-finite and geometrically connected is universally
  injective.

## References

* [Stacks Project, Tag 0AGE](https://stacks.math.columbia.edu/tag/0AGE)
* [Stacks Project, Tag 03MX](https://stacks.math.columbia.edu/tag/03MX)
* [Stacks Project, Tag 0ACB](https://stacks.math.columbia.edu/tag/0ACB)
* [Stacks Project, Tag 06S0](https://stacks.math.columbia.edu/tag/06S0)
* [Stacks Project, Tag 047Z](https://stacks.math.columbia.edu/tag/047Z)
* [Stacks Project, Tag 02LF](https://stacks.math.columbia.edu/tag/02LF)
* [Stacks Project, Tag 0389](https://stacks.math.columbia.edu/tag/0389)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out at the default limit
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_UniversallyInjectiveEtaleCriterion :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_UniversallyInjectiveEtaleCriterion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks in the big fppf site times out at the default limit
/-- Pullbacks in the big fppf site (instance search times out without this shortcut). -/
local instance hasPullbacks_site_UniversallyInjectiveEtaleCriterion :
    HasPullbacks (BigFppfOver B S hS) := inferInstance

local instance (priority := high) hasPullback_site_UniversallyInjectiveEtaleCriterion
    {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An algebraic space over `S` with a locally quasi-finite morphism to an object of the
site whose underlying scheme has at most one point is decent. -/
theorem isDecentSpace_of_isLocallyQuasiFinite_to_subsingleton
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (K : BigFppfOver B S hS) [Subsingleton ((BigFppfOver.toScheme B S hS).obj K)]
    (q : F ⟶ yoneda.obj K) (hq : IsLocallyQuasiFinite B S hS q) :
    IsDecentSpace B S hS F := by
  classical
  let T := BigFppfOver.toScheme B S hS
  rw [isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS F hF]
  intro x U hU φ hφ
  have : IsAffine (T.obj U) := hU
  let h : U ⟶ K := yoneda.preimage (φ ≫ q)
  have hh : yoneda.map h = φ ≫ q := yoneda.map_preimage _
  have hlqf : LocallyQuasiFinite (T.map h) :=
    (hq U K φ (𝟙 _) h hφ (presheaf_yoneda_map_id_etale B S hS K)
      (by rw [Category.comp_id, hh])).2
  have hUfin : Finite (T.obj U) := by
    rcases isEmpty_or_nonempty (T.obj U) with hE | ⟨⟨u⟩⟩
    · infer_instance
    · have : Nonempty (T.obj K) := ⟨T.map h u⟩
      have : IsAffine (T.obj K) := inferInstance
      have hfin := (T.map h).finite_preimage_singleton (T.map h u)
      rw [show (T.map h) ⁻¹' {T.map h u} = Set.univ from
        Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _] at hfin
      exact Set.finite_univ_iff.mp hfin
  have hptsU : Finite (points B S hS (yoneda.obj U)) :=
    Finite.of_equiv _ (schemePointsHomeomorph B S hS U).toEquiv.symm
  refine ⟨Set.toFinite _, ?_⟩
  have hPfin : Finite (T.obj (pullback h h)) := by
    have e := PreservesPullback.iso T h h
    have : LocallyQuasiFinite (pullback.fst (T.map h) (T.map h)) := inferInstance
    rcases isEmpty_or_nonempty (T.obj U) with hE | ⟨⟨u⟩⟩
    · have : IsEmpty (T.obj (pullback h h)) := ⟨fun a => hE.false (T.map (pullback.fst h h) a)⟩
      infer_instance
    · have : Nonempty (T.obj K) := ⟨T.map h u⟩
      have : IsAffine (T.obj K) := inferInstance
      have : QuasiCompact (T.map h) := inferInstance
      have : QuasiCompact (pullback.fst (T.map h) (T.map h)) := inferInstance
      have hfin := (pullback.fst (T.map h) (T.map h)).finite_preimage
        (Set.finite_univ (α := T.obj U))
      rw [Set.preimage_univ] at hfin
      have : Finite (pullback (T.map h) (T.map h) : Scheme) := Set.finite_univ_iff.mp hfin
      exact Finite.of_equiv _ (Scheme.homeoOfIso e).toEquiv.symm
  have hpts : Finite (points B S hS (pullback (yoneda.map h) (yoneda.map h))) :=
    Finite.of_equiv _ ((schemePointsHomeomorph B S hS (pullback h h)).toEquiv.symm.trans
      (pointsEquivOfIso B S hS (PreservesPullback.iso yoneda h h)))
  let m : pullback φ φ ⟶ pullback (yoneda.map h) (yoneda.map h) :=
    pullback.lift (pullback.fst φ φ) (pullback.snd φ φ) (by
      rw [hh, ← Category.assoc, pullback.condition, Category.assoc])
  have h1 : m ≫ pullback.fst _ _ = pullback.fst φ φ := pullback.lift_fst _ _ _
  have h2 : m ≫ pullback.snd _ _ = pullback.snd φ φ := pullback.lift_snd _ _ _
  have : Mono m := ⟨fun a b hab => pullback.hom_ext
    (by simpa only [Category.assoc, h1] using congrArg (· ≫ pullback.fst _ _) hab)
    (by simpa only [Category.assoc, h2] using congrArg (· ≫ pullback.snd _ _) hab)⟩
  have : Finite (points B S hS (pullback φ φ)) :=
    Finite.of_injective _ (pointsMap_injective_of_mono B S hS m)
  exact Set.toFinite _

/-- A morphism of schemes which is locally quasi-finite and geometrically connected is
universally injective. -/
theorem
    _root_.AlgebraicGeometry.universallyInjective_of_locallyQuasiFinite_of_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [GeometricallyConnected f] :
    _root_.AlgebraicGeometry.UniversallyInjective f := by
  have key : ∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [LocallyQuasiFinite f']
      [GeometricallyConnected f'], Function.Injective f' := by
    intro X' Y' f' _ _ x₁ x₂ he
    have hc := (f'.isConnected_preimage_singleton (f' x₁)).isPreconnected
    have hs := (IsPreconnected.isDiscrete_iff_subsingleton hc).mp
      (f'.isDiscrete_preimage_singleton (f' x₁))
    exact hs (by simp) (by simpa using he.symm)
  constructor
  intro X' Y' i₁ i₂ f' h
  have : LocallyQuasiFinite f' :=
    MorphismProperty.of_isPullback h.flip (inferInstance : LocallyQuasiFinite f)
  have : GeometricallyConnected f' :=
    MorphismProperty.of_isPullback h.flip (inferInstance : GeometricallyConnected f)
  exact key f'

section RepresentableTarget

variable {U : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ yoneda.obj U)
  (hf : IsLocallyOfFiniteType B S hS f)
  (hinj : ∀ (V : BigFppfOver B S hS) (v : V ⟶ U),
    Etale ((BigFppfOver.toScheme B S hS).map v) →
      Function.Injective (pointsMap B S hS (pullback f (yoneda.map v))
        (pullback.snd f (yoneda.map v))))

include hinj in
/-- Under the étale hypothesis, the morphism itself is injective on points. -/
private theorem injective_pointsMap_of_etale_tests :
    Function.Injective (pointsMap B S hS X f) := by
  have hid : Etale ((BigFppfOver.toScheme B S hS).map (𝟙 U)) := by
    rw [show (BigFppfOver.toScheme B S hS).map (𝟙 U) = 𝟙 _ from CategoryTheory.Functor.map_id _ _]
    infer_instance
  let e : X ⟶ pullback f (yoneda.map (𝟙 U)) :=
    pullback.lift (𝟙 X) f (by simp)
  have he : e ≫ pullback.fst _ _ = 𝟙 X := pullback.lift_fst _ _ _
  have : Mono e := mono_of_mono_fac he
  intro x y hxy
  refine pointsMap_injective_of_mono B S hS e (hinj U (𝟙 U) hid ?_)
  rwa [← pointsMap_comp_apply, ← pointsMap_comp_apply, pullback.lift_snd]

include hinj in
/-- Under the étale hypothesis, the field fibre over a monomorphic field-valued point of the
target has at most one point. -/
private theorem subsingleton_points_fieldFibre (c : FieldValuedPoint B S hS (yoneda.obj U))
    (hc : Mono (fieldMorphism B S hS (yoneda.obj U) c)) :
    Subsingleton (points B S hS (fieldFibre B S hS f c)) := by
  refine ⟨fun w₁ w₂ => injective_pointsMap_fst_fieldFibre B S hS f c hc ?_⟩
  have h₁ := (range_pointsMap_fst_fieldFibre B S hS f c).subset (Set.mem_range_self w₁)
  have h₂ := (range_pointsMap_fst_fieldFibre B S hS f c).subset (Set.mem_range_self w₂)
  exact injective_pointsMap_of_etale_tests B S hS f hinj (h₁.trans h₂.symm)

include hX hf hinj in
/-- Under the étale hypothesis, the structure morphism of every field fibre is locally
quasi-finite. -/
private theorem isLocallyQuasiFinite_snd_fieldFibre_of_etale_tests
    (c : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsLocallyQuasiFinite B S hS (pullback.snd f (yonedaEquiv.symm c.value)) := by
  have hY := isAlgebraicSpace_yoneda B S hS U
  refine isLocallyQuasiFinite_snd_fieldFibre_of_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY
    hf c (isAlgebraicSpace_pullback B S hS _ _ hX (isAlgebraicSpace_yoneda B S hS _) hY)
    fun x _ => ?_
  have hsub : Subsingleton ↥(pointsMap B S hS X f ⁻¹' {pointsMap B S hS X f x}) :=
    ⟨fun a b => Subtype.ext (injective_pointsMap_of_etale_tests B S hS f hinj
      (a.2.trans b.2.symm))⟩
  exact (isIsolatedPoint_fibre_iff_isQuasiFiniteAt B S hS hX hY f hf
    (isDecentSpace_yoneda B S hS U) (pointsMap B S hS X f x) ⟨x, rfl⟩).mp (by
      change IsOpen _
      rw [show ({⟨x, rfl⟩} : Set ↥(pointsMap B S hS X f ⁻¹' {pointsMap B S hS X f x})) =
        Set.univ from Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _]
      exact isOpen_univ)

include hX hf hinj in
/-- Under the étale hypothesis, when the field fibre over the residue field of a point `x₀` of
`U` is represented by an object `Z` of the site, the structure morphism `Z ⟶ Spec κ(x₀)` is a
universally injective morphism of schemes. -/
private theorem universallyInjective_of_isIso_fieldFibre
    (x₀ : (BigFppfOver.toScheme B S hS).obj U) {Z : BigFppfOver B S hS}
    (e : yoneda.obj Z ≅ fieldFibre B S hS f (canonicalSiteFieldPoint B S hS U x₀))
    (φ : Z ⟶ (canonicalSiteFieldPoint B S hS U x₀).siteObject)
    (hφ : yoneda.map φ = e.hom ≫ pullback.snd _ _)
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj Z)) :
    _root_.AlgebraicGeometry.UniversallyInjective ((BigFppfOver.toScheme B S hS).map φ) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let c := canonicalSiteFieldPoint B S hS U x₀
  let k := (T.obj U).residueField x₀
  have hcval : T.map c.value = (T.obj U).fromSpecResidueField x₀ :=
    map_siteFieldPointOfSchemeMap_value_left B S hS U _ _
  have hEt : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf e.hom := by
    have h0 := presheaf_yoneda_map_id_etale B S hS Z
    rw [CategoryTheory.Functor.map_id] at h0
    have := (MorphismProperty.cancel_right_of_respectsIso _ (𝟙 _) e.hom).2 h0
    simpa using this
  have hlqf : LocallyQuasiFinite (T.map φ) :=
    (isLocallyQuasiFinite_snd_fieldFibre_of_etale_tests B S hS hX f hf hinj c Z c.siteObject
      e.hom (𝟙 _) φ hEt (presheaf_yoneda_map_id_etale B S hS _)
      (by rw [Category.comp_id, hφ])).2
  have hgc : GeometricallyConnected (T.map φ) := by
    refine (geometricallyConnected_iff_forall_finite_separable (k := k) (X := T.obj Z)
      (T.map φ)).2 fun k' _ _ _ _ => ?_
    obtain ⟨N, ⟨eN⟩, hNaff⟩ :=
      exists_etaleNeighborhood_residueField_algEquiv_and_isAffine (T.obj U) x₀ k'
    let := N.residueFieldMap.hom.toAlgebra
    have : CompactSpace N.scheme := inferInstance
    have hV : B.Contains N.scheme :=
      (Scheme.size_le_of_locallyOfFiniteType N.toBase).trans_lt U.left.property
    let V : BigFppfOver B S hS :=
      Over.mk ((⟨N.toBase⟩ : B.obj hV ⟶ U.left) ≫ U.hom)
    let v : V ⟶ U := Over.homMk (⟨N.toBase⟩ : B.obj hV ⟶ U.left) rfl
    have hTv : T.map v = N.toBase := rfl
    have hvet : Etale (T.map v) := by rw [hTv]; infer_instance
    let aI : CommRingCat.of (N.scheme.residueField N.point) ≅ CommRingCat.of k' :=
      eN.toRingEquiv.toCommRingCatIso
    let m : Spec (.of k') ⟶ N.scheme := Spec.map aI.hom ≫ N.scheme.fromSpecResidueField N.point
    have : QuasiCompact m := inferInstance
    have hK' : B.Contains (Spec (.of k')) := (Scheme.size_le_of_mono_quasiCompact m).trans_lt hV
    let r := siteFieldPointOfSchemeMap B S hS c.siteObject hK'
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))
    let R' := r.siteObject
    let ι : R' ⟶ c.siteObject := r.value
    have hι : T.map ι = Spec.map (CommRingCat.ofHom (algebraMap k k')) :=
      map_siteFieldPointOfSchemeMap_value_left B S hS _ _ _
    have hNq : N.scheme.fromSpecResidueField N.point ≫ N.toBase =
        Spec.map N.residueFieldMap ≫ (T.obj U).fromSpecResidueField x₀ := by
      simp only [AlgebraicGeometry.EtaleNeighborhood.residueFieldMap, Spec.map_comp,
        Category.assoc, Scheme.residueFieldCongr_inv,
        Scheme.residueFieldCongr_fromSpecResidueField,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    have ha : N.residueFieldMap ≫ aI.hom = CommRingCat.ofHom (algebraMap k k') := by
      ext z
      exact eN.commutes z
    have hkey : m ≫ N.toBase =
        Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ (T.obj U).fromSpecResidueField x₀ := by
      rw [Category.assoc, hNq, ← Category.assoc, ← Spec.map_comp, ha]
    have e1 : B.inclusion.map R'.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ B.inclusion.map c.siteObject.hom := by
      change B.inclusion.map (siteMapOfSchemeMap B S hS c.siteObject hK' _ ≫ _) = _
      rw [Functor.map_comp, map_siteMapOfSchemeMap]
      rfl
    have e2 : B.inclusion.map c.siteObject.hom =
        (T.obj U).fromSpecResidueField x₀ ≫ B.inclusion.map U.hom := by
      rw [← hcval]
      change _ = B.inclusion.map c.value.left ≫ B.inclusion.map U.hom
      rw [← Functor.map_comp, Over.w]
      rfl
    have e3 : B.inclusion.map V.hom = N.toBase ≫ B.inclusion.map U.hom := by
      change B.inclusion.map (_ ≫ U.hom) = _
      rw [Functor.map_comp]
      rfl
    let m' : T.obj R' ⟶ T.obj V := m
    have hm : m' ≫ B.inclusion.map V.hom = B.inclusion.map R'.hom := by
      rw [e3, e1, e2, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ B.inclusion.map U.hom) hkey
    let κ' : R' ⟶ V := siteHomOfSchemeHom B S hS m' hm
    have hκ' : T.map κ' = m' := siteHomOfSchemeHom_map B S hS m' hm
    have hιj : ι ≫ c.value = κ' ≫ v := by
      apply T.map_injective
      rw [Functor.map_comp, Functor.map_comp, hι, hcval, hκ', hTv]
      exact hkey.symm
    have : Mono (T.map κ') := by rw [hκ']; exact inferInstanceAs (Mono m)
    have : Mono κ' := Functor.mono_of_mono_map T this
    let G := pullback (yoneda.map φ) (yoneda.map ι)
    have hcond : (pullback.fst (yoneda.map φ) (yoneda.map ι) ≫ e.hom ≫
        pullback.fst f (yonedaEquiv.symm c.value)) ≫ f =
        (pullback.snd (yoneda.map φ) (yoneda.map ι) ≫ yoneda.map κ') ≫ yoneda.map v := by
      calc _ = pullback.fst (yoneda.map φ) (yoneda.map ι) ≫ (e.hom ≫
              pullback.snd f (yonedaEquiv.symm c.value)) ≫ yoneda.map c.value := by
            simp only [Category.assoc, pullback.condition]; rfl
        _ = pullback.snd (yoneda.map φ) (yoneda.map ι) ≫ yoneda.map (ι ≫ c.value) := by
            rw [← hφ, ← Category.assoc, pullback.condition, Category.assoc,
              ← Functor.map_comp]
        _ = _ := by rw [hιj, Functor.map_comp, Category.assoc]
    let μ : G ⟶ pullback f (yoneda.map v) := pullback.lift _ _ hcond
    have hμ₁ : μ ≫ pullback.fst _ _ = pullback.fst (yoneda.map φ) (yoneda.map ι) ≫ e.hom ≫
        pullback.fst f (yonedaEquiv.symm c.value) := pullback.lift_fst _ _ _
    have hμ₂ : μ ≫ pullback.snd _ _ =
        pullback.snd (yoneda.map φ) (yoneda.map ι) ≫ yoneda.map κ' := pullback.lift_snd _ _ _
    have : Mono μ := by
      refine ⟨fun a b hab => ?_⟩
      have hs : a ≫ pullback.snd (yoneda.map φ) (yoneda.map ι) =
          b ≫ pullback.snd (yoneda.map φ) (yoneda.map ι) := by
        rw [← cancel_mono (yoneda.map κ')]
        simpa only [Category.assoc, hμ₂] using congrArg (· ≫ pullback.snd _ _) hab
      have hf₁ : (a ≫ pullback.fst (yoneda.map φ) (yoneda.map ι)) ≫ e.hom =
          (b ≫ pullback.fst (yoneda.map φ) (yoneda.map ι)) ≫ e.hom := by
        apply pullback.hom_ext
        · simpa only [Category.assoc, hμ₁] using congrArg (· ≫ pullback.fst _ _) hab
        · simp only [Category.assoc, ← hφ]
          rw [pullback.condition, ← Category.assoc, hs, Category.assoc]
      have hf₂ := (Iso.cancel_iso_hom_right _ _ e).1 hf₁
      exact pullback.hom_ext hf₂ hs
    have : Subsingleton (T.obj R') := subsingleton_toScheme_siteObject B S hS _ r
    have : Subsingleton (points B S hS (yoneda.obj R')) :=
      (schemePointsHomeomorph B S hS R').toEquiv.subsingleton
    have hG : Subsingleton (points B S hS G) := by
      refine ⟨fun g₁ g₂ => pointsMap_injective_of_mono B S hS μ
        (hinj V v hvet ?_)⟩
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hμ₂, pointsMap_comp_apply,
        pointsMap_comp_apply, Subsingleton.elim
          (pointsMap B S hS G (pullback.snd (yoneda.map φ) (yoneda.map ι)) g₁)
          (pointsMap B S hS G (pullback.snd (yoneda.map φ) (yoneda.map ι)) g₂)]
    rw [← hι]
    have hP : Subsingleton (pullback (T.map φ) (T.map ι) : Scheme) := by
      have e₁ := (Scheme.homeoOfIso (PreservesPullback.iso T φ ι)).toEquiv
      have e₂ := (schemePointsHomeomorph B S hS (pullback φ ι)).toEquiv.symm.trans
        (pointsEquivOfIso B S hS (PreservesPullback.iso yoneda φ ι))
      exact (e₁.symm.trans e₂).subsingleton
    have : Surjective (T.map ι) := by
      have := subsingleton_toScheme_siteObject B S hS _ c
      exact ⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩
    have hPne : Nonempty (pullback (T.map φ) (T.map ι) : Scheme) := by
      obtain ⟨z⟩ := hne
      obtain ⟨w, -⟩ := (pullback.fst (T.map φ) (T.map ι)).surjective z
      exact ⟨w⟩
    exact @ConnectedSpace.mk _ _ ⟨(@Set.subsingleton_of_subsingleton _ hP _).isPreconnected⟩ hPne
  exact universallyInjective_of_locallyQuasiFinite_of_geometricallyConnected _

include hX hf hinj in
/-- **The étale criterion for a representable target.** A morphism `f : X ⟶ U` locally of
finite type from an algebraic space to a scheme of the site is universally injective as soon as
every étale base change `X ×_U V ⟶ V` along a scheme `V` is injective on points. -/
theorem universallyInjective_of_injective_pointsMap_pullback_yoneda :
    UniversallyInjective B S hS f := by
  classical
  let T := BigFppfOver.toScheme B S hS
  have hY := isAlgebraicSpace_yoneda B S hS U
  refine universallyInjective_of_fieldPoints B S hS f fun p y hy => ⟨p, 𝟙 _, by simp, ?_⟩
  suffices hpy : p.value = y by simp [hpy]
  let x₀ : T.obj U := T.map (f.app _ p.value) (IsLocalRing.closedPoint p.carrier)
  let c := canonicalSiteFieldPoint B S hS U x₀
  have hcval : T.map c.value = (T.obj U).fromSpecResidueField x₀ :=
    map_siteFieldPointOfSchemeMap_value_left B S hS U _ _
  have hcmono : Mono (yonedaEquiv.symm c.value) := by
    have : Mono (T.map c.value) := hcval ▸ (inferInstance :
      Mono (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x₀))
    have : Mono c.value := Functor.mono_of_mono_map T this
    exact inferInstanceAs (Mono (yoneda.map c.value))
  have hcls : c.class B S hS (yoneda.obj U) =
      (FieldValuedPoint.map B S hS X f p).class B S hS (yoneda.obj U) :=
    injective_pointsToScheme B S hS U (by
      rw [pointsToScheme_class, pointsToScheme_class]
      exact canonicalSiteFieldPoint_point B S hS U x₀)
  obtain ⟨d, hd, -⟩ :=
    FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS (yoneda.obj U) hY c _ hcls
  have hd' : d ≫ c.value = f.app _ p.value := hd
  let F := fieldFibre B S hS f c
  have hF : IsAlgebraicSpace B S hS F :=
    isAlgebraicSpace_pullback B S hS _ _ hX (isAlgebraicSpace_yoneda B S hS _) hY
  have hw : ∀ z : X.obj (Opposite.op p.siteObject), f.app _ z = f.app _ p.value →
      yonedaEquiv.symm z ≫ f = yoneda.map d ≫ yonedaEquiv.symm c.value := by
    intro z hz
    rw [yonedaEquiv_symm_naturality_right, hz, ← hd']
    rfl
  let z₁ : yoneda.obj p.siteObject ⟶ F := pullback.lift _ _ (hw p.value rfl)
  let z₂ : yoneda.obj p.siteObject ⟶ F := pullback.lift _ _ (hw y hy.symm)
  have hne : Nonempty (points B S hS F) :=
    ⟨({ carrier := p.carrier, contained := p.contained, toBase := p.toBase
        value := yonedaEquiv z₁ } : FieldValuedPoint B S hS F).class B S hS F⟩
  have hsub := subsingleton_points_fieldFibre B S hS f hinj c hcmono
  have hdec : IsDecentSpace B S hS F :=
    have := subsingleton_toScheme_siteObject B S hS _ c
    isDecentSpace_of_isLocallyQuasiFinite_to_subsingleton B S hS hF c.siteObject _
      (isLocallyQuasiFinite_snd_fieldFibre_of_etale_tests B S hS hX f hf hinj c)
  have : F.IsRepresentable := isRepresentable_of_subsingleton_points B S hS hF hdec hne hsub
  let Z := F.reprX
  let e : yoneda.obj Z ≅ F := (Functor.representableBy F).toIso
  let φ : Z ⟶ c.siteObject := yoneda.preimage (e.hom ≫ pullback.snd _ _)
  have hφ : yoneda.map φ = e.hom ≫ pullback.snd _ _ := yoneda.map_preimage _
  have hZne : Nonempty (T.obj Z) := by
    obtain ⟨w⟩ := hne
    exact ⟨schemePointsHomeomorph B S hS Z ((pointsEquivOfIso B S hS e).symm w)⟩
  have hui := universallyInjective_of_isIso_fieldFibre B S hS hX f hf hinj x₀ e φ hφ hZne
  have hfield : ∀ (K : Type u) [Field K], Function.Injective
      (fun g : Spec (.of K) ⟶ T.obj Z => g ≫ T.map φ) :=
    ((tfae_universallyInjective (T.map φ)).out 1 2).mp hui
  have hz : ∀ z z' : yoneda.obj p.siteObject ⟶ F, z ≫ pullback.snd _ _ = yoneda.map d →
      z' ≫ pullback.snd _ _ = yoneda.map d → z = z' := fun z z' hz hz' => by
    have ha : ∀ z : yoneda.obj p.siteObject ⟶ F, z ≫ pullback.snd _ _ = yoneda.map d →
        yoneda.preimage (z ≫ e.inv) ≫ φ = d := fun z hz => by
      apply yoneda.map_injective
      rw [Functor.map_comp, hφ, yoneda.map_preimage, Category.assoc, e.inv_hom_id_assoc, hz]
      rfl
    have heq : yoneda.preimage (z ≫ e.inv) = yoneda.preimage (z' ≫ e.inv) := by
      apply T.map_injective
      apply hfield p.carrier
      change T.map _ ≫ T.map φ = T.map _ ≫ T.map φ
      rw [← Functor.map_comp, ← Functor.map_comp, ha z hz, ha z' hz']
    have h2 := congrArg yoneda.map heq
    rw [yoneda.map_preimage, yoneda.map_preimage] at h2
    exact (Iso.cancel_iso_inv_right _ _ e).1 h2
  exact yonedaEquiv.symm.injective ((pullback.lift_fst _ _ (hw p.value rfl)).symm.trans
    ((congrArg (· ≫ pullback.fst _ _) (hz z₁ z₂ (pullback.lift_snd _ _ _)
      (pullback.lift_snd _ _ _))).trans (pullback.lift_fst _ _ (hw y hy.symm))))

end RepresentableTarget

/-! ### The criterion -/

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, and assume that for every étale morphism `V ⟶ Y` from a scheme `V` the
map `|X ×_Y V| → |V|` is injective. Then `f` is universally injective. -/
@[stacks 0AGE]
theorem universallyInjective_of_injective_pointsMap_pullback_of_isEtale_yoneda
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hinj : ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsEtale B S hS g →
      Function.Injective (pointsMap B S hS (pullback g f) (pullback.fst g f))) :
    UniversallyInjective B S hS f := by
  obtain ⟨Z, g, hgs, hge⟩ := hY.exists_atlas
  have htfae := (universallyInjective_tfae B S hS hX hY f).out 4 1
  refine htfae.mp
    ⟨Z, g, (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY Z g).mp hgs, ?_⟩
  have hZ := isAlgebraicSpace_yoneda B S hS Z
  refine universallyInjective_of_injective_pointsMap_pullback_yoneda B S hS
    (isAlgebraicSpace_pullback B S hS f g hX hZ hY) (pullback.snd f g)
    (IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f g).flip hX hY hf)
    fun V v hv => ?_
  have hvE : IsEtale B S hS (yoneda.map v) := (isEtale_iff_presheaf_of_yoneda B S hS _).2
    ((presheaf_yoneda_map_iff B S hS AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
      v).2 hv)
  have hgE : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).2 hge
  have h := hinj V (yoneda.map v ≫ g) (isEtale_comp B S hS hvE hgE)
  have sq := ((IsPullback.of_hasPullback (pullback.snd f g) (yoneda.map v)).paste_horiz
    (IsPullback.of_hasPullback f g)).flip
  exact injective_pointsMap_of_comp_isIso B S hS sq.isoPullback.hom
    (IsPullback.isoPullback_hom_fst sq) h

/-- The criterion of Stacks 0AGE with the hypothesis taken over all étale morphisms `V ⟶ Y`
from algebraic spaces `V`. -/
theorem universallyInjective_of_injective_pointsMap_pullback_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hinj : ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS V →
      ∀ g : V ⟶ Y, IsEtale B S hS g →
        Function.Injective (pointsMap B S hS (pullback g f) (pullback.fst g f))) :
    UniversallyInjective B S hS f :=
  universallyInjective_of_injective_pointsMap_pullback_of_isEtale_yoneda B S hS hX hY f hf
    fun V g hg => hinj (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) g hg

end AlgebraicGeometry.Space

end
