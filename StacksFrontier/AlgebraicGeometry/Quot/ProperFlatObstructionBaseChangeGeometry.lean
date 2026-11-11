module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionBaseChangeIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelPullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickeningAdditions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentExtUniverseComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorScalar

/-!
# The special fibre of a deformation is a thickening of its total space

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over a field, and let
`x = (X ⟶ Spec A)` be a deformation of `x₀` over an object `A` of `𝒞_Λ`, with no condition on
the maximal ideal of `A`. The arrow `x₀ ⟶ x` is a cartesian square over the closed point
`Spec k ⟶ Spec A`, which is a closed immersion bijective on points (`A` is Artinian local). Its
map of total spaces `j : X₀ ⟶ X` is therefore a closed immersion surjective on points, and the
direct image along `j` of the small étale topoi is an equivalence.

This is the geometric input of the comparison of the obstruction groups `T²_{X/A}(I)` and
`T²_{X₀/k}(I)` of [Stacks, Remark 0D1P] for `I` killed by `𝔪_A`: on the `Type u` models
`AlgebraicGeometry.Space.modelTopos` of the two small étale ringed topoi, `j` gives a morphism of
ringed topoi whose direct image of sheaves of modules is exact, so that the total direct image
along it is not derived.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceDeformation.closedPointMap`: `Spec k ⟶ Spec A`, as a morphism
  of the site between the two charts.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreMap`: `j : X₀ ⟶ X`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreModelHom`: the morphism of ringed
  topoi `j_m` between the models of the small étale ringed topoi of `X₀` and `X`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.isPullback_specialFibreMap`: the square
  `X₀ ⟶ X` over `Spec k ⟶ Spec A` is cartesian.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.isClosedImmersion_specialFibreMap`,
  `AlgebraicGeometry.ProperFlatSpaceDeformation.isSurjective_specialFibreMap`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.isEquivalence_pushforward_specialFibreMap`:
  `j_*` is an equivalence of small étale topoi.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibrePushforwardTensorIso`: on the small
  étale sites, `j_*(𝒪_{X₀} ⊗_{Γ(Spec A)} I) ≅ 𝒪_X ⊗_{Γ(Spec A)} I` for `I` killed by `𝔪_A`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.isEquivalence_pushforward_specialFibreModelHom`,
  `preservesFiniteColimits_pushforwardModules_specialFibreModelHom`:
  the same on the models, and exactness of the direct image of modules.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin
open Stacks.Cohomology.SiteModules

attribute [-instance] AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

/-! ### `F / J F` for a module killed by `J` -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))))
  (F : Modules.{u, u} B S hS X hX) (J : Ideal A)

/-- If `J` kills `F`, the inclusion `J F ⟶ F` is zero. -/
theorem idealMultipleι_eq_zero_of_globalSmul_eq_zero
    (hF : ∀ c ∈ J, globalSmul _ (φ c) F = 0) : idealMultipleι φ F J = 0 := by
  have h : idealMultipleHom φ F J = 0 := Sigma.hom_ext _ _ fun c => by
    rw [ι_idealMultipleHom, comp_zero, hF c.1 c.2]
  refine (cancel_epi (Abelian.factorThruImage (idealMultipleHom φ F J))).1 ?_
  rw [comp_zero, Abelian.image.fac, h]

/-- **`F / J F ≅ F` when `J` kills `F`**, the inverse being the projection `F ⟶ F / J F`. -/
def idealQuotientIsoOfGlobalSmulEqZero (hF : ∀ c ∈ J, globalSmul _ (φ c) F = 0) :
    idealQuotient φ F J ≅ F where
  hom := cokernel.desc _ (𝟙 F)
    (by rw [idealMultipleι_eq_zero_of_globalSmul_eq_zero φ F J hF, zero_comp])
  inv := idealQuotientπ φ F J
  hom_inv_id := by
    refine (cancel_epi (idealQuotientπ φ F J)).1 ?_
    rw [← Category.assoc, cokernel.π_desc, Category.id_comp, Category.comp_id]
  inv_hom_id := cokernel.π_desc _ _ _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

/-! ### The closed point of an Artinian local ring -/

section ClosedPoint

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **`Spec k ⟶ Spec A` is surjective** for an object `A` of `𝒞_Λ`: every prime of the Artinian
local ring `A` is its maximal ideal, the kernel of the residue map. -/
theorem surjective_specMap_residueMap (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Surjective (Spec.map (CommRingCat.ofHom (residueMap A))) := by
  rw [surjective_iff]
  change Function.Surjective (PrimeSpectrum.comap (residueMap A))
  intro P
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
  change Ideal.comap (residueMap A) ⊥ = P.asIdeal
  rw [← RingHom.ker_eq_comap_bot,
    IsLocalRing.ker_eq_maximalIdeal _ (residueMap_surjective_of_artinian A)]
  exact (IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime P.asIdeal)).symm

/-- `Spec k ⟶ Spec A` is a closed immersion for an object `A` of `𝒞_Λ`. -/
theorem isClosedImmersion_specMap_residueMap (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom (residueMap A))) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (residueMap A))
    (residueMap_surjective_of_artinian A)

end ClosedPoint

/-! ### The map of a deformation over the closed point -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
    hx₀)

/-- **The closed point `Spec k ⟶ Spec A` of a deformation**, as a morphism of the site between
the charts of `x₀` and of the deformation: the base of the arrow `x₀ ⟶ x`. -/
def closedPointMap :
    algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        (contains_specialFibre x₀ hx₀) ⟶
      algebraOver a.algebra B S hS a.toS a.contains :=
  eqToHom (obj_eq_specialFibre x₀ hx₀).symm ≫
    (cartesianProperFlatProjection B S hS).map a.arrow ≫ eqToHom a.obj_eq

/-- The closed point of a deformation is, as a morphism of schemes, the spectrum of the residue
map. -/
theorem toScheme_map_closedPointMap :
    (BigFppfOver.toScheme B S hS).map (closedPointMap a) =
      Spec.map (CommRingCat.ofHom (residueMap a.algebra)) := by
  rw [← a.arrow_base]
  simp only [closedPointMap, Functor.map_comp, eqToHom_map]
  rfl

/-- The closed point of a deformation is a closed immersion of schemes. -/
theorem isClosedImmersion_toScheme_map_closedPointMap :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (closedPointMap a)) := by
  rw [toScheme_map_closedPointMap]
  exact isClosedImmersion_specMap_residueMap a.algebra

/-- The closed point of a deformation is a surjective morphism of schemes. -/
theorem surjective_toScheme_map_closedPointMap :
    Surjective ((BigFppfOver.toScheme B S hS).map (closedPointMap a)) := by
  rw [toScheme_map_closedPointMap]
  exact surjective_specMap_residueMap a.algebra

/-- **The map `j : X₀ ⟶ X` of total spaces** of the arrow `x₀ ⟶ x` of a deformation. -/
abbrev specialFibreMap : x₀.obj.obj.left ⟶ a.point.obj.obj.left :=
  a.arrow.hom.hom.left

/-- The square of presheaves underlying
`AlgebraicGeometry.ProperFlatSpaceDeformation.isPullback_specialFibreMap`. -/
private theorem isPullback_specialFibreMap_hom :
    IsPullback (specialFibreMap a).hom
      (Space.ProperFlatLift.chartStructureMap x₀ (obj_eq_specialFibre x₀ hx₀)).hom
      (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq).hom
      (schemeSpaceMap (closedPointMap a)).hom := by
  have h := CartesianProperFlatSpaces.isPullback_hom a.arrow
  refine h.of_iso (Iso.refl _) (Iso.refl _)
    (yoneda.mapIso (eqToIso (obj_eq_specialFibre x₀ hx₀)))
    (yoneda.mapIso (eqToIso a.obj_eq)) ?_ ?_ ?_ ?_
  · simp
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · change yoneda.map a.arrow.hom.hom.right ≫ yoneda.map (eqToHom a.obj_eq) =
      yoneda.map (eqToHom (obj_eq_specialFibre x₀ hx₀)) ≫ yoneda.map (closedPointMap a)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp only [closedPointMap, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl

/-- **The arrow of a deformation is a cartesian square over the closed point**: `X₀` is the
fibre product `X ×_{Spec A} Spec k`, the square formed by `j : X₀ ⟶ X`, the structure morphisms
`X₀ ⟶ Spec k`, `X ⟶ Spec A` at the two charts, and `Spec k ⟶ Spec A`. -/
theorem isPullback_specialFibreMap :
    IsPullback (specialFibreMap a)
      (Space.ProperFlatLift.chartStructureMap x₀ (obj_eq_specialFibre x₀ hx₀))
      (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)
      (schemeSpaceMap (closedPointMap a)) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (isPullback_specialFibreMap_hom a).w)
    (isPullback_specialFibreMap_hom a)

/-- **The square of a deformation commutes**: `j ≫ (X ⟶ Spec A) = (X₀ ⟶ Spec k) ≫
(Spec k ⟶ Spec A)`, at the two charts. -/
theorem specialFibreMap_comp_chartStructureMap :
    specialFibreMap a ≫ Space.ProperFlatLift.chartStructureMap a.point a.obj_eq =
      Space.ProperFlatLift.chartStructureMap x₀ (obj_eq_specialFibre x₀ hx₀) ≫
        schemeSpaceMap (closedPointMap a) :=
  (isPullback_specialFibreMap a).w

/-- **`j : X₀ ⟶ X` is a closed immersion**, as a base change of the closed immersion
`Spec k ⟶ Spec A`. -/
theorem isClosedImmersion_specialFibreMap :
    Space.IsClosedImmersion B S hS (specialFibreMap a).hom :=
  Space.isClosedImmersion_of_isPullback_schemeSpaceMap B S hS _ _ _ _
    (isPullback_specialFibreMap a) (isClosedImmersion_toScheme_map_closedPointMap a)

/-- **`j : X₀ ⟶ X` is surjective on points**, as a base change of the surjection
`Spec k ⟶ Spec A`. -/
theorem isSurjective_specialFibreMap :
    Space.IsSurjective B S hS (specialFibreMap a).hom :=
  Space.isSurjective_of_isPullback B S hS (isPullback_specialFibreMap a).flip
    (Space.isSurjective_yoneda_map B S hS _ (surjective_toScheme_map_closedPointMap a))

/-- **The direct image along `j : X₀ ⟶ X` is an equivalence of small étale topoi**: `j` is a
closed immersion surjective on points. -/
theorem isEquivalence_pushforward_specialFibreMap :
    (Space.smallEtaleRingedToposHom B S hS
      (specialFibreMap a)).toToposHom.pushforward.IsEquivalence :=
  Space.isEquivalence_pushforward_smallEtaleRingedToposHom B S hS _
    (isClosedImmersion_specialFibreMap a)
    ((Space.surjective_iff_pointsMap_surjective B S hS x₀.obj.obj.left.2 a.point.obj.obj.left.2 _
      (isClosedImmersion_specialFibreMap a).rep).2 (isSurjective_specialFibreMap a))

/-! ### Modules killed by the maximal ideal, on the total space -/

/-- `Γ(Spec A) ⟶ Γ(Spec k)` is surjective. -/
theorem surjective_appTop_closedPointMap :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map (closedPointMap a)).appTop.hom := by
  rw [toScheme_map_closedPointMap]
  intro y
  obtain ⟨x, hx⟩ := residueMap_surjective_of_artinian a.algebra
    ((Scheme.ΓSpecIso (CommRingCat.of k)).hom y)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of a.algebra)).inv x, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
  have h := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of a.algebra)).inv x))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (residueMap a.algebra)))
  change ((Spec.map (CommRingCat.ofHom (residueMap a.algebra))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of a.algebra)).inv x) = _
  rw [h]
  change (CommRingCat.ofHom (residueMap a.algebra)).hom
    (((Scheme.ΓSpecIso (CommRingCat.of a.algebra)).inv ≫
      (Scheme.ΓSpecIso (CommRingCat.of a.algebra)).hom).hom x) = _
  rw [Iso.inv_hom_id]
  exact hx

/-- **`j_* j^* M ≅ M` for an `𝒪_X`-module `M` killed by `𝔪_A`**: the unit `M ⟶ j_* j^* M`
identifies `M / 𝔪_A M` with `j_* j^* M` (`AlgebraicGeometry.Space.baseChangeQuotientIso`, `j`
being the base change of `Spec k ⟶ Spec A`), and `M / 𝔪_A M = M`. Here `𝔪_A` is the kernel of
`Γ(Spec A) ⟶ Γ(Spec k)`, acting on `M` through `X ⟶ Spec A`. -/
def specialFibrePushforwardPullbackIso (M : Space.Modules.{u, u} B S hS a.point.obj.obj.left.1
      a.point.obj.obj.left.2)
    (hM : ∀ c ∈ Space.siteMapKer B S hS (closedPointMap a),
      globalSmul _ (Space.targetScalars B S hS
        (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq) c) M = 0) :
    (Space.modulePushforward B S hS (specialFibreMap a)).obj
        ((Space.modulePullback B S hS (specialFibreMap a)).obj M) ≅ M :=
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (algebraOver a.algebra B S hS a.toS a.contains)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of a.algebra)))
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        (contains_specialFibre x₀ hx₀))) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  (Space.baseChangeQuotientIso B S hS _ (closedPointMap a) _ _ (isPullback_specialFibreMap a)
      (isClosedImmersion_toScheme_map_closedPointMap a) (surjective_appTop_closedPointMap a)
      M).symm ≪≫
    Space.idealQuotientIsoOfGlobalSmulEqZero _ M _ hM

/-- **`j^*(𝒪_X ⊗_{Γ(Spec A)} I) ≅ 𝒪_{X₀} ⊗_{Γ(Spec A)} I`**, the base ring acting on `X₀` through
`X₀ ⟶ Spec k ⟶ Spec A` (`AlgebraicGeometry.Space.baseRingTensorModulePullbackCompIso` and the
commutative square of the deformation). -/
def specialFibrePullbackTensorIso
    (I : ModuleCat.{u} (Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains))) :
    (Space.modulePullback B S hS (specialFibreMap a)).obj
        ((Space.baseRingTensorModule B S hS a.point.obj.obj.left
          (Space.baseRingHomOfMap
            (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq))).obj I) ≅
      (Space.baseRingTensorModule B S hS x₀.obj.obj.left
        (Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap x₀
          (obj_eq_specialFibre x₀ hx₀) ≫ schemeSpaceMap (closedPointMap a)))).obj I :=
  (Space.baseRingTensorModulePullbackCompIso B S hS (specialFibreMap a)
      (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)).app I ≪≫
    eqToIso (by rw [specialFibreMap_comp_chartStructureMap])

/-- **`𝔪_A` kills `𝒪_X ⊗_{Γ(Spec A)} I` when it kills `I`**: multiplication by `c` in the kernel of
`Γ(Spec A) ⟶ Γ(Spec k)`, through `X ⟶ Spec A`, is `𝒪_X ⊗ (c • 𝟙_I) = 0`. -/
theorem globalSmul_targetScalars_baseRingTensorModule_eq_zero
    (I : ModuleCat.{u} (Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains)))
    (hI : ∀ c : Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains),
      c ∈ Space.siteMapKer B S hS (closedPointMap a) → ∀ i : I, c • i = 0)
    (c : Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains))
    (hc : c ∈ Space.siteMapKer B S hS (closedPointMap a)) :
    globalSmul _ (Space.targetScalars B S hS
        (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq) c)
      ((Space.baseRingTensorModule B S hS a.point.obj.obj.left
        (Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq))).obj
          I) = 0 := by
  let X := a.point.obj.obj.left
  let φ := Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)
  let e := Space.modelModulesEquiv B S hS X
  let N : Space.RestrictedModelModules B S hS X := (Space.modelTensorFunctor φ).obj I
  have h0 : c • 𝟙 I = 0 := by
    ext i
    exact hI c hc i
  have hs : Space.modelRestrictGlobalSections B S hS X
      (Space.targetScalars B S hS (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq) c) =
      (⟨(φ c).1, (φ c).2⟩ : GlobalSectionRing (Space.modelRingSheaf B S hS X)) :=
    Subtype.ext (funext fun _ => rfl)
  have h1 : (baseRingTensorFunctor.{u, u, u, u} φ).map (c • 𝟙 I) = 0 :=
    (congrArg (baseRingTensorFunctor.{u, u, u, u} φ).map h0).trans
      ((Space.modelTensorFunctor φ).map_zero I I)
  have hN : globalSmul _ (Space.modelRestrictGlobalSections B S hS X
      (Space.targetScalars B S hS (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq) c)) N
      = 0 :=
    (congrArg (fun s => globalSmul _ s N) hs).trans
      ((baseRingTensorFunctor_map_smul_id.{u, u, u, u} φ c I).symm.trans h1)
  have hEN : globalSmul _ (Space.modelRestrictGlobalSections B S hS X
      (Space.targetScalars B S hS (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq) c))
      (e.functor.obj (e.inverse.obj N)) = 0 := by
    refine ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·)
      (e.counitIso.hom_inv_id_app N).symm)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ e.counitIso.inv.app N)
      (comp_globalSmul _ _ (e.counitIso.hom.app N)).symm).trans ?_
    refine (congrArg (fun g => (e.counitIso.hom.app N ≫ g) ≫ e.counitIso.inv.app N) hN).trans ?_
    rw [comp_zero, zero_comp]
  exact e.functor.map_injective ((Space.modelModulesEquiv_map_globalSmul B S hS
    (Space.targetScalars B S hS (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq) c)
    (e.inverse.obj N)).trans (hEN.trans (e.functor.map_zero _ _).symm))

/-- **`j_*(𝒪_{X₀} ⊗_{Γ(Spec A)} I) ≅ 𝒪_X ⊗_{Γ(Spec A)} I` for a `Γ(Spec A)`-module `I` killed by
`𝔪_A`**, on the small étale sites, the base ring acting on `X₀` through
`X₀ ⟶ Spec k ⟶ Spec A`: `j_*j^*(𝒪_X ⊗ I) ≅ 𝒪_X ⊗ I` and `j^*(𝒪_X ⊗ I) ≅ 𝒪_{X₀} ⊗ I`. -/
def specialFibrePushforwardTensorIso
    (I : ModuleCat.{u} (Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains)))
    (hI : ∀ c : Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains),
      c ∈ Space.siteMapKer B S hS (closedPointMap a) → ∀ i : I, c • i = 0) :
    (Space.modulePushforward B S hS (specialFibreMap a)).obj
        ((Space.baseRingTensorModule B S hS x₀.obj.obj.left
          (Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap x₀
            (obj_eq_specialFibre x₀ hx₀) ≫ schemeSpaceMap (closedPointMap a)))).obj I) ≅
      (Space.baseRingTensorModule B S hS a.point.obj.obj.left
        (Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq))).obj I :=
  (Space.modulePushforward B S hS (specialFibreMap a)).mapIso
      (specialFibrePullbackTensorIso a I).symm ≪≫
    specialFibrePushforwardPullbackIso a _
      (globalSmul_targetScalars_baseRingTensorModule_eq_zero a I hI)

/-! ### The morphism of ringed topoi on the models -/

/-- **The morphism of ringed topoi `j_m` between the models of the small étale ringed topoi of
`X₀` and `X`**: `ρ_X ∘ j ∘ π_{X₀}`
(`AlgebraicGeometry.Space.smallEtaleModelPullbackRingedToposHom`), the models
`(smallEtaleModelRingedSite X).toRingedTopos` being by definition
`AlgebraicGeometry.Space.modelTopos X`. -/
abbrev specialFibreModelHom :
    RingedToposHom (Space.modelTopos x₀.obj.obj.left) (Space.modelTopos a.point.obj.obj.left) :=
  Space.smallEtaleModelPullbackRingedToposHom (specialFibreMap a)

/-- **The direct image of sheaves of sets along `j_m` is an equivalence**: it is the composite of
the direct image along `j`, an equivalence, with the two equivalences of the models. -/
instance isEquivalence_pushforward_specialFibreModelHom :
    (specialFibreModelHom a).toToposHom.pushforward.IsEquivalence := by
  have := isEquivalence_pushforward_specialFibreMap a
  have : ((Space.smallEtaleModelEquivalence B S hS
      x₀.obj.obj.left.1).inverse.sheafPushforwardContinuous (Type u)
      (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
      (Space.smallEtaleModelTopology B S hS x₀.obj.obj.left.1)).IsEquivalence :=
    (Equivalence.sheafCongr (Space.smallEtaleModelTopology B S hS x₀.obj.obj.left.1)
      (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
      (Space.smallEtaleModelEquivalence B S hS x₀.obj.obj.left.1)
      (Type u)).isEquivalence_functor
  have : ((Space.smallEtaleModelEquivalence B S hS
      a.point.obj.obj.left.1).functor.sheafPushforwardContinuous (Type u)
      (Space.smallEtaleModelTopology B S hS a.point.obj.obj.left.1)
      (Space.SmallEtale.topology B S hS a.point.obj.obj.left.1)).IsEquivalence :=
    (Equivalence.sheafCongr (Space.smallEtaleModelTopology B S hS a.point.obj.obj.left.1)
      (Space.SmallEtale.topology B S hS a.point.obj.obj.left.1)
      (Space.smallEtaleModelEquivalence B S hS a.point.obj.obj.left.1)
      (Type u)).isEquivalence_inverse
  change (((Space.smallEtaleModelEquivalence B S hS
      x₀.obj.obj.left.1).inverse.sheafPushforwardContinuous (Type u)
      (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
      (Space.smallEtaleModelTopology B S hS x₀.obj.obj.left.1) ⋙
    (Space.smallEtaleRingedToposHom B S hS (specialFibreMap a)).toToposHom.pushforward) ⋙
    (Space.smallEtaleModelEquivalence B S hS
      a.point.obj.obj.left.1).functor.sheafPushforwardContinuous (Type u)
      (Space.smallEtaleModelTopology B S hS a.point.obj.obj.left.1)
      (Space.SmallEtale.topology B S hS a.point.obj.obj.left.1)).IsEquivalence
  infer_instance

/-- **The direct image of sheaves of modules along `j_m` is exact**: it is left exact as a right
adjoint, and right exact because the direct image of sheaves of sets, an equivalence, preserves
epimorphisms. -/
theorem preservesFiniteColimits_pushforwardModules_specialFibreModelHom :
    PreservesFiniteColimits (specialFibreModelHom a).pushforwardModules :=
  RingedToposHom.preservesFiniteColimits_pushforwardModules (specialFibreModelHom a)

/-- The direct image of sheaves of modules along `j_m` is left exact. -/
theorem preservesFiniteLimits_pushforwardModules_specialFibreModelHom :
    PreservesFiniteLimits (specialFibreModelHom a).pushforwardModules :=
  RingedToposHom.pushforwardModules_preservesFiniteLimits (specialFibreModelHom a)

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
