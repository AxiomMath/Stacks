module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartScheme

/-!
# Morphisms between the thickenings of étale charts

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X`.  `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartScheme`
attaches to every object `V` of the small étale site of `X` a first-order thickening `V ⊂ V'`
whose structure sheaf is the restriction of `𝒜` to the Zariski site of `V`.  This file makes the
assignment `V ↦ V'` act on morphisms: a morphism `g : V ⟶ U` of the small étale site induces a
morphism of schemes `g' : V' ⟶ U'`, whose map of points is that of `g` and whose map of sections
is the restriction maps of `𝒜`.  This is the functor `U ↦ U'` of the proof of
[Stacks Project, Tag 05ZT].

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.chartThickeningMap`: the morphism `V' ⟶ U'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartThickeningFunctor`: the functor `U ↦ U'`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.chartImmersion_comp_chartThickeningMap`: the
  square formed with `g` and the two inclusions `V ⊂ V'`, `U ⊂ U'` commutes.

## Implementation notes

The stalk maps of `g'` are local because the reductions `𝒜_x ⟶ 𝒪_{V,x}` are local and reflect
units, and the square with `g` commutes; this is
`AlgebraicGeometry.Space.SquareZeroExtension.isLocalHom_stalkMap_chartThickeningMapSh`.

No `@[stacks]` attribute: this is one step of the proof of Tag 05ZT.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Restricting a morphism of schemes to an open and its preimage commutes, on global sections,
with the identification of the global sections of an open subscheme with the sections over the
open. -/
theorem Scheme.morphismRestrict_appTop_restrictFunctorΓ {V U : Scheme.{u}} (g : V ⟶ U)
    (O : U.Opens) :
    (g ∣_ O).appTop ≫ (Scheme.restrictFunctorΓ (X := V)).hom.app (op (g ⁻¹ᵁ O)) =
      (Scheme.restrictFunctorΓ (X := U)).hom.app (op O) ≫ g.app O := by
  have key : ∀ {W₁ W₂ : U.Opens} {W₃ : V.Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ g ⁻¹ᵁ W₁)
      (h₃ : g ⁻¹ᵁ W₂ ≤ W₃),
      g.app W₁ ≫ V.presheaf.map (homOfLE h₂).op ≫ V.presheaf.map (homOfLE h₃).op =
        U.presheaf.map (homOfLE h₁).op ≫ g.app W₂ := by
    intro W₁ W₂ W₃ h₁ h₂ h₃
    rw [← Functor.map_comp, Scheme.Hom.naturality]
    rfl
  simp only [Scheme.restrictFunctorΓ_hom_app, morphismRestrict_appTop]
  exact key (W₁ := O.ι ''ᵁ ⊤) (W₂ := O) (W₃ := (g ⁻¹ᵁ O).ι ''ᵁ ((g ∣_ O) ⁻¹ᵁ ⊤))
    (by simp) (image_morphismRestrict_preimage g O ⊤).le (by simp)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- The sheaf component of the morphism of thickened charts induced by a morphism of charts:
the restriction maps of `𝒜` along the restrictions of the morphism to the opens of the target
and their preimages. -/
def chartThickeningMapC {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    (chartThickenedSpace B S hS E U).presheaf ⟶
      (chartSchemeMap g).base _* (chartThickenedSpace B S hS E V).presheaf :=
  Functor.whiskerRight (NatTrans.op (openChartRestrictNatTrans B S hS X.1 g)) E.A.obj

/-- The morphism of thickened sheafed spaces induced by a morphism of charts. -/
def chartThickeningMapSh {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    chartThickenedSpace B S hS E V ⟶ chartThickenedSpace B S hS E U :=
  InducedCategory.homMk { base := (chartSchemeMap g).base, c := chartThickeningMapC B S hS E g }

/-- **The square of a morphism of charts and its thickening commutes**, as sheafed spaces. -/
theorem chartZariskiInclusion_comp_chartThickeningMapSh {U V : SmallEtale B S hS X.1}
    (g : V ⟶ U) :
    chartZariskiInclusion B S hS E V ≫ chartThickeningMapSh B S hS E g =
      (chartSchemeMap g).toLRSHom.toShHom ≫ chartZariskiInclusion B S hS E U := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  ext O a
  change (Scheme.restrictFunctorΓ (X := chartScheme V)).hom.app (op (chartSchemeMap g ⁻¹ᵁ O))
      (E.π.hom.app _ (E.A.obj.map (openChartRestrict B S hS X.1 g O).op a)) =
    (chartSchemeMap g).app O
      ((Scheme.restrictFunctorΓ (X := chartScheme U)).hom.app (op O) (E.π.hom.app _ a))
  exact (congrArg _ (ConcreteCategory.congr_hom
    (E.π.hom.naturality (openChartRestrict B S hS X.1 g O).op) a)).trans
    (ConcreteCategory.congr_hom
      (Scheme.morphismRestrict_appTop_restrictFunctorΓ (chartSchemeMap g) O) _)

/-- The stalk maps of the morphism of thickened charts are local. -/
theorem isLocalHom_stalkMap_chartThickeningMapSh {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (x : chartScheme V) :
    IsLocalHom ((chartThickeningMapSh B S hS E g).hom.stalkMap x).hom := by
  have hU : IsLocalHom ((chartZariskiInclusion B S hS E U).hom.stalkMap
      ((chartSchemeMap g).base x)).hom := by
    rw [chartZariskiInclusion_stalkMap]
    exact isLocalHom_stalkMap_chartZariskiπ B S hS E U _
  have comp : ∀ {A B C : SheafedSpace CommRingCat.{u}} (p : A ⟶ B) (q : B ⟶ C) (y : A),
      (p ≫ q).hom.stalkMap y = q.hom.stalkMap (p.hom.base y) ≫ p.hom.stalkMap y :=
    fun p q y => PresheafedSpace.stalkMap.comp p.hom q.hom y
  have h1 : IsLocalHom (((chartSchemeMap g).toLRSHom.toShHom ≫
      chartZariskiInclusion B S hS E U).hom.stalkMap x).hom := by
    rw [comp]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ ((chartSchemeMap g).toLRSHom.prop x) hU
  have h2 := LocallyRingedSpace.isLocalHom_stalkMap_congr _ _
    (chartZariskiInclusion_comp_chartThickeningMapSh B S hS E g).symm x h1
  rw [comp] at h2
  exact @isLocalHom_of_comp _ _ _ _ _ _ _ ((chartZariskiInclusion B S hS E V).hom.stalkMap x).hom h2

/-- The morphism of thickened charts induced by a morphism of charts is a morphism of locally
ringed spaces: its stalk maps are local because the reductions are local and reflect units, and
the square with the morphism of charts commutes. -/
def chartThickeningMapLRS {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    chartThickenedLRS B S hS E V ⟶ chartThickenedLRS B S hS E U :=
  LocallyRingedSpace.homMk (X := chartThickenedLRS B S hS E V)
    (Y := chartThickenedLRS B S hS E U) (chartThickeningMapSh B S hS E g) fun x =>
    isLocalHom_stalkMap_chartThickeningMapSh B S hS E g x

/-- **The morphism `V' ⟶ U'` of thickened charts induced by a morphism `V ⟶ U` of charts.** -/
def chartThickeningMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    chartThickening B S hS E V ⟶ chartThickening B S hS E U :=
  Scheme.Hom.mk (chartThickeningMapLRS B S hS E g)

/-- The square of a morphism of charts and the induced morphism of thickenings commutes. -/
theorem chartImmersion_comp_chartThickeningMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    chartImmersion B S hS E V ≫ chartThickeningMap B S hS E g =
      chartSchemeMap g ≫ chartImmersion B S hS E U :=
  Scheme.Hom.ext' (LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (chartZariskiInclusion_comp_chartThickeningMapSh B S hS E g))

/-- Restricting a composite of morphisms of charts to an open is the composite of the
restrictions, up to the identification of the iterated preimage with the preimage. -/
theorem _root_.AlgebraicGeometry.Space.openChartRestrict_comp_of_le
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {W V U : SmallEtale B S hS F}
    (g : W ⟶ V) (g' : V ⟶ U) (O : (chartScheme U).Opens)
    (i : chartSchemeMap g ⁻¹ᵁ (chartSchemeMap g' ⁻¹ᵁ O) ⟶ chartSchemeMap (g ≫ g') ⁻¹ᵁ O) :
    (openChartFunctor B S hS F W).map i ≫ openChartRestrict B S hS F (g ≫ g') O =
      openChartRestrict B S hS F g (chartSchemeMap g' ⁻¹ᵁ O) ≫ openChartRestrict B S hS F g' O := by
  apply hom_ext_of_toScheme_map_eq
  change (chartScheme W).homOfLE i.le ≫ (chartSchemeMap (g ≫ g') ∣_ O) =
    (chartSchemeMap g ∣_ (chartSchemeMap g' ⁻¹ᵁ O)) ≫ (chartSchemeMap g' ∣_ O)
  rw [← cancel_mono O.ι, Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
    ← Category.assoc, Scheme.homOfLE_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  simp [chartSchemeMap]

/-- The morphism of sheafed spaces underlying the map of thickened charts of a composite is the
composite of the morphisms. -/
theorem chartThickeningMapSh_comp {W V U : SmallEtale B S hS X.1} (g : W ⟶ V) (g' : V ⟶ U) :
    chartThickeningMapSh B S hS E (g ≫ g') =
      chartThickeningMapSh B S hS E g ≫ chartThickeningMapSh B S hS E g' := by
  have hb : (chartSchemeMap (g ≫ g')).base =
      (chartSchemeMap g).base ≫ (chartSchemeMap g').base := by
    simp [chartSchemeMap]
  refine SheafedSpace.ext _ _ hb ?_
  ext O a
  revert a
  obtain ⟨O, rfl⟩ : ∃ O' : (chartScheme U).Opens, O' = O := ⟨O, rfl⟩
  intro a
  rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app]
  change (E.A.obj.map (openChartRestrict B S hS X.1 (g ≫ g') O).op ≫
      E.A.obj.map ((openChartFunctor B S hS X.1 W).op.map (eqToHom _))) a =
    (E.A.obj.map (openChartRestrict B S hS X.1 g' O).op ≫
      E.A.obj.map (openChartRestrict B S hS X.1 g (chartSchemeMap g' ⁻¹ᵁ O)).op) a
  refine ConcreteCategory.congr_hom (((E.A.obj.map_comp _ _).symm.trans
    (congrArg E.A.obj.map (Quiver.Hom.unop_inj ?_))).trans (E.A.obj.map_comp _ _)) a
  exact openChartRestrict_comp_of_le B S hS X.1 g g' O (homOfLE (le_of_eq (by
    rw [show chartSchemeMap (g ≫ g') = chartSchemeMap g ≫ chartSchemeMap g' by
      simp [chartSchemeMap], Scheme.Hom.comp_preimage])))

/-- Restricting the identity morphism of a chart to an open is the identity, up to the
identification of the preimage with the open. -/
theorem _root_.AlgebraicGeometry.Space.openChartRestrict_id
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U : SmallEtale B S hS F) (O : (chartScheme U).Opens)
    (i : O ⟶ chartSchemeMap (𝟙 U) ⁻¹ᵁ O) :
    (openChartFunctor B S hS F U).map i ≫ openChartRestrict B S hS F (𝟙 U) O = 𝟙 _ := by
  apply hom_ext_of_toScheme_map_eq
  change (chartScheme U).homOfLE i.le ≫ (chartSchemeMap (𝟙 U) ∣_ O) = 𝟙 _
  rw [← cancel_mono O.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Scheme.homOfLE_ι, Category.id_comp]
  simp [chartSchemeMap]

/-- The morphism of sheafed spaces underlying the map of thickened charts of the identity is the
identity. -/
theorem chartThickeningMapSh_id (U : SmallEtale B S hS X.1) :
    chartThickeningMapSh B S hS E (𝟙 U) = 𝟙 _ := by
  have hb : (chartSchemeMap (𝟙 U)).base = 𝟙 _ := by simp [chartSchemeMap]
  refine SheafedSpace.ext _ _ hb ?_
  ext O a
  revert a
  obtain ⟨O, rfl⟩ : ∃ O' : (chartScheme U).Opens, O' = O := ⟨O, rfl⟩
  intro a
  rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app]
  have hO : O ≤ chartSchemeMap (𝟙 U) ⁻¹ᵁ O := by simp [chartSchemeMap]
  exact ConcreteCategory.congr_hom ((E.A.obj.map_comp _ _).symm.trans
    ((congrArg E.A.obj.map (Quiver.Hom.unop_inj
      (openChartRestrict_id B S hS X.1 U O (homOfLE hO)))).trans (E.A.obj.map_id _))) a

/-- **The functor `U ↦ U'`** of the proof of [Stacks Project, Tag 05ZT], on the whole small étale
site of `X`. -/
def chartThickeningFunctor : SmallEtale B S hS X.1 ⥤ Scheme.{u} where
  obj U := chartThickening B S hS E U
  map g := chartThickeningMap B S hS E g
  map_id U := Scheme.Hom.ext' (LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (chartThickeningMapSh_id B S hS E U))
  map_comp g g' := Scheme.Hom.ext' (LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (chartThickeningMapSh_comp B S hS E g g'))

/-- The functor `chartThickeningFunctor` sends a morphism of charts `g` to
`chartThickeningMap g`. -/
theorem chartThickeningFunctor_map {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    (chartThickeningFunctor B S hS E).map g = chartThickeningMap B S hS E g := rfl

/-- An affine open of the thickening of a chart is an affine open of the chart. -/
theorem isAffineOpen_of_isAffineOpen_chartThickening (U : SmallEtale B S hS X.1)
    {O : (chartScheme U).Opens} (hO : IsAffineOpen (X := chartThickening B S hS E U) O) :
    IsAffineOpen O :=
  have := (isFirstOrderThickening_chartImmersion B S hS E U).1
  hO.preimage (chartImmersion B S hS E U)

/-- The ring map of sections of the morphism of thickened charts over an affine open and an
affine open of its preimage is a restriction map of `𝒜`. -/
theorem chartThickeningMap_appLE {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (O : (chartScheme U).Opens) (Q : (chartScheme V).Opens) (e : Q ≤ chartSchemeMap g ⁻¹ᵁ O) :
    (chartThickeningMap B S hS E g).appLE O Q e =
      E.A.obj.map ((openChartFunctor B S hS X.1 V).map (homOfLE e) ≫
        openChartRestrict B S hS X.1 g O).op :=
  (E.A.obj.map_comp _ _).symm

/-- **The morphism of thickened charts induced by a morphism of the small étale site is
étale.**  Étaleness is affine-local, and on affine opens the map of sections is a restriction map
of `𝒜` between affine objects of the small étale site, which is étale by
`AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isAffine`. -/
theorem etale_chartThickeningMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    Etale (chartThickeningMap B S hS E g) := by
  rw [HasRingHomProperty.iff_appLE (P := @Etale)]
  rintro ⟨O, hO⟩ ⟨Q, hQ⟩ e
  let m : openChart B S hS X.1 V Q ⟶ openChart B S hS X.1 U O :=
    (openChartFunctor B S hS X.1 V).map (homOfLE e) ≫ openChartRestrict B S hS X.1 g O
  let : Algebra (E.A.obj.obj (op (openChart B S hS X.1 U O)))
      (E.A.obj.obj (op (openChart B S hS X.1 V Q))) := (E.A.obj.map m.op).hom.toAlgebra
  change RingHom.Etale ((chartThickeningMap B S hS E g).appLE O Q e).hom
  rw [chartThickeningMap_appLE B S hS E g O Q e]
  exact SquareZeroExtension.algebraEtale_app_of_isAffine B S hS E m
    (isAffineOpen_of_isAffineOpen_chartThickening B S hS E V hQ)
    (isAffineOpen_of_isAffineOpen_chartThickening B S hS E U hO) rfl

/-- **The square of a morphism of charts and its thickening is cartesian**: `V = U ×_{U'} V'`.
The comparison `V ⟶ U ×_{U'} V'` is étale, being a morphism of étale `U`-schemes, a closed
immersion, being one after composition with the closed immersion `U ×_{U'} V' ⟶ V'`, and
surjective, because all four schemes have the points of their reductions; so it is an
isomorphism. -/
theorem isPullback_chartImmersion_chartThickeningMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    IsPullback (chartImmersion B S hS E V) (chartSchemeMap g) (chartThickeningMap B S hS E g)
      (chartImmersion B S hS E U) := by
  have hsq := chartImmersion_comp_chartThickeningMap B S hS E g
  have := (isFirstOrderThickening_chartImmersion B S hS E U).1
  have := (isFirstOrderThickening_chartImmersion B S hS E V).1
  have := etale_chartThickeningMap B S hS E g
  have : Etale (chartSchemeMap g) := SmallEtale.etale_map B S hS X.1 g
  let φ : chartScheme V ⟶ pullback (chartThickeningMap B S hS E g) (chartImmersion B S hS E U) :=
    pullback.lift _ _ hsq
  have hφ₁ : φ ≫ pullback.fst _ _ = chartImmersion B S hS E V := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd _ _ = chartSchemeMap g := pullback.lift_snd _ _ _
  have : Etale (φ ≫ pullback.snd _ _) := hφ₂ ▸ inferInstance
  have : Etale φ := Etale.of_comp φ (pullback.snd _ _)
  have : AlgebraicGeometry.IsClosedImmersion (φ ≫ pullback.fst _ _) := hφ₁ ▸ inferInstance
  have : AlgebraicGeometry.IsClosedImmersion φ :=
    AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion φ (pullback.fst _ _)
  have : Surjective φ := by
    refine ⟨fun p => ⟨(pullback.fst (chartThickeningMap B S hS E g)
      (chartImmersion B S hS E U)).base p, ?_⟩⟩
    exact (pullback.fst (chartThickeningMap B S hS E g)
      (chartImmersion B S hS E U)).isClosedEmbedding.injective
      ((Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun k => k.base ((pullback.fst (chartThickeningMap B S hS E g)
          (chartImmersion B S hS E U)).base p)) hφ₁).trans rfl))
  have : IsIso φ := Stacks.Etale.isIso_of_etale_of_universallyInjective_of_surjective φ
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso φ) hφ₁ hφ₂

/-- **A morphism of étale schemes over a thickening is an isomorphism as soon as its base change
to the reduction is**, in the form of two cartesian squares with a common corner: by
[Stacks Project, Tag 039R] base change to the reduction is an equivalence of étale sites, so it
reflects isomorphisms. -/
theorem _root_.AlgebraicGeometry.isIso_of_isPullback_of_isPullback_of_surjective_isClosedImmersion
    {T₀ T A B C : Scheme.{u}} (i : T₀ ⟶ T) [AlgebraicGeometry.IsClosedImmersion i]
    (hi : Function.Surjective i.base) (p : A ⟶ T) (q : B ⟶ T) [Etale p] [Etale q] (ψ : A ⟶ B)
    (hψ : ψ ≫ q = p) (c₁ : C ⟶ A) (c₂ : C ⟶ T₀) (hA : IsPullback c₁ c₂ p i)
    (hB : IsPullback (c₁ ≫ ψ) c₂ q i) : IsIso ψ := by
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : T.Etale ⥤ T₀.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ i
  have : F.IsEquivalence :=
    Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion i hi
  let A' : T.Etale := MorphismProperty.Over.mk ⊤ p ‹_›
  let B' : T.Etale := MorphismProperty.Over.mk ⊤ q ‹_›
  let ψ' : A' ⟶ B' := MorphismProperty.Over.homMk ψ hψ
  have hl : (F.map ψ').left = hA.isoPullback.inv ≫ hB.isoPullback.hom := by
    apply pullback.hom_ext
    · refine (pullback.lift_fst _ _ _).trans ?_
      change pullback.fst p i ≫ ψ = (hA.isoPullback.inv ≫ hB.isoPullback.hom) ≫ pullback.fst q i
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc,
        IsPullback.isoPullback_inv_fst]
    · refine (pullback.lift_snd _ _ _).trans ?_
      change pullback.snd p i = (hA.isoPullback.inv ≫ hB.isoPullback.hom) ≫ pullback.snd q i
      rw [Category.assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_inv_snd]
  have : IsIso ((Over.forget T₀).map
      ((Scheme.Etale.forget T₀).map (F.map ψ'))) := by
    change IsIso (F.map ψ').left
    rw [hl]
    exact inferInstanceAs (IsIso (hA.isoPullback.symm ≪≫ hB.isoPullback).hom)
  have : IsIso ((Scheme.Etale.forget T₀).map (F.map ψ')) :=
    isIso_of_reflects_iso _ (Over.forget T₀)
  have : IsIso (F.map ψ') := isIso_of_reflects_iso _ (Scheme.Etale.forget T₀)
  have : IsIso ψ' := isIso_of_reflects_iso ψ' F
  change IsIso ((Over.forget T).map ((Scheme.Etale.forget T).map ψ'))
  infer_instance

/-- **The thickened chart functor carries fibre products of the small étale site to fibre
products of schemes**: `(V ×_U W)' = V' ×_{U'} W'`.  The comparison is a morphism of étale
`W'`-schemes whose base change to `W` is an isomorphism, by the cartesian squares of the
reductions, so it is an isomorphism by
`AlgebraicGeometry.isIso_of_isPullback_of_isPullback_of_surjective_isClosedImmersion`. -/
theorem isPullback_chartThickeningMap_of_toScheme {P V W U : SmallEtale B S hS X.1}
    {a : P ⟶ V} {b : P ⟶ W} {g : V ⟶ U} {h : W ⟶ U} (hw : a ≫ g = b ≫ h)
    (HS : IsPullback (chartSchemeMap a) (chartSchemeMap b) (chartSchemeMap g) (chartSchemeMap h)) :
    IsPullback (chartThickeningMap B S hS E a) (chartThickeningMap B S hS E b)
      (chartThickeningMap B S hS E g) (chartThickeningMap B S hS E h) := by
  have hcomm : chartThickeningMap B S hS E a ≫ chartThickeningMap B S hS E g =
      chartThickeningMap B S hS E b ≫ chartThickeningMap B S hS E h :=
    ((chartThickeningFunctor B S hS E).map_comp a g).symm.trans
      ((congrArg (chartThickeningFunctor B S hS E).map hw).trans
        ((chartThickeningFunctor B S hS E).map_comp b h))
  have := (isFirstOrderThickening_chartImmersion B S hS E W).1
  have := etale_chartThickeningMap B S hS E b
  have := etale_chartThickeningMap B S hS E g
  let ψ := pullback.lift (chartThickeningMap B S hS E a) (chartThickeningMap B S hS E b) hcomm
  have hψ₁ : ψ ≫ pullback.fst _ _ = chartThickeningMap B S hS E a := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd _ _ = chartThickeningMap B S hS E b := pullback.lift_snd _ _ _
  have houter : IsPullback ((chartImmersion B S hS E P ≫ ψ) ≫ pullback.fst _ _)
      (chartSchemeMap b) (chartThickeningMap B S hS E g)
      (chartImmersion B S hS E W ≫ chartThickeningMap B S hS E h) := by
    rw [Category.assoc, hψ₁, chartImmersion_comp_chartThickeningMap,
      chartImmersion_comp_chartThickeningMap]
    exact HS.paste_horiz (isPullback_chartImmersion_chartThickeningMap B S hS E g)
  have hB : IsPullback (chartImmersion B S hS E P ≫ ψ) (chartSchemeMap b) (pullback.snd _ _)
      (chartImmersion B S hS E W) :=
    IsPullback.of_right houter (by
      rw [Category.assoc, hψ₂, chartImmersion_comp_chartThickeningMap])
      (IsPullback.of_hasPullback _ _)
  have : IsIso ψ := isIso_of_isPullback_of_isPullback_of_surjective_isClosedImmersion
    (chartImmersion B S hS E W)
    (isFirstOrderThickening_chartImmersion B S hS E W).isThickening.2
    (chartThickeningMap B S hS E b) (pullback.snd _ _) ψ hψ₂ _ _
    (isPullback_chartImmersion_chartThickeningMap B S hS E b) hB
  exact IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso ψ) hψ₁ hψ₂

/-- The maps of thickened charts carry a pullback square of the small étale site of `X` to a
pullback square of schemes. -/
theorem isPullback_chartThickeningMap {P V W U : SmallEtale B S hS X.1} {a : P ⟶ V} {b : P ⟶ W}
    {g : V ⟶ U} {h : W ⟶ U} (H : IsPullback a b g h) :
    IsPullback (chartThickeningMap B S hS E a) (chartThickeningMap B S hS E b)
      (chartThickeningMap B S hS E g) (chartThickeningMap B S hS E h) :=
  isPullback_chartThickeningMap_of_toScheme B S hS E H.w
    ((H.map (SmallEtale.toOver B S hS X.1)).map (BigFppfOver.toScheme B S hS))

/-- The map of thickened charts of a composite is the composite of the maps. -/
theorem chartThickeningMap_comp {W V U : SmallEtale B S hS X.1} (g : W ⟶ V) (g' : V ⟶ U) :
    chartThickeningMap B S hS E (g ≫ g') =
      chartThickeningMap B S hS E g ≫ chartThickeningMap B S hS E g' :=
  (chartThickeningFunctor B S hS E).map_comp g g'

/-- The map of thickened charts of the identity is the identity. -/
theorem chartThickeningMap_id (U : SmallEtale B S hS X.1) :
    chartThickeningMap B S hS E (𝟙 U) = 𝟙 _ :=
  (chartThickeningFunctor B S hS E).map_id U

end SquareZeroExtension

end Space

end AlgebraicGeometry

end
