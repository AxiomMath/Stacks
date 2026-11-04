module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSquareZeroLiftDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposTransitivityTriangleDerived
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.SolutionSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Obstruction.SpaceExtFunctors

/-!
# The deformation theory of `Spaces'_{fp, flat, proper}` at a chart: the data of the 07YZ route

In the `07YZ` route of [Stacks, Remark 0D1P] to [Stacks, Lemma 0D3X] the deformation theory of
an object `x = (X → Spec A)` of `Spaces'_{fp, flat, proper}` over an affine chart is read off the
cotangent complex of `X → Spec A` through [Stacks, Section 08V3]: tangent vectors are
`Ext¹_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A M)` and obstructions live in `Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)`.
This file fixes the two pieces of data in terms of which those groups are formed, and records the
first half of the dictionary between lifts in the stack and the extension problems of
[Stacks, Section 08V3].

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.chartStructureMap` — `X → Spec A`, the structure
  morphism of `x` as a morphism of algebraic spaces into `Spec A`.
* `AlgebraicGeometry.Space.ProperFlatLift.chartBaseRingHom` — the base-ring datum `A → Γ(𝒪_X)` on
  the model of the small étale site, through `A ≅ Γ(Spec A)`; `𝒪_X ⊗_A −` is
  `AlgebraicGeometry.Space.modelTensorFunctor` of it, and the functors
  `M ↦ Ext^i_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A M)` of the source are
  `AlgebraicGeometry.Space.cotangentExtOne/Two (chartStructureMap x hx) (chartBaseRingHom x hx)`,
  functors `ModuleCat A ⥤ ModuleCat A` as `Deformation.Artin.FunctorDeformationTheory` wants.
* `AlgebraicGeometry.Space.ProperFlatLift.chartExtConnecting` — the connecting map
  `T¹(M₃) ⟶ T²(M₁)` of a short exact sequence of `A`-modules, the field `δ` of that structure.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.shortExact_map_modelTensorFunctor_chartBaseRingHom` —
  `M ↦ 𝒪_X ⊗_A M` is exact, `X` being flat over `A`.

* `AlgebraicGeometry.Space.modelCotangentComplexIsoOfCompIso` — `L_{X/Z} ≅ L_{X/Y}` on the model
  of the small étale site of `X`, for `g : X ⟶ Y` and an isomorphism `Y ≅ Z`; at a chart,
  `AlgebraicGeometry.Space.ProperFlatLift.chartCotangentComplexIso` identifies the cotangent
  complex of the extension problem of `X → Spec A ⊂ Spec A'` with `L_{X/A}`.
* `AlgebraicGeometry.Space.ProperFlatLift.isSquareZeroClosedImmersion_arrow` — the closed
  immersion `Spec A ⟶ Spec A'` of a square-zero thickening of Situation 07YX is a square-zero
  closed immersion of the site.
* `AlgebraicGeometry.Space.ProperFlatLift.nonempty_lift_iff_nonempty_solution` — `x` lifts along
  a square-zero thickening of Situation 07YX exactly when the extension problem on the small étale
  site of `X` attached to `X → Spec A ⊂ Spec A'` has a solution: a lift, a flat deformation
  ([Stacks, Tag 0D17]) and a solution are the same thing. This is the lifting side of the field
  `obstruction_iff_lift`, whose other side is [Stacks, Tag 08V5] (1).

## References

* [Stacks Project, Tag 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u v₁ w₁ v₂ w₂ v' u'

/-! ### Transport of an identification of inverse images to an equivalent site -/

namespace Deformation.ToposThickening

open AlgebraicGeometry RingedToposExtensionProblem
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

variable {X : RingedTopos.{w₁, v₁, u}} {B₁ B₂ : RingedTopos.{v', u', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B₁.J.HasSheafCompose (forget RingCat.{u})]
  [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {D : Type v₂} [Category.{w₂} D] (K : GrothendieckTopology D) (e : X.C ≌ D)
  [e.inverse.IsDenseSubsite K X.J]
  [K.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (f₁ : RingedToposHom X B₁) (f₂ : RingedToposHom X B₂)

/-- An identification `f₁⁻¹F₁ ≅ f₂⁻¹F₂` of inverse images of sheaves of rings on the two bases,
carried to the transported morphisms `f'ᵢ = fᵢ ∘ (Sh(𝒟) ≅ Sh(𝒞))` of `siteTransportHom`. -/
noncomputable def siteTransportInverseImageRingIso {F₁ : Sheaf B₁.J CommRingCat.{u}}
    {F₂ : Sheaf B₂.J CommRingCat.{u}}
    (a : (inverseImageCommRingFunctor f₁.toToposHom).obj F₁ ≅
      (inverseImageCommRingFunctor f₂.toToposHom).obj F₂) :
    (inverseImageCommRingFunctor (siteTransportHom K e f₁).toToposHom).obj F₁ ≅
      (inverseImageCommRingFunctor (siteTransportHom K e f₂).toToposHom).obj F₂ :=
  (siteTransportInverseImageIso K e f₁.toToposHom).app F₁ ≪≫
    (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).mapIso a ≪≫
    ((siteTransportInverseImageIso K e f₂.toToposHom).app F₂).symm

/-- **The transport of identifications of inverse images is natural**: identifications
`a : f₁⁻¹F₁ ≅ f₂⁻¹F₂` and `b : f₁⁻¹F₁' ≅ f₂⁻¹F₂'` compatible with maps `m₁ : F₁ ⟶ F₁'` and
`m₂ : F₂ ⟶ F₂'` stay compatible after transport to the equivalent site. -/
theorem siteTransportInverseImageRingIso_hom_comp_map {F₁ F₁' : Sheaf B₁.J CommRingCat.{u}}
    {F₂ F₂' : Sheaf B₂.J CommRingCat.{u}} (m₁ : F₁ ⟶ F₁') (m₂ : F₂ ⟶ F₂')
    (a : (inverseImageCommRingFunctor f₁.toToposHom).obj F₁ ≅
      (inverseImageCommRingFunctor f₂.toToposHom).obj F₂)
    (b : (inverseImageCommRingFunctor f₁.toToposHom).obj F₁' ≅
      (inverseImageCommRingFunctor f₂.toToposHom).obj F₂')
    (h : a.hom ≫ (inverseImageCommRingFunctor f₂.toToposHom).map m₂ =
      (inverseImageCommRingFunctor f₁.toToposHom).map m₁ ≫ b.hom) :
    (siteTransportInverseImageRingIso K e f₁ f₂ a).hom ≫
        (inverseImageCommRingFunctor (siteTransportHom K e f₂).toToposHom).map m₂ =
      (inverseImageCommRingFunctor (siteTransportHom K e f₁).toToposHom).map m₁ ≫
        (siteTransportInverseImageRingIso K e f₁ f₂ b).hom := by
  have n₂ := (siteTransportInverseImageIso K e f₂.toToposHom).inv.naturality m₂
  have n₁ := (siteTransportInverseImageIso K e f₁.toToposHom).hom.naturality m₁
  simp only [Functor.comp_map] at n₁ n₂
  show ((siteTransportInverseImageIso K e f₁.toToposHom).hom.app F₁ ≫
      (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).map a.hom ≫
      (siteTransportInverseImageIso K e f₂.toToposHom).inv.app F₂) ≫
        (inverseImageCommRingFunctor (f₂.toToposHom.comp
          (X.ofSiteEquivalenceToposHom K e))).map m₂ =
    (inverseImageCommRingFunctor (f₁.toToposHom.comp (X.ofSiteEquivalenceToposHom K e))).map m₁ ≫
      (siteTransportInverseImageIso K e f₁.toToposHom).hom.app F₁' ≫
      (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).map b.hom ≫
      (siteTransportInverseImageIso K e f₂.toToposHom).inv.app F₂'
  rw [Category.assoc, Category.assoc, ← n₂, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
    ← reassoc_of% n₁]

/-- The transported identification is compatible with the structure maps, if `a` is. -/
theorem siteTransportInverseImageRingIso_hom_fSharpInverseImage
    (a : (inverseImageCommRingFunctor f₁.toToposHom).obj B₁.O ≅
      (inverseImageCommRingFunctor f₂.toToposHom).obj B₂.O)
    (ha : a.hom ≫ f₂.fSharpInverseImage = f₁.fSharpInverseImage) :
    (siteTransportInverseImageRingIso K e f₁ f₂ a).hom ≫
        (siteTransportHom K e f₂).fSharpInverseImage =
      (siteTransportHom K e f₁).fSharpInverseImage := by
  show (siteTransportInverseImageIso K e f₁.toToposHom).hom.app B₁.O ≫
      (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).map a.hom ≫
      (siteTransportInverseImageIso K e f₂.toToposHom).inv.app B₂.O ≫
      (siteTransportHom K e f₂).fSharpInverseImage = _
  rw [siteTransportHom_fSharpInverseImage, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, ha,
    siteTransportHom_fSharpInverseImage]

end Deformation.ToposThickening

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

/-! ### The cotangent complex does not see an isomorphism of the target -/

section CotangentIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y) (ρ : Y ≅ Z)

/-- The structure map of the small étale ringed topos morphism of an isomorphism of algebraic
spaces is an isomorphism (an isomorphism is étale, Stacks 03LV). -/
theorem isIso_fSharpInverseImage_iso_hom :
    IsIso (smallEtaleRingedToposHom B S hS ρ.hom).fSharpInverseImage := by
  have : IsIso ρ.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map ρ.hom))
  exact isIso_fSharpInverseImage_of_isEtale B S hS ρ.hom (isEtale_of_isIso B S hS ρ.hom.hom)

/-- **`(g ≫ ρ)⁻¹𝒪_Z ≅ g⁻¹𝒪_Y`** on the small étale site of `X`, for an isomorphism `ρ : Y ≅ Z`:
the composition law of inverse images followed by `g⁻¹` of the structure map `ρ⁻¹𝒪_Z ≅ 𝒪_Y`. -/
noncomputable def inverseImageRingIsoOfCompIso :
    (smallEtaleInverseImageRing B S hS (g ≫ ρ.hom)).obj (smallEtaleRingedTopos B S hS Z).O ≅
      (smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS Y).O :=
  haveI := isIso_fSharpInverseImage_iso_hom ρ
  ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS g ρ.hom).app _).symm ≪≫
    (smallEtaleInverseImageRing B S hS g).mapIso
      (asIso (smallEtaleRingedToposHom B S hS ρ.hom).fSharpInverseImage)

/-- The isomorphism `inverseImageRingIsoOfCompIso g ρ` intertwines the structure maps of the
morphisms of ringed topoi of `g ≫ ρ` and of `g`. -/
theorem inverseImageRingIsoOfCompIso_hom_fSharpInverseImage :
    (inverseImageRingIsoOfCompIso g ρ).hom ≫
        (smallEtaleRingedToposHom B S hS g).fSharpInverseImage =
      (smallEtaleRingedToposHom B S hS (g ≫ ρ.hom)).fSharpInverseImage := by
  rw [inverseImageRingIsoOfCompIso, Iso.trans_hom, Category.assoc, Functor.mapIso_hom, asIso_hom,
    ← smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS g ρ.hom,
    Iso.symm_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]

/-- **`(g ≫ ρ)⁻¹𝒪_Z ≅ g⁻¹𝒪_Y` on the model of the small étale site of `X`.** -/
noncomputable def modelInverseImageRingIsoOfCompIso :
    (inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
        (modelRingedToposHom (g ≫ ρ.hom)).toToposHom).obj (smallEtaleRingedTopos B S hS Z).O ≅
      (inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
        (modelRingedToposHom g).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O :=
  Deformation.ToposThickening.siteTransportInverseImageRingIso
    (X := smallEtaleRingedTopos B S hS X) (smallEtaleModelTopology B S hS X.1)
    (smallEtaleModelEquiv B S hS X)
    (smallEtaleRingedToposHom B S hS (g ≫ ρ.hom)) (smallEtaleRingedToposHom B S hS g)
    (inverseImageRingIsoOfCompIso g ρ)

/-- The isomorphism `modelInverseImageRingIsoOfCompIso g ρ` intertwines the structure maps of the
model morphisms of ringed topoi of `g ≫ ρ` and of `g`. -/
theorem modelInverseImageRingIsoOfCompIso_hom_fSharpInverseImage :
    (modelInverseImageRingIsoOfCompIso g ρ).hom ≫ (modelRingedToposHom g).fSharpInverseImage =
      (modelRingedToposHom (g ≫ ρ.hom)).fSharpInverseImage :=
  Deformation.ToposThickening.siteTransportInverseImageRingIso_hom_fSharpInverseImage
    (X := smallEtaleRingedTopos B S hS X) (smallEtaleModelTopology B S hS X.1)
    (smallEtaleModelEquiv B S hS X) (smallEtaleRingedToposHom B S hS (g ≫ ρ.hom))
    (smallEtaleRingedToposHom B S hS g) (inverseImageRingIsoOfCompIso g ρ)
    (inverseImageRingIsoOfCompIso_hom_fSharpInverseImage g ρ)

variable [HasDerivedCategory.{t} (modelModules X)]

/-- **(G1) `L_{X/Z} ≅ L_{X/Y}` for an isomorphism `ρ : Y ≅ Z`**, on the model of the small étale
site of `X`: the cotangent complex of `g ≫ ρ` is that of `g`, through the isomorphism of inverse
images of structure sheaves `(g ≫ ρ)⁻¹𝒪_Z ≅ g⁻¹𝒪_Y` compatible with the two structure maps
(`AlgebraicGeometry.Space.modelInverseImageRingIsoOfCompIso`). -/
noncomputable def modelCotangentComplexIsoOfCompIso :
    (modelRingedToposHom (g ≫ ρ.hom)).cotangentComplexDerived ≅
      (modelRingedToposHom g).cotangentComplexDerived :=
  DerivedCategory.Q.mapIso
    (CategoryTheory.Sheaf.squareCotangentComplexIso
        (a := (modelInverseImageRingIsoOfCompIso g ρ).hom) (b := 𝟙 (modelTopos X).O)
        ((Category.comp_id _).trans
          (modelInverseImageRingIsoOfCompIso_hom_fSharpInverseImage g ρ).symm) ≪≫
      SheafOfModules.restrictScalarsIdComplexIso _
        ((sheafCompose (modelTopos X).J (forget₂ CommRingCat.{u} RingCat.{u})).map_id _) _)

end CotangentIso

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Stacks.Cohomology.SiteModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

/-! ### The base-ring datum at a chart -/

/-- **The structure morphism `X → Spec A` of `x`**, as a morphism of algebraic spaces into the
space represented by `Spec A`. -/
def chartStructureMap : x.obj.obj.left ⟶ schemeSpace (algebraOver A B S hS toS hA) :=
  commaHomAsSpaceMap x.obj.obj ≫ (schemeSpaceFunctor B S hS).map (eqToHom hx)

/-- **The base-ring datum `A → Γ(𝒪_X)` of `x`** on the model of the small étale site of `X`: the
global functions of `Spec A` pulled back along `X → Spec A`, precomposed with `A ≅ Γ(Spec A)`.
The functor `𝒪_X ⊗_A −` of the source is `AlgebraicGeometry.Space.modelTensorFunctor` of it. -/
def chartBaseRingHom : A →+* modelGlobalFunctions B S hS x.obj.obj.left :=
  (baseRingHomOfMap (chartStructureMap x hx)).comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The structure morphism of `x` at a chart is flat. -/
theorem isFlat_chartStructureMap : Space.IsFlat B S hS (chartStructureMap x hx).hom :=
  isFlat_commaHomAsSpaceMap_comp_eqToHom hx x.obj.property.2.1

/-- **`M ↦ 𝒪_X ⊗_A M` is exact at a chart**: for a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of
`A`-modules, `0 → 𝒪_X ⊗_A M₁ → 𝒪_X ⊗_A M₂ → 𝒪_X ⊗_A M₃ → 0` is short exact on the model. The
functor is a left adjoint, hence right exact; it preserves injections because the rings of the
affine étale charts of `X` are flat over `Γ(Spec A)` (`X → Spec A` being flat), hence over `A`
through the isomorphism `A ≅ Γ(Spec A)`. -/
theorem shortExact_map_modelTensorFunctor_chartBaseRingHom
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) :
    (Sq.map (modelTensorFunctor (chartBaseRingHom x hx))).ShortExact := by
  have adj := baseRingTensorAdjunction.{u, u, u, u, u} (chartBaseRingHom x hx)
  have : PreservesColimitsOfSize.{0, 0}
      (baseRingTensorFunctor.{u, u, u, u, u} (chartBaseRingHom x hx)) :=
    adj.leftAdjoint_preservesColimits
  have : (modelTensorFunctor (chartBaseRingHom x hx)).IsLeftAdjoint := adj.isLeftAdjoint
  have := hSq.mono_f
  have := hSq.epi_g
  have hcov : ∀ W, ∃ (I : Type u) (Vi : I → SmallModel.{u} (SmallEtale B S hS x.obj.obj.left.1))
      (g : ∀ i, Vi i ⟶ W), Sieve.ofArrows Vi g ∈ smallEtaleModelTopology B S hS x.obj.obj.left.1 W ∧
        ∀ i, let := baseRingSectionAlgebra (chartBaseRingHom x hx) (Opposite.op (Vi i));
          Module.Flat A ((smallEtaleModelStructureSheaf B S hS x.obj.obj.left).obj.obj
            (Opposite.op (Vi i))) := by
    intro W
    obtain ⟨I, Vi, g, hS', hfl⟩ := exists_ofArrows_mem_modelTopology_flat (chartStructureMap x hx)
      (isFlat_chartStructureMap x hx) (inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))) W
    refine ⟨I, Vi, g, hS', fun i => ?_⟩
    have h := RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)) (hfl i)
    exact h
  have : Mono (Sq.map (modelTensorFunctor (chartBaseRingHom x hx))).f :=
    Stacks.Cohomology.SiteModules.mono_baseRingTensorFunctor_map (chartBaseRingHom x hx) hcov Sq.f
      ((ModuleCat.mono_iff_injective Sq.f).1 inferInstance)
  have : Epi (Sq.map (modelTensorFunctor (chartBaseRingHom x hx))).g :=
    inferInstanceAs (Epi ((modelTensorFunctor (chartBaseRingHom x hx)).map Sq.g))
  exact ShortComplex.ShortExact.mk' (hSq.exact.map_of_epi_of_preservesCokernel _ inferInstance
    inferInstance) inferInstance inferInstance

/-- **The connecting map `T¹(M₃) ⟶ T²(M₁)` at a chart**, for every short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of `A`-modules: `AlgebraicGeometry.Space.cotangentExtConnecting` of the
short exact sequence `0 → 𝒪_X ⊗_A M₁ → 𝒪_X ⊗_A M₂ → 𝒪_X ⊗_A M₃ → 0`. This is the field `δ` of
`Deformation.Artin.FunctorDeformationTheory` for `Spaces'_{fp, flat, proper}`. -/
def chartExtConnecting [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) :
    (cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj Sq.X₃ ⟶
      (cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)).obj Sq.X₁ :=
  cotangentExtConnecting (chartStructureMap x hx) (chartBaseRingHom x hx)
    (shortExact_map_modelTensorFunctor_chartBaseRingHom x hx hSq)

/-! ### Lifts along a square-zero thickening of Situation 07YX -/

variable {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')

/-- The closed immersion `Spec A ⟶ Spec A'` of a square-zero thickening of Situation 07YX is a
square-zero closed immersion of the site. -/
theorem isSquareZeroClosedImmersion_arrow : IsSquareZeroClosedImmersion B S hS D.arrow :=
  isSquareZeroClosedImmersion_of_specMap B S hS (CommRingCat.ofHom D.q)
    D.squareZeroSurjection.1 D.squareZeroSurjection.2 _ _ D.arrow (Iso.refl _) (Iso.refl _)
    (D.arrow_spec.trans ((Category.id_comp _).trans (Category.comp_id _)).symm)

/-- The special map of `x` along `Spec A ⊂ Spec A'` is flat: it is the flat structure morphism
of `x` followed by an isomorphism. -/
theorem isFlat_specialMap_arrow :
    Space.IsFlat B S hS (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x hx).hom := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsFlat B S hS g.hom
  exact @MorphismProperty.RespectsIso.postcomp _ _ P
    (@MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ P
      (isFlat_isStableUnderBaseChange B S hS)) _ _ _
    (rangeSpaceIso B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1).hom
    (Iso.isIso_hom _) (chartStructureMap x hx) (isFlat_chartStructureMap x hx)

/-- The special map of `x` along `Spec A ⊂ Spec A'` is the structure morphism `X → Spec A`
followed by the identification of `Spec A` with the closed subspace. -/
theorem specialMap_arrow_eq :
    specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x hx =
      chartStructureMap x hx ≫
        (rangeSpaceIso B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1).hom :=
  (Category.assoc _ _ _).symm

/-- **(G1) at a chart: the cotangent complex of the extension problem of a thickening is
`L_{X/A}`.** The morphism of ringed topoi of the extension problem of `X → Spec A ⊂ Spec A'`,
transported to the model of the small étale site of `X`, is that of
`X → Spec A ≅ (Spec A ⊂ Spec A')` (`specialMap_arrow_eq`); its cotangent complex is that of
`X → Spec A`, the two targets being identified by `AlgebraicGeometry.Space.rangeSpaceIso`. This
is the comparison along which the obstruction class of [Stacks, Tag 08V5] of the problem lands in
`Ext²_{𝒪_X}(L_{X/A}, −)`. -/
noncomputable def chartCotangentComplexIso [HasDerivedCategory.{t} (modelModules x.obj.obj.left)] :
    (modelRingedToposHom (chartStructureMap x hx ≫
        (rangeSpaceIso B S hS D.arrow
          (isSquareZeroClosedImmersion_arrow D).1).hom)).cotangentComplexDerived ≅
      (modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived :=
  modelCotangentComplexIsoOfCompIso (chartStructureMap x hx)
    (rangeSpaceIso B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1)

/-- **Lifts of `x` are solutions of the extension problem of [Stacks, Section 08V3].** For an
object `x = (X → Spec A)` of `Spaces'_{fp, flat, proper}` and a square-zero thickening `A' → A`
of Situation 07YX, `x` lifts to `Spec A'` exactly when the extension problem on the small étale
site of `X` attached to `X → Spec A ⊂ Spec A'` — the inverse image of
`0 → 𝒞 → 𝒪_{Spec A'} → 𝒪_{Spec A} → 0` with prescribed module `f^*𝒞` — has a solution.

A lift is a flat deformation
(`AlgebraicGeometry.Space.ProperFlatLift.liftClassesEquivDeformationClasses`,
via [Stacks, Tag 0CG6]) and a flat deformation is a solution
(`AlgebraicGeometry.Space.FlatThickeningDeformation.classesEquiv`, [Stacks, Tag 0D17]). -/
theorem nonempty_lift_iff_nonempty_solution :
    Nonempty ((Under.post (cartesianProperFlatProjection B S hS)).Fiber
        (Under.mk (eqToHom hx ≫ D.arrow))) ↔
      Nonempty (FlatThickeningDeformation.problem
        (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x hx)
        (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow
          (isSquareZeroClosedImmersion_arrow D))).CompatibleFirstOrderThickening := by
  have e₁ := liftClassesEquivDeformationClasses (i := D.arrow) (x := x) (hx := hx)
    (isSquareZeroClosedImmersion_arrow D)
  have e₂ := FlatThickeningDeformation.classesEquiv
    (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow
      (isSquareZeroClosedImmersion_arrow D))
    (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x hx)
    (isFlat_specialMap_arrow x hx D)
  exact (nonempty_quotient_iff _).symm.trans
    ((e₁.trans e₂).nonempty_congr.trans (nonempty_quotient_iff _))

end AlgebraicGeometry.Space.ProperFlatLift

end
