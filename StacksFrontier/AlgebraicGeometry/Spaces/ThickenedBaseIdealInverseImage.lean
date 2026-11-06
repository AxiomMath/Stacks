module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBasePushoutQcqs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposSheafSetsFibreSquare
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The base ideal of a problem over a thickened base, as an inverse image

Let `f : X ⟶ D` be a morphism of algebraic spaces and `i : D ⟶ D'` a closed immersion with
quasi-coherent ideal `𝓘 = Ker(𝒪_{D'} ⟶ i_*𝒪_D)`. For a square-zero extension problem over `f`
whose thickened base is identified with `i⁻¹𝒪_{D'}`, the base ideal
`f⁻¹𝒥 = Ker(f⁻¹𝒪_{D'} ⟶ f⁻¹𝒪_D)` is, section by section, the image of the inverse image
`(f ≫ i)⁻¹𝓘` of the quasi-coherent ideal `𝓘`; the inverse image of sheaves is left exact. This is
what the source's proof of [Stacks Project, Tag 0D3Q] leaves tacit: post-composition with
`φ : ℱ ⟶ 𝒢` is injective on the maps `f⁻¹𝒥 ⟶ ℱ` when `DQ_X(ℱ) ⟶ DQ_X(𝒢)` is an isomorphism,
because those maps are maps out of `(f ≫ i)^*𝓘`, which is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.isPullback_kernelIdealSheaf`: `𝓘` is the kernel of `𝒪_{D'} ⟶ i_*𝒪_D`
  as a pullback square of sheaves of sets.

## References

* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor pushforwardCommRingFunctor)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] HasDerivedCategory.standard

/-- The inverse image of a morphism of topoi preserves finite products, read off directly from
its left exactness (instance search through the presheaf limits times out). -/
local instance (priority := high) preservesFiniteProducts_inverseImage_thickenedBaseIdeal
    {E : Type*} [Category E] {F : Type*} [Category F] (g : MorphismOfTopoi E F) :
    PreservesFiniteProducts g.inverseImage :=
  ⟨fun n ↦ g.preservesFiniteLimits.preservesFiniteLimits (Discrete (Fin n))⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X D D' : AlgebraicSpaces B S hS} (f : X ⟶ D) (i : D ⟶ D')

/-- **The kernel ideal of a morphism is the kernel of its structure map**, as a pullback square of
sheaves of sets: the ideal is the fibre of `i♯ : 𝒪_{D'} ⟶ i_*𝒪_D` over the zero section. -/
theorem isPullback_kernelIdealSheaf :
    IsPullback ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS D')).map
        (kernelIdealSheaf B S hS i).ι) (terminal.from _)
      ((sheafCompose (SmallEtale.topology B S hS D'.1) (forget RingCat.{u})).map
        (structureSharp B S hS i))
      (Sheaf.ringZeroHom _) := by
  refine Stacks.Sheaves.ToposPullback.isPullback_terminal_of_sections _ _ _ ?_
    (fun U b b' h => Subtype.ext h) fun U a ha => ⟨⟨a, ha⟩, rfl⟩
  refine Sheaf.hom_ext_sections fun U b => ?_
  rw [(Sheaf.sectionsFunctor _ U).map_comp_apply]
  exact b.2

/-- The counit of the inverse image and direct image of sheaves of commutative rings along a
closed immersion is an isomorphism: the direct image of sheaves of sets is fully faithful. -/
theorem isIso_commRingImageAdjunction_counit (hi : IsClosedImmersion B S hS i.hom)
    (O : Sheaf (SmallEtale.topology B S hS D.1) CommRingCat.{u}) :
    IsIso ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
      (smallEtaleRingedToposHom B S hS i).toToposHom).counit.app O) := by
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi
  have : (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward.Full := hff.full
  have : (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward.Faithful := hff.faithful
  have : IsIso ((sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map
      ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS i).toToposHom).counit.app O)) := by
    have e := Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_counit_forget
      (smallEtaleRingedToposHom B S hS i).toToposHom O
    have h : IsIso ((smallEtaleRingedToposHom B S hS i).toToposHom.adj.counit.app
        ((sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).obj O)) :=
      inferInstance
    exact (congrArg IsIso e).mpr h
  exact isIso_of_reflects_iso _ (sheafCompose (SmallEtale.topology B S hS D.1)
    (forget CommRingCat.{u}))

/-- **The reduction of the thickened base, read on `X`, factors through the inverse image of
`i♯ : 𝒪_{D'} ⟶ i_*𝒪_D` along `f ≫ i`**, followed by the comparison
`(f ≫ i)⁻¹i_*𝒪_D ≅ f⁻¹i⁻¹i_*𝒪_D` and the inverse image of the counit `i⁻¹i_*𝒪_D ⟶ 𝒪_D`. -/
theorem thickenedBaseIso_hom_comp_map {𝒜 : Sheaf (SmallEtale.topology B S hS D.1) CommRingCat.{u}}
    (e : 𝒜 ≅ (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O)
    (r : 𝒜 ⟶ (smallEtaleRingedTopos B S hS D).O)
    (hr : e.hom ≫ (smallEtaleRingedToposHom B S hS i).fSharpInverseImage = r) :
    (thickenedBaseIso B S hS f i e).hom ≫ (smallEtaleInverseImageRing B S hS f).map r =
      (smallEtaleInverseImageRing B S hS (f ≫ i)).map (smallEtaleRingedToposHom B S hS i).fSharp ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS f i).inv.app _ ≫
        (smallEtaleInverseImageRing B S hS f).map
          ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
            (smallEtaleRingedToposHom B S hS i).toToposHom).counit.app
              (smallEtaleRingedTopos B S hS D).O) := by
  have hr' : e.inv ≫ r = (smallEtaleRingedToposHom B S hS i).fSharpInverseImage := by
    rw [← hr, Iso.inv_hom_id_assoc]
  have hs : (smallEtaleRingedToposHom B S hS i).fSharpInverseImage =
      (smallEtaleInverseImageRing B S hS i).map (smallEtaleRingedToposHom B S hS i).fSharp ≫
        (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
          (smallEtaleRingedToposHom B S hS i).toToposHom).counit.app
            (smallEtaleRingedTopos B S hS D).O :=
    Adjunction.homEquiv_counit _ _ _ _
  let c := smallEtaleRingedToposHom_compInverseImageRingIso B S hS f i
  let F := smallEtaleInverseImageRing B S hS f
  have hn := c.inv.naturality (smallEtaleRingedToposHom B S hS i).fSharp
  refine (Category.assoc (c.inv.app _) (F.map e.inv) (F.map r)).trans ?_
  refine (congrArg (c.inv.app _ ≫ ·) ((F.map_comp e.inv r).symm.trans
    ((congrArg F.map (hr'.trans hs)).trans (F.map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ F.map ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
    (smallEtaleRingedToposHom B S hS i).toToposHom).counit.app
      (smallEtaleRingedTopos B S hS D).O)) hn.symm).trans ?_
  exact Category.assoc _ _ _

/-- `𝓘` is quasi-coherent for a closed immersion: [Stacks Project, Tag 03MB], part (1). -/
theorem isQuasicoherentOnSite_kernelIdealModule (hi : IsClosedImmersion B S hS i.hom) :
    (kernelIdealModule B S hS i).IsQuasicoherentOnSite := by
  have h := ((closedImmersion_quasicoherentIdeal_correspondence B S hS D').1 i hi).2.2.2
  rwa [ker_pushforwardStructureProjection] at h

/-- **The inverse image `(f ≫ i)⁻¹𝓘` of the ideal of `D` in `D'`**, a module over
`(f ≫ i)⁻¹𝒪_{D'}`. -/
abbrev compInverseImageKernelIdeal :=
  (Stacks.Sheaves.RingedToposModules.inverseImageModules
    (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D').O)).obj
      (kernelIdealModule B S hS i)

/-- The inverse image of the inclusion `𝓘 ⟶ 𝒪_{D'}`, into `(f ≫ i)⁻¹𝒪_{D'}`. -/
def compInverseImageKernelIdealι :
    compInverseImageKernelIdeal B S hS f i ⟶ SheafOfModules.unit
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D').O)) :=
  (Stacks.Sheaves.RingedToposModules.inverseImageModules
      (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D').O)).map
        (kernelIdealSheaf B S hS i).ι ≫
    (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D').O)).inv

/-- The inverse image of the inclusion of `𝓘`, on sections: the inverse image of the inclusion of
sheaves of sets. -/
theorem compInverseImageKernelIdealι_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : (compInverseImageKernelIdeal B S hS f i).val.obj U) :
    (compInverseImageKernelIdealι B S hS f i).val.app U m =
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        ((smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS D')).map
            (kernelIdealSheaf B S hS i).ι)) m :=
  rfl

/-- The inverse image of `i♯ : 𝒪_{D'} ⟶ i_*𝒪_D` along `f ≫ i`. -/
abbrev inverseImageStructureSharp :=
  (smallEtaleInverseImageRing B S hS (f ≫ i)).map (smallEtaleRingedToposHom B S hS i).fSharp

/-- On sections, `inverseImageStructureSharp` is the map of underlying sheaves of
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMap` applied to `i♯` along `f ≫ i`. -/
theorem inverseImageStructureSharp_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
      (smallEtaleRingedTopos B S hS D').O).obj.obj U) :
    (inverseImageStructureSharp B S hS f i).hom.app U a =
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
          (Stacks.Sheaves.ToposPullback.pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
            (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage
            (structureSharp B S hS i))) a := by
  have e1 := congrArg (fun m => (Sheaf.sectionsFunctor _ U).map m a)
    (Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
      (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage
      (smallEtaleRingedToposHom B S hS i).fSharp)
  have e2 := congrArg (fun m => (Sheaf.sectionsFunctor _ U).map m a)
    (Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMap
      (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage
      (structureSharp B S hS i))
  have hX : (sheafCompose (SmallEtale.topology B S hS D'.1) (forget CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS i).fSharp =
      (sheafCompose (SmallEtale.topology B S hS D'.1) (forget RingCat.{u})).map
        (structureSharp B S hS i) := by
    rw [← forgetCommRingSheaf_map_fSharp]
    exact Sheaf.hom_ext_sections fun _ _ => rfl
  have e3 := congrArg (fun m => (Sheaf.sectionsFunctor _ U).map
    ((smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage.map m) a) hX
  exact e1.trans (e3.trans e2.symm)

/-- The inverse image of `𝓘` lands in the kernel of the inverse image of `i♯`. -/
theorem inverseImageStructureSharp_ι (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : (compInverseImageKernelIdeal B S hS f i).val.obj U) :
    (inverseImageStructureSharp B S hS f i).hom.app U
      (show ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
        (smallEtaleRingedTopos B S hS D').O).obj.obj U from
          (compInverseImageKernelIdealι B S hS f i).val.app U m) = 0 := by
  refine (inverseImageStructureSharp_app B S hS f i U _).trans ?_
  exact Stacks.Sheaves.ToposPullback.sections_comp_eq_zero_of_isPullback
    (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage
    (structureSharp B S hS i) _ (isPullback_kernelIdealSheaf B S hS i) U m

/-- **Every section of `(f ≫ i)⁻¹𝒪_{D'}` killed by the inverse image of `i♯` comes from
`(f ≫ i)⁻¹𝓘`**: the inverse image is left exact. -/
theorem exists_inverseImageKernelIdealι (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
      (smallEtaleRingedTopos B S hS D').O).obj.obj U)
    (ha : (inverseImageStructureSharp B S hS f i).hom.app U a = 0) :
    ∃ m : (compInverseImageKernelIdeal B S hS f i).val.obj U,
      (show ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
        (smallEtaleRingedTopos B S hS D').O).obj.obj U from
          (compInverseImageKernelIdealι B S hS f i).val.app U m) = a := by
  have ha' := (inverseImageStructureSharp_app B S hS f i U a).symm.trans ha
  have hEU := Stacks.Sheaves.ToposPullback.existsUnique_sections_of_isPullback
    (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).toToposHom.inverseImage
    (structureSharp B S hS i) _ (isPullback_kernelIdealSheaf B S hS i) U _ ha'
  exact ⟨hEU.exists.choose, (compInverseImageKernelIdealι_app B S hS f i U _).trans
    hEU.exists.choose_spec⟩

/-- Evaluating a composite of sheaf maps on sections: if `α ≫ β = 𝟙`, then `β ∘ α = id` there. -/
private theorem sheaf_hom_app_app_of_comp_eq_id {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A B : Sheaf J CommRingCat.{u}} (α : A ⟶ B) (β : B ⟶ A)
    (h : α ≫ β = 𝟙 A) (U : Cᵒᵖ) (y : A.obj.obj U) : β.hom.app U (α.hom.app U y) = y :=
  congrArg (fun k : A ⟶ A => k.hom.app U y) h

/-- **The kernel of the reduction of the thickened base, read on `X`**, is the kernel of the
inverse image of `i♯ : 𝒪_{D'} ⟶ i_*𝒪_D` along `f ≫ i`, for a closed immersion `i`: the two maps
differ by an isomorphism. -/
theorem thickenedBaseReduction_app_eq_zero_iff (hi : IsClosedImmersion B S hS i.hom)
    {𝒜 : Sheaf (SmallEtale.topology B S hS D.1) CommRingCat.{u}}
    (e : 𝒜 ≅ (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O)
    (r : 𝒜 ⟶ (smallEtaleRingedTopos B S hS D).O)
    (hr : e.hom ≫ (smallEtaleRingedToposHom B S hS i).fSharpInverseImage = r)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
      (smallEtaleRingedTopos B S hS D').O).obj.obj U) :
    ((smallEtaleInverseImageRing B S hS f).map r).hom.app U
        ((thickenedBaseIso B S hS f i e).hom.hom.app U a) = 0 ↔
      (inverseImageStructureSharp B S hS f i).hom.app U a = 0 := by
  let ψ := (smallEtaleRingedToposHom_compInverseImageRingIso B S hS f i).inv.app
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).obj
        (smallEtaleRingedTopos B S hS D).O) ≫
    (smallEtaleInverseImageRing B S hS f).map
      ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS i).toToposHom).counit.app
          (smallEtaleRingedTopos B S hS D).O)
  have := isIso_commRingImageAdjunction_counit B S hS i hi (smallEtaleRingedTopos B S hS D).O
  have : IsIso ψ := inferInstance
  have hinv := sheaf_hom_app_app_of_comp_eq_id ψ (inv ψ) (IsIso.hom_inv_id ψ) U
  have hψ : ∀ y, ψ.hom.app U y = 0 ↔ y = 0 := fun y =>
    ⟨fun h => (hinv y).symm.trans ((congrArg _ h).trans (map_zero _)), fun h => h ▸ map_zero _⟩
  have hc := congrArg (fun k : (smallEtaleInverseImageRing B S hS (f ≫ i)).obj
      (smallEtaleRingedTopos B S hS D').O ⟶ (smallEtaleInverseImageRing B S hS f).obj
        (smallEtaleRingedTopos B S hS D).O => k.hom.app U a)
    (thickenedBaseIso_hom_comp_map B S hS f i e r hr)
  exact (Eq.congr_left hc).trans (hψ _)

open Deformation.ToposThickening in
/-- **Post-composition with `φ` is injective on the maps out of the base ideal**, for a problem
over `f : X ⟶ D` whose thickened base is `i⁻¹𝒪_{D'}` along a closed immersion `i`, when `X` is
qcqs and `DQ_X(ℱ) ⟶ DQ_X(𝒢)` is an isomorphism. The base ideal is covered by `(f ≫ i)⁻¹𝓘`, and
maps out of it are maps out of the quasi-coherent `(f ≫ i)^*𝓘`. -/
theorem baseIdeal_comp_injective_of_isIso_coherator_map (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hi : IsClosedImmersion B S hS i.hom)
    (P : RingedToposExtensionProblem (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS D))
    (hPf : P.f = smallEtaleRingedToposHom B S hS f)
    (eBase : P.baseExtension ≅
      (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O)
    (heBase : eBase.hom ≫ (smallEtaleRingedToposHom B S hS i).fSharpInverseImage =
      P.baseReduction)
    {M N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (φ : M ⟶ N)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)))
    (d₁ d₂ : P.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose
        (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          P.f.fSharpInverseImage)).obj M)
    (h : d₁ ≫ (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map P.f.fSharpInverseImage)).map φ =
        d₂ ≫ (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map P.f.fSharpInverseImage)).map φ) :
    d₁ = d₂ := by
  cases P with
  | mk Pf baseExt red hred hsq I G incl c hzero huniv =>
  subst hPf
  let P : RingedToposExtensionProblem.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS D) :=
    RingedToposExtensionProblem.mk.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS f)
      baseExt red hred hsq I G incl c hzero huniv
  set θ := thickenedBaseIso B S hS f i eBase
  have hθinv := sheaf_hom_app_app_of_comp_eq_id θ.inv θ.hom θ.inv_hom_id
  have hι : ∀ U m, ((inverseImageCommRingFunctor P.f.toToposHom).map P.baseReduction).hom.app U
      (θ.hom.hom.app U (show ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
        (smallEtaleRingedTopos B S hS D').O).obj.obj U from
          (compInverseImageKernelIdealι B S hS f i).val.app U m)) = 0 := fun U m =>
    (thickenedBaseReduction_app_eq_zero_iff B S hS f i hi eBase red heBase U _).2
      (inverseImageStructureSharp_ι B S hS f i U m)
  have hρ : ∀ U r, ((smallEtaleRingedToposModulesHom B S hS (f ≫ i)).fSharpInverseImage).hom.app
      U r = P.f.fSharpInverseImage.hom.app U
        (((inverseImageCommRingFunctor P.f.toToposHom).map P.baseReduction).hom.app U
          (θ.hom.hom.app U r)) := fun U r =>
    (congrArg (fun k : inverseImageBase B S hS (f ≫ i) ⟶ structureSheaf B S hS X.1 X.2 =>
      k.hom.app U r) (thickenedBaseIso_hom_comp B S hS f i eBase red heBase)).symm
  have hsurj : ∀ U (a : ((smallEtaleInverseImageRing B S hS f).obj baseExt).obj.obj U),
      ((smallEtaleInverseImageRing B S hS f).map red).hom.app U a = 0 →
        ∃ m : (compInverseImageKernelIdeal B S hS f i).val.obj U,
          θ.hom.hom.app U (show ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
            (smallEtaleRingedTopos B S hS D').O).obj.obj U from
              (compInverseImageKernelIdealι B S hS f i).val.app U m) = a := fun U a ha => by
    have h1 : ((smallEtaleInverseImageRing B S hS f).map red).hom.app U
        (θ.hom.hom.app U (θ.inv.hom.app U a)) = 0 :=
      (congrArg (((smallEtaleInverseImageRing B S hS f).map red).hom.app U) (hθinv U a)).trans ha
    let b : ((smallEtaleInverseImageRing B S hS (f ≫ i)).obj
      (smallEtaleRingedTopos B S hS D').O).obj.obj U := θ.inv.hom.app U a
    have h0 : (inverseImageStructureSharp B S hS f i).hom.app U b = 0 :=
      (thickenedBaseReduction_app_eq_zero_iff B S hS f i hi eBase red heBase U b).1 h1
    have hE := exists_inverseImageKernelIdealι B S hS f i U b h0
    exact ⟨hE.choose, (congrArg (θ.hom.hom.app U) hE.choose_spec).trans (hθinv U a)⟩
  refine P.idealTransfer_injective θ.hom (compInverseImageKernelIdealι B S hS f i) hι
    (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).fSharpInverseImage hρ hsurj ?_
  refine inverseImage_comp_injective_of_isIso_coherator_map B S hS (f ≫ i) hZ hXc hXs φ hDQ
    (kernelIdealModule B S hS i) (isQuasicoherentOnSite_kernelIdealModule B S hS i hi) _ _ ?_
  have key := P.idealTransfer_comp θ.hom (compInverseImageKernelIdealι B S hS f i) hι
    (smallEtaleRingedToposModulesHom B S hS (f ≫ i)).fSharpInverseImage hρ φ
  exact (key d₁).symm.trans ((congrArg _ h).trans (key d₂))

end AlgebraicGeometry.Space

end
