module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.PullbackModuleFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsAlongIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction

/-!
# An ideal read on the smaller site

Let `Φ : Sh(D, K) ⥤ Sh(C, J)` be a fully faithful, finite-product-preserving functor between
categories of sheaves of sets, let `α : Λ ⟶ Q` be a morphism of sheaves of rings on `(D, K)`,
and let `η : R ⟶ Φ_*Λ` be an **isomorphism** of sheaves of rings on `(C, J)`, where `Φ_*Λ` is
the transport `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` of `Λ` along `Φ`. Write
`σ : R ⟶ Φ_*Q` for the composite of `η` with the transport of `α`.

Transport along `Φ`, followed by restriction of scalars along `η`, is a fully faithful functor

`𝒯 : Mod(Λ) ⥤ Mod(R)`,

and the composite `Mod(Q) ⟶ Mod(Λ) ⟶ Mod(R)`, restriction of scalars along `α` followed by
`𝒯`, is the direct image of modules in its inverse-image presentation. Given a sheaf of
`Q`-modules `N` and an isomorphism

`μ : ker(σ) ≅ 𝒯((restrictScalars α).obj N)`

identifying the kernel ideal of `σ` — an ideal of `R` — with the direct image of `N`, the
module `N` itself is an ideal of `Λ`: there is a morphism `ι : (restrictScalars α).obj N ⟶ Λ`
of sheaves of `Λ`-modules which is injective on sections, whose image over every object of the
smaller site is exactly the kernel of `α`, and whose image has square zero.

## Main definitions

* `Stacks.SheafOfModules.IdealTransport.transport`: the functor `𝒯` above.
* `Stacks.SheafOfModules.IdealTransport.fullyFaithfulTransport`: it is fully faithful.
* `Stacks.SheafOfModules.IdealTransport.structureSharpModuleMap`: the morphism of
  `R`-modules `R ⟶ 𝒯((restrictScalars α).obj Q)` whose sections are `σ`.
* `Stacks.SheafOfModules.IdealTransport.idealι`: the inclusion `ι : N ⟶ Λ`, the preimage under
  `𝒯` of the inclusion `ker(σ) ⟶ R`.
* `Stacks.SheafOfModules.IdealTransport.idealKernelSection` and
  `Stacks.SheafOfModules.IdealTransport.idealKernelIso`: the inverse of the factorization of
  `ι` through `ker(α)`, and the resulting isomorphism `N ≅ ker(α)`.

## Main results

* `Stacks.SheafOfModules.IdealTransport.structureSharpModuleMap_val_app_apply`: the sections of
  `structureSharpModuleMap` are those of `σ`.
* `Stacks.SheafOfModules.IdealTransport.idealι_comp_eq_zero` and
  `Stacks.SheafOfModules.IdealTransport.app_idealι_eq_zero`: the inclusion lands in the kernel of
  `α`, globally and on sections.
* `Stacks.SheafOfModules.IdealTransport.idealι_injective`: it is injective on sections.
* `Stacks.SheafOfModules.IdealTransport.exists_idealι_eq`: every section of `Λ` killed by `α`
  is in its image.
* `Stacks.SheafOfModules.IdealTransport.mul_eq_zero_of_app_eq_zero` and
  `Stacks.SheafOfModules.IdealTransport.mul_app_idealι_eq_zero`: the kernel of `α` has square
  zero, stated of two sections it kills and of two sections in the image of `ι`.
* `Stacks.SheafOfModules.IdealTransport.idealKernelIso_hom_comp_ι`: the isomorphism
  `N ≅ ker(α)` composed with the inclusion of the kernel is `ι`.

## Implementation notes

The transport of `(restrictScalars α).obj (unit Q)` along `Φ` and the restriction of scalars of
`unit (Φ_*Q)` along `σ` are modules over `R` with the same underlying sheaf of sets, but they
are not the same object: their scalar actions agree only through the product comparison of `Φ`.
So `structureSharpModuleMap` is defined as the first composite, and its sections are identified
definitionally with those of `σ`.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3), the kernel ideal of a
  closed immersion of topoi.
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ), part (3).
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930), restriction of scalars
  along a surjection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

namespace Stacks.SheafOfModules.IdealTransport

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {R : Sheaf J RingCat.{ww}} {Λ Q : Sheaf K RingCat.{ww'}}
  (α : Λ ⟶ Q) (η : R ⟶ pullbackRingSheaf J Φ Λ)

/-! ### The direct image in its inverse-image presentation -/

/-- Transport of sheaves of `Λ`-modules along `Φ`, read as sheaves of `R`-modules through
`η : R ⟶ Φ_*Λ`. -/
abbrev transport : _root_.SheafOfModules.{ww'} Λ ⥤ _root_.SheafOfModules.{ww} R :=
  pullbackModuleFunctor J Φ Λ ⋙ _root_.SheafOfModules.restrictScalars η

/-- Transport is additive. -/
instance additive_transport : (transport J Φ η).Additive := inferInstance

/-- **Transport is fully faithful** when `Φ` is and `η` is an isomorphism. -/
def fullyFaithfulTransport [Φ.Full] [Φ.Faithful] [IsIso η] :
    (transport J Φ η).FullyFaithful :=
  (fullyFaithfulPullbackModuleFunctor Φ Λ).comp (ChangeOfRings.fullyFaithfulOfIsIso η)

/-- **The structure sheaf of the larger site is the transport of the structure sheaf of the
smaller one**, as a module over itself, when `η` is an isomorphism. -/
def unitTransportIso [IsIso η] :
    _root_.SheafOfModules.unit R ≅ (transport J Φ η).obj (_root_.SheafOfModules.unit Λ) :=
  ChangeOfRings.unitRestrictScalarsIso η

/-! ### The structure map as a morphism of modules -/

/-- The morphism of sheaves of `R`-modules `R ⟶ 𝒯((restrictScalars α).obj Q)` whose sections
are those of `σ = η ≫ Φ_*α`: the isomorphism `R ≅ 𝒯 Λ` followed by the transport of `α`, read
as a morphism of modules. -/
def structureSharpModuleMap [IsIso η] :
    _root_.SheafOfModules.unit R ⟶
      (transport J Φ η).obj ((_root_.SheafOfModules.restrictScalars α).obj
        (_root_.SheafOfModules.unit Q)) :=
  (unitTransportIso J Φ η).hom ≫
    (transport J Φ η).map (_root_.SheafOfModules.unitToRestrictScalarsObjUnit α)

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- The defining equation of `Stacks.SheafOfModules.IdealTransport.structureSharpModuleMap`. -/
theorem structureSharpModuleMap_eq [IsIso η] :
    structureSharpModuleMap J Φ α η =
      (unitTransportIso J Φ η).hom ≫
        (transport J Φ η).map (_root_.SheafOfModules.unitToRestrictScalarsObjUnit α) :=
  rfl

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- **The sections of `structureSharpModuleMap` are those of `σ = η ≫ Φ_*α`.** -/
theorem structureSharpModuleMap_val_app_apply [IsIso η] (V : Cᵒᵖ) (a : R.obj.obj V) :
    (structureSharpModuleMap J Φ α η).val.app V a =
      ((η ≫ pullbackRingSheafMap J Φ α).hom.app V) a :=
  rfl

/-- Equal morphisms of sheaves of modules agree on sections. -/
private theorem val_app_apply_congr {X : Type*} [Category X] {T : GrothendieckTopology X}
    {S : Sheaf T RingCat} {A B : _root_.SheafOfModules S} {f g : A ⟶ B} (h : f = g)
    (V : Xᵒᵖ) (x : A.val.obj V) : f.val.app V x = g.val.app V x := by
  rw [h]

omit [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww'})] in
/-- The inclusion of the kernel ideal of a morphism of sheaves of rings is killed by that
morphism read as a morphism of modules. -/
theorem kerIdeal_ι_comp_unitToRestrictScalarsObjUnit :
    (_root_.SheafOfModules.kerIdeal α).ι ≫
        _root_.SheafOfModules.unitToRestrictScalarsObjUnit α = 0 :=
  _root_.SheafOfModules.kerIota_comp (_root_.SheafOfModules.unitToRestrictScalarsObjUnit α)

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- The inclusion of the kernel ideal of `α`, transported and read in `R`, is killed by the
morphism `structureSharpModuleMap`. -/
theorem transport_kerIdeal_ι_comp [IsIso η] :
    ((transport J Φ η).map (_root_.SheafOfModules.kerIdeal α).ι ≫
          (unitTransportIso J Φ η).inv) ≫
        structureSharpModuleMap J Φ α η = 0 := by
  rw [structureSharpModuleMap_eq, Category.assoc, Iso.inv_hom_id_assoc,
    ← (transport J Φ η).map_comp, kerIdeal_ι_comp_unitToRestrictScalarsObjUnit α,
    (transport J Φ η).map_zero]

variable (σ : R ⟶ pullbackRingSheaf J Φ Q)

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- The sections of `structureSharpModuleMap` are those of any `σ` the composite
`η ≫ Φ_*α` is equal to. -/
theorem structureSharpModuleMap_val_app_apply_of_eq [IsIso η]
    (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) (V : Cᵒᵖ) (a : R.obj.obj V) :
    (structureSharpModuleMap J Φ α η).val.app V a = (σ.hom.app V) a :=
  (structureSharpModuleMap_val_app_apply J Φ α η V a).trans
    (ConcreteCategory.congr_hom
      (congrArg (fun m : R ⟶ pullbackRingSheaf J Φ Q ↦ m.hom.app V) hσ) a)

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- A section of `R` lies in the kernel ideal of `σ` exactly when `structureSharpModuleMap`
kills it. -/
theorem mem_kerIdeal_iff [IsIso η] (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) (V : Cᵒᵖ)
    (a : R.obj.obj V) :
    a ∈ (_root_.SheafOfModules.kerIdeal σ).obj V ↔
      (structureSharpModuleMap J Φ α η).val.app V a = 0 := by
  rw [structureSharpModuleMap_val_app_apply_of_eq J Φ α η σ hσ V a]
  exact (_root_.SheafOfModules.mem_kerIdeal σ V a).trans RingHom.mem_ker

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- The inclusion of the kernel ideal of `σ` into `R` is killed by
`structureSharpModuleMap`. -/
theorem kerIdeal_ι_comp_structureSharpModuleMap [IsIso η]
    (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    (_root_.SheafOfModules.kerIdeal σ).ι ≫ structureSharpModuleMap J Φ α η = 0 :=
  _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext fun z ↦
      (mem_kerIdeal_iff J Φ α η σ hσ V z.1).1 z.2))

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- The transported inclusion of the kernel ideal of `α`, read in `R`, has its sections in the
kernel ideal of `σ`. -/
theorem transport_kerIdeal_ι_mem [IsIso η] (hσ : η ≫ pullbackRingSheafMap J Φ α = σ)
    (V : Cᵒᵖ)
    (m : ((transport J Φ η).obj
      (_root_.SheafOfModules.kerIdeal α).toSheafOfModules).val.obj V) :
    ((transport J Φ η).map (_root_.SheafOfModules.kerIdeal α).ι ≫
        (unitTransportIso J Φ η).inv).val.app V m ∈
      (_root_.SheafOfModules.kerIdeal σ).obj V :=
  (mem_kerIdeal_iff J Φ α η σ hσ V _).2
    (val_app_apply_congr (transport_kerIdeal_ι_comp J Φ α η) V m)

/-! ### The ideal read on the smaller site -/

variable {N : _root_.SheafOfModules.{ww'} Q}
  (μ : (_root_.SheafOfModules.kerIdeal σ).toSheafOfModules ≅
    (transport J Φ η).obj ((_root_.SheafOfModules.restrictScalars α).obj N))

section Ideal

variable [Φ.Full] [Φ.Faithful] [hηiso : IsIso η]

include μ

/-- The inclusion of the kernel ideal of `σ` into `R`, read through the identification `μ` of
that ideal with the transport of `N`. -/
def transportedIdealι :
    (transport J Φ η).obj ((_root_.SheafOfModules.restrictScalars α).obj N) ⟶
      (transport J Φ η).obj (_root_.SheafOfModules.unit Λ) :=
  μ.inv ≫ (_root_.SheafOfModules.kerIdeal σ).ι ≫ (unitTransportIso J Φ η).hom

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] [Φ.Full] [Φ.Faithful] in
/-- The defining equation of `Stacks.SheafOfModules.IdealTransport.transportedIdealι`. -/
theorem transportedIdealι_eq :
    transportedIdealι J Φ α η σ μ =
      μ.inv ≫ (_root_.SheafOfModules.kerIdeal σ).ι ≫ (unitTransportIso J Φ η).hom :=
  rfl

/-- **The inclusion `ι : N ⟶ Λ` of the ideal read on the smaller site**: the morphism of sheaves
of `Λ`-modules whose transport is the inclusion of the kernel ideal of `σ` into `R`, read
through `μ` and the isomorphism `R ≅ 𝒯 Λ`. -/
def idealι : (_root_.SheafOfModules.restrictScalars α).obj N ⟶ _root_.SheafOfModules.unit Λ :=
  (fullyFaithfulTransport J Φ η).preimage (transportedIdealι J Φ α η σ μ)

/-- The defining property of `Stacks.SheafOfModules.IdealTransport.idealι`: its transport is the
inclusion of the kernel ideal of `σ`, read through `μ`. -/
theorem map_idealι :
    (transport J Φ η).map (idealι J Φ α η σ μ) = transportedIdealι J Φ α η σ μ :=
  (fullyFaithfulTransport J Φ η).map_preimage _

/-- **The transport of the inclusion `ι`, on sections over an object of the larger site, is `η`
of a section of `R` killed by `σ`.** -/
theorem exists_mem_kerIdeal_map_idealι_val_app (V : Cᵒᵖ)
    (t : ((transport J Φ η).obj
      ((_root_.SheafOfModules.restrictScalars α).obj N)).val.obj V) :
    ∃ r : R.obj.obj V, (σ.hom.app V) r = 0 ∧
      ((transport J Φ η).map (idealι J Φ α η σ μ)).val.app V t = (η.hom.app V) r := by
  refine ⟨(μ.inv.val.app V t).1, ?_, ?_⟩
  · exact RingHom.mem_ker.1
      ((_root_.SheafOfModules.mem_kerIdeal σ V _).1 (μ.inv.val.app V t).2)
  · exact val_app_apply_congr
      ((map_idealι J Φ α η σ μ).trans (transportedIdealι_eq J Φ α η σ μ)) V t

/-- **The inclusion lands in the kernel of `α`.** -/
theorem idealι_comp_eq_zero (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    idealι J Φ α η σ μ ≫ _root_.SheafOfModules.unitToRestrictScalarsObjUnit α = 0 := by
  refine (fullyFaithfulTransport J Φ η).map_injective ?_
  rw [(transport J Φ η).map_comp, map_idealι, (transport J Φ η).map_zero,
    transportedIdealι_eq, Category.assoc, Category.assoc,
    ← structureSharpModuleMap_eq J Φ α η,
    kerIdeal_ι_comp_structureSharpModuleMap J Φ α η σ hσ, Limits.comp_zero]

/-- **The inclusion lands in the kernel of `α`**, on sections. -/
theorem app_idealι_eq_zero (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) (V : Dᵒᵖ)
    (m : ((_root_.SheafOfModules.restrictScalars α).obj N).val.obj V) :
    (α.hom.app V) ((idealι J Φ α η σ μ).val.app V m) = 0 :=
  val_app_apply_congr (idealι_comp_eq_zero J Φ α η σ μ hσ) V m

/-- The factorization of the inclusion through the kernel ideal of `α`. -/
def idealKernelLift (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    (_root_.SheafOfModules.restrictScalars α).obj N ⟶
      (_root_.SheafOfModules.kerIdeal α).toSheafOfModules :=
  _root_.SheafOfModules.kerLift (idealι J Φ α η σ μ) (idealι_comp_eq_zero J Φ α η σ μ hσ)

/-- The factorization through the kernel ideal of `α`, composed with the inclusion of that
kernel ideal, is `ι`. -/
theorem idealKernelLift_comp (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    idealKernelLift J Φ α η σ μ hσ ≫ (_root_.SheafOfModules.kerIdeal α).ι =
      idealι J Φ α η σ μ :=
  _root_.SheafOfModules.kerLift_comp _ _

/-- **The inverse of the factorization through the kernel ideal of `α`.** -/
def idealKernelSection (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    (_root_.SheafOfModules.kerIdeal α).toSheafOfModules ⟶
      (_root_.SheafOfModules.restrictScalars α).obj N :=
  (fullyFaithfulTransport J Φ η).preimage
    (Stacks.SheafOfModules.sheafFactorThruSubmodule
        ((transport J Φ η).map (_root_.SheafOfModules.kerIdeal α).ι ≫
          (unitTransportIso J Φ η).inv)
        (_root_.SheafOfModules.kerIdeal σ)
        (transport_kerIdeal_ι_mem J Φ α η σ hσ) ≫
      μ.hom)

/-- The defining equation of `Stacks.SheafOfModules.IdealTransport.idealKernelSection`. -/
theorem idealKernelSection_eq (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    idealKernelSection J Φ α η σ μ hσ =
      (fullyFaithfulTransport J Φ η).preimage
        (Stacks.SheafOfModules.sheafFactorThruSubmodule
            ((transport J Φ η).map (_root_.SheafOfModules.kerIdeal α).ι ≫
              (unitTransportIso J Φ η).inv)
            (_root_.SheafOfModules.kerIdeal σ)
            (transport_kerIdeal_ι_mem J Φ α η σ hσ) ≫
          μ.hom) :=
  rfl

/-- `Stacks.SheafOfModules.IdealTransport.idealKernelSection` composed with the inclusion `ι` is
the inclusion of the kernel ideal of `α`. -/
theorem idealKernelSection_comp_idealι (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    idealKernelSection J Φ α η σ μ hσ ≫ idealι J Φ α η σ μ =
      (_root_.SheafOfModules.kerIdeal α).ι := by
  refine (fullyFaithfulTransport J Φ η).map_injective ?_
  rw [(transport J Φ η).map_comp, map_idealι, idealKernelSection_eq,
    (fullyFaithfulTransport J Φ η).map_preimage, transportedIdealι_eq, Category.assoc,
    Iso.hom_inv_id_assoc, ← Category.assoc,
    Stacks.SheafOfModules.sheafFactorThruSubmodule_ι, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Every section of `Λ` killed by `α` is in the image of the inclusion.** -/
theorem exists_idealι_eq (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) (V : Dᵒᵖ) (s : Λ.obj.obj V)
    (hs : (α.hom.app V) s = 0) :
    ∃ m : ((_root_.SheafOfModules.restrictScalars α).obj N).val.obj V,
      (idealι J Φ α η σ μ).val.app V m = s :=
  ⟨(idealKernelSection J Φ α η σ μ hσ).val.app V
      ⟨s, (_root_.SheafOfModules.mem_kerIdeal α V s).2 (RingHom.mem_ker.2 hs)⟩,
    val_app_apply_congr (idealKernelSection_comp_idealι J Φ α η σ μ hσ) V _⟩

/-- The inclusion `ι` is a monomorphism. -/
theorem mono_idealι : Mono (idealι J Φ α η σ μ) := by
  have := (fullyFaithfulTransport J Φ η).faithful
  have : Mono ((transport J Φ η).map (idealι J Φ α η σ μ)) := by
    rw [map_idealι, transportedIdealι_eq]
    exact mono_comp _ _
  exact (transport J Φ η).mono_of_mono_map inferInstance

/-- **The inclusion `ι` is injective on sections.** -/
theorem idealι_injective (V : Dᵒᵖ) :
    Function.Injective ((idealι J Φ α η σ μ).val.app V) := by
  have := mono_idealι J Φ α η σ μ
  have h0 : (_root_.SheafOfModules.kerSubmodule (idealι J Φ α η σ μ)).ι ≫
      idealι J Φ α η σ μ = 0 :=
    _root_.SheafOfModules.kerIota_comp (idealι J Φ α η σ μ)
  have hker : (_root_.SheafOfModules.kerSubmodule (idealι J Φ α η σ μ)).ι = 0 :=
    (cancel_mono (idealι J Φ α η σ μ)).1 (h0.trans Limits.zero_comp.symm)
  intro x y hxy
  have hzero : (idealι J Φ α η σ μ).val.app V (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmem : (x - y) ∈ (_root_.SheafOfModules.kerSubmodule (idealι J Φ α η σ μ)).obj V :=
    (_root_.SheafOfModules.mem_kerSubmodule (idealι J Φ α η σ μ) V (x - y)).2 hzero
  exact sub_eq_zero.1 (val_app_apply_congr hker V ⟨x - y, hmem⟩)

/-- **The isomorphism `N ≅ ker(α)`**, given by the factorization of `ι` through the kernel ideal
of `α`. -/
def idealKernelIso (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    (_root_.SheafOfModules.restrictScalars α).obj N ≅
      (_root_.SheafOfModules.kerIdeal α).toSheafOfModules where
  hom := idealKernelLift J Φ α η σ μ hσ
  inv := idealKernelSection J Φ α η σ μ hσ
  hom_inv_id := by
    have := mono_idealι J Φ α η σ μ
    refine (cancel_mono (idealι J Φ α η σ μ)).1 ?_
    rw [Category.assoc, idealKernelSection_comp_idealι, idealKernelLift_comp,
      Category.id_comp]
  inv_hom_id := by
    refine (cancel_mono (_root_.SheafOfModules.kerIdeal α).ι).1 ?_
    rw [Category.assoc, idealKernelLift_comp, idealKernelSection_comp_idealι,
      Category.id_comp]

/-- The isomorphism `N ≅ ker(α)` composed with the inclusion of the kernel ideal is the
inclusion `ι`. -/
theorem idealKernelIso_hom_comp_ι (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) :
    (idealKernelIso J Φ α η σ μ hσ).hom ≫ (_root_.SheafOfModules.kerIdeal α).ι =
      idealι J Φ α η σ μ :=
  idealKernelLift_comp J Φ α η σ μ hσ

/-- **The kernel of `α` has square zero**: two sections of `Λ` over the same object which `α`
kills have vanishing product. -/
theorem mul_eq_zero_of_app_eq_zero (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) (V : Dᵒᵖ)
    (m m' : Λ.obj.obj V) (hm : (α.hom.app V) m = 0) (hm' : (α.hom.app V) m' = 0) :
    m * m' = 0 := by
  obtain ⟨y, hy⟩ := exists_idealι_eq J Φ α η σ μ hσ V m' hm'
  have hact : m • y =
      (ConcreteCategory.hom (α.hom.app V)) m • (show N.val.obj V from y) := rfl
  have hsmul : m • y = 0 := by
    rw [hact, hm, zero_smul]
    rfl
  have hlin : (idealι J Φ α η σ μ).val.app V (m • y) =
      m • (idealι J Φ α η σ μ).val.app V y :=
    ((idealι J Φ α η σ μ).val.app V).hom.map_smul m y
  have key : (idealι J Φ α η σ μ).val.app V (m • y) = 0 := by rw [hsmul, map_zero]
  rw [hlin, hy] at key
  exact key

/-- **The image of the inclusion has square zero**: the product of two sections of `Λ` in the
image of `ι` vanishes. -/
theorem mul_app_idealι_eq_zero (hσ : η ≫ pullbackRingSheafMap J Φ α = σ) (V : Dᵒᵖ)
    (m m' : ((_root_.SheafOfModules.restrictScalars α).obj N).val.obj V) :
    (show ToType (Λ.obj.obj V) from (idealι J Φ α η σ μ).val.app V m) *
        (show ToType (Λ.obj.obj V) from (idealι J Φ α η σ μ).val.app V m') = 0 :=
  mul_eq_zero_of_app_eq_zero J Φ α η σ μ hσ V _ _
    (app_idealι_eq_zero J Φ α η σ μ hσ V m) (app_idealι_eq_zero J Φ α η σ μ hσ V m')

end Ideal

end Stacks.SheafOfModules.IdealTransport

end
