module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.StructureSheafLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Inverting a family of sections of the structure sheaf on a sheaf of modules

Let `X` be a ringed site, let `S` be a restriction-stable family of multiplicative subsets
`S(U) ⊆ O_X(U)`, and let `F` be a presheaf of `O_X`-modules.  Localizing each module of
sections at its multiplicative subset gives a presheaf `S⁻¹F` of `S⁻¹O_X`-modules, together
with a canonical map `F ⟶ S⁻¹F` of `O_X`-modules.

The sectionwise localization is realized as the sectionwise extension of scalars of Tag 03CU
along the canonical map `O_X ⟶ S⁻¹O_X`, that is, as the presheaf
`U ↦ S(U)⁻¹O_X(U) ⊗_{O_X(U)} F(U)`, and the canonical map as the unit of the change-of-rings
adjunction.

For a *sheaf* `F` of `O_X`-modules the sheafification `(S⁻¹F)^#` of the sectionwise
localization is then the universal sheaf of `O_X`-modules receiving `F` on which the
prescribed local sections act invertibly, and it is the extension of scalars of `F` to the
sheafified localization `(S⁻¹O_X)^#` of the structure sheaf.

## Main definitions

* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationModulePresheaf`: `S⁻¹F`,
  with `toLocalizationModulePresheaf` the canonical map `F ⟶ S⁻¹F`, read over `O_X`.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationModuleSheaf`:
  `(S⁻¹F)^#`, with `toLocalizationModuleSheaf` the canonical map `F ⟶ (S⁻¹F)^#`.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.sectionwiseLocalizationLift`: the lift
  of a map of presheaves of modules through a sectionwise localization.
* `AlgebraicGeometry.RingedSite.toModuleSheafification`: the map from a sheaf of modules to the
  sheafification of a presheaf of modules it maps to.
* `AlgebraicGeometry.RingedSite.pullbackIsoSheafification`: the pullback of sheaves of modules
  along `O_X ⟶ R` is the sheafification of a base change of presheaves of modules.

## Main results

All in the namespace `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf`:

* `algebra_eq_toAlgebra` and `isLocalization_localizationPresheaf_toAlgebra`: the algebra
  structure that the sectionwise extension of scalars tensors over is the localization algebra,
  so the ring of sections of `S⁻¹O_X` is the localization of the ring of sections of `O_X`.
* `isLocalizedModule_toLocalizationModulePresheaf`: each module of sections of `S⁻¹F` is the
  localization of the corresponding module of sections of `F`.
* `existsUnique_comp_sectionwiseLocalizationLift`: the universal property of a sectionwise
  localization of presheaves of modules.
* `existsUnique_lift_localizationModuleSheaf`: the universal property of `(S⁻¹F)^#` — a map of
  `O_X`-modules `F ⟶ G` on which each local section of `S` acts invertibly on `G` factors
  uniquely through `F ⟶ (S⁻¹F)^#`.
* `localizationModuleSheafIsoTensor` and `unit_comp_localizationModuleSheafIsoTensor`:
  `(S⁻¹F)^# = (S⁻¹O_X)^# ⊗_{O_X} F` as sheaves of `(S⁻¹O_X)^#`-modules, compatibly with the
  canonical maps out of `F`.

## References

* [Stacks Project, Section 18.44 (Tag 0EMB)](https://stacks.math.columbia.edu/tag/0EMB)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 0EMD](https://stacks.math.columbia.edu/tag/0EMD)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u v w z

namespace Stacks.PresheafOfModules.ChangeOfRings

/-- The module of sections over `U` of a presheaf of modules over the presheaf of rings
underlying a presheaf of commutative rings `O`, read as a module over the commutative ring
`O(U)` of sections. -/
instance moduleObj {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (M : PresheafOfModules.{z} (ringPresheaf O)) (U : Cᵒᵖ) : Module (O.obj U) (M.obj U) :=
  (M.obj U).isModule

end Stacks.PresheafOfModules.ChangeOfRings

namespace AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

open Stacks.PresheafOfModules.ChangeOfRings

variable {X : RingedSite.{u, v, w}} (S : MultiplicativeSubpresheaf X)

/-- The algebra structure over which the sectionwise extension of scalars along
`S.toLocalizationPresheaf` forms its tensor product is the localization algebra: the two have
the same `algebraMap`. -/
theorem algebra_eq_toAlgebra (U : X.Cᵒᵖ) :
    (inferInstance : Algebra (X.O.obj.obj U) (S.localizationPresheaf.obj U)) =
      (S.toLocalizationPresheaf.app U).hom.toAlgebra :=
  Algebra.algebra_ext _ _ fun _ ↦ rfl

/-- The ring of sections of `S⁻¹O_X` is the localization of the ring of sections of `O_X`, for
the algebra structure the sectionwise extension of scalars uses. -/
instance isLocalization_localizationPresheaf_toAlgebra (U : X.Cᵒᵖ) :
    letI := (S.toLocalizationPresheaf.app U).hom.toAlgebra
    IsLocalization (S.obj U) (S.localizationPresheaf.obj U) := by
  rw [← algebra_eq_toAlgebra S U]
  infer_instance

variable (F : PresheafOfModules.{max w z} (ringPresheaf X.O.obj))

/-- `S⁻¹F`, the presheaf of sectionwise localizations of a presheaf of `O_X`-modules: the
sectionwise extension of scalars of Tag 03CU along the canonical map `O_X ⟶ S⁻¹O_X`, whose
sections over `U` are `S(U)⁻¹O_X(U) ⊗_{O_X(U)} F(U)`. -/
def localizationModulePresheaf :
    PresheafOfModules.{max w z} (ringPresheaf S.localizationPresheaf) :=
  (changeOfRings S.toLocalizationPresheaf).obj F

/-- The canonical map `F ⟶ S⁻¹F`, read as a map of presheaves of `O_X`-modules.  It is the unit
of the change-of-rings adjunction of Tag 03CU, so on sections it is `t ↦ 1 ⊗ t`. -/
def toLocalizationModulePresheaf :
    F ⟶ (restrictScalars S.toLocalizationPresheaf).obj (S.localizationModulePresheaf F) :=
  (changeOfRingsAdjunction S.toLocalizationPresheaf).unit.app F

/-- On sections the canonical map `F ⟶ S⁻¹F` is `t ↦ 1 ⊗ t`, which is the canonical map into
the base change. -/
theorem toLocalizationModulePresheaf_app_apply (U : X.Cᵒᵖ) (t : F.obj U) :
    ((S.toLocalizationModulePresheaf F).app U).hom t =
      letI := (S.toLocalizationPresheaf.app U).hom.toAlgebra
      (1 : S.localizationPresheaf.obj U) ⊗ₜ[X.O.obj.obj U] t :=
  changeOfRingsAdjunction_unit_app_apply S.toLocalizationPresheaf F U t

/-- **Each module of sections of `S⁻¹F` is the localization of the corresponding module of
sections of `F`.** -/
theorem isLocalizedModule_toLocalizationModulePresheaf (U : X.Cᵒᵖ) :
    letI := (S.toLocalizationPresheaf.app U).hom.toAlgebra
    IsLocalizedModule (S.obj U) ((S.toLocalizationModulePresheaf F).app U).hom := by
  let := (S.toLocalizationPresheaf.app U).hom.toAlgebra
  let : Module (X.O.obj.obj U) (F.obj U) := (F.obj U).isModule
  have hmk : ((S.toLocalizationModulePresheaf F).app U).hom =
      TensorProduct.mk (X.O.obj.obj U) (S.localizationPresheaf.obj U) (F.obj U) 1 :=
    LinearMap.ext (S.toLocalizationModulePresheaf_app_apply F U)
  rw [hmk]
  exact IsLocalization.tensorProduct_isLocalizedModule (S.obj U) (S.localizationPresheaf.obj U)
    (M := F.obj U)

section SectionwiseLocalization

variable {M L N : PresheafOfModules.{max w z} (ringPresheaf X.O.obj)}

/-- The sectionwise lift of `φ` over an object, through a map `can` which is sectionwise a
localization at `S`. -/
def sectionwiseLocalizationLiftApp (can : M ⟶ L)
    (hcan : ∀ U : X.Cᵒᵖ, IsLocalizedModule (S.obj U) ((can.app U).hom)) (φ : M ⟶ N)
    (hN : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      Function.Bijective fun t : N.obj U ↦ (s : X.O.obj.obj U) • t)
    (U : X.Cᵒᵖ) : L.obj U ⟶ N.obj U :=
  letI := hcan U
  ModuleCat.ofHom (IsLocalizedModule.lift (S.obj U) ((can.app U).hom) (φ.app U).hom
    fun s ↦ (Module.End.isUnit_iff _).2 (hN U s))

/-- The sectionwise lift factors the given map over each object. -/
theorem sectionwiseLocalizationLiftApp_comp_apply (can : M ⟶ L)
    (hcan : ∀ U : X.Cᵒᵖ, IsLocalizedModule (S.obj U) ((can.app U).hom)) (φ : M ⟶ N)
    (hN : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      Function.Bijective fun t : N.obj U ↦ (s : X.O.obj.obj U) • t)
    (U : X.Cᵒᵖ) (x : M.obj U) :
    (S.sectionwiseLocalizationLiftApp can hcan φ hN U).hom ((can.app U).hom x) =
      (φ.app U).hom x := by
  let := hcan U
  exact DFunLike.congr_fun (IsLocalizedModule.lift_comp (S.obj U) ((can.app U).hom)
    (φ.app U).hom fun s ↦ (Module.End.isUnit_iff _).2 (hN U s)) x

/-- The lift of a map `φ : M ⟶ N` of presheaves of `O_X`-modules through a map `can : M ⟶ L`
which is sectionwise a localization at `S`, assuming that each prescribed local section acts
bijectively on the sections of `N`.  Over each object it is the lift given by the universal
property of a localized module. -/
@[ega "0 1.2.4" "more general"]
def sectionwiseLocalizationLift (can : M ⟶ L)
    (hcan : ∀ U : X.Cᵒᵖ, IsLocalizedModule (S.obj U) ((can.app U).hom)) (φ : M ⟶ N)
    (hN : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      Function.Bijective fun t : N.obj U ↦ (s : X.O.obj.obj U) • t) :
    L ⟶ N where
  app U := S.sectionwiseLocalizationLiftApp can hcan φ hN U
  naturality {U V} f := by
    let := hcan U
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp]
    apply IsLocalizedModule.ext (S.obj U) ((can.app U).hom)
    · exact fun s ↦ (Module.End.isUnit_iff _).2
        (hN V ⟨(X.O.obj.map f).hom s, S.map f s.2⟩)
    · ext x
      simp only [LinearMap.comp_apply]
      rw [← PresheafOfModules.naturality_apply can f x]
      exact (S.sectionwiseLocalizationLiftApp_comp_apply can hcan φ hN V
          ((M.map f).hom x)).trans
        ((PresheafOfModules.naturality_apply φ f x).trans
          (congrArg (N.map f).hom
            (S.sectionwiseLocalizationLiftApp_comp_apply can hcan φ hN U x).symm))

/-- The sectionwise lift factors the given map. -/
theorem comp_sectionwiseLocalizationLift (can : M ⟶ L)
    (hcan : ∀ U : X.Cᵒᵖ, IsLocalizedModule (S.obj U) ((can.app U).hom)) (φ : M ⟶ N)
    (hN : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      Function.Bijective fun t : N.obj U ↦ (s : X.O.obj.obj U) • t) :
    can ≫ S.sectionwiseLocalizationLift can hcan φ hN = φ := by
  refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact S.sectionwiseLocalizationLiftApp_comp_apply can hcan φ hN U x

/-- Two maps out of a sectionwise localization agree as soon as they agree after restriction
along the localization map, provided each prescribed local section acts bijectively on the
target. -/
theorem hom_ext_of_isLocalizedModule (can : M ⟶ L)
    (hcan : ∀ U : X.Cᵒᵖ, IsLocalizedModule (S.obj U) ((can.app U).hom))
    (hN : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      Function.Bijective fun t : N.obj U ↦ (s : X.O.obj.obj U) • t)
    {g h : L ⟶ N} (hgh : can ≫ g = can ≫ h) : g = h := by
  refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext ?_
  let := hcan U
  refine IsLocalizedModule.ext (S.obj U) ((can.app U).hom)
    (fun s ↦ (Module.End.isUnit_iff _).2 (hN U s)) ?_
  ext x
  simp only [LinearMap.comp_apply]
  exact congrArg (fun k : M ⟶ N ↦ (k.app U).hom x) hgh

/-- **The universal property of a sectionwise localization of presheaves of modules.**  A map
of presheaves of `O_X`-modules `φ : M ⟶ N` on which each prescribed local section of `S` acts
bijectively factors uniquely through a sectionwise localization `can : M ⟶ L` of `M` at `S`. -/
@[ega "0 1.2.4" "more general"]
theorem existsUnique_comp_sectionwiseLocalizationLift (can : M ⟶ L)
    (hcan : ∀ U : X.Cᵒᵖ, IsLocalizedModule (S.obj U) ((can.app U).hom)) (φ : M ⟶ N)
    (hN : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      Function.Bijective fun t : N.obj U ↦ (s : X.O.obj.obj U) • t) :
    ∃! m : L ⟶ N, can ≫ m = φ :=
  ⟨S.sectionwiseLocalizationLift can hcan φ hN,
    S.comp_sectionwiseLocalizationLift can hcan φ hN,
    fun _ hm ↦ S.hom_ext_of_isLocalizedModule can hcan hN
      (hm.trans (S.comp_sectionwiseLocalizationLift can hcan φ hN).symm)⟩

end SectionwiseLocalization

end AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}

section Sheafification

variable [HasWeakSheafify X.J AddCommGrpCat.{max w z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w z}]
  {F G : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {P : PresheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}

/-- The map from a sheaf of `O_X`-modules to the sheafification of a presheaf of `O_X`-modules
it maps to: the inverse of the sheafification counit, which is an isomorphism at a sheaf,
followed by the sheafification of the given map. -/
def toModuleSheafification (can : F.val ⟶ P) :
    F ⟶ (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj P :=
  inv ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app F) ≫
    (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map can

/-- The adjoint of the sheafification counit at a sheaf of modules, composed with a map of
sheaves of modules, is the underlying map of presheaves. -/
theorem homEquiv_sheafification_counit_comp (φ : F ⟶ G) :
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv F.val G
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app F ≫ φ) =
      φ.val :=
  (Equiv.eq_symm_apply _).mp
    (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.naturality φ).symm.trans
      (Adjunction.homEquiv_counit
        (PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) F.val G φ.val).symm)

/-- A map out of the sheafification factors the canonical map as `φ` exactly when its adjoint
factors the given map of presheaves as the underlying map of `φ`. -/
theorem toModuleSheafification_comp_eq_iff (can : F.val ⟶ P) (φ : F ⟶ G)
    (ψ : (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj P ⟶ G) :
    toModuleSheafification can ≫ ψ = φ ↔
      can ≫ (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv P G ψ = φ.val := by
  rw [toModuleSheafification, Category.assoc, IsIso.inv_comp_eq,
    ← homEquiv_sheafification_counit_comp φ, ← Adjunction.homEquiv_naturality_left,
    Equiv.apply_eq_iff_eq]
  exact Iff.rfl

/-- If a map `can : F.val ⟶ P` of presheaves of `O_X`-modules out of a sheaf of modules has the
universal property that `φ.val` factors uniquely through it, then `φ` factors uniquely through
the induced map from `F` to the sheafification of `P`. -/
theorem existsUnique_comp_toModuleSheafification (can : F.val ⟶ P) (φ : F ⟶ G)
    (m : P ⟶ G.val) (hm : can ≫ m = φ.val)
    (huniq : ∀ m₁ m₂ : P ⟶ G.val, can ≫ m₁ = can ≫ m₂ → m₁ = m₂) :
    ∃! ψ : (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj P ⟶ G,
      toModuleSheafification can ≫ ψ = φ := by
  refine ⟨((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv P G).symm m,
    (toModuleSheafification_comp_eq_iff can φ _).2 ?_,
    fun ψ' hψ' ↦ (Equiv.eq_symm_apply _).2
      (huniq _ m (((toModuleSheafification_comp_eq_iff can φ ψ').1 hψ').trans hm.symm))⟩
  exact (congrArg (fun k ↦ can ≫ k)
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv P G).apply_symm_apply
        m)).trans hm

end Sheafification

section Pullback

variable {O₁ : X.Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf X.J RingCat.{w}}
  (θ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⟶ O₁) (σ : O₁ ⟶ R.obj)

/-- The morphism of sheaves of rings `O_X ⟶ R` determined by a factorization of the structure
sheaf through a presheaf of rings `O₁`, written in the form that the pullback of sheaves of
modules along the identity functor of the site expects. -/
def ringSheafHom : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    ((𝟭 X.C).sheafPushforwardContinuous RingCat.{w} X.J X.J).obj R :=
  ⟨θ ≫ σ⟩

variable [Presheaf.IsLocallyInjective X.J σ] [Presheaf.IsLocallySurjective X.J σ]
  [HasWeakSheafify X.J AddCommGrpCat.{max w z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w z}]
  {Λ : PresheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⥤
    PresheafOfModules.{max w z} O₁}

/-- The canonical map from a sheaf of `O_X`-modules to the pushforward of the sheafification of
its base change: the unit of `Λ ⊣ restrictScalars θ` followed by the restriction of the
sheafification unit. -/
def toPushforwardSheafification (adjΛ : Λ ⊣ PresheafOfModules.restrictScalars θ)
    (F : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    F ⟶ (SheafOfModules.pushforward (ringSheafHom θ σ)).obj
      ((PresheafOfModules.sheafification σ).obj (Λ.obj F.val)) :=
  ⟨adjΛ.unit.app F.val ≫ (PresheafOfModules.restrictScalars θ).map
    ((PresheafOfModules.sheafificationAdjunction σ).unit.app (Λ.obj F.val))⟩

/-- The left-hand compatibility isomorphism for restricting the composite adjunction along the
inclusion of sheaves of modules into presheaves of modules: an identity. -/
def pullbackComm₁ :
    SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (Λ ⋙ PresheafOfModules.sheafification σ) ≅
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ Λ ⋙
          PresheafOfModules.sheafification σ) ⋙
        𝟭 (SheafOfModules.{max w z} R) :=
  Iso.refl _

/-- The right-hand compatibility isomorphism for restricting the composite adjunction along the
inclusion of sheaves of modules into presheaves of modules: restricting scalars along `θ` and
then along `σ` is restricting scalars along the composite, so this too is an identity. -/
def pullbackComm₂ :
    𝟭 (SheafOfModules.{max w z} R) ⋙ (SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars σ) ⋙ PresheafOfModules.restrictScalars θ ≅
      SheafOfModules.pushforward.{max w z} (ringSheafHom θ σ) ⋙
        SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Iso.refl _

/-- Sheafifying a base change of presheaves of modules is left adjoint to the pushforward of
sheaves of modules along `O_X ⟶ R`.  This is the composite of the given adjunction with the
sheafification adjunction, restricted along the fully faithful inclusion of sheaves of modules
into presheaves of modules. -/
def pushforwardAdjunctionOfLeftAdjoint (adjΛ : Λ ⊣ PresheafOfModules.restrictScalars θ) :
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ Λ ⋙
        PresheafOfModules.sheafification σ) ⊣
      SheafOfModules.pushforward.{max w z} (ringSheafHom θ σ) :=
  Adjunction.restrictFullyFaithful
    (adjΛ.comp (PresheafOfModules.sheafificationAdjunction σ))
    (SheafOfModules.fullyFaithfulForget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (Functor.FullyFaithful.id _)
    (pullbackComm₁ σ) (pullbackComm₂ θ σ)

/-- The unit of `pushforwardAdjunctionOfLeftAdjoint` is the canonical map
`toPushforwardSheafification`. -/
theorem pushforwardAdjunctionOfLeftAdjoint_unit_app
    (adjΛ : Λ ⊣ PresheafOfModules.restrictScalars θ)
    (F : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (pushforwardAdjunctionOfLeftAdjoint θ σ adjΛ).unit.app F =
      toPushforwardSheafification θ σ adjΛ F := by
  apply (SheafOfModules.fullyFaithfulForget.{max w z}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_injective
  rw [pushforwardAdjunctionOfLeftAdjoint, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [pullbackComm₁, pullbackComm₂, Iso.refl_hom, NatTrans.id_app,
    Adjunction.comp_unit_app]
  rfl

variable [(SheafOfModules.pushforward.{max w z} (ringSheafHom θ σ)).IsRightAdjoint]

/-- Mathlib's pullback of sheaves of modules along `O_X ⟶ R` agrees with sheafifying the base
change of presheaves of modules: both are left adjoint to the pushforward. -/
def pullbackIsoSheafification (adjΛ : Λ ⊣ PresheafOfModules.restrictScalars θ) :
    SheafOfModules.pullback.{max w z} (ringSheafHom θ σ) ≅
      SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ Λ ⋙
        PresheafOfModules.sheafification σ :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction (ringSheafHom θ σ))
    (pushforwardAdjunctionOfLeftAdjoint θ σ adjΛ)

/-- The comparison isomorphism is compatible with the canonical maps out of `F`. -/
theorem unit_comp_pullbackIsoSheafification
    (adjΛ : Λ ⊣ PresheafOfModules.restrictScalars θ)
    (F : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (SheafOfModules.pullbackPushforwardAdjunction (ringSheafHom θ σ)).unit.app F ≫
      (SheafOfModules.pushforward (ringSheafHom θ σ)).map
        ((pullbackIsoSheafification θ σ adjΛ).hom.app F) =
      toPushforwardSheafification θ σ adjΛ F :=
  (Adjunction.unit_leftAdjointUniq_hom_app _ _ F).trans
    (pushforwardAdjunctionOfLeftAdjoint_unit_app θ σ adjΛ F)

end Pullback

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

open Stacks.PresheafOfModules.ChangeOfRings

variable {X : RingedSite.{u, v, w}} (S : MultiplicativeSubpresheaf X)

section ModuleSheaf

variable [HasWeakSheafify X.J AddCommGrpCat.{max w z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w z}]

/-- `(S⁻¹F)^#`, the sheafification of the sectionwise localization of a sheaf of `O_X`-modules,
as a sheaf of `O_X`-modules. -/
def localizationModuleSheaf
    (G : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
    ((restrictScalars S.toLocalizationPresheaf).obj (S.localizationModulePresheaf G.val))

/-- The canonical map `F ⟶ (S⁻¹F)^#` of sheaves of `O_X`-modules. -/
def toLocalizationModuleSheaf
    (G : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    G ⟶ S.localizationModuleSheaf G :=
  toModuleSheafification (S.toLocalizationModulePresheaf G.val)

/-- **The universal property of `(S⁻¹F)^#`.**  A map of sheaves of `O_X`-modules `φ : F ⟶ G`
such that each prescribed local section of `S` acts invertibly on `G` factors uniquely through
the canonical map `F ⟶ (S⁻¹F)^#`. -/
@[stacks 0EMD "localization_universal_property", ega "0 1.2.4" "more general"]
theorem existsUnique_lift_localizationModuleSheaf
    {F G : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : F ⟶ G)
    (hG : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      letI : Module (X.O.obj.obj U) (G.val.obj U) := (G.val.obj U).isModule
      Function.Bijective fun t : G.val.obj U ↦ (s : X.O.obj.obj U) • t) :
    ∃! ψ : S.localizationModuleSheaf F ⟶ G, S.toLocalizationModuleSheaf F ≫ ψ = φ := by
  have h := S.existsUnique_comp_sectionwiseLocalizationLift (S.toLocalizationModulePresheaf F.val)
    (S.isLocalizedModule_toLocalizationModulePresheaf F.val) φ.val hG
  exact existsUnique_comp_toModuleSheafification _ φ _ h.exists.choose_spec fun _ _ hm ↦
    (S.existsUnique_comp_sectionwiseLocalizationLift _
      (S.isLocalizedModule_toLocalizationModulePresheaf F.val) _ hG).unique hm rfl

end ModuleSheaf

section Tensor

variable {R : Sheaf X.J RingCat.{w}}
  (σ : ringPresheaf S.localizationPresheaf ⟶ R.obj)
  [Presheaf.IsLocallyInjective X.J σ] [Presheaf.IsLocallySurjective X.J σ]
  [HasWeakSheafify X.J AddCommGrpCat.{max w z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w z}]

/-- The morphism of sheaves of rings `O_X ⟶ R` induced by a map `σ` from the presheaf of
sectionwise localizations; when `σ` is locally bijective, `R` is `(S⁻¹O_X)^#`. -/
abbrev localizationRingSheafHom : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    ((𝟭 X.C).sheafPushforwardContinuous RingCat.{w} X.J X.J).obj R :=
  ringSheafHom (Functor.whiskerRight S.toLocalizationPresheaf
    (forget₂ CommRingCat RingCat)) σ

variable [(SheafOfModules.pushforward.{max w z} (S.localizationRingSheafHom σ)).IsRightAdjoint]

/-- **`(S⁻¹F)^# = (S⁻¹O_X)^# ⊗_{O_X} F` as sheaves of `(S⁻¹O_X)^#`-modules.**  The
sheafification of the sectionwise localization of `F` is the extension of scalars of `F` along
`O_X ⟶ (S⁻¹O_X)^#`. -/
@[stacks 0EMD "localization_tensor_iso"]
def localizationModuleSheafIsoTensor
    (F : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (PresheafOfModules.sheafification σ).obj (S.localizationModulePresheaf F.val) ≅
      (SheafOfModules.pullback (S.localizationRingSheafHom σ)).obj F :=
  ((pullbackIsoSheafification _ σ
    (changeOfRingsAdjunction S.toLocalizationPresheaf)).app F).symm

/-- The identification `(S⁻¹F)^# = (S⁻¹O_X)^# ⊗_{O_X} F` is compatible with the canonical maps
out of `F`: the unit of the pullback--pushforward adjunction corresponds to the sectionwise
localization map followed by the sheafification unit. -/
@[stacks 0EMD "localization_tensor_iso"]
theorem unit_comp_localizationModuleSheafIsoTensor
    (F : SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (SheafOfModules.pullbackPushforwardAdjunction
        (S.localizationRingSheafHom σ)).unit.app F ≫
      (SheafOfModules.pushforward (S.localizationRingSheafHom σ)).map
        (S.localizationModuleSheafIsoTensor σ F).inv =
      toPushforwardSheafification _ σ (changeOfRingsAdjunction S.toLocalizationPresheaf) F :=
  unit_comp_pullbackIsoSheafification _ σ
    (changeOfRingsAdjunction S.toLocalizationPresheaf) F

end Tensor

end AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

end
