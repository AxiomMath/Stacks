module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffinePushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleFirstOrderThickeningIdeal
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsIdealMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseFactorisation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue

/-!
# The ideal of an affine first order thickening, as an associated module

Let `h : U ⟶ U'` be a morphism of the big fppf site whose underlying schemes are affine and whose
scheme map is a first order thickening, with rings of global functions `R = Γ(U)`, `R' = Γ(U')`
and kernel `J = Ker(R' ⟶ R)`, a square-zero ideal and hence an `R`-module. The small étale ringed
topoi give a first order thickening `t` with square-zero ideal `𝒥 ⊂ 𝒪_{U'}`
(`AlgebraicGeometry.Space.smallEtaleRingedToposHomFirstOrderThickening`). This file identifies
the pulled-back ideal `t^*𝒥` on the small étale site of `U` with the associated module `J^~`:

`t^*𝒥 ≅ t^*(J^~) ≅ (R ⊗_{R'} J)^~ ≅ J^~`.

The first step is the affine computation of `𝒥` itself: `𝒥` is quasi-coherent, so it is the
associated module of its module of sections, and its sections are cut out of `R'` by the kernel
property of the defining ideal, read through the adjunction `(-)^~ ⊣ Γ`. The second step is the
base change of associated modules along an affine morphism
(`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso`), and the third is the algebra
`R ⊗_{R'} J ≅ J/J² = J`.

These are helpers for the tangent spaces of `Coh_{X/Y}` (Stacks 08W8) and of the functor of
quotients (Stacks 0CZW); no declaration here carries a `@[stacks]` attribute.

## Main definitions

* `AlgebraicGeometry.Space.siteThickeningIdealTildeIso`: `𝒥 ≅ J^~` on `U'`, as `R'`-modules.
* `AlgebraicGeometry.Space.thickeningIdealTildeIso`: `t^*𝒥 ≅ J^~` on `U`.
* `ModuleCat.extendScalarsKerIso`: `R ⊗_{R'} J ≅ J` for a square-zero kernel `J`.

## Main results

* `AlgebraicGeometry.Space.siteThickeningIdealTildeIso_hom_comp`: the identification
  `𝒥 ≅ J^~` is compatible with the inclusions into `R'^~ = 𝒪_{U'}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open AlgebraicGeometry (RingedToposHom)

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

open scoped ChangeOfRings

namespace Deformation.ToposThickening

open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedToposHom (unitStructureMap pullbackUnitStructureMap
  pushforwardModules pullbackAdjPushforwardModules)

universe v u' w v' u'' w'

section Generic

variable {X : RingedTopos.{v, u', w}} {Y : RingedTopos.{v', u'', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {i : RingedToposHom X Y} (hI : IdealOfThickening i)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- A map into the structure sheaf of the target killed by the structure map of a thickening
factors through the defining ideal. -/
theorem IdealOfThickening.exists_factor_of_comp_unitStructureMap_eq_zero
    {N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (m : N ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hm : m ≫ unitStructureMap i = 0) : ∃ l : N ⟶ hI.I, l ≫ hI.incl = m :=
  (Stacks.SheafOfModules.existsUnique_factorThrough hI.incl hI.injective m fun U z ↦
    (hI.kernel U _).1 ((RingedToposHom.unitStructureMap_val_app i U _).symm.trans
      (congrArg (fun k : N ⟶ (pushforwardModules i).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ↦
        k.val.app U z) hm))).exists

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The inclusion of a defining ideal is a monomorphism, being injective on sections. -/
theorem IdealOfThickening.cancel_incl
    {N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {f g : N ⟶ hI.I} (hfg : f ≫ hI.incl = g ≫ hI.incl) : f = g :=
  (Stacks.SheafOfModules.existsUnique_factorThrough hI.incl hI.injective (g ≫ hI.incl)
    fun U z ↦ ⟨g.val.app U z, rfl⟩).unique hfg rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A map into the structure sheaf of the target is killed by the structure map exactly when its
pullback vanishes. -/
theorem pullbackModules_map_eq_zero_iff_comp_unitStructureMap (f : RingedToposHom X Y)
    {N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (m : N ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (f.toModulesHom.pullbackModules).map m = 0 ↔ m ≫ unitStructureMap f = 0 := by
  have hz : (pullbackAdjPushforwardModules f).homEquiv N
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0 = 0 :=
    Adjunction.homAddEquiv_zero _ _ _
  constructor
  · intro h
    rw [← RingedToposHom.homEquiv_map_comp_pullbackUnitStructureMap f m, h, zero_comp, hz]
  · intro h
    have h' : (f.toModulesHom.pullbackModules).map m ≫ pullbackUnitStructureMap f = 0 :=
      ((pullbackAdjPushforwardModules f).homEquiv _ _).injective
        ((RingedToposHom.homEquiv_map_comp_pullbackUnitStructureMap f m).trans (h.trans hz.symm))
    exact (cancel_mono (pullbackUnitStructureMap f)).1 (h'.trans (zero_comp).symm)

end Generic

end Deformation.ToposThickening

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


section Scalar

/-- Extension of scalars carries multiplication by `y` on `R` to multiplication by `f y` on
`S`, through `S ⊗_R R ≅ S`. -/
theorem _root_.ModuleCat.ExtendScalars.map_smul_id_comp_objSelfIso_hom {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) (y : R) :
    (ModuleCat.extendScalars f).map (y • 𝟙 (ModuleCat.of R R)) ≫
        (ModuleCat.ExtendScalars.objSelfIso f).hom =
      (ModuleCat.ExtendScalars.objSelfIso f).hom ≫ (f y • 𝟙 (ModuleCat.of S S)) := by
  ext x
  show (ModuleCat.ExtendScalars.objSelfIso f).hom ((1 : S) ⊗ₜ[R,f] (y • x)) =
    f y • (ModuleCat.ExtendScalars.objSelfIso f).hom ((1 : S) ⊗ₜ[R,f] x)
  rw [ModuleCat.ExtendScalars.objSelfIso_hom_tmul, ModuleCat.ExtendScalars.objSelfIso_hom_tmul,
    smul_eq_mul, smul_eq_mul, map_mul]
  ring

/-- Multiplication by `y` on the free module of rank one vanishes only for `y = 0`. -/
theorem _root_.ModuleCat.smul_id_self_eq_zero_iff {R : Type u} [CommRing R] (y : R) :
    y • 𝟙 (ModuleCat.of R R) = 0 ↔ y = 0 := by
  constructor
  · intro hy
    have := congrArg (fun g : ModuleCat.of R R ⟶ ModuleCat.of R R ↦ g.hom (1 : R)) hy
    simpa using this
  · rintro rfl
    exact zero_smul _ _

/-- Multiplication maps on the free module of rank one are determined by the scalar. -/
theorem _root_.ModuleCat.smul_id_self_eq_iff {R : Type u} [CommRing R] (y y' : R) :
    y • 𝟙 (ModuleCat.of R R) = y' • 𝟙 (ModuleCat.of R R) ↔ y = y' := by
  rw [← sub_eq_zero, ← sub_smul, ModuleCat.smul_id_self_eq_zero_iff, sub_eq_zero]

/-- The morphism `R ⟶ M` sending `1` to `z`. -/
def homFromSelfOfElement {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (z : M) :
    ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M z)

/-- The morphism `R ⟶ M` attached to `z` sends `1` to `z`. -/
theorem homFromSelfOfElement_one {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (z : M) :
    (homFromSelfOfElement M z).hom 1 = z := by
  simp [homFromSelfOfElement]

/-- The morphism attached to `z` followed by `f` is the morphism attached to `f z`. -/
theorem homFromSelfOfElement_comp {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} (z : M)
    (f : M ⟶ N) : homFromSelfOfElement M z ≫ f = homFromSelfOfElement N (f.hom z) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
  show f.hom (r • z) = r • f.hom z
  exact map_smul f.hom r z

/-- **Maps out of a left adjoint applied to a module are determined by its elements**: two maps
`F M ⟶ X` agreeing after `F (r ↦ r m)` for every `m ∈ M` are equal. -/
theorem hom_ext_of_adjunction_homFromSelfOfElement {R : Type u} [CommRing R] {C : Type*}
    [Category C] {F : ModuleCat.{u} R ⥤ C} {G : C ⥤ ModuleCat.{u} R} (adj : F ⊣ G)
    {M : ModuleCat.{u} R} {X : C} {φ ψ : F.obj M ⟶ X}
    (h : ∀ m : M, F.map (homFromSelfOfElement M m) ≫ φ = F.map (homFromSelfOfElement M m) ≫ ψ) :
    φ = ψ := by
  apply (adj.homEquiv _ _).injective
  refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  have hm := congrArg (adj.homEquiv _ _) (h m)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    homFromSelfOfElement_comp, homFromSelfOfElement_comp] at hm
  have := congrArg (fun g : ModuleCat.of R R ⟶ G.obj X ↦ g.hom 1) hm
  dsimp only at this
  rwa [homFromSelfOfElement_one, homFromSelfOfElement_one] at this

section KerExtend

variable {R' R : Type u} [CommRing R'] [CommRing R] (π : R' →+* R) (hπ : Function.Surjective π)
  (h2 : RingHom.ker π ^ 2 = ⊥)

/-- The scalar tower for the square-zero kernel of a surjection. -/
theorem _root_.Stacks.Smooth.kerModule_isScalarTower :
    letI := π.toAlgebra
    letI := Stacks.Smooth.kerModule hπ h2
    IsScalarTower R' R (RingHom.ker π) := by
  let := π.toAlgebra
  let := Stacks.Smooth.kerModule hπ h2
  refine ⟨fun r' s k ↦ ?_⟩
  rw [Algebra.smul_def, mul_smul]
  show π r' • (s • k) = r' • (s • k)
  exact Stacks.Smooth.kerModule_smul hπ h2 r' (s • k)

/-- **`R ⊗_{R'} J ≅ J` for the square-zero kernel `J` of a surjection `R' ⟶ R`**, as
`R`-modules. -/
def _root_.ModuleCat.extendScalarsKerIso :
    (ModuleCat.extendScalars π).obj (ModuleCat.of R' (RingHom.ker π)) ≅
      @ModuleCat.of R _ (RingHom.ker π) _ (Stacks.Smooth.kerModule hπ h2) := by
  letI := π.toAlgebra
  letI := Stacks.Smooth.kerModule hπ h2
  haveI := Stacks.Smooth.kerModule_isScalarTower π hπ h2
  let f : R →ₗ[R] RingHom.ker π →ₗ[R'] RingHom.ker π :=
    { toFun := fun s ↦
        { toFun := fun k ↦ s • k
          map_add' := fun k k' ↦ smul_add s k k'
          map_smul' := fun r' k ↦ by
            change s • (r' • k) = r' • (s • k)
            rw [← Stacks.Smooth.kerModule_smul hπ h2 r' k,
              ← Stacks.Smooth.kerModule_smul hπ h2 r' (s • k), smul_smul, smul_smul, mul_comm] }
      map_add' := fun s s' ↦ LinearMap.ext fun k ↦ add_smul s s' k
      map_smul' := fun s s' ↦ LinearMap.ext fun k ↦ mul_smul s s' k }
  let L : TensorProduct R' R (RingHom.ker π) →ₗ[R] RingHom.ker π :=
    TensorProduct.AlgebraTensorModule.lift f
  have hg : ∀ (s : R) (k : RingHom.ker π),
      (1 : R) ⊗ₜ[R'] (s • k) = s • ((1 : R) ⊗ₜ[R'] k) := by
    intro s k
    obtain ⟨r', rfl⟩ := hπ s
    rw [Stacks.Smooth.kerModule_smul hπ h2 r' k, ← TensorProduct.smul_tmul,
      TensorProduct.smul_tmul']
    congr 1
  let g : RingHom.ker π →ₗ[R] TensorProduct R' R (RingHom.ker π) :=
    { toFun := fun k ↦ (1 : R) ⊗ₜ[R'] k
      map_add' := fun k k' ↦ TensorProduct.tmul_add _ _ _
      map_smul' := hg }
  refine (LinearEquiv.ofLinear L g ?_ ?_).toModuleIso
  · refine LinearMap.ext fun k ↦ ?_
    change L ((1 : R) ⊗ₜ[R'] k) = k
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    exact one_smul R k
  · refine TensorProduct.AlgebraTensorModule.ext fun s k ↦ ?_
    change (1 : R) ⊗ₜ[R'] (L (s ⊗ₜ[R'] k)) = s ⊗ₜ[R'] k
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    obtain ⟨r', rfl⟩ := hπ s
    change (1 : R) ⊗ₜ[R'] (π r' • k) = π r' ⊗ₜ[R'] k
    rw [Stacks.Smooth.kerModule_smul hπ h2 r' k, ← TensorProduct.smul_tmul, Algebra.smul_def,
      mul_one]
    rfl

/-- `R ⊗_{R'} J ≅ J` sends `s ⊗ k` to `s • k`. -/
theorem _root_.ModuleCat.extendScalarsKerIso_hom_tmul (s : R) (k : RingHom.ker π) :
    (ModuleCat.extendScalarsKerIso π hπ h2).hom.hom (s ⊗ₜ[R',π] k) =
      @HSMul.hSMul R (RingHom.ker π) (RingHom.ker π)
        (@instHSMul R (RingHom.ker π) (Stacks.Smooth.kerModule hπ h2).toSMul) s k := by
  let := π.toAlgebra
  let := Stacks.Smooth.kerModule hπ h2
  have := Stacks.Smooth.kerModule_isScalarTower π hπ h2
  exact TensorProduct.AlgebraTensorModule.lift_tmul _ s k

/-- Extending scalars of `r ↦ r k` and identifying `R ⊗_{R'} J ≅ J` gives `s ↦ s k`. -/
theorem _root_.ModuleCat.extendScalars_homFromSelfOfElement_kerIso (k : RingHom.ker π) :
    (ModuleCat.ExtendScalars.objSelfIso π).inv ≫
        (ModuleCat.extendScalars π).map (homFromSelfOfElement (ModuleCat.of R' (RingHom.ker π)) k) ≫
        (ModuleCat.extendScalarsKerIso π hπ h2).hom =
      homFromSelfOfElement
        (@ModuleCat.of R _ (RingHom.ker π) _ (Stacks.Smooth.kerModule hπ h2)) k := by
  let := Stacks.Smooth.kerModule hπ h2
  refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
  show (ModuleCat.extendScalarsKerIso π hπ h2).hom.hom
      ((ModuleCat.extendScalars π).map (homFromSelfOfElement (ModuleCat.of R' (RingHom.ker π)) k)
        (r ⊗ₜ[R',π] (1 : R'))) = r • k
  rw [ModuleCat.ExtendScalars.map_tmul, homFromSelfOfElement_one]
  exact ModuleCat.extendScalarsKerIso_hom_tmul π hπ h2 r k

end KerExtend

end Scalar

section ThickeningKer

variable {T T'₁ T'₂ : Scheme.{u}} [IsAffine T'₁] [IsAffine T'₂] {i₁ : T ⟶ T'₁} {i₂ : T ⟶ T'₂}
  (hi₁ : Stacks.Thickenings.IsFirstOrderThickening i₁)
  (hi₂ : Stacks.Thickenings.IsFirstOrderThickening i₂)

/-- The kernel `Ker(Γ(T') ⟶ Γ(T))` of an affine first order thickening, as a `Γ(T)`-module. -/
abbrev thickeningKerModuleOf (hi : Stacks.Thickenings.IsFirstOrderThickening i₁) :
    ModuleCat.{u} Γ(T, ⊤) :=
  @ModuleCat.of Γ(T, ⊤) _ (RingHom.ker i₁.appTop.hom) _
    (Stacks.Smooth.kerModule (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hi)
      (Stacks.Smooth.ker_appTop_sq_eq_bot hi))

omit [IsAffine T'₁] [IsAffine T'₂] in
/-- `g^♯` carries the kernel of `i₁^♯` into the kernel of `i₂^♯` when `i₂ ≫ g = i₁`. -/
theorem appTop_mem_ker_of_comp_eq (g : T'₂ ⟶ T'₁) (hg : i₂ ≫ g = i₁)
    (x : RingHom.ker i₁.appTop.hom) : g.appTop.hom (x : Γ(T'₁, ⊤)) ∈ RingHom.ker i₂.appTop.hom := by
  rw [RingHom.mem_ker, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg]
  exact x.2

/-- **The map of kernels of a morphism of affine first order thickenings under `T`**: for
`g : T'₂ ⟶ T'₁` with `i₂ ≫ g = i₁`, the restriction of `g^♯ : Γ(T'₁) ⟶ Γ(T'₂)` to the kernels,
a map of `Γ(T)`-modules. -/
def thickeningKerMap (g : T'₂ ⟶ T'₁) (hg : i₂ ≫ g = i₁) :
    thickeningKerModuleOf hi₁ ⟶ thickeningKerModuleOf hi₂ :=
  letI := Stacks.Smooth.kerModule (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hi₁)
    (Stacks.Smooth.ker_appTop_sq_eq_bot hi₁)
  letI := Stacks.Smooth.kerModule (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hi₂)
    (Stacks.Smooth.ker_appTop_sq_eq_bot hi₂)
  ModuleCat.ofHom
    { toFun := fun x ↦ ⟨g.appTop.hom x, appTop_mem_ker_of_comp_eq g hg x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add g.appTop.hom (x : Γ(T'₁, ⊤)) y)
      map_smul' := fun s x ↦ by
        obtain ⟨r, rfl⟩ := Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hi₁ s
        have hr : i₂.appTop.hom (g.appTop.hom r) = i₁.appTop.hom r := by
          rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg]
        have e1 : ((i₁.appTop.hom r • x : RingHom.ker i₁.appTop.hom) : Γ(T'₁, ⊤)) = r * x :=
          congrArg Subtype.val (Stacks.Smooth.kerModule_smul _ _ r x)
        have e2 : ∀ y : RingHom.ker i₂.appTop.hom,
            ((i₁.appTop.hom r • y : RingHom.ker i₂.appTop.hom) : Γ(T'₂, ⊤)) =
              g.appTop.hom r * y := by
          intro y
          rw [← hr]
          exact congrArg Subtype.val (Stacks.Smooth.kerModule_smul _ _ (g.appTop.hom r) y)
        apply Subtype.ext
        refine Eq.trans ?_ (e2 _).symm
        change g.appTop.hom ((i₁.appTop.hom r • x : RingHom.ker i₁.appTop.hom) : Γ(T'₁, ⊤)) = _
        rw [e1, map_mul] }

/-- The map of kernels is `g^♯` on elements. -/
theorem thickeningKerMap_apply (g : T'₂ ⟶ T'₁) (hg : i₂ ≫ g = i₁) (x : RingHom.ker i₁.appTop.hom) :
    (((thickeningKerMap hi₁ hi₂ g hg).hom x : RingHom.ker i₂.appTop.hom) : Γ(T'₂, ⊤)) =
      g.appTop.hom x :=
  rfl

end ThickeningKer

section GenericSection

/-- The bookkeeping behind
`AlgebraicGeometry.Space.representedThickeningIdealSection_comp_tildeIsoAux_hom`, in arbitrary
categories: a section built from `ε : 1 ≅ Pb 1`, `u' : F' R' ≅ 1`, `κ` and
`T : 𝒥 ≅ F' K'`, followed by `Pb T`, the base change `P` and `FU ek`, is `u⁻¹ ≫ FU θ` as soon as
`P` is normalized at `R'` and `θ = objSelf⁻¹ ≫ ext κ ≫ ek`. -/
theorem generic_section_comp_iso {R' R : Type u} [CommRing R'] [CommRing R] (ρ : R' →+* R)
    {C D : Type*} [Category C] [Category D]
    (F' : ModuleCat.{u} R' ⥤ C) (FU : ModuleCat.{u} R ⥤ D) (Pb : C ⥤ D)
    (P : F' ⋙ Pb ≅ ModuleCat.extendScalars ρ ⋙ FU) {oC : C} {oD : D}
    (ε : oD ≅ Pb.obj oC) (u' : F'.obj (ModuleCat.of R' R') ≅ oC)
    (u : FU.obj (ModuleCat.of R R) ≅ oD)
    (hP : P.hom.app (ModuleCat.of R' R') ≫ FU.map (ModuleCat.ExtendScalars.objSelfIso ρ).hom =
      Pb.map u'.hom ≫ ε.inv ≫ u.inv)
    {I : C} {K' : ModuleCat.{u} R'} {K : ModuleCat.{u} R} (T : I ≅ F'.obj K')
    (κ : ModuleCat.of R' R' ⟶ K') (ek : (ModuleCat.extendScalars ρ).obj K' ≅ K)
    (θ : ModuleCat.of R R ⟶ K)
    (hθ : (ModuleCat.ExtendScalars.objSelfIso ρ).inv ≫ (ModuleCat.extendScalars ρ).map κ ≫
      ek.hom = θ) :
    (ε.hom ≫ Pb.map (u'.inv ≫ F'.map κ ≫ T.inv)) ≫
        (Pb.mapIso T ≪≫ P.app K' ≪≫ FU.mapIso ek).hom = u.inv ≫ FU.map θ := by
  have hP' : P.hom.app (ModuleCat.of R' R') =
      (Pb.map u'.hom ≫ ε.inv ≫ u.inv) ≫ FU.map (ModuleCat.ExtendScalars.objSelfIso ρ).inv := by
    rw [← hP, Category.assoc, ← FU.map_comp, Iso.hom_inv_id, FU.map_id]
    exact (Category.comp_id _).symm
  have hn := P.hom.naturality κ
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc, Functor.map_comp,
    Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% hn, hP']
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← FU.map_comp, ← FU.map_comp, hθ]

end GenericSection

section AffineThickening

variable {U U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (h : U ⟶ U')

variable (U') in
/-- The associated-module functor of `R = Γ(U')`, with values read in the spelling of the small
étale ringed topos of `U'`. -/
abbrev toposAssociatedFunctor :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).O) :=
  representedAffineAssociated B S hS U'

variable (U') in
/-- The associated module of an `R`-module, for `R = Γ(U')`, in the spelling of the small étale
ringed topos of `U'`. -/
abbrev toposAssociated (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).O) :=
  (toposAssociatedFunctor U').obj M

/-- Multiplication by `y ∈ Γ(U')` on the associated module of `Γ(U')`, in the spelling of the
small étale ringed topos. -/
abbrev tildeSmul (y : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :
    toposAssociated U' (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ⟶
      toposAssociated U' (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :=
  (representedAffineAssociated B S hS U').map
      (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))

variable (U') in
/-- The identification of the associated module of `Γ(U')` with `𝒪_{U'}`, in the spelling of
the small étale ringed topos. -/
abbrev toposAssociatedUnitIso :
    toposAssociated U' (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).O) :=
  representedAffineAssociatedObjUnitIso B S hS U'

/-- The pullback of multiplication by `y` on `Γ(U')^~` vanishes exactly when `h^♯ y = 0`. -/
theorem pullbackModules_map_tildeSmul_eq_zero_iff
    (y : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :
    ((smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom.pullbackModules).map
        (tildeSmul y) = 0 ↔
      (representedAffineCommRingCatHom B S hS h).hom y = 0 := by
  have hn := (representedAffineAssociatedPullbackIso B S hS h).hom.naturality
    (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
  have := (representedAffineAssociatedFullyFaithful B S hS U).faithful
  refine (Preadditive.IsIso.comp_right_eq_zero _
    ((representedAffineAssociatedPullbackIso B S hS h).hom.app
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))).symm.trans ?_
  refine (Eq.congr_left hn).trans ?_
  refine (Preadditive.IsIso.comp_left_eq_zero _ _).trans ?_
  refine (Functor.map_eq_zero_iff (representedAffineAssociated B S hS U)).trans ?_
  refine (Preadditive.IsIso.comp_right_eq_zero _
    (ModuleCat.ExtendScalars.objSelfIso
      (representedAffineCommRingCatHom B S hS h).hom).hom).symm.trans ?_
  refine (Eq.congr_left (ModuleCat.ExtendScalars.map_smul_id_comp_objSelfIso_hom _ y)).trans ?_
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).trans (ModuleCat.smul_id_self_eq_zero_iff _)

/-- **Multiplication by `y` on `𝒪_{U'}` is killed by the structure map of `h` exactly when
`h^♯ y = 0`.** -/
theorem tildeSmul_comp_unitStructureMap_eq_zero_iff
    (y : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :
    (tildeSmul y ≫ (toposAssociatedUnitIso U').hom) ≫ RingedToposHom.unitStructureMap
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)) = 0 ↔
      (representedAffineCommRingCatHom B S hS h).hom y = 0 := by
  refine (Deformation.ToposThickening.pullbackModules_map_eq_zero_iff_comp_unitStructureMap
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h))
    (tildeSmul y ≫ (toposAssociatedUnitIso U').hom)).symm.trans ?_
  refine Iff.trans ?_ (pullbackModules_map_tildeSmul_eq_zero_iff h y)
  have e := ((smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS h)).toModulesHom.pullbackModules).map_comp
    (tildeSmul y) (toposAssociatedUnitIso U').hom
  exact (Eq.congr_left e).trans (Preadditive.IsIso.comp_right_eq_zero _ _)

variable (hiso : IsIso (Subfunctor.toRange (representedSpaceMap B S hS h).hom))
  (hfo : IsFirstOrderThickening B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
    (Subfunctor.range (representedSpaceMap B S hS h).hom))

/-- The defining ideal `𝒥 ⊂ 𝒪_{U'}` of the first order thickening `U ⊂ U'` of the small étale
ringed topoi. -/
abbrev affineThickeningIdeal :
    Deformation.ToposThickening.IdealOfThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)) :=
  (smallEtaleRingedToposHomFirstOrderThickening B S hS (representedSpaceMap B S hS h)
    hiso hfo).idealOfThickening

/-- For `y` in the kernel of `h^♯`, multiplication by `y` on `𝒪_{U'}` factors through `𝒥`. -/
theorem exists_tildeSmul_factor (y : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
    (hy : (representedAffineCommRingCatHom B S hS h).hom y = 0) :
    ∃ l : toposAssociated U' (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ⟶ (affineThickeningIdeal h hiso hfo).I,
      l ≫ (affineThickeningIdeal h hiso hfo).incl = tildeSmul y ≫ (toposAssociatedUnitIso U').hom :=
  (affineThickeningIdeal h hiso hfo).exists_factor_of_comp_unitStructureMap_eq_zero _
    ((tildeSmul_comp_unitStructureMap_eq_zero_iff h y).2 hy)

/-- The ideal `𝒥`, in the spelling of the modules on the small étale ringed site of the
represented space `U'`. -/
abbrev siteThickeningIdeal :
    Modules.{u, u} B S hS (yoneda.obj U') (isAlgebraicSpace_yoneda B S hS U') :=
  (affineThickeningIdeal h hiso hfo).I

/-- The direct image of `𝒪_U` along `h`, in the spelling of the small étale ringed site of `U'`. -/
abbrev sitePushforwardUnit :
    Modules.{u, u} B S hS (yoneda.obj U') (isAlgebraicSpace_yoneda B S hS U') :=
  (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).pushforwardModules.obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O))

/-- The structure map `𝒪_{U'} ⟶ h_*𝒪_U`, in the spelling of the small étale ringed site. -/
abbrev siteUnitStructureMap :
    structureModule ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ ⟶ sitePushforwardUnit h :=
  RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h))

/-- The inclusion `𝒥 ⟶ 𝒪_{U'}`, in the spelling of the small étale ringed site. -/
abbrev siteThickeningIdealIncl :
    siteThickeningIdeal h hiso hfo ⟶
      structureModule ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ :=
  (affineThickeningIdeal h hiso hfo).incl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- The ideal is killed by the structure map, in the site spelling. -/
theorem siteThickeningIdealIncl_comp_siteUnitStructureMap :
    siteThickeningIdealIncl h hiso hfo ≫ siteUnitStructureMap h = 0 :=
  (affineThickeningIdeal h hiso hfo).incl_comp_unitStructureMap

/-- `tildeSmul_comp_unitStructureMap_eq_zero_iff`, in the site spelling. -/
theorem site_map_smul_comp_eq_zero_iff (y : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :
    ((representedAffineAssociated B S hS U').map
        (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≫
      (representedAffineAssociatedObjUnitIso B S hS U').hom) ≫ siteUnitStructureMap h = 0 ↔
      (representedAffineCommRingCatHom B S hS h).hom y = 0 :=
  tildeSmul_comp_unitStructureMap_eq_zero_iff h y

/-- The inclusion `𝒥 ⟶ Γ(U')^~` of the ideal into the associated module of `Γ(U')`, in the
spelling of the small étale ringed site. -/
def siteThickeningIdealToTilde :
    siteThickeningIdeal h hiso hfo ⟶
      (representedAffineAssociated B S hS U').obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :=
  siteThickeningIdealIncl h hiso hfo ≫ (representedAffineAssociatedObjUnitIso B S hS U').inv

/-- For `y` in the kernel of `h^♯`, multiplication by `y` on `Γ(U')^~` factors through `𝒥`, in the
spelling of the small étale ringed site. -/
theorem exists_siteThickeningIdeal_factor (y : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
    (hy : (representedAffineCommRingCatHom B S hS h).hom y = 0) :
    ∃ l : (representedAffineAssociated B S hS U').obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ⟶ siteThickeningIdeal h hiso hfo,
      l ≫ siteThickeningIdealToTilde h hiso hfo =
        (representedAffineAssociated B S hS U').map
          (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) := by
  obtain ⟨l, hl⟩ :=
    (affineThickeningIdeal h hiso hfo).exists_factor_of_comp_unitStructureMap_eq_zero
    (N := toposAssociated U' (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    ((representedAffineAssociated B S hS U').map
        (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≫
      (representedAffineAssociatedObjUnitIso B S hS U').hom)
    ((site_map_smul_comp_eq_zero_iff h y).2 hy)
  let l' : (representedAffineAssociated B S hS U').obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ⟶ siteThickeningIdeal h hiso hfo := l
  have hl' : l' ≫ siteThickeningIdealIncl h hiso hfo =
      (representedAffineAssociated B S hS U').map
        (y • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≫
      (representedAffineAssociatedObjUnitIso B S hS U').hom := hl
  refine ⟨l', ?_⟩
  rw [siteThickeningIdealToTilde, ← Category.assoc, hl', Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The sections of `𝒥` mapped into `Γ(U')`: the sections of the inclusion
`𝒥 ⟶ Γ(U')^~`, read through `Γ(U') ≅ Γ(Γ(U')^~)`. -/
def affineThickeningIdealSections :
    (representedAffineSections B S hS U').obj (siteThickeningIdeal h hiso hfo) ⟶
      ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
  (representedAffineSections B S hS U').map (siteThickeningIdealToTilde h hiso hfo) ≫
    inv ((representedAffineAssociatedAdjunction B S hS U').unit.app
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- **The element computation.** For a morphism `ψ : Γ(U')^~ ⟶ 𝒥`, the image in `Γ(U')` of the
section it corresponds to is the function `y` with `ψ` followed by the inclusion equal to
multiplication by `y`. -/
theorem map_smul_affineThickeningIdealSections
    (ψ : (representedAffineAssociated B S hS U').obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ⟶ siteThickeningIdeal h hiso hfo) :
    (representedAffineAssociated B S hS U').map
        ((affineThickeningIdealSections h hiso hfo).hom
          (((representedAffineAssociatedAdjunction B S hS U').homEquiv _ _ ψ).hom 1) •
          𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) =
      ψ ≫ siteThickeningIdealToTilde h hiso hfo := by
  let adj := representedAffineAssociatedAdjunction B S hS U'
  let M := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
  let φ : M ⟶ M := (representedAffineAssociatedFullyFaithful B S hS U').preimage
    (ψ ≫ siteThickeningIdealToTilde h hiso hfo)
  have hφ : (representedAffineAssociated B S hS U').map φ =
      ψ ≫ siteThickeningIdealToTilde h hiso hfo :=
    (representedAffineAssociatedFullyFaithful B S hS U').map_preimage _
  have hsmul : φ = φ.hom 1 • 𝟙 M := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    show φ.hom x = φ.hom 1 • x
    have : φ.hom x = x • φ.hom 1 := by
      rw [← φ.hom.map_smul, smul_eq_mul, mul_one]
    rw [this, smul_eq_mul, smul_eq_mul, mul_comm]
  have e1 : adj.homEquiv _ _ ψ ≫ affineThickeningIdealSections h hiso hfo = φ := by
    rw [affineThickeningIdealSections, ← Category.assoc,
      ← Adjunction.homEquiv_naturality_right, ← hφ, Adjunction.homEquiv_unit]
    have hn := adj.unit.naturality φ
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have e2 : (affineThickeningIdealSections h hiso hfo).hom ((adj.homEquiv _ _ ψ).hom 1) =
      φ.hom 1 := by
    rw [← e1]
    rfl
  rw [e2, ← hφ, ← hsmul]

/-- The morphism `Γ(U')^~ ⟶ 𝒥` corresponding to a section of `𝒥`. -/
abbrev siteThickeningIdealSectionHom
    (z : (representedAffineSections B S hS U').obj (siteThickeningIdeal h hiso hfo)) :
    (representedAffineAssociated B S hS U').obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ⟶ siteThickeningIdeal h hiso hfo :=
  ((representedAffineAssociatedAdjunction B S hS U').homEquiv _ _).symm
    (homFromSelfOfElement _ z)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- The section corresponding to the morphism attached to a section is that section. -/
theorem homEquiv_siteThickeningIdealSectionHom_one
    (z : (representedAffineSections B S hS U').obj (siteThickeningIdeal h hiso hfo)) :
    (((representedAffineAssociatedAdjunction B S hS U').homEquiv _ _
      (siteThickeningIdealSectionHom h hiso hfo z)).hom 1) = z := by
  rw [Equiv.apply_symm_apply]
  exact homFromSelfOfElement_one _ z

/-- The sections of `𝒥` land in the kernel of `h^♯`. -/
theorem affineThickeningIdealSections_mem
    (z : (representedAffineSections B S hS U').obj (siteThickeningIdeal h hiso hfo)) :
    (representedAffineCommRingCatHom B S hS h).hom
      ((affineThickeningIdealSections h hiso hfo).hom z) = 0 := by
  have e := map_smul_affineThickeningIdealSections h hiso hfo
    (siteThickeningIdealSectionHom h hiso hfo z)
  rw [homEquiv_siteThickeningIdealSectionHom_one] at e
  refine (site_map_smul_comp_eq_zero_iff h _).1 ?_
  rw [e, siteThickeningIdealToTilde]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    siteThickeningIdealIncl_comp_siteUnitStructureMap, comp_zero]

/-- Every function in the kernel of `h^♯` is the image of a section of `𝒥`. -/
theorem exists_affineThickeningIdealSections_eq (y : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
    (hy : (representedAffineCommRingCatHom B S hS h).hom y = 0) :
    ∃ z, (affineThickeningIdealSections h hiso hfo).hom z = y := by
  obtain ⟨l, hl⟩ := exists_siteThickeningIdeal_factor h hiso hfo y hy
  refine ⟨((representedAffineAssociatedAdjunction B S hS U').homEquiv _ _ l).hom 1, ?_⟩
  have e := (map_smul_affineThickeningIdealSections h hiso hfo l).trans hl
  have e' := (representedAffineAssociatedFullyFaithful B S hS U').map_injective e
  exact (ModuleCat.smul_id_self_eq_iff _ _).1 e'

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- The map from the sections of `𝒥` to `Γ(U')` is injective. -/
theorem affineThickeningIdealSections_injective :
    Function.Injective (affineThickeningIdealSections h hiso hfo).hom := by
  intro z z' hzz
  have key : ∀ w, (representedAffineAssociated B S hS U').map
      ((affineThickeningIdealSections h hiso hfo).hom w •
        𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) =
      siteThickeningIdealSectionHom h hiso hfo w ≫ siteThickeningIdealToTilde h hiso hfo := by
    intro w
    have e := map_smul_affineThickeningIdealSections h hiso hfo
      (siteThickeningIdealSectionHom h hiso hfo w)
    rwa [homEquiv_siteThickeningIdealSectionHom_one] at e
  have e := key z
  have e' := key z'
  rw [hzz, e'] at e
  have e₂ : siteThickeningIdealSectionHom h hiso hfo z' ≫ siteThickeningIdealIncl h hiso hfo =
      siteThickeningIdealSectionHom h hiso hfo z ≫ siteThickeningIdealIncl h hiso hfo := by
    have := congrArg (· ≫ (representedAffineAssociatedObjUnitIso B S hS U').hom) e
    simp only [siteThickeningIdealToTilde, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at this
    exact this
  have e₃ := (affineThickeningIdeal h hiso hfo).cancel_incl e₂
  exact (homEquiv_siteThickeningIdealSectionHom_one h hiso hfo z).symm.trans
    ((congrArg (fun ψ ↦ ((representedAffineAssociatedAdjunction B S hS U').homEquiv _ _ ψ).hom 1)
      e₃.symm).trans (homEquiv_siteThickeningIdealSectionHom_one h hiso hfo z'))

/-- The image of the sections of `𝒥` in `Γ(U')` is the kernel of `h^♯`. -/
theorem range_affineThickeningIdealSections :
    LinearMap.range (affineThickeningIdealSections h hiso hfo).hom =
      RingHom.ker (representedAffineCommRingCatHom B S hS h).hom := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact affineThickeningIdealSections_mem h hiso hfo z
  · intro hy
    exact exists_affineThickeningIdealSections_eq h hiso hfo y hy

/-- **The sections of `𝒥` are the kernel of `Γ(U') ⟶ Γ(U)`**, as `Γ(U')`-modules. -/
def affineThickeningIdealSectionsEquiv :
    (representedAffineSections B S hS U').obj (siteThickeningIdeal h hiso hfo) ≃ₗ[
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)]
      RingHom.ker (representedAffineCommRingCatHom B S hS h).hom :=
  (LinearEquiv.ofInjective _ (affineThickeningIdealSections_injective h hiso hfo)).trans
    (LinearEquiv.ofEq _ _ (range_affineThickeningIdealSections h hiso hfo))

/-- The identification of the sections of `𝒥` with the kernel, on elements. -/
theorem affineThickeningIdealSectionsEquiv_apply
    (z : (representedAffineSections B S hS U').obj (siteThickeningIdeal h hiso hfo)) :
    ((affineThickeningIdealSectionsEquiv h hiso hfo z :
        RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) =
      (affineThickeningIdealSections h hiso hfo).hom z :=
  rfl

/-- **The ideal `𝒥` of `U ⊂ U'` is the associated module of the kernel of `Γ(U') ⟶ Γ(U)`.** -/
def siteThickeningIdealTildeIso :
    siteThickeningIdeal h hiso hfo ≅ (representedAffineAssociated B S hS U').obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom)) :=
  haveI := isIso_representedAffineAssociatedAdjunction_counit_app B S hS
    (siteThickeningIdeal h hiso hfo)
    (isQuasicoherentOnSite_smallEtaleThickeningIdeal B S hS _ hiso hfo)
  (asIso ((representedAffineAssociatedAdjunction B S hS U').counit.app
      (siteThickeningIdeal h hiso hfo))).symm ≪≫
    (representedAffineAssociated B S hS U').mapIso
      (affineThickeningIdealSectionsEquiv h hiso hfo).toModuleIso

/-- The identification of `𝒥` with the associated module of the kernel is compatible with the
inclusions into `Γ(U')^~`. -/
theorem siteThickeningIdealTildeIso_hom_comp :
    (siteThickeningIdealTildeIso h hiso hfo).hom ≫ (representedAffineAssociated B S hS U').map
        (ModuleCat.ofHom (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom).subtype) =
      siteThickeningIdealToTilde h hiso hfo := by
  let adj := representedAffineAssociatedAdjunction B S hS U'
  let M := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
  have := isIso_representedAffineAssociatedAdjunction_counit_app B S hS
    (siteThickeningIdeal h hiso hfo)
    (isQuasicoherentOnSite_smallEtaleThickeningIdeal B S hS _ hiso hfo)
  have hc : (affineThickeningIdealSectionsEquiv h hiso hfo).toModuleIso.hom ≫
      ModuleCat.ofHom (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom).subtype =
      affineThickeningIdealSections h hiso hfo := by
    ext z
    rfl
  have htri := adj.left_triangle_components M
  have hη : (representedAffineAssociated B S hS U').map (inv (adj.unit.app M)) =
      adj.counit.app ((representedAffineAssociated B S hS U').obj M) := by
    rw [Functor.map_inv, IsIso.inv_eq_of_hom_inv_id htri]
  have hn := adj.counit.naturality (siteThickeningIdealToTilde h hiso hfo)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [siteThickeningIdealTildeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, ← Functor.map_comp, hc, affineThickeningIdealSections, Functor.map_comp, hη,
    hn, asIso_inv, IsIso.inv_hom_id_assoc]

/-- `𝒥 ≅ J^~`, in the spelling of the small étale ringed topos of `U'`. -/
abbrev toposThickeningIdealTildeIso :
    (affineThickeningIdeal h hiso hfo).I ≅ toposAssociated U'
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom)) :=
  siteThickeningIdealTildeIso h hiso hfo

variable (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h))

/-- The kernel `J = Ker(Γ(U') ⟶ Γ(U))` with its `Γ(U)`-module structure. -/
abbrev thickeningKerModuleCat : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  thickeningKerModuleOf hh

/-- `t^*𝒥 ≅ J^~`, with the pullback along the four-field morphism `t.toModulesHom`. -/
def representedThickeningIdealTildeIsoAux :
    (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.obj
        (affineThickeningIdeal h hiso hfo).I ≅
      toposAssociated U (thickeningKerModuleCat h hh) :=
  (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.mapIso
      (toposThickeningIdealTildeIso h hiso hfo) ≪≫
    (representedAffineAssociatedPullbackIso B S hS h).app _ ≪≫
    (toposAssociatedFunctor U).mapIso
      (ModuleCat.extendScalarsKerIso _
        (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hh)
        (Stacks.Smooth.ker_appTop_sq_eq_bot hh))

/-- The two four-field spellings of the pullback of `𝒥` along `t`. -/
def representedThickeningIdealPullbackSpellingIso :
    (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toRingedToposModulesHom.pullbackModules.obj
        (affineThickeningIdeal h hiso hfo).I ≅
    (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.obj
        (affineThickeningIdeal h hiso hfo).I :=
  eqToIso (congrArg (fun φ : Stacks.Sheaves.RingedToposModules.RingedToposHom
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) ↦
      φ.pullbackModules.obj (affineThickeningIdeal h hiso hfo).I)
      (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom_eq_toRingedToposModulesHom.symm)

/-- **The pulled-back ideal of `U ⊂ U'` is the associated module of the kernel**, in the
spelling of the represented spaces: `t^*𝒥 ≅ (Γ(U) ⊗_{Γ(U')} J)^~ ≅ J^~`, where
`J = Ker(Γ(U') ⟶ Γ(U))` with its `Γ(U)`-module structure. -/
def representedThickeningIdealTildeIso :
    (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toRingedToposModulesHom.pullbackModules.obj
        (affineThickeningIdeal h hiso hfo).I ≅ toposAssociated U (thickeningKerModuleCat h hh) :=
  representedThickeningIdealPullbackSpellingIso h hiso hfo ≪≫
    representedThickeningIdealTildeIsoAux h hiso hfo hh

/-- **The generator of `𝒥` attached to `a ∈ J`**: the map `𝒪_{U'} ⟶ 𝒥` whose composite with the
inclusion is multiplication by `a`. It is `r ↦ r a` on associated modules. -/
def representedThickeningIdealGenerator
    (a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
    structureModule ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ ⟶
      siteThickeningIdeal h hiso hfo :=
  (representedAffineAssociatedObjUnitIso B S hS U').inv ≫
    (representedAffineAssociated B S hS U').map (homFromSelfOfElement _ a) ≫
    (siteThickeningIdealTildeIso h hiso hfo).inv

/-- The generator attached to `a` followed by the inclusion is multiplication by `a`. -/
theorem representedThickeningIdealGenerator_comp_incl
    (a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
    representedThickeningIdealGenerator h hiso hfo a ≫ siteThickeningIdealIncl h hiso hfo =
      (representedAffineAssociatedObjUnitIso B S hS U').inv ≫
        (representedAffineAssociated B S hS U').map
          ((a : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) •
            𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≫
        (representedAffineAssociatedObjUnitIso B S hS U').hom := by
  have hsub : homFromSelfOfElement (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
        (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom)) a ≫
      ModuleCat.ofHom (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom).subtype =
      (a : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) •
        𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    show ((x • a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) =
        (a : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) • x
    rw [Submodule.coe_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  have hι : (siteThickeningIdealTildeIso h hiso hfo).inv ≫ siteThickeningIdealToTilde h hiso hfo =
      (representedAffineAssociated B S hS U').map
        (ModuleCat.ofHom (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom).subtype) := by
    rw [← siteThickeningIdealTildeIso_hom_comp, Iso.inv_hom_id_assoc]
  have hincl : siteThickeningIdealIncl h hiso hfo =
      siteThickeningIdealToTilde h hiso hfo ≫
        (representedAffineAssociatedObjUnitIso B S hS U').hom := by
    rw [siteThickeningIdealToTilde, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hincl, representedThickeningIdealGenerator, Category.assoc, Category.assoc,
    ← Category.assoc (siteThickeningIdealTildeIso h hiso hfo).inv, hι, ← hsub, Functor.map_comp]
  simp only [Category.assoc]

/-- **The global section of `t^*𝒥` attached to `a ∈ J`**: `𝒪_U ≅ t^*𝒪_{U'}` followed by the
pullback of the generator `𝒪_{U'} ⟶ 𝒥` of multiplication by `a`. -/
def representedThickeningIdealSection
    (a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) ⟶
      (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.obj
        (affineThickeningIdeal h hiso hfo).I :=
  (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toModulesHom).hom ≫
    (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.map
      ((toposAssociatedUnitIso U').inv ≫
        (toposAssociatedFunctor U').map (homFromSelfOfElement _ a) ≫
        (toposThickeningIdealTildeIso h hiso hfo).inv)

/-- **The global section `ā` of `t^*𝒥` is `r ↦ r a` on associated modules.** -/
theorem representedThickeningIdealSection_comp_tildeIsoAux_hom
    (a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
    representedThickeningIdealSection h hiso hfo a ≫
        (representedThickeningIdealTildeIsoAux h hiso hfo hh).hom =
      (toposAssociatedUnitIso U).inv ≫
        (toposAssociatedFunctor U).map (homFromSelfOfElement (thickeningKerModuleCat h hh) a) := by
  have H := generic_section_comp_iso (representedAffineCommRingCatHom B S hS h).hom
    (toposAssociatedFunctor U') (toposAssociatedFunctor U)
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toModulesHom.pullbackModules
    (representedAffineAssociatedPullbackIso B S hS h)
    (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toModulesHom)
    (toposAssociatedUnitIso U') (toposAssociatedUnitIso U)
    (representedAffineAssociatedPullbackIso_hom_app_self B S hS h)
    (toposThickeningIdealTildeIso h hiso hfo)
    (homFromSelfOfElement (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
      (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom)) a)
    (ModuleCat.extendScalarsKerIso _ (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hh)
        (Stacks.Smooth.ker_appTop_sq_eq_bot hh))
    (homFromSelfOfElement (thickeningKerModuleCat h hh) a)
    (ModuleCat.extendScalars_homFromSelfOfElement_kerIso _ _ _ a)
  have e1 : representedThickeningIdealSection h hiso hfo a =
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toModulesHom).hom ≫
      (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.map
        ((toposAssociatedUnitIso U').inv ≫ (toposAssociatedFunctor U').map
          (homFromSelfOfElement (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
            (RingHom.ker (representedAffineCommRingCatHom B S hS h).hom)) a) ≫
          (toposThickeningIdealTildeIso h hiso hfo).inv) := rfl
  have e2 : (representedThickeningIdealTildeIsoAux h hiso hfo hh).hom =
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.mapIso
        (toposThickeningIdealTildeIso h hiso hfo) ≪≫
      (representedAffineAssociatedPullbackIso B S hS h).app _ ≪≫
      (toposAssociatedFunctor U).mapIso
        (ModuleCat.extendScalarsKerIso _
          (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hh)
          (Stacks.Smooth.ker_appTop_sq_eq_bot hh))).hom := rfl
  exact (congrArg₂ (· ≫ ·) e1 e2).trans H

/-- The global section `ā` read through the full identification `t^*𝒥 ≅ J^~`. -/
theorem representedThickeningIdealSection_comp_tildeIso_hom
    (a : RingHom.ker (representedAffineCommRingCatHom B S hS h).hom) :
    (representedThickeningIdealSection h hiso hfo a ≫
        (representedThickeningIdealPullbackSpellingIso h hiso hfo).inv) ≫
        (representedThickeningIdealTildeIso h hiso hfo hh).hom =
      (toposAssociatedUnitIso U).inv ≫
        (toposAssociatedFunctor U).map (homFromSelfOfElement (thickeningKerModuleCat h hh) a) :=
  ((Category.assoc _ _ _).trans
    (congrArg (fun m ↦ representedThickeningIdealSection h hiso hfo a ≫ m)
    (Iso.inv_hom_id_assoc (representedThickeningIdealPullbackSpellingIso h hiso hfo)
      (representedThickeningIdealTildeIsoAux h hiso hfo hh).hom))).trans
    (representedThickeningIdealSection_comp_tildeIsoAux_hom h hiso hfo hh a)

end AffineThickening

section SchemeSpace

variable {U U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (h : U ⟶ U')
  (hiso : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h).hom))
  (hfo : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U')
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h).hom))
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h))

variable (U) in
/-- The associated-module functor on `U`, with values read in the spelling of the small étale
ringed topos of `(schemeSpaceFunctor B S hS).obj U` used by the pulled-back ideals of test
schemes. -/
abbrev schemeAssociatedFunctor :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj U)).O) :=
  representedAffineAssociated B S hS U

variable (U) in
/-- `Γ(U)^~ ≅ 𝒪_U`, in the spelling of `AlgebraicGeometry.Space.schemeAssociatedFunctor`. -/
abbrev schemeAssociatedUnitIso :
    (schemeAssociatedFunctor U).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj U)).O) :=
  representedAffineAssociatedObjUnitIso B S hS U

/-- The associated module on `U` of the kernel `J = Ker(Γ(U') ⟶ Γ(U))`, with its `Γ(U)`-module
structure of a square-zero kernel (`thickeningKerModuleOf`), in the spelling of the small étale
ringed topos of `U` used by the pulled-back ideals of test schemes
(`AlgebraicGeometry.Space.QuotientSituation.testSchemeBasePullbackIdeal`). -/
abbrev thickeningKerTilde :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj U)).O) :=
  (schemeAssociatedFunctor U).obj (thickeningKerModuleOf hh)

/-- **The pulled-back ideal of an affine first order thickening is the associated module of the
kernel.** For `h : U ⟶ U'` with `U, U'` affine whose scheme map is a first order thickening,
`t^*𝒥 ≅ J^~` on the small étale site of `U`, where `𝒥 ⊂ 𝒪_{U'}` is the square-zero ideal of the
first order thickening of small étale ringed topoi and `J = Ker(Γ(U') ⟶ Γ(U))` with the
`Γ(U)`-module structure of a square-zero kernel. -/
def thickeningIdealTildeIso :
    (smallEtaleRingedToposHom B S hS
        ((schemeSpaceFunctor B S hS).map h)).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h)
          hiso hfo).idealOfThickening.I ≅ thickeningKerTilde h hh :=
  representedThickeningIdealTildeIso h hiso hfo hh

/-- **The global section `ā` of `t^*𝒥` attached to `a ∈ J`**: `𝒪_U ≅ t^*𝒪_{U'}` followed by the
pullback of the map `𝒪_{U'} ⟶ 𝒥` whose composite with the inclusion is multiplication by `a`
(`AlgebraicGeometry.Space.representedThickeningIdealGenerator_comp_incl`). -/
def thickeningIdealSection
    (a : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h)).hom) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj U)).O) ⟶
      (smallEtaleRingedToposHom B S hS
        ((schemeSpaceFunctor B S hS).map h)).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h)
          hiso hfo).idealOfThickening.I :=
  representedThickeningIdealSection h hiso hfo a ≫
    (representedThickeningIdealPullbackSpellingIso h hiso hfo).inv

/-- **`ā` is `r ↦ r a` on associated modules**, through `t^*𝒥 ≅ J^~`. -/
theorem thickeningIdealSection_comp_tildeIso_hom
    (a : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h)).hom) :
    thickeningIdealSection h hiso hfo a ≫ (thickeningIdealTildeIso h hiso hfo hh).hom =
      (schemeAssociatedUnitIso U).inv ≫
        (schemeAssociatedFunctor U).map (homFromSelfOfElement (thickeningKerModuleOf hh) a) :=
  representedThickeningIdealSection_comp_tildeIso_hom h hiso hfo hh a

include hh in
/-- **Maps out of `t^*𝒥` are determined by the global sections `ā`, `a ∈ J`.** -/
theorem thickeningIdealHom_ext
    {X : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj U)).O)}
    {φ ψ : (smallEtaleRingedToposHom B S hS
        ((schemeSpaceFunctor B S hS).map h)).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h)
          hiso hfo).idealOfThickening.I ⟶ X}
    (hφψ : ∀ a, thickeningIdealSection h hiso hfo a ≫ φ = thickeningIdealSection h hiso hfo a ≫ ψ) :
    φ = ψ := by
  refine (cancel_epi (thickeningIdealTildeIso h hiso hfo hh).inv).1 ?_
  have adj : schemeAssociatedFunctor U ⊣ representedAffineSections B S hS U :=
    representedAffineAssociatedAdjunction B S hS U
  refine hom_ext_of_adjunction_homFromSelfOfElement adj fun a ↦ ?_
  have hF : (schemeAssociatedFunctor U).map (homFromSelfOfElement (thickeningKerModuleOf hh) a) =
      (schemeAssociatedUnitIso U).hom ≫ thickeningIdealSection h hiso hfo a ≫
        (thickeningIdealTildeIso h hiso hfo hh).hom :=
    (Iso.inv_comp_eq _).1 (thickeningIdealSection_comp_tildeIso_hom h hiso hfo hh a).symm
  have e : ∀ χ : (smallEtaleRingedToposHom B S hS
        ((schemeSpaceFunctor B S hS).map h)).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h)
          hiso hfo).idealOfThickening.I ⟶ X,
      (schemeAssociatedFunctor U).map (homFromSelfOfElement (thickeningKerModuleOf hh) a) ≫
          (thickeningIdealTildeIso h hiso hfo hh).inv ≫ χ =
        (schemeAssociatedUnitIso U).hom ≫ thickeningIdealSection h hiso hfo a ≫ χ := fun χ ↦
    (congrArg (· ≫ (thickeningIdealTildeIso h hiso hfo hh).inv ≫ χ) hF).trans
      ((Category.assoc _ _ _).trans (congrArg ((schemeAssociatedUnitIso U).hom ≫ ·)
        ((Category.assoc _ _ _).trans (congrArg (thickeningIdealSection h hiso hfo a ≫ ·)
          (Iso.hom_inv_id_assoc (thickeningIdealTildeIso h hiso hfo hh) χ)))))
  exact (e φ).trans ((congrArg ((schemeAssociatedUnitIso U).hom ≫ ·) (hφψ a)).trans (e ψ).symm)

end SchemeSpace

section IdealMap

variable {U U'₁ U'₂ U'₃ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₂)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₃)]
  (h₁ : U ⟶ U'₁) (h₂ : U ⟶ U'₂) (h₃ : U ⟶ U'₃) (g : U'₂ ⟶ U'₁) (hg : h₂ ≫ g = h₁)
  (g' : U'₃ ⟶ U'₂) (hg' : h₃ ≫ g' = h₂)
  (hiso₁ : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h₁).hom))
  (hfo₁ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U'₁)
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h₁).hom))
  (hiso₂ : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h₂).hom))
  (hfo₂ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U'₂)
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h₂).hom))
  (hiso₃ : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h₃).hom))
  (hfo₃ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U'₃)
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h₃).hom))
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂))
  (hh₃ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₃))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₂)] in
include hg in
/-- A factorisation `h₂ ≫ g = h₁` under `U` persists on the underlying schemes. -/
theorem toScheme_map_comp_map_eq_of_comp_eq :
    (BigFppfOver.toScheme B S hS).map h₂ ≫ (BigFppfOver.toScheme B S hS).map g =
      (BigFppfOver.toScheme B S hS).map h₁ := by
  rw [← Functor.map_comp, hg]

/-- The map of kernels `J₁ ⟶ J₂` induced by `g : U'₂ ⟶ U'₁` under `U`: the restriction of `g^♯`. -/
abbrev thickeningKerMapOf :
    thickeningKerModuleOf hh₁ ⟶ thickeningKerModuleOf hh₂ :=
  thickeningKerMap hh₁ hh₂ ((BigFppfOver.toScheme B S hS).map g)
    (toScheme_map_comp_map_eq_of_comp_eq h₁ h₂ g hg)

/-- **The map of pulled-back ideals `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂` of a morphism `g : U'₂ ⟶ U'₁` of
affine first order thickenings of `U`.** It is the associated map of the restriction
`J₁ ⟶ J₂` of `g^♯` to the kernels, read through `t_k^*𝒥_k ≅ J_k^~`; on the global sections `ā`
it is `ā ↦ \overline{g^♯ a}` (`thickeningIdealSection_comp_thickeningIdealMap`). -/
def thickeningIdealMap :
    (smallEtaleRingedToposHom B S hS
        ((schemeSpaceFunctor B S hS).map h₁)).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h₁)
          hiso₁ hfo₁).idealOfThickening.I ⟶
      (smallEtaleRingedToposHom B S hS
        ((schemeSpaceFunctor B S hS).map h₂)).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h₂)
          hiso₂ hfo₂).idealOfThickening.I :=
  (thickeningIdealTildeIso h₁ hiso₁ hfo₁ hh₁).hom ≫
    (schemeAssociatedFunctor U).map (thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂) ≫
    (thickeningIdealTildeIso h₂ hiso₂ hfo₂ hh₂).inv

/-- **`λ_g` is the associated map of `J₁ ⟶ J₂`**, through `t_k^*𝒥_k ≅ J_k^~`. -/
theorem thickeningIdealMap_comp_tildeIso_hom :
    thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ ≫
        (thickeningIdealTildeIso h₂ hiso₂ hfo₂ hh₂).hom =
      (thickeningIdealTildeIso h₁ hiso₁ hfo₁ hh₁).hom ≫
        (schemeAssociatedFunctor U).map (thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂) :=
  (Category.assoc _ _ _).trans (congrArg ((thickeningIdealTildeIso h₁ hiso₁ hfo₁ hh₁).hom ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg ((schemeAssociatedFunctor U).map
      (thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂) ≫ ·)
      ((thickeningIdealTildeIso h₂ hiso₂ hfo₂ hh₂).inv_hom_id.trans rfl) |>.trans
        (Category.comp_id _))))

/-- **`λ_g` on the global sections: `ā ↦ \overline{g^♯ a}`.** -/
theorem thickeningIdealSection_comp_thickeningIdealMap
    (a : RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map h₁)).hom) :
    thickeningIdealSection h₁ hiso₁ hfo₁ a ≫
        thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ =
      thickeningIdealSection h₂ hiso₂ hfo₂ ((thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂).hom a) := by
  refine (cancel_mono (thickeningIdealTildeIso h₂ hiso₂ hfo₂ hh₂).hom).1 ?_
  refine ((Category.assoc _ _ _).trans (congrArg (thickeningIdealSection h₁ hiso₁ hfo₁ a ≫ ·)
    (thickeningIdealMap_comp_tildeIso_hom h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (schemeAssociatedFunctor U).map
    (thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂))
    (thickeningIdealSection_comp_tildeIso_hom h₁ hiso₁ hfo₁ hh₁ a))).trans ?_
  refine Eq.trans ?_ (thickeningIdealSection_comp_tildeIso_hom h₂ hiso₂ hfo₂ hh₂ _).symm
  refine (Category.assoc _ _ _).trans (congrArg ((schemeAssociatedUnitIso U).inv ≫ ·) ?_)
  exact ((schemeAssociatedFunctor U).map_comp _ _).symm.trans
    (congrArg (schemeAssociatedFunctor U).map
      (homFromSelfOfElement_comp (M := thickeningKerModuleOf hh₁) (N := thickeningKerModuleOf hh₂) a
        (thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂)))

/-- `λ` of the identity is the identity. -/
theorem thickeningIdealMap_id :
    thickeningIdealMap h₁ h₁ (𝟙 U'₁) (Category.comp_id h₁) hiso₁ hfo₁ hiso₁ hfo₁ hh₁ hh₁ = 𝟙 _ := by
  have hκ : thickeningKerMapOf h₁ h₁ (𝟙 U'₁) (Category.comp_id h₁) hh₁ hh₁ = 𝟙 _ := by
    let := Stacks.Smooth.kerModule (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hh₁)
      (Stacks.Smooth.ker_appTop_sq_eq_bot hh₁)
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
    show (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map (𝟙 U'₁))).hom x = x
    rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
    rfl
  unfold thickeningIdealMap
  rw [hκ, CategoryTheory.Functor.map_id]
  exact (congrArg ((thickeningIdealTildeIso h₁ hiso₁ hfo₁ hh₁).hom ≫ ·) (Category.id_comp _)).trans
    (thickeningIdealTildeIso h₁ hiso₁ hfo₁ hh₁).hom_inv_id

/-- `λ` is compatible with composition. -/
theorem thickeningIdealMap_comp :
    thickeningIdealMap h₁ h₃ (g' ≫ g) (by rw [← Category.assoc, hg', hg]) hiso₁ hfo₁ hiso₃ hfo₃
        hh₁ hh₃ =
      thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ ≫
        thickeningIdealMap h₂ h₃ g' hg' hiso₂ hfo₂ hiso₃ hfo₃ hh₂ hh₃ := by
  have hκ : thickeningKerMapOf h₁ h₃ (g' ≫ g) (by rw [← Category.assoc, hg', hg]) hh₁ hh₃ =
      thickeningKerMapOf h₁ h₂ g hg hh₁ hh₂ ≫ thickeningKerMapOf h₂ h₃ g' hg' hh₂ hh₃ := by
    let := Stacks.Smooth.kerModule (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hh₁)
      (Stacks.Smooth.ker_appTop_sq_eq_bot hh₁)
    let := Stacks.Smooth.kerModule (Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hh₃)
      (Stacks.Smooth.ker_appTop_sq_eq_bot hh₃)
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
    show (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map (g' ≫ g))).hom x =
      (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map g')).hom
        ((Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map g)).hom x)
    rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  unfold thickeningIdealMap
  rw [hκ]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

end IdealMap


end AlgebraicGeometry.Space

end
