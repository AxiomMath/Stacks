module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of associated module sheaves across a morphism of homogeneous spectra

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings whose irrelevant ideals
satisfy `ℬ₊ ≤ 𝒜₊.map φ`, so that `r = AlgebraicGeometry.Proj.map φ : Proj ℬ ⟶ Proj 𝒜` is
defined. Let `𝒨` be a graded `𝒜`-module, `𝒩` a graded `ℬ`-module, and let `f : M → N` be a
`φ`-semilinear map carrying `𝒨 i` into `𝒩 i`. This file constructs the canonical comparison

`r^* M̃ ⟶ Ñ`

of the associated module sheaves of Tag 01M6, as the adjoint of an explicit morphism
`M̃ ⟶ r_* Ñ`: a section of `M̃` over an open `U` is a family of fractions indexed by the points of
`U` that is locally `m / s` with `m` and `s` homogeneous of equal degree, and `f` together with
`φ` localizes each such fraction at the prime below a point of `r^{-1}U`.

## Main definitions

* `Stacks.ProjModuleComparison.fibreMap`: the comparison of module fibres at a homogeneous prime
  of `ℬ` and its preimage, sending `m / s` to `f m / φ s`.
* `Stacks.ProjModuleComparison.sectionFun` and
  `Stacks.ProjModuleComparison.sectionsMap`: the comparison on sections, as a map of fraction
  families and then as a map of the section modules.
* `Stacks.ProjModuleComparison.pushforwardModuleMap`: the adjoint transpose `M̃ ⟶ r_* Ñ`.
* `Stacks.ProjModuleComparison.moduleMap`: the comparison `r^* M̃ ⟶ Ñ` itself.

## Main results

* `Stacks.ProjModuleComparison.notMemComapFun_iff`: an element of `A` avoids the homogeneous
  prime below a point exactly when its image avoids the homogeneous prime at that point.
* `Stacks.ProjModuleComparison.locallyModuleFraction_sectionFun`: the comparison carries a family
  of local homogeneous fractions of `𝒨` to one of `𝒩`.
* `Stacks.ProjModuleComparison.fibreMap_smul` and
  `Stacks.ProjModuleComparison.fibreMap_val_smul`: the fibre comparison is semilinear over the
  structure-sheaf map of `AlgebraicGeometry.Proj.map`.
* `Stacks.ProjModuleComparison.homEquiv_moduleMap`: the adjoint transpose of `moduleMap` is
  `pushforwardModuleMap`.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjModuleComparison

/-- Degrees of a graded ring act on degrees of a graded module over it by addition. -/
local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {A B : Type u} {M N : Type u} {σ τ μ ν : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
  (f : M →ₛₗ[φ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)

/-- An element of `A` avoids the homogeneous prime below `y`
exactly when its image avoids the homogeneous prime at `y`. -/
theorem notMemComapFun_iff (y : ProjectiveSpectrum ℬ) (s : A) :
    s ∉ (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal ↔
      φ s ∉ y.asHomogeneousIdeal :=
  Iff.rfl

/-- The homogeneous prime below `y` is the preimage of the homogeneous prime at `y`. -/
theorem comapFun_toIdeal (y : ProjectiveSpectrum ℬ) :
    (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal =
      y.asHomogeneousIdeal.toIdeal.comap φ.toRingHom := rfl

/-- The multiplicative map on denominators: an element of `A` avoiding the homogeneous prime
below `y` goes to its image in `B`, which avoids the homogeneous prime at `y`. -/
def denomMap (y : ProjectiveSpectrum ℬ) :
    (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl →*
      y.asHomogeneousIdeal.toIdeal.primeCompl where
  toFun s := ⟨φ s, (notMemComapFun_iff φ hφ y s).mp s.2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' _ _ := Subtype.ext (map_mul φ _ _)

/-- The underlying element of a transported denominator is the image of the denominator. -/
@[simp] theorem coe_denomMap (y : ProjectiveSpectrum ℬ)
    (s : (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl) :
    (denomMap φ hφ y s : B) = φ s := rfl

/-- The comparison of module fibres: the fraction `m / s` in the localization of `M` at the
homogeneous prime below `y` goes to the fraction `f m / φ s` in the localization of `N` at `y`. -/
def fibreMap (y : ProjectiveSpectrum ℬ)
    (z : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    ModuleFiber (M := N) ℬ y :=
  LocalizedModule.liftOn z (fun p ↦ LocalizedModule.mk (f p.1) (denomMap φ hφ y p.2)) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine LocalizedModule.mk_eq.mpr ⟨denomMap φ hφ y u, ?_⟩
    simpa only [Submonoid.smul_def, coe_denomMap, map_smulₛₗ,
      GradedRingHom.coe_toRingHom] using congrArg f hu)

/-- The fibre comparison on a fraction: apply `f` to the numerator and `φ` to the denominator. -/
@[simp] theorem fibreMap_mk (y : ProjectiveSpectrum ℬ) (m : M)
    (s : (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl) :
    fibreMap φ hφ f y (LocalizedModule.mk m s) =
      LocalizedModule.mk (f m) (denomMap φ hφ y s) :=
  LocalizedModule.liftOn_mk _ m s

/-- The fibre comparison preserves zero. -/
theorem fibreMap_zero (y : ProjectiveSpectrum ℬ) :
    fibreMap φ hφ f y 0 = 0 := by
  rw [show (0 : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) =
      LocalizedModule.mk 0 1 from (LocalizedModule.zero_mk _).symm,
    fibreMap_mk, map_zero, LocalizedModule.zero_mk]

/-- The fibre comparison is additive. -/
theorem fibreMap_add (y : ProjectiveSpectrum ℬ)
    (z z' : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ f y (z + z') = fibreMap φ hφ f y z + fibreMap φ hφ f y z' := by
  induction z, z' using LocalizedModule.induction_on₂ with
  | h m m' s s' =>
    rw [LocalizedModule.mk_add_mk, fibreMap_mk, fibreMap_mk, fibreMap_mk,
      LocalizedModule.mk_add_mk]
    refine congrArg₂ LocalizedModule.mk ?_ (map_mul (denomMap φ hφ y) s s')
    simp only [Submonoid.smul_def, coe_denomMap, map_add, map_smulₛₗ,
      GradedRingHom.coe_toRingHom]

/-- The fibre comparison is semilinear over the comparison of local rings. -/
theorem fibreMap_smul (y : ProjectiveSpectrum ℬ)
    (u : Localization
      (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl)
    (z : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ f y (u • z) =
      Localization.localRingHom
        (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal
        y.asHomogeneousIdeal.toIdeal φ.toRingHom (comapFun_toIdeal φ hφ y) u •
          fibreMap φ hφ f y z := by
  induction u using Localization.induction_on with
  | H p =>
    induction z using LocalizedModule.induction_on with
    | h m s =>
      rw [Localization.localRingHom_mk, LocalizedModule.mk_smul_mk, fibreMap_mk,
        fibreMap_mk, LocalizedModule.mk_smul_mk]
      refine congrArg₂ LocalizedModule.mk ?_ (Subtype.ext ?_)
      · simp only [map_smulₛₗ, GradedRingHom.coe_toRingHom]
      · simp only [Submonoid.coe_mul, coe_denomMap, map_mul,
          GradedRingHom.coe_toRingHom]

/-- The fibre comparison is semilinear over the comparison of structure-sheaf sections: the
scalar `c` acting over `U` acts, after comparison, as its image under the structure-sheaf map of
`AlgebraicGeometry.Proj.map`. -/
theorem fibreMap_val_smul (U : Opens (ProjectiveSpectrum.top 𝒜))
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U))
    (y : U.comap (ProjectiveSpectrum.comap φ hφ))
    (z : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y.1)) :
    fibreMap φ hφ f y.1 (HomogeneousLocalization.val
        (c.1 (⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ : U)) • z) =
      HomogeneousLocalization.val
        (HomogeneousLocalization.localRingHom φ
          (ProjectiveSpectrum.comapFun φ hφ y.1).asHomogeneousIdeal.toIdeal
          y.1.asHomogeneousIdeal.toIdeal rfl
          (c.1 (⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ : U))) • fibreMap φ hφ f y.1 z := by
  rw [fibreMap_smul]
  exact congrArg (· • fibreMap φ hφ f y.1 z) (HomogeneousLocalization.val_localRingHom
    (c.1 (⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ : U))).symm

/-- The comparison on sections, as a map of dependent functions into the module fibres: a
fraction family on an open of `Proj 𝒜` is carried to one on any open of `Proj ℬ` mapping into
it. -/
def sectionFun (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap φ hφ ⁻¹' U.1)
    (a : ∀ x : U, ModuleFiber (M := M) 𝒜 x.1) (y : V) : ModuleFiber (M := N) ℬ y.1 :=
  fibreMap φ hφ f y.1 (a ⟨ProjectiveSpectrum.comapFun φ hφ y.1, hUV y.2⟩)

omit [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩] in
include hf in
/-- The comparison carries a family of local homogeneous fractions of `𝒨` to one of `𝒩`: a
representative `m / s` with `m ∈ 𝒨 k` and `s ∈ 𝒜 k` goes to `f m / φ s` with `f m ∈ 𝒩 k` and
`φ s ∈ ℬ k`. -/
theorem locallyModuleFraction_sectionFun (U : Opens (ProjectiveSpectrum.top 𝒜))
    (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap φ hφ ⁻¹' U.1)
    (a : ∀ x : U, ModuleFiber (M := M) 𝒜 x.1)
    (ha : (locallyModuleFraction 𝒜 𝒨).pred a) :
    (locallyModuleFraction ℬ 𝒩).pred (sectionFun φ hφ f U V hUV a) := by
  rintro ⟨p, hpV⟩
  obtain ⟨W, hmemW, iWU, k, m, s, hm, hs, hns, hfrac⟩ :=
    ha ⟨ProjectiveSpectrum.comapFun φ hφ p, hUV hpV⟩
  exact ⟨W.comap (ProjectiveSpectrum.comap φ hφ) ⊓ V, ⟨hmemW, hpV⟩, Opens.infLERight _ _,
    k, f m, φ s, hf _ hm, φ.map_mem hs,
    fun y ↦ (notMemComapFun_iff φ hφ y.1 s).mp (hns ⟨_, y.2.1⟩),
    fun y ↦ (congrArg (fibreMap φ hφ f y.1) (hfrac ⟨_, y.2.1⟩)).trans
      (fibreMap_mk φ hφ f y.1 m ⟨s, hns ⟨_, y.2.1⟩⟩)⟩

include hf in
/-- The comparison on the sections of the associated module sheaves over an open and its
preimage. -/
def sectionsMap (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    moduleSections 𝒜 𝒨 U →
      moduleSections ℬ 𝒩 (U.comap (ProjectiveSpectrum.comap φ hφ)) :=
  fun a ↦ ⟨sectionFun φ hφ f U _ Set.Subset.rfl a.1,
    locallyModuleFraction_sectionFun φ hφ f hf U _ Set.Subset.rfl a.1 a.2⟩

/-- The value of the comparison of sections at a point. -/
@[simp] theorem sectionsMap_apply (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : moduleSections 𝒜 𝒨 U) (y : U.comap (ProjectiveSpectrum.comap φ hφ)) :
    (sectionsMap φ hφ f hf U a).1 y = fibreMap φ hφ f y.1 (a.1 ⟨_, y.2⟩) := rfl

include hf in
/-- The comparison morphism `M̃ ⟶ r_* Ñ`, where `r = AlgebraicGeometry.Proj.map φ`. -/
def pushforwardModuleMap :
    associatedModuleSheaf 𝒜 𝒨 ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Proj.map φ hφ)).obj (associatedModuleSheaf ℬ 𝒩) := by
  letI : ∀ U, Module
      (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      ((modulePresheaf 𝒜 𝒨).obj U) :=
    fun U ↦ modulePresheafModule 𝒜 𝒨 U
  letI : ∀ U, Module
      (((ProjectiveSpectrum.Proj.structureSheaf ℬ).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      ((modulePresheaf ℬ 𝒩).obj U) :=
    fun U ↦ modulePresheafModule ℬ 𝒩 U
  exact
    { val :=
        { app := fun U ↦ ConcreteCategory.ofHom
            { toFun := sectionsMap φ hφ f hf U.unop
              map_add' := fun a b ↦ Subtype.ext (funext fun y ↦
                fibreMap_add φ hφ f y.1
                  (a.1 ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩)
                  (b.1 ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩))
              map_smul' := fun c a ↦ Subtype.ext (funext fun y ↦
                fibreMap_val_smul φ hφ f U.unop c y
                  (a.1 ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩)) }
          naturality := fun _ ↦ rfl } }

include hf in
/-- The canonical comparison `r^* M̃ ⟶ Ñ`, where `r = AlgebraicGeometry.Proj.map φ`: the
morphism adjoint to `Stacks.ProjModuleComparison.pushforwardModuleMap`. -/
@[ega "II 8.12.4" "special case"]
def moduleMap :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Proj.map φ hφ)).obj (associatedModuleSheaf 𝒜 𝒨) ⟶
      associatedModuleSheaf ℬ 𝒩 :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Proj.map φ hφ)).homEquiv _ _).symm (pushforwardModuleMap φ hφ f hf)

/-- The adjoint transpose of the comparison `r^* M̃ ⟶ Ñ` is
`Stacks.ProjModuleComparison.pushforwardModuleMap`. -/
theorem homEquiv_moduleMap :
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Proj.map φ hφ)).homEquiv _ _) (moduleMap φ hφ f hf) =
      pushforwardModuleMap φ hφ f hf :=
  Equiv.apply_symm_apply _ _

end Stacks.ProjModuleComparison

end
