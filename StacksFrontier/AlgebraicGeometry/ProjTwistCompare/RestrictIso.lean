module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Chart
public import StacksFrontier.AlgebraicGeometry.SchemeModuleGlue.Chart
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Psi
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Basic
public import StacksFrontier.AlgebraicGeometry.TwistDataConstruction.Absolute
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection

/-!
# The comparison on twists along an isomorphism of homogeneous spectra, as a restriction

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings defined everywhere on
`Proj ℬ`, inducing an isomorphism `c = Proj.map ψ : Proj ℬ ⟶ Proj 𝒜`, and suppose the comparison
maps `θ_n` of Tag 01MY on the twists are isomorphisms. Then `c` identifies the twists: the
restriction of `𝒪_{Proj 𝒜}(n)` along `c` is `𝒪_{Proj ℬ}(n)`. This file builds that isomorphism in
the form the glueing of relative twists consumes — a morphism of sheaves out of a *restriction*,
whose sections are those of `𝒪_{Proj 𝒜}(n)` over the image — and computes it on sections: a local
section is sent fibre by fibre by `a / s ↦ ψ a / ψ s`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistCompare.restrictTwistIso`: **the isomorphism
  `c^{-1}𝒪_{Proj 𝒜}(n) ≅ 𝒪_{Proj ℬ}(n)`**, the adjoint along `c` of Tag 01MY's comparison.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.restrictTwistIso_hom_app`: it is the fibrewise
  comparison of `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`, restricted.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.restrictTwistIso_mul`: it carries the canonical
  product of absolute twist sections to the canonical product.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.restrictTwistIso_degreeSection`: it carries the
  homogeneous section of `a` to the homogeneous section of `ψ a`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.ProjTwistCompare

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
  (hdom : mapDomain 𝒜 ℬ ψ = ⊤)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
include hdom in
/-- The inclusion of the domain of definition is the inverse of the identification used to define
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`, when the domain is everything. -/
public theorem mapDomain_ι_eq_inv :
    (mapDomain 𝒜 ℬ ψ).ι =
      inv ((Scheme.topIso _).inv ≫ ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom) :=
  IsIso.eq_inv_of_hom_inv_id (by
    rw [Category.assoc]
    exact RelativeProj.topIso_inv_isoOfEq_hom_ι 𝒜 ℬ ψ hdom)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
include hdom in
/-- The inclusion of the domain of definition is an isomorphism when it is everything. -/
public theorem isIso_mapDomain_ι : IsIso (mapDomain 𝒜 ℬ ψ).ι := by
  rw [mapDomain_ι_eq_inv 𝒜 ℬ ψ hdom]
  infer_instance

include hdom in
/-- The glued morphism is the inclusion followed by `Proj.map ψ`. -/
public theorem mapHom_eq_ι_comp :
    mapHom 𝒜 ℬ ψ = (mapDomain 𝒜 ℬ ψ).ι ≫ AlgebraicGeometry.Proj.map ψ hψ := by
  rw [← RelativeProj.mapHomOfTop_eq_map 𝒜 ℬ ψ hψ hdom, RelativeProj.mapHomOfTop,
    mapDomain_ι_eq_inv 𝒜 ℬ ψ hdom, ← Category.assoc (Scheme.topIso _).inv,
    IsIso.inv_hom_id_assoc]

/-- The unit of restriction along an open immersion is an isomorphism when the image of every
inverse image is the open itself. -/
private theorem isIso_restrictAdjunction_unit_app_of_image_preimage {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (hv : ∀ V : Y.Opens, f ''ᵁ (f ⁻¹ᵁ V) = V) (M : Y.Modules) :
    IsIso ((Scheme.Modules.restrictAdjunction f).unit.app M) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have : IsIso (homOfLE (f.image_preimage_le V)) := homOfLE_isIso_of_eq _ (hv V)
  have : IsIso (homOfLE (f.image_preimage_le V)).op := CategoryTheory.isIso_op _
  exact Functor.map_isIso M.presheaf _

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
include hdom in
/-- The unit of restriction along the inclusion of the domain of definition is an isomorphism,
the domain being everything. -/
public theorem isIso_restrictAdjunction_unit_app (M : (AlgebraicGeometry.Proj ℬ).Modules) :
    IsIso ((Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app M) :=
  isIso_restrictAdjunction_unit_app_of_image_preimage _ (fun V => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, hdom,
      top_inf_eq]) M

/-! ### The comparison as a morphism out of a restriction -/

/-- A composite of morphisms of sheaves of modules, on sections. -/
theorem sheafComp_val_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : _root_.SheafOfModules.{u} R} (φ : M ⟶ N) (φ' : N ⟶ P)
    (U : Cᵒᵖ) (s : M.val.obj U) :
    (φ ≫ φ').val.app U s = φ'.val.app U (φ.val.app U s) :=
  rfl

include hdom in
/-- The inverse of the unit of restriction along the inclusion of the domain of definition. -/
public def invUnit (n : ℤ) :
    (Scheme.Modules.pushforward (mapDomain 𝒜 ℬ ψ).ι).obj
        ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) ⟶
      twistingSheaf ℬ n :=
  @inv _ _ _ _ ((Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
    (twistingSheaf ℬ n)) (isIso_restrictAdjunction_unit_app 𝒜 ℬ ψ hdom (twistingSheaf ℬ n))

/-- The inverse of the unit of restriction along the inclusion of the domain of definition is an
isomorphism. -/
public instance isIso_invUnit (n : ℤ) : IsIso (invUnit 𝒜 ℬ ψ hdom n) :=
  @IsIso.inv_isIso _ _ _ _ _ (isIso_restrictAdjunction_unit_app 𝒜 ℬ ψ hdom (twistingSheaf ℬ n))

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The inverse of the unit is a restriction map, on sections. -/
public theorem invUnit_app (n : ℤ) (V : (AlgebraicGeometry.Proj ℬ).Opens)
    (hV : V ≤ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ V))
    (y : (twistingSheaf ℬ n).val.obj
      (op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ V)))) :
    (invUnit 𝒜 ℬ ψ hdom n).val.app (op V) y =
      (twistingSheaf ℬ n).val.map (homOfLE hV).op y := by
  have hI := isIso_restrictAdjunction_unit_app 𝒜 ℬ ψ hdom (twistingSheaf ℬ n)
  have hinj : Function.Injective
      (((Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
        (twistingSheaf ℬ n)).val.app (op V)) := fun a b hab =>
    (TwistRigidity.iso_inv_app_hom_app (@asIso _ _ _ _ _ hI) (op V) a).symm.trans
      ((congrArg _ hab).trans (TwistRigidity.iso_inv_app_hom_app (@asIso _ _ _ _ _ hI) (op V) b))
  refine hinj ((TwistRigidity.iso_hom_app_inv_app (@asIso _ _ _ _ _ hI) (op V) y).trans ?_)
  exact (PresheafOfModules.map_map_eq_self (twistingSheaf ℬ n).val (homOfLE hV).op
    (homOfLE ((mapDomain 𝒜 ℬ ψ).ι.image_preimage_le V)).op y).symm

section Restrict

variable [IsIso (AlgebraicGeometry.Proj.map ψ hψ)]

/-- **The adjoint form of the comparison, pushed into `Proj.map ψ`**:
`𝒪_{Proj 𝒜}(n) ⟶ (Proj.map ψ)_* 𝒪_{Proj ℬ}(n)`. It is
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`, followed by the identification of
the direct image along the glued morphism with the direct image along `Proj.map ψ`, the domain of
definition being everything. -/
public def twistPushMap (n : ℤ) :
    twistingSheaf 𝒜 n ⟶
      (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf ℬ n) :=
  twistPushforwardMap 𝒜 ℬ ψ n ≫
    (Scheme.Modules.pushforwardCongr (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)).hom.app _ ≫
    (Scheme.Modules.pushforwardComp (mapDomain 𝒜 ℬ ψ).ι
      (AlgebraicGeometry.Proj.map ψ hψ)).inv.app _ ≫
    (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map (invUnit 𝒜 ℬ ψ hdom n)

/-- **The comparison on the `n`-th twist along `Proj.map ψ`, as a morphism out of the
restriction**: the adjoint, for the restriction–pushforward adjunction along the open immersion
`Proj.map ψ`, of `twistPushMap`. -/
public def restrictTwistMap (n : ℤ) :
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf 𝒜 n) ⟶
      twistingSheaf ℬ n :=
  ((Scheme.Modules.restrictAdjunction (AlgebraicGeometry.Proj.map ψ hψ)).homEquiv _ _).symm
    (twistPushMap 𝒜 ℬ ψ hψ hdom n)

end Restrict

/-! ### Invertibility -/

/-- The unit of the restriction--pushforward adjunction along an isomorphism of schemes is an
isomorphism. -/
public theorem isIso_restrictAdjunction_unit_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (M : Y.Modules) : IsIso ((Scheme.Modules.restrictAdjunction f).unit.app M) :=
  isIso_restrictAdjunction_unit_app_of_image_preimage f (fun V => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso,
      top_inf_eq]) M

/-- The unit of the pullback--pushforward adjunction along an isomorphism of schemes is an
isomorphism. -/
alias isIso_pullbackAdjunction_unit_of_isIso :=
  Stacks.AlgebraicGeometry.RelativeProjChain.isIso_pullbackPushforwardAdjunction_unit_app

section Iso

variable [IsIso (AlgebraicGeometry.Proj.map ψ hψ)]

include hψ hdom in
/-- The glued morphism is an isomorphism. -/
public theorem isIso_mapHom : IsIso (mapHom 𝒜 ℬ ψ) := by
  have := isIso_mapDomain_ι 𝒜 ℬ ψ hdom
  rw [mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom]
  infer_instance

include hψ hdom in
/-- The adjoint form of the comparison is an isomorphism once the comparison is. -/
public theorem isIso_twistPushforwardMap (n : ℤ) [IsIso (twistMap 𝒜 ℬ ψ n)] :
    IsIso (twistPushforwardMap 𝒜 ℬ ψ n) := by
  have := isIso_mapHom 𝒜 ℬ ψ hψ hdom
  have h1 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _).symm
      (twistPushforwardMap 𝒜 ℬ ψ n)) := by
    have h := (inferInstance : IsIso (twistMap 𝒜 ℬ ψ n))
    unfold twistMap at h
    have : IsIso ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (twistingSheaf ℬ n)) :=
      inferInstanceAs (IsIso ((Scheme.Modules.restrictFunctorIsoPullback
        (mapDomain 𝒜 ℬ ψ).ι).app (twistingSheaf ℬ n)).hom)
    exact IsIso.of_isIso_comp_right _
      ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (twistingSheaf ℬ n))
  have h2 := isIso_pullbackAdjunction_unit_of_isIso (mapHom 𝒜 ℬ ψ) (twistingSheaf 𝒜 n)
  have e := (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _
    ).apply_symm_apply (twistPushforwardMap 𝒜 ℬ ψ n)).symm.trans
    ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv_unit _ _ _)
  rw [e]
  have h3 := Functor.map_isIso (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ))
    (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _).symm
      (twistPushforwardMap 𝒜 ℬ ψ n))
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3

include hψ hdom in
/-- The pushed comparison `twistPushMap` is an isomorphism once the comparison is. -/
public theorem isIso_twistPushMap (n : ℤ) [IsIso (twistMap 𝒜 ℬ ψ n)] :
    IsIso (twistPushMap 𝒜 ℬ ψ hψ hdom n) := by
  have h0 := isIso_twistPushforwardMap 𝒜 ℬ ψ hψ hdom n
  have h1 : IsIso ((Scheme.Modules.pushforwardCongr (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)).hom.app
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforwardCongr
      (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)).app _).hom)
  have h2 : IsIso ((Scheme.Modules.pushforwardComp (mapDomain 𝒜 ℬ ψ).ι
      (AlgebraicGeometry.Proj.map ψ hψ)).inv.app
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforwardComp (mapDomain 𝒜 ℬ ψ).ι
      (AlgebraicGeometry.Proj.map ψ hψ)).app _).inv)
  have h3 := Functor.map_isIso (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ))
    (invUnit 𝒜 ℬ ψ hdom n)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h0
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3))

include hψ hdom in
/-- `restrictTwistMap` is an isomorphism once the comparison is: it is the restriction of
`twistPushMap` followed by the counit of restriction along an open immersion. -/
public theorem isIso_restrictTwistMap (n : ℤ) [IsIso (twistMap 𝒜 ℬ ψ n)] :
    IsIso (restrictTwistMap 𝒜 ℬ ψ hψ hdom n) := by
  have h0 := isIso_twistPushMap 𝒜 ℬ ψ hψ hdom n
  have e := (Scheme.Modules.restrictAdjunction (AlgebraicGeometry.Proj.map ψ hψ)).homEquiv_counit
    (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistPushMap 𝒜 ℬ ψ hψ hdom n)
  unfold restrictTwistMap
  rw [e]
  have h1 := @Functor.map_isIso _ _ _ _ _ _
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.map ψ hψ))
    (twistPushMap 𝒜 ℬ ψ hψ hdom n) h0
  have h2 : IsIso ((Scheme.Modules.restrictAdjunction (AlgebraicGeometry.Proj.map ψ hψ)).counit.app
      (twistingSheaf ℬ n)) :=
    NatIso.isIso_app_of_isIso (Scheme.Modules.restrictAdjunction
      (AlgebraicGeometry.Proj.map ψ hψ)).counit _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- **The isomorphism `c^{-1}𝒪_{Proj 𝒜}(n) ≅ 𝒪_{Proj ℬ}(n)`** along `c = Proj.map ψ`, for `ψ`
defined everywhere on `Proj ℬ` with `c` and every comparison `θ_n` of Tag 01MY isomorphisms. -/
public def restrictTwistIso (hθ : ∀ n : ℤ, IsIso (twistMap 𝒜 ℬ ψ n)) (n : ℤ) :
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf 𝒜 n) ≅
      twistingSheaf ℬ n :=
  haveI := hθ n
  @asIso _ _ _ _ (restrictTwistMap 𝒜 ℬ ψ hψ hdom n) (isIso_restrictTwistMap 𝒜 ℬ ψ hψ hdom n)

/-- The forward map of `restrictTwistIso` is `restrictTwistMap`. -/
public theorem restrictTwistIso_hom (hθ : ∀ n : ℤ, IsIso (twistMap 𝒜 ℬ ψ n)) (n : ℤ) :
    (restrictTwistIso 𝒜 ℬ ψ hψ hdom hθ n).hom = restrictTwistMap 𝒜 ℬ ψ hψ hdom n :=
  rfl

end Iso

/-- An open of `Proj ℬ` inside the inverse image under `Proj.map ψ` of `U` lies inside the image,
under the inclusion of the domain of definition, of the inverse image of `U` under the glued
morphism. -/
private theorem le_image_preimage_of_le_preimage (hdom : mapDomain 𝒜 ℬ ψ = ⊤)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    {W : (AlgebraicGeometry.Proj ℬ).Opens} (h : W ≤ AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ U) :
    W ≤ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) := by
  intro x hx
  refine ⟨⟨x, hdom ▸ trivial⟩, ?_, rfl⟩
  rw [mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom]
  exact h hx

/-! ### On sections -/

section Sections

variable [IsIso (AlgebraicGeometry.Proj.map ψ hψ)]

include hdom in
/-- An open of `Proj ℬ` is inside the image, under the inclusion of the domain of definition, of
the inverse image under the glued morphism of its image under `Proj.map ψ`. -/
public theorem le_image_preimage_image (W : (AlgebraicGeometry.Proj ℬ).Opens) :
    W ≤ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ
      (mapHom 𝒜 ℬ ψ ⁻¹ᵁ (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W)) :=
  le_image_preimage_of_le_preimage 𝒜 ℬ ψ hψ hdom _ fun x hx => ⟨x, hx, rfl⟩


omit [IsIso (AlgebraicGeometry.Proj.map ψ hψ)] in
include hdom in
/-- The inverse image under `Proj.map ψ` of an open of `Proj 𝒜` lies inside the image, under the
inclusion of the domain of definition, of its inverse image under the glued morphism. -/
public theorem preimage_le_image_preimage (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ U ≤ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) :=
  le_image_preimage_of_le_preimage 𝒜 ℬ ψ hψ hdom U le_rfl

/-- The identification of the direct images along equal morphisms, on sections. -/
public theorem pushforwardCongr_hom_app_val {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    (M : X.Modules) (U : Y.Opens) (y : M.val.obj (op (f ⁻¹ᵁ U))) :
    ((Scheme.Modules.pushforwardCongr hf).hom.app M).val.app (op U) y =
      M.val.map (eqToHom (hf ▸ rfl : g ⁻¹ᵁ U = f ⁻¹ᵁ U)).op y := by
  subst hf
  exact congrArg (fun k => (ConcreteCategory.hom k) y)
    (Scheme.Modules.pushforwardCongr_hom_app_app (M := M) (rfl : f = f) U)

omit [IsIso (AlgebraicGeometry.Proj.map ψ hψ)] in
/-- `twistPushMap` on sections, as the composite of its four factors. -/
public theorem twistPushMap_app_eq (n : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (x : (twistingSheaf 𝒜 n).val.obj (op U)) :
    (twistPushMap 𝒜 ℬ ψ hψ hdom n).val.app (op U) x =
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map
        (invUnit 𝒜 ℬ ψ hdom n)).val.app (op U)
      (((Scheme.Modules.pushforwardComp (mapDomain 𝒜 ℬ ψ).ι
          (AlgebraicGeometry.Proj.map ψ hψ)).inv.app
          ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))).val.app
        (op U)
      (((Scheme.Modules.pushforwardCongr (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)).hom.app
          ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))).val.app
        (op U) ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U) x))) :=
  rfl

/-- The direct image of a morphism, on sections. -/
public theorem pushforward_map_val_app {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : X.Modules}
    (φ : M ⟶ N) (U : Y.Opens) (y : M.val.obj (op (f ⁻¹ᵁ U))) :
    ((Scheme.Modules.pushforward f).map φ).val.app (op U) y = φ.val.app (op (f ⁻¹ᵁ U)) y :=
  rfl

/-- The inverse of the composition isomorphism of direct images, on sections. -/
public theorem pushforwardComp_inv_val_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) (U : Z.Opens) (y : M.val.obj (op ((f ≫ g) ⁻¹ᵁ U))) :
    ((Scheme.Modules.pushforwardComp f g).inv.app M).val.app (op U) y = y :=
  rfl

/-- The restriction maps of a restriction along an open immersion. -/
public theorem restrict_val_map {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) {V V' : X.Opens} (i : V' ⟶ V) (y : M.val.obj (op (j ''ᵁ V))) :
    ((Scheme.Modules.restrictFunctor j).obj M).val.map i.op y =
      M.val.map (j.opensFunctor.map i).op y :=
  rfl

/-- Two restriction maps compose to the restriction map along the composite inclusion. -/
public theorem map_map_eq {X : TopCat.{u}} {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{u} R) {O₁ O₂ O₃ : Opens X}
    (a : op O₁ ⟶ op O₂) (b : op O₂ ⟶ op O₃) (d : op O₁ ⟶ op O₃) (y : N.obj (op O₁)) :
    N.map b (N.map a y) = N.map d y :=
  (PresheafOfModules.map_comp_apply N a b y).symm.trans
    (PresheafOfModules.congr_map_apply N (Subsingleton.elim (a ≫ b) d) y)

/-- Three restriction maps compose to the restriction map along the composite inclusion. -/
public theorem map_map_map_eq {X : TopCat.{u}} {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{u} R) {O₁ O₂ O₃ O₄ : Opens X}
    (a : op O₁ ⟶ op O₂) (b : op O₂ ⟶ op O₃) (c : op O₃ ⟶ op O₄) (d : op O₁ ⟶ op O₄)
    (y : N.obj (op O₁)) :
    N.map c (N.map b (N.map a y)) = N.map d y :=
  (congrArg (N.map c) (map_map_eq N a b (a ≫ b) y)).trans (map_map_eq N (a ≫ b) c d y)

omit [IsIso (AlgebraicGeometry.Proj.map ψ hψ)] in
/-- **`twistPushMap` on sections**: the adjoint comparison, restricted. -/
public theorem twistPushMap_app (n : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (x : (twistingSheaf 𝒜 n).val.obj (op U)) :
    (twistPushMap 𝒜 ℬ ψ hψ hdom n).val.app (op U) x =
      (twistingSheaf ℬ n).val.map (homOfLE (preimage_le_image_preimage 𝒜 ℬ ψ hψ hdom U)).op
        ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U) x) := by
  have hV : AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ U ≤ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ
      ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ (AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ U)) := by
    intro x hx
    exact ⟨⟨x, hdom ▸ trivial⟩, hx, rfl⟩
  refine (twistPushMap_app_eq 𝒜 ℬ ψ hψ hdom n U x).trans ?_
  refine (pushforward_map_val_app (AlgebraicGeometry.Proj.map ψ hψ) (invUnit 𝒜 ℬ ψ hdom n) U
    _).trans ?_
  refine (congrArg ((invUnit 𝒜 ℬ ψ hdom n).val.app (op (AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ U)))
    (pushforwardComp_inv_val_app (mapDomain 𝒜 ℬ ψ).ι (AlgebraicGeometry.Proj.map ψ hψ)
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) U
      _)).trans ?_
  refine (congrArg ((invUnit 𝒜 ℬ ψ hdom n).val.app (op (AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ U)))
    (pushforwardCongr_hom_app_val (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) U
      ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U) x))).trans ?_
  refine (invUnit_app 𝒜 ℬ ψ hdom n _ hV _).trans ?_
  refine (congrArg ((twistingSheaf ℬ n).val.map (homOfLE hV).op)
    (restrict_val_map (mapDomain 𝒜 ℬ ψ).ι (twistingSheaf ℬ n)
      (eqToHom (congrArg (fun φ => φ ⁻¹ᵁ U) (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)).symm)
      ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U) x))).trans ?_
  exact map_map_eq (twistingSheaf ℬ n).val
    ((mapDomain 𝒜 ℬ ψ).ι.opensFunctor.map
      (eqToHom (congrArg (fun φ => φ ⁻¹ᵁ U) (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)).symm)).op
    (homOfLE hV).op (homOfLE (preimage_le_image_preimage 𝒜 ℬ ψ hψ hdom U)).op
    ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U) x)

/-- The restriction of a morphism into a direct image followed by the counit, on sections. -/
public theorem restrictCounit_comp_val_app {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward j).obj N)
    (W : X.Opens) (x : M.val.obj (op (j ''ᵁ W))) :
    ((Scheme.Modules.restrictFunctor j).map φ ≫
        (Scheme.Modules.restrictAdjunction j).counit.app N).val.app (op W) x =
      N.val.map (eqToHom (j.preimage_image_eq W).symm).op (φ.val.app (op (j ''ᵁ W)) x) :=
  rfl

/-- **`restrictTwistMap` on sections**: over an open `W` of `Proj ℬ`, a section of
`𝒪_{Proj 𝒜}(n)` over the image of `W` goes to the restriction to `W` of its image under the
adjoint comparison `twistPushforwardMap`. -/
public theorem restrictTwistMap_app (n : ℤ) (W : (AlgebraicGeometry.Proj ℬ).Opens)
    (x : (twistingSheaf 𝒜 n).val.obj (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W))) :
    (restrictTwistMap 𝒜 ℬ ψ hψ hdom n).val.app (op W) x =
      (twistingSheaf ℬ n).val.map (homOfLE (le_image_preimage_image 𝒜 ℬ ψ hψ hdom W)).op
        ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W)) x) := by
  have e := (Scheme.Modules.restrictAdjunction (AlgebraicGeometry.Proj.map ψ hψ)).homEquiv_counit
    (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistPushMap 𝒜 ℬ ψ hψ hdom n)
  have e1 := congrArg (fun φ : (Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf 𝒜 n) ⟶ twistingSheaf ℬ n =>
    φ.val.app (op W) x) e
  refine e1.trans ?_
  refine (restrictCounit_comp_val_app (AlgebraicGeometry.Proj.map ψ hψ)
    (twistPushMap 𝒜 ℬ ψ hψ hdom n) W x).trans ?_
  refine (congrArg ((twistingSheaf ℬ n).val.map
      (eqToHom ((AlgebraicGeometry.Proj.map ψ hψ).preimage_image_eq W).symm).op)
    (twistPushMap_app 𝒜 ℬ ψ hψ hdom n _ x)).trans ?_
  exact map_map_eq (twistingSheaf ℬ n).val _ _ _ _

/-- **`restrictTwistMap` carries the canonical product of absolute twist sections to the canonical
product.** -/
public theorem restrictTwistMap_mul (i j : ℤ) (W : (AlgebraicGeometry.Proj ℬ).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W)))
    (b : (twistingSheaf 𝒜 j).val.obj (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W))) :
    (restrictTwistMap 𝒜 ℬ ψ hψ hdom (i + j)).val.app (op W)
        (RelativeProjTwists.absoluteTwistProduct 𝒜 i j (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W)
          a b) =
      RelativeProjTwists.absoluteTwistProduct ℬ i j W
        ((restrictTwistMap 𝒜 ℬ ψ hψ hdom i).val.app (op W) a)
        ((restrictTwistMap 𝒜 ℬ ψ hψ hdom j).val.app (op W) b) := by
  refine (restrictTwistMap_app 𝒜 ℬ ψ hψ hdom (i + j) W _).trans ?_
  refine (congrArg ((twistingSheaf ℬ (i + j)).val.map
      (homOfLE (le_image_preimage_image 𝒜 ℬ ψ hψ hdom W)).op)
    (ThetaMultiplicative.twistPushforwardMap_absoluteTwistProduct 𝒜 ℬ ψ i j _ a b)).trans ?_
  refine (TwistDataConstruction.twistProd_naturality ℬ i j
    (homOfLE (le_image_preimage_image 𝒜 ℬ ψ hψ hdom W)).op _ _).trans ?_
  exact congrArg₂ (RelativeProjTwists.absoluteTwistProduct ℬ i j W)
    (restrictTwistMap_app 𝒜 ℬ ψ hψ hdom i W a).symm
    (restrictTwistMap_app 𝒜 ℬ ψ hψ hdom j W b).symm

/-- **`restrictTwistMap` carries the homogeneous section attached to `a` to the homogeneous section
attached to `ψ a`**, restricted to any open. -/
public theorem restrictTwistMap_degreeSection (k : ℕ) (a : 𝒜 k)
    (W : (AlgebraicGeometry.Proj ℬ).Opens) :
    (restrictTwistMap 𝒜 ℬ ψ hψ hdom k).val.app (op W)
        ((twistingSheaf 𝒜 k).val.map (homOfLE le_top).op (degreeSection 𝒜 k a)) =
      (twistingSheaf ℬ k).val.map (homOfLE le_top).op
        (degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩) := by
  refine (restrictTwistMap_app 𝒜 ℬ ψ hψ hdom k W _).trans ?_
  refine (congrArg ((twistingSheaf ℬ k).val.map
      (homOfLE (le_image_preimage_image 𝒜 ℬ ψ hψ hdom W)).op)
    (PresheafOfModules.naturality_apply (twistPushforwardMap 𝒜 ℬ ψ k).val
      (homOfLE (le_top : AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W ≤ ⊤)).op
      (degreeSection 𝒜 k a))).trans ?_
  refine (congrArg (fun z => (twistingSheaf ℬ k).val.map
      (homOfLE (le_image_preimage_image 𝒜 ℬ ψ hψ hdom W)).op
      (((Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
        ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ k))).val.map
        (homOfLE (le_top : AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W ≤ ⊤)).op z))
    (ProjTwistTheta.twistPushforwardMap_degreeSection 𝒜 ℬ ψ k a)).trans ?_
  exact map_map_map_eq (twistingSheaf ℬ k).val _ _ _ _ _

variable (hθ : ∀ n : ℤ, IsIso (twistMap 𝒜 ℬ ψ n))

/-- **`restrictTwistIso` on sections**. -/
public theorem restrictTwistIso_hom_app (n : ℤ) (W : (AlgebraicGeometry.Proj ℬ).Opens)
    (x : (twistingSheaf 𝒜 n).val.obj (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W))) :
    (restrictTwistIso 𝒜 ℬ ψ hψ hdom hθ n).hom.val.app (op W) x =
      (twistingSheaf ℬ n).val.map (homOfLE (le_image_preimage_image 𝒜 ℬ ψ hψ hdom W)).op
        ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W)) x) :=
  restrictTwistMap_app 𝒜 ℬ ψ hψ hdom n W x

/-- **`restrictTwistIso` carries the canonical product to the canonical product.** -/
public theorem restrictTwistIso_mul (i j : ℤ) (W : (AlgebraicGeometry.Proj ℬ).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W)))
    (b : (twistingSheaf 𝒜 j).val.obj (op (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W))) :
    (restrictTwistIso 𝒜 ℬ ψ hψ hdom hθ (i + j)).hom.val.app (op W)
        (RelativeProjTwists.absoluteTwistProduct 𝒜 i j (AlgebraicGeometry.Proj.map ψ hψ ''ᵁ W)
          a b) =
      RelativeProjTwists.absoluteTwistProduct ℬ i j W
        ((restrictTwistIso 𝒜 ℬ ψ hψ hdom hθ i).hom.val.app (op W) a)
        ((restrictTwistIso 𝒜 ℬ ψ hψ hdom hθ j).hom.val.app (op W) b) :=
  restrictTwistMap_mul 𝒜 ℬ ψ hψ hdom i j W a b

/-- **`restrictTwistIso` carries the homogeneous section of `a` to that of `ψ a`.** -/
public theorem restrictTwistIso_degreeSection (k : ℕ) (a : 𝒜 k)
    (W : (AlgebraicGeometry.Proj ℬ).Opens) :
    (restrictTwistIso 𝒜 ℬ ψ hψ hdom hθ k).hom.val.app (op W)
        ((twistingSheaf 𝒜 k).val.map (homOfLE le_top).op (degreeSection 𝒜 k a)) =
      (twistingSheaf ℬ k).val.map (homOfLE le_top).op
        (degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩) :=
  restrictTwistMap_degreeSection 𝒜 ℬ ψ hψ hdom k a W

end Sections

end Stacks.AlgebraicGeometry.ProjTwistCompare

end
