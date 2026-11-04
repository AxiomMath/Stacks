module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom

/-!
# The completion of the internal hom, at the module universe of the schemes

`AlgebraicGeometry.Space.smallEtaleInternalHomSmall M N` is the internal hom `𝓗om(M, N)` of two
`𝒪_F`-modules whose sections live in the universe of the schemes; its universe lift is
`AlgebraicGeometry.Space.smallEtaleInternalHom M N`. This file builds, for it, the comparison of
the inverse system `𝓗 / 𝓘 ^ n 𝓗` with the internal homs into `N / 𝓘 ^ n N`, and identifies the
inverse limit of the global sections of the latter with the morphisms of inverse systems
`(M / 𝓘 ^ n M) ⟶ (N / 𝓘 ^ n N)`, as
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom` does for the universe lift.

## Main definitions

* `AlgebraicGeometry.Space.C1573.smallEtaleInternalHomSmallMapRight`: postcomposition.
* `AlgebraicGeometry.Space.C1573.smallEtaleInternalHomSmallAdicComparisonApp`: the comparison
  `𝓗 / 𝓘 ^ (n + 1) 𝓗 ⟶ 𝓗om(M, N / 𝓘 ^ (n + 1) N)`.
* `AlgebraicGeometry.Space.C1573.smallEtaleInternalHomSmallAdicEquivOfBijective`: if the
  comparison on inverse limits is bijective on every chart, the identification of the inverse
  limit of the global sections of `𝓗 / 𝓘 ^ n 𝓗` with the morphisms of inverse systems
  `(M / 𝓘 ^ n M) ⟶ (N / 𝓘 ^ n N)`.

## Main results

* `AlgebraicGeometry.Space.C1573.smallEtaleInternalHomSmallShrink_mapRight`: postcomposition on
  the sections, read in the universe lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SheafOfModules.C1573

universe w v₁ u₁ m t

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  (N : _root_.SheafOfModules.{max m t} R) [∀ X, Small.{m} (N.val.obj X)]

/-- The restriction maps of `Stacks.SheafOfModules.sheafShrink N` are those of `N`. -/
theorem sheafShrink_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (sheafShrink.{m, t} R N).val.obj X) :
    Shrink.addEquiv ((sheafShrink.{m, t} R N).val.map f x) =
      N.val.map f (Shrink.addEquiv x) :=
  shrinkPresheaf_map_apply N.val.presheaf f x

end Stacks.SheafOfModules.C1573

namespace AlgebraicGeometry.Space.C1573

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Postcomposition with a morphism of `𝒪_F`-modules, as a morphism of internal homs at the
module universe of the schemes. -/
def smallEtaleInternalHomSmallMapRight (M : Modules.{u, u} B S hS F hF)
    {N N' : Modules.{u, u} B S hS F hF} (f : N ⟶ N') :
    smallEtaleInternalHomSmall B S hS F hF M N ⟶ smallEtaleInternalHomSmall B S hS F hF M N' :=
  (RingedSite.internalHomSheafSmallFunctor (smallEtaleRingedSite B S hS F hF) M).map f

/-- Postcomposition with a composite is the composite of the postcompositions. -/
theorem smallEtaleInternalHomSmallMapRight_comp (M : Modules.{u, u} B S hS F hF)
    {N N' N'' : Modules.{u, u} B S hS F hF} (f : N ⟶ N') (g : N' ⟶ N'') :
    smallEtaleInternalHomSmallMapRight B S hS F hF M (f ≫ g) =
      smallEtaleInternalHomSmallMapRight B S hS F hF M f ≫
        smallEtaleInternalHomSmallMapRight B S hS F hF M g :=
  (RingedSite.internalHomSheafSmallFunctor (smallEtaleRingedSite B S hS F hF) M).map_comp f g

/-- The sections of the small internal hom over a chart are those of its universe lift. -/
def smallEtaleInternalHomSmallShrink (M N : Modules.{u, u} B S hS F hF)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) :
    (smallEtaleInternalHomSmall B S hS F hF M N).val.obj U ≃+
      (smallEtaleInternalHom B S hS F hF M N).val.obj U :=
  haveI : Small.{u} ((smallEtaleInternalHom B S hS F hF M N).val.obj U) :=
    RingedSite.small_internalHomSheaf_obj (smallEtaleRingedSite B S hS F hF) M N U
  Shrink.addEquiv (α := ((smallEtaleInternalHom B S hS F hF M N).val.obj U))

/-- Postcomposition on the small internal hom is postcomposition on the universe lift, on the
sections over a chart. -/
theorem smallEtaleInternalHomSmallShrink_mapRight (M : Modules.{u, u} B S hS F hF)
    {N N' : Modules.{u, u} B S hS F hF} (f : N ⟶ N')
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ)
    (x : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj U) :
    smallEtaleInternalHomSmallShrink B S hS F hF M N' U
        ((smallEtaleInternalHomSmallMapRight B S hS F hF M f).val.app U x) =
      (smallEtaleInternalHomMapRight B S hS F hF M f).val.app U
        (smallEtaleInternalHomSmallShrink B S hS F hF M N U x) := by
  have h := RingedSite.moduleULift_map_internalHomSheafSmallFunctor_map
    (smallEtaleRingedSite B S hS F hF) M f
  have h2 := congrArg (fun k => (k.val.app U (ULift.up x)).down) h
  have h3 := congrArg (smallEtaleInternalHomSmallShrink B S hS F hF M N' U) h2
  have : Small.{u} ((smallEtaleInternalHom B S hS F hF M N').val.obj U) :=
    RingedSite.small_internalHomSheaf_obj (smallEtaleRingedSite B S hS F hF) M N' U
  exact h3.trans (AddEquiv.apply_symm_apply
    (Shrink.addEquiv (α := ((smallEtaleInternalHom B S hS F hF M N').val.obj U))) _)

/-- The identification of the sections of the small internal hom with those of its universe lift
is linear. -/
theorem smallEtaleInternalHomSmallShrink_smul (M N : Modules.{u, u} B S hS F hF)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj U)
    (x : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj U) :
    smallEtaleInternalHomSmallShrink B S hS F hF M N U (r • x) =
      r • smallEtaleInternalHomSmallShrink B S hS F hF M N U x :=
  Stacks.SheafOfModules.shrinkPresheaf_addEquiv_smul _
    (RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F hF) M N).val U r x

/-- The identification of sections is compatible with restriction. -/
theorem smallEtaleInternalHomSmallShrink_map (M N : Modules.{u, u} B S hS F hF)
    {U V : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (g : U ⟶ V)
    (x : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj U) :
    smallEtaleInternalHomSmallShrink B S hS F hF M N V
        ((smallEtaleInternalHomSmall B S hS F hF M N).val.map g x) =
      (smallEtaleInternalHom B S hS F hF M N).val.map g
        (smallEtaleInternalHomSmallShrink B S hS F hF M N U x) :=
  Stacks.SheafOfModules.C1573.sheafShrink_map_apply _
    (RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F hF) M N) g x

/-- A power of `𝓘` which annihilates `N` annihilates the small `𝓗om(M, N)`. -/
theorem smul_smallEtaleInternalHomSmall_eq_zero
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (k : ℕ) (M N : Modules.{u, u} B S hS F hF)
    (hN : IsPowAnnihilated B S hS F hF 𝓘 k N) (U : (smallEtaleRingedSite B S hS F hF).C)
    (r : chartRing B S hS F hF U) (hr : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k)
    (α : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj (op U)) : r • α = 0 :=
  (smallEtaleInternalHomSmallShrink B S hS F hF M N (op U)).injective <|
    (smallEtaleInternalHomSmallShrink_smul B S hS F hF M N (op U) r α).trans <|
      (smul_smallEtaleInternalHom_eq_zero B S hS F hF 𝓘 k M N hN U r hr _).trans (map_zero _).symm

/-! ### Global sections -/

/-- The global sections of the small internal hom are those of its universe lift. -/
def smallEtaleInternalHomSmallSectionsShrink (M N : Modules.{u, u} B S hS F hF) :
    (smallEtaleInternalHomSmall B S hS F hF M N).sections ≃
      (smallEtaleInternalHom B S hS F hF M N).sections where
  toFun s := PresheafOfModules.sectionsMk
    (fun U => smallEtaleInternalHomSmallShrink B S hS F hF M N U (s.1 U))
    fun U V g => (smallEtaleInternalHomSmallShrink_map B S hS F hF M N g (s.1 U)).symm.trans
      (congrArg _ (PresheafOfModules.sections_property s g))
  invFun s := PresheafOfModules.sectionsMk
    (fun U => (smallEtaleInternalHomSmallShrink B S hS F hF M N U).symm (s.1 U))
    fun U V g => by
      apply (smallEtaleInternalHomSmallShrink B S hS F hF M N V).injective
      refine (smallEtaleInternalHomSmallShrink_map B S hS F hF M N g _).trans ?_
      refine ((congrArg _ (AddEquiv.apply_symm_apply _ _)).trans ?_).trans
        (AddEquiv.apply_symm_apply _ _).symm
      exact PresheafOfModules.sections_property s g
  left_inv s := PresheafOfModules.sections_ext _ _ fun U =>
    (smallEtaleInternalHomSmallShrink B S hS F hF M N U).symm_apply_apply _
  right_inv s := PresheafOfModules.sections_ext _ _ fun U =>
    (smallEtaleInternalHomSmallShrink B S hS F hF M N U).apply_symm_apply _

/-- The identification of global sections commutes with postcomposition. -/
theorem smallEtaleInternalHomSmallSectionsShrink_map (M : Modules.{u, u} B S hS F hF)
    {N N' : Modules.{u, u} B S hS F hF} (f : N ⟶ N')
    (s : (smallEtaleInternalHomSmall B S hS F hF M N).sections) :
    smallEtaleInternalHomSmallSectionsShrink B S hS F hF M N'
        (SheafOfModules.sectionsMap (smallEtaleInternalHomSmallMapRight B S hS F hF M f) s) =
      SheafOfModules.sectionsMap (smallEtaleInternalHomMapRight B S hS F hF M f)
        (smallEtaleInternalHomSmallSectionsShrink B S hS F hF M N s) :=
  PresheafOfModules.sections_ext _ _ fun U =>
    smallEtaleInternalHomSmallShrink_mapRight B S hS F hF M f U (s.1 U)

/-! ### The comparison with the internal hom of the completion -/

section Comparison

variable (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (M N : Modules.{u, u} B S hS F hF)

/-- The comparison `𝓗 / 𝓘 ^ (n + 1) 𝓗 ⟶ 𝓗om(M, N / 𝓘 ^ (n + 1) N)` at level `n`, for the small
internal hom `𝓗 = 𝓗om(M, N)`. -/
def smallEtaleInternalHomSmallAdicComparisonApp (n : ℕ) :
    smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N) ⟶
      smallEtaleInternalHomSmall B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) :=
  cokernel.desc _ (smallEtaleInternalHomSmallMapRight B S hS F hF M
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N))
    ((idealPowerSubsheaf_ι_comp_zero_iff B S hS F hF 𝓘 (n + 1) _).mpr fun U r hr α =>
      (map_smul ((smallEtaleInternalHomSmallMapRight B S hS F hF M
            (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N)).val.app (op U)).hom
          r α).trans
        (smul_smallEtaleInternalHomSmall_eq_zero B S hS F hF 𝓘 (n + 1) M _
          (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) U r hr _))

/-- The projection `𝓗 ⟶ 𝓗 / 𝓘 ^ (n + 1) 𝓗` followed by the comparison is postcomposition with
the projection `N ⟶ N / 𝓘 ^ (n + 1) N`. -/
@[simp]
theorem smallEtaleAdicQuotientProjection_comp_smallComparisonApp (n : ℕ) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N) ≫
        smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N n =
      smallEtaleInternalHomSmallMapRight B S hS F hF M
        (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N) :=
  cokernel.π_desc _ _ _

/-- The comparison is a morphism of inverse systems. -/
theorem smallEtaleInternalHomSmallAdicComparison_compat (n : ℕ) :
    smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N) ≫
        smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N n =
      smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N (n + 1) ≫
        smallEtaleInternalHomSmallMapRight B S hS F hF M
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N) := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1 + 1)
    (smallEtaleInternalHomSmall B S hS F hF M N))).mp ?_
  rw [← Category.assoc, smallEtaleAdicQuotientProjection_comp_transition,
    smallEtaleAdicQuotientProjection_comp_smallComparisonApp, ← Category.assoc,
    smallEtaleAdicQuotientProjection_comp_smallComparisonApp,
    ← smallEtaleInternalHomSmallMapRight_comp, smallEtaleAdicQuotientProjection_comp_transition]

/-- The inverse limits of the global sections of the small internal homs into the ideal-power
quotients and of their universe lifts agree. -/
def smallEtaleInternalHomSmallAdicSectionsShrink :
    adicSections B S hS F hF
        (fun n => smallEtaleInternalHomSmall B S hS F hF M
          (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
        (fun n => smallEtaleInternalHomSmallMapRight B S hS F hF M
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N)) ≃
      adicSections B S hS F hF
        (fun n => smallEtaleInternalHom B S hS F hF M
          (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
        (fun n => smallEtaleInternalHomMapRight B S hS F hF M
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N)) where
  toFun s := ⟨fun n => smallEtaleInternalHomSmallSectionsShrink B S hS F hF M _ (s.1 n),
    fun n => by
      rw [← smallEtaleInternalHomSmallSectionsShrink_map, s.2 n]⟩
  invFun s := ⟨fun n => (smallEtaleInternalHomSmallSectionsShrink B S hS F hF M _).symm (s.1 n),
    fun n => by
      apply (smallEtaleInternalHomSmallSectionsShrink B S hS F hF M _).injective
      rw [smallEtaleInternalHomSmallSectionsShrink_map, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, s.2 n]⟩
  left_inv s := Subtype.ext (funext fun n => Equiv.symm_apply_apply _ _)
  right_inv s := Subtype.ext (funext fun n => Equiv.apply_symm_apply _ _)

/-- If the comparison on inverse limits is bijective on every chart, the inverse limit of the
global sections of `𝓗 / 𝓘 ^ n 𝓗`, for `𝓗` the internal hom `𝓗om(M, N)` at the module universe of
the schemes, is the set of morphisms of inverse systems `(M / 𝓘 ^ n M) ⟶ (N / 𝓘 ^ n N)`. -/
def smallEtaleInternalHomSmallAdicEquivOfBijective
    (h : ∀ U, Function.Bijective (adicSectionsMapAt B S hS F hF
      (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmall B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmallMapRight B S hS F hF M
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N))
      (smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N)
      (smallEtaleInternalHomSmallAdicComparison_compat B S hS F hF 𝓘 M N) U)) :
    adicSections B S hS F hF
        (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N))
        (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N)) ≃
      (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M ⟶
        smallEtaleAdicQuotientSystem B S hS F hF 𝓘 N) :=
  (((Equiv.ofBijective _ (bijective_adicSectionsMap_of_bijective_adicSectionsMapAt
        B S hS F hF _ _ _ _ _
        (smallEtaleInternalHomSmallAdicComparison_compat B S hS F hF 𝓘 M N) h)).trans
      (smallEtaleInternalHomSmallAdicSectionsShrink B S hS F hF 𝓘 M N)).trans
    (Equiv.ofBijective _
        (bijective_smallEtaleInternalHomAdicSection B S hS F hF 𝓘 M N)).symm).trans
    (systemHomEquiv B S hS F hF _ _ _ _).symm

end Comparison

end AlgebraicGeometry.Space.C1573

end
