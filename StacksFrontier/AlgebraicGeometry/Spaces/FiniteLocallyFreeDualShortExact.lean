module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeOfRankDual
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteMonoidalClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLeftDualFiniteLocallyFree
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.CategoryTheory.Monoidal.RigidShortExact

/-!
# Duality is exact on short exact sequences of finite locally free modules on a space

Let `F` be an algebraic space over a scheme `S` and let `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` be a short exact
sequence of finite locally free `𝒪_F`-modules on the small étale site. Then the sequence of duals

  `0 ⟶ ℰ₃^∨ ⟶ ℰ₂^∨ ⟶ ℰ₁^∨ ⟶ 0`,  `ℰ^∨ = 𝓗om(ℰ, 𝒪_F)`,

is short exact.

## Main results

* `AlgebraicGeometry.Space.isFlat_of_hasRightDual`: an `𝒪_F`-module with a dual is flat.
* `AlgebraicGeometry.Space.mono_whiskerRight_of_shortExact`: a short exact sequence whose third
  term has a dual stays a monomorphism on the left after tensoring with any module.
* `AlgebraicGeometry.Space.shortExact_rightDual`: the sequence of right duals and right adjoint
  mates of a short exact sequence whose terms have duals is short exact.
* `AlgebraicGeometry.Space.exists_shortExact_dual`: **the dual of a short exact sequence of finite
  locally free `𝒪_F`-modules is short exact.**
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_dual`: the dual of a module of rank `r` has
  rank `r`.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

attribute [local instance] modulesMonoidalPreadditive

/-- An `𝒪_F`-module with a dual is flat. -/
theorem isFlat_of_hasRightDual (M : Modules.{u, u} B S hS F hF) [HasRightDual M] :
    AlgebraicGeometry.SheafOfModules.IsFlat M := by
  let : SymmetricCategory (Modules.{u, u} B S hS F hF) :=
    RingedSite.modulesSymmetric (smallEtaleRingedSite B S hS F hF)
  let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
  have hc : PreservesFiniteColimits (tensorRight M) :=
    (tensorRightAdjunction M Mᘁ).leftAdjoint_preservesColimits.preservesFiniteColimits.{0, 0}
  have hl : PreservesFiniteLimits (tensorRight M) :=
    (tensorRightAdjunction Mᘁ M).rightAdjoint_preservesLimits.preservesFiniteLimits.{0, 0}
  have e := RingedSite.tensorRightIso (smallEtaleRingedSite B S hS F hF) M
  rw [AlgebraicGeometry.SheafOfModules.IsFlat, exactFunctor_iff]
  exact ⟨@preservesFiniteLimits_of_natIso _ _ _ _ _ _ e hl,
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _ e hc⟩

/-- **A short exact sequence of `𝒪_F`-modules whose third term has a dual is pure**: tensoring
it on the right with any module keeps its first map a monomorphism. -/
theorem mono_whiskerRight_of_shortExact {S' : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hS' : S'.ShortExact) [HasRightDual S'.X₃] (T : Modules.{u, u} B S hS F hF) :
    Mono (S'.f ▷ T) := by
  obtain ⟨_, hse⟩ := Stacks.SheafOfModules.FlatCover.sheafTensorRight_shortExact_of_isFlat_X₃
    (smallEtaleRingedSite B S hS F hF).O S' T hS' (isFlat_of_hasRightDual B S hS F hF S'.X₃)
  have hm := hse.mono_f
  have e := RingedSite.tensorRightIso (smallEtaleRingedSite B S hS F hF) T
  have key : S'.f ▷ T = (e.app S'.X₁).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).flip.obj
        T).map S'.f ≫ (e.app S'.X₂).inv := by
    rw [Iso.app_hom, Iso.app_inv, ← Category.assoc, ← e.hom.naturality, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    rfl
  rw [key]
  exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom (e.app S'.X₁))) _
    (@mono_comp _ _ _ _ _ _ hm _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_inv (e.app S'.X₂))))

/-- **The sequence of duals of a short exact sequence of `𝒪_F`-modules with duals is short
exact**, the maps being the right adjoint mates. -/
theorem shortExact_rightDual {S' : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hS' : S'.ShortExact) [HasRightDual S'.X₁] [HasRightDual S'.X₂] [HasRightDual S'.X₃] :
    S'.rightDual.ShortExact := by
  let : BraidedCategory (Modules.{u, u} B S hS F hF) :=
    RingedSite.modulesBraided (smallEtaleRingedSite B S hS F hF)
  exact hS'.rightDual (mono_whiskerRight_of_shortExact B S hS F hF hS')

/-- **Duality is exact on short exact sequences of finite locally free modules on an algebraic
space.** If `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` is a short exact sequence of finite locally free
`𝒪_F`-modules, there is a short exact sequence of their duals
`0 ⟶ ℰ₃^∨ ⟶ ℰ₂^∨ ⟶ ℰ₁^∨ ⟶ 0`, the dual being the internal Hom `𝓗om(-, 𝒪_F)` into the structure
sheaf; its maps are the transposes of the given ones. -/
theorem exists_shortExact_dual {S' : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hS' : S'.ShortExact) (h₁ : SheafOfModules.IsFiniteLocallyFreeOnSite S'.X₁)
    (h₂ : SheafOfModules.IsFiniteLocallyFreeOnSite S'.X₂)
    (h₃ : SheafOfModules.IsFiniteLocallyFreeOnSite S'.X₃) :
    ∃ (a : (ihom S'.X₃).obj (𝟙_ _) ⟶ (ihom S'.X₂).obj (𝟙_ _))
      (b : (ihom S'.X₂).obj (𝟙_ _) ⟶ (ihom S'.X₁).obj (𝟙_ _)) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact := by
  let : BraidedCategory (Modules.{u, u} B S hS F hF) :=
    RingedSite.modulesBraided (smallEtaleRingedSite B S hS F hF)
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS F hF S'.X₁ h₁
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS F hF S'.X₂ h₂
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS F hF S'.X₃ h₃
  let e₁ := rightDualIsoIhomUnit S'.X₁ S'.X₁ᘁ
  let e₂ := rightDualIsoIhomUnit S'.X₂ S'.X₂ᘁ
  let e₃ := rightDualIsoIhomUnit S'.X₃ S'.X₃ᘁ
  have hse := shortExact_rightDual B S hS F hF hS'
  refine ⟨e₃.inv ≫ rightAdjointMate S'.g ≫ e₂.hom, e₂.inv ≫ rightAdjointMate S'.f ≫ e₁.hom,
    by simp only [Category.assoc, Iso.hom_inv_id_assoc,
      reassoc_of% (show rightAdjointMate S'.g ≫ rightAdjointMate S'.f = 0 from S'.rightDual.zero),
      zero_comp, comp_zero], ?_⟩
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk e₃ e₂ e₁ ?_ ?_) hse <;> simp

/-- **The dual of a finite locally free `𝒪_F`-module of rank `r` has rank `r`.** -/
theorem isFiniteLocallyFreeOfRank_dual (M : Modules.{u, u} B S hS F hF) {r : ℕ}
    (hM : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) M r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF)
      ((ihom M).obj (𝟙_ _)) r :=
  RingedSite.isFiniteLocallyFreeOfRank_internalHomSheafSmall_unit
    (smallEtaleRingedSite B S hS F hF) M hM

end AlgebraicGeometry.Space

end
