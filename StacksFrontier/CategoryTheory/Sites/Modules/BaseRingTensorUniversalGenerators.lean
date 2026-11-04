module

public import StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorInverseLimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor

/-!
# Maps into `𝒪 ⊗_R N` out of a universal arrow, compared on generators

Let `𝒪` be a sheaf of commutative rings on a site, `R` a ring with `φ : R →+* Γ(𝒪)`, and
`ψ : 𝒫 ⟶ 𝒪` a map of sheaves of rings. Let `c₁ : I₁ ⟶ 𝒪 ⊗_R N₁` and `c₂ : I₂ ⟶ 𝒪 ⊗_R N₂` be
`𝒫`-linear maps, with `c₁` *universal* (every `𝒫`-linear map `I₁ ⟶ M` to an `𝒪`-module
factors uniquely through it), and let `d : I₁ ⟶ I₂` and `κ : N₁ ⟶ N₂`. If every section
`1 ⊗ n` of `𝒪 ⊗_R N₁` over every object is `c₁(a)` for a section `a` of `I₁` with
`c₂(d(a)) = 1 ⊗ κ(n)`, then `c₂ ∘ d = (𝒪 ⊗ κ) ∘ c₁`. The map `𝒪 ⊗_R N₁ ⟶ 𝒪 ⊗_R N₂` through
which `d ≫ c₂` factors is determined by its values on the sections `1 ⊗ n`
(Stacks 01BH for a base ring), and those are computed through `c₁`.

This is how the prescribed maps of the extension problems at a chart are compared along a
morphism of thickenings in Remark 0D1P.

## Main results

* `Stacks.Cohomology.SiteModules.comp_eq_comp_map_baseRingTensorFunctor_of_generators`

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O : Sheaf J CommRingCat.{u}} {P : Sheaf J RingCat.{u}} (ψ : P ⟶ ringSheafOfSite O)
  {R : Type u} [CommRing R] (φ : R →+* GlobalFunctionRing O)

/-- **A map out of a universal arrow into `𝒪 ⊗_R N₂`, compared on generators.** For `𝒫`-linear
maps `c₁ : I₁ ⟶ 𝒪 ⊗_R N₁` (universal) and `c₂ : I₂ ⟶ 𝒪 ⊗_R N₂`, `d : I₁ ⟶ I₂` and
`κ : N₁ ⟶ N₂`: if every section `1 ⊗ n` of `𝒪 ⊗_R N₁` over every object `U` is `c₁(a)` for some
`a ∈ I₁(U)` with `c₂(d(a)) = 1 ⊗ κ(n)`, then `d ≫ c₂ = c₁ ≫ (𝒪 ⊗ κ)`. -/
theorem comp_eq_comp_map_baseRingTensorFunctor_of_generators {I₁ I₂ : SheafOfModules.{u} P}
    {N₁ N₂ : ModuleCat.{u} R}
    (c₁ : I₁ ⟶ (SheafOfModules.restrictScalars ψ).obj
      ((baseRingTensorFunctor.{u, u, u, u, u} φ).obj N₁))
    (c₂ : I₂ ⟶ (SheafOfModules.restrictScalars ψ).obj
      ((baseRingTensorFunctor.{u, u, u, u, u} φ).obj N₂))
    (huniv : ∀ M : SheafOfModules.{u} (ringSheafOfSite O),
      Function.Bijective fun k : (baseRingTensorFunctor.{u, u, u, u, u} φ).obj N₁ ⟶ M =>
        c₁ ≫ (SheafOfModules.restrictScalars ψ).map k)
    (d : I₁ ⟶ I₂) (κ : N₁ ⟶ N₂)
    (hgen : ∀ (n : N₁) (U : Cᵒᵖ), ∃ a : I₁.val.obj U,
      c₁.val.app U a = ((baseRingTensorUnit.{u, u, u, u, u} φ N₁).hom n).eval U ∧
        c₂.val.app U (d.val.app U a) =
          ((baseRingTensorUnit.{u, u, u, u, u} φ N₂).hom (κ.hom n)).eval U) :
    d ≫ c₂ = c₁ ≫ (SheafOfModules.restrictScalars ψ).map
      ((baseRingTensorFunctor.{u, u, u, u, u} φ).map κ) := by
  obtain ⟨m, hm⟩ := (huniv _).2 (d ≫ c₂)
  have hm' : m = (baseRingTensorFunctor.{u, u, u, u, u} φ).map κ := by
    apply (baseRingTensorHomEquiv.{u, u, u, u, u} φ N₁ _).injective
    rw [baseRingTensorHomEquiv_apply, baseRingTensorHomEquiv_apply,
      ← baseRingTensorUnit_naturality]
    refine ModuleCat.hom_ext (LinearMap.ext fun n => Subtype.ext (funext fun U => ?_))
    obtain ⟨a, ha₁, ha₂⟩ := hgen n U
    have h := congrArg (fun t => t.val.app U a) hm
    change m.val.app U (c₁.val.app U a) = c₂.val.app U (d.val.app U a) at h
    change m.val.app U (((baseRingTensorUnit.{u, u, u, u, u} φ N₁).hom n).eval U) =
      ((baseRingTensorUnit.{u, u, u, u, u} φ N₂).hom (κ.hom n)).eval U
    rw [← ha₁, h, ha₂]
  rw [← hm, hm']

/-- **A map out of a universal arrow into `𝒪 ⊗_R N₂`, compared on global generators.** The form
of `comp_eq_comp_map_baseRingTensorFunctor_of_generators` with the generators given as global
sections `σ : 𝒫 ⟶ I₁`: if for every `n` some `σ` is carried by `c₁` to the section `1 ⊗ n`, and by
`c₂ ∘ d` to `1 ⊗ κ(n)` (both read over `𝒫` through `ψ`), then `d ≫ c₂ = c₁ ≫ (𝒪 ⊗ κ)`. -/
theorem comp_eq_comp_map_baseRingTensorFunctor_of_unitGenerators {I₁ I₂ : SheafOfModules.{u} P}
    {N₁ N₂ : ModuleCat.{u} R}
    (c₁ : I₁ ⟶ (SheafOfModules.restrictScalars ψ).obj
      ((baseRingTensorFunctor.{u, u, u, u, u} φ).obj N₁))
    (c₂ : I₂ ⟶ (SheafOfModules.restrictScalars ψ).obj
      ((baseRingTensorFunctor.{u, u, u, u, u} φ).obj N₂))
    (huniv : ∀ M : SheafOfModules.{u} (ringSheafOfSite O),
      Function.Bijective fun k : (baseRingTensorFunctor.{u, u, u, u, u} φ).obj N₁ ⟶ M =>
        c₁ ≫ (SheafOfModules.restrictScalars ψ).map k)
    (d : I₁ ⟶ I₂) (κ : N₁ ⟶ N₂)
    (hgen : ∀ n : N₁, ∃ σ : SheafOfModules.unit P ⟶ I₁,
      σ ≫ c₁ = Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit ψ ≫
          (SheafOfModules.restrictScalars ψ).map ((SheafOfModules.unitHomEquiv _).symm
            ((baseRingTensorUnit.{u, u, u, u, u} φ N₁).hom n)) ∧
        σ ≫ d ≫ c₂ = Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit ψ ≫
          (SheafOfModules.restrictScalars ψ).map ((SheafOfModules.unitHomEquiv _).symm
            ((baseRingTensorUnit.{u, u, u, u, u} φ N₂).hom (κ.hom n)))) :
    d ≫ c₂ = c₁ ≫ (SheafOfModules.restrictScalars ψ).map
      ((baseRingTensorFunctor.{u, u, u, u, u} φ).map κ) := by
  refine comp_eq_comp_map_baseRingTensorFunctor_of_generators ψ φ c₁ c₂ huniv d κ
    fun n U => ?_
  obtain ⟨σ, h₁, h₂⟩ := hgen n
  have hu := Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app_one ψ U
  have key : ∀ {N : ModuleCat.{u} R} (x : N)
      (f : SheafOfModules.unit P ⟶ (SheafOfModules.restrictScalars ψ).obj
        ((baseRingTensorFunctor.{u, u, u, u, u} φ).obj N)),
      f = Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit ψ ≫
          (SheafOfModules.restrictScalars ψ).map ((SheafOfModules.unitHomEquiv _).symm
            ((baseRingTensorUnit.{u, u, u, u, u} φ N).hom x)) →
        f.val.app U (1 : P.obj.obj U) =
          ((baseRingTensorUnit.{u, u, u, u, u} φ N).hom x).eval U := by
    intro N x f hf
    refine (congrArg (fun m => m.val.app U (1 : P.obj.obj U)) hf).trans ?_
    change ((SheafOfModules.unitHomEquiv _).symm
      ((baseRingTensorUnit.{u, u, u, u, u} φ N).hom x)).val.app U
        ((Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit ψ).val.app U
          (1 : P.obj.obj U)) = _
    rw [hu]
    exact congrArg (fun s : ((baseRingTensorFunctor.{u, u, u, u, u} φ).obj N).sections =>
      s.val U) ((SheafOfModules.unitHomEquiv _).apply_symm_apply _)
  exact ⟨σ.val.app U (1 : P.obj.obj U), key _ _ h₁, key _ _ h₂⟩

end Stacks.Cohomology.SiteModules
