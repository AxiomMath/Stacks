module

public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.CyclicClassifyingStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardShiftedSum
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAffineLocalization
public import StacksFrontier.RingTheory.Localization.ProductOfRetracts

/-!
# The unbounded derived pushforward of `[Spec k[x] / (ℤ/pℤ)] ⟶ Spec k[x]`

Assembly of the discussion of **Stacks 07DC**.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Stack Opposite

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

namespace Stacks.Examples.UnboundedDerivedPushforward

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  Stacks.Cohomology.AcyclicCover.evaluation_additive
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall

variable (𝒞 : BigFppfSite.{u}) {R : CommRingCat.{u}} (hS : 𝒞.Contains (Spec R))

/-- The ring `𝒪(y)` of sections at an object `y` of `Spec R`, over which sections of fppf modules
are modules. -/
abbrev affineRing (y : (affineSchemeStack.{u, w} 𝒞 R hS).val.val.obj) : RingCat.{u} :=
  (FibredSite.ringStructureSheafCore 𝒞 _ hS (affineSchemeStack.{u, w} 𝒞 R hS).val.val.p
    (affineSchemeStack.{u, w} 𝒞 R hS).val.isFiberedInGroupoids .fppf).obj.obj (op y)

/-- **A product of modules with rank-one retracts is not locally quasi-coherent.** Let `F m`,
`m ≥ 0`, and `H` be modules in `LQCoh^fbc` on `Spec R`, where `𝒪(Spec R)` is a domain in which `r`
is a nonzero non-unit. Suppose that the sections of `H` over `Spec R` and over `D(r)` are the
products of those of the `F m`, compatibly with restriction, and that each `Γ(Spec R, F m)` has
`𝒪(Spec R)` as a linear retract. This is impossible: the vector `(e_m / r^m)_m` over `D(r)` has
unbounded denominators, while `H` is quasi-coherent. -/
theorem false_of_sections_eq_pi (r : R)
    [hdom : IsDomain (affineSchemeStack.sectionsRing.{u, w} 𝒞 R hS
      (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS))]
    (hr₀ : affineSchemeStack.terminalElement.{u, w} 𝒞 R hS r ≠ 0)
    (hru : ¬ IsUnit (affineSchemeStack.terminalElement.{u, w} 𝒞 R hS r))
    (F : ℕ → fppfModules 𝒞 (Spec R) hS (affineSchemeStack.{u, w} 𝒞 R hS))
    (hF : ∀ m, lqcohSheafFbcFppfModules.{u, w, u} 𝒞 (associatedBigEtaleSite 𝒞) rfl _ hS
      (affineSchemeStack.{u, w} 𝒞 R hS) (F m))
    (H : fppfModules 𝒞 (Spec R) hS (affineSchemeStack.{u, w} 𝒞 R hS))
    (hH : lqcohSheafFbcFppfModules.{u, w, u} 𝒞 (associatedBigEtaleSite 𝒞) rfl _ hS
      (affineSchemeStack.{u, w} 𝒞 R hS) H)
    (α₀ : H.val.obj (op (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)) ≃ₗ[affineRing.{u, w} 𝒞 hS
      (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)]
        ((m : ℕ) → (F m).val.obj (op (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS))))
    (α₁ : H.val.obj (op (affineSchemeStack.basicOpenObj.{u, w} 𝒞 R hS r)) ≃ₗ[affineRing.{u, w} 𝒞 hS
      (affineSchemeStack.basicOpenObj.{u, w} 𝒞 R hS r)]
        ((m : ℕ) → (F m).val.obj (op (affineSchemeStack.basicOpenObj.{u, w} 𝒞 R hS r))))
    (hα : ∀ (s : H.val.obj (op (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS))) (m : ℕ),
      α₁ (H.val.map (affineSchemeStack.basicOpenι.{u, w} 𝒞 R hS r).op s) m =
        (F m).val.map (affineSchemeStack.basicOpenι.{u, w} 𝒞 R hS r).op (α₀ s m))
    (e : ∀ m, (F m).val.obj (op (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)))
    (ψ : ∀ m, (F m).val.obj (op (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)) →ₗ[affineRing.{u, w}
      𝒞 hS (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)]
        affineRing.{u, w} 𝒞 hS (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS))
    (he : ∀ m, ψ m (e m) = 1) : False := by
  refine Stacks.Localization.false_of_retracts_of_surjective_up_to_powers
    (A := affineSchemeStack.sectionsRing.{u, w} 𝒞 R hS
      (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS))
    (A' := affineSchemeStack.sectionsRing.{u, w} 𝒞 R hS
      (affineSchemeStack.basicOpenObj.{u, w} 𝒞 R hS r))
    (affineSchemeStack.basicOpenRestriction.{u, w} 𝒞 R hS r)
    (affineSchemeStack.terminalElement.{u, w} 𝒞 R hS r) hr₀ hru
    (affineSchemeStack.isUnit_basicOpenRestriction.{u, w} 𝒞 R hS r)
    (M := fun m => (affineSchemeStack.etaleStructureModule.{u, w} 𝒞 R hS (F m)).obj
      (op (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)))
    (M' := fun m => (affineSchemeStack.etaleStructureModule.{u, w} 𝒞 R hS (F m)).obj
      (op (affineSchemeStack.basicOpenObj.{u, w} 𝒞 R hS r)))
    (fun m => ((affineSchemeStack.etaleStructureModule.{u, w} 𝒞 R hS (F m)).map
      (affineSchemeStack.basicOpenι.{u, w} 𝒞 R hS r).op).hom.toAddMonoidHom)
    (fun m a v => affineSchemeStack.map_basicOpenι_smul.{u, w} 𝒞 R hS (F m) r a v)
    (fun m v hv => affineSchemeStack.exists_pow_smul_eq_zero_of_map_eq_zero.{u, w} 𝒞
      (associatedBigEtaleSite 𝒞) rfl R hS (F m) r (hF m) v hv)
    e (fun m =>
      { toFun := fun v => ψ m v
        map_add' := fun v v' => map_add (ψ m) v v'
        map_smul' := fun a v => (ψ m).map_smul a v }) he
    (H := (affineSchemeStack.etaleStructureModule.{u, w} 𝒞 R hS H).obj
      (op (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)))
    (H' := (affineSchemeStack.etaleStructureModule.{u, w} 𝒞 R hS H).obj
      (op (affineSchemeStack.basicOpenObj.{u, w} 𝒞 R hS r)))
    ((affineSchemeStack.etaleStructureModule.{u, w} 𝒞 R hS H).map
      (affineSchemeStack.basicOpenι.{u, w} 𝒞 R hS r).op).hom.toAddMonoidHom
    α₀.toAddMonoidHom α₁.toAddEquiv ?_ ?_ ?_
  · intro a h m
    exact congrFun (α₁.map_smul a h) m
  · intro h m
    exact hα h m
  · intro h'
    exact affineSchemeStack.exists_pow_smul_eq_map.{u, w} 𝒞 (associatedBigEtaleSite 𝒞) rfl
      R hS H r hH h'

/-- **The retracts on the sections of `R^m f_* 𝒪_𝒳`.** For a quasi-compact and quasi-separated
`f` and an object `y` over an affine scheme, a linear retract `𝒪(y) → R^m Γ(y, f_*(-))(𝒪_𝒳)` moves,
through `AlgebraicGeometry.Stack.fppfModulesHigherDirectImageSectionsIsoRightDerived`, to the
sections `Γ(y, R^m f_* 𝒪_𝒳)`. -/
theorem exists_retract_sections_of_retracts {𝒳 𝒴 : AlgebraicStacks.{u, w} 𝒞 (Spec R) hS}
    (f : 𝒳 ⟶ 𝒴) (hqc : IsQuasiCompactMorphism 𝒞 _ hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated 𝒞 _ hS f)
    (y₀ : 𝒴.val.val.obj) (hy₀' : IsAffineOver 𝒞 _ hS (𝒴.val.val.p.obj y₀))
    (hD : ∀ m : ℕ, ∃ (e : ((fppfModulesPushforward 𝒞 _ hS f ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y₀)).rightDerived m).obj (SheafOfModules.unit _))
      (ψ : ((fppfModulesPushforward 𝒞 _ hS f ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y₀)).rightDerived m).obj (SheafOfModules.unit _) →ₗ[
          (FibredSite.ringStructureSheafCore 𝒞 _ hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
            .fppf).obj.obj (op y₀)]
          (FibredSite.ringStructureSheafCore 𝒞 _ hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
            .fppf).obj.obj (op y₀)), ψ e = 1)
    (m : ℕ) : ∃ (e : (((fppfModulesPushforward 𝒞 _ hS f).rightDerived m).obj
        (SheafOfModules.unit _)).val.obj (op y₀))
      (ψ : (((fppfModulesPushforward 𝒞 _ hS f).rightDerived m).obj
        (SheafOfModules.unit _)).val.obj (op y₀) →ₗ[
          (FibredSite.ringStructureSheafCore 𝒞 _ hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
            .fppf).obj.obj (op y₀)]
          (FibredSite.ringStructureSheafCore 𝒞 _ hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
            .fppf).obj.obj (op y₀)), ψ e = 1 := by
  obtain ⟨e, ψ, he⟩ := hD m
  let i := fppfModulesHigherDirectImageSectionsIsoRightDerived 𝒞 (associatedBigEtaleSite 𝒞)
      rfl _ hS f hqc hqs m y₀ hy₀'
  let L := i.toLinearEquiv
  exact ⟨L.symm e, ψ.comp L.toLinearMap, by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, he]⟩

/-- **The degree-zero step of Stacks 07DC.** Let `f : 𝒳 ⟶ 𝒴 = Spec R` be a quasi-compact and
quasi-separated `1`-morphism of algebraic stacks into an affine scheme, let `r ∈ R` be such that
`𝒪(Spec R)` is a domain in which `r` is a nonzero non-unit, and suppose that for every `m` the
`m`-th right derived functor of `Γ(Spec R, f_*(-))` at `𝒪_𝒳` has `𝒪(Spec R)` as a linear retract.
Then `Rf_*(⊕_{m ≥ 0} 𝒪_𝒳[m])` is not in `D_{LQCoh^fbc}(𝒪_{Spec R})`: the sections of its
degree-zero cohomology sheaf over `Spec R` and over `D(r)` are the products of those of the
`R^m f_* 𝒪_𝒳`, and `false_of_sections_eq_pi` applies. -/
theorem not_derivedCategoryB_of_retracts (r : R)
    (hdom : IsDomain (affineSchemeStack.sectionsRing.{u, w} 𝒞 R hS
      (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS)))
    (hr₀ : affineSchemeStack.terminalElement.{u, w} 𝒞 R hS r ≠ 0)
    (hru : ¬ IsUnit (affineSchemeStack.terminalElement.{u, w} 𝒞 R hS r))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} 𝒞 (Spec R) hS} (h𝒴 : 𝒴 = affineSchemeStack.{u, w} 𝒞 R hS)
    (f : 𝒳 ⟶ 𝒴) (hqc : IsQuasiCompactMorphism 𝒞 _ hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated 𝒞 _ hS f)
    [HasDerivedCategory (fppfModules 𝒞 _ hS 𝒳)] [HasDerivedCategory (fppfModules 𝒞 _ hS 𝒴)]
    (y₀ : 𝒴.val.val.obj) (hy₀ : HEq y₀ (affineSchemeStack.terminalObj.{u, w} 𝒞 R hS))
    (hD : ∀ m : ℕ, ∃ (e : ((fppfModulesPushforward 𝒞 _ hS f ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y₀)).rightDerived m).obj (SheafOfModules.unit _))
      (ψ : ((fppfModulesPushforward 𝒞 _ hS f ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y₀)).rightDerived m).obj (SheafOfModules.unit _) →ₗ[
          (FibredSite.ringStructureSheafCore 𝒞 _ hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
            .fppf).obj.obj (op y₀)]
          (FibredSite.ringStructureSheafCore 𝒞 _ hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
            .fppf).obj.obj (op y₀)), ψ e = 1) :
    ¬ DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, w, u} 𝒞 (associatedBigEtaleSite 𝒞) rfl _ hS 𝒴)
      ((fppfModulesDerivedPushforward 𝒞 _ hS f).obj (fppfModulesShiftedUnitSum 𝒞 _ hS 𝒳)) := by
  intro hE
  obtain ⟨hH, α, hα⟩ := lqcohSheafFbcFppfModules_homology_zero_and_exists_linearEquiv_sections
    𝒞 (associatedBigEtaleSite 𝒞) rfl _ hS f hqc hqs hE
  have hF : ∀ m, lqcohSheafFbcFppfModules.{u, w, u} 𝒞 (associatedBigEtaleSite 𝒞) rfl _ hS 𝒴
      (((fppfModulesPushforward 𝒞 _ hS f).rightDerived m).obj (SheafOfModules.unit _)) :=
    fun m => lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage 𝒞
      (associatedBigEtaleSite 𝒞) rfl _ hS f hqc hqs (SheafOfModules.unit _)
      (lqcohSheafFbcFppfModules_unit 𝒞 (associatedBigEtaleSite 𝒞) rfl _ hS _) m
  have hy₀' : IsAffineOver 𝒞 _ hS (𝒴.val.val.p.obj y₀) := by
    subst h𝒴
    obtain rfl := eq_of_heq hy₀
    exact inferInstanceAs (IsAffine (Spec R))
  -- the retracts, moved to the sections of `R^m f_* 𝒪_𝒳`
  have hret := fun m => exists_retract_sections_of_retracts 𝒞 hS f hqc hqs y₀ hy₀' hD m
  choose e ψ he using hret
  clear hD hE
  subst h𝒴
  obtain rfl := eq_of_heq hy₀
  have hy₁ : IsAffineOver 𝒞 _ hS ((affineSchemeStack.{u, w} 𝒞 R hS).val.val.p.obj
      (affineSchemeStack.basicOpenObj.{u, w} 𝒞 R hS r)) :=
    (isAffineOpen_top (Spec R)).basicOpen (affineSchemeStack.globalElement R r)
  exact false_of_sections_eq_pi (hdom := hdom) 𝒞 hS r hr₀ hru _ hF _ hH (α _ hy₀') (α _ hy₁)
    (fun s m => hα _ _ hy₁ hy₀' (affineSchemeStack.basicOpenι.{u, w} 𝒞 R hS r) s m) e ψ he

end Stacks.Examples.UnboundedDerivedPushforward
