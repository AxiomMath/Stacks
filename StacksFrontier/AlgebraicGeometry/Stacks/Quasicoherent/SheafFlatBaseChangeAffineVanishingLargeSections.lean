module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatAffineCartesianCechVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeEtaleWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoveringsLargeCoefficients

/-!
# Affine vanishing for `LQCoh^fbc` at module universe `u + 1`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u` (the seating of an algebraic stack), and let
`F` be a sheaf of modules on the fppf site of `𝒳` with sections in `Type (u + 1)` which belongs to
the faithful class `LQCoh^fbc(𝒪_𝒳)`: locally quasi-coherent (Stacks 06WJ) with the flat base
change property of Stacks 0762 read with the pullback of sheaves.  Then for every object `x`
lying over an affine scheme, `H^n_{fppf}(x, F) = 0` for `n > 0`.

This is the module universe `u + 1` form of
`AlgebraicGeometry.Stack.isZero_sheafCohomology_of_sheafFlatBaseChange`; it is Cartan's criterion
(Stacks 03F9) along the families of arrows lying over standard fppf coverings, in the form
`Stacks.CechSite.isZero_rightDerived_sheafSections_of_cechCohomology_isZero`, whose coefficient
universe is free above the site, with the Čech input
`AlgebraicGeometry.Stack.isZero_cechCohomology_of_isCartesianOnFlatAffineArrows`.  The flat base
change property is cartesianness on flat affine arrows by
`AlgebraicGeometry.Stack.hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows`.

## Main results

* `AlgebraicGeometry.Stack.isGrothendieckAbelian_fppfAbelianSheavesSucc`: the abelian sheaves at
  section universe `u + 1` on the fppf site form a Grothendieck abelian category.
* `AlgebraicGeometry.Stack.isZero_rightDerived_sheafSections_of_isCartesianOnFlatAffineArrows_succ`
  and `AlgebraicGeometry.Stack.isZero_rightDerived_sheafSections_of_sheafFlatBaseChange_succ`:
  **the affine vanishing**, for the right-derived functors of sections of the underlying
  abelian sheaf.

No `@[stacks]` attribute is claimed: these are helpers of Stacks 0771 at module universe `u + 1`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

/-- **The abelian sheaves with sections in `Type (u + 1)` on the fppf site of `𝒳` form a
Grothendieck abelian category**: the site is essentially small at that universe. -/
theorem isGrothendieckAbelian_fppfAbelianSheavesSucc :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (associatedTopology B S hS p B.topology) AddCommGrpCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ AddCommGrpCat.{u + 1}

attribute [local instance] isGrothendieckAbelian_fppfAbelianSheavesSucc

include hp in
/-- **The higher fppf cohomology over an object lying over an affine scheme vanishes**, at
section universe `u + 1`, for the underlying abelian sheaf of a sheaf of modules which is
cartesian on flat affine arrows. -/
theorem isZero_rightDerived_sheafSections_of_isCartesianOnFlatAffineArrows_succ
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS p hp B.topology le_rfl F.val)
    (x : 𝒳) (hx : IsAffine ((toScheme B S hS p).obj x)) (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections (associatedTopology B S hS p B.topology)
      AddCommGrpCat.{u + 1}).obj (op x)).rightDerived n).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj F)) := by
  classical
  have : HasPullbacks 𝒳 := hasPullbacks_fibred B S hS p hp
  let J := associatedTopology B S hS p B.topology
  let Bset : Set 𝒳 := {y | IsAffine ((toScheme B S hS p).obj y)}
  let Cov : ∀ y : 𝒳, Set {𝒰 : PreZeroHypercover.{u} y // 𝒰.sieve₀ ∈ J y} := fun y 𝒰 ↦
    ∃ hy : IsAffine ((toScheme B S hS p).obj y),
      @IsStandardCovering .fppf _ hy _ (fun i ↦ (toScheme B S hS p).obj (𝒰.1.X i))
        (fun i ↦ (toScheme B S hS p).map (𝒰.1.f i))
  have hProducts : ∀ {y : 𝒳} (𝒰 : {𝒰 : PreZeroHypercover.{u} y // 𝒰.sieve₀ ∈ J y}),
      𝒰 ∈ Cov y → ∀ (m : ℕ) (i : Fin (m + 1) → 𝒰.1.I₀),
        HasProduct (fun a ↦ Over.mk (𝒰.1.f (i a))) := fun _ _ m _ ↦
    Stacks.Sites.hasProduct_over_fin m _ (fun _ _ _ ↦ inferInstance)
  refine Stacks.CechSite.isZero_rightDerived_sheafSections_of_cechCohomology_isZero.{0} J
    Bset Cov hProducts ?_ ?_ _ ?_ x hx n hn
  · intro y 𝒰 h𝒰
    have hy := h𝒰.1
    have hstd := h𝒰.2
    refine ⟨hy, fun i ↦ hstd.affine_source i, fun m i ↦ ?_⟩
    have := hProducts 𝒰 h𝒰
    have : MorphismProperty.IsStableUnderComposition @IsAffineHom :=
      ⟨fun _ _ hf hg ↦ by have := hf; have := hg; infer_instance⟩
    have : MorphismProperty.RespectsIso @IsAffineHom :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have haff := prop_toScheme_map_cechProduct_hom B S hS p hp @IsAffineHom 𝒰.1
      (fun j ↦ by have := hstd.affine_source j; infer_instance) m i
    exact isAffine_of_isAffineHom
      ((toScheme B S hS p).map (∏ᶜ (fun a ↦ Over.mk (𝒰.1.f (i a)))).hom)
  · intro y hy R hR
    have : IsAffine ((toScheme B S hS p).obj y) := hy
    obtain ⟨𝒰, h𝒰J, hstd, hle⟩ := exists_standardFppfFamily_le_of_mem_fppf B S hS p hp hR
    exact ⟨⟨𝒰, h𝒰J⟩, ⟨hy, hstd⟩, hle⟩
  · intro y 𝒰 h𝒰 m hm
    have : IsAffine ((toScheme B S hS p).obj y) := h𝒰.1
    have := hProducts 𝒰 h𝒰
    exact isZero_cechCohomology_of_isCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS p hp
      B.topology le_rfl F.val hF 𝒰.1 h𝒰.2 m hm

include hp in
/-- **The higher fppf cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` vanishes over an object lying
over an affine scheme**, at section universe `u + 1`: `H^n(x, F) = 0` for `n > 0`, for the
right-derived functors of sections of the underlying abelian sheaf. -/
theorem isZero_rightDerived_sheafSections_of_sheafFlatBaseChange_succ
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
      B E h S hS p hp F.val)
    (x : 𝒳) (hx : IsAffine ((toScheme B S hS p).obj x)) (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections (associatedTopology B S hS p B.topology)
      AddCommGrpCat.{u + 1}).obj (op x)).rightDerived n).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj F)) :=
  isZero_rightDerived_sheafSections_of_isCartesianOnFlatAffineArrows_succ B S hS p hp F
    (fun _ _ φ hφ hx' hy' ↦
      (hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows.{u, u + 1, u, u}
        B E h S hS p hp F.val hF.1).1 hF.2 φ hφ hx' hy')
    x hx n hn

end AlgebraicGeometry.Stack

end
