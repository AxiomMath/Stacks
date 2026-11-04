module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapBijectiveExtensionClosed
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AbelianUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Adequator
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineAdequatorVanishing
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteModuleInjectives
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionAcyclic

/-!
# Extension groups of adequate modules, compared with those of all modules

Let `U = Spec A` be affine. For adequate `𝒪`-modules `𝓕` and `𝓖` and `i ≥ 0`, this file studies
the natural map

`Ext^i_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^i_{Mod((Sch/U)_τ, 𝒪)}(𝓕, 𝓖)`.

It is bijective in degrees `0` and `1`, and in every degree as soon as the higher right derived
functors of the adequator `Stacks.Adequate.affineAdequator` vanish on `Adeq(𝒪)`.

## Main results

* `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_zero`: the map is bijective in degree `0`.
* `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_one`: the map is bijective in degree `1`.
* `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_of_isZero_rightDerived`: the map is bijective
  in every degree if the higher right derived functors of `Stacks.Adequate.affineAdequator`
  vanish on `Adeq(𝒪)`.
* `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_of_siteModuleExtension`: the map is
  bijective in every degree if `Ext` from linearly adequate functors into module extensions on
  the algebras of the site vanishes in positive degrees.
* `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_of_siteZExt`: the same, with that vanishing
  stated for `Abelian.zExt`.

## References

* [Stacks Project, Tag 06ZW](https://stacks.math.columbia.edu/tag/06ZW)
* [Stacks Project, Tag 06ZV](https://stacks.math.columbia.edu/tag/06ZV)
* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

private instance : ObjectProperty.IsClosedUnderKernels (adequate.{u, u} B) :=
  adequate_isClosedUnderKernels B

private instance : ObjectProperty.IsClosedUnderCokernels (adequate.{u, u} B) :=
  adequate_isClosedUnderCokernels B

private instance : ObjectProperty.IsClosedUnderFiniteProducts (adequate.{u, u} B) :=
  adequate_isClosedUnderFiniteProducts B

private instance : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B

private instance : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1

private instance : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2

private instance : (affineAdequator B).Additive :=
  (affineAdequatorAdjunction B).right_adjoint_additive

private instance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
  HasDerivedCategory.standard _

private instance : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
  HasDerivedCategory.standard _

private instance : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
  hasExt_of_hasDerivedCategory _

private instance : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
  hasExt_of_hasDerivedCategory _

private instance : PreservesLimitsOfSize.{0, 0} (affineAdequator B) :=
  (affineAdequatorAdjunction B).rightAdjoint_preservesLimits

/-- For `U = Spec A` affine, if the higher right derived functors of the adequator
`Stacks.Adequate.affineAdequator` vanish on `Adeq(𝒪)`, then for all adequate `𝒪`-modules `𝓕`,
`𝓖` and every degree `n` the natural map
`Ext^n_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^n_{Mod((Sch/U)_τ, 𝒪)}(𝓕, 𝓖)` is bijective. -/
public theorem bijective_mapExtAddHom_ι_adequate_of_isZero_rightDerived :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : (affineAdequator B).Additive :=
      (affineAdequatorAdjunction B).right_adjoint_additive
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    (∀ (G : (adequate.{u, u} B).FullSubcategory) (p : ℕ), 0 < p →
        IsZero (((affineAdequator B).rightDerived p).obj G.obj)) →
      ∀ (F G : (adequate.{u, u} B).FullSubcategory) (n : ℕ),
        Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G n) := by
  intro hvanishing F G n
  exact Stacks.ExtAdjunction.mapExtAddHom_bijective_of_isZero_rightDerived
    (affineAdequatorAdjunction B) F G inferInstance (fun p hp ↦ hvanishing G p hp) n

/-- For `U = Spec A` affine and adequate `𝒪`-modules `𝓕`, `𝓖`, the natural map
`Ext^0_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^0_{Mod((Sch/U)_τ, 𝒪)}(𝓕, 𝓖)` is bijective. -/
@[stacks 06ZW "degree 0, where the comparison is the map on Hom and the inclusion of the \
strictly full subcategory of adequate modules is fully faithful; every degree is \
bijective_mapExtAddHom_ι_adequate in HigherExtsAdequate/AdequateExtComparisonAll"]
public theorem bijective_mapExtAddHom_ι_adequate_zero :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    ∀ (F G : (adequate.{u, u} B).FullSubcategory),
      Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G 0) := by
  intro F G
  have hfun : ⇑((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G 0)
      = Ext.homEquiv₀.symm ∘ (adequate.{u, u} B).ι.map ∘ Ext.homEquiv₀ := by
    rw [Functor.mapExtAddHom_coe]
    exact Ext.mapExactFunctor₀ _ _ _
  rw [hfun]
  exact Ext.homEquiv₀.symm.bijective.comp
    (Function.Bijective.comp
      ⟨(adequate.{u, u} B).ι.map_injective, (adequate.{u, u} B).ι.map_surjective⟩
      Ext.homEquiv₀.bijective)

/-- For `U = Spec A` affine and adequate `𝒪`-modules `𝓕`, `𝓖`, the natural map
`Ext^1_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^1_{Mod((Sch/U)_τ, 𝒪)}(𝓕, 𝓖)` is bijective. -/
@[stacks 06ZW "degree 1, where the comparison is bijective because the adequate modules are \
closed under extensions, Tag 06VQ (3), and Ext^1 is the group of Yoneda extensions; every \
degree is bijective_mapExtAddHom_ι_adequate in HigherExtsAdequate/AdequateExtComparisonAll"]
public theorem bijective_mapExtAddHom_ι_adequate_one :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    ∀ (F G : (adequate.{u, u} B).FullSubcategory),
      Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G 1) := by
  intro F G
  have hmem : ∀ Z : SheafOfModules.{u} B.structureSheaf,
      (adequate.{u, u} B).ι.essImage Z → adequate.{u, u} B Z := by
    rintro Z ⟨W, ⟨e⟩⟩
    exact (adequate.{u, u} B).prop_of_iso e W.property
  refine (adequate.{u, u} B).ι.bijective_mapExtAddHom_one_of_essImage_shortExact.{u + 1, u + 1}
    (fun S hS h₁ h₃ ↦ ⟨⟨S.X₂, (adequate_isClosedUnderExtensions B).prop_X₂_of_shortExact hS
      (hmem _ h₁) (hmem _ h₃)⟩, ⟨Iso.refl _⟩⟩) F G

/-- For `U = Spec A` affine, the natural map
`Ext^n_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^n_{Mod((Sch/U)_τ, 𝒪)}(𝓕, 𝓖)` is bijective for all adequate `𝓕`,
`𝓖` and every `n`, as soon as, in the module-valued functors on the `A`-algebras of the site, the
positive-degree extension groups from linearly adequate functors into extensions of scalars of
modules vanish. -/
public theorem bijective_mapExtAddHom_ι_adequate_of_siteModuleExtension :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (siteModuleFunctors B) := HasExt.standard _
    (∀ X : siteModuleFunctors B,
      AdequateFunctor.IsLinearlyAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) X →
      ∀ (M : ModuleCat.{u} A) (q : ℕ),
        Subsingleton (Abelian.Ext.{u + 1} (C := siteModuleFunctors B) X
          ((AdequateFunctor.moduleExtensionFunctorOn.{u, u}
            (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj M)
          (q + 1))) →
      ∀ (F G : (adequate.{u, u} B).FullSubcategory) (n : ℕ),
        Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G n) := by
  intro hcore
  let : HasExt.{u + 1} (siteModuleFunctors B) := HasExt.standard _
  refine bijective_mapExtAddHom_ι_adequate_of_isZero_rightDerived B fun G p hp ↦ ?_
  refine isZero_rightDerived_affineAdequator_of_site.{u + 1} B (fun X Y hX hY p hp ↦ ?_) G p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by lia⟩
  exact subsingleton_ext_siteModuleFunctors_of_moduleExtension B X hX (hcore X hX) Y hY q

/-- The module-valued functors on the `A`-algebras of the site are the module-valued functors on
the full subcategory `algebraInSite A (schemeSizeBelow B.cutoff)`. -/
public theorem siteModuleFunctors_eq :
    siteModuleFunctors B = AdequateFunctor.ModuleValuedFunctorOn.{u, u}
      (AdequateFunctor.algebraInSite (A : Type u) (schemeSizeBelow B.cutoff)).ι :=
  rfl

attribute [local instance] HasDerivedCategory.standard in
/-- `Ext` vanishing in the derived-category form `Abelian.zExt` gives it in Mathlib's form
`Abelian.Ext.{u + 1}`, on the module-valued functors on the algebras of the site. -/
public theorem subsingleton_ext_siteModuleFunctors_of_zExt
    (X Y : siteModuleFunctors B) (n : ℕ) (h : Subsingleton (Abelian.zExt X Y n)) :
    letI : HasExt.{u + 1} (siteModuleFunctors B) := HasExt.standard _
    Subsingleton (Abelian.Ext.{u + 1} X Y n) :=
  let : HasExt.{u + 1} (siteModuleFunctors B) := HasExt.standard _
  (Abelian.Ext.homEquiv.{u + 1, u + 1} (X := X) (Y := Y) (n := n)).subsingleton_congr.mpr h

attribute [local instance] HasDerivedCategory.standard in
/-- For `U = Spec A` affine, the natural map
`Ext^n_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^n_{Mod((Sch/U)_τ, 𝒪)}(𝓕, 𝓖)` is bijective for all adequate `𝓕`,
`𝓖` and every `n`, as soon as `Abelian.zExt` from linearly adequate functors into module
extensions over the algebras of the site vanishes in positive degrees. -/
public theorem bijective_mapExtAddHom_ι_adequate_of_siteZExt :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    (∀ X : siteModuleFunctors B,
      AdequateFunctor.IsLinearlyAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) X →
      ∀ (M : ModuleCat.{u} A) (i : ℤ), 0 < i →
        Subsingleton (Abelian.zExt X
          ((AdequateFunctor.moduleExtensionFunctorOn.{u, u}
            (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj M) i)) →
      ∀ (F G : (adequate.{u, u} B).FullSubcategory) (n : ℕ),
        Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G n) :=
  fun hcore ↦ bijective_mapExtAddHom_ι_adequate_of_siteModuleExtension B fun X hX M q ↦
    subsingleton_ext_siteModuleFunctors_of_zExt B X _ (q + 1)
      (hcore X hX M ((q + 1 : ℕ) : ℤ) (by lia))

end Stacks.Adequate

end
