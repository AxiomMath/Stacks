module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatGroupoidPresentationRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerre

/-!
# The two readings of `LQCoh^fbc(𝒪_𝒳)` on sheaves agree

The library states the flat base change property of **Stacks 0762**, read on sheaves of modules,
in two ways:

* `AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheaf` asks that the components of
  `AlgebraicGeometry.Stack.sheafifiedRestrictComparisonNatTrans` be isomorphisms along arrows over
  flat morphisms;
* `AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty` asks that the comparison map of
  presheaves of modules be a local isomorphism for the small étale topology, which for an étale
  sheaf is invertibility of the components of `AlgebraicGeometry.Stack.sheafRestrictComparison`
  (`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison`).

Both comparison maps of sheaves are the sheafification adjunct of the same comparison map of
presheaves of modules, so they coincide, and the two readings of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`,
`AlgebraicGeometry.Stack.lqcFbcFppf` and `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`, are
the same object property.  So are the subcategories `D_{LQCoh^fbc}(𝒪_𝒳)` of the derived category
they cut out.

## Main results

* `AlgebraicGeometry.Stack.sheafifiedRestrictComparisonNatTrans_app_eq_sheafRestrictComparison_app`:
  the two comparison maps of sheaves agree.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_iff_hasSheafFlatBaseChangeProperty`.
* `AlgebraicGeometry.Stack.lqcFbcFppf_iff_lqcohSheafFbcFppfModules` and
  `AlgebraicGeometry.Stack.lqcFbcFppf_eq_lqcohSheafFbcFppfModules`.
* `AlgebraicGeometry.Stack.derivedCategoryB_lqcFbcFppf_eq`.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w t

namespace AlgebraicGeometry.Stack

section Fibred

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The comparison map `c_φ : a_{small}^*(ℱ|_{V_ét}) ⟶ ℱ|_{U_ét}` of **Stacks 06WC** read on
sheaves of modules is the same map in its two packagings: both
`AlgebraicGeometry.Stack.sheafifiedRestrictComparisonNatTrans` and
`AlgebraicGeometry.Stack.sheafRestrictComparison` have as component at `ℱ` the sheafification
adjunct of the comparison map of presheaves of modules. -/
theorem sheafifiedRestrictComparisonNatTrans_app_eq_sheafRestrictComparison_app {x z : 𝒳}
    (φ : z ⟶ x)
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    (sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ).app ℱ =
      (sheafRestrictComparison B E h S hS p hp φ).app ℱ :=
  rfl

/-- **The two readings of Stacks 0762 on étale sheaves agree.** An étale sheaf of
`𝒪_𝒳`-modules has the flat base change property read through
`AlgebraicGeometry.Stack.sheafifiedRestrictComparisonNatTrans` if and only if its underlying
presheaf has the flat base change property `AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`
(the comparison maps of presheaves being local isomorphisms). -/
theorem hasFlatBaseChangePropertySheaf_iff_hasSheafFlatBaseChangeProperty
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    HasFlatBaseChangePropertySheaf B E h S hS p hp ℱ ↔
      HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ℱ.val := by
  rw [hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison]
  exact ⟨fun H _ _ φ hφ => H φ hφ, fun H _ _ φ hφ => H φ hφ⟩

/-- An étale sheaf of `𝒪_𝒳`-modules lies in
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheaf` if and only if its underlying
presheaf satisfies `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange`. -/
theorem locallyQuasicoherentFlatBaseChangeSheaf_iff
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp ℱ ↔
      IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp ℱ.val :=
  and_congr Iff.rfl (hasFlatBaseChangePropertySheaf_iff_hasSheafFlatBaseChangeProperty
    B E h S hS p hp ℱ)

/-- An fppf sheaf of `𝒪_𝒳`-modules lies in
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafFppf` if and only if its
underlying presheaf satisfies
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange`: restriction to the étale
topology does not change the underlying presheaf of modules. -/
theorem locallyQuasicoherentFlatBaseChangeSheafFppf_iff
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) :
    locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp F ↔
      IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F.val :=
  locallyQuasicoherentFlatBaseChangeSheaf_iff B E h S hS p hp
    ((fppfToEtaleSheafOfModules B S hS p hp).obj F)

end Fibred

section Stack

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`: the two readings agree, elementwise.** A sheaf of
`𝒪_𝒳`-modules on an algebraic stack lies in `AlgebraicGeometry.Stack.lqcFbcFppf` if and only if
it lies in `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules` (at module universe `u`, over the
big étale site associated with `B`). -/
theorem lqcFbcFppf_iff_lqcohSheafFbcFppfModules (F : fppfModules B S hS 𝒳) :
    lqcFbcFppf B S hS 𝒳 F ↔
      lqcohSheafFbcFppfModules.{u, w, u} B (associatedBigEtaleSite B) rfl S hS 𝒳 F :=
  locallyQuasicoherentFlatBaseChangeSheafFppf_iff B (associatedBigEtaleSite B) rfl S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`: the two readings agree.** The object properties
`AlgebraicGeometry.Stack.lqcFbcFppf` and `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules` (at
module universe `u`, over the big étale site associated with `B`) are equal. -/
theorem lqcFbcFppf_eq_lqcohSheafFbcFppfModules :
    lqcFbcFppf B S hS 𝒳 =
      lqcohSheafFbcFppfModules.{u, w, u} B (associatedBigEtaleSite B) rfl S hS 𝒳 :=
  funext fun F => propext (lqcFbcFppf_iff_lqcohSheafFbcFppfModules B S hS 𝒳 F)

/-- **The two readings of `D_{LQCoh^fbc}(𝒪_𝒳)` agree.** For any choice of derived category of
`Mod(𝒪_𝒳)`, the complexes whose cohomology sheaves lie in `AlgebraicGeometry.Stack.lqcFbcFppf` are
those whose cohomology sheaves lie in `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`. -/
theorem derivedCategoryB_lqcFbcFppf_eq [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)] :
    DerivedCategoryB.derivedCategoryB (lqcFbcFppf B S hS 𝒳) =
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, w, u} B (associatedBigEtaleSite B) rfl S hS 𝒳) := by
  rw [lqcFbcFppf_eq_lqcohSheafFbcFppfModules]

end Stack

end AlgebraicGeometry.Stack

end
