module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatAffineCartesianWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeCartesianLargeSections

/-!
# `LQCoh^fbc` is a weak Serre subcategory of the étale modules at module universe `u + 1`

Let `𝒳` be a category fibred in groupoids over `(Sch/S)_{fppf}`. At a module universe above the
universe of the schemes, a locally quasi-coherent module `F` (Stacks 06WJ) has the flat base change
property of Stacks 0762, read with the pullback of sheaves, exactly when it is cartesian on flat
arrows between objects over affine schemes: the forward direction is
`bijective_restrictionBaseChange_of_isLocallyBijectiveRestrictModulePullbackComparison`, the
converse `hasSheafFlatBaseChangePropertyUnivLE_of_isCartesianOnFlatAffineArrows`. Hence
**Stacks 0771 (2)** for `Mod(𝒳_ét, 𝒪_𝒳)` at module universe `u + 1` is
`isWeakSerreClass_isLocallyQuasicoherent_isCartesianOnFlatAffineArrows_succ`. All names in this
docstring are in the namespace `AlgebraicGeometry.Stack`.

## Main results

* `hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows`
* `isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_succ`
* `isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeEtaleModulesSucc`

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The flat base change property of Stacks 0762 is cartesianness on flat affine arrows**, for
a locally quasi-coherent module at module universe `max (u + 1) v w m`. -/
theorem hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows
    {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherent B E h S hS p hp F) :
    HasSheafFlatBaseChangeProperty.{u, v, w, max (u + 1) v w m} B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) F ↔
      IsCartesianOnFlatAffineArrows.{u, v, w, m} B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F :=
  ⟨fun hbc _ _ φ hφ hx hy =>
    bijective_restrictionBaseChange_of_isLocallyBijectiveRestrictModulePullbackComparison.{u, v, w,
      m} B E h S hS p hp F hF φ (hbc φ hφ) hx hy,
    hasSheafFlatBaseChangePropertyUnivLE_of_isCartesianOnFlatAffineArrows F⟩

section Succ

variable {𝒵 : Type (u + 1)} [Category.{u} 𝒵] (r : 𝒵 ⥤ BigFppfOver B S hS)
  (hr : r.IsFiberedInGroupoids)

/-- **Stacks 0771 (2) for `Mod(𝒳_ét, 𝒪_𝒳)` at module universe `u + 1`**, for a category fibred in
groupoids whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u`: the étale
sheaves of modules which are locally quasi-coherent and have the flat base change property of
Stacks 0762, read with the pullback of sheaves, form a weak Serre subcategory. -/
theorem isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_succ :
    letI := abelian_etaleModuleSheavesSucc B S hS r hr
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS r hr (etaleTopology B)
        (etaleTopology_le_topology B)))
      (fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
        B E h S hS r hr F.val) := by
  let := abelian_etaleModuleSheavesSucc B S hS r hr
  convert isWeakSerreClass_isLocallyQuasicoherent_isCartesianOnFlatAffineArrows_succ
    B E h S hS r hr using 1
  funext F
  exact propext (and_congr_right fun hF =>
    (hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows.{u, u + 1, u, u}
      B E h S hS r hr F.val hF))

end Succ

/-- **Stacks 0771 (2) for `Mod(𝒳_ét, 𝒪_𝒳)` at module universe `u + 1`, for an algebraic stack**:
`LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of the étale sheaves of modules. -/
theorem isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeEtaleModulesSucc
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI : Abelian (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale)) :=
      abelian_etaleModuleSheavesSucc B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModulesUnivLE.{u, w, u + 1} B E h S hS
      𝒳).IsWeakSerreClass :=
  isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_succ.{u} B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
