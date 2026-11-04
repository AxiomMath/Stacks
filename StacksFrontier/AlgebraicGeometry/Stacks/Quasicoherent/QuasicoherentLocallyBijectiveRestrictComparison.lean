module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CartesianRestrictModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsLocallyQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange

/-!
# A quasi-coherent module on a category fibred in groupoids lies in `LQCoh^fbc` (Stacks 06WK)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. The forward direction of
**Stacks 06WK** says that a quasi-coherent module `𝓕` on `(𝒳_{fppf}, 𝒪_𝒳)` (Stacks 06WG)

* (a) is locally quasi-coherent (Stacks 06WJ), and
* (b) has, for *every* arrow `φ : x ⟶ y` of `𝒳` lying over `f : U ⟶ V`, invertible comparison
  map `c_φ : f_{small}^*(𝓕|_{V_ét}) ⟶ 𝓕|_{U_ét}` of Stacks 06WC, the pullback being the pullback
  of sheaves.

Clause (a) is `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite` (and its
large-universe form). This file proves clause (b), in the form of FBC's faithful predicate: the
presheaf comparison is locally bijective, i.e. invertible after sheafifying its source; and it
assembles the two into the inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` for the faithful flat base change
property of Stacks 0762, at module universe `u` and at `u + 1`. Nothing is assumed.

Clause (b) is the comparison-map theorem of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CartesianRestrictModulePullbackComparison`,
applied to the cartesian property of a quasi-coherent module over the affine objects of `𝒳`
(`AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`,
the content of Descent, Proposition 03DX in this library).

## Main results

All in the namespace `AlgebraicGeometry.Stack`:

* `isLocallyBijectiveRestrictModulePullbackComparison_of_isQuasicoherentOnSite` (and
  `…_freeModuleUniverse`): **clause (b) of the forward direction of Stacks 06WK**, for every arrow
  of `𝒳`.
* `hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite_freeModuleUniverse`: Stacks 0762 for a
  quasi-coherent module with sections in a larger universe (the module-universe-`u` form is
  `hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite`).
* `isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse`:
  (a) and (b) together, likewise.
* `isQuasicoherentOnSite_le_locallyQuasicoherentSheafFlatBaseChangeFppfModules` and `…_succ`:
  **`QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` in `Mod(𝒪_𝒳)`** for an algebraic stack, at module universes `u`
  and `u + 1`; `locallyQuasicoherentSheafFlatBaseChangeEtaleModules_toSiteModules` and `…_succ`:
  the same in `Mod(𝒳_ét, 𝒪_𝒳)`.

## References

* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

open AffineCategory in
/-- **A quasi-coherent module on `𝒳_{fppf}` is cartesian over the arrows between affine objects**:
its base-change comparison `𝒪(x₁) ⊗_{𝒪(x₂)} 𝓕(x₂) ⟶ 𝓕(x₁)` is bijective. -/
theorem bijective_restrictionBaseChange_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) {x₁ x₂ : 𝒳} (e : x₁ ⟶ x₂)
    (h₁ : _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)))
    (h₂ : _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂))) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) M.val)
      e.op) := by
  have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := isCocontinuous_inclusion_siteKind B S hS p hp .fppf
  have hres := Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite
    (J := associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
    (K := BigFppfOver.associatedTopology B S hS p .fppf)
    (AffineCategory.inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf) M hM
  let f : (⟨x₁, h₁⟩ : AffineCategory B S hS p) ⟶ ⟨x₂, h₂⟩ := ObjectProperty.homMk e
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_restrictionBaseChange_of_isQuasicoherentOnSite B S hS p _ rfl hp .fppf _ _ hres f.op)

/-- A quasi-coherent module on `𝒳_{fppf}` is cartesian over the arrows between affine objects, at
module universe `max (u + 1) v w m`. -/
theorem bijective_restrictionBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse
    (M : SheafOfModules.{max (u + 1) v w m}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) {x₁ x₂ : 𝒳} (e : x₁ ⟶ x₂)
    (h₁ : _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)))
    (h₂ : _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂))) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u,
      max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (commRestrictModule.{u, v, w, max (u + 1) v w m} B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) M.val) e.op) := by
  let f : (⟨x₁, h₁⟩ : AffineCategory B S hS p) ⟶ ⟨x₂, h₂⟩ := ObjectProperty.homMk e
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_restrictionBaseChange_affine_of_isQuasicoherentOnSite_freeModuleUniverse.{u, v, w, m}
      B S hS p hp M hM f)

/-- **Clause (b) of the forward direction of Stacks 06WK, for the pullback of sheaves.** For a
quasi-coherent module on `(𝒳_{fppf}, 𝒪_𝒳)` and every arrow `φ : x ⟶ y` of `𝒳`, the comparison
map `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of Stacks 06WC is locally bijective, i.e. it is
an isomorphism of sheaves after sheafifying its source. -/
theorem isLocallyBijectiveRestrictModulePullbackComparison_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) {x y : 𝒳} (φ : x ⟶ y) :
    IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE.{u, v, w, u} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) φ M.val :=
  isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_cartesian.{u, v, w, u}
    B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ M.val
    (fun _ _ e h₁ h₂ => bijective_restrictionBaseChange_of_isQuasicoherentOnSite B S hS p hp M hM e
      h₁ h₂)

/-- Clause (b) of the forward direction of Stacks 06WK, at module universe `max (u + 1) v w m`. -/
theorem
    isLocallyBijectiveRestrictModulePullbackComparison_of_isQuasicoherentOnSite_freeModuleUniverse
    (M : SheafOfModules.{max (u + 1) v w m}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) {x y : 𝒳} (φ : x ⟶ y) :
    IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE.{u, v, w, max (u + 1) v w m}
      B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ M.val :=
  isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_cartesian.{u, v, w,
    max (u + 1) v w m}
    B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ M.val
    (fun _ _ e h₁ h₂ =>
      bijective_restrictionBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse.{u, v, w, m}
        B S hS p hp M hM e h₁ h₂)

/-- Stacks 0762 for a quasi-coherent module, at module universe `max (u + 1) v w m`. -/
theorem hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite_freeModuleUniverse
    (M : SheafOfModules.{max (u + 1) v w m}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    HasSheafFlatBaseChangeProperty.{u, v, w, max (u + 1) v w m} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) M.val :=
  fun φ _ =>
    isLocallyBijectiveRestrictModulePullbackComparison_of_isQuasicoherentOnSite_freeModuleUniverse.{
      u, v, w, m} B E h S hS p hp M hM φ

/-- The forward direction of Stacks 06WK, at module universe `max (u + 1) v w m`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse
    (M : SheafOfModules.{max (u + 1) v w m}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, max (u + 1) v w m}
      B E h S hS p hp M.val :=
  ⟨isLocallyQuasicoherent_of_isQuasicoherentOnSite_freeModuleUniverse.{u, v, w, m}
      B E h S hS p hp M hM,
    hasSheafFlatBaseChangeProperty_of_isQuasicoherentOnSite_freeModuleUniverse.{u, v, w, m}
      B E h S hS p hp M hM⟩

section AlgebraicStacks

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 06WK, forward direction, in `Mod(𝒪_𝒳)`**: `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` for the
faithful flat base change property of Stacks 0762, at module universe `u`. -/
theorem isQuasicoherentOnSite_le_locallyQuasicoherentSheafFlatBaseChangeFppfModules :
    SheafOfModules.isQuasicoherentOnSite (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf) ≤
      lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 :=
  fun M hM => isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M hM

/-- **Stacks 06WK, forward direction, in `Mod(𝒪_𝒳)` at module universe `u + 1`**:
`QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` for the faithful flat base change property. -/
theorem isQuasicoherentOnSite_le_locallyQuasicoherentSheafFlatBaseChangeFppfModules_succ :
    SheafOfModules.isQuasicoherentOnSite.{u + 1} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) ≤
      lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳 :=
  fun M hM =>
    isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse.{u,
      u + 1, u, u} B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M hM

/-- **Stacks 06WK, forward direction, in `Mod(𝒳_ét, 𝒪_𝒳)`**: the étale module underlying a
quasi-coherent module on `𝒳` (Stacks 06WG) lies in `LQCoh^fbc(𝒪_𝒳)`, at module universe `u`. -/
theorem locallyQuasicoherentSheafFlatBaseChangeEtaleModules_toSiteModules
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳
      ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).obj M) :=
  isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.obj M.property

/-- Stacks 06WK, forward direction, in `Mod(𝒳_ét, 𝒪_𝒳)` at module universe `u + 1`. -/
theorem locallyQuasicoherentSheafFlatBaseChangeEtaleModules_toSiteModules_succ
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    locallyQuasicoherentSheafFlatBaseChangeEtaleModulesUnivLE.{u, w, u + 1} B E h S hS 𝒳
      ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).obj M) :=
  isLocallyQuasicoherentWithSheafFlatBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse.{u,
    u + 1, u, u} B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.obj M.property

end AlgebraicStacks

end AlgebraicGeometry.Stack
