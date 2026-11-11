module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.SiteEquivalenceCohomologyVanishing

/-!
# Transporting the vanishing of the cohomology of the structure sheaf

The cohomology `Hⁿ(X, 𝒪_X)` of the structure sheaf of an algebraic space `X` on its small étale
site does not depend on how `X` is presented. This file shows that its vanishing is unchanged

* from the Zariski cohomology of a scheme `T` to the étale cohomology of the algebraic space it
  represents (Descent, Proposition 03DX, through
  `AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIso`);
* along an isomorphism of algebraic spaces over the same base;
* along the lower-shriek extension `Λ_h` of algebraic spaces from a base `W` to a base `S`
  (Stacks 04SG), the small étale sites of `Λ_h X` and `X` being equivalent.

Combined, the vanishing of `H¹(T, 𝒪_T)` for a scheme `T` over `Spec K` gives the vanishing of
`H¹(Z, 𝒪_Z)` for an algebraic space `Z` over `Spec A` whose lower-shriek extension along
`Spec A ⟶ Spec K` is isomorphic to `T`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_unit_schemeSpace_iff`: `Hⁿ(T, 𝒪_T) = 0` (Zariski)
  exactly when `Hⁿ(h_T, 𝒪) = 0` (étale) for the space `h_T` represented by `T`.
* `AlgebraicGeometry.Space.isZero_rightDerived_unit_iff_of_iso`: invariance under an isomorphism
  of algebraic spaces.
* `AlgebraicGeometry.Space.isZero_rightDerived_unit_relocalizeSpace_iff`: invariance under the
  lower-shriek extension.
* `AlgebraicGeometry.Space.isZero_rightDerived_one_unit_of_iso_relocalizeSpace`: the combination,
  in degree one.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.SiteModules

/-! ### Invariance under an isomorphism of algebraic spaces -/

section Iso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The vanishing of `Hⁿ(X, 𝒪_X)` is invariant under isomorphism of algebraic spaces**: for
`X ≅ Y` over the same base, `Hⁿ(X, 𝒪_X) = 0` exactly when `Hⁿ(Y, 𝒪_Y) = 0`. The small étale
sites of `X` and `Y` are equivalent (`AlgebraicGeometry.Space.SmallEtale.congr`), with the same
underlying schemes, so that the structure sheaves correspond. -/
theorem isZero_rightDerived_unit_iff_of_iso {X Y : AlgebraicSpaces B S hS} (φ : X ≅ Y)
    (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived
        n).obj (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ↔
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived
        n).obj (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) := by
  intro _ _
  let e := SmallEtale.congr B S hS ((ObjectProperty.ι _).mapIso φ)
  have : e.functor.IsContinuous (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1) :=
    SmallEtale.congr_functor_isContinuous B S hS _
  have : e.inverse.IsContinuous (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1) :=
    Functor.isContinuous_iff_coverPreserving.2 (SmallEtale.congr_inverse_coverPreserving B S hS _)
  let R : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u} :=
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O
  have : HasInjectiveResolutions (SheafOfModules.{u} R) :=
    hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have : HasInjectiveResolutions (SheafOfModules.{u} (Stacks.SheafOfModules.reindexRing
      (SmallEtale.topology B S hS X.1) e R)) :=
    hasInjectiveResolutions_modules B S hS X.1 X.2
  exact (isZero_rightDerived_unit_reindex_iff (SmallEtale.topology B S hS X.1) e R n).symm

end Iso

/-! ### Invariance under the lower-shriek extension -/

section Relocalize

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **The vanishing of `Hⁿ(X, 𝒪_X)` does not depend on the base**: for an algebraic space `X`
over `W` and its lower-shriek extension `Λ_h X` along `h : W ⟶ S`, `Hⁿ(Λ_h X, 𝒪) = 0` exactly
when `Hⁿ(X, 𝒪_X) = 0`. The small étale sites of `Λ_h X` and of `X` are equivalent
(`AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`, Stacks 04SG), with the same
structure sheaf. -/
theorem isZero_rightDerived_unit_relocalizeSpace_iff (X : AlgebraicSpaces B W hW) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2
    have := hasInjectiveResolutions_modules B W hW X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2).O)).rightDerived
        n).obj (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2).O))) ↔
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B W hW X.1 X.2).O)).rightDerived
        n).obj (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B W hW X.1 X.2).O))) := by
  intro _ _
  let R : Sheaf (SmallEtale.topology B S hS (relocalizeSpace B hW hS h X).1) RingCat.{u} :=
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2).O
  have : HasInjectiveResolutions (SheafOfModules.{u} R) :=
    hasInjectiveResolutions_modules B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2
  have : HasInjectiveResolutions (SheafOfModules.{u} (Stacks.SheafOfModules.reindexRing
      (SmallEtale.topology B W hW X.1) (SmallEtale.relocalizeEquivalence B W S hW hS h X.1) R)) :=
    hasInjectiveResolutions_modules B W hW X.1 X.2
  exact isZero_rightDerived_unit_reindex_iff (SmallEtale.topology B W hW X.1)
    (SmallEtale.relocalizeEquivalence B W S hW hS h X.1) R n

end Relocalize

/-! ### From the Zariski cohomology of a scheme to the étale cohomology of the space -/

section Represented

variable {B : BigFppfSite.{u}} {K : Type u} [CommRing K] {hK : B.Contains (Spec (.of K))}

/-- **The Zariski cohomology of `𝒪_T` vanishes exactly when the étale cohomology of `𝒪` on the
represented space does.** For an object `U` of the big fppf site over `Spec K`, with underlying
scheme `T`, `Hⁿ(T, 𝒪_T) = 0` exactly when `Hⁿ(h_T, 𝒪) = 0` on the small étale site of the
algebraic space `h_T = AlgebraicGeometry.schemeSpace U`. This is
`AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIso` at `𝓕 = 𝒪_T`, whose associated
module is the structure sheaf. -/
theorem isZero_rightDerived_unit_schemeSpace_iff (U : BigFppfOver B (Spec (.of K)) hK) (n : ℕ) :
    have := hasInjectiveResolutions_modules B (Spec (.of K)) hK (schemeSpace U).1
      (schemeSpace U).2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of K)) hK
        (schemeSpace U).1 (schemeSpace U).2).O)).rightDerived n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of K)) hK (schemeSpace U).1 (schemeSpace U).2).O))) ↔
    IsZero (((SheafOfModules.evaluation
        ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U).ringCatSheaf (op ⊤)).rightDerived n).obj
          (SheafOfModules.unit _)) := by
  intro _
  let T := (BigFppfOver.toScheme B (Spec (.of K)) hK).obj U
  let eT := _root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) T
    U.left.property
  have hI : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} eT) := inferInstance
  let a : (_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
      T U.left.property).obj (SheafOfModules.unit T.ringCatSheaf) ≅
      SheafOfModules.unit (representedSchemeStructureSheaf B (Spec (.of K)) hK U) :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} eT) hI
  let b : (representedSmallEtaleModuleEquivalence B (Spec (.of K)) hK U).functor.obj
      (SheafOfModules.unit (representedSchemeStructureSheaf B (Spec (.of K)) hK U)) ≅
      SheafOfModules.unit (representedStructureRingSheaf B (Spec (.of K)) hK U) :=
    Stacks.SheafOfModules.reindexEquivalenceUnitIso _ _ _
  have e := representedCohomologyAssociatedModuleIso K B hK U (SheafOfModules.unit T.ringCatSheaf)
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit T) n
  have h₁ := (((globalSectionsFunctor.{u + 1, u, u, u}
    (representedStructureRingSheaf B (Spec (.of K)) hK U)).rightDerived n).mapIso
      ((representedSmallEtaleModuleEquivalence B (Spec (.of K)) hK U).functor.mapIso a ≪≫ b))
  refine (h₁.isZero_iff.symm.trans ?_)
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  refine Iff.trans ?_ ((ModuleCat.isZero_iff_subsingleton.symm.trans e.isZero_iff).trans
    (ModuleCat.isZero_iff_subsingleton.trans ⟨fun h => ?_, fun h => ?_⟩))
  · exact Iff.rfl
  · exact (Equiv.ulift.symm.subsingleton_congr).2 h
  · exact (Equiv.ulift.symm.subsingleton_congr).1 h

end Represented

/-! ### The combination in degree one -/

/-- **`H¹(𝒪)` vanishes on an algebraic space whose lower-shriek extension is a scheme with
`H¹(T, 𝒪_T) = 0`.** Let `Z` be an algebraic space over `Spec A`, `h : Spec A ⟶ Spec K` a morphism
of the big fppf site, and `U` an object of the big fppf site over `Spec K`, with underlying scheme
`T`, such that `h_T ≅ Λ_h Z` over `Spec K`. If the Zariski cohomology `H¹(T, 𝒪_T)` vanishes, then
so does the étale cohomology `H¹(Z, 𝒪_Z)`. -/
theorem isZero_rightDerived_one_unit_of_iso_relocalizeSpace
    {B : BigFppfSite.{u}} {K A : Type u} [CommRing K] [CommRing A]
    {hK : B.Contains (Spec (.of K))} {hA : B.Contains (Spec (.of A))}
    (h : B.obj hA ⟶ B.obj hK) (U : BigFppfOver B (Spec (.of K)) hK)
    (Z : AlgebraicSpaces B (Spec (.of A)) hA)
    (φ : schemeSpace U ≅ relocalizeSpace B hA hK h Z)
    (hH1 : IsZero (((SheafOfModules.evaluation
        ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U).ringCatSheaf
          (Opposite.op ⊤)).rightDerived 1).obj (SheafOfModules.unit _))) :
    have := hasInjectiveResolutions_modules B (Spec (.of A)) hA Z.1 Z.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA Z.1 Z.2).O)).rightDerived 1).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA Z.1 Z.2).O)))) := by
  intro _
  have h₁ := (isZero_rightDerived_unit_schemeSpace_iff U 1).2 hH1
  have h₂ := (isZero_rightDerived_unit_iff_of_iso φ 1).1 h₁
  exact (isZero_rightDerived_unit_relocalizeSpace_iff B hA hK h Z 1).1 h₂

end AlgebraicGeometry.Space

end
