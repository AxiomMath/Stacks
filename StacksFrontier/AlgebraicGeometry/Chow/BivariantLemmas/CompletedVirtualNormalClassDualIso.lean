module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalRank

/-!
# The class of a virtual normal sheaf at arbitrary rank depends only on its dual

The class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBK, for a virtual normal sheaf `𝒩` of
arbitrary rank for a closed immersion, depends on `𝒩` only up to an isomorphism of duals
`𝒩'^∨ ≅ 𝒩^∨` compatible with the surjections onto the conormal sheaf.

## Main results

* `Stacks.Chow.VirtualNormalBundle.baseChangeDualIsoOfDualIso` — the base change (Stacks 0FBJ) of
  an isomorphism of duals.
* `Stacks.Chow.componentRank_eq_of_dualIso` — finite locally free modules with isomorphic duals
  have the same rank on every connected component.
* `Stacks.Chow.completedVirtualNormalGysinClass_eq_of_dualIso` — the class at arbitrary rank
  depends on `𝒩` only up to an isomorphism of duals compatible with the surjections.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Chow

/-! ### Base change of an isomorphism of duals -/

section DualIso

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] {i' : Z' ⟶ X'} [IsImmersion i']
  (g : Z' ⟶ Z) (f : X' ⟶ X) (sq : IsPullback i' g f i) {𝒩 𝒩' : VirtualNormalBundle i}
  (ψ : dualSheaf 𝒩'.bundle ≅ dualSheaf 𝒩.bundle)

/-- **The base change of an isomorphism of duals** along a cartesian square (Stacks 0FBJ): the
pullback of `ψ : 𝒩'^∨ ≅ 𝒩^∨`, read through the dual base-change isomorphisms. -/
def VirtualNormalBundle.baseChangeDualIsoOfDualIso :
    dualSheaf (𝒩'.baseChange i i' g f sq).bundle ≅ dualSheaf (𝒩.baseChange i i' g f sq).bundle :=
  (@asIso _ _ _ _ (pullbackDualMap g 𝒩'.bundle)
      (pullbackDualMap_isIso g 𝒩'.bundle 𝒩'.isFiniteLocallyFree)).symm ≪≫
    (modulePullback g.toLRSHom.toShHom).mapIso ψ ≪≫
    @asIso _ _ _ _ (pullbackDualMap g 𝒩.bundle)
      (pullbackDualMap_isIso g 𝒩.bundle 𝒩.isFiniteLocallyFree)

/-- The base change of an isomorphism of duals compatible with the surjections is compatible with
the surjections of the base changes. -/
theorem VirtualNormalBundle.baseChangeDualIsoOfDualIso_hom_comp_surjection
    (hψ : ψ.hom ≫ 𝒩.surjection = 𝒩'.surjection) :
    (VirtualNormalBundle.baseChangeDualIsoOfDualIso g f sq ψ).hom ≫
        (𝒩.baseChange i i' g f sq).surjection = (𝒩'.baseChange i i' g f sq).surjection := by
  rw [VirtualNormalBundle.baseChange_surjection, VirtualNormalBundle.baseChange_surjection]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (((modulePullback g.toLRSHom.toShHom).map_comp _ _).symm.trans
        (congrArg (modulePullback g.toLRSHom.toShHom).map hψ)))))))

end DualIso

/-! ### The classes at arbitrary rank depend only on the dual up to isomorphism -/

/-- **Two finite locally free modules with isomorphic duals have the same rank on every
connected component.** -/
theorem componentRank_eq_of_dualIso {W : Scheme.{u}} [LocallyConnectedSpace W] {E E' : W.Modules}
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (ψ : dualSheaf E' ≅ dualSheaf E)
    (a : _root_.ConnectedComponents W) : componentRank E a = componentRank E' a :=
  (Scheme.Modules.fiberRank_dualSheaf E inferInstance _).symm.trans
    ((Scheme.Modules.fiberRank_eq_of_iso ψ.symm _).trans
      (Scheme.Modules.fiberRank_dualSheaf E' inferInstance _))

section Completed

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  (𝒩 𝒩' : VirtualNormalBundle i) (ψ : dualSheaf 𝒩'.bundle ≅ dualSheaf 𝒩.bundle)
  (hψ : ψ.hom ≫ 𝒩.surjection = 𝒩'.surjection)

include hψ in
/-- **Stacks 0FBK at arbitrary rank: `c(Z ⟶ X, 𝒩)` depends on `𝒩` only up to an isomorphism of
duals compatible with the surjections.** On a connected component `Z_a` the ranks of `𝒩` and `𝒩'`
agree, since a finite locally free module has the fibre rank of its dual, and there the classes
are equal by the constant-rank statement for `𝒩|_{Z_a}`, `𝒩'|_{Z_a}`. -/
theorem completedVirtualNormalGysinClass_eq_of_dualIso :
    completedVirtualNormalGysinClass C sZ sX i hi 𝒩 =
      completedVirtualNormalGysinClass C sZ sX i hi 𝒩' := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  funext a
  rw [completedVirtualNormalGysinClass_apply, completedVirtualNormalGysinClass_apply]
  have key : ∀ (r r' : ℕ) (_ : r = r')
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.toComponent i a).bundle r]
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩'.toComponent i a).bundle r'],
      DirectSum.of _ (r : ℤ)
        (BivariantClass.copy C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens a).ι ≫ sZ)
          ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
          (componentRestriction_comp_componentInclusion i a) _
          (i.resConnectedComponent_comp_ι_comp hi a) (by simp)
          (openImmersionComposite C ((Z.connectedComponentOpens a).ι ≫ sZ)
            ((componentNeighbourhood i a).ι ≫ sX)
            ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
            (componentRestriction i a) (componentInclusion i a)
            (componentRestriction_comp_structureMorphism C sZ sX i hi a)
            (by rw [← Category.assoc, Scheme.homOfLE_ι]) (r : ℤ)
            (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
              ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
              (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a)
              r))) =
      DirectSum.of _ (r' : ℤ)
        (BivariantClass.copy C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens a).ι ≫ sZ)
          ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
          (componentRestriction_comp_componentInclusion i a) _
          (i.resConnectedComponent_comp_ι_comp hi a) (by simp)
          (openImmersionComposite C ((Z.connectedComponentOpens a).ι ≫ sZ)
            ((componentNeighbourhood i a).ι ≫ sX)
            ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
            (componentRestriction i a) (componentInclusion i a)
            (componentRestriction_comp_structureMorphism C sZ sX i hi a)
            (by rw [← Category.assoc, Scheme.homOfLE_ι]) (r' : ℤ)
            (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
              ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
              (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩'.toComponent i a)
              r'))) := by
    intro r r' h _ _
    subst h
    rw [virtualNormalGysinClass_eq_of_dualIso C _ _ _ _ (𝒩.toComponent i a) (𝒩'.toComponent i a)
      (VirtualNormalBundle.baseChangeDualIsoOfDualIso _ _ _ ψ)
      (VirtualNormalBundle.baseChangeDualIsoOfDualIso_hom_comp_surjection _ _ _ ψ hψ) r]
  exact key _ _ (componentRank_eq_of_dualIso ψ a)

end Completed

end Stacks.Chow

end
