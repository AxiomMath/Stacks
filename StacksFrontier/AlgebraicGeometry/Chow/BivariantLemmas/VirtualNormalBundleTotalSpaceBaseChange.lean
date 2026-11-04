module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleConeEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleClassifyingMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vector bundle of a base-changed virtual normal bundle

For a cartesian square of closed immersions and a virtual normal bundle `𝒩` for `Z ⟶ X`, the
vector bundle `V(g^*𝒩)` of the base-changed virtual normal bundle of [Stacks, Tag 0FBJ] is the
base change `V(𝒩) ×_Z Z'` of the vector bundle of `𝒩`.

## References

* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F G : SheafOfModules.{u} X.ringCatSheaf} [F.IsQuasicoherent]
  [G.IsQuasicoherent]

/-- The morphism of vector bundles induced by an isomorphism of modules is an isomorphism. -/
instance isIso_vectorBundleMap (f : F ⟶ G) [IsIso f] : IsIso (vectorBundleMap X f) :=
  ⟨vectorBundleMap X (inv f), by rw [← vectorBundleMap_comp, IsIso.inv_hom_id, vectorBundleMap_id],
    by rw [← vectorBundleMap_comp, IsIso.hom_inv_id, vectorBundleMap_id]⟩

/-- The underlying morphism of schemes of the morphism of vector bundles induced by an
isomorphism of modules is an isomorphism. -/
instance isIso_vectorBundleMap_left (f : F ⟶ G) [IsIso f] : IsIso (vectorBundleMap X f).left :=
  inferInstanceAs (IsIso ((Over.forget X).map (vectorBundleMap X f)))

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i']
  (g : Z' ⟶ Z) (f : X' ⟶ X) (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i)

/-- **The vector bundle of `g^*𝒩` is the base change of that of `𝒩`**: `V(g^*𝒩) ≅ V(𝒩) ×_Z Z'`,
through the dual base-change isomorphism `(g^*𝒩)^∨ ≅ g^*(𝒩^∨)` and Stacks 01CI. -/
@[ega "IV 18.5.1" "V(E∨) ×_Z Z′ ≅ V((g*E)∨)"]
def VirtualNormalBundle.baseChangeTotalSpaceIso :
    (𝒩.baseChange i i' g f sq).totalSpace ≅ pullback 𝒩.projection g :=
  @asIso _ _ _ _ (Scheme.Modules.vectorBundleMap Z'
      (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (G := dualSheaf (𝒩.baseChange i i' g f sq).bundle) (pullbackDualMap g 𝒩.bundle)).left
      (@Scheme.Modules.isIso_vectorBundleMap_left _
        ((Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
        (dualSheaf (𝒩.baseChange i i' g f sq).bundle) inferInstance inferInstance
        (pullbackDualMap g 𝒩.bundle)
        (pullbackDualMap_isIso g 𝒩.bundle 𝒩.isFiniteLocallyFree)) ≪≫
    (Scheme.Modules.vectorBundlePullbackIso g (dualSheaf 𝒩.bundle)).symm

/-- **The morphism `V(g^*𝒩) ⟶ V(𝒩)` over `g`.** -/
def VirtualNormalBundle.baseChangeTotalSpaceMap :
    (𝒩.baseChange i i' g f sq).totalSpace ⟶ 𝒩.totalSpace :=
  (𝒩.baseChangeTotalSpaceIso i i' g f sq).hom ≫ pullback.fst _ _

/-- The isomorphism `V(g^*𝒩) ≅ V(𝒩) ×_Z Z'` followed by the second projection is the bundle
projection `V(g^*𝒩) ⟶ Z'`. -/
theorem VirtualNormalBundle.baseChangeTotalSpaceIso_hom_snd :
    (𝒩.baseChangeTotalSpaceIso i i' g f sq).hom ≫ pullback.snd 𝒩.projection g =
      (𝒩.baseChange i i' g f sq).projection := by
  have h1 : (Scheme.Modules.vectorBundlePullbackIso g (dualSheaf 𝒩.bundle)).inv ≫
      pullback.snd 𝒩.projection g = Scheme.Modules.vectorBundleToBase Z'
        ((Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle)) :=
    (Iso.inv_comp_eq _).mpr
      (Scheme.Modules.vectorBundlePullbackIso_hom_vectorBundleToBase g _).symm
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans ?_)
  exact Scheme.Modules.vectorBundleMap_left_comp Z'
    (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
    (G := dualSheaf (𝒩.baseChange i i' g f sq).bundle) (pullbackDualMap g 𝒩.bundle)

/-- **`V(g^*𝒩) = V(𝒩) ×_Z Z'`**: the square formed by `V(g^*𝒩) ⟶ V(𝒩)` and the two bundle
projections is cartesian. -/
theorem VirtualNormalBundle.isPullback_baseChangeTotalSpaceMap :
    IsPullback (𝒩.baseChangeTotalSpaceMap i i' g f sq) (𝒩.baseChange i i' g f sq).projection
      𝒩.projection g :=
  IsPullback.of_iso_pullback ⟨by
      rw [← VirtualNormalBundle.baseChangeTotalSpaceIso_hom_snd,
        VirtualNormalBundle.baseChangeTotalSpaceMap, Category.assoc, Category.assoc,
        pullback.condition]⟩
    (𝒩.baseChangeTotalSpaceIso i i' g f sq) rfl
    (VirtualNormalBundle.baseChangeTotalSpaceIso_hom_snd i i' g f sq 𝒩)

/-- The morphism `V(g^*𝒩) ⟶ V(𝒩)` as a morphism of schemes over `Z`. -/
def VirtualNormalBundle.baseChangeTotalSpaceOver :
    (Over.map g).obj (Scheme.Modules.vectorBundleOver Z'
        (F := dualSheaf (𝒩.baseChange i i' g f sq).bundle)) ⟶
      Scheme.Modules.vectorBundleOver Z (F := dualSheaf 𝒩.bundle) :=
  (Over.map g).map (Scheme.Modules.vectorBundleMap Z'
      (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (G := dualSheaf (𝒩.baseChange i i' g f sq).bundle) (pullbackDualMap g 𝒩.bundle)) ≫
    Scheme.Modules.vectorBundlePullbackProjection g (dualSheaf 𝒩.bundle)

/-- The underlying morphism of schemes of `baseChangeTotalSpaceOver` is
`baseChangeTotalSpaceMap`. -/
theorem VirtualNormalBundle.baseChangeTotalSpaceOver_left :
    (𝒩.baseChangeTotalSpaceOver i i' g f sq).left = 𝒩.baseChangeTotalSpaceMap i i' g f sq :=
  (Category.assoc _ _ _).symm

/-- **The classifying module map of `Y ⟶ V(g^*𝒩) ⟶ V(𝒩)`** is the transpose of the dual
base-change map followed by the classifying map of `Y ⟶ V(g^*𝒩)`. -/
theorem VirtualNormalBundle.vectorBundleClassifyingMap_map_comp_baseChangeTotalSpaceOver
    {Y : Over Z'} (k : Y ⟶ Scheme.Modules.vectorBundleOver Z'
      (F := dualSheaf (𝒩.baseChange i i' g f sq).bundle)) :
    Scheme.Modules.vectorBundleClassifyingMap (dualSheaf 𝒩.bundle)
        ((Over.map g).map k ≫ 𝒩.baseChangeTotalSpaceOver i i' g f sq) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _ ≫
        (Scheme.Modules.pushforward g).map (pullbackDualMap g 𝒩.bundle ≫
          Scheme.Modules.vectorBundleClassifyingMap
            (dualSheaf (𝒩.baseChange i i' g f sq).bundle) k) := by
  have h : (Over.map g).map k ≫ 𝒩.baseChangeTotalSpaceOver i i' g f sq =
      (Over.map g).map (k ≫ Scheme.Modules.vectorBundleMap Z'
        (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
        (G := dualSheaf (𝒩.baseChange i i' g f sq).bundle) (pullbackDualMap g 𝒩.bundle)) ≫
        Scheme.Modules.vectorBundlePullbackProjection g (dualSheaf 𝒩.bundle) := by
    rw [VirtualNormalBundle.baseChangeTotalSpaceOver, Functor.map_comp, Category.assoc]
  rw [h, Scheme.Modules.vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection]
  exact congrArg (fun t => _ ≫ (Scheme.Modules.pushforward g).map t)
    (Scheme.Modules.vectorBundleClassifyingMap_comp_vectorBundleMap
      ((Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (G := dualSheaf (𝒩.baseChange i i' g f sq).bundle) (pullbackDualMap g 𝒩.bundle) k)

end Stacks.Chow

end
