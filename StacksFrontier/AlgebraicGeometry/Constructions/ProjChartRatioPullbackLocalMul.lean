module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.LocalPowerProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullbackMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict

/-!
# Pulling back a product of two local sections of tensor powers

Let `k : Y' ⟶ Y` be a morphism of schemes and `L` an invertible `𝒪_Y`-module. The inverse image of
a product of two sections of the iterated tensor powers of `L` over one arbitrary open is the
product of their inverse images. Along the inclusion of an open subscheme `U`, the product of two
sections over `U` becomes the product of global sections on `U`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.pullPowSection`: the pullback of a
  section of `L ^⊗ n` over `W`, as a section of `(k^*L) ^⊗ n` over `k^{-1}(W)`.
* `…ProjChartRatioPullbackLocalMul.restrictPowSection`: a section of `L ^⊗ n` over an open `U`,
  read as a global section of `(L|_U) ^⊗ n` on the open subscheme `U`.

## Main results

* `…ProjChartRatioPullbackLocalMul.pullbackIntPowIso_pullbackUnit_mulBilinear`, and its scheme
  spelling `…pullbackIntPowIso_pullbackUnit_localMul`: the comparison of the integral tensor
  powers carries the pullback-unit image of a local product to the product of the pullback-unit
  images, over an arbitrary open and in every pair of integer degrees.
* `…ProjChartRatioPullbackLocalMul.pullPowSection_localMulSections`: the pullback of a local
  product is the product of the pullbacks, in every pair of nonnegative degrees.
* `…ProjChartRatioPullbackLocalMul.restrictPowSection_localMulSections`: over the open subscheme
  `U` the product becomes `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules.TensorPower (tensorPower coherentMulIso mulBilinear mulBilinear_app
  tensorSheafMapIso)
open Stacks.RingedSpace (pullbackFunctor pullbackUnit pullbackUnit_naturality structureRingSheaf)
open Stacks.PullbackTensorCoherence (pullbackTensorComparison pullbackTensorComparison_pullbackUnit)
open Stacks.TensorPowerPullback (isSheafStructure pullbackIntPowIso pullbackTensorator
  pullbackIntPowIso_coherentMulIso)
open Stacks.SheafOfModules (tensorSectionsAt)
open PresheafOfModules (Hom)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.NatTensorPowLocalMul (localMulSections)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (L : SheafOfModules.{u} (structureRingSheaf Y))
  [Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheafStructure Y) L]

/-- The tensor product sheaf of two isomorphisms acts factorwise on the section of a pure tensor:
`i ⊗ j` sends the section of `M ⊗ N` over `U` determined by `s` and `t` to the section of
`M' ⊗ N'` determined by `i s` and `j t`. -/
private theorem tensorSheafMapIso_tensorSectionsAt (Z : RingedSpace.{u, u})
    {M M' N N' : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf Z.presheaf (isSheafStructure Z))}
    (i : M ≅ M') (j : N ≅ N') (U : (Opens Z.carrier)ᵒᵖ) (s : M.val.obj U) (t : N.val.obj U) :
    Hom.app (tensorSheafMapIso Z.presheaf (isSheafStructure Z) i j).hom.val U
        (tensorSectionsAt Z.presheaf (isSheafStructure Z) U M N s t) =
      tensorSectionsAt Z.presheaf (isSheafStructure Z) U M' N' (Hom.app i.hom.val U s)
        (Hom.app j.hom.val U t) := by
  refine (Stacks.SheafOfModules.toSheafify_app_map_obj (O := Z.presheaf) (hO := isSheafStructure Z)
    (f := PresheafOfModules.tensorHom (O := Z.presheaf) i.hom.val j.hom.val) _ _).trans ?_
  exact congrArg (ConcreteCategory.hom ((Stacks.SheafOfModules.TensorSheafification.toSheafify
    Z.presheaf (isSheafStructure Z) _).app _)) (PresheafOfModules.tensorHom_tmul _ _ _ _ _)

/-- The comparison of the integral tensor powers carries the pullback-unit image of a local
product to the product of the pullback-unit images, over one arbitrary open and in every pair of
integer degrees. -/
public theorem pullbackIntPowIso_pullbackUnit_mulBilinear (n m : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (y : (tensorPower Y.presheaf (isSheafStructure Y) L n).val.obj U)
    (z : (tensorPower Y.presheaf (isSheafStructure Y) L m).val.obj U) :
    Hom.app (pullbackIntPowIso f L (n + m)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
        (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L (n + m)) U
          ((mulBilinear Y.presheaf (isSheafStructure Y) L n m).app U y z))
      = (mulBilinear X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n m).app
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
          (Hom.app (pullbackIntPowIso f L n).hom.val _ (pullbackUnit f _ U y))
          (Hom.app (pullbackIntPowIso f L m).hom.val _ (pullbackUnit f _ U z)) := by
  have hA := mulBilinear_app Y.presheaf (isSheafStructure Y) L n m U y z
  have hB := pullbackUnit_naturality f (coherentMulIso Y.presheaf (isSheafStructure Y) L n m).hom U
    (tensorSectionsAt Y.presheaf (isSheafStructure Y) U
      (tensorPower Y.presheaf (isSheafStructure Y) L n)
      (tensorPower Y.presheaf (isSheafStructure Y) L m) y z)
  have hC : Hom.app (pullbackIntPowIso f L (n + m)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
        (Hom.app ((pullbackFunctor f).map
            (coherentMulIso Y.presheaf (isSheafStructure Y) L n m).hom).val
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
          (pullbackUnit f ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf)
                (forget₂ CommRingCat RingCat) ((isSheafStructure Y))⟩).obj
              ((tensorPower Y.presheaf (isSheafStructure Y) L n))).obj
              ((tensorPower Y.presheaf (isSheafStructure Y) L m)))) U
            (tensorSectionsAt Y.presheaf (isSheafStructure Y) U
              (tensorPower Y.presheaf (isSheafStructure Y) L n)
              (tensorPower Y.presheaf (isSheafStructure Y) L m) y z)))
      = Hom.app
          (coherentMulIso X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n m).hom.val
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
          (Hom.app (tensorSheafMapIso X.presheaf (isSheafStructure X) (pullbackIntPowIso f L n)
              (pullbackIntPowIso f L m)).hom.val
            ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
            (Hom.app (pullbackTensorator f (tensorPower Y.presheaf (isSheafStructure Y) L n)
                (tensorPower Y.presheaf (isSheafStructure Y) L m)).hom.val
              ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
              (pullbackUnit f ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf)
                    (forget₂ CommRingCat RingCat) ((isSheafStructure Y))⟩).obj
                  ((tensorPower Y.presheaf (isSheafStructure Y) L n))).obj
                  ((tensorPower Y.presheaf (isSheafStructure Y) L m)))) U
            (tensorSectionsAt Y.presheaf (isSheafStructure Y) U
              (tensorPower Y.presheaf (isSheafStructure Y) L n)
              (tensorPower Y.presheaf (isSheafStructure Y) L m) y z)))) :=
    congrArg (fun g : (pullbackFunctor f).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf)
            (forget₂ CommRingCat RingCat) ((isSheafStructure Y))⟩).obj
          ((tensorPower Y.presheaf (isSheafStructure Y) L n))).obj
          ((tensorPower Y.presheaf (isSheafStructure Y) L m)))) ⟶
          (tensorPower X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) (n + m)) =>
      Hom.app (SheafOfModules.Hom.val g) ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
        (pullbackUnit f ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf)
              (forget₂ CommRingCat RingCat) ((isSheafStructure Y))⟩).obj
            ((tensorPower Y.presheaf (isSheafStructure Y) L n))).obj
            ((tensorPower Y.presheaf (isSheafStructure Y) L m)))) U
          (tensorSectionsAt Y.presheaf (isSheafStructure Y) U
            (tensorPower Y.presheaf (isSheafStructure Y) L n)
            (tensorPower Y.presheaf (isSheafStructure Y) L m) y z)))
      (pullbackIntPowIso_coherentMulIso f L n m)
  have hD : Hom.app (pullbackTensorator f (tensorPower Y.presheaf (isSheafStructure Y) L n)
          (tensorPower Y.presheaf (isSheafStructure Y) L m)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
        (pullbackUnit f ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf)
              (forget₂ CommRingCat RingCat) ((isSheafStructure Y))⟩).obj
            ((tensorPower Y.presheaf (isSheafStructure Y) L n))).obj
            ((tensorPower Y.presheaf (isSheafStructure Y) L m)))) U
          (tensorSectionsAt Y.presheaf (isSheafStructure Y) U
            (tensorPower Y.presheaf (isSheafStructure Y) L n)
            (tensorPower Y.presheaf (isSheafStructure Y) L m) y z))
      = (tensorSectionsAt X.presheaf (isSheafStructure X)
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
          ((pullbackFunctor f).obj (tensorPower Y.presheaf (isSheafStructure Y) L n))
          ((pullbackFunctor f).obj (tensorPower Y.presheaf (isSheafStructure Y) L m))
          (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L n) U y)
          (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L m) U z)) :=
    pullbackTensorComparison_pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L n)
      (tensorPower Y.presheaf (isSheafStructure Y) L m) U y z
  have hE : Hom.app (tensorSheafMapIso X.presheaf (isSheafStructure X) (pullbackIntPowIso f L n)
          (pullbackIntPowIso f L m)).hom.val ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
        (tensorSectionsAt X.presheaf (isSheafStructure X)
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
          ((pullbackFunctor f).obj (tensorPower Y.presheaf (isSheafStructure Y) L n))
          ((pullbackFunctor f).obj (tensorPower Y.presheaf (isSheafStructure Y) L m))
          (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L n) U y)
          (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L m) U z))
      = (tensorSectionsAt X.presheaf (isSheafStructure X)
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
          (tensorPower X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n)
          (tensorPower X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) m)
          (Hom.app (pullbackIntPowIso f L n).hom.val
            ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
            (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L n) U y))
          (Hom.app (pullbackIntPowIso f L m).hom.val
            ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
            (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L m) U z))) :=
    tensorSheafMapIso_tensorSectionsAt X (pullbackIntPowIso f L n) (pullbackIntPowIso f L m)
      ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
      (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L n) U y)
      (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L m) U z)
  have hF := mulBilinear_app X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n m
    ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
    (Hom.app (pullbackIntPowIso f L n).hom.val ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
      (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L n) U y))
    (Hom.app (pullbackIntPowIso f L m).hom.val ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
      (pullbackUnit f (tensorPower Y.presheaf (isSheafStructure Y) L m) U z))
  rw [hA]
  exact Eq.trans
    (congrArg (fun t => Hom.app (pullbackIntPowIso f L (n + m)).hom.val
      ((RingedSpaceModuleAdjunction.opensMap f).op.obj U) t) hB.symm)
    (hC.trans ((congrArg (fun w => Hom.app
          (coherentMulIso X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n m).hom.val
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U)
          (Hom.app (tensorSheafMapIso X.presheaf (isSheafStructure X) (pullbackIntPowIso f L n)
              (pullbackIntPowIso f L m)).hom.val
            ((RingedSpaceModuleAdjunction.opensMap f).op.obj U) w)) hD).trans
      ((congrArg (fun v => Hom.app
          (coherentMulIso X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n m).hom.val
          ((RingedSpaceModuleAdjunction.opensMap f).op.obj U) v) hE).trans hF.symm)))

/-- For an isomorphism `e : A ≅ B` of modules, `e.hom` undoes `e.inv` on a section over an
arbitrary open `W`. -/
public theorem hom_app_inv_app {Z : Scheme.{u}} {A B : Z.Modules} (e : A ≅ B) (W : Z.Opens)
    (u : Γ(B, W)) : e.hom.app W (e.inv.app W u) = u :=
  (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t W) e.inv_hom_id) u).trans rfl


section Scheme

variable {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (M : Z.Modules)
  [Stacks.Ample.IsInvertibleModule Z M]

/-- An invertible module on a scheme is invertible as a sheaf of modules over `Z.presheaf`. -/
local instance invZ : Stacks.SheafOfModules.IsInvertible Z.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) M :=
  Stacks.PowerFamilyBridge.instIsInvertible Z.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) M

/-- The comparison of the integral tensor powers carries the pullback-unit image of a local
product `Stacks.TensorPowerDivision.localMul` to the product of the pullback-unit images, at the
scheme spelling of the powers and of the product. -/
public theorem pullbackIntPowIso_pullbackUnit_localMul (n m : ℤ) (W : Z.Opens)
    (y : Γ(Stacks.AmpleProjectiveImmersion.tensorPowerModule Z M n, W))
    (z : Γ(Stacks.AmpleProjectiveImmersion.tensorPowerModule Z M m, W)) :
    Hom.app (pullbackIntPowIso k.toLRSHom.toShHom M (n + m)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap k.toLRSHom.toShHom).op.obj (op W))
        (pullbackUnit k.toLRSHom.toShHom
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule Z M (n + m)) (op W)
          (Stacks.TensorPowerDivision.localMul M y z))
      = Stacks.TensorPowerDivision.localMul ((Scheme.Modules.pullback k).obj M)
          (Hom.app (pullbackIntPowIso k.toLRSHom.toShHom M n).hom.val
            ((RingedSpaceModuleAdjunction.opensMap k.toLRSHom.toShHom).op.obj (op W))
            (pullbackUnit k.toLRSHom.toShHom
              (Stacks.AmpleProjectiveImmersion.tensorPowerModule Z M n) (op W) y))
          (Hom.app (pullbackIntPowIso k.toLRSHom.toShHom M m).hom.val
            ((RingedSpaceModuleAdjunction.opensMap k.toLRSHom.toShHom).op.obj (op W))
            (pullbackUnit k.toLRSHom.toShHom
              (Stacks.AmpleProjectiveImmersion.tensorPowerModule Z M m) (op W) z)) :=
  pullbackIntPowIso_pullbackUnit_mulBilinear k.toLRSHom.toShHom M n m (op W) y z

/-- The pullback of a section of `L ^⊗ n` over an open `W`, as a section of `(k^*L) ^⊗ n` over
`k^{-1}(W)`: the unit of the module-pullback adjunction at `W`, read in the iterated tensor
powers through `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` on each side and the
comparison `Stacks.TensorPowerPullback.pullbackIntPowIso` between them. -/
public def pullPowSection (n : ℕ) (W : Z.Opens) (x : Γ(natTensorPow M n, W)) :
    Γ(natTensorPow ((Scheme.Modules.pullback k).obj M) n, k ⁻¹ᵁ W) :=
  (powCompare
      ((Scheme.Modules.pullback k).obj M) n).inv.app (k ⁻¹ᵁ W)
    (Hom.app (pullbackIntPowIso k.toLRSHom.toShHom M (n : ℤ)).hom.val
      ((RingedSpaceModuleAdjunction.opensMap k.toLRSHom.toShHom).op.obj (op W))
      (pullbackUnit k.toLRSHom.toShHom
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule Z M (n : ℤ)) (op W)
        ((powCompare M n).hom.app W x)))

/-- The pullback of a local product is the product of the pullbacks, over one arbitrary open and
in every pair of nonnegative degrees:

`k^*(y · z) = k^*y · k^*z`  in  `Γ((k^*L) ^⊗ (n + m), k^{-1}(W))`,

the product being `Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections` on both
sides. -/
public theorem pullPowSection_localMulSections (n m : ℕ) (W : Z.Opens)
    (y : Γ(natTensorPow M n, W))
    (z : Γ(natTensorPow M m, W)) :
    pullPowSection k M (n + m) W
        (localMulSections M y z)
      = localMulSections
          ((Scheme.Modules.pullback k).obj M)
          (pullPowSection k M n W y) (pullPowSection k M m W z) := by
  have h1 : (powCompare M (n + m)).hom.app W
        (localMulSections M y z)
      = Stacks.TensorPowerDivision.localMul M
          ((powCompare M n).hom.app W y)
          ((powCompare M m).hom.app W z) :=
    hom_app_inv_app (powCompare M (n + m)) W _
  have h2 := pullbackIntPowIso_pullbackUnit_localMul k M (n : ℤ) (m : ℤ) W
    ((powCompare M n).hom.app W y)
    ((powCompare M m).hom.app W z)
  have hpow : ∀ (a : ℕ) (x : Γ(natTensorPow M a, W)),
      (powCompare ((Scheme.Modules.pullback k).obj M) a).hom.app (k ⁻¹ᵁ W)
        (pullPowSection k M a W x)
      = Hom.app (pullbackIntPowIso k.toLRSHom.toShHom M (a : ℤ)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap k.toLRSHom.toShHom).op.obj (op W))
        (pullbackUnit k.toLRSHom.toShHom
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule Z M (a : ℤ)) (op W)
          ((powCompare M a).hom.app W x)) :=
    fun a x => hom_app_inv_app (powCompare ((Scheme.Modules.pullback k).obj M) a) (k ⁻¹ᵁ W) _
  show (powCompare
      ((Scheme.Modules.pullback k).obj M) (n + m)).inv.app (k ⁻¹ᵁ W)
      (Hom.app (pullbackIntPowIso k.toLRSHom.toShHom M ((n + m : ℕ) : ℤ)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap k.toLRSHom.toShHom).op.obj (op W))
        (pullbackUnit k.toLRSHom.toShHom _ (op W)
          ((powCompare M (n + m)).hom.app W
            (localMulSections M y z)))) = _
  rw [h1]
  refine Eq.trans (congrArg (fun t => (powCompare ((Scheme.Modules.pullback k).obj M)
      (n + m)).inv.app (k ⁻¹ᵁ W) t) h2) ?_
  show _ = (powCompare ((Scheme.Modules.pullback k).obj M) (n + m)).inv.app (k ⁻¹ᵁ W)
      (Stacks.TensorPowerDivision.localMul ((Scheme.Modules.pullback k).obj M)
        ((powCompare ((Scheme.Modules.pullback k).obj M) n).hom.app (k ⁻¹ᵁ W)
          (pullPowSection k M n W y))
        ((powCompare ((Scheme.Modules.pullback k).obj M) m).hom.app (k ⁻¹ᵁ W)
          (pullPowSection k M m W z)))
  rw [hpow n y, hpow m z]
  rfl


end Scheme

section Restrict

variable {Z : Scheme.{u}} (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M] (U : Z.Opens)

/-- A section of `L ^⊗ n` over an open `U`, read as a global section of `(L|_U) ^⊗ n` on the open
subscheme `U`: `pullPowSection` along the inclusion `U.ι`, followed by the restriction from
`U.ι^{-1}(U)` to `⊤`. -/
public def restrictPowSection (n : ℕ) (x : Γ(natTensorPow M n, U)) :
    Γ(natTensorPow ((Scheme.Modules.pullback U.ι).obj M) n, (⊤ : U.toScheme.Opens)) :=
  (natTensorPow ((Scheme.Modules.pullback U.ι).obj M) n).presheaf.map
      (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op
    (pullPowSection U.ι M n U x)

/-- The restriction of a product of two sections over `U` is the product of their restrictions,
the product of global sections on the open subscheme `U` being
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`. -/
public theorem restrictPowSection_localMulSections (n m : ℕ)
    (y : Γ(natTensorPow M n, U)) (z : Γ(natTensorPow M m, U)) :
    restrictPowSection M U (n + m) (localMulSections M y z)
      = Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections
          ((Scheme.Modules.pullback U.ι).obj M)
          (restrictPowSection M U n y) (restrictPowSection M U m z) := by
  refine Eq.trans (congrArg (fun t => (natTensorPow ((Scheme.Modules.pullback U.ι).obj M)
      (n + m)).presheaf.map
      (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op t)
    (pullPowSection_localMulSections U.ι M n m U y z)) ?_
  rw [Stacks.AlgebraicGeometry.NatTensorPowLocalMul.map_localMulSections]
  exact Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections_top _ _ _

end Restrict

end Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

end
