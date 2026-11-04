module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExtExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage

/-!
# The top-degree trace of a family of curves commutes with classes in `Ext`

Let `f : U → S` be a separated morphism of finite type with a compactification whose fibres have
dimension at most one, `N` a positive integer and `Λ = ℤ/N`. Then `Rf_!(f⁻¹ X)` lives in degrees
`≤ 2` for every sheaf `X` of `Λ`-modules on `S`
(`Stacks.EtaleCohomology.isLE_derivedLowerShriek_inverseImage_single`). Given an identification
`ν : R²f_! f⁻¹ ≅ 𝟭` of functors on sheaves, the **top-degree trace** `t_X : Rf_!(f⁻¹ X) ⟶ X[-2]`
is the truncation map onto `R²f_!(f⁻¹ X)[-2]` followed by `ν`
(`Stacks.EtaleCohomology.lowerShriekTopTrace`). It commutes with every class `β ∈ Ext^m_S(X, Y)`:
`t_Y[m] ∘ Rf_!(f⁻¹ β) = β[-2] ∘ t_X` (`Stacks.EtaleCohomology.map_comp_lowerShriekTopTrace`). The
sheaf-level naturality of `ν` alone gives this in degree `0` only; positive degrees come from
`Stacks.TopTruncationExt.map_comp_topTrace`.

This is the compatibility used for the class of a point through an elementary fibration in the
proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); for an elementary fibration `ν`
is `Stacks.EtaleCohomology.RelativeTraceOfElementaryFibration` (it is carried here as the datum
`ν`).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.lowerShriekTopTrace`.

## Main results

* `Stacks.EtaleCohomology.isLE_derivedLowerShriek_inverseImage_single`.
* `Stacks.EtaleCohomology.map_comp_lowerShriekTopTrace`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {U S : Scheme.{u}} (f : U ⟶ S) (jf : CompactificationOf (Over.mk f)) (N : ℕ) [NeZero N]
  (hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ 1)

include hf in
/-- **`Rf_!(f⁻¹ X)` lives in degrees `≤ 2`** when the fibres of the compactification have
dimension at most one, `ℤ/N`-modules being torsion. -/
theorem isLE_derivedLowerShriek_inverseImage_single (X : EtaleModules.{u, 0} (ZMod N) S) :
    (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f jf (ZMod N)).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj X)))).IsLE 2 := by
  have hL : isTorsionPlus.{u, 0} (ZMod N) U ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj X)) :=
    fun _ => isTorsionEtaleModule_of_natCast_eq_zero (ZMod N) N (NeZero.pos N)
      (ZMod.natCast_self N) _
  simpa using isLE_derivedLowerShriek_of_isTorsionPlus (ZMod N) f jf 1 hf _ hL 0 inferInstance

variable (ν : etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙
      DerivedCategory.Plus.homologyFunctor _ 2 ≅ 𝟭 (EtaleModules.{u, 0} (ZMod N) S))

/-- **The top-degree trace** `t_X : Rf_!(f⁻¹ X) ⟶ X[-2]` of a family of curves: the truncation
onto `R²f_!(f⁻¹ X)[-2]` followed by `ν : R²f_! f⁻¹ ≅ 𝟭`. -/
def lowerShriekTopTrace (X : EtaleModules.{u, 0} (ZMod N) S) :
    ShiftedHom (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f jf (ZMod N)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj X))))
      ((DerivedCategory.singleFunctor _ 0).obj X) (-2) :=
  Stacks.TopTruncationExt.topTrace 2 (etaleModuleInverseImage.{u, 0} (ZMod N) f)
    (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι)
    (isLE_derivedLowerShriek_inverseImage_single f jf N hf) ν X

/-- **The top-degree trace of a family of curves commutes with classes in `Ext`**: for
`β ∈ Ext^m_S(X, Y)`, `t_Y[m] ∘ Rf_!(f⁻¹ β) = β[-2] ∘ t_X` as morphisms
`Rf_!(f⁻¹ X) ⟶ Y[m - 2]`. -/
theorem map_comp_lowerShriekTopTrace {X Y : EtaleModules.{u, 0} (ZMod N) S} {m : ℕ}
    (β : Ext X Y m) (c : ℤ) (h₁ : -2 + (m : ℤ) = c) (h₂ : (m : ℤ) + -2 = c) :
    ((Stacks.TopTruncationExt.extPlus
        (β.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod N) f))).map
          (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι)).comp
        (lowerShriekTopTrace f jf N hf ν Y) h₁ =
      (lowerShriekTopTrace f jf N hf ν X).comp β.hom h₂ := by
  rw [lowerShriekTopTrace, lowerShriekTopTrace,
    Stacks.TopTruncationExt.map_comp_topTrace 2 (etaleModuleInverseImage.{u, 0} (ZMod N) f)
      (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι)
      (isLE_derivedLowerShriek_inverseImage_single f jf N hf) ν β c h₁ h₂,
    Int.negOnePow_even _ ⟨m, by ring⟩, one_smul]

end Stacks.EtaleCohomology

end
