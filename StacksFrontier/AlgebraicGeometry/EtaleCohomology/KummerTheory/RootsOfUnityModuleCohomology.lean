module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomology

/-!
# The cohomology of `ℤ/n` as a sheaf of `ℤ/n`-modules is the cohomology of `μ_n`

Let `X` be a scheme over a field `k` containing a primitive `n`-th root of unity `ζ`. The
cohomology `Hⁱ(X, ℤ/n)` of the constant sheaf of `ℤ/n`-modules, computed in sheaves of
`ℤ/n`-modules as `Ext` out of the constant sheaf (the cohomology of the trace formula,
[Stacks, Tag 03UG]), is the cohomology `Hⁱ(X, μ_n)` of the sheaf of `n`-th roots of unity of
the Kummer sequence, computed in abelian sheaves:

`Ext^i_{ℤ/n}(ℤ/n_X, ℤ/n_X) ≃+ Hⁱ(X, μ_n)`.

The comparison is `Stacks.EtaleCohomology.extConstantAddEquivSheafH` (independence of the
coefficient ring) followed by `μ_n ≅ ℤ/n`, `m ↦ ζ^m` (`Stacks.Kummer.rootsOfUnityConstantIso`).
It is how `H¹(X, ℤ/n) ≅ Pic(X)[n]` and `H²(X, ℤ/n) ≅ Pic(X)/n` (Tag 03RQ) reach the
cohomology of sheaves of `ℤ/n`-modules.

## Main definitions

* `Stacks.Kummer.etaleModuleConstantUnderlyingIso`: the abelian sheaf underlying the constant
  sheaf of `ℤ/n`-modules is `μ_n`.
* `Stacks.Kummer.extConstantAddEquivSheafHRootsOfUnity`:
  `Ext^i_{ℤ/n}(ℤ/n_X, ℤ/n_X) ≃+ Hⁱ(X, μ_n)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u

namespace Stacks.Kummer

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

/-- **The abelian sheaf underlying the constant sheaf of `ℤ/n`-modules is `μ_n`**, through
`m ↦ ζ^m`. -/
def etaleModuleConstantUnderlyingIso :
    (Stacks.EtaleCohomology.etaleModuleUnderlyingAbelian X (ZMod n)).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology) ≅
      rootsOfUnitySheaf.{u, 0} X n :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod n) X.smallEtaleTopology).app _ ≪≫
    rootsOfUnityConstantIso f hζ hn

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`Hⁱ(X, ℤ/n) ≃+ Hⁱ(X, μ_n)`** over a field with a primitive `n`-th root of unity: the
cohomology of the constant sheaf of `ℤ/n`-modules, as `Ext` out of itself in sheaves of
`ℤ/n`-modules, is the cohomology of the abelian sheaf `μ_n`. -/
def extConstantAddEquivSheafHRootsOfUnity (i : ℕ) :
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
        X.smallEtaleTopology) i).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology) ≃+
      Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} X n) i :=
  (Stacks.EtaleCohomology.extConstantAddEquivSheafH X _ i).trans
    (AlgebraicGeometry.SmallEtale.extPostcompIsoAddEquiv
      (etaleModuleConstantUnderlyingIso f hζ hn) i)

end Stacks.Kummer

end
