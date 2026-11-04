module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit

/-!
# Descending an invertible sheaf from `X_K` to a finite-type stage

Let `K/k` be a field extension, write `K` as the union of its finitely generated `k`-subalgebras
`Aᵢ`, and set `Xᵢ = X ×_{Spec k} Spec Aᵢ`. Then `X_K` is the limit of the `Xᵢ`
(`AlgebraicGeometry.FieldExtensionDescent.baseChangeLimitCone`), and by [Stacks Project, Tag 0B8W]
(2) (`Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit`) every
invertible sheaf on `X_K` is the pullback of an invertible sheaf on some `Xᵢ`.

## Main results

* `AlgebraicGeometry.FieldExtensionDescent.exists_isInvertible_baseChangeDiagram_pullback_iso`: an
  invertible sheaf on `X_K` is the pullback of an invertible sheaf on `Xᵢ` for some finitely
  generated `k`-subalgebra `Aᵢ ⊆ K`, as soon as `X` is quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace AlgebraicGeometry.FieldExtensionDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Let `X` be a quasi-compact quasi-separated scheme over a field `k` and let `K/k` be a field
extension. An invertible sheaf on `X_K` is the pullback of an invertible sheaf on
`Xᵢ = X ×_{Spec k} Spec Aᵢ` for some finitely generated `k`-subalgebra `Aᵢ ⊆ K`. -/
theorem exists_isInvertible_baseChangeDiagram_pullback_iso [CompactSpace X]
    [QuasiSeparatedSpace X]
    (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).Modules)
    (hL : SheafOfModules.IsInvertible
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).sheaf.obj
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).ringCatSheaf.property L) :
    ∃ (i : (FGSubalgebra k K)ᵒᵖ) (Lᵢ : ((baseChangeDiagram k K f).obj i).Modules),
      SheafOfModules.IsInvertible ((baseChangeDiagram k K f).obj i).sheaf.obj
          ((baseChangeDiagram k K f).obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback
          ((baseChangeLimitCone k K f).cone.π.app i)).obj Lᵢ) :=
  exists_isInvertible_pullback_iso_of_isLimit (baseChangeDiagram k K f)
    (baseChangeLimitCone k K f).cone (baseChangeLimitCone k K f).isLimit L hL

end AlgebraicGeometry.FieldExtensionDescent

end
