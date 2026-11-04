module

public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit

/-!
# Ampleness at the limit presentation of a field extension

Let `K/k` be a field extension and `X` a quasi-compact quasi-separated scheme over `k`. Then `X_K`
is the limit of the base changes `X ×_k Spec Aᵢ` of `X` to the finitely generated `k`-subalgebras
`Aᵢ` of `K` (`AlgebraicGeometry.FieldExtensionDescent.baseChangeLimitCone`). This file applies
[Stacks Project, Tag 09MT] to that limit: an invertible module on some `X ×_k Spec Aⱼ` whose
pullback to `X_K` is ample is already ample on `X ×_k Spec Aⱼ'` for some larger `Aⱼ'`.

## Main results

* `AlgebraicGeometry.FieldExtensionDescent.exists_isAmple_pullback_baseChangeDiagram_map`:
  [Stacks Project, Tag 09MT] at the limit presentation of `X_K`.

## References

* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace AlgebraicGeometry.FieldExtensionDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (.of k))

/-- Let `M` be an invertible module on the base change `X ×_k Spec Aⱼ` of `X` to a finitely
generated `k`-subalgebra `Aⱼ` of `K`. If the pullback of `M` to `X_K` is ample, then the pullback
of `M` to `X ×_k Spec Aⱼ'` is ample for some larger finitely generated subalgebra `Aⱼ'`. -/
theorem exists_isAmple_pullback_baseChangeDiagram_map (j : (FGSubalgebra k K)ᵒᵖ)
    (M : ((baseChangeDiagram k K f).obj j).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((baseChangeDiagram k K f).obj j).toRingedSpace.presheaf
      (structureSheafRing ((baseChangeDiagram k K f).obj j).toRingedSpace).property M]
    (hample : Scheme.Modules.IsAmple (baseChangeLimitCone k K f).cone.pt
      ((Scheme.Modules.pullback ((baseChangeLimitCone k K f).cone.π.app j)).obj M)) :
    ∃ (j' : (FGSubalgebra k K)ᵒᵖ) (g : j' ⟶ j),
      Scheme.Modules.IsAmple ((baseChangeDiagram k K f).obj j')
        ((Scheme.Modules.pullback ((baseChangeDiagram k K f).map g)).obj M) :=
  Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs _ _
    (baseChangeLimitCone k K f).isLimit j M hample

end AlgebraicGeometry.FieldExtensionDescent

end
