module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Pasting

/-!
# The base-change assertion for direct images is local on the base

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
this file proves that invertibility of the canonical base-change morphism
`g^* f_* ⟶ f'_* (g')^*` at a module `F` may be checked after restricting to the members of an
open covering of `S'`, in the form: it is enough that the base-change morphism of the square
obtained by pasting `w` with the restriction square of `f'` over each member be invertible.
This is the step of Stacks Tag 02KG which says that the base-change assertion is local on the
base.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_pullback_map_baseChangeNatTrans`: for one
  open `V` of `S'`, invertibility of the base-change morphism of the pasted square gives
  invertibility of the inverse image to `V` of the base-change morphism of `w`.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_cover`: the
  resulting local criterion for an open covering of `S'`.

## Route

`Stacks.AlgebraicGeometry.AffineBaseChangeIso.baseChangeNatTrans_comp_square_app` writes the
base-change morphism of the pasted square as a composite of four factors, of which the first
and the last are components of the comparisons `Scheme.Modules.pullbackComp` and the third is
the base-change morphism of the restriction square, invertible by
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`.  The
remaining factor is the inverse image to `V` of the base-change morphism of `w`.  Locality is
then `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, whose
hypothesis is stated for `Scheme.Modules.restrictFunctor` rather than
`Scheme.Modules.pullback`; the two are compared by naturality of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

Several `IsIso` instances are supplied by explicit application of
`CategoryTheory.IsIso.comp_isIso` rather than by instance search: the category structure on
`AlgebraicGeometry.Scheme.Modules` is a different instance from the one on `SheafOfModules`,
equal to it only after unfolding a non-reducible definition.

## What is not done

**No assertion of [Stacks, Tag 02KG] is proved here, and no project tag attribute is
attached.**  Nothing here exhibits a single square whose base-change morphism is invertible
beyond those already covered by `isIso_baseChangeNatTrans_restrictSquare`; the hypothesis of
`isIso_baseChangeNatTrans_of_cover` has to be discharged elsewhere, and no affineness or
quasi-coherence hypothesis is used or available here.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.TwoSquare
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- If the base-change morphism of the square obtained from `w` by restricting over an open `V`
of `S'` is invertible at `F`, then so is the inverse image to `V` of the base-change morphism
of `w` itself. -/
theorem isIso_pullback_map_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    (V : S'.Opens)
    (H : IsIso ((AffinePushforward.baseChangeNatTrans
      (comp_square w (AffineBaseChange.restrictSquare f' V))).app F)) :
    IsIso ((Scheme.Modules.pullback V.ι).map
      ((AffinePushforward.baseChangeNatTrans w).app F)) := by
  rw [baseChangeNatTrans_comp_square_app w (AffineBaseChange.restrictSquare f' V)] at H
  have hC : IsIso ((AffinePushforward.baseChangeNatTrans
      (AffineBaseChange.restrictSquare f' V)).app ((Scheme.Modules.pullback g').obj F)) :=
    AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f' V _
  have hD : IsIso ((Scheme.Modules.pushforward (f' ∣_ V)).map
      ((Scheme.Modules.pullbackComp (f' ⁻¹ᵁ V).ι g').hom.app F)) :=
    Functor.map_isIso _ _
  have hA : IsIso ((Scheme.Modules.pullbackComp V.ι g).inv.app
      ((Scheme.Modules.pushforward f).obj F)) := inferInstance
  have hCD := @IsIso.comp_isIso _ _ _ _ _ _ _ hC hD
  have h₁ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hA H
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hCD h₁

/-- The base-change assertion is local on the base: if the base-change morphism of the square
obtained from `w` by restricting over each member of an open covering of `S'` is invertible at
`F`, then the base-change morphism of `w` is invertible at `F`. -/
theorem isIso_baseChangeNatTrans_of_cover (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    {I : Type*} (V : I → S'.Opens) (hV : IsOpenCover V)
    (H : ∀ i, IsIso ((AffinePushforward.baseChangeNatTrans
      (comp_square w (AffineBaseChange.restrictSquare f' (V i)))).app F)) :
    IsIso ((AffinePushforward.baseChangeNatTrans w).app F) := by
  refine AffineBaseChange.isIso_of_isIso_restrict _ V hV fun i ↦ ?_
  have hp := isIso_pullback_map_baseChangeNatTrans w F (V i) (H i)
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.naturality
    ((AffinePushforward.baseChangeNatTrans w).app F)
  have he : IsIso ((Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.app
      ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g).obj F)) := inferInstance
  have h₂ : IsIso ((Scheme.Modules.restrictFunctor (V i).ι).map
      ((AffinePushforward.baseChangeNatTrans w).app F) ≫
      (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.app _) := by
    rw [hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ he hp
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h₂

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
