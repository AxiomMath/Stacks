module

public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Finite presentation of a pullback restricted to an open

Two consequences of Stacks Tag 01BQ (finite presentation is stable under pullback, proved as
`Stacks.Modules.isFinitePresentation_pullback`) and Stacks Tag 0H96 (the cokernel of a map from
a finite type module to a finitely presented one is finitely presented, proved as
`Stacks.SheafOfModules.isFinitePresentation_cokernel`), in the shape a relative statement over
an open of the base needs them.

## Main results

* `Stacks.Modules.isFinitePresentation_pullback_on_preimage`: if `F` restricted to `U ⊆ X` is of
  finite presentation, then `g^* F` restricted to `g ⁻¹ᵁ U` is of finite presentation, for any
  `g : Y ⟶ X`. The two restrictions are compared through `g ∣_ U`.
* `Stacks.Modules.isFinitePresentation_pullback_cokernel`: the restriction to `f ⁻¹ᵁ U` of a
  cokernel `coker (α : G ⟶ F)` is of finite presentation as soon as the restriction of `F` is,
  with `G` of finite type.

## Implementation notes

Both statements take finite presentation of the restricted module as an explicit hypothesis
rather than an instance: the consumers obtain it as a `have`, over an open of the base that is
not fixed.

## References

* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Modules

/-- **Finite presentation over an open is inherited by a pullback over its preimage.** The
pullback of `F` along `g` restricted to `g ⁻¹ᵁ U` is the pullback along `g ∣_ U` of the
restriction of `F` to `U`, because `(g ⁻¹ᵁ U).ι ≫ g = (g ∣_ U) ≫ U.ι`, so Stacks Tag 01BQ
applies to `g ∣_ U`. -/
theorem isFinitePresentation_pullback_on_preimage
    {Y X : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) (U : X.Opens)
    (hfp : ((Scheme.Modules.pullback U.ι).obj F).IsFinitePresentation) :
    ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback g).obj F)).IsFinitePresentation := by
  let e := ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app F) ≪≫
    ((Scheme.Modules.pullbackCongr (morphismRestrict_ι g U).symm).app F) ≪≫
    ((Scheme.Modules.pullbackComp (g ∣_ U) U.ι).app F).symm
  exact (SheafOfModules.isFinitePresentation (g ⁻¹ᵁ U).toScheme.ringCatSheaf).prop_of_iso
    e.symm (isFinitePresentation_pullback (g ∣_ U) _ hfp)

/-- **A cokernel is of finite presentation over an open where its target is.** Restriction to an
open commutes with cokernels and preserves finite type, so this is Stacks Tag 0H96 on
`f ⁻¹ᵁ U`. -/
theorem isFinitePresentation_pullback_cokernel
    {X S : Scheme.{u}} (f : X ⟶ S) (F G : X.Modules)
    [G.IsFiniteType] (U : S.Opens)
    (hF : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (α : G ⟶ F) :
    ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (cokernel α)).IsFinitePresentation := by
  let T := Scheme.Modules.pullback (f ⁻¹ᵁ U).ι
  have : (T.obj F).IsFinitePresentation := hF
  have : (T.obj G).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType (f ⁻¹ᵁ U).ι.toLRSHom.toShHom G
  have hC : (cokernel (T.map α)).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel (T.map α)
  exact (SheafOfModules.isFinitePresentation (f ⁻¹ᵁ U).toScheme.ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso T α).symm hC

end Stacks.Modules

end
