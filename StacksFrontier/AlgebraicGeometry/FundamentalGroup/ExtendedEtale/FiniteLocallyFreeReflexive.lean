module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree

/-!
# A finite locally free sheaf of modules is reflexive, on any scheme

A sheaf of modules on a scheme that is locally isomorphic to a finite free sheaf has free
stalks, so its stalks are reflexive modules over the local rings, and a module of finite
presentation whose dual is of finite presentation and whose stalks are reflexive is reflexive
([Stacks, Tag 0AY3]). Both finite-presentation facts follow from finite local freeness, so the
conclusion holds with no hypothesis on the scheme and no coherence.

## Main results

* `Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree'` — a finite locally
  free sheaf of modules on a scheme is reflexive. The coherent form on a locally Noetherian scheme
  is `Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree`.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.ReflexiveEquivalence

universe u

namespace Stacks.FundamentalGroup.ExtendedEtale

/-- **A finite locally free sheaf of modules on a scheme is reflexive**, with no hypothesis on
the scheme and no coherence. Each stalk is free of finite rank by
`isReflexive_stalk_of_iso_free`, transported from the trivialising open by
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_stalk_of_isReflexive_stalk_restrict`,
and [Stacks, Tag 0AY3] (2) ⇒ (1) concludes.

This is `isReflexive_of_isFiniteLocallyFree` with both of its extra hypotheses removed; that
statement is kept as it stands for its existing consumers. The stalkwise criterion asks for
finite presentation of `ℱ` and of `ℱ^∨`, and finite local freeness gives both: the dual of a
finite locally free module is again finite locally free, by
`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf`, and a finite locally
free module is of finite presentation. -/
public theorem isReflexive_of_isFiniteLocallyFree' {X : Scheme.{u}}
    (F : X.Modules) (hF : Scheme.Modules.IsFiniteLocallyFree F) : IsReflexive F := by
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) F := (Scheme.Modules.isFiniteLocallyFree_iff F).mp hF
  have hfp : F.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree F hflf
  have hdfp : (dualSheaf F).IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree _
      (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf F hflf)
  refine isReflexive_of_forall_isReflexive_stalk F fun x => ?_
  obtain ⟨U, hxU, I, hIfin, ⟨e⟩⟩ := hF x
  exact isReflexive_stalk_of_isReflexive_stalk_restrict U.ι F ⟨x, hxU⟩
    (isReflexive_stalk_of_iso_free (Y := U.toScheme) ⟨x, hxU⟩ (F.restrict U.ι) I e)

end Stacks.FundamentalGroup.ExtendedEtale

end
