module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Vanishing of the cohomology of a sheaf restricted to a dense subsite

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)` and carry a terminal object of
`C` to a terminal object of `D`.  Restriction of abelian sheaves along `G` is then an equivalence
of sheaf categories carrying the constant sheaf on a group to the constant sheaf on that group,
so the global cohomology of an abelian sheaf on `(D, K)` and of its restriction to `(C, J)` are
the same group in every degree; in particular one of them vanishes exactly when the other does.

`Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_constantSheaf_of_isDenseSubsite` is this
statement for a constant sheaf.  The sheaf here is arbitrary, which is what a vanishing theorem
proved on the larger site needs in order to be read on the subsite.

## Main results

* `Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite`: **the
  vanishing of the cohomology of an abelian sheaf passes to its restriction to a dense
  subsite.**  The `Ext` universes on the two sides are unrelated.

## Implementation notes

The equivalence of sheaf categories is `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, whose
inverse is restriction along `G` on the nose, and the identification of the two constant sheaves
is Mathlib's `CategoryTheory.equivCommuteConstant'`.  Vanishing is transported by
`Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence`, which crosses the two `Ext`
universes, and the objects of the `Ext`-group are moved to their intended spellings by
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source` and
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target`.

## References

* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' v₁ u₁ v₂ u₂ a

namespace Stacks.Cohomology.DenseSubsiteVanishing

/-- **The vanishing of the cohomology of an abelian sheaf passes to its restriction to a dense
subsite.**  If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` and carries the
terminal object `TC` of `C` to a terminal object of `D`, then the vanishing of the degree-`q`
cohomology of an abelian sheaf `F` on `(D, K)` gives the vanishing of the degree-`q` cohomology
of its restriction along `G`.

The `Ext` universes on the two sides are unrelated. -/
public theorem subsingleton_H_restriction_of_isDenseSubsite
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsDenseSubsite J K]
    [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
    {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))
    (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w'} F q)) :
    Subsingleton (Sheaf.H.{w}
      ((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj F) q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : HasBinaryProducts (Sheaf K AddCommGrpCat.{a}) := inferInstance
  have : PreservesLimitsOfShape (Discrete WalkingPair) E.symm.functor :=
    E.symm.symm.toAdjunction.rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : E.symm.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : E.symm.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₀ : Subsingleton (Abelian.Ext.{w'}
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      (E.symm.inverse.obj (E.inverse.obj F)) q) :=
    Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target (E.counitIso.app F).symm q h
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant' J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))).symm q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E.symm
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      (E.inverse.obj F) q h₀)

end Stacks.Cohomology.DenseSubsiteVanishing

end
