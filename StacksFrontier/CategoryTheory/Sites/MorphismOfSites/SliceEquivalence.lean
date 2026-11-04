module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over

/-!
# An equivalence of sites induces an equivalence of their localizations

Let `e : C ≌ D` be an equivalence of categories which is an equivalence of sites for topologies
`J` on `C` and `K` on `D`. Then for every object `W` of `C` the induced equivalence of slices
`C/W ≌ D/e(W)` of `CategoryTheory.Over.postEquiv` is again an equivalence of sites, for the
localized topologies `J.over W` and `K.over e(W)`, and therefore identifies the two localized
topoi.

This is the step from "the two sites have the same topos" to "their localizations have the same
topos", and it is not formal: the localized topology `GrothendieckTopology.over` is defined
through `Sieve.overEquiv`, so the comparison has to be made for sieves on slice objects.

Mathlib supplies the halves of this for `CategoryTheory.Over.post`: cocontinuity of
`Over.post F` for the localized topologies is an instance, and continuity is
`CategoryTheory.Functor.isContinuous_overPost`. What is missing is the assembly for an
*equivalence*, whose backward functor is not an `Over.post` but `Over.post e.inverse` followed
by `CategoryTheory.Over.map` of the unit. The continuous half of that assembly is already in
this tree, as `CategoryTheory.Over.postEquivFunctorIsContinuous` and
`.postEquivInverseIsContinuous` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InternalHomSiteEquivalence.lean`; this file adds
the cocontinuous half, which is what `CategoryTheory.Functor.IsDenseSubsite` — and hence
`CategoryTheory.Equivalence.sheafCongr` — requires.

## Main results

* `CategoryTheory.Over.postEquivFunctorIsCocontinuous` and
  `.postEquivInverseIsCocontinuous`: the two functors of the equivalence of slices are
  cocontinuous.
* `CategoryTheory.Over.postEquivSheafCongr`: sheaves on `C/W` and on `D/e(W)` agree, at any
  coefficients.

## Implementation notes

`postEquivInverseIsCocontinuous` names the middle topology of the composite twice, at two
different spellings of the same object: `Over.map` of the unit is cocontinuous for the
topologies over `(e.functor ⋙ e.inverse).obj W`, which is how the unit's own type spells its
domain, while Mathlib's instance for `Over.post e.inverse` concludes at the topology over
`e.inverse.obj (e.functor.obj W)`. The two are definitionally equal but *not* equal at
reducible transparency, because `CategoryTheory.Functor.comp` is not reducible, so instance
synthesis will not bridge them; the composite is therefore assembled with
`CategoryTheory.Functor.isCocontinuous_comp` applied to hypotheses stated at the two spellings,
where the elaborator's full defeq check does bridge them. This mirrors what
`postEquivInverseIsContinuous` does for the continuous half.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v v' u u' t₁ t₂

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (e : C ≌ D) [e.functor.IsCocontinuous J K] [e.inverse.IsCocontinuous K J]

/-- The forward functor of the equivalence of slices `C/W ≌ D/e(W)` is cocontinuous for the
localized topologies: it is `Over.post e.functor`, for which Mathlib has the instance. -/
instance postEquivFunctorIsCocontinuous (W : C) :
    (Over.postEquiv (X := W) e).functor.IsCocontinuous (J.over W) (K.over (e.functor.obj W)) :=
  inferInstanceAs ((Over.post (X := W) e.functor).IsCocontinuous _ _)

/-- The backward functor of the equivalence of slices `C/W ≌ D/e(W)` is cocontinuous for the
localized topologies: it is `Over.post e.inverse` followed by `Over.map` of the unit. -/
instance postEquivInverseIsCocontinuous (W : C) :
    (Over.postEquiv (X := W) e).inverse.IsCocontinuous (K.over (e.functor.obj W)) (J.over W) := by
  have h₁ : (Over.post (X := e.functor.obj W) e.inverse).IsCocontinuous
      (K.over (e.functor.obj W)) (J.over (e.inverse.obj (e.functor.obj W))) := inferInstance
  have h₂ : (Over.map (e.unitIso.inv.app W)).IsCocontinuous
      (J.over ((e.functor ⋙ e.inverse).obj W)) (J.over ((𝟭 C).obj W)) := inferInstance
  exact isCocontinuous_comp _ _ _ (J.over (e.inverse.obj (e.functor.obj W)))

/-- **An equivalence of sites induces an equivalence of their localizations.** Sheaves on the
slice `C/W` and on the slice `D/e(W)` agree, at any coefficients.

The equivalence of slices is `CategoryTheory.Over.postEquiv`; it is a dense subsite inclusion
for the localized topologies because both of its functors are cocontinuous, so
`CategoryTheory.Equivalence.sheafCongr` applies. -/
def postEquivSheafCongr (W : C) (A : Type t₁) [Category.{t₂} A] :
    Sheaf (J.over W) A ≌ Sheaf (K.over (e.functor.obj W)) A :=
  haveI : (Over.postEquiv (X := W) e).inverse.IsDenseSubsite
      (K.over (e.functor.obj W)) (J.over W) :=
    Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _
  (Over.postEquiv (X := W) e).sheafCongr _ _ A

end CategoryTheory.Over

end
