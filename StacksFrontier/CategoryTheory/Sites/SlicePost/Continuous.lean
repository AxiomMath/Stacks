module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-!
# Continuity of `Over.post` between slice sites

Let `u : C ⥤ D` be a functor between sites `(C, J)` and `(D, K)`, and let `V : C`. Then `u` induces
`Over.post u : Over V ⥤ Over (u.obj V)`, the functor `u'` of Stacks 03CF and 03EF (in the Stacks
Project's conventions `u` goes `D → C`, so `C` here is the Stacks Project's `D`). For a continuous
`u`, this file proves that `Over.post u` is continuous for the localized topologies `J.over V` and
`K.over (u.obj V)` under either of two further hypotheses:

* `C` has pullbacks and `u` preserves them; on sites with fibre products this is the Stacks
  Project's notion of a continuous functor;
* `Over.post u` is representably flat, which holds when `C` has finite limits and `u` is left
  exact, the hypotheses of Stacks 03EF.

## Main results

* `CategoryTheory.Limits.preservesLimitsOfShape_overPost_of_isConnected`: `Over.post F` preserves
  limits of any *connected* shape that `F` preserves and `C` has.
* `CategoryTheory.compatiblePreserving_overPost`: `Over.post u` is compatible-preserving when it is
  representably flat.
* `CategoryTheory.representablyFlat_overPost`: `Over.post u` is representably flat when `C` has
  finite limits and `u` is left exact.
* `CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks` and
  `CategoryTheory.Functor.isContinuous_overPost_of_flat`: `Over.post u` is continuous under each of
  the two hypotheses.
* `CategoryTheory.Functor.isContinuous_overPost_of_preservesFiniteLimits`: the instance stating
  that `Over.post u` is continuous when `C` has finite limits and `u` is left exact.
-/


@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Limits

/-- `Over.post F` preserves limits of a *connected* shape `J'` as soon as `F` does and `C` has
them. -/
instance preservesLimitsOfShape_overPost_of_isConnected {J' : Type w} [Category.{w'} J']
    [IsConnected J'] [HasLimitsOfShape J' C] {X : C} (F : C ⥤ D)
    [PreservesLimitsOfShape J' F] : PreservesLimitsOfShape J' (Over.post (X := X) F) := by
  constructor
  intro G
  have : PreservesLimit G (Over.post (X := X) F ⋙ Over.forget (F.obj X)) := by
    rw [Over.post_forget_eq_forget_comp]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (Over.forget (F.obj X))

end Limits

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- `Over.post u : Over V ⥤ Over (u.obj V)` is representably flat as soon as `C` has finite limits
and `u` is left exact. -/
instance representablyFlat_overPost [HasFiniteLimits C] (u : C ⥤ D) [PreservesFiniteLimits u]
    (V : C) : RepresentablyFlat (Over.post (X := V) u) :=
  haveI : HasFiniteLimits (Over V) := inferInstance
  flat_of_preservesFiniteLimits _

namespace Functor

/-- Let `u : C ⥤ D` be a continuous functor of sites, let `C` have pullbacks and let `u` preserve
them. Then `Over.post u : Over V ⥤ Over (u.obj V)` is continuous for the localized topologies
`J.over V` and `K.over (u.obj V)`. -/
@[stacks 03CF "Continuity of the functor `u' : D/V ⥤ C/U`, `V'/V ↦ u(V')/U`, which the proof of
  03CF asserts without argument and which is the input to every other clause. Proved here for `u`
  continuous with fibre products which `u` preserves, i.e. for Stacks' notion of continuity on
  sites with fibre products; see `Functor.isContinuous_overPost_of_flat` for the flat version and
  the module docstring for why bare `Functor.IsContinuous` is not known to suffice."]
theorem isContinuous_overPost_of_preservesPullbacks [HasPullbacks C] (u : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] (V : C) :
    (Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V)) :=
  have : PreservesOneHypercovers.{max u v} (Over.post (X := V) u) (J.over V)
      (K.over (u.obj V)) :=
    PreservesOneHypercovers.of_coverPreserving
      ((CoverPreserving.of_isContinuous u J K).overPost V)
  isContinuous_of_preservesOneHypercovers.{max u v} _ _ _

/-- Let `u : C ⥤ D` be a continuous functor of sites such that
`Over.post u : Over V ⥤ Over (u.obj V)` is representably flat. Then `Over.post u` is continuous for
the localized topologies `J.over V` and `K.over (u.obj V)`. -/
@[stacks 03EF "Continuity of `u' : D/V ⥤ C/U` under 03EF's hypotheses: 03EF assumes `u` left exact
  between sites with all finite limits, whence `Over.post u` is flat and this lemma applies. This
  is the continuity half of `Functor.isMorphismOfSites_overPost`."]
theorem isContinuous_overPost_of_flat (u : C ⥤ D) [u.IsContinuous J K] (V : C)
    [RepresentablyFlat (Over.post (X := V) u)] :
    (Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V)) :=
  isContinuous_iff_coverPreserving.2 ((CoverPreserving.of_isContinuous u J K).overPost V)

/-- If `C` has finite limits and the continuous functor `u : C ⥤ D` is left exact, then
`Over.post u : Over V ⥤ Over (u.obj V)` is continuous for the localized topologies `J.over V` and
`K.over (u.obj V)`. -/
instance isContinuous_overPost_of_preservesFiniteLimits [HasFiniteLimits C] (u : C ⥤ D)
    [PreservesFiniteLimits u]
    [u.IsContinuous J K] (V : C) :
    (Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V)) :=
  isContinuous_overPost_of_flat J K u V

end Functor

end CategoryTheory
