module

public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullNaturality

/-!
# Restriction along the componentwise localization of a relocalized object

Let `(C, J)` be a small site and let `f : M ⟶ N` be a morphism of semi-representable objects of
`C`. The componentwise localization functors satisfy `j_M = r_f ⋙ j_N`, where
`r_f = componentOverMap f` is the componentwise relocalization functor
(`CategoryTheory.SemiRepresentable.componentOverMap_comp_componentOverForget`). This file records
the consequence on sheaves: restriction along `j_N` followed by restriction along `r_f` is
restriction along `j_M`.

This is the front face of the cube in the *source's* fork proof of the fullness clause of
Stacks 0D8E — not the route this repository takes, which proves that clause from local fullness
of `j_total` in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringUnit.lean`. Its back face is the
same square with the componentwise restrictions of
`CategoryTheory.SemiRepresentable.componentLocalizationAdjunction` in place of restriction along
`j_M` and `j_N`.

## Main definitions

* `CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso`: restriction along `j_N`
  then along `r_f` is restriction along `j_M`.

## Main results

* `CategoryTheory.SemiRepresentable.componentOverMap_isContinuous` and
  `.componentOverMap_isCocontinuous`: the componentwise relocalization functor `r_f` is
  continuous and cocontinuous for the two componentwise localized topologies, which is Stacks
  0D85 read through the localization datum `⟨M, N, f⟩`.

## Implementation notes

`relocalizationForgetPushforwardIso` takes the two topologies as parameters together with proofs
that they are the componentwise localized ones, exactly as
`CategoryTheory.SemiRepresentable.pushPullProductIso` does, and for the same reason: the intended
consumer is the component site of a simplicial semi-representable object, whose topology is only
propositionally the componentwise localized one.

The underlying equation of functors `r_f ⋙ j_N = j_M` is *not* definitional — it is proved by
`CategoryTheory.Functor.ext` — so the comparison is not `Iso.refl` and Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp`, which is, does not apply. What does
apply is `CategoryTheory.Functor.sheafPushforwardContinuousComp'`, which takes an isomorphism
`F ⋙ G ≅ FG` of the underlying functors; here that isomorphism is `eqToIso` of the proved
equation. Restriction along a continuous functor does compose definitionally, so nothing beyond
Mathlib is needed.

The continuity of `r_f` for the two componentwise localized topologies is Stacks 0D85, which the
library has as
`CategoryTheory.SemiRepresentable.LocalizationSites.relocalizationFunctor_isContinuous` for a
localization datum; the datum here is `⟨M, N, f⟩`, whose relocalization functor is `r_f` by
`CategoryTheory.SemiRepresentable.LocalizationSites.relocalizationFunctor_eq`. It is introduced by
`letI` rather than left to synthesis, which does not unfold the datum.

## References

* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The componentwise relocalization functor of `f : M ⟶ N` is continuous for the two
componentwise localized topologies, by Stacks 0D85 applied to the localization datum
`⟨M, N, f⟩`. -/
instance componentOverMap_isContinuous {M N : FormalCoproduct.{u} C} (f : M ⟶ N) :
    (componentOverMap f).IsContinuous (componentwiseTopology J M) (componentwiseTopology J N) :=
  LocalizationSites.relocalizationFunctor_isContinuous (⟨M, N, f⟩ : LocalizationSites.{u} C J)

/-- The componentwise relocalization functor of `f : M ⟶ N` is cocontinuous for the two
componentwise localized topologies, by Stacks 0D85 applied to the localization datum
`⟨M, N, f⟩`. -/
instance componentOverMap_isCocontinuous {M N : FormalCoproduct.{u} C} (f : M ⟶ N) :
    (componentOverMap f).IsCocontinuous (componentwiseTopology J M) (componentwiseTopology J N) :=
  LocalizationSites.relocalizationFunctor_isCocontinuous (⟨M, N, f⟩ : LocalizationSites.{u} C J)

/-- **Restriction along `j_N` then along `r_f` is restriction along `j_M`.** For a morphism
`f : M ⟶ N` of semi-representable objects the componentwise localization functor of `M` is the
componentwise relocalization functor of `f` followed by that of `N`, so the restriction functors
on sheaves compose accordingly.

The two topologies are parameters, each with a proof that it is the componentwise localized
topology, so that the statement applies verbatim to a site whose topology is only
propositionally that one; the transport is the pair of `subst`s at the head of the proof.

This is the front face of the cube in the source's fork proof of the fullness clause of
Stacks 0D8E. -/
def relocalizationForgetPushforwardIso {M N : FormalCoproduct.{u} C} (f : M ⟶ N)
    (Jm : GrothendieckTopology (ComponentOver M)) (hJm : Jm = componentwiseTopology J M)
    (Jn : GrothendieckTopology (ComponentOver N)) (hJn : Jn = componentwiseTopology J N)
    [(componentOverForget M).IsContinuous Jm J]
    [(componentOverForget N).IsContinuous Jn J]
    [(componentOverMap f).IsContinuous Jm Jn] :
    (componentOverForget N).sheafPushforwardContinuous (Type u) Jn J ⋙
        (componentOverMap f).sheafPushforwardContinuous (Type u) Jm Jn ≅
      (componentOverForget M).sheafPushforwardContinuous (Type u) Jm J := by
  subst hJm
  subst hJn
  exact Functor.sheafPushforwardContinuousComp'
    (F := componentOverMap f) (G := componentOverForget N) (FG := componentOverForget M)
    (eqToIso (componentOverMap_comp_componentOverForget f)) (Type u)
    (componentwiseTopology J M) (componentwiseTopology J N) J

/-- `relocalizationForgetPushforwardIso` is the comparison of Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` that its proof produces: the two
`subst`s are at identity equations and reduce away. This is what makes the isomorphism computable
at a point of use, and it holds at the parameter topologies, not only at the componentwise
localized ones. -/
theorem relocalizationForgetPushforwardIso_eq {M N : FormalCoproduct.{u} C} (f : M ⟶ N)
    (Jm : GrothendieckTopology (ComponentOver M)) (hJm : Jm = componentwiseTopology J M)
    (Jn : GrothendieckTopology (ComponentOver N)) (hJn : Jn = componentwiseTopology J N)
    [(componentOverForget M).IsContinuous Jm J]
    [(componentOverForget N).IsContinuous Jn J]
    [(componentOverMap f).IsContinuous Jm Jn] :
    relocalizationForgetPushforwardIso J f Jm hJm Jn hJn =
      Functor.sheafPushforwardContinuousComp'
        (F := componentOverMap f) (G := componentOverForget N) (FG := componentOverForget M)
        (eqToIso (componentOverMap_comp_componentOverForget f)) (Type u) Jm Jn J := by
  subst hJm
  subst hJn
  rfl

/-- **The one-object case: restriction to `C/V` then along `g : U ⟶ V` is restriction to
`C/U`.** This is the componentwise content of the back face of the same cube: a component of the
componentwise restriction of `componentLocalizationAdjunction` at `M` is the restriction to
`C/M_i`, and the transition of `f` restricts it from the component `N_{f(i)}`. -/
def overMapPullbackIso {U V : C} (g : U ⟶ V) :
    J.overPullback (Type u) V ⋙
        (Over.map g).sheafPushforwardContinuous (Type u) (J.over U) (J.over V) ≅
      J.overPullback (Type u) U :=
  Functor.sheafPushforwardContinuousComp'
    (F := Over.map g) (G := Over.forget V) (FG := Over.forget U)
    (Iso.refl _) (Type u) (J.over U) (J.over V) J

end CategoryTheory.SemiRepresentable

end
