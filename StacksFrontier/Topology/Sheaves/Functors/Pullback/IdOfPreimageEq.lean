module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PullbackIdentityOnCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tag 03SO — a self-map fixing every open induces the identity on cohomology

Let `X` be a topological space and `g : X ⟶ X` a continuous map such that `g ⁻¹' U = U` for
every open `U` of `X`. Then the preimage functor `Opens.map g` is isomorphic to the identity
functor of the site `Opens X`, so sheaf pushforward along `g` is isomorphic to the identity
functor on abelian sheaves. This is exactly the hypothesis of
`Stacks.Cohomology.cohomologyPullbackMap_comp_leftAdjointIdIso`, instantiated at the
pullback–pushforward adjunction along `g`: the map `g` induces on sheaf cohomology is the
identity, in every degree and for every abelian sheaf.

## Main definitions

* `opensMapIdOfPreimageEq` — the isomorphism `Opens.map g ≅ 𝟭 (Opens X)` coming from the
  pointwise equality of preimages with the opens themselves.
* `sheafPushforwardIdOfPreimageEq` — sheaf pushforward along `g` is isomorphic to the identity
  functor on abelian sheaves.
* `sheafAdjunctionOpensMap` — the pullback–pushforward adjunction along `g`, on the site
  `Opens X`.

## Main results

* `cohomologyPullbackMap_eq_id_of_preimageEq` — **Stacks tag 03SO.** The map `g` induces on
  sheaf cohomology is the identity, in every degree and for every abelian sheaf.

## Implementation notes

The identification of `g`'s pullback with the identity is obtained generically, from the
pushforward side, in `Stacks.Cohomology.cohomologyPullbackMap_comp_leftAdjointIdIso`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/PullbackIdentityOnCohomology.lean`), which is
also what `Stacks 03SP` instantiates for the small étale site of a scheme. Only the
isomorphism `sheafPushforwardIdOfPreimageEq` is specific to `X` and `g` here. The coefficient
category is kept at the same universe as `X`, which is what lets `HasSheafify` resolve
automatically; `HasExt` is never automatically derivable, so it is kept as an explicit
hypothesis, as elsewhere in this development.

Everything is stated for `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`, never for
`TopCat.Sheaf AddCommGrpCat X`, even though the two are definitionally the same category.
`TopCat.Sheaf` is a `def` with its own `deriving Category` instance and its own `Abelian`
instance (`Mathlib.Topology.Sheaves.Abelian`), so a statement phrased with it carries
category and abelian instances that are only defeq to — not syntactically the ones in — the
`HasExt` hypothesis, and `Sheaf.H` of such a sheaf has no synthesizable group structure. For
the same reason the adjunction is taken from `Functor.sheafAdjunctionContinuous`, which is
the definition `TopCat.Sheaf.pullbackPushforwardAdjunction` unfolds to.

## References

* [Stacks Project, Tag 03SO](https://stacks.math.columbia.edu/tag/03SO)
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat

universe u w

variable {X : TopCat.{u}} (g : X ⟶ X) (h : ∀ U : Opens X, ⇑g ⁻¹' (U : Set X) = (U : Set X))

/-- If `g ⁻¹' U = U` for every open `U` of `X`, the preimage functor `Opens.map g` is
isomorphic to the identity functor of the site `Opens X`. -/
noncomputable def opensMapIdOfPreimageEq : Opens.map g ≅ 𝟭 (Opens X) where
  hom := { app := fun U => eqToHom (Opens.ext ((Opens.map_coe g U).trans (h U))) }
  inv := { app := fun U => eqToHom (Opens.ext ((Opens.map_coe g U).trans (h U))).symm }

/-- If `g ⁻¹' U = U` for every open `U` of `X`, sheaf pushforward along `g` is isomorphic to
the identity functor on abelian sheaves. -/
noncomputable def sheafPushforwardIdOfPreimageEq :
    (Opens.map g).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) ≅
      𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Functor.sheafPushforwardContinuousIso (opensMapIdOfPreimageEq g h) _ _ _ ≪≫
    Functor.sheafPushforwardContinuousId _ _

/-- The adjunction between pullback and pushforward of abelian sheaves along `g`. This is
`TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat g` — the same definition — read on
the site `Opens X` rather than through `TopCat.Sheaf`, which is where sheaf cohomology lives. -/
noncomputable def sheafAdjunctionOpensMap :
    (Opens.map g).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) ⊣
      (Opens.map g).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) :=
  (Opens.map g).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _

/-- **Stacks tag 03SO.** Let `X` be a topological space and `g : X ⟶ X` a continuous map such
that `g ⁻¹' U = U` for every open `U` of `X`. Then the map `g` induces on sheaf cohomology,
followed by the canonical comparison of the pullback sheaf with the original one, is the
identity, in every degree `n` and for every abelian sheaf `F`: `g` induces the identity on
cohomology, for any coefficients.

See [Stacks Project, Tag 03SO](https://stacks.math.columbia.edu/tag/03SO). -/
@[stacks 03SO "g induces the identity on cohomology, for any coefficients"]
theorem cohomologyPullbackMap_eq_id_of_preimageEq
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    (Sheaf.H.map ((Adjunction.leftAdjointIdIso (sheafAdjunctionOpensMap g)
          (sheafPushforwardIdOfPreimageEq g h)).hom.app F) n).comp
        (Stacks.Cohomology.cohomologyPullbackMap.{w} (sheafAdjunctionOpensMap g)
          (sheafPushforwardIdOfPreimageEq g h) F n) =
      AddMonoidHom.id (Sheaf.H.{w} F n) :=
  Stacks.Cohomology.cohomologyPullbackMap_comp_leftAdjointIdIso.{w} (sheafAdjunctionOpensMap g)
    (sheafPushforwardIdOfPreimageEq g h) F n

end
