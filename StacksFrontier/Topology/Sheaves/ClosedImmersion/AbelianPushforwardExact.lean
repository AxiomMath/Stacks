module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Abelian
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianExact
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the stalk comparison for a pushforward of abelian sheaves

For a map `i : Z ⟶ X` of topological spaces and a presheaf `F` of abelian groups on `Z`, the
comparison maps `(i_* F)_{i z} ⟶ F_z` given by `TopCat.Presheaf.stalkPushforward` are natural in
`F`.

## Main results

* `TopCat.Presheaf.stalkPushforward_naturality`: naturality, in the presheaf, of the comparison map
  `(i_* F)_{i z} ⟶ F_z`.

## References

* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor

universe u

namespace TopCat.Presheaf

/-- The comparison maps `(i_* F)_{i z} ⟶ F_z` are natural in the presheaf `F`. -/
@[ega "0 3.4.4" "special case"]
lemma stalkPushforward_naturality
    {Z X : TopCat.{u}} (i : Z ⟶ X) {F G : Z.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G) (z : Z) :
    F.stalkPushforward AddCommGrpCat i z ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map φ =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat (i.hom z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat i).map φ) ≫
          G.stalkPushforward AddCommGrpCat i z := by
  let P := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z
  let Q := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i.hom z)
  dsimp [P, Q, TopCat.Presheaf.stalkFunctor]
  change F.stalkPushforward AddCommGrpCat i z ≫ P.map φ =
    Q.map ((TopCat.Presheaf.pushforward AddCommGrpCat i).map φ) ≫
      G.stalkPushforward AddCommGrpCat i z
  dsimp [P, Q]
  apply TopCat.Presheaf.stalk_hom_ext _; intro U hU
  rw [← Category.assoc, TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkFunctor_map_germ ((Opens.map i).obj U) z hU φ]
  simp

end TopCat.Presheaf

end
