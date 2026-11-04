module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackNaturalityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedGroup
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.PreconnectedRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The flat-pullback class of a smooth morphism in the completed bivariant group

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `g : P ⟶ Y` be a
smooth morphism of schemes locally of finite type over `S`. The flat-pullback class of
Stacks 0B78 is attached to a flat morphism of a *fixed* relative dimension `r`, and lies in
`A^{-r}(P ⟶ Y)`. A smooth morphism has a relative dimension that is only locally constant on `P`,
so its flat pullback `g^*` is an element of the completed bivariant group
`A^*(P ⟶ Y)^∧ = ∏_i A^*(P_i ⟶ Y_{a(i)})` of Stacks 0FE0: on each connected component `P_i` of `P`
the restriction `P_i ⟶ Y_{a(i)}` of `g` is smooth of pure relative dimension `r_i`, and the
component of `g^*` there is the class of Stacks 0B78 of that restriction, in degree `-r_i`.

## Main definitions

* `Stacks.Chow.smoothComponentRelativeDimension` — the relative dimension `r_i` of a smooth
  morphism on a connected component `P_i` of its source.
* `Stacks.Chow.completedFlatPullbackOfSmooth` — `g^* ∈ A^*(P ⟶ Y)^∧`.

## Main results

* `Stacks.Chow.relativeDimension_smoothComponentRelativeDimension` — the restriction of `g` to
  `P_i` has pure relative dimension `r_i`.
* `Stacks.Chow.completedFlatPullbackOfSmooth_apply` — on `P_i` the class `g^*` is the class of
  Stacks 0B78 of the restriction, placed in degree `-r_i`.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Smooth

variable {P Y : Scheme.{u}} [IsLocallyNoetherian P] [IsLocallyNoetherian Y] (g : P ⟶ Y)

/-- A connected component of a locally Noetherian scheme is a preconnected space. -/
instance preconnectedSpace_connectedComponentOpens (a : _root_.ConnectedComponents P) :
    PreconnectedSpace (P.connectedComponentOpens a) := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe a
  have hcc : (P.connectedComponentOpens (_root_.ConnectedComponents.mk x) : Set P) =
      connectedComponent x := by
    rw [Scheme.coe_connectedComponentOpens, connectedComponents_preimage_singleton]
  exact Subtype.preconnectedSpace (hcc ▸ isPreconnected_connectedComponent)

/-- The restriction of a smooth morphism to a connected component of its source is smooth. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.smooth_resConnectedComponent [Smooth g]
    (a : _root_.ConnectedComponents P) :
    Smooth (g.resConnectedComponent a) :=
  inferInstanceAs (Smooth (g.resLE _ _ _))

/-- The relative dimension of a smooth morphism `g : P ⟶ Y` on a connected component `P_a` of its
source: the pure relative dimension of the restriction `P_a ⟶ Y_{g(a)}`. -/
def smoothComponentRelativeDimension [Smooth g] (a : _root_.ConnectedComponents P) : ℕ :=
  (exists_relativeDimension_of_smooth_of_preconnectedSpace (g.resConnectedComponent a)).choose

/-- The restriction of a smooth morphism to a connected component of its source has pure
relative dimension `Stacks.Chow.smoothComponentRelativeDimension`. -/
@[sga "4½ Th_finitude 2.2" "Clause a)"]
theorem relativeDimension_smoothComponentRelativeDimension [Smooth g]
    (a : _root_.ConnectedComponents P) :
    AlgebraicGeometry.RelativeDimension (g.resConnectedComponent a)
      (smoothComponentRelativeDimension g a) :=
  (exists_relativeDimension_of_smooth_of_preconnectedSpace (g.resConnectedComponent a)).choose_spec

end Smooth

section Class

variable (C : ChowSituation.{u}) {P Y : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g]
  (hg : g ≫ sY = sP)

/-- **`g^* ∈ A^*(P ⟶ Y)^∧` for a smooth morphism `g`.** The flat-pullback class of Stacks 0B78 of
a smooth morphism, viewed in the completed bivariant group of Stacks 0FE0: on each connected
component `P_a` of `P` it is the class of Stacks 0B78 of the restriction `P_a ⟶ Y_{g(a)}`, which is
smooth of pure relative dimension `r_a`, placed in degree `-r_a`. -/
def completedFlatPullbackOfSmooth :
    completedBivariantGroup C (gysinSystemOfInvertible C) sP sY g hg :=
  letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  fun a ↦ DirectSum.of _ (-(smoothComponentRelativeDimension g a : ℤ))
    (flatPullbackBivariantClassOfInvertible C ((P.connectedComponentOpens a).ι ≫ sP)
        ((Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)).ι ≫ sY)
        (g.resConnectedComponent a) (g.resConnectedComponent_comp_ι_comp hg a)
        (smoothComponentRelativeDimension g a)
        (relativeDimension_smoothComponentRelativeDimension g a))

/-- On a connected component `P_a` of `P`, the completed class `g^*` is the class of Stacks 0B78
of the restriction of `g`, placed in degree `-r_a`. -/
theorem completedFlatPullbackOfSmooth_apply [IsLocallyNoetherian P] [IsLocallyNoetherian Y]
    (a : _root_.ConnectedComponents P) :
    completedFlatPullbackOfSmooth C sP sY g hg a =
      DirectSum.of _ (-(smoothComponentRelativeDimension g a : ℤ))
        (flatPullbackBivariantClassOfInvertible C ((P.connectedComponentOpens a).ι ≫ sP)
            ((Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)).ι ≫ sY)
            (g.resConnectedComponent a) (g.resConnectedComponent_comp_ι_comp hg a)
            (smoothComponentRelativeDimension g a)
            (relativeDimension_smoothComponentRelativeDimension g a)) :=
  rfl

end Class

end Stacks.Chow

end
