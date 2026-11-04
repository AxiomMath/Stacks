module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Stacks 008O: stalks of pulled-back abelian (pre)sheaves

For a continuous map `f : X ⟶ Y`:

* Part (1): if `G` is an abelian presheaf on `Y`, the canonical bijection
  `G_{f(x)} ≃ (f_p G)_x` (Stacks tag `0078`) is an isomorphism of abelian
  groups.

* Part (2): if `G` is an abelian sheaf on `Y`, the canonical bijection
  `G_{f(x)} ≃ (f⁻¹ G)_x` (the sheaf-level analogue) is an isomorphism of
  abelian groups.

Both parts are recorded in Mathlib for an arbitrary value category `C` with
filtered colimits. Part (1) is `TopCat.Presheaf.stalkPullbackIso` specialised
to `C = AddCommGrpCat`. Part (2) is obtained from part (1) by composing
through `TopCat.Sheaf.pullbackIso`, which identifies the sheaf pullback with
the sheafification of the presheaf pullback, and through the canonical
isomorphism between the stalk functor on presheaves and the composition
`presheafToSheaf ⋙ Sheaf.forget ⋙ stalkFunctor`. The latter iso comes from
the fact that both functors are left adjoint to the skyscraper presheaf
functor (`Presheaf.skyscraperPresheafStalkAdjunction` /
`Presheaf.skyscraperSheafForgetAdjunction`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

open scoped AlgebraicGeometry


universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

namespace Stacks.Topology.AbelianStalk

/-- **Stacks tag 008O, part (1).**
For a continuous map `f : X ⟶ Y` and an abelian presheaf `G` on `Y`, the
canonical comparison map between the stalk of `G` at `f x` and the stalk of
the presheaf pullback `f_p G` at `x` is an isomorphism of abelian groups.

This is `TopCat.Presheaf.stalkPullbackIso` specialised to the category of
abelian groups. -/
@[stacks 008O "(1)"]
noncomputable def stalkPullbackIso_presheaf
    (G : Y.Presheaf AddCommGrpCat.{v}) (x : X) :
    G.stalk (f x) ≅ ((Presheaf.pullback AddCommGrpCat.{v} f).obj G).stalk x :=
  Presheaf.stalkPullbackIso AddCommGrpCat.{v} f G x

/-- For an abelian presheaf `P` on a topological space `X` and `x : X`, the
canonical map from the stalk of `P` to the stalk of its sheafification (the
image of the sheafification unit under the stalk functor) is an isomorphism.

This is `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` read as an
isomorphism. -/
noncomputable def sheafifyStalkIso
    (P : X.Presheaf AddCommGrpCat.{v}) (x : X) :
    (Presheaf.stalkFunctor AddCommGrpCat.{v} x).obj P ≅
      (Presheaf.stalkFunctor AddCommGrpCat.{v} x).obj
        ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj P)) :=
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{v} P
  asIso ((Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P))

/-- **Stacks tag 008O, part (2).**
For a continuous map `f : X ⟶ Y` and an abelian sheaf `G` on `Y`, the canonical
comparison map between the stalk of `G` at `f x` and the stalk of the sheaf
pullback `f⁻¹ G` at `x` is an isomorphism of abelian groups.

The proof factors the comparison through the presheaf pullback: first
`Presheaf.stalkPullbackIso` gives the presheaf-level iso, then
`Sheaf.pullbackIso` identifies the sheaf pullback with the sheafification of
the presheaf pullback, and `sheafifyStalkIso` (above) gives the stalk iso for
the sheafification step. -/
@[stacks 008O "(2)"]
noncomputable def stalkPullbackIso_sheaf
    (G : Y.Sheaf AddCommGrpCat.{v}) (x : X) :
    G.presheaf.stalk (f x) ≅
      ((Sheaf.pullback AddCommGrpCat.{v} f).obj G).presheaf.stalk x := by
  -- Step 1: presheaf-level iso `G_{f(x)} ≅ (f_p G)_x`.
  refine Presheaf.stalkPullbackIso AddCommGrpCat.{v} f G.presheaf x ≪≫ ?_
  -- Step 2: sheafification stalk iso for the presheaf pullback.
  refine sheafifyStalkIso ((Presheaf.pullback AddCommGrpCat.{v} f).obj G.presheaf) x ≪≫ ?_
  -- Step 3: transport along `Sheaf.pullbackIso`, the natural iso between the
  -- sheaf pullback and the sheafified presheaf pullback. The composite
  -- `Sheaf.pullback _ f ⋙ Sheaf.forget _ _` agrees with
  -- `Sheaf.forget _ _ ⋙ Presheaf.pullback _ f ⋙ presheafToSheaf _ _ ⋙ Sheaf.forget _ _`
  -- by `Sheaf.pullbackIso`, so the natural transformation between underlying
  -- presheaves is an iso.
  exact (Presheaf.stalkFunctor AddCommGrpCat.{v} x).mapIso
    ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).mapIso
      ((Sheaf.pullbackIso AddCommGrpCat.{v} f).symm.app G))

end Stacks.Topology.AbelianStalk
