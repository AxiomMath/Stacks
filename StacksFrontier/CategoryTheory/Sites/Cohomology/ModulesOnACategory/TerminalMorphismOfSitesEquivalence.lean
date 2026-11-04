module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalMorphismOfSites
import StacksCore.Tactic.StacksAttribute

/-!
# The equivalence between derived modules over a section ring and quasi-coherent derived modules

Let `C` be a category with a terminal object `X`, viewed as a site with the chaotic topology, let
`O : Cᵒᵖ ⥤ RingCat` be a sheaf of rings whose section rings are commutative, and write `R = O(X)`.
The unique functor `C ⥤ pt` is the obvious morphism of sites `f : (C, O) → (pt, R)`, whose
pushforward is `Rf_* = RΓ(X, -)` and whose derived pullback `Lf^* : D(R) ⥤ D(O)` is the functor
constructed in `TerminalMorphismOfSites`.

`Lf^*` and `Rf_*` restrict to mutually quasi-inverse equivalences between `D(R)` and the full
subcategory `QC(O) ⊆ D(O)` of objects whose derived sections are cartesian: `Lf^*` lands in
`QC(O)`, the unit of `Lf^* ⊣ Rf_*` is invertible on all of `D(R)`, and its counit is invertible on
every object of `QC(O)`.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.main_equivalence`: the three assertions, for
  the derived pullback along the morphism of sites of a terminal object.

## Implementation notes

`BrownRepresentability` proves the three assertions for an arbitrary base-change datum `bc` and an
arbitrary morphism of sites over it, as `main_equivalence_of_morphismOfSites`. What is proved here
is that statement at the canonical base-change datum
`Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.baseChangeDataOfComm` — the canonical
one, over arbitrary ring and module universes — and at the morphism of sites
`Stacks.ModulesOnACategory.TerminalMorphismOfSites.morphismOfSites` constructed from `O` and the
terminal object, so that it assumes nothing beyond the commutativity `hO` of the section rings of
`O`, which is also the hypothesis of the canonical datum itself. No generality is given up: the
universes are those of the generic form.

This is stated here rather than alongside the generic form because the morphism of sites is built
from the material of `BrownRepresentability` and so is only available downstream of it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

universe w u v r

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

-- As in `BrownRepresentability`, the ambient derived category uses the small-Hom model and the
-- section categories use the standard localization model.
attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}} {X : C} (hX : IsTerminal X)

/-- **Lemma 21.43.4 (tag 0H0R).** The adjunction `Lf^* ⊣ Rf_*` along the morphism of sites
`f : (C, O) → (pt, O(X))` of a terminal object `X` exhibits `Lf^*` and `Rf_*` as mutually
quasi-inverse equivalences between `D(O(X))` and `QC(O)`: the derived pullback lands in `QC(O)`,
the unit is invertible on all of `D(O(X))`, and the counit is invertible on every object of
`QC(O)`.

Both the base change and the derived pullback are the library's own constructions here — the
canonical base-change datum, and the morphism of sites of `X` — so the only hypothesis is the
commutativity `hO` of the section rings of `O`. -/
@[stacks 0H0R]
theorem main_equivalence (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x) :
    (∀ P, IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} O hO)
        ((morphismOfSites O hO hX).Lpullback.obj P)) ∧
    (∀ P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X))),
      IsIso ((morphismOfSites O hO hX).adj.unit.app P)) ∧
    (∀ K, IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} O hO) K →
      IsIso ((morphismOfSites O hO hX).adj.counit.app K)) :=
  main_equivalence_of_morphismOfSites.{w} (baseChangeDataOfComm.{r, v, u, w} O hO)
    (morphismOfSites O hO hX)

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
