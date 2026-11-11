module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsSituation
import StacksCore.Tactic.StacksAttribute

/-!
# A site given by its coverings, with a distinguished set of quasi-compact objects

Let `C` be a site in the sense of the Stacks Project: a category together with a class
`Cov(C)` of coverings satisfying the isomorphism, locality and base change axioms. Let `B` be a
set of objects of `C`. The three conditions considered are

1. every object of `C` has a covering by elements of `B`;
2. every `U ∈ B` is quasi-compact;
3. for a covering `{U_i → U}` with `U_i, U ∈ B` the fibre products `U_i ×_U U_j` are
   quasi-compact.

Condition (3) quantifies over the coverings of the site, not over all families generating a
covering sieve, and the fibre products in it exist by the base change axiom. This file records
the situation with the site given by its class of coverings, so that all three conditions are
read in terms of `Cov(C)` itself.

## Main definitions

* `Stacks.Sites.IsQuasiCompactForCoverings`: an object `U` is quasi-compact for a class of
  coverings when every covering of `U` is refined, over the identity of `U`, by a covering whose
  index map has finite image.
* `Stacks.Sites.CoveringsSituation`: a class of coverings satisfying the site axioms together
  with a distinguished set of objects.
* `Stacks.Sites.CoveringsSituation.HasEnoughObjects`,
  `Stacks.Sites.CoveringsSituation.ObjectsAreQuasiCompact` and
  `Stacks.Sites.CoveringsSituation.CoverPullbacksAreQuasiCompact`: conditions (1), (2) and (3).
* `Stacks.Sites.coveringsOfTopology`: the families whose generated sieve is covering for a
  Grothendieck topology.
* `Stacks.Sites.QuasiCompactObjectsSituation.toCoveringsSituation`: in a category with fibre
  products, a Grothendieck topology with a set of objects, read as the site whose coverings are
  all families generating a covering sieve.

## Main results

* `Stacks.Sites.CoveringsSituation.hasPullback`: the fibre products in condition (3) exist.
* `Stacks.Sites.isSite_coveringsOfTopology`: in a category with fibre products, the families
  generating a covering sieve satisfy the site axioms.
* `Stacks.Sites.QuasiCompactObjectsSituation.coverPullbacksAreQuasiCompact_iff`: for that site,
  condition (3) is the condition `QuasiCompactObjectsSituation.CoverPullbacksAreQuasiCompact`
  stated for the Grothendieck topology; likewise for conditions (1) and (2).

## Implementation notes

`QuasiCompactObjectsSituation` states the three conditions for a Grothendieck topology, where
a covering is any family generating a covering sieve. Its condition (3) is therefore a
condition on every such family, which is in general strictly more than the source asks: for
the category with two objects `V, U` and two parallel arrows `a, b : V ⟶ U`, with the site
whose coverings are the single isomorphisms, the family `{𝟙 U, a, b}` generates the maximal
sieve while the fibre product of `a` and `b` does not exist. The present formulation agrees
with that one for the site of all families generating a covering sieve, which is what
`QuasiCompactObjectsSituation.toCoveringsSituation` and its lemmas record.

Quasi-compactness of an object is read in terms of the coverings of the site, as in Stacks
090H; for the site of all families generating a covering sieve it is
`GrothendieckTopology.IsQuasiCompactObject`.

## References

* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C]

/-- An object `U` is *quasi-compact* for a class `IsCov` of coverings if for every covering
`𝒰 = {U_i → U}` in `IsCov` there is a covering `𝒱 = {V_j → U}` in `IsCov` and a morphism of
families `𝒱 ⟶ 𝒰` over the identity of `U`, given by `α : J → I` and `V_j ⟶ U_{α(j)}`, such that
the image of `α` is finite. This is Stacks 090H for the site given by `IsCov`. -/
def IsQuasiCompactForCoverings (IsCov : Covering.{u, v, w} C → Prop) (U : C) : Prop :=
  ∀ 𝒰 : PreZeroHypercover.{w} U, IsCov ⟨U, 𝒰⟩ →
    ∃ (𝒱 : PreZeroHypercover.{w} U) (φ : 𝒱.Hom 𝒰), IsCov ⟨U, 𝒱⟩ ∧ (Set.range φ.s₀).Finite

/-- A site, given by a class `IsCov` of coverings satisfying the site axioms, together with a
set of its objects. Conditions (1), (2) and (3) on the set are
`CoveringsSituation.HasEnoughObjects`, `CoveringsSituation.ObjectsAreQuasiCompact` and
`CoveringsSituation.CoverPullbacksAreQuasiCompact`. -/
@[stacks 0937 "The standing data: a site, given by its class of coverings, and a set B of its
  objects. Conditions (1), (2) and (3) are `CoveringsSituation.HasEnoughObjects`,
  `CoveringsSituation.ObjectsAreQuasiCompact` and
  `CoveringsSituation.CoverPullbacksAreQuasiCompact`, all stated in terms of the coverings of the
  site."]
structure CoveringsSituation (C : Type u) [Category.{v} C] where
  /-- The class of coverings of the site. -/
  IsCov : Covering.{u, v, w} C → Prop
  /-- The coverings satisfy the isomorphism, locality and base change axioms. -/
  isSite : IsSite IsCov
  /-- The distinguished set of objects. -/
  objects : Set C

namespace CoveringsSituation

/-- Condition (1): every object of the site has a covering all of whose members belong to the
distinguished set. -/
@[stacks 0937 "condition (1)"]
def HasEnoughObjects (S : CoveringsSituation.{w} C) : Prop :=
  ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{w} U, S.IsCov ⟨U, 𝒰⟩ ∧ ∀ i, 𝒰.X i ∈ S.objects

/-- Condition (2): every object of the distinguished set is quasi-compact for the coverings of
the site. -/
@[stacks 0937 "condition (2)"]
def ObjectsAreQuasiCompact (S : CoveringsSituation.{w} C) : Prop :=
  ∀ U : C, U ∈ S.objects → IsQuasiCompactForCoverings S.IsCov U

/-- The fibre products of the members of a covering of the site exist: they are given by the
base change axiom applied along a member of the covering. -/
theorem hasPullback (S : CoveringsSituation.{w} C) {U : C} {𝒰 : PreZeroHypercover.{w} U}
    (h𝒰 : S.IsCov ⟨U, 𝒰⟩) (i j : 𝒰.I₀) : HasPullback (𝒰.f i) (𝒰.f j) := by
  obtain ⟨_, _, _, hpb, -⟩ := S.isSite.2.2 ⟨U, 𝒰⟩ h𝒰 (𝒰.X j) (𝒰.f j)
  exact (hpb i).hasPullback

/-- Condition (3): for a covering `{U_i → U}` of the site with `U` and every `U_i` in the
distinguished set, every fibre product `U_i ×_U U_j` is quasi-compact. The fibre products exist
by the base change axiom, `CoveringsSituation.hasPullback`, which chooses them. -/
@[stacks 0937 "condition (3)"]
def CoverPullbacksAreQuasiCompact (S : CoveringsSituation.{w} C) : Prop :=
  ∀ (U : C) (𝒰 : PreZeroHypercover.{w} U) (h𝒰 : S.IsCov ⟨U, 𝒰⟩),
    U ∈ S.objects →
      (∀ i, 𝒰.X i ∈ S.objects) →
      ∀ i j,
        haveI := S.hasPullback h𝒰 i j
        IsQuasiCompactForCoverings S.IsCov (pullback (𝒰.f i) (𝒰.f j))

end CoveringsSituation

/-! ### The site of all families generating a covering sieve -/

/-- The families whose generated sieve is covering for the Grothendieck topology `J`. -/
def coveringsOfTopology (J : GrothendieckTopology C) : Covering.{u, v, max u v} C → Prop :=
  fun 𝒰 => 𝒰.2.sieve₀ ∈ J 𝒰.1

/-- Postcomposing a family generating a covering sieve with an isomorphism of its target coming
from an equality of objects leaves it generating a covering sieve. -/
private theorem generate_ofArrows_comp_eqToHom_mem (J : GrothendieckTopology C) {A B : C}
    (e : A = B) {ι : Type*} (X : ι → C) (f : ∀ j, X j ⟶ A)
    (hf : Sieve.generate (Presieve.ofArrows X f) ∈ J A) :
    Sieve.generate (Presieve.ofArrows X fun j => f j ≫ eqToHom e) ∈ J B := by
  subst e
  simpa using hf

/-- In a category with fibre products, the families generating a covering sieve of a
Grothendieck topology satisfy the isomorphism, locality and base change axioms of a site. -/
theorem isSite_coveringsOfTopology [HasPullbacks C] (J : GrothendieckTopology C) :
    IsSite (coveringsOfTopology J) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    change Sieve.generate (PreZeroHypercover.singleton.{max u v} f).presieve₀ ∈ J U
    rw [PreZeroHypercover.presieve₀_singleton]
    exact (J.mem_toPrecoverage_iff _).1
      (Precoverage.HasIsos.mem_coverings_of_isIso (J := J.toPrecoverage) f)
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    exact Precoverage.IsStableUnderComposition.comp_mem_coverings
      (J := J.toPrecoverage) 𝒰.2.f h𝒰 (fun i j => (𝒱 i).2.f j ≫ eqToHom (h i))
      fun i => generate_ofArrows_comp_eqToHom_mem J (h i) (𝒱 i).2.X (𝒱 i).2.f (h𝒱 i)
  · intro 𝒰 h𝒰 V g
    refine ⟨fun i => pullback (𝒰.2.f i) g, fun i => pullback.fst _ _,
      fun i => pullback.snd _ _, fun i => IsPullback.of_hasPullback _ _, ?_⟩
    exact Precoverage.mem_coverings_of_isPullback (J := J.toPrecoverage) 𝒰.2.f h𝒰 g _ _
      fun i => (IsPullback.of_hasPullback (𝒰.2.f i) g).flip

/-- For the site of all families generating a covering sieve, quasi-compactness of an object is
quasi-compactness for the Grothendieck topology. -/
theorem isQuasiCompactForCoverings_coveringsOfTopology_iff (J : GrothendieckTopology C)
    (U : C) :
    IsQuasiCompactForCoverings (coveringsOfTopology J) U ↔ J.IsQuasiCompactObject U :=
  Iff.rfl

namespace QuasiCompactObjectsSituation

variable [HasPullbacks C]

/-- In a category with fibre products, a Grothendieck topology with a set of objects, read as
the site whose coverings are all families generating a covering sieve. -/
def toCoveringsSituation (S : QuasiCompactObjectsSituation C) :
    CoveringsSituation.{max u v} C where
  IsCov := coveringsOfTopology S.topology
  isSite := isSite_coveringsOfTopology S.topology
  objects := S.objects

/-- Condition (1) for the site of all families generating a covering sieve is condition (1)
for the Grothendieck topology. -/
theorem hasEnoughObjects_iff (S : QuasiCompactObjectsSituation C) :
    S.toCoveringsSituation.HasEnoughObjects ↔ S.HasEnoughObjects :=
  Iff.rfl

/-- Condition (2) for the site of all families generating a covering sieve is condition (2)
for the Grothendieck topology. -/
theorem objectsAreQuasiCompact_iff (S : QuasiCompactObjectsSituation C) :
    S.toCoveringsSituation.ObjectsAreQuasiCompact ↔ S.ObjectsAreQuasiCompact :=
  Iff.rfl

/-- Condition (3) for the site of all families generating a covering sieve is condition (3)
for the Grothendieck topology: in a category with fibre products the existence conjunct of the
latter holds automatically. -/
theorem coverPullbacksAreQuasiCompact_iff (S : QuasiCompactObjectsSituation C) :
    S.toCoveringsSituation.CoverPullbacksAreQuasiCompact ↔
      S.CoverPullbacksAreQuasiCompact := by
  constructor
  · intro h U 𝒰 h𝒰 hU hX i j
    exact ⟨inferInstance, h U 𝒰 h𝒰 hU hX i j⟩
  · intro h U 𝒰 h𝒰 hU hX i j
    exact (h U 𝒰 h𝒰 hU hX i j).2

/-- A Grothendieck topology on a category with fibre products satisfying conditions (1), (2)
and (3) of `QuasiCompactObjectsSituation` gives a site, the one of all families generating a
covering sieve, satisfying conditions (1), (2) and (3) of `CoveringsSituation`. -/
theorem toCoveringsSituation_conditions (S : QuasiCompactObjectsSituation C)
    (h₁ : S.HasEnoughObjects) (h₂ : S.ObjectsAreQuasiCompact)
    (h₃ : S.CoverPullbacksAreQuasiCompact) :
    S.toCoveringsSituation.HasEnoughObjects ∧ S.toCoveringsSituation.ObjectsAreQuasiCompact ∧
      S.toCoveringsSituation.CoverPullbacksAreQuasiCompact :=
  ⟨h₁, h₂, (coverPullbacksAreQuasiCompact_iff S).2 h₃⟩

end QuasiCompactObjectsSituation

end Stacks.Sites

end
