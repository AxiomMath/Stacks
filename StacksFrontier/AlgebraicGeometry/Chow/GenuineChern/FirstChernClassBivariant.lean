module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts

/-!
# The first Chern class of an invertible module as a bivariant class

For an invertible `𝒪_X`-module `ℒ` on a scheme `X` locally of finite type over the base of
chapter 42, [Stacks, Tag 0B77] says that the rule assigning to `g : T ⟶ X` the operation
`c₁(g^*ℒ) ∩ - : A_k(T) ⟶ A_{k-1}(T)` is a bivariant class `c₁(ℒ) ∈ A^1(X)`. An invertible module
is finite locally free of rank one, so this is the case `r = j = 1` of [Stacks, Tag 0B7H]
(`Stacks.Chow.GenuineChern.chernClass`), the Chern class cap product of rank one being the first
Chern class cap (`Stacks.Chow.GenuineChern.chernCap_one_eq_invCap`).

## Main definitions

* `Stacks.Chow.GenuineChern.firstChernClass`: the class `c₁(ℒ) ∈ A^1(X)`.
* `Stacks.Chow.GenuineChern.firstChernClassBivariantClass`: the class bundled with its
  characterization.

## Main results

* `Stacks.Chow.GenuineChern.idRule_firstChernClass`: the operation of `c₁(ℒ)` on every test
  scheme `g : T ⟶ X` is `c₁(g^*ℒ) ∩ -`.

## References

* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The first Chern class `c₁(ℒ) ∈ A^1(X)` of an invertible module: the bivariant class of
degree `1` for `𝟙 X` that caps by `c₁(g^*ℒ) ∩ -` on every test scheme `g : T ⟶ X`. -/
def firstChernClass :
    BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) 1 :=
  haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  chernClass C sX L 1 1

/-- The operation of `c₁(ℒ)` on a test scheme `g : T ⟶ X` is `c₁(g^*ℒ) ∩ -`. -/
theorem idRule_firstChernClass {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    (firstChernClass C sX L).idRule C sX (gysinSystemOfInvertible C) g k α =
      (invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj L)).capOnChow C (g ≫ sX) (k - 1)
        (chowGroupCast C (g ≫ sX) (by omega) α) := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 g
  exact (idRule_chernClass C sX L 1 1 g k α).trans
    (chernCap_one_eq_invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj L) k α)

/-- For an invertible module `ℒ` on `X`, the rule assigning to `f : X' ⟶ X` the operation
`c₁(f^*ℒ) ∩ - : A_k(X') ⟶ A_{k-1}(X')` is a bivariant class of degree `1`: the class
`c₁(ℒ) ∈ A^1(X)` together with the statement that it caps by `c₁(f^*ℒ) ∩ -` on every test
scheme. -/
@[stacks 0B77]
def firstChernClassBivariantClass :
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) 1 //
      ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ sX) k),
        c.idRule C sX (gysinSystemOfInvertible C) g k α =
          (invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj L)).capOnChow C (g ≫ sX) (k - 1)
            (chowGroupCast C (g ≫ sX) (by omega) α)} :=
  ⟨firstChernClass C sX L, fun g _ k α => idRule_firstChernClass C sX L g k α⟩

end Stacks.Chow.GenuineChern

end
