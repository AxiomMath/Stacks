module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleProper
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleGysin
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InverseIsoGysin
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRule

/-!
# The Chern classes of a finite locally free module as bivariant classes

Let `X` be locally of finite type over the base of chapter 42 and let `ℰ` be a finite locally
free `𝒪_X`-module of rank `r`. [Stacks, Tag 0B7H] says that for `0 ≤ j ≤ r` the rule assigning to
`g : T ⟶ X` the operation `c_j(g^*ℰ) ∩ - : A_k(T) ⟶ A_{k-j}(T)` is a bivariant class
`c_j(ℰ) ∈ A^j(X)`.

The operations are `Stacks.Chow.GenuineChern.chernCap`, the cap products of [Stacks, Tag 02U6].

## Main definitions

* `Stacks.Chow.GenuineChern.chernClass` — the class `c_j(ℰ) ∈ A^j(X)`.
* `Stacks.Chow.GenuineChern.chernClassBivariantClass` — the class `c_j(ℰ)` bundled with its
  characterization.

## Main results

* `Stacks.Chow.GenuineChern.isChernClassBivariant_chernClass` — the class `c_j(ℰ)` caps by
  `c_j(g^*ℰ) ∩ -` on every test scheme.
* `Stacks.Chow.GenuineChern.idRule_chernClass` — its operation on a test scheme `g : T ⟶ X` is
  `c_j(g^*ℰ) ∩ -`.

## References

* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
  (j : Fin (r + 1))

/-- The `j`-th Chern class `c_j(ℰ) ∈ A^j(X)` of a finite locally free module of rank `r`: the
bivariant class of degree `j` for `𝟙 X` that caps by `c_j(g^*ℰ) ∩ -` on every test scheme
`g : T ⟶ X`. -/
def chernClass : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)
    (j : ℤ) :=
  chernClassBivariant C sX F r (gysinSystemOfInvertible C) (chernCap C r) j
    (chernCap_properNaturality C sX F r j) (chernCap_flatNaturality C sX F r j)
    (chernCap_gysinNaturality C sX F r j) (gysinSystemOfInvertible_isNaturalUnderInverseIso C)

/-- The class `c_j(ℰ)` caps by `c_j(g^*ℰ) ∩ -` on every test scheme. -/
theorem isChernClassBivariant_chernClass :
    IsChernClassBivariant C sX F r (gysinSystemOfInvertible C) (chernCap C r)
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j (chernClass C sX F r j) :=
  isChernClassBivariant_chernClassBivariant C sX F r (gysinSystemOfInvertible C) (chernCap C r) j
    _ _ _ _

/-- The operation of `c_j(ℰ)` on a test scheme `g : T ⟶ X` is `c_j(g^*ℰ) ∩ -`. -/
theorem idRule_chernClass {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
    (chernClass C sX F r j).idRule C sX (gysinSystemOfInvertible C) g k α =
      chernCap C r (g ≫ sX) ((Scheme.Modules.pullback g).obj F) k j α :=
  isChernClassBivariant_chernClass C sX F r j g k α

/-- For a finite locally free module `ℰ` of rank `r` on `X` and `0 ≤ j ≤ r`, the rule assigning
to `f : X' ⟶ X` the operation `c_j(f^*ℰ) ∩ - : A_k(X') ⟶ A_{k-j}(X')` is a bivariant class of
degree `j`: the class `c_j(ℰ) ∈ A^j(X)` together with its characterization. -/
@[stacks 0B7H]
def chernClassBivariantClass :
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ) //
      IsChernClassBivariant C sX F r (gysinSystemOfInvertible C) (chernCap C r)
        (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j c} :=
  ⟨chernClass C sX F r j, isChernClassBivariant_chernClass C sX F r j⟩

end Stacks.Chow.GenuineChern

end
