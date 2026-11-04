module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCyclesDescent

/-!
# The Chern classes of a finite locally free module are bivariant classes

Let `X` be locally of finite type over the base of chapter 42, let `ℰ` be a locally free
`𝒪_X`-module of rank `r` and let `0 ≤ p ≤ r`. [Stacks, Tag 0B7H] says that the rule assigning to
`f : X' ⟶ X` the operation `c_p(f^*ℰ) ∩ - : A_k(X') ⟶ A_{k-p}(X')` is a bivariant class of
degree `p`. Here `c_p(f^*ℰ) ∩ -` is the operation of [Stacks, Tag 02U5] on `k`-cycles, which
factors through rational equivalence by [Stacks, Tag 02U7].

`Stacks.Chow.GenuineChern.chernClassBivariantClassOnCycles` is a bivariant class `c` of degree
`p` for `𝟙 X` such that, for every `f : X' ⟶ X` locally of finite type and every `k`-cycle `α` on
`X'`, `c ∩ [α] = c_p(f^*ℰ) ∩ α` with the right hand side the operation
`Stacks.Chow.GenuineChern.chernCapOnCycles` of Stacks 02U5. The base change of `𝟙 X` along `f` is
the chosen pullback `X ×_X X'`, identified with `X'` by its second projection; the cap operation
is read on `X'` through that identification.

The class is `Stacks.Chow.GenuineChern.chernClass`, built from the cap products of
[Stacks, Tag 02U6]; that these agree with the operation of Stacks 02U5 on every cycle is
`Stacks.Chow.GenuineChern.chernCap_mk_eq_chernCapOnCycles`.

The group `A^p(X)` is `Stacks.Chow.BivariantClass` at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible` of the Gysin maps of Stacks 02TO for the first Chern class
of an invertible module, so its third axiom is axiom (3) of [Stacks, Tag 0B76] for the genuine
Gysin maps.

## Main definitions

* `Stacks.Chow.GenuineChern.chernClassBivariantClassOnCycles` — **Stacks 0B7H**.

## References

* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U7](https://stacks.math.columbia.edu/tag/02U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
  (j : Fin (r + 1))

/-- **Stacks 0B7H.** For a locally free module `ℰ` of rank `r` on `X` and `0 ≤ j ≤ r`, the rule
assigning to `f : X' ⟶ X` the operation `c_j(f^*ℰ) ∩ - : A_k(X') ⟶ A_{k-j}(X')` of Stacks 02U5 is
a bivariant class of degree `j`: a class `c ∈ A^j(X)` with `c ∩ [α] = c_j(f^*ℰ) ∩ α` for every
`f : X' ⟶ X` and every `k`-cycle `α` on `X'`, the cap operation being read on `X'` through the
identification `X ×_X X' ≅ X'`. -/
@[stacks 0B7H]
def chernClassBivariantClassOnCycles :
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ) //
      ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : CycleGroup C (g ≫ sX) k),
        letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
        chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
            (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g)
            (k - (j : ℤ)) (c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sX) k) α)) =
          chernCapOnCycles C (g ≫ sX) ((Scheme.Modules.pullback g).obj F) r k j α} :=
  ⟨chernClass C sX F r j, fun g _ k α ↦
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
    (isChernClassBivariant_chernClass C sX F r j g k _).trans
      (chernCap_mk_eq_chernCapOnCycles C (g ≫ sX) ((Scheme.Modules.pullback g).obj F) r k j α)⟩

end Stacks.Chow.GenuineChern

end
