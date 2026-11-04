module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksCore.Tactic.StacksAttribute

/-!
# Divisor cuts of a fixed invertible sheaf, and the independence of their cycle classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `L` be an invertible `𝒪_X`-module. Cutting a closed subscheme
`i : Y ⟶ X` of `δ`-dimension `k + 1` by the divisor of a global section `s` of `L|_Y` produces
the closed subscheme `Z(s) ⊆ Y ⊆ X`, and **Stacks 02SQ** computes its cycle class:

`[Z(s)]_k = c₁(L) ∩ [Y]_{k + 1}` in `A_k(X)`.

The right-hand side does not mention `s`. So the class of the cut is the same for *every* section
of `L|_Y` that cuts properly, and that is what this file records.

## Main definitions

* `Stacks.Chow.CompleteIntersection.IsProperDivisorCut` — the three hypotheses of Stacks 02SQ for
  a global section `s` of `L|_Y` on a closed subscheme `i : Y ⟶ X`: that `Y` has
  `δ`-dimension at most `k + 1`, that the zero scheme of `s` has `δ`-dimension at most `k`, and
  that multiplication by `s` is injective on the local ring at the generic point of every
  component of that zero scheme of `δ`-dimension `k`.
* `Stacks.Chow.CompleteIntersection.cutSubscheme` — the closed immersion `Z(s) ⟶ X` of the cut
  into the ambient scheme, the composite of `Z(s) ⟶ Y` with `i`.
* `Stacks.Chow.CompleteIntersection.IsIteratedDivisorCut` — a `d`-fold complete intersection of
  divisors of sections of `L`: a chain `X = W_0 ⊇ ⋯ ⊇ W_d` in which each `W_{j+1}` is a proper
  divisor cut of `W_j`.

## Main results

* `Stacks.Chow.CompleteIntersection.mk_cutSubscheme_eq_firstChernClassCapChow` — the class of a
  proper divisor cut is the Chern cap of the class being cut: `[Z(s)]_k = c₁(L) ∩ [Y]_{k+1}` in
  `A_k(X)`, with both sides read as Chow classes.
* `Stacks.Chow.CompleteIntersection.mk_cutSubscheme_eq_mk_cutSubscheme` — **the independence in
  codimension one**: two global sections of `L|_Y` which both cut `Y` properly have cut
  subschemes with the same cycle class in `A_k(X)`.
* `Stacks.Chow.CompleteIntersection.mk_eq_mk_of_isIteratedDivisorCut` — **the independence in
  every codimension**: any two `d`-fold complete intersections of divisors of sections of the
  same `L`, ending in the same `δ`-dimension, have the same cycle class.

## Implementation notes

The `δ`-dimension of a scheme over the base is `Stacks.Chow.schemeDeltaDimension`, with values in
`EInt`; the cut's hypotheses bound it above rather than pinning it, exactly as Stacks 02SQ does,
so that a cut which drops the dimension by more than one is still admissible.

## References

* [Stacks Project, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Chow.CompleteIntersection

open Stacks.Chow Stacks.Divisors Stacks.ChernCap42

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (i : Y ⟶ X) [IsClosedImmersion i] (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The zero scheme on `Y` of a global section of the restriction of `L` to `Y`. -/
abbrev cutIdeal (s : ((Scheme.Modules.pullback i).obj L).sections) : Y.IdealSheafData :=
  Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) (s.eval (op ⊤))

/-- The closed immersion of the divisor cut `Z(s) ⊆ Y` into the ambient scheme `X`. -/
abbrev cutSubscheme (s : ((Scheme.Modules.pullback i).obj L).sections) :
    (cutIdeal i L s).subscheme ⟶ X :=
  (cutIdeal i L s).subschemeι ≫ i

/-- **The hypotheses of Stacks 02SQ for one cut.** A global section `s` of `L|_Y` cuts the closed
subscheme `i : Y ⟶ X` properly in degree `k` when `Y` has `δ`-dimension at most `k + 1`, the zero
scheme `Z(s)` has `δ`-dimension at most `k`, and multiplication by `s` is injective on the local
ring at the generic point of every component of `Z(s)` of `δ`-dimension `k`. -/
def IsProperDivisorCut (s : ((Scheme.Modules.pullback i).obj L).sections) : Prop :=
  schemeDeltaDimension C (i ≫ p) ≤ (k + 1 : EInt) ∧
    schemeDeltaDimension C ((cutIdeal i L s).subschemeι ≫ (i ≫ p)) ≤ (k : EInt) ∧
      ∀ ξ : genericPoints (cutIdeal i L s).subscheme,
        relativeDimension C.dimensionFunction (i ≫ p)
            ((cutIdeal i L s).subschemeι ξ.1) = k →
          Function.Injective (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              ((cutIdeal i L s).subschemeι ξ.1)).map
              ((Scheme.Modules.toPresheaf Y).map
                (((Scheme.Modules.pullback i).obj L).unitHomEquiv.symm s))))

/-- **Stacks 02SQ, read on Chow classes.** The class of a proper divisor cut of `L` is the class
being cut, capped with the first Chern class of `L`:

`[Z(s)]_k = c₁(L) ∩ [Y]_{k + 1}` in `A_k(X)`.

Stacks 02SQ states this with the cut applied to the *cycle* `[Y]_{k+1}`; here both sides are Chow
classes, using the descended cap product of Stacks 02TI. -/
theorem mk_cutSubscheme_eq_firstChernClassCapChow
    (s : ((Scheme.Modules.pullback i).obj L).sections)
    (hs : IsProperDivisorCut C p i k L s) :
    QuotientAddGroup.mk' (rationalEquivalences C p k)
        (cycleAssociatedToClosedSubscheme C p (cutSubscheme i L s) k) =
      firstChernClassCapChow C k p L (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))
        (cycleAssociatedToClosedSubscheme C p i (k + 1))) :=
  (firstChernClassCapOfInvertible_closedSubscheme_eq_zeroScheme C p i k L s hs.1 hs.2.1
    hs.2.2).symm

/-- **The independence of a divisor cut from the section that cuts.** Two global sections of
`L|_Y` which both cut the closed subscheme `i : Y ⟶ X` properly in degree `k` have cut
subschemes with the same cycle class in `A_k(X)`. -/
theorem mk_cutSubscheme_eq_mk_cutSubscheme
    (s s' : ((Scheme.Modules.pullback i).obj L).sections)
    (hs : IsProperDivisorCut C p i k L s) (hs' : IsProperDivisorCut C p i k L s') :
    QuotientAddGroup.mk' (rationalEquivalences C p k)
        (cycleAssociatedToClosedSubscheme C p (cutSubscheme i L s) k) =
      QuotientAddGroup.mk' (rationalEquivalences C p k)
        (cycleAssociatedToClosedSubscheme C p (cutSubscheme i L s') k) :=
  (mk_cutSubscheme_eq_firstChernClassCapChow C p i k L s hs).trans
    (mk_cutSubscheme_eq_firstChernClassCapChow C p i k L s' hs').symm

/-! ### Complete intersections: iterating the cut -/

/-- **A `d`-fold complete intersection of divisors of sections of `L`.** The closed immersion
`ι : A ⟶ X` presents `A` as the result of `d` successive proper divisor cuts of `L` starting from
`X`, the last cut landing in `δ`-dimension `k`: there is a chain

`X = W_0 ⊇ W_1 ⊇ ⋯ ⊇ W_d = A`

in which `W_{j+1}` is the zero scheme of a global section of `L` restricted to `W_j`, each cut
satisfying the hypotheses of Stacks 02SQ at its own degree.

The recursion is indexed by the degree the chain *ends* at, so the inner chain of a `(d+1)`-fold
cut ending at `k` is a `d`-fold cut ending at `k + 1`. The sections and the intermediate
subschemes are existentially quantified. -/
def IsIteratedDivisorCut (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ℕ → ℤ → ∀ A : Scheme.{u}, (A ⟶ X) → Prop
  | 0, _, _, ι => IsIso ι
  | (d + 1), k, A, ι =>
    ∃ (W : Scheme.{u}) (κ : W ⟶ X) (hκ : IsClosedImmersion κ),
      letI : IsClosedImmersion κ := hκ
      IsIteratedDivisorCut C p L d (k + 1) W κ ∧
        ∃ s : ((Scheme.Modules.pullback κ).obj L).sections,
          IsProperDivisorCut C p κ k L s ∧
            ∃ e : A ≅ (cutIdeal κ L s).subscheme, e.hom ≫ cutSubscheme κ L s = ι

/-- **The independence of a complete intersection from the sections that cut it.** Any two
`d`-fold complete intersections of divisors of sections of the *same* invertible sheaf `L`, both
ending in `δ`-dimension `k`, have the same cycle class in `A_k(X)`. -/
theorem mk_eq_mk_of_isIteratedDivisorCut (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ∀ (d : ℕ) (k : ℤ) {A A' : Scheme.{u}} (ι : A ⟶ X) (ι' : A' ⟶ X)
      [IsClosedImmersion ι] [IsClosedImmersion ι'],
      IsIteratedDivisorCut C p L d k A ι → IsIteratedDivisorCut C p L d k A' ι' →
        QuotientAddGroup.mk' (rationalEquivalences C p k)
            (cycleAssociatedToClosedSubscheme C p ι k) =
          QuotientAddGroup.mk' (rationalEquivalences C p k)
            (cycleAssociatedToClosedSubscheme C p ι' k)
  | 0, k, A, A', ι, ι', _, _, h, h' => by
    let : IsIso ι := h
    let : IsIso ι' := h'
    exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso C p ι ι'
      (asIso ι ≪≫ (asIso ι').symm) (by simp) k)
  | (d + 1), k, A, A', ι, ι', _, _, h, h' => by
    obtain ⟨W, κ, hκ, hchain, s, hs, e, he⟩ := h
    obtain ⟨W', κ', hκ', hchain', s', hs', e', he'⟩ := h'
    let : IsClosedImmersion κ := hκ
    let : IsClosedImmersion κ' := hκ'
    rw [cycleAssociatedToClosedSubscheme_eq_of_iso C p ι (cutSubscheme κ L s) e he k,
      cycleAssociatedToClosedSubscheme_eq_of_iso C p ι' (cutSubscheme κ' L s') e' he' k,
      mk_cutSubscheme_eq_firstChernClassCapChow C p κ k L s hs,
      mk_cutSubscheme_eq_firstChernClassCapChow C p κ' k L s' hs']
    exact congrArg _ (mk_eq_mk_of_isIteratedDivisorCut C p L d (k + 1) κ κ' hchain hchain')

end Stacks.Chow.CompleteIntersection

end
