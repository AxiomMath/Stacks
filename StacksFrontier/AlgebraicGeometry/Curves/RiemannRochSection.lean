module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochGenuine
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
import StacksCore.Tactic.StacksAttribute

/-!
# The prose of Section [Stacks, Tag 0B5B], Riemann--Roch

Section [Stacks, Tag 0B5B] works with a field `k` and a proper scheme `X` of dimension at most
one over `k`. Its displayed formulas are tags of their own and are formalized as such: the degree
formula [Stacks, Tag 0BRX] is `AlgebraicGeometry.curveDegree`, the equality
`deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)` of [Stacks, Tag 0BRY] is
`AlgebraicGeometry.curveDegree_eq_chowDegree_firstChernCapOnCycles_fundamental`, the first
Riemann--Roch formula [Stacks, Tag 0BRZ] is
`AlgebraicGeometry.eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add`, and
`(𝓛 · X) = deg(𝓛)` and `deg_𝓛(X) = (𝓛 · X) = deg(𝓛)` of [Stacks, Tag 0BS0] and
[Stacks, Tag 0BS1] are `AlgebraicGeometry.eq_invertibleCurveDegree_of_isSelfIntersectionNumber`
and `AlgebraicGeometry.isSelfIntersectionNumber_one_iff_of_topologicalKrullDim_eq_one`. The two
lemmas of the section, [Stacks, Tag 0BS5] and [Stacks, Tag 0BS6], are also tags of their own.

This file formalizes the two mathematical assertions the section makes in its own prose.

* `AlgebraicGeometry.selfIntersectionNumber_pos_and_invertibleCurveDegree_pos_of_isAmple`:
  **"If `𝓛` is ample, then this integer is positive"**, the integer being
  `(𝓛 · X) = deg(𝓛)`.
* `AlgebraicGeometry.curveDegree_dualizingSheafOverField_eq_neg_two_mul_and_chowDegree`:
  **"`-1/2` of the first Chern class of `ω_X` capped with the cycle `[X]_1` is a zero cycle
  whose degree is `χ(X, 𝒪_X)`"**, in the case the section names, `ω_X` invertible, read off
  [Stacks, Tag 0BS5] exactly as the section says it will be.

## The dimension in the positivity claim

The section's standing hypothesis is `dim X ≤ 1`, but the positivity claim needs `dim X = 1`, and
it is stated so here. At dimension zero it is false: for `X = Spec k` the module `𝓛 = 𝒪_X` is
ample (`X` is affine), and `deg(𝒪_X) = χ(X, 𝒪_X) - χ(X, 𝒪_X) = 0` by the defining formula
[Stacks, Tag 0BRX]; equally `(𝒪_X · X)`, the linear coefficient of the constant polynomial
`n ↦ χ(X, 𝒪_X)`, is `0`. (For empty `X` both are `0` as well.) The section goes on to call this
integer `deg_𝓛(X)` by [Stacks, Tag 0BEW], which defines `deg_𝓛(Z)` as `(𝓛^{dim Z} · Z)`; that
reading `(𝓛 · X)` presupposes `dim X = 1`, so the corrected hypothesis is the one the section's
own notation uses. The proof is [Stacks, Tag 0BEV] at the closed subscheme `X ⊆ X`, transported
to `deg(𝓛)` by [Stacks, Tag 0BEY].

## The Riemann--Roch claim

The section says it will "use Lemma [Stacks, Tag 0BS5] to get the desired formula for
`χ(X, 𝒪_X)` in the case that `ω_X` is invertible", the formula being that
`-½ c₁(ω_X) ∩ [X]_1` has degree `χ(X, 𝒪_X)`. Here `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` is the module
of [Stacks, Tag 0BS2], `Stacks.Duality.dualizingSheafOverField`, and "`ω_X` invertible" is the
instance argument that it is finite locally free of rank one, which is what `c₁(ω_X)` and
`deg(ω_X)` need to be terms at all. Lemma [Stacks, Tag 0BS5] is used in its second form, so the
hypotheses are those of that form: `X` Cohen--Macaulay and equidimensional of dimension one. The
proof is the section's: [Stacks, Tag 0BS3] gives `ω_X^• ≅ ω_X[1]`
(`Stacks.Duality.dualizingSheafShiftOneIsoOfIsCohenMacaulay`), which turns the first formula of
[Stacks, Tag 0BS5] into its second, `χ(X, 𝒪_X) = -χ(X, ω_X)`
(`AlgebraicGeometry.eulerCharacteristic_unit_eq_neg_eulerCharacteristic_dualizingSheafOverField`);
the degree formula [Stacks, Tag 0BRX] then gives `deg(ω_X) = χ(X, ω_X) - χ(X, 𝒪_X) = -2 χ(X, 𝒪_X)`,
and [Stacks, Tag 0BRY] identifies `deg(ω_X)` with `deg(c₁(ω_X) ∩ [X]_1)`. Neither the condition
`H⁰(X, 𝒪_X) = k` of Situation [Stacks, Tag 0B5D] nor any Gorenstein hypothesis is used.

The section glosses "`ω_X` invertible" as "`X` is Gorenstein". The direction "Gorenstein and
equidimensional of dimension one implies `ω_X` invertible" is clause (1) of [Stacks, Tag 0BS6],
which carries that tag; combined with that clause, the statement here is clause (2) of
[Stacks, Tag 0BS6].

The half-integer zero cycle `-½ c₁(ω_X) ∩ [X]_1` is a cycle with
rational coefficients; its degree is `-½` times the degree of the integral cycle
`c₁(ω_X) ∩ [X]_1`, which is how it is written.

## References

* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
* [Stacks Project, Tag 0BEY](https://stacks.math.columbia.edu/tag/0BEY)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The degree of an invertible module is unchanged by pulling back along the identity.** The
degree of [Stacks, Tag 0AYR] of `(𝟙 X)^* 𝓛`, computed over `𝟙 X ≫ f`, is the degree of `𝓛`
computed over `f`: the structure morphisms agree and `(𝟙 X)^* 𝓛 ≅ 𝓛`. -/
theorem invertibleCurveDegree_comp_pullback_id (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    invertibleCurveDegree k (𝟙 X ≫ f) hdim ((Scheme.Modules.pullback (𝟙 X)).obj L) =
      invertibleCurveDegree k f hdim L := by
  have key : ∀ (g : X ⟶ Spec (.of k)) [IsProper g], g = f →
      invertibleCurveDegree k g hdim ((Scheme.Modules.pullback (𝟙 X)).obj L) =
        invertibleCurveDegree k f hdim L := by
    rintro g _ rfl
    unfold invertibleCurveDegree
    congr 1
    exact finsum_congr fun n => by
      rw [finrank_cohomologyOverField_eq_of_iso k g ((Scheme.Modules.pullbackId X).app L) n]
      rfl
  exact key _ (Category.id_comp f)

/-- **"If `𝓛` is ample, then this integer is positive"** (Section [Stacks, Tag 0B5B]): on a
proper scheme `X` of dimension one over a field `k`, an ample invertible `𝒪_X`-module `𝓛` has
positive numerical intersection number `(𝓛 · X)` ([Stacks, Tag 0BEP], at the closed subscheme
`X ⊆ X`) and positive degree `deg(𝓛)` ([Stacks, Tag 0AYR]).

The section states this under its standing hypothesis `dim X ≤ 1`; at dimension zero it is false
(`X = Spec k`, `𝓛 = 𝒪_X`, where both integers are `0`), so the hypothesis here is `dim X = 1`,
the dimension at which the section's name `deg_𝓛(X) = (𝓛 · X)` for this integer
([Stacks, Tag 0BEW]) applies. See the module documentation. -/
@[stacks 0B5B "the section's positivity claim: if L is ample then the integer (L . X) = deg(L) is \
positive. Stated for dim X = 1: under the section's standing dim X <= 1 the claim fails at \
dimension zero (X = Spec k, L = O_X ample, deg(O_X) = chi(O_X) - chi(O_X) = 0 = (O_X . X)), and \
dim X = 1 is the dimension at which the section's name deg_L(X) = (L . X) (Tag 0BEW) applies"]
theorem selfIntersectionNumber_pos_and_invertibleCurveDegree_pos_of_isAmple
    (hdim : topologicalKrullDim X = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < selfIntersectionNumber k f (𝟙 X) 1 hdim.le L ∧
      0 < invertibleCurveDegree k f hdim.le L := by
  have h : 0 < selfIntersectionNumber k f (𝟙 X) 1 hdim.le L :=
    selfIntersectionNumber_pos k f (𝟙 X) 1 (by rw [hdim]; rfl) L hL
  refine ⟨h, ?_⟩
  have e := intersectionNumber_one_eq_invertibleCurveDegree k f (𝟙 X) hdim.le L
  rw [invertibleCurveDegree_comp_pullback_id] at e
  rw [← e]
  exact h

/-- **The Riemann--Roch claim of Section [Stacks, Tag 0B5B]**: let `X` be a proper scheme over a
field `k`, Cohen--Macaulay and equidimensional of dimension one, and let
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the module of [Stacks, Tag 0BS2]. If `ω_X` is invertible, then

* `deg(ω_X) = -2 χ(X, 𝒪_X)`, with `deg` the degree of [Stacks, Tag 0AYR], and
* the zero cycle `-½ c₁(ω_X) ∩ [X]_1` has degree `χ(X, 𝒪_X)`.

This is what the section obtains from Lemma [Stacks, Tag 0BS5] "in the case that `ω_X` is
invertible". The proof is the section's: `χ(X, 𝒪_X) = -χ(X, ω_X)` by [Stacks, Tag 0BS5] at
`ω_X^• = ω_X[1]` ([Stacks, Tag 0BS3]), then [Stacks, Tag 0BRX] and [Stacks, Tag 0BRY]. Nothing
beyond the stated hypotheses is used; in particular not `H⁰(X, 𝒪_X) = k`. See the module
documentation. -/
@[stacks 0B5B "the section's Riemann-Roch claim: in the case that omega_X is invertible, \
-1/2 c_1(omega_X) cap [X]_1 is a zero cycle (with half-integer coefficients) whose degree is \
chi(X, O_X), together with deg(omega_X) = -2 chi(X, O_X); obtained, as the section says, from \
Tag 0BS5 (at omega^bullet = omega[1], Tag 0BS3), whose hypotheses X Cohen-Macaulay and \
equidimensional of dimension 1 it keeps. omega_X invertible is the instance that the module of \
Tag 0BS2 is finite locally free of rank 1. The section's gloss 'omega_X invertible, i.e., X \
Gorenstein' is clause (1) of Tag 0BS6"]
theorem curveDegree_dualizingSheafOverField_eq_neg_two_mul_and_chowDegree
    (hcm : IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Duality.dualizingSheafOverField f) 1] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : (Stacks.Ample.unitModule X).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
    curveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) 1 =
        -2 * eulerCharacteristic k f (Stacks.Ample.unitModule X) ∧
      (-(1 / 2 : ℚ)) *
          (chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
            (IsLocalRing.closedPoint k)
            (chowGroupCast (fieldChowSituation k) f (show (1 : ℤ) - 1 = 0 by simp)
              (GenuineChern.firstChernCapOnCycles (fieldChowSituation k) f
                (Stacks.Duality.dualizingSheafOverField f) 1 1
                (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (𝟙 X) 1))) : ℚ) =
        (eulerCharacteristic k f (Stacks.Ample.unitModule X) : ℚ) := by
  have hχ := eulerCharacteristic_unit_eq_neg_eulerCharacteristic_dualizingSheafOverField f hcm
    hequi hdim
  unfold eulerCharacteristic at hχ ⊢
  have hχ' : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ)) =
      -∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) n) : ℤ) := hχ
  have hdeg : curveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) 1 =
      -2 * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ)) := by
    unfold curveDegree
    rw [Nat.cast_one, one_mul]
    linarith
  refine ⟨hdeg, ?_⟩
  rw [← curveDegree_eq_chowDegree_firstChernCapOnCycles_fundamental k f hdim.le, hdeg]
  push_cast
  ring

end AlgebraicGeometry

end
