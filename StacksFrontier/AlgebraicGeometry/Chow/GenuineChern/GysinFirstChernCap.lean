module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinKeyFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications

/-!
# Gysin pullback commutes with the first Chern class of an invertible module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `(ℒ, s, i : D ⟶ X)` be a triple as in Definition 02T8 and let `𝒩` be an
invertible `𝒪_X`-module. Stacks 0B72 asserts

  `i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α`  in  `A_{k-2}(D)`,  for every `α ∈ A_k(X)`.

## Main results

* `Stacks.Chow.GenuineChern.properChowPushforward_gysinChowOfInvertible` — for the zero scheme
  `j : Z(t) ⟶ X` of a global section `t` of an invertible module `ℳ`, `j_* j^* β = c₁(ℳ) ∩ β` on
  Chow groups.
* `Stacks.Chow.GenuineChern.gysinChowOfInvertible_firstChernClassCapChow` — Gysin pullback
  commutes with capping with the first Chern class: `i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α`.

## References

* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- For an invertible module `ℳ` with a global section `t` and zero scheme `j : Z(t) ⟶ X`, pushing
the Gysin class `j^*β` forward along `j` gives `c₁(ℳ) ∩ β`. -/
theorem properChowPushforward_gysinChowOfInvertible (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (t : Γ(M, ⊤))
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme X M t).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X M t).subschemeι rfl k)
    (β : chowGroup C p (k + 1)) :
    properChowPushforward C ((Stacks.Divisors.zeroScheme X M t).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X M t).subschemeι rfl k hfac
        (gysinChowOfInvertible C p k M t β) =
      firstChernClassCapChow C k p M β := by
  induction β using QuotientAddGroup.induction_on with
  | H b =>
    change properChowPushforward C ((Stacks.Divisors.zeroScheme X M t).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X M t).subschemeι rfl k hfac
        (gysinHomomorphismOfInvertible C p k M t b) = firstChernClassCapOfInvertible C p k M b
    exact properChowPushforward_gysinHomomorphismOfInvertible C p k M t b

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- Let `ℒ` be an invertible module on `X` with a global section `s` and zero scheme
`i : D = Z(s) ⟶ X`, and let `𝒩` be an invertible module on `X`. Then Gysin pullback along `i`
commutes with capping with the first Chern class of `𝒩`:

  `i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α`  in  `A_k(D)`,  for every `α ∈ A_{k+2}(X)`. -/
@[stacks 0B72 "the identity i^* (c_1(N) cap a) = c_1(i^* N) cap i^* a on Chow groups, for every \
class a, stated for the descended operations of Stacks 02TO and 02TI that the library proves \
outright (`gysinChowOfInvertible`, `firstChernClassCapChow`); nothing about the Gysin map, the \
cap product or their descent is left over. The source proves the tag with the proof of Stacks \
0B73 through Stacks 02TM on the integral components; here it is deduced from Stacks 0B73 itself \
for the pair `(L, s)` and the zero section of `N`, using Stacks 02T9 to read `j_* j^*` as the \
cap product and Stacks 02TA for the pushforward along `Z(0) = X ⟶ X`"]
theorem gysinChowOfInvertible_firstChernClassCapChow (α : chowGroup C p (k + 1 + 1)) :
    gysinChowOfInvertible C p k L s (firstChernClassCapChow C (k + 1) p N α) =
      firstChernClassCapChow C k ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj N)
        (gysinChowOfInvertible C p (k + 1) L s α) := by
  obtain ⟨e, he⟩ := exists_iso_zeroSchemeInter L N s 0
  let D := Stacks.Divisors.zeroScheme X L s
  let E := Stacks.Divisors.zeroScheme X N (0 : Γ(N, ⊤))
  let ZD := zeroSchemeInter L N s 0
  let ZE := zeroSchemeInter N L 0 s
  set j : ZE.subscheme ⟶ D.subscheme := e.inv ≫ ZD.subschemeι with hjdef
  have hj : j ≫ D.subschemeι = ZE.subschemeι ≫ E.subschemeι := by
    rw [hjdef, Category.assoc, ← he, Iso.inv_hom_id_assoc]
  have hjp : j ≫ (D.subschemeι ≫ p) = ZE.subschemeι ≫ E.subschemeι ≫ p := by
    rw [← Category.assoc, hj, Category.assoc]
  have hej : e.hom ≫ j = ZD.subschemeι := by rw [hjdef, Iso.hom_inv_id_assoc]
  rw [← properChowPushforward_gysinChowOfInvertible C p (k + 1) N 0
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)]
  rw [show gysinChowOfInvertible C p k L s = (gysinSystemOfInvertible C).onChow p L s k from rfl,
    gysinSystemOfInvertible_isNaturalUnderProperPushforward C (E.subschemeι ≫ p) p E.subschemeι rfl
      L s k j hj (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)]
  have h0B73 := gysinChowOfInvertible_comm C p k L N s 0 e he α
  change properChowPushforward C (ZE.subschemeι ≫ E.subschemeι ≫ p) (D.subschemeι ≫ p) j hjp k _
      (gysinChowOfInvertible C (E.subschemeι ≫ p) k _ _
        (gysinChowOfInvertible C p (k + 1) N 0 α)) = _
  rw [← h0B73, chowPushforwardOfIso, ← properChowPushforward_comp_apply C
    (ZD.subschemeι ≫ D.subschemeι ≫ p) (ZE.subschemeι ≫ E.subschemeι ≫ p) (D.subschemeι ≫ p)
    e.hom j ZD.subschemeι hej _ hjp rfl k _ _
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)]
  exact properChowPushforward_gysinChowOfInvertible C (D.subschemeι ≫ p) k _ _ _ _

end Stacks.Chow.GenuineChern

end
