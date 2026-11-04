module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity

/-!
# Pulling a divisor cycle back to an effective Cartier divisor

Let `X` be an integral scheme locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, of delta-dimension `n = k + 2`, let `i : D ⟶ X` be an effective Cartier divisor,
and let `N` be an invertible module on `X` with a nonzero meromorphic section `t`. Stacks 02TM
asserts

  `i^* div_N(t) = c₁(N|_D) ∩ [D]_{n-1}`  in  `A_{n-2}(D)`.

That identity is proved here from the rational equivalence that the key formula of Stacks 0AYC
exhibits on `D`, both sides being computed on the presentations of `div_N(t)` and of `[D]_{n-1}`
by the locally finite component formulas of Stacks 02T8 and 02SO.

Pushing the identity forward along the closed immersion `i` and reading the right hand side on `X`
through Stacks 02SU turns it into

  `D · div_N(t) = c₁(N) ∩ [D]_{n-1}`  in  `A_{n-2}(X)`,

with `D · −` the intersection `i_* i^*` with the divisor. In that form it rests on the key formula
on `X` alone: the left hand side is capping with `c₁(𝒪_X(D))` by Stacks 02T9, and
`[D]_{n-1} = div_{𝒪_X(D)}(1_D)`, so the identity becomes the commutativity of Stacks 02TH for the
pair `(𝒪_X(D), N)` with their sections `1_D` and `t`.

## Main definitions

* `Stacks.Chow.KeyFormulaRationalEquivalenceOnDivisor` — the rational equivalence of Stacks 0AYC
  read on `D`: the two cycles on `D` representing the two sides of Stacks 02TM differ by a cycle
  rationally equivalent to zero on `D`.

## Main results

* `Stacks.Chow.effectiveCartierIntersection_eq_firstChernClassCap_of_keyFormula` — **Stacks 02TM**
  after pushforward along `i`, granting the key formula of Stacks 0AYC.
* `Stacks.Chow.gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible_of_keyFormula` —
  **Stacks 02TM** with the conclusion the source states, an identity in `A_{n-2}(D)`, granting
  the rational equivalence of Stacks 0AYC on `D`.

## Implementation notes

### The two forms of the conclusion

The source states the identity in `A_{n-2}(D)`, and that is the form of
`Stacks.Chow.gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible_of_keyFormula`: the
left hand side is the Gysin pullback of Stacks 02T8 along `i`, which already takes its values on
`D`, and the right hand side is the cap product of Stacks 02SO with the restriction `N|_D`
applied to the fundamental cycle `[D]_{n-1}` of `D` read as a cycle on `D`. Pushing the identity
forward along `i` and reading the right hand side on `X` through Stacks 02SU gives the form of
`Stacks.Chow.effectiveCartierIntersection_eq_firstChernClassCap_of_keyFormula`; since `i_*` is
not injective on Chow groups, the two are different statements and both are recorded.

### What the two forms grant

The identity on `X` is the commutativity of Stacks 02TH, so it follows from the key formula of
Stacks 0AYC as that formula is recorded here, namely
`Stacks.Chow.KeyFormulaData.KeyFormula`, an equality of cycles on `X`.

The identity on `D` needs the rational equivalence that the key formula exhibits to live on `D`:
the terms `div_{Z_i}(∂_{B_i}(f_i, g_i))` with `Z_i ⊄ D` drop out because there `f_i = 1`, so the
surviving terms are supported on the irreducible components of `D` and give a rational
equivalence on `D`. That refinement cannot be read off `Stacks.Chow.KeyFormulaData.KeyFormula`:
the data record their cycles and tame symbols on the subschemes `Z_i` of `X`, and factoring the
pushforward of a term through `D` would need `(Z_i).comap i` identified with `Z_i` together with
the transport of the rational functions of `Z_i` along that isomorphism. So the `D`-form takes
the rational equivalence on `D` as the explicit hypothesis
`Stacks.Chow.KeyFormulaRationalEquivalenceOnDivisor`, which is the last step of the source's
proof, and derives from it the identity of the source by computing both sides on the given
presentations through the component formulas of Stacks 02T8 and 02SO.

### The parameters threaded, and why

The source's data are carried as explicit parameters, in the way established by
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity`. For the form on `X` these are:

* the key formula `Stacks.Chow.KeyFormulaData.KeyFormula` of Stacks 0AYC, which is a statement
  rather than a theorem here;
* the component rule `chernN` of the cap product of `N`, standing in for Stacks 02SO, whose
  component input is the divisor cycle of Stacks 02SJ;
* the cycles `[D]_{n-1}` and `div_N(t)` together with their presentations
  `∑_i ord_{B_i}(f_i) [Z_i]` and `∑_i ord_{B_i}(g_i) [Z_i]` by the family of the key formula,
  which is the second step of the source's proof;
* the hypotheses `hchernE` and `hchernN` identifying the two component rules on the `Z_i` with the
  restricted divisors `div_{𝒪_X(D)|Z_i}(s_i|Z_i)` and `div_{N|Z_i}(t_i|Z_i)` of the key formula
  data, which is the source's choice of generators `s_i` and `t_i` at the generic points `ξ_i` and
  the third step of its proof.

The component rule of `𝒪_X(D)` is *not* a parameter: it is
`Stacks.Chow.firstChernComponentCycleRule` at `Stacks.Divisors.divisorSheaf`, which is also the
rule through which Stacks 02T9 identifies intersection with `D`.

For the form on `D` the parameters are the two cycles `div_N(t)` and `[D]_{n-1}`, the latter now
on `D`, again with the presentations of the second step of the source's proof — the first by the
family `{Z_i}` of the key formula data and the second by a locally finite family of integral
closed subschemes of `D` of delta-dimension `n - 1` — together with the rational equivalence
`Stacks.Chow.KeyFormulaRationalEquivalenceOnDivisor`. No component rule is a parameter there:
`N|_D` is an invertible module on `D`, so its cap product is
`Stacks.Chow.firstChernClassCapOfInvertible`, and the Gysin pullback is that of `𝒪_X(D)` and its
canonical section, `Stacks.Chow.gysinHomomorphismOfInvertible`.

### The grading

The source states Stacks 02TM for `dim_δ(X) = n` with the conclusion in `CH_{n-2}(D)`. Here the
hypothesis reads `dim_δ(X) = k + 2` and the conclusion lands in `A_k(D)` — in `A_k(X)` for the
form pushed forward to `X` — which is the same statement with `k = n - 2`.

## References

* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] {k : ℤ}

/-- **Stacks 02TM, pushed forward to the ambient scheme.** Let `X` be integral of
delta-dimension `k + 2`, let `E` be an effective Cartier divisor on `X` and let `N` be an
invertible module with a nonzero meromorphic section `t`. Then intersecting `div_N(t)` with `E`
agrees with capping the fundamental cycle `[E]_{k+1}` with the first Chern class of `N`, in
`A_k(X)`.

This is the identity `i^* div_N(t) = c₁(N|_E) ∩ [E]_{k+1}` of the source after pushing forward
along the closed immersion `i : E ⟶ X`, the right hand side being read on `X` through Stacks 02SU;
see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapDivisor`.

Intersection with `E` is capping with `c₁(𝒪_X(E))` by Stacks 02T9, and the fundamental cycle
`[E]_{k+1}` is the divisor cycle of the canonical section `1_E` of `𝒪_X(E)`, presented by the
family `{Z_i}` of the key formula through `hfundamentalCycle`. So the identity is the
commutativity of Stacks 02TH for the pair `(𝒪_X(E), N)`. -/
@[stacks 02TM "after pushforward along E ⟶ X, granting the key formula 0AYC"]
theorem effectiveCartierIntersection_eq_firstChernClassCap_of_keyFormula
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (E : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor E] (D : KeyFormulaData X)
    (hKey : D.KeyFormula C p) (chernN : FirstChernComponentCycleRule C p k)
    (hchernE : ∀ (i : D.Index) (hW : IsIntegral (D.component i).subscheme)
      (hDim : schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      (firstChernComponentCycleRule C p k (Stacks.Divisors.divisorSheaf E)
        (D.component i) hW hDim).1 = D.restrictedDivisorL i)
    (hchernN : ∀ (i : D.Index) (hW : IsIntegral (D.component i).subscheme)
      (hDim : schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      (chernN (D.component i) hW hDim).1 = D.restrictedDivisorN i)
    (fundamentalCycle divN : CycleGroup C p (k + 1))
    (hfundamentalCycle : ∀ x : X, fundamentalCycle.1 x = ∑ᶠ i, D.orderL i *
      (cycleAssociatedToClosedSubscheme C p (D.component i).subschemeι (k + 1)).1 x)
    (hdivN : ∀ x : X, divN.1 x = ∑ᶠ i, D.orderN i *
      (cycleAssociatedToClosedSubscheme C p (D.component i).subschemeι (k + 1)).1 x) :
    effectiveCartierIntersectionOfInvertible C p k (Stacks.Divisors.divisorSheaf E)
        (Stacks.Divisors.divisorSheafGlobalSection E)
        (isEffectiveCartierDivisor_zeroScheme_divisorSheaf E) divN =
      firstChernClassCap C p k chernN fundamentalCycle := by
  rw [effectiveCartierIntersection_divisorSheaf_eq_firstChernClassCapOfInvertible C p k E divN]
  exact (firstChernClassCap_comm_of_keyFormula C p hn D hKey
    (firstChernComponentCycleRule C p k (Stacks.Divisors.divisorSheaf E)) chernN hchernE hchernN
    fundamentalCycle divN hfundamentalCycle hdivN).symm

/-! ### Stacks 02TM on the divisor -/

/-- **The rational equivalence of the key formula, read on the divisor.** Let `E` be an effective
Cartier divisor on the integral scheme `X` of delta-dimension `k + 2`, let `i : E ⟶ X` be its
closed immersion, let `N` be an invertible module on `X` and let `{Z_i}` be the family of prime
divisors of the key formula data `D`, with `ord_{B_i}(g_i)` the orders of vanishing of the
meromorphic section of `N` along them. Let `{V_j}` be a locally finite family of integral closed
subschemes of `E` of delta-dimension `k + 1` and `m_j` integers, presenting the fundamental cycle
`[E]_{k+1}` of `E` as a cycle on `E`.

The assertion is that a `k`-cycle on `E` whose coefficients are those of
`∑_i ord_{B_i}(g_i) · i^*[Z_i]`, and a `k`-cycle on `E` whose coefficients are those of
`∑_j m_j · c₁(N|_E) ∩ [V_j]`, differ by a cycle rationally equivalent to zero on `E`.

These two cycles represent the two sides of Stacks 02TM, by the locally finite component formula
of Stacks 02T8 for the Gysin pullback and that of Stacks 02SO for the cap product. In the source
their difference is exhibited as `∑_i div_{Z_i}(∂_{B_i}(f_i, g_i))` by the key formula of Stacks
0AYC, in which the terms with `Z_i ⊄ E` vanish because the chosen generator of `𝒪_X(E)` at the
generic point of such a `Z_i` is the canonical section itself, so that `f_i = 1`; the surviving
terms are supported on the irreducible components of `E`, and so give a rational equivalence on
`E` rather than only on `X`. That last step is what this assertion records; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapDivisor`. -/
def KeyFormulaRationalEquivalenceOnDivisor
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (E : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor E] (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (D : KeyFormulaData X) {J : Type u}
    (V : J → (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subscheme.IdealSheafData)
    (hV : ∀ j, IsIntegral (V j).subscheme)
    (hVdim : ∀ j, schemeDeltaDimension C ((V j).subschemeι ≫
        (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
          (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt))
    (m : J → ℤ) : Prop :=
  ∀ u v : CycleGroup C ((Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) k,
    (∀ z : (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subscheme,
      u.1 z = ∑ᶠ i : D.Index, D.orderN i *
        (gysinComponentCycle C p k (Stacks.Divisors.divisorSheaf E)
          (Stacks.Divisors.divisorSheafGlobalSection E)
          (firstChernComponentClass C p k (Stacks.Divisors.divisorSheaf E)) (D.component i)
          (D.isIntegral_component i)
          (D.schemeDeltaDimension_component_add_one C p hn i)).1 z) →
    (∀ z : (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subscheme,
      v.1 z = ∑ᶠ j : J, m j *
        (firstChernComponentCycle C ((Stacks.Divisors.zeroScheme X
            (Stacks.Divisors.divisorSheaf E)
            (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) k
          (firstChernComponentCycleRule C ((Stacks.Divisors.zeroScheme X
              (Stacks.Divisors.divisorSheaf E)
              (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) k
            ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X
              (Stacks.Divisors.divisorSheaf E)
              (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι).obj N))
          (V j) (hV j) (hVdim j)).1 z) →
    IsRationallyEquivalentToZero C ((Stacks.Divisors.zeroScheme X
      (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) k (u - v)

/-- **Stacks 02TM.** Let `X` be integral of delta-dimension `k + 2`, let `E` be an effective
Cartier divisor on `X` with closed immersion `i : E ⟶ X`, and let `N` be an invertible module on
`X` with a nonzero meromorphic section `t`. Then

`i^* div_N(t) = c₁(N|_E) ∩ [E]_{k+1}`  in  `A_k(E)`,

the identity of the source: the left hand side is the Gysin pullback of Stacks 02T8 along `i`,
which takes its values in the Chow group of `E`, and the right hand side is the cap product of
Stacks 02SO on `E` with the first Chern class of the restriction `N|_E`, applied to the
fundamental cycle of `E` read as a cycle on `E`.

The divisor cycle `div_N(t)` of Stacks 02SJ and the fundamental cycle `[E]_{k+1}` are explicit
parameters, each with the presentation the second step of the source's proof gives it: the first
by the family `{Z_i}` of prime divisors of the key formula data `D`, with the orders
`ord_{B_i}(g_i)`, and the second by a locally finite family `{V_j}` of integral closed subschemes
of `E` of delta-dimension `k + 1`, with multiplicities `m_j`. The remaining input is the rational
equivalence `Stacks.Chow.KeyFormulaRationalEquivalenceOnDivisor` on `E`, which is the last step
of the source's proof; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapDivisor`.

Given these, the two sides are computed on their presentations by the locally finite component
formulas of Stacks 02T8 and 02SO, and the rational equivalence identifies the resulting two
classes. -/
@[stacks 02TM "the identity i^* div_N(t) = c₁(N|_D) ∩ [D]_{n-1} in A_{n-2}(D), the conclusion \
of the source, granting the rational equivalence `KeyFormulaRationalEquivalenceOnDivisor` that \
the key formula 0AYC exhibits on D — the last step of the source's proof — together with the \
divisor cycle div_N(t) of 02SJ and the fundamental cycle [D]_{n-1} read on D, each with its \
presentation by a locally finite family of integral closed subschemes of delta-dimension n-1, \
which is the second step of the source's proof"]
theorem gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible_of_keyFormula
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (E : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor E] (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (D : KeyFormulaData X) {J : Type u}
    (V : J → (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subscheme.IdealSheafData)
    (hV : ∀ j, IsIntegral (V j).subscheme)
    (hVdim : ∀ j, schemeDeltaDimension C ((V j).subschemeι ≫
        (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
          (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt))
    (hVlocal : LocallyFinite fun j ↦ ((V j).support :
      Set (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
        (Stacks.Divisors.divisorSheafGlobalSection E)).subscheme))
    (m : J → ℤ)
    (hKeyOnDivisor : KeyFormulaRationalEquivalenceOnDivisor C p hn E N D V hV hVdim m)
    (divN : CycleGroup C p (k + 1))
    (hdivN : ∀ x : X, divN.1 x = ∑ᶠ i, D.orderN i *
      (cycleAssociatedToClosedSubscheme C p (D.component i).subschemeι (k + 1)).1 x)
    (fundamentalCycle : CycleGroup C ((Stacks.Divisors.zeroScheme X
      (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) (k + 1))
    (hfundamentalCycle : ∀ z : (Stacks.Divisors.zeroScheme X
      (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subscheme,
      fundamentalCycle.1 z = ∑ᶠ j, m j *
        (cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme X
            (Stacks.Divisors.divisorSheaf E)
            (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p)
          (V j).subschemeι (k + 1)).1 z) :
    gysinHomomorphismOfInvertible C p k (Stacks.Divisors.divisorSheaf E)
        (Stacks.Divisors.divisorSheafGlobalSection E) divN =
      firstChernClassCapOfInvertible C ((Stacks.Divisors.zeroScheme X
          (Stacks.Divisors.divisorSheaf E)
          (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X
          (Stacks.Divisors.divisorSheaf E)
          (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι).obj N)
        fundamentalCycle := by
  obtain ⟨β, hβ, hβcoeff⟩ := gysinHomomorphismOfInvertible_finsum C p k
    (Stacks.Divisors.divisorSheaf E) (Stacks.Divisors.divisorSheafGlobalSection E)
    D.component D.isIntegral_component (D.schemeDeltaDimension_component_add_one C p hn)
    D.locallyFinite_support_component D.orderN divN hdivN
  obtain ⟨γ, hγ, hγcoeff⟩ := firstChernClassCapOfInvertible_finsum C
    ((Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι ≫ p) k
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X
      (Stacks.Divisors.divisorSheaf E)
      (Stacks.Divisors.divisorSheafGlobalSection E)).subschemeι).obj N)
    V hV hVdim hVlocal m fundamentalCycle hfundamentalCycle
  rw [hβ, hγ]
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (hKeyOnDivisor β γ hβcoeff hγcoeff)

end Stacks.Chow

end
