module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalChernWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ConstantRankComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The power sums of the Chern classes add in a short exact sequence: Stacks 0F9C

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let

  `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0`

be a short exact sequence of **finite locally free** `𝒪_X`-modules — no constancy of the ranks
is assumed, as the source assumes none.
[Stacks, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C) is

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`  in  `A^p(X)`

for every `p`, where `P_p` is the universal power-sum polynomial of
[Stacks, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B) evaluated at the Chern classes, and
dividing by `p!` it is the additivity `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)` of the Chern character.

## Where the identity lives

`A^p(X)` is `Stacks.Chow.chowCohomologyComponent` at the Gysin system of the first Chern class of
an invertible module, and `A^*(X) = ∏_{q ≥ 0} A^q(X)` is the **ring**
`Stacks.Chow.TotalChowClass`: it has `Stacks.Chow.TotalChowClass.instRing`, whose product is the
Cauchy product of the compositions `A^i(X) × A^j(X) ⟶ A^{i+j}(X)` of [Stacks, Tag 0B75]. So a
polynomial in the Chern classes of a module *is* a bivariant class here, and the identity is
stated where the source states it. The Chern classes themselves are the bivariant classes
`Stacks.Chow.GenuineChern.chernClass` of [Stacks, Tag 0B7H], assembled into the total Chern class
`Stacks.Chow.totalChern`.

`P_p` is Newton's recursion of Stacks 0F9B, `AlgebraicGeometry.newtonPowerSum`, applied to the
homogeneous components of the total Chern class with the rank as its degree-zero term; for a
module of constant rank that is `Stacks.Chow.modulePowerSum`, and `P_0(ℰ)` is the rank, as in the
source's recursion.

## The rank is not assumed constant

Ranks of finite locally free modules are locally constant, so `X` decomposes into the open and
closed loci `X_r` where the rank of `ℰ` is `r` (`Stacks.Chow.rankLocus`,
`Stacks.Chow.isClopenDecomposition_rankLociFamily`), and [Stacks, Tag 0FDZ] identifies
`A^*(X)` with `∏_r A^*(X_r)`. `Stacks.Chow.modulePowerSumArbitraryRank` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSum` is the class whose
component on `X_r` is the constant-rank power sum of `ℰ|_{X_r}`, and
`Stacks.Chow.res_modulePowerSumArbitraryRank_of_constantRank` there says that its restriction
along *any* morphism along which the rank becomes constant is the constant-rank power sum there,
which is the characterization everything below is read through. The additivity is then
read on a decomposition refining the rank decompositions of `ℰ₁` and of `ℰ₂`: on a piece of it
both have constant ranks `a` and `c`, the pulled-back sequence is still short exact
(`AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree`, no flatness
needed) and the middle term has constant rank `a + c`, so the constant-rank identity applies.

## The constant-rank identity

For constant ranks the identity is Newton's recursion applied to the Whitney sum formula. The two
inputs are

* the **Whitney sum formula**, [Stacks, Tag 02UI], on total classes:
  `Stacks.Chow.totalChern_shortExact`, `c(ℰ) = c(ℰ₁) c(ℰ₂)` in `A^*(X)`;
* the **commutativity of Chern classes**, the displayed identity of [Stacks, Tag 02UA], on total
  classes: `Stacks.Chow.commute_homComponent_totalChern`.

Granted those, `Stacks.Chow.TotalChowClass.newtonPowerSum_mul_of_commute_homComponent` is
Newton's identities read as the single equation `c · ν(c) = D(c)`, and gives
`P_p(ab) = P_p(a) + P_p(b)` with the degree-zero terms adding — which is `r₁ + r₂ = r₁ + r₂` for
the ranks. The splitting principle of the source is not redone: it enters only through the two
results of the chapter above, both already available with no extra hypotheses.

## Main definitions

* `Stacks.Chow.moduleChernCharacterComponent`, `Stacks.Chow.moduleChernCharacter` — the component
  `ch_p(ℰ) = P_p(ℰ)/p! ∈ A^p(X) ⊗ 𝐐` and the Chern character
  `ch(ℰ) ∈ ∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`, the home [Stacks, Tag 0ESX] gives it.

`P_p(ℰ) ∈ A^*(X)` itself and its degree-`p` component `P_p(ℰ) ∈ A^p(X)` are
`Stacks.Chow.modulePowerSumArbitraryRank` and
`Stacks.Chow.modulePowerSumComponentArbitraryRank` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSum`.

## Main results

* `Stacks.Chow.modulePowerSum_eq_add_of_shortExact` — the identity for modules of constant rank,
  in `A^*(X)`.
* `Stacks.Chow.modulePowerSumComponentArbitraryRank_eq_add_of_shortExact` — **Stacks 0F9C**,
  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)` in `A^p(X)`.
* `Stacks.Chow.moduleChernCharacter_eq_add_of_shortExact` — **Stacks 0F9C**, the headline
  equality `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)`.

## References

* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-! ### The constant-rank identity of Stacks 0F9C in `A^*(X)` -/

/-- **Stacks 0F9C for modules of constant rank, in the ring `A^*(X)`.** For a short exact
sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` with `ℰ₁` of rank `r₁` and `ℰ₂` of rank `r₂`,

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`

for every `p`, the rank of the middle term being `r₁ + r₂`. -/
theorem modulePowerSum_eq_add_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (r₁ r₂ : ℕ) (h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁)
    (h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂) (p : ℕ) :
    modulePowerSum C sX S.X₂ (r₁ + r₂)
        (GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r₁ r₂ h₁ h₃) p =
      modulePowerSum C sX S.X₁ r₁ h₁ p + modulePowerSum C sX S.X₃ r₂ h₃ p := by
  let := h₁
  let := h₃
  let := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r₁ r₂ h₁ h₃
  rw [modulePowerSum, modulePowerSum, modulePowerSum, totalChern_shortExact C sX S hS r₁ r₂]
  have hz : ((r₁ + r₂ : ℕ) : ℤ) • (1 : TotalChowClass C sX) =
      (r₁ : ℤ) • (1 : TotalChowClass C sX) + (r₂ : ℤ) • (1 : TotalChowClass C sX) := by
    rw [Nat.cast_add, add_zsmul]
  rw [hz]
  exact TotalChowClass.newtonPowerSum_mul_of_commute_homComponent
    (totalChern_apply_zero C sX S.X₁ r₁) (totalChern_apply_zero C sX S.X₃ r₂)
    (commute_homComponent_totalChern C sX S.X₁ S.X₃ r₁ r₂) _ _ p

/-! ### The Chern character of a module whose rank need not be constant -/

section ArbitraryRank

variable (E : X.Modules) [hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The component `ch_p(ℰ) = P_p(ℰ)/p! ∈ A^p(X) ⊗ 𝐐` of the Chern character** of a finite
locally free module whose rank need not be constant. -/
def moduleChernCharacterComponent (p : ℕ) :
    rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] modulePowerSumComponentArbitraryRank C sX E p

/-- **The Chern character `ch(ℰ) = (ch_0(ℰ), ch_1(ℰ), ch_2(ℰ), …)`** of a finite locally free
module whose rank need not be constant, as an element of the product `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`,
which is the home Stacks 0ESX gives it: the degree in which the Chern character is concentrated
is governed by the rank, which is unbounded in general. -/
def moduleChernCharacter : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX :=
  fun p ↦ moduleChernCharacterComponent C sX E p

/-- The degree-`p` entry of `ch(ℰ)` is `ch_p(ℰ)`. -/
theorem moduleChernCharacter_apply (p : ℕ) :
    moduleChernCharacter C sX E p = moduleChernCharacterComponent C sX E p :=
  rfl

end ArbitraryRank

/-! ### Stacks 0F9C -/

/-- Rank is preserved by pulling back along a composite when it is for the last factor. -/
private theorem isFiniteLocallyFreeOfRank_pullback_comp {W Y Z : Scheme.{u}} (g : W ⟶ Y)
    (f : Y ⟶ Z) (M : Z.Modules) (n : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ((Scheme.Modules.pullback f).obj M) n) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (g ≫ f)).obj M) n :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullbackComp g f).app M)
    (GenuineChern.isFiniteLocallyFreeOfRank_pullback g _ n)

section ShortExact

variable (S : ShortComplex X.Modules) (hS : S.ShortExact)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂]
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃]

include hS

/-- **The identity of Stacks 0F9C where both outer ranks become constant.** Along a morphism
`γ : Z ⟶ X` over which `γ^*ℰ₁` and `γ^*ℰ₂` have constant ranks `a` and `c`, the restrictions
along `γ` of the arbitrary-rank power sums satisfy `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`. -/
theorem res_modulePowerSumArbitraryRank_eq_add_of_shortExact {Z : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] (γ : Z ⟶ X) [LocallyOfFiniteType γ] (hs : γ ≫ sX = sZ) (a c : ℕ)
    (ha : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback γ).obj S.X₁) a)
    (hc : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback γ).obj S.X₃) c) (p : ℕ) :
    TotalChowClass.res γ hs (modulePowerSumArbitraryRank C sX S.X₂ p) =
      TotalChowClass.res γ hs (modulePowerSumArbitraryRank C sX S.X₁ p) +
        TotalChowClass.res γ hs (modulePowerSumArbitraryRank C sX S.X₃ p) := by
  have hSZ : (S.map (Scheme.Modules.pullback γ)).ShortExact :=
    Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree γ S hS
  rw [res_modulePowerSumArbitraryRank_of_constantRank C sX S.X₁ γ hs a ha p,
    res_modulePowerSumArbitraryRank_of_constantRank C sX S.X₃ γ hs c hc p,
    res_modulePowerSumArbitraryRank_of_constantRank C sX S.X₂ γ hs (a + c)
      (GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
        (S.map (Scheme.Modules.pullback γ)) hSZ a c ha hc) p]
  exact modulePowerSum_eq_add_of_shortExact C sZ (S.map (Scheme.Modules.pullback γ)) hSZ a c
    ha hc p

/-- **Stacks 0F9C in the ring `A^*(X)`.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules of not necessarily constant rank,

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`

for every `p`. -/
theorem modulePowerSumArbitraryRank_eq_add_of_shortExact (p : ℕ) :
    modulePowerSumArbitraryRank C sX S.X₂ p =
      modulePowerSumArbitraryRank C sX S.X₁ p + modulePowerSumArbitraryRank C sX S.X₃ p := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily S.X₁) fun i ↦ ?_
  refine TotalChowClass.eq_of_res_eq
    ((isClopenDecomposition_rankLociFamily S.X₃).preimage (rankLociFamily S.X₁ i).ι) fun j ↦ ?_
  have ha : ∀ t, (rankLociFamily S.X₁ i).ι ⁻¹ᵁ rankLociFamily S.X₃ t ≤
      (rankLociFamily S.X₁ i).ι ⁻¹ᵁ rankLociFamily S.X₃ (id t) := fun _ ↦ le_rfl
  have hfac : ((rankLociFamily S.X₁ i).ι ⁻¹ᵁ rankLociFamily S.X₃ j).ι ≫
        (rankLociFamily S.X₁ i).ι =
      pieceMap (rankLociFamily S.X₁ i).ι
          (fun t ↦ (rankLociFamily S.X₁ i).ι ⁻¹ᵁ rankLociFamily S.X₃ t)
          (rankLociFamily S.X₃) id ha j ≫
        (rankLociFamily S.X₃ j).ι :=
    (pieceMap_comp_ι _ _ _ id ha j).symm
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily S.X₁ i).ι).obj S.X₁) i.down :=
    isFiniteLocallyFreeOfRank_pullback_rankLocus S.X₁ i.down
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily S.X₃ j).ι).obj S.X₃) j.down :=
    isFiniteLocallyFreeOfRank_pullback_rankLocus S.X₃ j.down
  rw [map_add, map_add, TotalChowClass.res_res, TotalChowClass.res_res, TotalChowClass.res_res]
  refine res_modulePowerSumArbitraryRank_eq_add_of_shortExact C sX S hS _ _ i.down j.down ?_ ?_ p
  · exact isFiniteLocallyFreeOfRank_pullback_comp _ _ _ i.down inferInstance
  · rw [hfac]
    exact isFiniteLocallyFreeOfRank_pullback_comp _ _ _ j.down inferInstance

/-- Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules. Then for
every `p`

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`  in  `A^p(X)`,

where `P_p` is the universal power-sum polynomial of Stacks 0F9B evaluated at the Chern classes.
No constancy of the ranks is assumed. -/
@[stacks 0F9C "the source's more precise equality P_p(E) = P_p(E_1) + P_p(E_2), stated where the \
source states it: IN A^p(X), the degree-p Chow cohomology of Tag 0B7E at the Gysin system of the \
first Chern class of an invertible module (Stacks.Chow.chowCohomologyComponent).  A^*(X) = \
prod_{q >= 0} A^q(X) is the RING Stacks.Chow.TotalChowClass, whose product is the Cauchy product \
of the compositions A^i(X) x A^j(X) -> A^{i+j}(X) of Tag 0B75 \
(Stacks.Chow.TotalChowClass.instRing), so a polynomial in the Chern classes of a module is itself \
a bivariant class here; the Chern classes are the bivariant classes of Tag 0B7H, \
Stacks.Chow.GenuineChern.chernClass, assembled into Stacks.Chow.totalChern.  P_p is CONSTRUCTED, \
by the Newton recurrence of Tag 0F9B (AlgebraicGeometry.newtonPowerSum) applied to the \
homogeneous components of the total Chern class with the rank as degree-zero term, so P_0(E) is \
the rank as in the source's recursion.  THE RANKS ARE ARBITRARY, exactly as in the source: only \
that the three terms are finite locally free is assumed, no rank is named, and the rank of a \
finite locally free module is locally constant, so X is decomposed into the open and closed loci \
where each rank is constant (Stacks.Chow.rankLocus) and the class is assembled over them by Tag \
0FDZ as Stacks.Chow.modulePowerSumArbitraryRank; \
Stacks.Chow.res_modulePowerSumArbitraryRank_of_constantRank identifies its restriction along any \
morphism of \
constant rank with the constant-rank power sum there, and the identity is read on a decomposition \
refining the rank decompositions of E_1 and of E_2.  No filtration and no splitting of the \
sequence is supposed: the pulled-back sequence stays short exact with no flatness, a short exact \
sequence with finite locally free quotient being locally split.  The splitting principle of the \
source is used only through the two results of the chapter it proves, both available here with no \
extra hypotheses: Tag 02UI on total classes (Stacks.Chow.totalChern_shortExact) and the \
commutativity of Chern classes of Tag 02UA (Stacks.Chow.commute_homComponent_totalChern).  PROVED \
HERE: that those two give the additivity of every power sum, which is Newton's identities read as \
the single equation c . nu(c) = D(c) for the derivation D multiplying the index-m component by m"]
theorem modulePowerSumComponentArbitraryRank_eq_add_of_shortExact (p : ℕ) :
    modulePowerSumComponentArbitraryRank C sX S.X₂ p =
      modulePowerSumComponentArbitraryRank C sX S.X₁ p +
        modulePowerSumComponentArbitraryRank C sX S.X₃ p := by
  rw [modulePowerSumComponentArbitraryRank, modulePowerSumComponentArbitraryRank,
    modulePowerSumComponentArbitraryRank,
    modulePowerSumArbitraryRank_eq_add_of_shortExact C sX S hS p]
  rfl

/-- **Stacks 0F9C, the headline equality in each degree.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free `𝒪_X`-modules and every `p`,

  `ch_p(ℰ) = ch_p(ℰ₁) + ch_p(ℰ₂)`  in  `A^p(X) ⊗ 𝐐`. -/
theorem moduleChernCharacterComponent_eq_add_of_shortExact (p : ℕ) :
    moduleChernCharacterComponent C sX S.X₂ p =
      moduleChernCharacterComponent C sX S.X₁ p + moduleChernCharacterComponent C sX S.X₃ p := by
  rw [moduleChernCharacterComponent, moduleChernCharacterComponent,
    moduleChernCharacterComponent,
    modulePowerSumComponentArbitraryRank_eq_add_of_shortExact C sX S hS p,
    TensorProduct.tmul_add]

/-- Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules. Then

  `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)`.

Both sides lie in `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`, the rational Chow cohomology of `X` in which
Stacks 0ESX places the Chern character. -/
@[stacks 0F9C "the headline equality ch(E) = ch(E_1) + ch(E_2) for a short exact sequence \
0 -> E_1 -> E -> E_2 -> 0 of finite locally free O_X-modules over X locally of finite type over \
the base of Situation 02QL.  THE RANKS ARE ARBITRARY, exactly as in the source: only that the \
three terms are finite locally free is assumed and no rank is named.  ch_p(F) = P_p(F)/p! is \
Stacks.Chow.moduleChernCharacterComponent, an element of A^p(X) tensor Q \
(Stacks.Chow.rationalChowCohomologyComponent) where A^p(X) is the degree-p Chow cohomology of Tag \
0B7E -- the RATIONAL BIVARIANT group, not a ring of cap operators; the integral identity it is \
divided by holds in A^p(X) itself, in the bivariant ring A^*(X) = \
Stacks.Chow.TotalChowClass.  ch(F) itself is Stacks.Chow.moduleChernCharacter, the family \
(ch_0(F), ch_1(F), ...) in the product prod_{p >= 0} (A^p(X) tensor Q), which is the home Tag \
0ESX gives the Chern character, the degree in which it is concentrated being governed by a rank \
that is unbounded in general; addition there is degreewise, so an equality of two such families \
is an equality of Chern characters read in every degree at once, and \
Stacks.Chow.moduleChernCharacterComponent_eq_add_of_shortExact is that reading.  It is derived \
from the source's more precise equality, \
Stacks.Chow.modulePowerSumComponentArbitraryRank_eq_add_of_shortExact, by dividing by p!: the \
division of a sum by a scalar is term by term, so unlike Tag 0F9D no binomial coefficient \
intervenes.  The splitting principle is NOT redone here; it enters only through Tag 02UI on total \
classes (Stacks.Chow.totalChern_shortExact) and the commutativity of Chern classes of Tag 02UA"]
theorem moduleChernCharacter_eq_add_of_shortExact :
    moduleChernCharacter C sX S.X₂ =
      moduleChernCharacter C sX S.X₁ + moduleChernCharacter C sX S.X₃ := by
  funext p
  exact moduleChernCharacterComponent_eq_add_of_shortExact C sX S hS p

end ShortExact

end Stacks.Chow

end
