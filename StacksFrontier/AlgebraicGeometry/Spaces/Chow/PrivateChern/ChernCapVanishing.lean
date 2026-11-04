module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassDualTensorOfProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FilteredTotalChernClass

/-!
# Vanishing of the Chern classes above the rank

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r`. The Chern classes `c_n(ℰ)` of `AlgebraicGeometry.Space.PrivateChern.chernCap` are the
coefficients of the inverse of the Segre series of `ℰ`, defined for every `n`; Stacks 0ERZ sets
`c_n(ℰ) = 0` for `n > r`, and the two agree: `c_n(ℰ) = 0` for `n > r`.

The proof is the splitting principle (Stacks 0ESC). Along a splitting `π : P ⟶ X` the module
`π^*ℰ` has a filtration of length `r` with invertible successive quotients `ℒ_1, …, ℒ_r`, so by
Stacks 0ES8 and induction (Stacks 0ESA) `∑_n c_n(π^*ℰ) X^n = ∏_{i=1}^r (1 + c_1(ℒ_i) X)`, a
polynomial of degree at most `r`. Since `π^* : CH_*(X) ⟶ CH_*(P)` is injective and intertwines
`c_n(ℰ)` with `c_n(π^*ℰ)`, `c_n(ℰ) = 0` for `n > r`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_eq_zero_of_lt_of_hasFiltrationOfLength`: the
  Chern classes of a module with a filtration of length `r` by invertible quotients vanish above
  `r`, granted Stacks 0ES8.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings`:
  the Chern classes of a module of rank `r` vanish above `r`, granted Stacks 0ES8 and splittings
  with an injective intertwining map.

## References

* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **Chern classes of a filtered module vanish above the length of the filtration**, granted
Stacks 0ES8 degree by degree: if `ℰ` on a good `P` has a filtration of length `r` with invertible
successive quotients then `c_n(ℰ) = 0` for `n > r`. -/
theorem chernCap_eq_zero_of_lt_of_hasFiltrationOfLength {P : D.Ambient} {sP : P ⟶ D.space}
    {hP : D.IsGood sP}
    (h8 : ∀ (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hP) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sP hP T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sP hP T.X₃ r) (n : ℕ),
      chernCap.{u, v} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, v} T.X₃ r h₃ (n + 1) +
          chernCap.{u, v} T.X₁ 1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
            (goodSpace hP) h₁) 1 * chernCap.{u, v} T.X₃ r h₃ n)
    {r : ℕ} {E : Modules.{u, u} D.site D.base D.base_mem P hP.1}
    (hE : (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength r E)
    (h : IsFiniteLocallyFreeOfRank D sP hP E r) {n : ℕ} (hn : r < n) :
    chernCap.{u, v} E r h n = 0 := by
  have := isClosedUnderIsomorphisms_invertibleModules D.site D.base D.base_mem (goodSpace hP)
  obtain ⟨F, hF, h0, htop, hq⟩ := hE.exists_subobject
  have hmk := mk_chernCap_eq_prod_of_filtration
    (fun L hL => chernCap.{u, v} L 1
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) hL) 1) h8 E h
    _ hq F hF h0 htop (fun _ => Iso.refl _)
  have hc := congrArg (PowerSeries.coeff n) hmk
  rw [PowerSeries.coeff_mk] at hc
  have key : ∀ xs : Fin r → AddMonoid.End (chowHomology.{u, v} D sP hP),
      PowerSeries.coeff n (List.ofFn fun i => 1 + PowerSeries.C (xs i) * PowerSeries.X).prod =
        0 := fun xs => by
    have := PowerSeries.coeff_list_prod_one_add_C_mul_X_of_length_lt (List.ofFn xs)
      (n := n) (by simpa using hn)
    rw [List.map_ofFn] at this
    exact this
  exact hc.trans (key _)

/-- **The Chern classes vanish above the rank**, granted Stacks 0ES8 degree by degree on every
good algebraic space and splittings with an injective map of Chow homologies intertwining the
Chern classes (the splitting principle, Stacks 0ESC, with the compatibility of the Chern classes
with flat pullback): for `ℰ` finite locally free of rank `r` on a good `X`, `c_n(ℰ) = 0` for
`n > r`. -/
theorem chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings
    (h8 : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP) (r : ℕ)
      (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hP) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sP hP T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sP hP T.X₃ r) (n : ℕ),
      chernCap.{u, v} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, v} T.X₃ r h₃ (n + 1) +
          chernCap.{u, v} T.X₁ 1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
            (goodSpace hP) h₁) 1 * chernCap.{u, v} T.X₃ r h₃ n)
    (hS : HasIntertwiningSplittings.{u, v} D)
    {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank D sX hX E r) {n : ℕ} (hn : r < n) :
    chernCap.{u, v} E r h n = 0 := by
  obtain ⟨P, sP, hP, π, g, hg, hfil, -, hnat⟩ := hS hX E E r r h h
  have hrP := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfil
  have hz := chernCap_eq_zero_of_lt_of_hasFiltrationOfLength.{u, v} (h8 hP) hfil hrP hn
  refine AddMonoidHom.ext fun α => hg ((hnat E r h hrP n α).symm.trans ?_)
  rw [hz]
  exact (map_zero g).symm

end AlgebraicGeometry.Space.PrivateChern

end
