module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FilteredTotalChernClass

/-!
# The Whitney formula from filtrations with invertible quotients

In Situation 0EDT let `X/B` be good and let `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence of
finite locally free `𝒪_X`-modules. Record the Chern classes as the power series
`c(ℰ) = ∑_n c_n(ℰ) X^n` with coefficients in the operations on `CH_*(X)`. Two steps of the proof
of the Whitney formula `c(ℰ) = c(ℰ₁) c(ℰ₂)` (Stacks 0ES9) through the splitting principle are
recorded here.

* If `ℰ₁` and `ℰ₂` have filtrations with invertible quotients `ℒ_i` and `ℳ_j`, then so has `ℰ`,
  with the quotients `ℒ_1, …, ℒ_a, ℳ_1, …, ℳ_b`, and the product formula of Stacks 0ESA gives
  `c(ℰ) = ∏ (1 + c_1(ℒ_i) X) ∏ (1 + c_1(ℳ_j) X) = c(ℰ₁) c(ℰ₂)`.
* An identity `c(ℰ') = c(ℰ'₁) c(ℰ'₂)` on a space `P` descends to `c(ℰ) = c(ℰ₁) c(ℰ₂)` on `X`
  along an injective map `g : CH_*(X) ⟶ CH_*(P)` intertwining the Chern classes of the
  `ℰ'_•` with those of the `ℰ_•`, such as the flat pullback along the morphism of the splitting
  principle.

Both are granted Stacks 0ES8 degree by degree on the space where the filtrations live.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.mk_chernCap_eq_mul_of_filtrations`: the Whitney formula
  for a short exact sequence whose outer terms are filtered with invertible quotients.
* `AlgebraicGeometry.Space.PrivateChern.mk_chernCap_eq_mul_of_injective`: descent of the Whitney
  formula along an injective intertwining map.

## References

* [Stacks Project, Tag 0ES9](https://stacks.math.columbia.edu/tag/0ES9)
* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **The Whitney formula for a sequence with filtered outer terms**, granted Stacks 0ES8 degree
by degree. If `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` is short exact and `ℰ₁`, `ℰ₂` have filtrations with invertible
quotients, then `c(ℰ) = c(ℰ₁) c(ℰ₂)` as power series of operations on `CH_*(X)`. -/
theorem mk_chernCap_eq_mul_of_filtrations
    (x : ∀ L : Modules.{u, u} D.site D.base D.base_mem X hX.1,
      IsInvertibleModule (goodSpace hX) L → AddMonoid.End (chowHomology.{u, v} D sX hX))
    (h8 : ∀ (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r) (n : ℕ),
      chernCap.{u, v} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, v} T.X₃ r h₃ (n + 1) + x T.X₁ h₁ * chernCap.{u, v} T.X₃ r h₃ n)
    {S : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)} (hS : S.ShortExact)
    {a b : ℕ} (h₁ : IsFiniteLocallyFreeOfRank D sX hX S.X₁ a)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX S.X₂ (a + b))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX S.X₃ b)
    (L : Fin a → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ i, IsInvertibleModule (goodSpace hX) (L i))
    (F₁ : Fin (a + 1) → Subobject S.X₁) (hF₁ : Monotone F₁) (h₁0 : F₁ 0 = ⊥)
    (h₁a : F₁ (Fin.last a) = ⊤)
    (e₁ : ∀ i : Fin a, cokernel (ofLE (F₁ i.castSucc) (F₁ i.succ) (hF₁ i.castSucc_le_succ)) ≅ L i)
    (M : Fin b → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : ∀ j, IsInvertibleModule (goodSpace hX) (M j))
    (F₃ : Fin (b + 1) → Subobject S.X₃) (hF₃ : Monotone F₃) (h₃0 : F₃ 0 = ⊥)
    (h₃b : F₃ (Fin.last b) = ⊤)
    (e₃ : ∀ j : Fin b, cokernel (ofLE (F₃ j.castSucc) (F₃ j.succ) (hF₃ j.castSucc_le_succ)) ≅ M j) :
    PowerSeries.mk (chernCap.{u, v} S.X₂ (a + b) h₂) =
      PowerSeries.mk (chernCap.{u, v} S.X₁ a h₁) * PowerSeries.mk (chernCap.{u, v} S.X₃ b h₃) := by
  have := hS.mono_f
  let N : Fin (a + b) → Modules.{u, u} D.site D.base D.base_mem X hX.1 :=
    Fin.addCases (motive := fun _ ↦ _) L M
  have hN : ∀ k, IsInvertibleModule (goodSpace hX) (N k) := fun k ↦ by
    induction k using Fin.addCases with
    | left i => simpa [N] using hL i
    | right j => simpa [N] using hM j
  rw [mk_chernCap_eq_prod_of_filtration x h8 S.X₂ h₂ N hN (Abelian.Subobject.concatFiltration F₁ F₃)
      (Abelian.Subobject.monotone_concatFiltration hS hF₁ hF₃ h₁a h₃0)
      (Abelian.Subobject.concatFiltration_zero hS h₁0 h₁a h₃0)
      (Abelian.Subobject.concatFiltration_last h₃b)
      (Abelian.Subobject.concatFiltrationSubquotientIso hS hF₁ hF₃ h₁a h₃0 L M e₁ e₃),
    mk_chernCap_eq_prod_of_filtration x h8 S.X₁ h₁ L hL F₁ hF₁ h₁0 h₁a e₁,
    mk_chernCap_eq_prod_of_filtration x h8 S.X₃ h₃ M hM F₃ hF₃ h₃0 h₃b e₃, List.ofFn_add,
    List.prod_append]
  have key : ∀ (E E' : Modules.{u, u} D.site D.base D.base_mem X hX.1) (_ : E = E')
      (p : IsFiniteLocallyFreeOfRank D sX hX E 1) (q : IsFiniteLocallyFreeOfRank D sX hX E' 1),
      chernCap.{u, v} E 1 p 1 = chernCap.{u, v} E' 1 q 1 := by
    rintro E _ rfl p q
    rfl
  refine congrArg₂ (· * ·) (congrArg List.prod ?_) (congrArg List.prod ?_)
  · exact List.ofFn_inj.mpr (funext fun i ↦ congrArg (fun y ↦ 1 + PowerSeries.C y * PowerSeries.X)
      (key _ _ (Fin.addCases_left i) _ _))
  · exact List.ofFn_inj.mpr (funext fun j ↦ congrArg (fun y ↦ 1 + PowerSeries.C y * PowerSeries.X)
      (key _ _ (Fin.addCases_right j) _ _))

/-- **Descent of the Whitney formula along an injective intertwining map.** Let
`g : CH_*(X) ⟶ CH_*(P)` be injective and intertwine the Chern classes of `ℰ'`, `ℰ'₁`, `ℰ'₂` on
`P` with those of `ℰ`, `ℰ₁`, `ℰ₂` on `X`. If `c(ℰ') = c(ℰ'₁) c(ℰ'₂)`, then
`c(ℰ) = c(ℰ₁) c(ℰ₂)`. -/
theorem mk_chernCap_eq_mul_of_injective {P : D.Ambient} {sP : P ⟶ D.space} {hP : D.IsGood sP}
    (g : chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D sP hP)
    (hg : Function.Injective g)
    {E E₁ E₂ : Modules.{u, u} D.site D.base D.base_mem X hX.1} {r r₁ r₂ : ℕ}
    (hE : IsFiniteLocallyFreeOfRank D sX hX E r) (hE₁ : IsFiniteLocallyFreeOfRank D sX hX E₁ r₁)
    (hE₂ : IsFiniteLocallyFreeOfRank D sX hX E₂ r₂)
    {E' E'₁ E'₂ : Modules.{u, u} D.site D.base D.base_mem P hP.1}
    (hE' : IsFiniteLocallyFreeOfRank D sP hP E' r)
    (hE'₁ : IsFiniteLocallyFreeOfRank D sP hP E'₁ r₁)
    (hE'₂ : IsFiniteLocallyFreeOfRank D sP hP E'₂ r₂)
    (hg₀ : ∀ n α, chernCap.{u, v} E' r hE' n (g α) = g (chernCap.{u, v} E r hE n α))
    (hg₁ : ∀ n α, chernCap.{u, v} E'₁ r₁ hE'₁ n (g α) = g (chernCap.{u, v} E₁ r₁ hE₁ n α))
    (hg₂ : ∀ n α, chernCap.{u, v} E'₂ r₂ hE'₂ n (g α) = g (chernCap.{u, v} E₂ r₂ hE₂ n α))
    (h : PowerSeries.mk (chernCap.{u, v} E' r hE') =
      PowerSeries.mk (chernCap.{u, v} E'₁ r₁ hE'₁) * PowerSeries.mk (chernCap.{u, v} E'₂ r₂ hE'₂)) :
    PowerSeries.mk (chernCap.{u, v} E r hE) =
      PowerSeries.mk (chernCap.{u, v} E₁ r₁ hE₁) * PowerSeries.mk (chernCap.{u, v} E₂ r₂ hE₂) := by
  ext n : 1
  have hn := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul] at hn ⊢
  simp only [PowerSeries.coeff_mk] at hn ⊢
  refine AddMonoidHom.ext fun α ↦ hg ?_
  have hsum : ∀ {M : Type _} [AddCommGroup M] (s : Finset (ℕ × ℕ))
      (f : ℕ × ℕ → AddMonoid.End M) (m : M), (∑ p ∈ s, f p) m = ∑ p ∈ s, f p m :=
    fun s f m ↦ AddMonoidHom.finsetSum_apply _ _ _
  calc g (chernCap.{u, v} E r hE n α) = chernCap.{u, v} E' r hE' n (g α) := (hg₀ n α).symm
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          chernCap.{u, v} E'₁ r₁ hE'₁ p.1 (chernCap.{u, v} E'₂ r₂ hE'₂ p.2 (g α)) := by
        rw [hn, hsum]
        rfl
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          g (chernCap.{u, v} E₁ r₁ hE₁ p.1 (chernCap.{u, v} E₂ r₂ hE₂ p.2 α)) :=
        Finset.sum_congr rfl fun p _ ↦ by rw [hg₂, hg₁]
    _ = g ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          chernCap.{u, v} E₁ r₁ hE₁ p.1 * chernCap.{u, v} E₂ r₂ hE₂ p.2) α) := by
        rw [hsum, map_sum]
        rfl

end AlgebraicGeometry.Space.PrivateChern

end
