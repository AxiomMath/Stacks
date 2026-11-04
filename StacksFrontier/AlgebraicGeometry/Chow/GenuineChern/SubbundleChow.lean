module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap

/-!
# The first Chern class along an invertible subsheaf: the computation on Chow groups

Let `0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` be a short exact sequence of finite locally free modules with `ℳ`
invertible, `𝒢` of rank `r + 1` and `𝒬` of rank `r ≥ 1`. The projective bundle `P(𝒬)` sits in
`P(𝒢)` as a closed subscheme `ι : P(𝒬) ⟶ P(𝒢)` over `X`, with `𝒪_{P(𝒢)}(1)` restricting to
`𝒪_{P(𝒬)}(1)`, and it is the zero scheme of the section of `𝒪_{P(𝒢)}(1) ⊗ π^*ℳ^{-1}` given by
`π^*ℳ ⟶ π^*𝒢 ⟶ 𝒪(1)`. On Chow groups this gives, for `α ∈ CH_k(X)`,

  `c₁(𝒪_{P(𝒢)}(1)) ∩ π_𝒢^*α = ι_*(π_𝒬^*α) + π_𝒢^*(c₁(ℳ) ∩ α)`

(Stacks 02TR for the divisor, 02SP and 02SS for the twist by `π^*ℳ`). This file draws the
consequence for the pushforwards of [Stacks, Tag 02TW]:

  `π_{𝒢*}(c₁(𝒪(1))^{r+1} ∩ π_𝒢^*α) = π_{𝒬*}(c₁(𝒪(1))^r ∩ π_𝒬^*α) + c₁(ℳ) ∩ α`,

which by `Stacks.Chow.chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily` is
`c₁(𝒢) ∩ α = c₁(𝒬) ∩ α + c₁(ℳ) ∩ α`, the first Chern class part of [Stacks, Tag 02UH].

Everything about the bundles enters as a hypothesis on Chow groups: the two bundle data are
parameters, `hcap` is Stacks 02SU for the closed immersion together with the restriction of the
twist, `hdiv` is the displayed divisor identity, and `htop` is the top half of 02TW for `P(𝒢)`.

## Main results

* `Stacks.Chow.projectiveBundleProjection_succ_eq_of_divisor` — the displayed identity of
  pushforwards.

## References

* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Closes the degree side conditions of transports. -/
local macro "deg" : tactic =>
  `(tactic| first | omega | (simp only [List.length_replicate] at *; omega) | simp)

variable (C : ChowSituation.{u}) {X PG PQ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sPG : PG ⟶ C.S) [LocallyOfFiniteType sPG] (πG : PG ⟶ X) [Flat πG] [IsProper πG]
  (hsPG : πG ≫ sX = sPG) (sPQ : PQ ⟶ C.S) [LocallyOfFiniteType sPQ] (πQ : PQ ⟶ X) [Flat πQ]
  [IsProper πQ] (hsPQ : πQ ≫ sX = sPQ) (r : ℕ)
  (hπG : AlgebraicGeometry.RelativeDimension πG (r + 1 - 1))
  (hπQ : AlgebraicGeometry.RelativeDimension πQ (r - 1))
  (hfacG : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPG sX πG hsPG (r + 1 - 1)
    hπG k)
  (hfacQ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPQ sX πQ hsPQ (r - 1)
    hπQ k)
  (twistG : ChernCapOperator C sPG) (twistQ : ChernCapOperator C sPQ)
  (ι : PQ ⟶ PG) [IsProper ι] (hι : ι ≫ sPG = sPQ)
  (capM : ∀ d : ℤ, chowGroup C sX (d + 1) →+ chowGroup C sX d)

/-- **The pushforward of the top power of the twist along an invertible subsheaf.** Given the
divisor identity `c₁(𝒪(1)) ∩ π_𝒢^*α = ι_*(π_𝒬^*α) + π_𝒢^*(c₁(ℳ) ∩ α)`, the compatibility of
the twists along `ι`, and the top half of Stacks 02TW for `P(𝒢)`,

  `π_{𝒢*}(c₁(𝒪(1))^{r+1} ∩ π_𝒢^*α) = π_{𝒬*}(c₁(𝒪(1))^r ∩ π_𝒬^*α) + c₁(ℳ) ∩ α`. -/
theorem projectiveBundleProjection_succ_eq_of_divisor (hr : 1 ≤ r) (hιπ : ι ≫ πG = πQ)
    (hcap : ∀ (d : ℤ) (y : chowGroup C sPQ (d + 1)),
      properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d)
          (twistQ.capOnChow C sPQ d y) =
        twistG.capOnChow C sPG d (properChowPushforward C sPQ sPG ι hι (d + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _) y))
    (hdiv : ∀ (k : ℤ) (α : chowGroup C sX k) (d : ℤ) (_ : d + 1 = k + ((r + 1 - 1 : ℕ) : ℤ))
      (y : chowGroup C sPG (d + 1))
      (_ : y ≍ projectiveBundlePullback C sX sPG πG hsPG (r + 1) hπG hfacG k α)
      (z : chowGroup C sPQ d)
      (_ : z ≍ projectiveBundlePullback C sX sPQ πQ hsPQ r hπQ hfacQ k α)
      (w : chowGroup C sPG d)
      (_ : w ≍ projectiveBundlePullback C sX sPG πG hsPG (r + 1) hπG hfacG (k - 1)
        (capM (k - 1) (chowGroupCast C sX (by omega) α))),
      twistG.capOnChow C sPG d y =
        properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d) z +
          w)
    (htop : ∀ (k : ℤ) (β : chowGroup C sX k),
      projectiveBundleProjection C sX sPG πG hsPG (r + 1) hπG hfacG twistG r k β =
        chowGroupCast C sX (by omega) β)
    (k : ℤ) (α : chowGroup C sX k) :
    projectiveBundleProjection C sX sPG πG hsPG (r + 1) hπG hfacG twistG (r + 1) k α =
      chowGroupCast C sX (by omega)
          (projectiveBundleProjection C sX sPQ πQ hsPQ r hπQ hfacQ twistQ r k α) +
        chowGroupCast C sX (by omega) (capM (k - 1) (chowGroupCast C sX (by omega) α)) := by
  subst hιπ
  set d : ℤ := k + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) with hd
  have hdk : d = k - 1 := by omega
  -- the three pieces of the divisor identity, in the degrees the computation needs
  set y : chowGroup C sPG (d + (r : ℤ) + 1) :=
    chowGroupCast C sPG (by omega)
      (projectiveBundlePullback C sX sPG πG hsPG (r + 1) hπG hfacG k α) with hy
  set z : chowGroup C sPQ (d + ((List.replicate r twistQ).length : ℤ)) :=
    chowGroupCast C sPQ (by deg)
      (projectiveBundlePullback C sX sPQ (ι ≫ πG) hsPQ r hπQ hfacQ k α) with hz
  set w : chowGroup C sPG (d + ((List.replicate r twistG).length : ℤ)) :=
    chowGroupCast C sPG (by deg)
      (projectiveBundlePullback C sX sPG πG hsPG (r + 1) hπG hfacG (k - 1)
        (capM (k - 1) (chowGroupCast C sX (by omega) α))) with hw
  have hyh : y ≍ projectiveBundlePullback C sX sPG πG hsPG (r + 1) hπG hfacG k α :=
    chowGroupCast_heq C sPG _ _
  have hzh : z ≍ projectiveBundlePullback C sX sPQ (ι ≫ πG) hsPQ r hπQ hfacQ k α :=
    chowGroupCast_heq C sPQ _ _
  have hwh : w ≍ projectiveBundlePullback C sX sPG πG hsPG (r + 1) hπG hfacG (k - 1)
      (capM (k - 1) (chowGroupCast C sX (by omega) α)) :=
    chowGroupCast_heq C sPG _ _
  have hdiv' := hdiv k α (d + (r : ℤ)) (by omega) y (chowGroupCast_heq C sPG _ _)
    (chowGroupCast C sPQ (by deg) z)
    ((chowGroupCast_heq C sPQ _ _).trans (chowGroupCast_heq C sPQ _ _))
    (chowGroupCast C sPG (by deg) w)
    ((chowGroupCast_heq C sPG _ _).trans (chowGroupCast_heq C sPG _ _))
  -- unfold the left-hand side and peel off the innermost cap
  have hlhs : projectiveBundleProjection C sX sPG πG hsPG (r + 1) hπG hfacG twistG (r + 1) k α =
      properChowPushforward C sPG sX πG hsPG d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPG sX πG hsPG d)
        (iteratedChernCapOnChow C sPG (List.replicate r twistG) d
          (chowGroupCast C sPG (by simp) (twistG.capOnChow C sPG (d + (r : ℤ)) y))) := by
    simp only [projectiveBundleProjection, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom]
    congr 1
    exact iteratedChernCapOnChow_replicate_succ_heq' C sPG twistG r d _ y
      ((chowGroupCast_heq C sPG _ _).trans (chowGroupCast_heq C sPG _ _).symm) _
      (chowGroupCast_heq C sPG _ _)
  rw [hlhs, hdiv']
  simp only [map_add]
  congr 1
  · -- the term `ι_*(π_𝒬^*α)`
    rw [← properChowPushforward_iteratedChernCapOnChow C sPQ sPG ι hι twistQ twistG hcap r d z
      _ ((chowGroupCast_heq C sPG _ _).trans
        (properChowPushforward_heq C sPQ sPG ι hι (by simp) (chowGroupCast_heq C sPQ _ _)))]
    rw [properChowPushforward_properChowPushforward]
    refine chowGroup_eq_of_heq C sX ?_
    refine HEq.trans ?_ (chowGroupCast_heq C sX _ _).symm
    simp only [projectiveBundleProjection, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom]
    refine properChowPushforward_heq C sPQ sX (ι ≫ πG) _ (by deg) ?_
    refine iteratedChernCapOnChow_heq C sPQ _ (by deg) ?_
    exact hzh.trans (chowGroupCast_heq C sPQ _ _).symm
  · -- the term `π_𝒢^*(c₁(ℳ) ∩ α)`
    have := htop (k - 1) (capM (k - 1) (chowGroupCast C sX (by omega) α))
    refine chowGroup_eq_of_heq C sX ?_
    refine HEq.trans ?_ ((heq_of_eq this).trans ((chowGroupCast_heq C sX _ _).trans
      (chowGroupCast_heq C sX _ _).symm))
    simp only [projectiveBundleProjection, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom]
    refine properChowPushforward_heq C sPG sX πG hsPG (by deg) ?_
    refine iteratedChernCapOnChow_heq C sPG _ (by deg) ?_
    exact (chowGroupCast_heq C sPG _ _).trans ((chowGroupCast_heq C sPG _ _).trans
      (hwh.trans (chowGroupCast_heq C sPG _ _).symm))

end Stacks.Chow

end
