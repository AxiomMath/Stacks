module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernFamily
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleGeometry
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClassesSegre

/-!
# The Chern classes along an invertible subsheaf: Stacks 02UG and 02UH

Let `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` be a short exact sequence of modules on a scheme `X` locally of
finite type over the base of chapter 42, with `ℒ` invertible and `ℰ`, `ℱ` finite locally free of
ranks `r + 1` and `r`. This file proves, for the Chern class cap products
`Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6],

  `c(ℰ) = c(ℒ) c(ℱ)`,  that is,  `c_m(ℰ) ∩ α = c_m(ℱ) ∩ α + c₁(ℒ) ∩ c_{m-1}(ℱ) ∩ α`,

which is [Stacks, Tag 02UH], and its case `ℒ = 𝒪_X`, [Stacks, Tag 02UG], where `c₁(𝒪_X) = 0`
gives `c(ℰ) = c(ℱ)`. The total Chern classes are read in the ring of graded cap families on the
Chow groups of `X` (`Stacks.Chow.GenuineChern.chernFamily`).

## The proof

The source proves Stacks 02UG through the closed immersion `ι : P(ℱ) ⟶ P(ℰ)` of projective
bundles and deduces Stacks 02UH from it by twisting with `ℒ^{-1}` and Stacks 02UD. The argument
here runs the proof of Stacks 02UG directly for an invertible `ℒ`, which needs no twist: `P(ℱ)` is
the zero scheme of a regular section of `𝒪_{P(ℰ)}(1) ⊗ π^*ℒ^{-1}`
(`Stacks.Chow.GenuineChern.subbundleHolds`), so by Stacks 02SP, 02TR and 02SS

  `c₁(𝒪(1)) ∩ π_ℰ^*x = ι_*(π_ℱ^*x) + π_ℰ^*(c₁(ℒ) ∩ x)`.

With the projection formula of Stacks 02SU along `ι`, each summand of the relation of Stacks
02U6 on `P(ℰ)` is the pushforward of a summand of the relation on `P(ℱ)` plus a term that
cancels against a neighbour
(`Stacks.Chow.GenuineChern.projectiveBundleChernRelation_add_capShift`), so the family
`(c_j(ℱ) ∩ α + c₁(ℒ) ∩ c_{j-1}(ℱ) ∩ α)_j` satisfies the relation on `P(ℰ)`, and the uniqueness
half of Stacks 02U6 identifies it with the family of `ℰ`.

## Main results

* `Stacks.Chow.GenuineChern.projectiveBundleChernTerm_succ_eq_of_divisor` — a summand of the
  relation on the bigger bundle, in terms of the smaller one.
* `Stacks.Chow.GenuineChern.projectiveBundleChernRelation_add_capShift` — the relation on the
  bigger bundle for the shifted family.
* `Stacks.Chow.GenuineChern.bundleChernCapFamily_eq_add_capShift` — the Chern class cap products
  of the middle term.
* `Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact_of_isInvertible` — **Stacks 02UH**.
* `Stacks.Chow.GenuineChern.chernFamily_eq_of_shortExact_of_iso_unit`,
  `Stacks.Chow.GenuineChern.chernCap_eq_of_shortExact_of_iso_unit` — **Stacks 02UG**.

## References

* [Stacks Project, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

section Divisor

variable (C : ChowSituation.{u}) {X PG PQ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sPG : PG ⟶ C.S) [LocallyOfFiniteType sPG] (πG : PG ⟶ X) [LocallyOfFiniteType πG] [Flat πG]
  (hsPG : πG ≫ sX = sPG) (sPQ : PQ ⟶ C.S) [LocallyOfFiniteType sPQ] (πQ : PQ ⟶ X)
  [LocallyOfFiniteType πQ] [Flat πQ] (hsPQ : πQ ≫ sX = sPQ) (n : ℕ)
  (hπG : AlgebraicGeometry.RelativeDimension πG (n + 1 + 1 - 1))
  (hπQ : AlgebraicGeometry.RelativeDimension πQ (n + 1 - 1))
  (hfacG : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPG sX πG hsPG
    (n + 1 + 1 - 1) hπG k)
  (hfacQ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPQ sX πQ hsPQ
    (n + 1 - 1) hπQ k)
  (twistG : ChernCapOperator C sPG) (twistQ : ChernCapOperator C sPQ)
  (ι : PQ ⟶ PG) [IsProper ι] (hι : ι ≫ sPG = sPQ)
  (capM : ∀ d : ℤ, chowGroup C sX (d + 1) →+ chowGroup C sX d)

/-- **A summand of the relation of Stacks 02U6, pushed into the bigger bundle.** Given the
compatibility `hcap` of the twists along `ι : P(𝒬) ⟶ P(𝒢)` (Stacks 02SU) and the divisor identity
`hdiv`, `c₁(𝒪(1)) ∩ π_𝒢^*α = ι_*(π_𝒬^*α) + π_𝒢^*(c₁(ℳ) ∩ α)`, for every `x`

  `c₁(𝒪(1))^{i+1} ∩ π_𝒢^*x = ι_*(c₁(𝒪(1))^i ∩ π_𝒬^*x) + c₁(𝒪(1))^i ∩ π_𝒢^*(c₁(ℳ) ∩ x)`. -/
theorem projectiveBundleChernTerm_succ_eq_of_divisor
    (hcap : ∀ (d : ℤ) (y : chowGroup C sPQ (d + 1)),
      properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d)
          (twistQ.capOnChow C sPQ d y) =
        twistG.capOnChow C sPG d (properChowPushforward C sPQ sPG ι hι (d + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _) y))
    (hdiv : ∀ (k : ℤ) (α : chowGroup C sX k) (d : ℤ) (_ : d + 1 = k + ((n + 1 + 1 - 1 : ℕ) : ℤ))
      (y : chowGroup C sPG (d + 1))
      (_ : y ≍ projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG k α)
      (z : chowGroup C sPQ d)
      (_ : z ≍ projectiveBundlePullback C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ k α)
      (w : chowGroup C sPG d)
      (_ : w ≍ projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG (k - 1)
        (capM (k - 1) (chowGroupCast C sX (by omega) α))),
      twistG.capOnChow C sPG d y =
        properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d) z +
          w)
    (k : ℤ) (i : ℕ) (hi : i ≤ n + 1) (x : chowGroup C sX (k - ((n + 1 - i : ℕ) : ℤ))) :
    projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k (i + 1) (by omega)
        (chowGroupCast C sX (by omega) x) =
      chowGroupCast C sPG (by omega)
          (properChowPushforward C sPQ sPG ι hι (k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ))
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _)
            (projectiveBundleChernTerm C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ twistQ k i hi x)) +
        projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k i (by omega)
          (capM (k - ((n + 1 + 1 - i : ℕ) : ℤ)) (chowGroupCast C sX (by omega) x)) := by
  have hdiv' := hdiv (k - ((n + 1 - i : ℕ) : ℤ)) x
    (k + ((n + 1 + 1 - 1 : ℕ) : ℤ) - ((n + 1 + 1 : ℕ) : ℤ) + (i : ℤ)) (by omega)
    (chowGroupCast C sPG (by omega)
      (projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG _ x))
    (chowGroupCast_heq C sPG _ _)
    (chowGroupCast C sPQ (by omega)
      (projectiveBundlePullback C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ _ x))
    (chowGroupCast_heq C sPQ _ _)
    (chowGroupCast C sPG (by omega)
      (projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG _
        (capM (k - ((n + 1 - i : ℕ) : ℤ) - 1) (chowGroupCast C sX (by omega) x))))
    (chowGroupCast_heq C sPG _ _)
  simp only [projectiveBundleChernTerm, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  -- peel off the innermost cap on the left
  refine (iteratedChernCapOnChow_replicate_succ_heq' C sPG twistG i
    (k + ((n + 1 + 1 - 1 : ℕ) : ℤ) - ((n + 1 + 1 : ℕ) : ℤ)) _
    (chowGroupCast C sPG (by omega)
      (projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG _ x))
    ((chowGroupCast_heq C sPG _ _).trans ((flatPullbackChow_heq C sPG sX πG hsPG _ hπG hfacG
      (by omega) (chowGroupCast_heq C sX _ x)).trans (chowGroupCast_heq C sPG _ _).symm))
    (chowGroupCast C sPG (by simp) (twistG.capOnChow C sPG _
      (chowGroupCast C sPG (by omega)
        (projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG _ x))))
    (chowGroupCast_heq C sPG _ _)).trans ?_
  rw [hdiv', map_add, map_add]
  congr 1
  · -- the pushforward term
    rw [properChowPushforward_iteratedChernCapOnChow C sPQ sPG ι hι twistQ twistG hcap i
      (k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) _
      (chowGroupCast C sPG (by simp)
        (properChowPushforward C sPQ sPG ι hι _
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _)
          (chowGroupCast C sPQ (by simp; omega)
            (projectiveBundlePullback C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ _ x))))
      ((chowGroupCast_heq C sPG _ _).trans (properChowPushforward_heq C sPQ sPG ι hι (by simp)
        (HEq.refl _)))]
    refine eq_of_heq (HEq.trans ?_ (chowGroupCast_heq C sPG _ _).symm)
    refine iteratedChernCapOnChow_heq C sPG _ (by omega) ?_
    refine (chowGroupCast_heq C sPG _ _).trans ((properChowPushforward_heq C sPQ sPG ι hι
      (by simp only [List.length_replicate]; omega)
      ((chowGroupCast_heq C sPQ _ _).trans (chowGroupCast_heq C sPQ _ _).symm)).trans
      (chowGroupCast_heq C sPG _ _).symm)
  · -- the term of `c₁(ℳ)`
    refine eq_of_heq (iteratedChernCapOnChow_heq C sPG _ rfl ?_)
    refine (chowGroupCast_heq C sPG _ _).trans ((chowGroupCast_heq C sPG _ _).trans
      (HEq.trans ?_ (chowGroupCast_heq C sPG _ _).symm))
    refine flatPullbackChow_heq C sPG sX πG hsPG _ hπG hfacG (by omega) ?_
    refine heq_apply_of_degree C sX sX (fun d => d + 1) (fun d => d) capM (by omega) ?_
    exact (chowGroupCast_heq C sX _ x).trans (chowGroupCast_heq C sX _ x).symm

/-- Members of a family of Chow classes indexed by `ℕ`, in degrees `k - j`, agree up to
transport at equal indices. -/
theorem natFamily_eq_chowGroupCast (k : ℤ) (e : ∀ j : ℕ, chowGroup C sX (k - (j : ℤ)))
    {i j : ℕ} (h : i = j) : e j = chowGroupCast C sX (by rw [h]) (e i) := by
  subst h; rfl

/-- The family `(c₁(ℳ) ∩ e_{j-1})_j`: zero in index `0`, and `c₁(ℳ) ∩ e_j` in index `j + 1`, for
a family `(e_j)_j` with `e_j` of degree `k - j` and an operation `c₁(ℳ) ∩ -` lowering the degree
by one. -/
def capShift (k : ℤ) (e : ∀ j : ℕ, chowGroup C sX (k - (j : ℤ))) :
    ∀ j : ℕ, chowGroup C sX (k - (j : ℤ))
  | 0 => 0
  | j + 1 => capM (k - ((j + 1 : ℕ) : ℤ)) (chowGroupCast C sX (by push_cast; ring) (e j))

/-- The shifted family vanishes in index `0`. -/
theorem capShift_zero (k : ℤ) (e : ∀ j : ℕ, chowGroup C sX (k - (j : ℤ))) :
    capShift C sX capM k e 0 = 0 :=
  rfl

/-- The shifted family in an index `j = m + 1`, with the transport made explicit. -/
theorem capShift_of_eq (k : ℤ) (e : ∀ j : ℕ, chowGroup C sX (k - (j : ℤ))) {j m : ℕ}
    (h : j = m + 1) :
    capShift C sX capM k e j = capM (k - (j : ℤ)) (chowGroupCast C sX (by omega) (e m)) := by
  subst h; rfl

/-- **The relation of Stacks 02U6 along an invertible subsheaf.** If `(e_j)_{j ≤ n+1}` satisfies
the relation on the bundle `P(𝒬)` and `e_{n+2} = 0`, then `(e_j + c₁(ℳ) ∩ e_{j-1})_{j ≤ n+2}`
satisfies the relation on the bundle `P(𝒢)`: the summands of the relation over `P(𝒢)` are, by
`Stacks.Chow.GenuineChern.projectiveBundleChernTerm_succ_eq_of_divisor`, the pushforwards of
those over `P(𝒬)` plus terms that cancel in pairs. -/
theorem projectiveBundleChernRelation_add_capShift
    (hcap : ∀ (d : ℤ) (y : chowGroup C sPQ (d + 1)),
      properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d)
          (twistQ.capOnChow C sPQ d y) =
        twistG.capOnChow C sPG d (properChowPushforward C sPQ sPG ι hι (d + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _) y))
    (hdiv : ∀ (k : ℤ) (α : chowGroup C sX k) (d : ℤ) (_ : d + 1 = k + ((n + 1 + 1 - 1 : ℕ) : ℤ))
      (y : chowGroup C sPG (d + 1))
      (_ : y ≍ projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG k α)
      (z : chowGroup C sPQ d)
      (_ : z ≍ projectiveBundlePullback C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ k α)
      (w : chowGroup C sPG d)
      (_ : w ≍ projectiveBundlePullback C sX sPG πG hsPG (n + 1 + 1) hπG hfacG (k - 1)
        (capM (k - 1) (chowGroupCast C sX (by omega) α))),
      twistG.capOnChow C sPG d y =
        properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d) z +
          w)
    (k : ℤ) (e : ∀ j : ℕ, chowGroup C sX (k - (j : ℤ))) (htop : e (n + 1 + 1) = 0)
    (he : ProjectiveBundleChernRelation C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ twistQ k
      fun j => e j) :
    ProjectiveBundleChernRelation C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k
      fun j => e j + capShift C sX capM k e j := by
  have hQ : ∑ i : Fin (n + 1 + 1), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ twistQ k i.val
        (Nat.lt_succ_iff.mp i.isLt) (e (n + 1 - i.val)) = 0 := he
  change ∑ i : Fin (n + 1 + 1 + 1), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k i.val
        (Nat.lt_succ_iff.mp i.isLt)
        (e (n + 1 + 1 - i.val) + capShift C sX capM k e (n + 1 + 1 - i.val)) = 0
  simp only [map_add, smul_add, Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (n := n + 1 + 1) (fun i => (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k i.val
        (Nat.lt_succ_iff.mp i.isLt) (e (n + 1 + 1 - i.val))),
    Fin.sum_univ_castSucc (n := n + 1 + 1) (fun i => (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k i.val
        (Nat.lt_succ_iff.mp i.isLt) (capShift C sX capM k e (n + 1 + 1 - i.val)))]
  have hhead : (-1 : ℤ) ^ ((0 : Fin (n + 1 + 1 + 1)) : ℕ) •
      projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k
        ((0 : Fin (n + 1 + 1 + 1)) : ℕ) (Nat.lt_succ_iff.mp (0 : Fin (n + 1 + 1 + 1)).isLt)
        (e (n + 1 + 1 - ((0 : Fin (n + 1 + 1 + 1)) : ℕ))) = 0 := by
    rw [natFamily_eq_chowGroupCast C sX k e
      (show n + 1 + 1 = n + 1 + 1 - ((0 : Fin (n + 1 + 1 + 1)) : ℕ) by simp), htop, map_zero,
      map_zero, smul_zero]
  have hlast : (-1 : ℤ) ^ ((Fin.last (n + 1 + 1)) : ℕ) •
      projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k
        ((Fin.last (n + 1 + 1)) : ℕ) (Nat.lt_succ_iff.mp (Fin.last (n + 1 + 1)).isLt)
        (capShift C sX capM k e (n + 1 + 1 - ((Fin.last (n + 1 + 1)) : ℕ))) = 0 := by
    rw [natFamily_eq_chowGroupCast C sX k (capShift C sX capM k e)
      (show 0 = n + 1 + 1 - ((Fin.last (n + 1 + 1)) : ℕ) by simp), capShift_zero, map_zero,
      map_zero, smul_zero]
  have hsucc : ∀ i : Fin (n + 1 + 1), (-1 : ℤ) ^ (i.val + 1) •
      projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k (i.val + 1)
        (by omega) (e (n + 1 + 1 - (i.val + 1))) =
      -((-1 : ℤ) ^ i.val • chowGroupCast C sPG (by omega)
          (properChowPushforward C sPQ sPG ι hι (k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ))
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _)
            (projectiveBundleChernTerm C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ twistQ k i.val
              (Nat.lt_succ_iff.mp i.isLt) (e (n + 1 - i.val))))) -
        (-1 : ℤ) ^ i.val •
          projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k i.val
            (by omega) (capM (k - ((n + 1 + 1 - i.val : ℕ) : ℤ))
              (chowGroupCast C sX (by omega) (e (n + 1 - i.val)))) := by
    intro i
    rw [natFamily_eq_chowGroupCast C sX k e (show n + 1 - i.val = n + 1 + 1 - (i.val + 1) by omega),
      projectiveBundleChernTerm_succ_eq_of_divisor C sX sPG πG hsPG sPQ πQ hsPQ n hπG hπQ hfacG
        hfacQ twistG twistQ ι hι capM hcap hdiv k i.val (Nat.lt_succ_iff.mp i.isLt),
      pow_succ, mul_neg_one, neg_smul, smul_add, neg_add']
  have hcast : ∀ i : Fin (n + 1 + 1), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k i.val
        (by omega) (capShift C sX capM k e (n + 1 + 1 - i.val)) =
      (-1 : ℤ) ^ i.val •
        projectiveBundleChernTerm C sX sPG πG hsPG (n + 1 + 1) hπG hfacG twistG k i.val
          (by omega) (capM (k - ((n + 1 + 1 - i.val : ℕ) : ℤ))
            (chowGroupCast C sX (by omega) (e (n + 1 - i.val)))) := by
    intro i
    rw [capShift_of_eq C sX capM k e (show n + 1 + 1 - i.val = n + 1 - i.val + 1 by omega)]
  rw [hhead, hlast, zero_add, add_zero]
  refine (congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => hsucc i)
    (Finset.sum_congr rfl fun i _ => hcast i)).trans ?_
  rw [← Finset.sum_add_distrib]
  simp only [sub_add_cancel]
  rw [Finset.sum_neg_distrib, neg_eq_zero]
  have hpush : ∑ i : Fin (n + 1 + 1), (-1 : ℤ) ^ i.val • chowGroupCast C sPG
        (show k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) =
          k + ((n + 1 + 1 - 1 : ℕ) : ℤ) - ((n + 1 + 1 : ℕ) : ℤ) by omega)
        (properChowPushforward C sPQ sPG ι hι (k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _)
          (projectiveBundleChernTerm C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ twistQ k i.val
            (Nat.lt_succ_iff.mp i.isLt) (e (n + 1 - i.val)))) =
      chowGroupCast C sPG (by omega)
        (properChowPushforward C sPQ sPG ι hι (k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _)
          (∑ i : Fin (n + 1 + 1), (-1 : ℤ) ^ i.val •
            projectiveBundleChernTerm C sX sPQ πQ hsPQ (n + 1) hπQ hfacQ twistQ k i.val
              (Nat.lt_succ_iff.mp i.isLt) (e (n + 1 - i.val)))) := by
    simp only [map_sum, map_zsmul]
  rw [hpush, hQ, map_zero, map_zero]

end Divisor

section Concrete

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The index-`(j+1)` component of `c(ℳ) * b` for `ℳ` of rank one: only the indices `0` and `1`
of `c(ℳ)` contribute. -/
theorem chernFamily_rankOne_mul_apply_succ (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    (b : GradedCapFamily (chowGroup C sX)) (k : ℤ) (j : ℕ) (x : chowGroup C sX k) :
    (chernFamily C sX M 1 * b) k (j + 1) x =
      capTo (chernFamily C sX M 1) 1 (by push_cast; ring) (b k j x) + b k (j + 1) x := by
  rw [gradedCap_mul_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero,
    zero_add, convolveTerm_of_le _ _ _ (Nat.le_succ j), convolveTerm_of_le _ _ _ le_rfl,
    capTo_congr_index _ (show j + 1 - j = 1 by omega),
    capTo_congr_index _ (show j + 1 - (j + 1) = 0 by omega), capTo_def (i := 0),
    chernFamily_apply_zero, gradedCap_one_apply_zero, gradedDegreeCast_gradedDegreeCast]
  · rfl
  · intro l hl
    have hlj : l < j := Finset.mem_range.mp hl
    rw [convolveTerm_of_le _ _ _ (by omega)]
    exact capTo_of_eq_zero _ _ (chernCapFamilyOnChow_of_gt C (chernCap C) sX M 1 _ (by omega)) _

/-- The index-`0` component of `c(ℳ) * b` is that of `b`. -/
theorem chernFamily_mul_apply_zero (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r]
    (b : GradedCapFamily (chowGroup C sX)) (k : ℤ) (x : chowGroup C sX k) :
    (chernFamily C sX M r * b) k 0 x = b k 0 x := by
  rw [gradedCap_mul_apply, Finset.sum_range_one, convolveTerm_of_le _ _ _ le_rfl, capTo_def,
    chernFamily_apply_zero, gradedCap_one_apply_zero, gradedDegreeCast_gradedDegreeCast]
  rfl

/-- The cap products with `c(ℳ)` of a module of rank `r` vanish in indices `j > r`. -/
private theorem chernFamily_apply_of_gt (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] (k : ℤ) {j : ℕ}
    (h : ¬ j ≤ r) (α : chowGroup C sX k) : chernFamily C sX M r k j α = 0 := by
  dsimp only [chernFamily]
  rw [chernCapFamilyOnChow_of_gt C (chernCap C) sX M r k h]
  rfl

/-- The cap products with `c(ℳ)` of a module of rank `n + 1` in indices `j ≤ n + 1` are the
Chern class cap products. -/
private theorem chernFamily_apply_of_lt (M : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (n + 1)] (k : ℤ)
    (j : Fin (n + 1 + 1)) (α : chowGroup C sX k) :
    chernFamily C sX M (n + 1) k j α = bundleChernCapFamily M n C sX k α j := by
  dsimp only [chernFamily]
  rw [chernCapFamilyOnChow_of_le C (chernCap C) sX M (n + 1) k (Nat.lt_succ_iff.mp j.isLt)]
  rfl

/-- `c₁(ℳ) ∩ -` of a module of rank one, read in the total Chern class, is the cap product with
the invertible module `ℳ`. -/
theorem capTo_chernFamily_rankOne (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1] {k n : ℤ}
    (h : k - ((1 : ℕ) : ℤ) = n) (y : chowGroup C sX k) :
    haveI := isInvertible_of_rank_one M
    capTo (chernFamily C sX M 1) 1 h y =
      firstChernClassCapChow C n sX M (chowGroupCast C sX (by omega) y) := by
  have := isInvertible_of_rank_one M
  rw [capTo_def]
  dsimp only [chernFamily]
  rw [chernCapFamilyOnChow_of_le C (chernCap C) sX M 1 k le_rfl]
  have h1 := firstChern_eq_bundleChernCapFamily_one M 0 C sX k y
  have h2 := firstChern_one sX (topHalf C) M k y
  refine eq_of_heq ((gradedDegreeCast_heq _ _).trans ?_)
  change bundleChernCapFamily M 0 C sX k y ⟨1, by omega⟩ ≍ _
  refine ((chowGroupCast_heq C sX _ _).symm.trans (heq_of_eq h1.symm)).trans ?_
  refine (heq_of_eq h2).trans ?_
  exact heq_apply_of_degree C sX sX (fun d => d + 1) (fun d => d)
    (fun d => firstChernClassCapChow C d sX M) (by omega)
    ((chowGroupCast_heq C sX _ y).trans (chowGroupCast_heq C sX _ y).symm)

/-- **The Chern classes of the middle term along an invertible subsheaf, as a family.** For a
short exact sequence `0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` with `ℳ` of rank one, `𝒢` of rank `n + 2` and `𝒬`
of rank `n + 1`, the family `(c_j(𝒬) ∩ α + c₁(ℳ) ∩ c_{j-1}(𝒬) ∩ α)_j` is the family of Chern
class cap products of `α` for `𝒢`: it satisfies the characterization of Stacks 02U6 on `P(𝒢)`. -/
theorem bundleChernCapFamily_eq_add_capShift (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (n + 1)]
    (k : ℤ) (α : chowGroup C sX k) :
    haveI := isInvertible_of_rank_one S.X₁
    (fun j : Fin (n + 1 + 1 + 1) => chernFamily C sX S.X₃ (n + 1) k j α +
        capShift C sX (fun d => firstChernClassCapChow C d sX S.X₁) k
          (fun j => chernFamily C sX S.X₃ (n + 1) k j α) j) =
      bundleChernCapFamily S.X₂ (n + 1) C sX k α := by
  have := isInvertible_of_rank_one S.X₁
  have := isFiniteLocallyFree_of_rank S.X₂ (n + 1 + 1)
  have := isFiniteLocallyFree_of_rank S.X₃ (n + 1)
  have : Epi S.g := hS.epi_g
  obtain ⟨⟨eTw⟩, L, hL, s, hD, e, he, ⟨eT⟩⟩ := subbundleHolds S hS n
  let := hL
  have := flat_bundleProj S.X₂ (n + 1)
  have := locallyOfFiniteType_bundleProj S.X₂ (n + 1)
  have := flat_bundleProj S.X₃ n
  have := locallyOfFiniteType_bundleProj S.X₃ n
  have hι : bundleEmbedding S.g ≫ (bundleProj S.X₂ ≫ sX) = bundleProj S.X₃ ≫ sX := by
    rw [bundleEmbedding_comp_bundleProj_assoc]
  refine eq_bundleChernCapFamily_of_isChernCapFamily S.X₂ (n + 1) C sX k α _ ⟨?_, ?_⟩
  · change chowGroupCast C sX _ (chernFamily C sX S.X₃ (n + 1) k 0 α + 0) = α
    rw [add_zero, chernFamily_apply_zero, gradedCap_one_apply_zero]
    exact eq_of_heq ((chowGroupCast_heq C sX _ _).trans (gradedDegreeCast_heq _ α))
  · refine projectiveBundleChernRelation_add_capShift C sX (bundleProj S.X₂ ≫ sX)
      (bundleProj S.X₂) rfl (bundleProj S.X₃ ≫ sX) (bundleProj S.X₃) rfl n
      (relativeDimension_bundleProj S.X₂ (n + 1)) (relativeDimension_bundleProj S.X₃ n)
      (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
      (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
      (bundleTwistCap S.X₂ C sX) (bundleTwistCap S.X₃ C sX) (bundleEmbedding S.g) hι
      (fun d ↦ firstChernClassCapChow C d sX S.X₁)
      (fun d y ↦ properChowPushforward_firstChernClassCapChow_of_isClosedImmersion C _ _
        (bundleEmbedding S.g) hι (bundleTwist S.X₂) (bundleTwist S.X₃) eTw.symm d y)
      (fun k α d hd y hy z hz w hw ↦ cap_flatPullback_eq_of_divisor C sX
        (bundleProj S.X₂ ≫ sX) (bundleProj S.X₂) rfl (bundleProj S.X₃ ≫ sX) (bundleProj S.X₃)
        rfl n (relativeDimension_bundleProj S.X₂ (n + 1)) (relativeDimension_bundleProj S.X₃ n)
        (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
        (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
        (bundleEmbedding S.g) hι (bundleEmbedding_comp_bundleProj S.g) L s hD e he
        (bundleTwist S.X₂) S.X₁ eT k α d hd y hy z hz w hw)
      k _ ?_ ?_
    · exact chernFamily_apply_of_gt C sX S.X₃ (n + 1) k (by omega) α
    · have hfam : (fun j : Fin (n + 1 + 1) => chernFamily C sX S.X₃ (n + 1) k j α) =
          bundleChernCapFamily S.X₃ n C sX k α :=
        funext fun j => chernFamily_apply_of_lt C sX S.X₃ n k j α
      rw [hfam]
      exact (isChernCapFamily_bundleChernCapFamily S.X₃ n C sX k α).2

/-- **Stacks 02UH, on the Chern class cap products.** For a short exact sequence
`0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` of modules on `X` with `ℒ` invertible and `ℰ`, `ℱ` finite locally free of
ranks `r + 1` and `r`, the total Chern classes satisfy

  `c(ℰ) = c(ℒ) c(ℱ)`

in the ring of graded cap families on the Chow groups of `X`: for every `k`, every `α ∈ A_k(X)`
and every `m`, `c_m(ℰ) ∩ α = c_m(ℱ) ∩ α + c₁(ℒ) ∩ c_{m-1}(ℱ) ∩ α`. -/
theorem chernFamily_eq_mul_of_shortExact_of_isInvertible (S : ShortComplex X.Modules)
    (exact_S : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₁]
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (r + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r] :
    haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible S.X₁
    chernFamily C sX S.X₂ (r + 1) = chernFamily C sX S.X₁ 1 * chernFamily C sX S.X₃ r := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible S.X₁
  rcases r with _ | n
  · -- the quotient vanishes and `ℒ ⟶ ℰ` is an isomorphism
    have hz : IsZero S.X₃ := Stacks.WeilCohomology.isZero_of_isFiniteLocallyFreeOfRank_zero _ ‹_›
    have : IsIso S.f := exact_S.isIso_f_iff.2 hz
    rw [chernFamily_of_rank_zero C sX S.X₃, mul_one]
    exact chernFamily_congr C sX S.X₁ 1 (asIso S.f).symm rfl
  funext k m
  refine AddMonoidHom.ext fun α => ?_
  rcases m with _ | j
  · rw [chernFamily_mul_apply_zero, chernFamily_apply_zero, chernFamily_apply_zero]
  rw [chernFamily_rankOne_mul_apply_succ, capTo_chernFamily_rankOne]
  by_cases hj : j + 1 ≤ n + 1 + 1
  · have hfam := congrFun (bundleChernCapFamily_eq_add_capShift C sX S exact_S n k α)
      ⟨j + 1, Nat.lt_succ_of_le hj⟩
    dsimp only at hfam
    have hlhs : chernFamily C sX S.X₂ (n + 1 + 1) k (j + 1) α =
        bundleChernCapFamily S.X₂ (n + 1) C sX k α ⟨j + 1, Nat.lt_succ_of_le hj⟩ :=
      chernFamily_apply_of_lt C sX S.X₂ (n + 1) k ⟨j + 1, Nat.lt_succ_of_le hj⟩ α
    rw [hlhs, ← hfam]
    exact add_comm _ _
  · rw [chernFamily_apply_of_gt C sX S.X₂ (n + 1 + 1) k hj,
      chernFamily_apply_of_gt C sX S.X₃ (n + 1) k (by omega),
      chernFamily_apply_of_gt C sX S.X₃ (n + 1) k (by omega), map_zero, map_zero, add_zero]

/-- **The total Chern class of a module isomorphic to `𝒪_X` is `1`**: `c₁(𝒪_X) ∩ α = 0`,
Stacks 02SP. -/
theorem chernFamily_eq_one_of_iso_unit (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) : chernFamily C sX M 1 = 1 := by
  have := isInvertible_of_rank_one M
  funext k i
  refine AddMonoidHom.ext fun α => ?_
  rcases i with _ | _ | i
  · rw [chernFamily_apply_zero]
  · have h := capTo_chernFamily_rankOne C sX M (k := k) (n := k - ((1 : ℕ) : ℤ)) rfl α
    rw [capTo_def, gradedDegreeCast_rfl] at h
    rw [h, firstChernClassCapChow_congr C sX _ e,
      show (1 : GradedCapFamily (chowGroup C sX)) k (0 + 1) = 0 from
        gradedCap_one_of_ne (by omega) k, AddMonoidHom.zero_apply]
    induction (chowGroupCast C sX (show k = k - ((1 : ℕ) : ℤ) + 1 by omega) α) using
      QuotientAddGroup.induction_on with
    | H c => exact (firstChernClassCapOfInvertible_unit C sX _ c).trans rfl
  · dsimp only [chernFamily]
    rw [chernCapFamilyOnChow_of_gt C (chernCap C) sX M 1 k (by omega),
      gradedCap_one_of_ne (by omega)]

/-- **Stacks 02UG, on the Chern class cap products.** For a short exact sequence
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` of modules on `X` with `ℰ`, `ℱ` finite locally free of ranks `r + 1`
and `r`, the total Chern classes agree,

  `c(ℰ) = c(ℱ)`,

in the ring of graded cap families on the Chow groups of `X`: `c_{r+1}(ℰ) ∩ α = 0` and
`c_j(ℰ) ∩ α = c_j(ℱ) ∩ α` for `j ≤ r`, for every class `α`. -/
theorem chernFamily_eq_of_shortExact_of_iso_unit (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (e : S.X₁ ≅ SheafOfModules.unit X.ringCatSheaf) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (r + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r] :
    chernFamily C sX S.X₂ (r + 1) = chernFamily C sX S.X₃ r := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ 1 :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm
      (isFiniteLocallyFreeOfRank_one_of_isInvertible _)
  have := isInvertible_of_rank_one S.X₁
  rw [chernFamily_eq_mul_of_shortExact_of_isInvertible C sX S hS r,
    chernFamily_eq_one_of_iso_unit C sX S.X₁ e, one_mul]

/-- **Stacks 02UG, on the Chern class cap products.** For a short exact sequence
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` of modules on `X` with `ℰ`, `ℱ` finite locally free of ranks `r + 1`
and `r`,

  `c_{r+1}(ℰ) ∩ α = 0`  and  `c_j(ℰ) ∩ α = c_j(ℱ) ∩ α`, `j = 0, …, r`,

for every `k` and every `α ∈ A_k(X)`. -/
theorem chernCap_eq_of_shortExact_of_iso_unit (S : ShortComplex X.Modules)
    (exact_S : S.ShortExact) (e : S.X₁ ≅ SheafOfModules.unit X.ringCatSheaf) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (r + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r] :
    (∀ (k : ℤ) (α : chowGroup C sX k), chernCap C (r + 1) sX S.X₂ k (Fin.last (r + 1)) α = 0) ∧
      ∀ (k : ℤ) (j : Fin (r + 1)) (α : chowGroup C sX k),
        chernCap C (r + 1) sX S.X₂ k j.castSucc α = chernCap C r sX S.X₃ k j α := by
  have h := chernFamily_eq_of_shortExact_of_iso_unit C sX S exact_S e r
  refine ⟨fun k α => ?_, fun k j α => ?_⟩
  · have h' := congrArg (fun c : GradedCapFamily (chowGroup C sX) => c k (r + 1) α) h
    dsimp only [chernFamily] at h'
    rw [chernCapFamilyOnChow_of_le C (chernCap C) sX S.X₂ (r + 1) k le_rfl,
      chernCapFamilyOnChow_of_gt C (chernCap C) sX S.X₃ r k (by omega)] at h'
    exact h'
  · have h' := congrArg (fun c : GradedCapFamily (chowGroup C sX) => c k j α) h
    dsimp only [chernFamily] at h'
    rw [chernCapFamilyOnChow_of_le C (chernCap C) sX S.X₂ (r + 1) k (by omega),
      chernCapFamilyOnChow_of_le C (chernCap C) sX S.X₃ r k (Nat.lt_succ_iff.mp j.isLt)] at h'
    exact h'

end Concrete

end Stacks.Chow.GenuineChern

end
