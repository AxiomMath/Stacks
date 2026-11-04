module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClassFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinChernCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.WeakBivariantCriterionProof
public import StacksCore.Tactic.StacksAttribute

/-!
# `f^!(c_i(ℰ) ∩ [Y]) = c_i(f^*ℰ) ∩ [X]`

Let `f : X ⟶ Y` be a local complete intersection morphism of schemes locally of finite type over
the base of Situation 02QL with Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` (Stacks 0FF3). This file proves the
last assertion of Stacks 0FF8: for `Y` satisfying the conditions of Stacks 0FE3 and `ℰ` a finite
locally free `𝒪_Y`-module,

  `f^!(c_i(ℰ) ∩ [Y]) = c_i(f^*ℰ) ∩ [X]`   and   `f^!(ch(ℰ) ∩ [Y]) = ch(f^*ℰ) ∩ [X]`.

The classes are read on the connected components (Stacks 0FE0): `c_i(ℰ) ∩ [Y]` is the family
`(c_i(ℰ) ∩ [Y_j]_{m+i})_{j,m}`, and `f^!` acts by `Stacks.Chow.completedCap`.

## The argument

As in the source, the assertion follows from the first two. An entry `c ∈ A^q(X_k ⟶ Y_j)` of
`f^!` satisfies `c ∩ (c_i(ℰ) ∩ α) = c_i(ℰ) ∩ (c ∩ α)` because the Chern classes of `ℰ|_{Y_j}`
commute with every bivariant class (the ingredient of the first assertion,
`Stacks.Chow.TotalChowClass.commutesWith_totalChernClassOfModule`), and `c_i(ℰ)` acts on
`X_k ×_{Y_j} Y_j` as `res(c_i(ℰ)) = c_i(f^*ℰ)` (Stacks 0B7F,
`Stacks.Chow.res_totalChernClassOfModule`). This gives
`f^!(c_i(ℰ) ∩ α) = c_i(f^*ℰ) ∩ f^!α` for every componentwise family `α`
(`Stacks.Chow.completedCap_componentClassCap`), and the second assertion `f^![Y] = [X]` finishes.
The Chern character `ch_p(ℰ) = P_p(ℰ)/p!` is handled the same way with the power sums `P_p`.

## Main definitions

* `Stacks.Chow.componentClassCap` — `x_i ∩ α` on the connected components, for a total class `x`.

## Main results

* `Stacks.Chow.completedCap_componentClassCap` — `c ∩ (x_i ∩ α) = res(x)_i ∩ (c ∩ α)`.
* `Stacks.Chow.lciGysinClass_completedCap_chernClassOfModule_cap` — **Stacks 0FF8**,
  `f^!(c_i(ℰ) ∩ [Y]) = c_i(f^*ℰ) ∩ [X]`.
* `Stacks.Chow.lciGysinClass_completedCap_chernCharacterOfModule_cap` — **Stacks 0FF8**,
  `f^!(ch_p(ℰ) ∩ [Y]) = ch_p(f^*ℰ) ∩ [X]` in `CH_*(X) ⊗ 𝐐`.

## References

* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section HEqLemmas

variable {C : ChowSituation.{u}}

/-- The cap operation of a bivariant class in two equal degrees. -/
theorem BivariantClass.cap_heq_of_degree_eq {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ} (c : BivariantClass C G sX sY f hf p)
    {T : Scheme.{u}}
    (t : T ⟶ Y) [LocallyOfFiniteType t] {k k' : ℤ} (hk : k = k') {α : chowGroup C (t ≫ sY) k}
    {α' : chowGroup C (t ≫ sY) k'} (hα : α ≍ α') : c.cap t k α ≍ c.cap t k' α' := by
  subst hk
  cases hα
  rfl

end HEqLemmas

section ClassCap

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  [IsLocallyNoetherian Y]

/-- **The operation of a Chow cohomology class on a family of classes on the connected
components**: `(x ∩ α)_{j,m} = x ∩ α_{j, m+i} ∈ CH_m(Y_j)` for `x ∈ A^i(Y)`, the operation of `x`
on the test scheme `Y_j ⟶ Y`. For `α = [Y]` read on the components and `x = c_i(ℰ)` this is
`c_i(ℰ) ∩ [Y]`. -/
def componentClassCap (i : ℕ) (x : chowCohomologyComponent C (gysinSystemOfInvertible C) sY i)
    (α : ∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
      chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m)
    (j : _root_.ConnectedComponents Y) (m : ℤ) :
    chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m :=
  chowGroupDegreeEquiv C _ (by ring : m + i - i = m)
    (x.idRule C sY (gysinSystemOfInvertible C) (Y.connectedComponentOpens j).ι (m + i)
      (α j (m + i)))

/-- `x ↦ x ∩ α` as an additive map, for the rational extension. -/
def componentClassCapHom (i : ℕ)
    (α : ∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
      chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sY i →+
      (∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
        chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m) where
  toFun x := componentClassCap C sY i x α
  map_zero' := by
    funext j m
    have h := map_zero (BivariantClass.idRuleHom C (gysinSystemOfInvertible C) sY
      (Y.connectedComponentOpens j).ι (m + i) (p := (i : ℤ)))
    rw [BivariantClass.idRuleHom_apply] at h
    simp only [componentClassCap, h, AddMonoidHom.zero_apply, map_zero, Pi.zero_apply]
  map_add' x y := by
    funext j m
    have h := map_add (BivariantClass.idRuleHom C (gysinSystemOfInvertible C) sY
      (Y.connectedComponentOpens j).ι (m + i) (p := (i : ℤ))) x y
    simp only [BivariantClass.idRuleHom_apply] at h
    simp only [componentClassCap, h, AddMonoidHom.add_apply, map_add, Pi.add_apply]

end ClassCap

section Entry

variable {C : ChowSituation.{u}} {X Y X' W : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (ι : W ⟶ Y) [IsOpenImmersion ι] (ιX : X' ⟶ X) [IsOpenImmersion ιX] (u : X' ⟶ W)
  [LocallyOfFiniteType u] (hu : u ≫ (ι ≫ sY) = ιX ≫ sX) (hsq : u ≫ ι = ιX ≫ f)

include hsq in
/-- **The commutation on one entry.** For `c ∈ A^p(X' ⟶ W)` over open subschemes `X' ⊆ X`,
`W ⊆ Y` compatible with `f`, and a total class `x` of `Y` whose restriction to `W` commutes with
every bivariant class, `c ∩ (x_i ∩ a) = res_f(x)_i ∩ (c ∩ a)`, both read on `X'`. -/
theorem chowPushforwardOfIso_cap_idRule_eq (x : TotalChowClass C sY)
    (hx : ∀ {X₁ : Scheme.{u}} (g₁ : X₁ ⟶ W) [LocallyOfFiniteType g₁] {q : ℤ}
      (c : BivariantClass C (gysinSystemOfInvertible C) (g₁ ≫ (ι ≫ sY)) (ι ≫ sY) g₁ rfl q),
      (TotalChowClass.res ι rfl x).CommutesWith C (ι ≫ sY) g₁ c (𝟙 W) (ι ≫ sY)
        (Category.id_comp _))
    (i : ℕ) {p : ℤ} (e : BivariantClass C (gysinSystemOfInvertible C) (ιX ≫ sX) (ι ≫ sY) u hu p)
    (a : ∀ m : ℤ, chowGroup C (ι ≫ sY) m) (n : ℤ) :
    chowPushforwardOfIso C (pullback.fst u (𝟙 W) ≫ (ιX ≫ sX)) (ιX ≫ sX) (pullback.fst u (𝟙 W))
        rfl n (chowGroupDegreeEquiv C _ (by ring : (n + p) - p = n)
          (e.cap (𝟙 W) (n + p) (chowGroupCongr C (Category.id_comp _).symm (n + p)
            (chowGroupDegreeEquiv C _ (by ring : n + p + i - i = n + p)
              ((x i).idRule C sY (gysinSystemOfInvertible C) ι (n + p + i) (a (n + p + i))))))) =
      chowGroupDegreeEquiv C _ (by ring : n + i - i = n)
        ((TotalChowClass.res f hf x i).idRule C sX (gysinSystemOfInvertible C) ιX (n + i)
          (chowPushforwardOfIso C (pullback.fst u (𝟙 W) ≫ (ιX ≫ sX)) (ιX ≫ sX)
            (pullback.fst u (𝟙 W)) rfl (n + i)
            (chowGroupDegreeEquiv C _ (by ring : (n + i + p) - p = n + i)
              (e.cap (𝟙 W) (n + i + p) (chowGroupCongr C (Category.id_comp _).symm (n + i + p)
                (a (n + i + p))))))) := by
  set y := TotalChowClass.res ι rfl x
  set fst := pullback.fst u (𝟙 W)
  have hK : n + p + i = n + i + p := by ring
  -- the two arguments `a` in equal degrees
  have ha : chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p + i) (a (n + p + i)) ≍
      chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + i + p) (a (n + i + p)) :=
    (chowGroupCongr_heq C _ _ _).trans
      ((congr_arg_heq a hK).trans (chowGroupCongr_heq C _ _ _).symm)
  -- the structure morphisms over the base
  have hZs : fst ≫ (ιX ≫ sX) = (fst ≫ (u ≫ ι)) ≫ sY := by
    rw [← hu]; simp only [Category.assoc]
  have hBs : ιX ≫ sX = (u ≫ ι) ≫ sY := by rw [← hu, Category.assoc]
  have hws : fst ≫ (ιX ≫ sX) = (pullback.snd u (𝟙 W) ≫ 𝟙 W) ≫ (ι ≫ sY) := by
    rw [← hu, ← Category.assoc, pullback.condition]
  have hwg : (pullback.snd u (𝟙 W) ≫ 𝟙 W) ≫ ι = fst ≫ (u ≫ ι) := by
    rw [← Category.assoc, pullback.condition]
  -- the middle class
  set Zm : chowGroup C ((fst ≫ (u ≫ ι)) ≫ sY) (n + i) := chowGroupCongr C hZs (n + i)
    (chowGroupDegreeEquiv C _ (by ring : (n + i + p) - p = n + i)
      (e.cap (𝟙 W) (n + i + p) (chowGroupCongr C (Category.id_comp _).symm (n + i + p)
        (a (n + i + p))))) with hZm
  have hZm_heq : Zm ≍ e.cap (𝟙 W) (n + i + p) (chowGroupCongr C (Category.id_comp _).symm
      (n + i + p) (a (n + i + p))) :=
    (chowGroupCongr_heq C _ _ _).trans (chowGroupDegreeEquiv_heq C _ _ _)
  have hfac := properPushforwardFactorsThroughRationalEquivalence_of_isIso C
    ((fst ≫ (u ≫ ι)) ≫ sY) ((u ≫ ι) ≫ sY) fst (by simp [Category.assoc]) (n + i)
  have hfacp := properPushforwardFactorsThroughRationalEquivalence_of_isIso C
    ((fst ≫ (u ≫ ι)) ≫ sY) ((u ≫ ι) ≫ sY) fst (by simp [Category.assoc]) (n + i - i)
  -- left side
  have hA : chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p)
      (chowGroupDegreeEquiv C _ (by ring : n + p + i - i = n + p)
        ((x i).idRule C sY (gysinSystemOfInvertible C) ι (n + p + i) (a (n + p + i)))) ≍
      (y i).idRule C (ι ≫ sY) (gysinSystemOfInvertible C) (𝟙 W) (n + p + i)
        (chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p + i) (a (n + p + i))) := by
    refine (chowGroupCongr_heq C _ _ _).trans ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
    refine HEq.symm ((TotalChowClass.op_res_apply ι rfl x (𝟙 W) (n + p + i) i _
      (chowGroupCongr C (by simp) (n + p + i) (a (n + p + i)))
      ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm)).trans ?_)
    exact IdentityCapRule.heq_congr C sY _ (Category.id_comp ι) rfl (chowGroupCongr_heq C _ _ _)
  have hB := e.cap_heq_of_degree_eq (𝟙 W) (by ring : n + p = n + p + i - i) hA
  have hCm := TotalChowClass.cap_idRule_heq_of_commutesWith y hx i u hu
    (BivariantChowClass.equivBivariantClass.symm e) (𝟙 W) (n + p + i)
    (chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p + i) (a (n + p + i)))
    (pullback.snd u (𝟙 W) ≫ 𝟙 W) rfl HEq.rfl
    (chowGroupCongr C hws (n + p + i - p) (e.cap (𝟙 W) (n + p + i)
      (chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p + i) (a (n + p + i)))))
    (chowGroupCongr_heq C _ _ _)
  have hD := TotalChowClass.op_res_apply ι rfl x (pullback.snd u (𝟙 W) ≫ 𝟙 W) (n + p + i - p) i
    (chowGroupCongr C hws (n + p + i - p) (e.cap (𝟙 W) (n + p + i)
      (chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p + i) (a (n + p + i)))))
    (chowGroupCongr C (by rw [hws]; simp only [Category.assoc]) (n + p + i - p)
      (e.cap (𝟙 W) (n + p + i)
        (chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p + i) (a (n + p + i)))))
    ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm)
  have hE : (x i).idRule C sY (gysinSystemOfInvertible C) ((pullback.snd u (𝟙 W) ≫ 𝟙 W) ≫ ι)
      (n + p + i - p) (chowGroupCongr C (by rw [hws]; simp only [Category.assoc])
        (n + p + i - p) (e.cap (𝟙 W) (n + p + i)
          (chowGroupCongr C (Category.id_comp (ι ≫ sY)).symm (n + p + i) (a (n + p + i))))) ≍
      (x i).idRule C sY (gysinSystemOfInvertible C) (fst ≫ (u ≫ ι)) (n + i) Zm :=
    IdentityCapRule.heq_congr C sY _ hwg (by ring) ((chowGroupCongr_heq C _ _ _).trans
      ((e.cap_heq_of_degree_eq (𝟙 W) hK ha).trans hZm_heq.symm))
  have hLcap := hB.trans (hCm.trans (hD.trans hE))
  have hF : chowPushforwardOfIso C (fst ≫ (ιX ≫ sX)) (ιX ≫ sX) fst rfl n
      (chowGroupDegreeEquiv C _ (by ring : (n + p) - p = n)
        (e.cap (𝟙 W) (n + p) (chowGroupCongr C (Category.id_comp _).symm (n + p)
          (chowGroupDegreeEquiv C _ (by ring : n + p + i - i = n + p)
            ((x i).idRule C sY (gysinSystemOfInvertible C) ι (n + p + i) (a (n + p + i))))))) ≍
      properChowPushforward C ((fst ≫ (u ≫ ι)) ≫ sY) ((u ≫ ι) ≫ sY) fst
        (by simp [Category.assoc]) (n + i - i) hfacp
        ((x i).idRule C sY (gysinSystemOfInvertible C) (fst ≫ (u ≫ ι)) (n + i) Zm) :=
    properChowPushforward_heq_of_eq C fst hZs hBs _ _ (by ring) _ _
      ((chowGroupDegreeEquiv_heq C _ _ _).trans hLcap)
  have hG := BivariantClass.idRule_properNaturality C sY (gysinSystemOfInvertible C) (x i)
    (u ≫ ι) fst (n + i) hfac hfacp Zm
  have hH : chowGroupDegreeEquiv C _ (by ring : n + i - i = n)
      ((TotalChowClass.res f hf x i).idRule C sX (gysinSystemOfInvertible C) ιX (n + i)
        (chowPushforwardOfIso C (fst ≫ (ιX ≫ sX)) (ιX ≫ sX) fst rfl (n + i)
          (chowGroupDegreeEquiv C _ (by ring : (n + i + p) - p = n + i)
            (e.cap (𝟙 W) (n + i + p) (chowGroupCongr C (Category.id_comp _).symm (n + i + p)
              (a (n + i + p))))))) ≍
      (x i).idRule C sY (gysinSystemOfInvertible C) (u ≫ ι) (n + i)
        (properChowPushforward C ((fst ≫ (u ≫ ι)) ≫ sY) ((u ≫ ι) ≫ sY) fst
          (by simp [Category.assoc]) (n + i) hfac Zm) := by
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    refine (TotalChowClass.op_res_apply f hf x ιX (n + i) i _
      (chowGroupCongr C (by rw [Category.assoc, hf]) (n + i) _)
      (chowGroupCongr_heq C _ _ _).symm).trans ?_
    exact IdentityCapRule.heq_congr C sY _ hsq.symm rfl ((chowGroupCongr_heq C _ _ _).trans
      (properChowPushforward_heq_of_eq C fst hZs hBs _ _ rfl _ _
        ((chowGroupDegreeEquiv_heq C _ _ _).trans hZm_heq.symm)))
  exact eq_of_heq (hF.trans ((heq_of_eq hG).symm.trans hH.symm))

end Entry

section Commute

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- `α ↦ c ∩ α` as an additive map, for the rational extension. -/
def completedCapHom (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) :
    (∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
      chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m) →+
      (∀ (k : _root_.ConnectedComponents X) (n : ℤ),
        chowGroup C ((X.connectedComponentOpens k).ι ≫ sX) n) where
  toFun α := completedCap C sX sY f hf c α
  map_zero' := by
    funext k n
    simp [completedCap]
  map_add' α β := by
    funext k n
    simp [completedCap, Finset.sum_add_distrib]

/-- **`c ∩ (x_i ∩ α) = res(x)_i ∩ (c ∩ α)`** for a completed class `c ∈ A^*(X ⟶ Y)^∧`, a family `α`
of classes on the connected components of `Y`, and a total class `x` of `Y` whose restrictions to
the connected components commute with every bivariant class. -/
theorem completedCap_componentClassCap (x : TotalChowClass C sY)
    (hx : ∀ (j : _root_.ConnectedComponents Y) {X₁ : Scheme.{u}}
      (g₁ : X₁ ⟶ (Y.connectedComponentOpens j : Scheme.{u})) [LocallyOfFiniteType g₁] {q : ℤ}
      (c : BivariantClass C (gysinSystemOfInvertible C)
        (g₁ ≫ ((Y.connectedComponentOpens j).ι ≫ sY)) ((Y.connectedComponentOpens j).ι ≫ sY) g₁
        rfl q),
      (TotalChowClass.res (Y.connectedComponentOpens j).ι rfl x).CommutesWith C
        ((Y.connectedComponentOpens j).ι ≫ sY) g₁ c (𝟙 _) ((Y.connectedComponentOpens j).ι ≫ sY)
        (Category.id_comp _))
    (i : ℕ) (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (α : ∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
      chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m)
    (k : _root_.ConnectedComponents X) (n : ℤ) :
    completedCap C sX sY f hf c (componentClassCap C sY i (x i) α) k n =
      componentClassCap C sX i (TotalChowClass.res f hf x i)
        (completedCap C sX sY f hf c α) k n := by
  classical
  unfold completedCap componentClassCap
  simp only [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact chowPushforwardOfIso_cap_idRule_eq f hf _ (X.connectedComponentOpens k).ι
    (f.resConnectedComponent k) (f.resConnectedComponent_comp_ι_comp hf k)
    (f.resConnectedComponent_comp_ι k) x (hx _) i (c k p) (α _) n

end Commute

section Gysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hfs : f ≫ sY = sX)
  (hf : IsLocalCompleteIntersectionMorphism f) (F : SmoothFactorization f) (E : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- `f^!` sends the fundamental classes `[Y_j]` to the fundamental classes `[X_k]`. -/
private theorem completedCap_lciGysinClass_eq_componentFundamentalClass
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] :
    completedCap C sX sY f hfs (lciGysinClass C sX sY f hfs hf F)
      (componentFundamentalClass C sY) = componentFundamentalClass C sX :=
  funext fun k => funext fun n =>
    lciGysinClass_completedCap_componentFundamentalClass C sX sY f hfs hf F hY k n

/-- **Stacks 0FF8, `f^!(c_i(ℰ) ∩ [Y]) = c_i(f^*ℰ) ∩ [X]`.** Let `f : X ⟶ Y` be a local complete
intersection morphism of schemes locally of finite type over `S` with Gysin map `f^!` of
Stacks 0FF3 (built from a factorization `F`), let `Y` satisfy the equivalent conditions of
Stacks 0FE3, and let `ℰ` be a finite locally free `𝒪_Y`-module of any rank, with Chern classes
`c_i` of Stacks 0ESW. Then

  `f^!(c_i(ℰ) ∩ [Y]) = c_i(f^*ℰ) ∩ [X]`,

the classes read on the connected components `X_k` of `X` (which determine a class on `X`,
`CH_n(X) = ∏_k CH_n(X_k)`), in every degree `n`: `c_i(ℰ) ∩ [Y]` is the family
`(c_i(ℰ) ∩ [Y_j]_{m+i})_{j,m}` (`Stacks.Chow.componentClassCap`), `f^!` acts on it by
`Stacks.Chow.completedCap`, and `[X]` is read as the family of fundamental classes `[X_k]`.

The source assumes `X` and `Y` satisfy the conditions of Stacks 0FE3, for example `Y`
Cohen–Macaulay; only the condition on `Y` is used. -/
@[stacks 0FF8 "third assertion: f^!(c_i(E) ∩ [Y]) = c_i(f^*E) ∩ [X] for the Gysin map of Tag 0FF3, \
E finite locally free of any rank (c_i of Tag 0ESW), read on the connected components of X in \
every degree; only the Tag 0FE3 condition on Y is assumed"]
theorem lciGysinClass_completedCap_chernClassOfModule_cap
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY)) (i : ℕ)
    (k : _root_.ConnectedComponents X) (n : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    completedCap C sX sY f hfs (lciGysinClass C sX sY f hfs hf F)
        (componentClassCap C sY i (chernClassOfModule C sY E i) (componentFundamentalClass C sY))
        k n =
      componentClassCap C sX i (chernClassOfModule C sX ((Scheme.Modules.pullback f).obj E) i)
        (componentFundamentalClass C sX) k n := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
  rw [← totalChernClassOfModule_apply C sY E i,
    ← totalChernClassOfModule_apply C sX ((Scheme.Modules.pullback f).obj E) i,
    completedCap_componentClassCap C sX sY f hfs _
      (fun j _ g₁ _ _ c => by
      have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree
        (Y.connectedComponentOpens j).ι E
      rw [res_totalChernClassOfModule C sY (Y.connectedComponentOpens j).ι rfl E]
      exact TotalChowClass.commutesWith_totalChernClassOfModule C _ g₁ c (𝟙 _) _
        (Category.id_comp _) _), res_totalChernClassOfModule C sY f hfs E,
    completedCap_lciGysinClass_eq_componentFundamentalClass C sX sY f hfs hf F hY]

/-- **Stacks 0FF8, `f^!(ch(ℰ) ∩ [Y]) = ch(f^*ℰ) ∩ [X]`.** In the situation of
`Stacks.Chow.lciGysinClass_completedCap_chernClassOfModule_cap`, for every `p`,

  `f^!(ch_p(ℰ) ∩ [Y]) = ch_p(f^*ℰ) ∩ [X]`   in `CH_*(X) ⊗ 𝐐`,

with `ch_p(ℰ) = P_p(ℰ)/p!` the Chern character of Stacks 0ESX
(`Stacks.Chow.chernCharacterOfModule`), the cap products of rational classes the rational
extensions of the integral ones, and the classes read on the connected components as in the
Chern class statement. -/
@[stacks 0FF8 "third assertion, for the Chern character: f^!(ch(E) ∩ [Y]) = ch(f^*E) ∩ [X] in \
CH_*(X) ⊗ Q, for every component ch_p(E) = P_p(E)/p! of Tag 0ESX, read on the connected \
components of X; only the Tag 0FE3 condition on Y is assumed"]
theorem lciGysinClass_completedCap_chernCharacterOfModule_cap
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY)) (p : ℕ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    LinearMap.lTensor ℚ
        (completedCapHom C sX sY f hfs (lciGysinClass C sX sY f hfs hf F)).toIntLinearMap
        (LinearMap.lTensor ℚ
          (componentClassCapHom C sY p (componentFundamentalClass C sY)).toIntLinearMap
          (chernCharacterOfModule C sY E p)) =
      LinearMap.lTensor ℚ
        (componentClassCapHom C sX p (componentFundamentalClass C sX)).toIntLinearMap
        (chernCharacterOfModule C sX ((Scheme.Modules.pullback f).obj E) p) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
  simp only [chernCharacterOfModule, LinearMap.lTensor_tmul]
  congr 1
  funext k n
  show completedCap C sX sY f hfs (lciGysinClass C sX sY f hfs hf F)
      (componentClassCap C sY p (modulePowerSumArbitraryRank C sY E p p)
        (componentFundamentalClass C sY)) k n =
    componentClassCap C sX p
      (modulePowerSumArbitraryRank C sX ((Scheme.Modules.pullback f).obj E) p p)
      (componentFundamentalClass C sX) k n
  rw [completedCap_componentClassCap C sX sY f hfs _
    (fun j _ g₁ _ _ c => by
      have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree
        (Y.connectedComponentOpens j).ι E
      rw [res_modulePowerSumArbitraryRank C sY (Y.connectedComponentOpens j).ι rfl E]
      exact TotalChowClass.commutesWith_modulePowerSumArbitraryRank C _ g₁ c (𝟙 _) _
        (Category.id_comp _) _ p), res_modulePowerSumArbitraryRank C sY f hfs E,
    completedCap_lciGysinClass_eq_componentFundamentalClass C sX sY f hfs hf F hY]

end Gysin

end Stacks.Chow

end
