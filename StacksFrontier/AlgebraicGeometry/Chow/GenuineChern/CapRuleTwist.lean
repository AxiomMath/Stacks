module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleComm
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassTwist
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass

/-!
# The Chern class cap products of a module whose projective bundle is twisted

Let `X` be locally of finite type over the base of chapter 42, `ℰ` and `ℰ'` finite locally free
of rank `r` and `ℒ` invertible on `X`, and suppose the projective bundle `π' : 𝐏(ℰ') ⟶ X` is that
of `ℰ` through an isomorphism `g` over `X` with `𝒪_{𝐏(ℰ')}(1) ≅ g^*𝒪_{𝐏(ℰ)}(1) ⊗ π'^*ℒ` — the
situation [Stacks, Tag 02NC] produces for `ℰ' = ℰ ⊗ ℒ`. Then for every `0 ≤ i ≤ r`

  `c_i(ℰ') ∩ α = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(ℰ) ∩ c₁(ℒ)^j ∩ α`

for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6], which is the
computation in the proof of [Stacks, Tag 02UD].

On `𝐏(ℰ')` the relation of Stacks 02U6 for `ℰ` holds with `ξ = c₁(g^*𝒪(1))`, the one for `ℰ'`
with `c₁(𝒪(1)) = ξ + x`, `x = c₁(π'^*ℒ)` ([Stacks, Tag 02SP]), and `ξ` commutes with `x`
([Stacks, Tag 02TJ]) while `x` commutes with `π'^*` ([Stacks, Tag 02SS]). The binomial algebra is
`Stacks.Chow.eq_binomialTransform_of_towerRelations`, and the uniqueness it consumes is the
injectivity half of [Stacks, Tag 02TX].

## Main results

* `Stacks.Chow.GenuineChern.chernCap_congr` — isomorphic modules have the same cap products.
* `Stacks.Chow.GenuineChern.alternatingTowerSum_extendFamily` — the relation of Stacks 02U6, read
  as the alternating sum of `Stacks.Chow.ChernClassTwist`.
* `Stacks.Chow.GenuineChern.bundleChernCapFamily_eq_binomialTransform` — the families of
  Stacks 02U6, rank `n + 1`.
* `Stacks.Chow.GenuineChern.chernCap_eq_sum_of_bundleIso` — the formula above.

## References

* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (C : ChowSituation.{u})

/-! ### Isomorphic modules -/

/-- **Isomorphic modules have the same Chern class cap products.** -/
theorem chernCap_congr {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {E E' : X.Modules} (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (e : E ≅ E') (k : ℤ) (j : Fin (r + 1)) (α : chowGroup C sX k) :
    chernCap C r sX E k j α = chernCap C r sX E' k j α := by
  have h := chernCap_flatPullback_heq C sX sX (𝟙 X) (Category.id_comp sX) 0
    (relativeDimension_identity X) E r E' (e.symm ≪≫ ((Scheme.Modules.pullbackId X).app E).symm)
    k j (flatPullbackFactorsThroughRationalEquivalence_id C sX k)
    (flatPullbackFactorsThroughRationalEquivalence_id C sX _) α
  rw [flatPullbackChow_id, flatPullbackChow_id, chernCap_chowGroupCast] at h
  refine eq_of_heq ((chowGroupCast_heq C sX _ _).symm.trans (h.symm.trans ?_))
  exact chowGroupCast_heq C sX _ _

/-! ### The relation of Stacks 02U6 as an alternating tower sum -/

section Tower

/-- A power of a cap operator, at heterogeneously equal arguments in equal degrees. -/
theorem capPow_heq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (O : ChernCapOperator C sP) {s s' : ℕ} {a a' m m' : ℤ} (h : a = m + s) (h' : a' = m' + s')
    (hs : s = s') (ha : a = a') (hm : m = m') {x : chowGroup C sP a} {x' : chowGroup C sP a'}
    (hx : x ≍ x') : capPow C sP O s a m h x ≍ capPow C sP O s' a' m' h' x' := by
  subst hs ha hm; cases hx; rfl

/-- **The descending tower of a cap operator is a power of it.** -/
theorem descentTower_towerStep {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (O : ChernCapOperator C sP) (D : ℤ) (e : ∀ j : ℕ, chowGroup C sP (D - (j : ℤ))) {m j : ℕ}
    (hj : j ≤ m) :
    descentTower (ChernCapOperator.towerStep C sP O D) e m j =
      capPow C sP O (m - j) (D - (j : ℤ)) (D - (m : ℤ)) (by omega) (e j) := by
  induction m, hj using Nat.le_induction with
  | base =>
    rw [descentTower_diag]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (capPow_heq C sP O (s := 0) (by simp) _ (by simp) rfl rfl HEq.rfl)
    rw [capPow_zero_apply]
    exact (chowGroupCast_heq C sP _ _).symm
  | succ m hm ih =>
    rw [descentTower_succ_of_le _ e hm, ih]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (capPow_heq C sP O (s := m - j + 1) (by push_cast; omega) _ (by omega)
      rfl rfl HEq.rfl)
    rw [capPow_succ_apply', ChernCapOperator.towerStep, chowGroupDegreeCast_apply]
    refine capOnChow_heq C sP O (by push_cast; ring) ?_
    refine (chowGroupCast_heq C sP _ _).trans ?_
    exact capPow_heq C sP O _ _ rfl rfl (by push_cast; ring) HEq.rfl

variable {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)

/-- A family indexed by `0 ≤ j ≤ r`, extended by zero to every `j : ℕ`. -/
def extendFamily {k : ℤ} (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))) :
    ∀ j : ℕ, chowGroup C sX (k - (j : ℤ)) :=
  fun j ↦ if h : j < r + 1 then c ⟨j, h⟩ else 0

/-- Below `r + 1` the extension by zero of a family agrees with the family. -/
theorem extendFamily_of_lt {k : ℤ} (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    {j : ℕ} (h : j < r + 1) : extendFamily C sX r c j = c ⟨j, h⟩ := by
  simp [extendFamily, h]

/-- **The relation of Stacks 02U6 is an alternating tower sum.** The alternating sum of
`Stacks.Chow.ChernClassTwist` for the tower of a cap operator on the bundle and the flat pullbacks
of a family is the left-hand side of the relation of Stacks 02U6. -/
theorem alternatingTowerSum_extendFamily (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))) :
    alternatingTowerSum (ChernCapOperator.towerStep C sP twist (bundleRelationDegree r k)) r
        (towerPullback (projectiveBundleTowerPullback C sX sP π hsP r hπ hfac k)
          (extendFamily C sX r c)) =
      chowGroupCast C sP (by simp only [bundleRelationDegree])
        (∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
          projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
            (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)) := by
  rw [alternatingTowerSum_def, Finset.sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul]
  congr 1
  rw [descentTower_towerStep C sP twist _ _ (by omega), towerPullback_apply,
    projectiveBundleChernTerm_eq_capPow]
  refine eq_of_heq ?_
  refine HEq.trans ?_ (chowGroupCast_heq C sP _ _).symm
  refine capPow_heq C sP twist _ _ (by omega) (by simp only [bundleRelationDegree]; omega)
    (by simp only [bundleRelationDegree]) ?_
  rw [extendFamily_of_lt C sX r c (by omega)]
  simp only [projectiveBundleTowerPullback, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  exact chowGroupCast_heq C sP _ _

/-- Additive cap operators have additive towers. -/
theorem towerStep_add {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (O₁ O₂ O₃ : ChernCapOperator C sP)
    (h : ∀ (m : ℤ) (y : chowGroup C sP (m + 1)),
      O₁.capOnChow C sP m y + O₂.capOnChow C sP m y = O₃.capOnChow C sP m y) (D : ℤ) (i : ℕ) :
    ChernCapOperator.towerStep C sP O₁ D i + ChernCapOperator.towerStep C sP O₂ D i =
      ChernCapOperator.towerStep C sP O₃ D i := by
  refine AddMonoidHom.ext fun x ↦ ?_
  simp only [AddMonoidHom.add_apply, ChernCapOperator.towerStep, chowGroupDegreeCast_apply, h]

/-- Commuting cap operators have commuting towers. -/
theorem towerStep_comm {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (O₁ O₂ : ChernCapOperator C sP)
    (h : ∀ (m : ℤ) (z : chowGroup C sP (m + 1 + 1)),
      O₁.capOnChow C sP m (O₂.capOnChow C sP (m + 1) z) =
        O₂.capOnChow C sP m (O₁.capOnChow C sP (m + 1) z)) (D : ℤ) (i : ℕ) :
    (ChernCapOperator.towerStep C sP O₁ D (i + 1)).comp (ChernCapOperator.towerStep C sP O₂ D i) =
      (ChernCapOperator.towerStep C sP O₂ D (i + 1)).comp
        (ChernCapOperator.towerStep C sP O₁ D i) := by
  refine AddMonoidHom.ext fun x ↦ ?_
  simp only [AddMonoidHom.comp_apply, ChernCapOperator.towerStep, chowGroupDegreeCast_apply]
  have key := h (D - ((i + 1 + 1 : ℕ) : ℤ))
    (chowGroupCast C sP (show D - (i : ℤ) = D - ((i + 1 + 1 : ℕ) : ℤ) + 1 + 1 by push_cast; ring) x)
  refine eq_of_heq ((HEq.trans ?_ (heq_of_eq key)).trans ?_)
  · refine capOnChow_heq C sP O₁ rfl ((chowGroupCast_heq C sP _ _).trans ?_)
    exact capOnChow_heq C sP O₂ (by push_cast; ring)
      ((chowGroupCast_heq C sP _ _).trans (chowGroupCast_heq C sP _ _).symm)
  · refine capOnChow_heq C sP O₂ rfl (HEq.symm ((chowGroupCast_heq C sP _ _).trans ?_))
    exact capOnChow_heq C sP O₁ (by push_cast; ring)
      ((chowGroupCast_heq C sP _ _).trans (chowGroupCast_heq C sP _ _).symm)

/-- **Stacks 02SS, read on the towers.** Flat pullback to the bundle intertwines the tower of
`c₁(ℒ) ∩ -` on `X` with the tower of `c₁(π^*ℒ) ∩ -` on the bundle. -/
theorem projectiveBundleTowerPullback_towerStep_invCap (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) (i : ℕ) :
    haveI := isInvertible_pullback π L
    (projectiveBundleTowerPullback C sX sP π hsP r hπ hfac k (i + 1)).comp
        (ChernCapOperator.towerStep C sX (invCap C sX L) k i) =
      (ChernCapOperator.towerStep C sP (invCap C sP ((Scheme.Modules.pullback π).obj L))
          (bundleRelationDegree r k) i).comp
        (projectiveBundleTowerPullback C sX sP π hsP r hπ hfac k i) := by
  have := isInvertible_pullback π L
  refine AddMonoidHom.ext fun x ↦ ?_
  simp only [AddMonoidHom.comp_apply, ChernCapOperator.towerStep, chowGroupDegreeCast_apply,
    projectiveBundleTowerPullback, AddEquiv.coe_toAddMonoidHom, projectiveBundlePullback]
  refine eq_of_heq ((chowGroupCast_heq C sP _ _).trans ?_)
  refine (flatPullbackChow_firstChernClassCapChow_heq C sP sX π hsP (r - 1) hπ hfac L _
    (Iso.refl _) (k - ((i + 1 : ℕ) : ℤ)) (chowGroupCast C sX (by push_cast; ring) x)
    (chowGroupCast C sP (by push_cast; ring)
      (flatPullbackChow C sP sX π hsP (r - 1) hπ (k - (i : ℤ)) (hfac _) x)) ?_).trans ?_
  · refine (chowGroupCast_heq C sP _ _).trans ?_
    exact flatPullbackChow_heq C sP sX π hsP (r - 1) hπ hfac (by push_cast; ring)
      (chowGroupCast_heq C sX _ x).symm
  · have hD : k - ((i + 1 : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ) =
        bundleRelationDegree r k - ((i + 1 : ℕ) : ℤ) := by
      simp only [bundleRelationDegree]; ring
    refine capOnChow_heq C sP (invCap C sP ((Scheme.Modules.pullback π).obj L)) hD ?_
    exact (chowGroupCast_heq C sP _ _).trans
      ((chowGroupCast_heq C sP _ _).trans (chowGroupCast_heq C sP _ _)).symm

end Tower

/-! ### The relation of Stacks 02U6 on the bundle of a twist -/

section Twist

/-- A twist of a module of rank `r` by an invertible module has rank `r`. -/
instance isFiniteLocallyFreeOfRank_sheafTensor {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) r :=
  mul_one r ▸ Stacks.Chow.isFiniteLocallyFreeOfRank_tensor hE
    (Stacks.Chow.isFiniteLocallyFreeOfRank_one_of_isInvertible L)

/-- A relation of Stacks 02U6 may be read in an equal degree, for heterogeneously equal
families. -/
theorem projectiveBundleChernRelation_congr {X P : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X)
    [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP) (r : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
    (twist : ChernCapOperator C sP) {k k' : ℤ} (hk : k = k')
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (c' : ∀ j : Fin (r + 1), chowGroup C sX (k' - (j : ℤ))) (hc : ∀ j, c j ≍ c' j)
    (h : ProjectiveBundleChernRelation C sX sP π hsP r hπ hfac twist k c) :
    ProjectiveBundleChernRelation C sX sP π hsP r hπ hfac twist k' c' := by
  subst hk
  obtain rfl : c = c' := funext fun j ↦ eq_of_heq (hc j)
  exact h

/-- **The relation of Stacks 02U6 for `ℰ`, transported to the bundle of `ℰ'`.** If `g` is a flat
map `𝐏(ℰ') ⟶ 𝐏(ℰ)` of relative dimension `0` over `X`, the family of `α` for `ℰ` satisfies the
relation of Stacks 02U6 on `𝐏(ℰ')` with `c₁(g^*𝒪_{𝐏(ℰ)}(1)) ∩ -` as twist: the pullback along `g`
carries the relation on `𝐏(ℰ)` to it, the summands corresponding by Stacks 02SS. -/
private theorem projectiveBundleChernRelation_bundleIso {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [Flat (bundleProj E)] [LocallyOfFiniteType (bundleProj E)] (E' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [Flat (bundleProj E')] [LocallyOfFiniteType (bundleProj E')]
    (g : bundle E' ⟶ bundle E) [LocallyOfFiniteType g] [Flat g]
    (hg : g ≫ bundleProj E = bundleProj E')
    (hf' : g ≫ (bundleProj E ≫ sX) = bundleProj E' ≫ sX)
    (hd' : AlgebraicGeometry.RelativeDimension g 0)
    (hfacP : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C (bundleProj E ≫ sX) sX
      (bundleProj E) rfl (n + 1 - 1) (relativeDimension_bundleProj E n) k)
    (hfacP' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C (bundleProj E' ≫ sX) sX
      (bundleProj E') rfl (n + 1 - 1) (relativeDimension_bundleProj E' n) k)
    (hfacg : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C (bundleProj E' ≫ sX)
      (bundleProj E ≫ sX) g hf' 0 hd' k)
    (k : ℤ) (α : chowGroup C sX k) :
    haveI := isInvertible_pullback g (bundleTwist E)
    ProjectiveBundleChernRelation C sX (bundleProj E' ≫ sX) (bundleProj E') rfl (n + 1)
      (relativeDimension_bundleProj E' n) hfacP'
      (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback g).obj (bundleTwist E))) k
      (bundleChernCapFamily E n C sX k α) := by
  have := isInvertible_pullback g (bundleTwist E)
  have hcompat := chernTermsCompatibleWithFlatPullback_of_square C sX sX (bundleProj E' ≫ sX)
    (bundleProj E ≫ sX) (bundleProj E') rfl (bundleProj E) rfl (n + 1)
    (relativeDimension_bundleProj E' n) (relativeDimension_bundleProj E n) hfacP' hfacP
    (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback g).obj (bundleTwist E)))
    (bundleTwistCap E C sX) (𝟙 X) (Category.id_comp sX) 0 (relativeDimension_identity X)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_id C sX k) g hf' hd' hfacg
    (by rw [hg, Category.comp_id])
    (fun e y y' hy ↦ flatPullbackChow_firstChernClassCapChow_heq C (bundleProj E' ≫ sX)
      (bundleProj E ≫ sX) g hf' 0 hd' hfacg (bundleTwist E) _ (Iso.refl _) e y y' hy)
  have hrelA := flatPullback_projectiveBundleChernRelation C sX sX (bundleProj E' ≫ sX)
    (bundleProj E ≫ sX) (bundleProj E') rfl (bundleProj E) rfl (n + 1)
    (relativeDimension_bundleProj E' n) (relativeDimension_bundleProj E n) hfacP' hfacP _ _
    (𝟙 X) (Category.id_comp sX) 0 (relativeDimension_identity X)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_id C sX k) g hf' hd' hfacg hcompat k
    _ (isChernCapFamily_bundleChernCapFamily E n C sX k α).2
  exact projectiveBundleChernRelation_congr C sX (bundleProj E' ≫ sX) (bundleProj E') rfl
    (n + 1) (relativeDimension_bundleProj E' n) hfacP' _ (show k + ((0 : ℕ) : ℤ) = k by simp) _
    (bundleChernCapFamily E n C sX k α) (fun j ↦ by
      simp only [flatPullbackChernFamily]
      refine (chowGroupCast_heq C sX _ _).trans ?_
      rw [flatPullbackChow_id]
      exact chowGroupCast_heq C sX _ _) hrelA

/-- **A family solving the relation of Stacks 02U6 for the zero class vanishes.** Its `0`-th
member being zero, it is the zero family, by the injectivity half of Stacks 02TX on the
projective bundle of `ℰ'`. -/
private theorem eq_zero_of_projectiveBundleChernRelation {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E' : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [Flat (bundleProj E')] [LocallyOfFiniteType (bundleProj E')]
    (hfacP' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C (bundleProj E' ≫ sX) sX
      (bundleProj E') rfl (n + 1 - 1) (relativeDimension_bundleProj E' n) k)
    (k : ℤ) (d : ∀ j : Fin (n + 1 + 1), chowGroup C sX (k - (j : ℤ)))
    (hd0 : d ⟨0, Nat.zero_lt_succ (n + 1)⟩ = 0)
    (hrel : ProjectiveBundleChernRelation C sX (bundleProj E' ≫ sX) (bundleProj E') rfl (n + 1)
      (relativeDimension_bundleProj E' n) hfacP' (bundleTwistCap E' C sX) k d) :
    d = fun _ ↦ 0 := by
  have h1 : IsChernCapFamily C sX (bundleProj E' ≫ sX) (bundleProj E') rfl (n + 1)
      (relativeDimension_bundleProj E' n) hfacP' (bundleTwistCap E' C sX) k 0 d := by
    refine ⟨?_, hrel⟩
    rw [hd0, map_zero]
  have h2 : IsChernCapFamily C sX (bundleProj E' ≫ sX) (bundleProj E') rfl (n + 1)
      (relativeDimension_bundleProj E' n) hfacP' (bundleTwistCap E' C sX) k 0 (fun _ ↦ 0) := by
    refine ⟨map_zero _, ?_⟩
    simp only [ProjectiveBundleChernRelation, map_zero, smul_zero, Finset.sum_const_zero]
  exact eq_of_isChernCapFamily C sX _ _ rfl _ _ _ _
    (projectiveBundleRelationInjective_bundle E' n C sX) k 0 h1 h2

/-- **The binomial transform, from the two relations on the bundle of `ℰ'`.** Given that the
family of `α` for `ℰ` solves the relation of Stacks 02U6 with the twist pulled back along `g`, and
that the tower of `𝒪_{𝐏(ℰ')}(1)` is the sum of the towers of `g^*𝒪_{𝐏(ℰ)}(1)` and of `π'^*ℒ`, the
family of `α` for `ℰ'` is the binomial transform of the family of `α` for `ℰ` along `c₁(ℒ) ∩ -`.

The three hypotheses of `Stacks.Chow.eq_binomialTransform_of_towerRelations` are the two
alternating tower sums of the relations and the uniqueness of the solution for the zero class. -/
private theorem eq_binomialTransform_of_towerRelations_bundle {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E L : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Flat (bundleProj E)] [LocallyOfFiniteType (bundleProj E)] (E' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [Flat (bundleProj E')] [LocallyOfFiniteType (bundleProj E')]
    (g : bundle E' ⟶ bundle E)
    (hfacP' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C (bundleProj E' ≫ sX) sX
      (bundleProj E') rfl (n + 1 - 1) (relativeDimension_bundleProj E' n) k)
    (k : ℤ) (α : chowGroup C sX k) :
    haveI := isInvertible_pullback g (bundleTwist E)
    haveI := isInvertible_pullback (bundleProj E') L
    ∀ (_ : ProjectiveBundleChernRelation C sX (bundleProj E' ≫ sX) (bundleProj E') rfl (n + 1)
        (relativeDimension_bundleProj E' n) hfacP'
        (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback g).obj (bundleTwist E))) k
        (bundleChernCapFamily E n C sX k α))
      (_ : (fun j ↦ ChernCapOperator.towerStep C (bundleProj E' ≫ sX)
          (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback g).obj (bundleTwist E)))
          (bundleRelationDegree (n + 1) k) j +
        ChernCapOperator.towerStep C (bundleProj E' ≫ sX)
          (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback (bundleProj E')).obj L))
          (bundleRelationDegree (n + 1) k) j) =
        ChernCapOperator.towerStep C (bundleProj E' ≫ sX) (bundleTwistCap E' C sX)
          (bundleRelationDegree (n + 1) k))
      {m : ℕ} (_ : m ≤ n + 1),
      extendFamily C sX (n + 1) (bundleChernCapFamily E' n C sX k α) m =
        binomialTransform (ChernCapOperator.towerStep C sX (invCap C sX L) k) (n + 1)
          (extendFamily C sX (n + 1) (bundleChernCapFamily E n C sX k α)) m := by
  have := isInvertible_pullback g (bundleTwist E)
  have := isInvertible_pullback (bundleProj E') L
  intro hrelE hsum m hm
  have hrelE' := alternatingTowerSum_extendFamily C sX (bundleProj E' ≫ sX) (bundleProj E') rfl
    (n + 1) (relativeDimension_bundleProj E' n) hfacP'
    (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback g).obj (bundleTwist E))) k
    (bundleChernCapFamily E n C sX k α)
  have hrelF' := alternatingTowerSum_extendFamily C sX (bundleProj E' ≫ sX) (bundleProj E') rfl
    (n + 1) (relativeDimension_bundleProj E' n) hfacP' (bundleTwistCap E' C sX) k
    (bundleChernCapFamily E' n C sX k α)
  have hfamF := (isChernCapFamily_bundleChernCapFamily E' n C sX k α).2
  refine eq_binomialTransform_of_towerRelations
    (G := fun j : ℕ ↦ chowGroup C sX (k - (j : ℤ)))
    (H := fun j : ℕ ↦ chowGroup C (bundleProj E' ≫ sX) (bundleRelationDegree (n + 1) k - (j : ℤ)))
    (ChernCapOperator.towerStep C sX (invCap C sX L) k)
    (ChernCapOperator.towerStep C (bundleProj E' ≫ sX)
      (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback g).obj (bundleTwist E)))
      (bundleRelationDegree (n + 1) k))
    (ChernCapOperator.towerStep C (bundleProj E' ≫ sX)
      (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback (bundleProj E')).obj L))
      (bundleRelationDegree (n + 1) k))
    (projectiveBundleTowerPullback C sX (bundleProj E' ≫ sX) (bundleProj E') rfl (n + 1)
      (relativeDimension_bundleProj E' n) hfacP' k)
    (towerStep_comm C _ _ _ (fun m z ↦ invCap_capOnChow_comm C _ m _ _ z) _)
    (projectiveBundleTowerPullback_towerStep_invCap C sX (bundleProj E' ≫ sX) (bundleProj E')
      rfl (n + 1) (relativeDimension_bundleProj E' n) hfacP' L k) (n + 1) _ _ ?_ ?_ ?_ ?_ hm
  · rw [extendFamily_of_lt C sX _ _ (by omega), extendFamily_of_lt C sX _ _ (by omega)]
    exact (chowGroupCast C sX (show k - ((0 : Fin (n + 1 + 1)) : ℤ) = k by simp)).injective
      ((bundleChernCapFamily_zero E' n C sX k α).trans
        (bundleChernCapFamily_zero E n C sX k α).symm)
  · rw [hrelE', show ∑ i : Fin (n + 1 + 1), _ = (0 : chowGroup C (bundleProj E' ≫ sX) _) from
      hrelE, map_zero]
  · rw [hsum, hrelF',
      show ∑ i : Fin (n + 1 + 1), _ = (0 : chowGroup C (bundleProj E' ≫ sX) _) from hfamF,
      map_zero]
  · intro d hd0 hd m hm
    let d' : ∀ j : Fin (n + 1 + 1), chowGroup C sX (k - (j : ℤ)) := fun j ↦ d j
    have hext : ∀ i ∈ Finset.range (n + 1 + 1),
        towerPullback (projectiveBundleTowerPullback C sX (bundleProj E' ≫ sX) (bundleProj E')
          rfl (n + 1) (relativeDimension_bundleProj E' n) hfacP' k) d (n + 1 - i) =
        towerPullback (projectiveBundleTowerPullback C sX (bundleProj E' ≫ sX) (bundleProj E')
          rfl (n + 1) (relativeDimension_bundleProj E' n) hfacP' k) (extendFamily C sX (n + 1) d')
            (n + 1 - i) := fun i hi ↦ by
      rw [towerPullback_apply, towerPullback_apply, extendFamily_of_lt C sX _ _ (by omega)]
    rw [hsum, alternatingTowerSum_def] at hd
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [descentTower_congr _ _ _ _ (hext i hi) (n + 1) (by omega)],
      ← alternatingTowerSum_def, alternatingTowerSum_extendFamily] at hd
    have hrel : ProjectiveBundleChernRelation C sX (bundleProj E' ≫ sX) (bundleProj E') rfl
        (n + 1) (relativeDimension_bundleProj E' n) hfacP' (bundleTwistCap E' C sX) k d' :=
      (chowGroupCast C (bundleProj E' ≫ sX) _).injective (hd.trans (map_zero _).symm)
    exact congrFun (eq_zero_of_projectiveBundleChernRelation C sX E' n hfacP' k d'
      (by change d 0 = 0; exact hd0) hrel) ⟨m, by omega⟩

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E L : X.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The families of Stacks 02U6 of two modules whose bundles differ by a twist.** If the
projective bundle of `ℰ'` is that of `ℰ` through an isomorphism `g` over `X` with
`𝒪_{𝐏(ℰ')}(1) ≅ g^*𝒪_{𝐏(ℰ)}(1) ⊗ π'^*ℒ`, then the family of `α` for `ℰ'` is the binomial
transform at `n + 1` of the family of `α` for `ℰ` along `c₁(ℒ) ∩ -`. -/
theorem bundleChernCapFamily_eq_binomialTransform (E' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)] :
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E'
      (n + 1)
    ∀ (g : bundle E' ⟶ bundle E) [IsIso g] (_ : g ≫ bundleProj E = bundleProj E')
      (_ : bundleTwist E' ≅ Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback g).obj (bundleTwist E))
        ((Scheme.Modules.pullback (bundleProj E')).obj L))
      (k : ℤ) (α : chowGroup C sX k) {m : ℕ} (_ : m ≤ n + 1),
      extendFamily C sX (n + 1) (bundleChernCapFamily E' n C sX k α) m =
        binomialTransform (ChernCapOperator.towerStep C sX (invCap C sX L) k) (n + 1)
          (extendFamily C sX (n + 1) (bundleChernCapFamily E n C sX k α)) m := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E'
    (n + 1)
  intro g _ hg τ k α m hm
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  let := flat_bundleProj E' n
  let := locallyOfFiniteType_bundleProj E' n
  have : LocallyOfFiniteType g := inferInstance
  have : Flat g := inferInstance
  have hd' : AlgebraicGeometry.RelativeDimension g 0 :=
    (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero g).mp inferInstance
  have := isInvertible_pullback g (bundleTwist E)
  have := isInvertible_pullback (bundleProj E') L
  have hf' : g ≫ (bundleProj E ≫ sX) = bundleProj E' ≫ sX := by rw [← Category.assoc, hg]
  have hfacP := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E ≫ sX) sX (bundleProj E) rfl _ (relativeDimension_bundleProj E n) k
  have hfacP' := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E' ≫ sX) sX (bundleProj E') rfl _ (relativeDimension_bundleProj E' n) k
  have hfacg := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E' ≫ sX) (bundleProj E ≫ sX) g hf' 0 hd' k
  -- the relation for `ℰ`, transported to the bundle of `ℰ ⊗ ℒ`
  have hrelE := projectiveBundleChernRelation_bundleIso C sX E n E' g hg hf' hd' hfacP hfacP'
    hfacg k α
  -- the towers
  have hcap : ∀ (m : ℤ) (y : chowGroup C (bundleProj E' ≫ sX) (m + 1)),
      (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback g).obj (bundleTwist E))).capOnChow
          C (bundleProj E' ≫ sX) m y +
        (invCap C (bundleProj E' ≫ sX) ((Scheme.Modules.pullback (bundleProj E')).obj L)).capOnChow
          C (bundleProj E' ≫ sX) m y =
      (bundleTwistCap E' C sX).capOnChow C (bundleProj E' ≫ sX) m y := fun m y ↦
    (firstChernClassCapChow_tensorObj C (bundleProj E' ≫ sX) m
      ((Scheme.Modules.pullback g).obj (bundleTwist E))
      ((Scheme.Modules.pullback (bundleProj E')).obj L) y).trans
    (firstChernClassCapChow_congr C (bundleProj E' ≫ sX) m τ.symm y)
  exact eq_binomialTransform_of_towerRelations_bundle C sX E L n E' g hfacP' k α hrelE
    (funext (towerStep_add C _ _ _ _ hcap _)) hm

end Twist

/-! ### Stacks 02UD -/

section Formula

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The formula of Stacks 02UD for two modules whose bundles differ by a twist.** If the
projective bundle of `ℰ'` is that of `ℰ` through an isomorphism `g` over `X` with
`𝒪_{𝐏(ℰ')}(1) ≅ g^*𝒪_{𝐏(ℰ)}(1) ⊗ π'^*ℒ`, then
`c_i(ℰ') ∩ α = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(ℰ) ∩ c₁(ℒ)^j ∩ α`. -/
theorem chernCap_eq_sum_of_bundleIso (E E' : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hgeo :
      haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
      haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E' r
      ∃ g : bundle E' ⟶ bundle E, IsIso g ∧ g ≫ bundleProj E = bundleProj E' ∧
        Nonempty (bundleTwist E' ≅ Scheme.Modules.tensorObj
          ((Scheme.Modules.pullback g).obj (bundleTwist E))
          ((Scheme.Modules.pullback (bundleProj E')).obj L)))
    (k : ℤ) (i : Fin (r + 1)) (α : chowGroup C sX k) :
    chernCap C r sX E' k i α =
      ∑ j : Fin ((i : ℕ) + 1), ((r - i + j : ℕ).choose j : ℤ) •
        chowGroupCast C sX (by simp only [Fin.val_mk]; omega)
          (chernCap C r sX E (k - (j : ℤ)) ⟨(i : ℕ) - j, by omega⟩
            (capPow C sX (invCap C sX L) j k (k - (j : ℤ)) (by ring) α)) := by
  obtain ⟨i, hi⟩ := i
  cases r with
  | zero =>
    obtain rfl : i = 0 := by omega
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_smul]
    rw [chernCap_zero, chernCap_zero]
    refine eq_of_heq ((chowGroupCast_heq C sX _ _).trans ?_)
    refine HEq.symm ((chowGroupCast_heq C sX _ _).trans ((chowGroupCast_heq C sX _ _).trans ?_))
    rw [capPow_zero_apply]
    exact chowGroupCast_heq C sX _ _
  | succ n =>
    obtain ⟨g, hiso, hg, ⟨τ⟩⟩ := hgeo
    rw [chernCap_succ, bundleChernCap_apply,
      ← extendFamily_of_lt C sX (n + 1) (bundleChernCapFamily E' n C sX k α) hi,
      bundleChernCapFamily_eq_binomialTransform C sX E L n E' g hg τ k α (by omega),
      binomialTransform_eq, ← Finset.sum_range_reflect, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj := j.isLt
    rw [descentTower_towerStep C sX (invCap C sX L) k _ (by omega),
      extendFamily_of_lt C sX (n + 1) _ (by omega), ← natCast_zsmul]
    congr 1
    · simp only [Fin.val_mk]
      rw [show n + 1 - (i + 1 - 1 - (j : ℕ)) = n + 1 - i + j by omega,
        show i - (i + 1 - 1 - (j : ℕ)) = j by omega]
    · have hcomm := lowering_capPow C sX (invCap C sX L) _
        (chernLowering C sX E (n + 1) ⟨i - j, by omega⟩)
        (chernLowering_invCap_comm C sX E (n + 1) ⟨i - j, by omega⟩ L) j k (k - (j : ℤ))
        (by ring) (k - ((i - (j : ℕ) : ℕ) : ℤ)) (k - (i : ℤ)) (by omega) (by simp)
        (by simp only; omega) α
      rw [chernLowering_apply, chernLowering_apply, capPow_cast] at hcomm
      refine eq_of_heq ((HEq.trans ?_ (heq_of_eq hcomm.symm)).trans ?_)
      · refine capPow_heq C sX (invCap C sX L) _ _ (by omega)
          (by simp only; omega) rfl ?_
        rw [chernCap_succ, bundleChernCap_apply]
        exact congr_arg_heq (bundleChernCapFamily E n C sX k α)
          (Fin.ext (by simp only; omega))
      · exact (chowGroupCast_heq C sX _ _).trans (chowGroupCast_heq C sX _ _).symm

end Formula

end Stacks.Chow.GenuineChern

end
