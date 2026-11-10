module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreSupportedInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional

/-!
# The top Segre operation and flat base change

Let `q : Q ⟶ Y` be a proper flat morphism of good algebraic spaces of relative dimension `d`, `ℒ`
invertible on `Q`, and `Φ_Y(α) = q_*(c₁(ℒ)^d ∩ q^*α)`. For a flat morphism `g : W ⟶ Y` of good
algebraic spaces of relative dimension `r`, with base change `q_W : Q_W = W ×_Y Q ⟶ W` and
projection `g' : Q_W ⟶ Q`, the operation `Φ_W` built from `q_W` and `g'^*ℒ` satisfies

`g^* Φ_Y(α) ∼_rat Φ_W(g^*α)` on `|g|^{-1}(T)`

for every `k`-cycle `α` supported on a closed `T ⊆ |Y|`. The three ingredients are Stacks 0EPD
(flat pullback commutes with proper pushforward), Stacks 0EQR (flat pullback commutes with the cap
product up to rational equivalence, used `d` times) and Stacks 0EPA (flat pullbacks compose),
together with Stacks 0EQY and Stacks 0EQC on subsets to carry the rational equivalences along.

This is how the coefficient of `[Z]` in `Φ_Y([Z])` is computed on an étale chart in the proof of
the top-degree case of Stacks 0ERU.

## Main results

* `rationallyEquivalentOn_flatPullbackMap_iteratedFirstChernCapCycle`:
  the iterated form of Stacks 0EQR on subsets.
* `rationallyEquivalentOn_flatPullbackMap_topSegreCycle`:
  `g^* Φ_Y(α) ∼_rat Φ_W(g^*α)` on `|g|^{-1}(T)`.

## References

* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### Reindexing degrees -/

section Cast

variable {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

theorem cycleGroupCast_cycleGroupCast {a b c : ℤ} (h₁ : a = b) (h₂ : b = c)
    (α : CycleGroup D sX a) :
    cycleGroupCast D sX h₂ (cycleGroupCast D sX h₁ α) = cycleGroupCast D sX (h₁.trans h₂) α :=
  rfl

theorem cycleGroupCast_rfl {a : ℤ} (α : CycleGroup D sX a) : cycleGroupCast D sX rfl α = α :=
  rfl

/-- The cap product commutes with reindexing of degrees. -/
theorem firstChernCapCycleMap_cycleGroupCast
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    {a b : ℤ} (h : a = b) (h' : a + 1 = b + 1) (α : CycleGroup D sX (a + 1)) :
    firstChernCapCycleMap D sX hX b (canonicalFirstChernRule D sX hX N hN b)
        (cycleGroupCast D sX h' α) =
      cycleGroupCast D sX h
        (firstChernCapCycleMap D sX hX a (canonicalFirstChernRule D sX hX N hN a) α) := by
  subst h
  rfl

variable (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The flat pullback does not depend on the target degree it is graded in. -/
theorem flatPullbackMap_eq_cycleGroupCast (m n n' : ℤ) (hmn : m + (r : ℤ) = n)
    (hmn' : m + (r : ℤ) = n') (α : CycleGroup D sY m) :
    flatPullbackMap D sX hX sY hY f hbase r hflat hr m n' hmn' α =
      cycleGroupCast D sX (hmn.symm.trans hmn')
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α) :=
  Subtype.ext rfl

/-- The flat pullback commutes with reindexing of the source degree. -/
theorem flatPullbackMap_cycleGroupCast (m m' n : ℤ) (h : m = m') (hm'n : m' + (r : ℤ) = n)
    (α : CycleGroup D sY m) :
    flatPullbackMap D sX hX sY hY f hbase r hflat hr m' n hm'n (cycleGroupCast D sY h α) =
      flatPullbackMap D sX hX sY hY f hbase r hflat hr m n (h ▸ hm'n) α := by
  subst h
  rfl

/-- The flat pullback along equal morphisms is the same. -/
theorem flatPullbackMap_congr {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (hb₁ : f₁ ≫ sY = sX)
    (hb₂ : f₂ ≫ sY = sX) (hf₁ : IsFlat D.site D.base D.base_mem f₁)
    (hf₂ : IsFlat D.site D.base D.base_mem f₂)
    (hr₁ : HasRelativeDimension r D.site D.base D.base_mem f₁)
    (hr₂ : HasRelativeDimension r D.site D.base D.base_mem f₂) (m n : ℤ) (hmn : m + (r : ℤ) = n) :
    flatPullbackMap D sX hX sY hY f₁ hb₁ r hf₁ hr₁ m n hmn =
      flatPullbackMap D sX hX sY hY f₂ hb₂ r hf₂ hr₂ m n hmn := by
  subst h
  rfl

end Cast

/-! ### Iterated Stacks 0EQR on subsets -/

section Iterated

variable {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- The inverse image `f^*ℒ` as a module on `X`. -/
abbrev pullbackLine : Modules.{u, u} D.site D.base D.base_mem X hX.1 :=
  (modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩)).obj L

include hL in
theorem isInvertibleModule_pullbackLine :
    IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (pullbackLine D sX hX sY hY f L) :=
  modulePullbackInvertible
    (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩) L hL

/-- **Iterated Stacks 0EQR on subsets.** For a `(k + d)`-cycle `γ` on `Y` supported on `T`,
`f^*(c₁(ℒ)^d ∩ γ) ∼_rat c₁(f^*ℒ)^d ∩ f^*γ` on `|f|^{-1}(T)`. -/
theorem rationallyEquivalentOn_flatPullbackMap_iteratedFirstChernCapCycle
    (T : Set (points D.site D.base D.base_mem Y)) :
    ∀ (d : ℕ) (k : ℤ) (γ : CycleGroup D sY (k + d)),
      (∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        γ.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T) →
      RationallyEquivalentOn.{u + 1} D sX hX (k + r)
        (pointsMap D.site D.base D.base_mem X f ⁻¹' T)
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + r) rfl
          (iteratedFirstChernCapCycle D sY hY d (fun _ => L) (fun _ => hL) k γ))
        (iteratedFirstChernCapCycle D sX hX d (fun _ => pullbackLine D sX hX sY hY f L)
          (fun _ => isInvertibleModule_pullbackLine D sX hX sY hY f L hL) (k + r)
          (cycleGroupCast D sX (by ring)
            (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + d) (k + d + r) rfl γ)))
  | 0, k, γ, _ => by
    exact rationallyEquivalentOn_refl.{u + 1} D sX hX _ _ _
  | d + 1, k, γ, hγT => by
    set capY := firstChernCapCycleMap D sY hY (k + d)
      (canonicalFirstChernRule D sY hY L hL (k + d))
    set γ' := capY (cycleGroupCast D sY (by push_cast; ring) γ)
    have hγ'T : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        γ'.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T :=
      subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero D sY hY (k + d) _ T _
        fun Z hZ => hγT Z hZ
    have IH := rationallyEquivalentOn_flatPullbackMap_iteratedFirstChernCapCycle T d k γ' hγ'T
    -- Stacks 0EQR at the last factor.
    have h0EQR := rationallyEquivalentOn_flatPullbackMap_firstChernCapCycleMap D sX hX sY hY f
      hbase r hflat hr L hL (k + d) T (cycleGroupCast D sY (by push_cast; ring) γ)
      (fun Z hZ => hγT Z hZ)
    have hstep :=
      rationallyEquivalentOn_iteratedFirstChernCapCycle_of_rationallyEquivalentOn.{u + 1}
        D sX hX d (fun _ => pullbackLine D sX hX sY hY f L)
        (fun _ => isInvertibleModule_pullbackLine D sX hX sY hY f L hL)
        (fun _ T k α hα => rationallyEquivalentOn_firstChernCapCycleMap D sX hX _ _ T k α hα)
        (pointsMap D.site D.base D.base_mem X f ⁻¹' T) (k + r)
        (rationallyEquivalentOn_cycleGroupCast.{u + 1} D sX hX (by ring) _ h0EQR)
    rw [iteratedFirstChernCapCycle_succ]
    refine RationallyEquivalentOn.trans IH (RationallyEquivalentOn.trans hstep ?_)
    rw [iteratedFirstChernCapCycle_succ]
    have hinner : cycleGroupCast D sX (show k + d + r = k + r + d by ring)
        (firstChernCapCycleMap D sX hX (k + d + r)
          (canonicalFirstChernRule D sX hX (pullbackLine D sX hX sY hY f L)
            (isInvertibleModule_pullbackLine D sX hX sY hY f L hL) (k + d + r))
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + d + 1) (k + d + r + 1) (by ring)
            (cycleGroupCast D sY (by push_cast; ring) γ))) =
        firstChernCapCycleMap D sX hX (k + r + d)
          (canonicalFirstChernRule D sX hX (pullbackLine D sX hX sY hY f L)
            (isInvertibleModule_pullbackLine D sX hX sY hY f L hL) (k + r + d))
          (cycleGroupCast D sX
            (show k + r + ((d + 1 : ℕ) : ℤ) = k + r + d + 1 by push_cast; ring)
            (cycleGroupCast D sX
              (show k + ((d + 1 : ℕ) : ℤ) + r = k + r + ((d + 1 : ℕ) : ℤ) by ring)
              (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + ((d + 1 : ℕ) : ℤ))
                (k + ((d + 1 : ℕ) : ℤ) + r) rfl γ))) := by
      rw [← firstChernCapCycleMap_cycleGroupCast D sX hX _ _ (show k + d + r = k + r + d by ring)
        (by ring)]
      rfl
    rw [hinner]
    exact rationallyEquivalentOn_refl.{u + 1} D sX hX _ _ _

end Iterated

/-! ### Flat base change of the top Segre operation -/

section BaseChange

variable {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- The coefficients of a flat pullback depend only on the morphism and the relative dimension,
not on the proofs of the hypotheses nor on the degrees. -/
theorem flatPullbackMap_coe_congr {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) {r₁ r₂ : ℕ} (hr : r₁ = r₂)
    (hb₁ : f₁ ≫ sY = sX) (hb₂ : f₂ ≫ sY = sX) (hf₁ : IsFlat D.site D.base D.base_mem f₁)
    (hf₂ : IsFlat D.site D.base D.base_mem f₂)
    (hr₁ : HasRelativeDimension r₁ D.site D.base D.base_mem f₁)
    (hr₂ : HasRelativeDimension r₂ D.site D.base D.base_mem f₂) (m n₁ n₂ : ℤ)
    (hmn₁ : m + (r₁ : ℤ) = n₁) (hmn₂ : m + (r₂ : ℤ) = n₂) (α : CycleGroup D sY m) :
    (flatPullbackMap D sX hX sY hY f₁ hb₁ r₁ hf₁ hr₁ m n₁ hmn₁ α).1 =
      (flatPullbackMap D sX hX sY hY f₂ hb₂ r₂ hf₂ hr₂ m n₂ hmn₂ α).1 := by
  subst h hr
  rfl

variable {Q W : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The flat pullbacks around a cartesian square agree**: for `Q_W = W ×_Y Q` with projections
`q_W` and `g'`, the cycles `g'^* q^* α` and `q_W^* g^* α` have the same coefficients (Stacks
0EPA applied to the two factorizations of the diagonal of the square). -/
theorem flatPullbackMap_flatPullbackMap_coe_of_comm
    {QW : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sW : W ⟶ D.space) (hW : D.IsGood sW)
    (sQW : QW ⟶ D.space) (hQW : D.IsGood sQW)
    {q : Q ⟶ Y} {g : W ⟶ Y} {qW : QW ⟶ W} {g' : QW ⟶ Q} (hcomm : g' ≫ q = qW ≫ g)
    (hq : q ≫ sY = sQ) (hg : g ≫ sY = sW) (hqW : qW ≫ sW = sQW) (hg' : g' ≫ sQ = sQW)
    (d r : ℕ) (hqf : IsFlat D.site D.base D.base_mem q)
    (hqd : HasRelativeDimension d D.site D.base D.base_mem q)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (hqWf : IsFlat D.site D.base D.base_mem qW)
    (hqWd : HasRelativeDimension d D.site D.base D.base_mem qW)
    (hg'f : IsFlat D.site D.base D.base_mem g')
    (hg'r : HasRelativeDimension r D.site D.base D.base_mem g')
    (k : ℤ) (n₁ n₂ m₁ m₂ : ℤ) (h₁ : k + (d : ℤ) = m₁) (h₁' : m₁ + (r : ℤ) = n₁)
    (h₂ : k + (r : ℤ) = m₂) (h₂' : m₂ + (d : ℤ) = n₂) (α : CycleGroup D sY k) :
    (flatPullbackMap D sQW hQW sQ hQ g' hg' r hg'f hg'r m₁ n₁ h₁'
        (flatPullbackMap D sQ hQ sY hY q hq d hqf hqd k m₁ h₁ α)).1 =
      (flatPullbackMap D sQW hQW sW hW qW hqW d hqWf hqWd m₂ n₂ h₂'
        (flatPullbackMap D sW hW sY hY g hg r hgf hgr k m₂ h₂ α)).1 := by
  subst h₁ h₂
  have e₁ := congrArg (fun φ => (φ α).1) (flatPullbackMap_comp D sQW hQW sQ hQ sY hY g' q hg' hq
    r d hg'f hg'r hqf hqd k n₁ (by push_cast; omega))
  have e₂ := congrArg (fun φ => (φ α).1) (flatPullbackMap_comp D sQW hQW sW hW sY hY qW g hqW hg
    d r hqWf hqWd hgf hgr k n₂ (by push_cast; omega))
  simp only [AddMonoidHom.comp_apply] at e₁ e₂
  rw [← e₁, ← e₂]
  exact flatPullbackMap_coe_congr D sQW hQW sY hY hcomm (Nat.add_comm r d) _ _ _ _ _ _ k n₁ n₂ _ _
    α

/-- **Flat base change of the top Segre operation, on subsets.** Let
```
Q_W --g'--> Q
 |q_W       |q
 v          v
 W  --g-->  Y
```
be a cartesian square of good algebraic spaces with `q` proper and flat of relative dimension `d`
and `g` flat of relative dimension `r`, and let `ℒ` be invertible on `Q`. For a `k`-cycle `α` on
`Y` supported on a closed `T`,

`g^* q_*(c₁(ℒ)^d ∩ q^*α) ∼_rat q_{W,*}(c₁(g'^*ℒ)^d ∩ q_W^* g^*α)` on `|g|^{-1}(T)`. -/
theorem rationallyEquivalentOn_flatPullbackMap_topSegreCycle
    {QW : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sW : W ⟶ D.space) (hW : D.IsGood sW)
    (sQW : QW ⟶ D.space) (hQW : D.IsGood sQW)
    {q : Q ⟶ Y} {g : W ⟶ Y} {qW : QW ⟶ W} {g' : QW ⟶ Q} (sq : IsPullback g' qW q g)
    (hq : q ≫ sY = sQ) (hg : g ≫ sY = sW) (hqW : qW ≫ sW = sQW) (hg' : g' ≫ sQ = sQW)
    (hqp : IsProper D.site D.base D.base_mem q) (d r : ℕ)
    (hqf : IsFlat D.site D.base D.base_mem q)
    (hqd : HasRelativeDimension d D.site D.base D.base_mem q)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (hqWp : IsProper D.site D.base D.base_mem qW)
    (hqWf : IsFlat D.site D.base D.base_mem qW)
    (hqWd : HasRelativeDimension d D.site D.base D.base_mem qW)
    (hg'f : IsFlat D.site D.base D.base_mem g')
    (hg'r : HasRelativeDimension r D.site D.base D.base_mem g')
    (L : Modules.{u, u} D.site D.base D.base_mem Q hQ.1)
    (hL : IsInvertibleModule (⟨Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (k n : ℤ) (hkn : k + (d : ℤ) = n) (T : Set (points D.site D.base D.base_mem Y))
    (hT : IsClosed T) (α : CycleGroup D sY k)
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T) :
    RationallyEquivalentOn.{u + 1} D sW hW (k + r) (pointsMap D.site D.base D.base_mem W g ⁻¹' T)
      (flatPullbackMap D sW hW sY hY g hg r hgf hgr k (k + r) rfl
        (topSegreCycle D sQ hQ sY hY hq hqp.2.1.2 L hL d k n hkn
          (flatPullbackMap D sQ hQ sY hY q hq d hqf hqd k n hkn α)))
      (topSegreCycle D sQW hQW sW hW hqW hqWp.2.1.2 (pullbackLine D sQW hQW sQ hQ g' L)
        (isInvertibleModule_pullbackLine D sQW hQW sQ hQ g' L hL) d (k + r) (n + r)
        (by omega)
        (flatPullbackMap D sQW hQW sW hW qW hqW d hqWf hqWd (k + r) (n + r) (by omega)
          (flatPullbackMap D sW hW sY hY g hg r hgf hgr k (k + r) rfl α))) := by
  set γ := cycleGroupCast D sQ hkn.symm (flatPullbackMap D sQ hQ sY hY q hq d hqf hqd k n hkn α)
  have hγT : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Q,
      γ.1 V ≠ 0 → subspacePointSet D.site D.base D.base_mem Q V.subspace ⊆
        pointsMap D.site D.base D.base_mem Q q ⁻¹' T :=
    subspacePointSet_subset_of_flatPullbackMap_ne_zero D sQ hQ sY hY q hq d hqf hqd k n hkn T α
      hαT
  simp only [topSegreCycle, AddMonoidHom.comp_apply]
  rw [flatPullback_properPushforward_unconditional D sQW hQW sQ hQ sW hW sY hY hg' hqW hq hg r
    hgf hgr sq hqp k (k + r) rfl]
  have hiter := rationallyEquivalentOn_flatPullbackMap_iteratedFirstChernCapCycle D sQW hQW sQ hQ
    g' hg' r hg'f hg'r L hL (pointsMap D.site D.base D.base_mem Q q ⁻¹' T) d k γ hγT
  have hcast : cycleGroupCast D sQW (show k + d + r = k + r + d by ring)
      (flatPullbackMap D sQW hQW sQ hQ g' hg' r hg'f hg'r (k + d) (k + d + r) rfl γ) =
      cycleGroupCast D sQW (show n + r = k + r + d by omega)
        (flatPullbackMap D sQW hQW sW hW qW hqW d hqWf hqWd (k + r) (n + r) (by omega)
          (flatPullbackMap D sW hW sY hY g hg r hgf hgr k (k + r) rfl α)) := by
    refine Subtype.ext ?_
    change (flatPullbackMap D sQW hQW sQ hQ g' hg' r hg'f hg'r (k + d) (k + d + r) rfl
      (cycleGroupCast D sQ hkn.symm (flatPullbackMap D sQ hQ sY hY q hq d hqf hqd k n hkn α))).1 = _
    rw [flatPullbackMap_cycleGroupCast]
    exact flatPullbackMap_flatPullbackMap_coe_of_comm D sY hY sQ hQ sW hW sQW hQW sq.w hq hg hqW
      hg' d r hqf hqd hgf hgr hqWf hqWd hg'f hg'r k (k + d + r) (n + r) n (k + r) hkn
      (by omega) rfl (by omega) α
  rw [hcast] at hiter
  have hpush := rationallyEquivalentOn_properCyclePushforward.{u + 1} D sQW hQW sW hW hqW hqWp
    (k + r) _ _ ((rationallyEquivalentOn_iff_zero.{u + 1} D sQW hQW _).1 hiter)
  rw [map_sub] at hpush
  refine RationallyEquivalentOn.mono ?_ ((rationallyEquivalentOn_iff_zero.{u + 1} D sW hW _).2
    hpush)
  refine closure_minimal ?_ (hT.preimage (continuous_pointsMap D.site D.base D.base_mem g))
  rintro _ ⟨x, hx, rfl⟩
  change pointsMap D.site D.base D.base_mem W g (pointsMap D.site D.base D.base_mem QW qW x) ∈ T
  have := congrArg (fun φ => pointsMap D.site D.base D.base_mem QW φ x) sq.w
  simp only [pointsMap_comp_apply] at this
  rw [← this]
  exact hx

end BaseChange

end AlgebraicGeometry.Space.PrivateChern

end
