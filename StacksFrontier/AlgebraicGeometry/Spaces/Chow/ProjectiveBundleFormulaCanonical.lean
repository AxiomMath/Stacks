module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonicalSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaCapPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleRelationAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence

/-!
# The map of the projective space bundle formula on Chow groups, and its injectivity

Let `f : Y → X` be a proper morphism of good algebraic spaces over the base which is flat of
relative dimension `n`, and let `ℒ` be an invertible `𝒪_Y`-module. For the projective bundle
`(π : P → X, 𝒪_P(1))` of a finite locally free module of rank `n + 1` this is the situation of
Stacks 0ERV, whose map is

`⊕_{i = 0}^{n} CH_{k+i}(X) → CH_{k+n}(P)`,  `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`.

This file builds that map on the Chow groups of Stacks 0EQ6 at the canonical embeddings of
Stacks 0ENK (`AlgebraicGeometry.Space.chowGroupCanonical`), for every such pair `(f, ℒ)`, in the
shape of `AlgebraicGeometry.Space.ProjectiveBundleRelation.bundleSum`: the source degrees are a
family `d` with `d i + n = N + i`. It then proves the injectivity half of Stacks 0ERV from the
identity `f_*(c₁(ℒ)^n ∩ f^*α) = α` of cycles (the top power of Stacks 0ERU): the powers below `n`
push forward to zero for dimension reasons
(`properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_zero`), so the argument is
the triangular one of the source, `AlgebraicGeometry.Space.eq_zero_of_sum_eq_zero_of_triangular`.

## Main definitions

* `AlgebraicGeometry.Space.chowGroupCanonicalCast`: the identification `CH_a(X) = CH_b(X)` for
  `a = b`.
* `AlgebraicGeometry.Space.firstChernCapPowChowMap`: `c₁(ℒ)^s ∩ - : CH_{m+s}(X) → CH_m(X)`.
* `AlgebraicGeometry.Space.bundleFormulaPull`, `AlgebraicGeometry.Space.bundleFormulaCap`: the
  flat pullback and the cap powers in the shape `bundleSum` asks for.
* `AlgebraicGeometry.Space.bundleFormulaMap`: the map `(α_i) ↦ ∑_i c₁(ℒ)^i ∩ f^*α_i`.

## Main results

* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMap`: the
  powers of the cap product preserve rational equivalence (Stacks 0EQY, iterated).
* `AlgebraicGeometry.Space.injective_bundleFormulaMap_of_top`: the injectivity half of
  Stacks 0ERV, from the top power of Stacks 0ERU.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Space

/-! ### Identifying Chow groups of equal degrees -/

section Cast

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- The identification `Z_a(X) = Z_b(X)` preserves the cycles rationally equivalent to zero. -/
theorem isRationallyEquivalentToZeroCanonical_cycleGroupCast {a b : ℤ} (h : a = b)
    {α : CycleGroup D sX a} (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX a α) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX b (cycleGroupCast D sX h α) := by
  subst h
  exact hα

/-- The identification `CH_a(X) = CH_b(X)` for `a = b`. -/
def chowGroupCanonicalCast {a b : ℤ} (h : a = b) :
    chowGroupCanonical.{v} D sX hX a →+ chowGroupCanonical.{v} D sX hX b :=
  chowGroupCanonicalHomOfCycleHom.{v} D sX hX sX hX a b (cycleGroupCast D sX h)
    fun _ hγ => isRationallyEquivalentToZeroCanonical_cycleGroupCast D sX hX h hγ

/-- The identification `CH_a(X) = CH_b(X)` sends the class of a cycle `α` to the class of `α`
viewed as a `b`-cycle. -/
@[simp]
theorem chowGroupCanonicalCast_chowClassCanonical {a b : ℤ} (h : a = b) (α : CycleGroup D sX a) :
    chowGroupCanonicalCast.{v} D sX hX h (chowClassCanonical.{v} D sX hX a α) =
      chowClassCanonical.{v} D sX hX b (cycleGroupCast D sX h α) :=
  rfl

end Cast

/-! ### Powers of the cap product on Chow groups -/

section Power

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The powers of the cap product preserve rational equivalence** (Stacks 0EQY, iterated):
`c₁(ℒ)^s ∩ -` carries an `(m + s)`-cycle rationally equivalent to zero to an `m`-cycle
rationally equivalent to zero, both at the canonical embeddings of Stacks 0ENK. -/
theorem isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMap (s : ℕ) :
    ∀ (m : ℤ) {α : CycleGroup D sX (m + s)},
      IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX (m + s) α →
        IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX m
          (firstChernCapPowCycleMap D sX hX L hL s m α) := by
  induction s with
  | zero =>
    intro m α hα
    exact isRationallyEquivalentToZeroCanonical_cycleGroupCast D sX hX _ hα
  | succ s ih =>
    intro m α hα
    exact isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule D sX
      hX m L hL (ih (m + 1) (isRationallyEquivalentToZeroCanonical_cycleGroupCast D sX hX _ hα))

/-- **`c₁(ℒ)^s ∩ - : CH_{m+s}(X) → CH_m(X)`**, the `s`-fold cap product of Stacks 0EQJ descended
to the Chow groups of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK. -/
def firstChernCapPowChowMap (s : ℕ) (m : ℤ) :
    chowGroupCanonical.{u + 1} D sX hX (m + s) →+ chowGroupCanonical.{u + 1} D sX hX m :=
  chowGroupCanonicalHomOfCycleHom.{u + 1} D sX hX sX hX (m + s) m
    (firstChernCapPowCycleMap D sX hX L hL s m)
    fun _ hγ => isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMap D sX hX L hL s m hγ

/-- On Chow classes, `c₁(ℒ)^s ∩ -` is the class of the cycle-level cap power:
`c₁(ℒ)^s ∩ [α] = [c₁(ℒ)^s ∩ α]`. -/
@[simp]
theorem firstChernCapPowChowMap_chowClassCanonical (s : ℕ) (m : ℤ)
    (α : CycleGroup D sX (m + s)) :
    firstChernCapPowChowMap D sX hX L hL s m (chowClassCanonical.{u + 1} D sX hX (m + s) α) =
      chowClassCanonical.{u + 1} D sX hX m (firstChernCapPowCycleMap D sX hX L hL s m α) :=
  rfl

end Power

/-! ### The map of the projective bundle formula -/

section Formula

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : Y ⟶ X) (hfB : f ≫ sX = sY) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- The flat pullback `f^* : CH_m(X) → CH_N(Y)`, `m + n = N`, in the shape of the pullback of
`AlgebraicGeometry.Space.ProjectiveBundleRelation.bundleSum`. -/
def bundleFormulaPull (m N : ℤ) (h : m + (n : ℤ) = N) :
    chowGroupCanonical.{u + 1} D sX hX m →+ chowGroupCanonical.{u + 1} D sY hY N :=
  flatPullbackChowMapCanonical.{u + 1} D sY hY sX hX f hfB n hflat hrel m N h

/-- The cap power `c₁(ℒ)^s ∩ - : CH_N(Y) → CH_m(Y)`, `N = m + s`, in the shape of the caps of
`AlgebraicGeometry.Space.ProjectiveBundleRelation.bundleSum`. -/
def bundleFormulaCap (s : ℕ) (N m : ℤ) (h : N = m + s) :
    chowGroupCanonical.{u + 1} D sY hY N →+ chowGroupCanonical.{u + 1} D sY hY m :=
  (firstChernCapPowChowMap D sY hY L hL s m).comp (chowGroupCanonicalCast.{u + 1} D sY hY h)

/-- **The map of the projective space bundle formula** (Stacks 0ERV) for `(f, ℒ)`:
`(α_i)_{i ≤ n} ↦ ∑_i c₁(ℒ)^i ∩ f^*α_i`, from `∏_i CH_{d i}(X)` to `CH_N(Y)`, for source degrees
with `d i + n = N + i`. For the projective bundle of a module of rank `n + 1` and `d i = k + i`
this is the map `⊕_{i=0}^{n} CH_{k+i}(X) → CH_{k+n}(P)` of the source. -/
def bundleFormulaMap (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    (∀ i, chowGroupCanonical.{u + 1} D sX hX (d i)) →+ chowGroupCanonical.{u + 1} D sY hY N :=
  ProjectiveBundleRelation.bundleSum (A := fun k => chowGroupCanonical.{u + 1} D sX hX k)
    (P := fun k => chowGroupCanonical.{u + 1} D sY hY k) (n : ℤ)
    (bundleFormulaPull D sX hX sY hY f hfB n hflat hrel)
    (bundleFormulaCap D sY hY L hL) (n + 1) N d hd

/-- The cycle-level operations only depend on the underlying coefficient functions and on the
degrees: the flat pullback. -/
theorem coe_flatPullbackMap_congr {m m' N N' : ℤ} (hm : m = m') (hN : N = N')
    (h : m + (n : ℤ) = N) (h' : m' + (n : ℤ) = N') (α : CycleGroup D sX m)
    (α' : CycleGroup D sX m') (hα : α.1 = α'.1) :
    (flatPullbackMap D sY hY sX hX f hfB n hflat hrel m N h α).1 =
      (flatPullbackMap D sY hY sX hX f hfB n hflat hrel m' N' h' α').1 := by
  subst hm hN
  rw [Subtype.ext hα]

/-- The cycle-level operations only depend on the underlying coefficient functions and on the
degrees: the proper pushforward. -/
theorem coe_properCyclePushforward_congr (hf : IsQuasiCompact D.site D.base D.base_mem f)
    {m m' : ℤ} (hm : m = m') (α : CycleGroup D sY m) (α' : CycleGroup D sY m')
    (hα : α.1 = α'.1) :
    (properCyclePushforward D sY hY sX hX hfB hf m α).1 =
      (properCyclePushforward D sY hY sX hX hfB hf m' α').1 := by
  subst hm
  rw [Subtype.ext hα]

/-- The degree bookkeeping of the `j`-th left inverse: `N = d j + (n - j)`. -/
private theorem degree_eq {n : ℕ} {N : ℤ} {d : Fin (n + 1) → ℤ}
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (j : Fin (n + 1)) :
    N = d j + ((n - (j : ℕ) : ℕ) : ℤ) := by
  have := hd j
  have hj := j.isLt
  push_cast [Nat.cast_sub (Nat.le_of_lt_succ hj)]
  omega

/-- The degree bookkeeping of the `j`-th left inverse on the `i`-th summand:
`N + i = d j + (n - j + i)`. -/
private theorem degree_add_eq {n : ℕ} {N : ℤ} {d : Fin (n + 1) → ℤ}
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (i j : Fin (n + 1)) :
    N + (i : ℕ) = d j + ((n - (j : ℕ) + (i : ℕ) : ℕ) : ℤ) := by
  rw [Nat.cast_add, ← add_assoc, ← degree_eq hd j]

/-- The `j`-th left inverse of the triangular argument, `α ↦ f_*(c₁(ℒ)^{n-j} ∩ α)`, from
`CH_N(Y)` to `CH_{d j}(X)`. -/
def bundleFormulaProjection (hp : IsProper D.site D.base D.base_mem f) (N : ℤ)
    (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (j : Fin (n + 1)) :
    chowGroupCanonical.{u + 1} D sY hY N →+ chowGroupCanonical.{u + 1} D sX hX (d j) :=
  (chowGroupCanonicalProperPushforward.{u + 1} D sY hY sX hX hfB hp (d j)).comp
    (bundleFormulaCap D sY hY L hL (n - (j : ℕ)) N (d j) (by
      have := hd j
      have hj := j.isLt
      push_cast [Nat.cast_sub (Nat.le_of_lt_succ hj)]
      omega))

/-- The composite of the `j`-th left inverse with the `i`-th summand is the class of
`f_*(c₁(ℒ)^{n-j+i} ∩ f^*α)`, at the level of underlying coefficient functions. -/
theorem bundleFormulaProjection_cap_pull (hp : IsProper D.site D.base D.base_mem f) (N : ℤ)
    (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (i j : Fin (n + 1))
    (α : CycleGroup D sX (d i)) :
    ∃ β : CycleGroup D sY (d j),
      bundleFormulaProjection D sX hX sY hY f hfB n L hL hp N d hd j
          (bundleFormulaCap D sY hY L hL i (N + (i : ℕ)) N rfl
            (bundleFormulaPull D sX hX sY hY f hfB n hflat hrel (d i) (N + (i : ℕ)) (hd i)
              (chowClassCanonical.{u + 1} D sX hX (d i) α))) =
        chowClassCanonical.{u + 1} D sX hX (d j)
          (properCyclePushforward D sY hY sX hX hfB hp.2.1.2 (d j) β) ∧
      β.1 = (firstChernCapPowCycleMap D sY hY L hL (n - (j : ℕ) + (i : ℕ)) (d j)
        (cycleGroupCast D sY (by
          have := hd i
          have := hd j
          have hj := j.isLt
          push_cast [Nat.cast_sub (Nat.le_of_lt_succ hj)]
          omega)
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel (d i) (N + (i : ℕ)) (hd i) α))).1 := by
  refine ⟨_, rfl, ?_⟩
  have key := firstChernCapPowCycleMap_firstChernCapPowCycleMap D sY hY L hL (n - (j : ℕ)) i (d j)
    (cycleGroupCast D sY (by rw [degree_add_eq hd i j, Nat.cast_add, add_assoc])
      (flatPullbackMap D sY hY sX hX f hfB n hflat hrel (d i) (N + (i : ℕ)) (hd i) α))
  refine Eq.trans ?_ ((congrArg Subtype.val key).trans ?_)
  · refine coe_firstChernCapPowCycleMap_congr D sY hY L hL rfl rfl _ _ ?_
    rw [cycleGroupCast_coe]
    refine coe_firstChernCapPowCycleMap_congr D sY hY L hL rfl ?_ _ _ rfl
    exact degree_eq hd j
  · exact coe_firstChernCapPowCycleMap_congr D sY hY L hL rfl rfl _ _ rfl

/-- **The injectivity half of Stacks 0ERV, from the top power of Stacks 0ERU.** If
`f_*(c₁(ℒ)^n ∩ f^*α) = α` for every cycle `α` on `X`, then the map
`(α_i) ↦ ∑_i c₁(ℒ)^i ∩ f^*α_i` of the projective bundle formula is injective in every degree.

The `j`-th left inverse is `f_*(c₁(ℒ)^{n-j} ∩ -)`: it kills the summands of index `i < j`, since
`f_*(c₁(ℒ)^s ∩ f^*-)` vanishes for `s < n`, and is the identity on the summand of index `j`. -/
theorem injective_bundleFormulaMap_of_top (hp : IsProper D.site D.base D.base_mem f)
    (htop : ∀ (k : ℤ) (α : CycleGroup D sX k),
      properCyclePushforward D sY hY sX hX hfB hp.2.1.2 k
        (firstChernCapPowCycleMap D sY hY L hL n k
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl α)) = α)
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    Function.Injective (bundleFormulaMap D sX hX sY hY f hfB n hflat hrel L hL N d hd) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine eq_zero_of_sum_eq_zero_of_triangular
    (A := fun i => chowGroupCanonical.{u + 1} D sX hX (d i))
    (fun i => (bundleFormulaCap D sY hY L hL i (N + (i : ℕ)) N rfl).comp
      (bundleFormulaPull D sX hX sY hY f hfB n hflat hrel (d i) (N + (i : ℕ)) (hd i)))
    (bundleFormulaProjection D sX hX sY hY f hfB n L hL hp N d hd) ?_ ?_ a ha
  · intro i j hij x
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨β, hβ, hβα⟩ := bundleFormulaProjection_cap_pull D sX hX sY hY f hfB n hflat hrel L hL
      hp N d hd i j α
    refine hβ.trans ?_
    have hlt : n - (j : ℕ) + (i : ℕ) < n := by
      have := j.isLt
      have : (i : ℕ) < j := hij
      omega
    have h0 := properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_zero D sX hX sY
      hY f hfB hp.2.1.2 n hflat hrel L hL (n - (j : ℕ) + (i : ℕ)) hlt (d i) (d j)
      ((hd i).trans (degree_add_eq hd i j)) α
    have hβ0 : properCyclePushforward D sY hY sX hX hfB hp.2.1.2 (d j) β = 0 := by
      rw [← h0]
      refine Subtype.ext (coe_properCyclePushforward_congr D sX hX sY hY f hfB hp.2.1.2 rfl _ _ ?_)
      rw [hβα]
      refine coe_firstChernCapPowCycleMap_congr D sY hY L hL rfl rfl _ _ ?_
      rw [cycleGroupCast_coe]
      exact coe_flatPullbackMap_congr D sX hX sY hY f hfB n hflat hrel rfl (degree_add_eq hd i j)
        (hd i) _ _ _ rfl
    show chowClassCanonical.{u + 1} D sX hX (d j) _ = 0
    rw [hβ0, map_zero]
  · intro i x
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨β, hβ, hβα⟩ := bundleFormulaProjection_cap_pull D sX hX sY hY f hfB n hflat hrel L hL
      hp N d hd i i α
    refine hβ.trans ?_
    have hβ1 : properCyclePushforward D sY hY sX hX hfB hp.2.1.2 (d i) β = α := by
      refine Eq.trans ?_ (htop (d i) α)
      refine Subtype.ext (coe_properCyclePushforward_congr D sX hX sY hY f hfB hp.2.1.2 rfl _ _ ?_)
      rw [hβα]
      refine coe_firstChernCapPowCycleMap_congr D sY hY L hL (by have := i.isLt; omega) rfl _ _ ?_
      rw [cycleGroupCast_coe]
      exact coe_flatPullbackMap_congr D sX hX sY hY f hfB n hflat hrel rfl (by
        have := hd i
        omega) (hd i) rfl _ _ rfl
    rw [hβ1]
    rfl

end Formula

end AlgebraicGeometry.Space

end
