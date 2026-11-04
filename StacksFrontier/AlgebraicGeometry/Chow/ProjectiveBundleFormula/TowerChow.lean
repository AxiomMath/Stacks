module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.DivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Map
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Tower
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback

/-!
# Intersection theory on a projective tower

Let `π : P ⟶ U` be a projective tower of fibre dimension `n`
(`Stacks.Chow.IsProjectiveTower`) with twist `L`, over a base situation of chapter 42, and let
`ξ = c₁(L) ∩ -`. This file proves, for every class `α` on `U`,

  `π_*(ξ^n ∩ π^*α) = α`,

the top case of [Stacks, Tag 02TW], and the surjectivity of the map of [Stacks, Tag 02TX] for a
projective tower. The proofs are inductions along the tower: if `D` is the zero scheme of the
section of `L` the tower provides, then `ξ ∩ π^*α = i_*((π|_D)^*α)` by [Stacks, Tag 02TR], capping
commutes with pushforward along `i` by [Stacks, Tag 02SU], and the complement of `D` is an
affine-space bundle, to which [Stacks, Tag 02TT] and the localization sequence of [Stacks, Tag
02RX] apply.

## Main definitions

* `Stacks.Chow.invCap` — the first Chern class cap operator of an invertible module.

## Main results

* `Stacks.Chow.exists_sections_eval_eq` — a global section is the value of a section of the
  sheaf of modules.
* `Stacks.Chow.properChowPushforward_invCap` — Stacks 02SU for a closed immersion, on Chow
  groups.
* `Stacks.Chow.IsProjectiveTower.bundleProjection_self` — `π_*(ξ^n ∩ π^*α) = α`.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Chow

/-- A global section of a sheaf of modules on a scheme is the value at the whole space of a
section of the sheaf. -/
theorem exists_sections_eval_eq {X : Scheme.{u}} (L : X.Modules) (t : Γ(L, ⊤)) :
    ∃ s : L.sections, s.eval (op ⊤) = t :=
  ⟨(Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal L
      (Limits.isTerminalTop (α := X.Opens))).symm t,
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal L
      (Limits.isTerminalTop (α := X.Opens))).right_inv t⟩

/-- **The first Chern class cap operator of an invertible module**: its component rule is the one
of Stacks 02SO and its factoring through rational equivalence is Stacks 02TI. -/
def invCap (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ChernCapOperator C p :=
  invertibleChernCapOperator C p L
    (fun k => firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k
      p L)

/-- On the class of a cycle `α`, the operator `invCap C p L` acts on Chow groups as the first
Chern class cap `firstChernClassCapOfInvertible C p k L α`. -/
@[simp]
theorem invCap_capOnChow_mk (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) (α : CycleGroup C p (k + 1)) :
    (invCap C p L).capOnChow C p k (QuotientAddGroup.mk' _ α) =
      firstChernClassCapOfInvertible C p k L α :=
  rfl

/-- **Stacks 02SU for a closed immersion, on Chow groups.** Pushforward along a closed immersion
`i : D ⟶ P` carries `c₁(i^*L) ∩ -` to `c₁(L) ∩ -`. -/
theorem properChowPushforward_invCap (C : ChowSituation.{u}) {D P : Scheme.{u}}
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (i : D ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sD) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible D.sheaf.obj D.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L)]
    (k : ℤ) (x : chowGroup C sD (k + 1)) :
    properChowPushforward C sD sP i hi k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sD sP i hi k)
        ((invCap C sD ((Scheme.Modules.pullback i).obj L)).capOnChow C sD k x) =
      (invCap C sP L).capOnChow C sP k
        (properChowPushforward C sD sP i hi (k + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sD sP i hi (k + 1))
          x) := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_mk, properChowPushforward_mk, invCap_capOnChow_mk]
  exact properChowPushforward_firstChernClassCapOfInvertible C sD sP i hi k L α

/-- Capping with a power of `ξ` is unchanged by moving between equal degrees. -/
private theorem capPow_capOnChow_cast (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (ξ : ChernCapOperator C sP) (s : ℕ) {a a' m b : ℤ} (ha : a = a')
    (h : a = m + s) (h' : a' = m + s) (e : b = a + 1) (e' : b = a' + 1) (x : chowGroup C sP b) :
    capPow C sP ξ s a m h (ξ.capOnChow C sP a (chowGroupCast C sP e x)) =
      capPow C sP ξ s a' m h' (ξ.capOnChow C sP a' (chowGroupCast C sP e' x)) := by
  subst ha; rfl

/-- Pushforward along a closed immersion `i` carries `c₁(i^*L)^s ∩ -` to `c₁(L)^s ∩ -`. -/
private theorem properChowPushforward_invCap_capPow (C : ChowSituation.{u}) {D P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (i : D ⟶ P) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ sP)] (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible D.sheaf.obj D.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L)]
    (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C (i ≫ sP) a) :
    properChowPushforward C (i ≫ sP) sP i rfl m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP i rfl m)
        (capPow C (i ≫ sP) (invCap C (i ≫ sP) ((Scheme.Modules.pullback i).obj L)) s a m h x) =
      capPow C sP (invCap C sP L) s a m h
        (properChowPushforward C (i ≫ sP) sP i rfl a
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP i rfl a) x) :=
  capPow_comm C sP (invCap C sP L) (i ≫ sP)
    (invCap C (i ≫ sP) ((Scheme.Modules.pullback i).obj L))
    (fun d ↦ properChowPushforward C (i ≫ sP) sP i rfl d
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP i rfl d))
    (fun d x ↦ properChowPushforward_invCap C (i ≫ sP) sP i rfl L d x) s a m h x

/-! ### One step of a tower -/

section Step

variable (C : ChowSituation.{u}) {P U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (n + 1))
  (L : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π (Stacks.Divisors.zeroScheme P L s))
  [LocallyOfFiniteType ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)]
  [Flat ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)]
  (hq : AlgebraicGeometry.RelativeDimension
    ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π) n)

include hD in
/-- **Stacks 02TR on Chow groups, in the degrees of a tower.** If `D = Z(s)` is a relative
effective Cartier divisor, then `ξ ∩ π^*β = i_*((π|_D)^*β)` for every class `β` on the base. -/
theorem capOnChow_bundlePullback_eq (m : ℤ) (β : chowGroup C sU m) :
    (invCap C sP L).capOnChow C sP (m + n)
        (chowGroupCast C sP (by push_cast; ring)
          (bundlePullback C sU sP π hsP (n + 1) hπ m β)) =
      properChowPushforward C ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ sP) sP
        (Stacks.Divisors.zeroScheme P L s).subschemeι rfl (m + n)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP _ rfl (m + n))
        (bundlePullback C sU ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ sP)
          ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)
          (by rw [Category.assoc, hsP]) n hq m β) := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ β
  obtain ⟨s', rfl⟩ := exists_sections_eval_eq L s
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by ring⟩
  rw [bundlePullback_mk, chowGroupCast_mk, invCap_capOnChow_mk, bundlePullback_mk,
    properChowPushforward_mk]
  exact firstChernClassCapOfInvertible_flatPullback_divisor C sP sU π hsP n hπ k L s' hD hq
    (by push_cast; ring) b

end Step

/-! ### The top power along a tower -/

/-- **The top case of Stacks 02TW for a projective tower.** For a projective tower
`π : P ⟶ U` of fibre dimension `n` with twist `L` and every class `β` on `U`,

  `π_*(c₁(L)^n ∩ π^*β) = β`.

By induction along the tower: at the bottom `π` is an isomorphism; in fibre dimension `n + 1`,
`c₁(L) ∩ π^*β = i_*((π|_D)^*β)` by Stacks 02TR, the remaining `n` caps commute with `i_*` by
Stacks 02SU, and the induction hypothesis applies to `D ⟶ U` with `L|_D`. -/
theorem IsProjectiveTower.bundleProjection_self (C : ChowSituation.{u}) {n : ℕ}
    {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules} (h : IsProjectiveTower n π L) :
    ∀ (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
      (hsP : π ≫ sU = sP)
      [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
      [LocallyOfFiniteType π] [Flat π] [IsProper π]
      (hπ : AlgebraicGeometry.RelativeDimension π n) (k : ℤ) (β : chowGroup C sU k),
      bundleProjection C sU sP π hsP n hπ (invCap C sP L) n k k (by ring) β = β := by
  induction h with
  | zero π L hiso hL =>
    intro sU _ sP _ hsP _ _ _ _ hπ k β
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ β
    simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply, bundlePullback_mk,
      capPow_zero_apply, chowGroupCast_mk, properChowPushforward_mk]
    congr 1
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    obtain ⟨a, rfl⟩ := exists_base_eq_of_isIso π z
    rw [properPushforward_apply_of_isIso C sP sU π hsP k _ a, val_cycleGroup_cast,
      flatPullback_apply]
    by_cases hb : b.1 (π.base a) = 0
    · rw [hb, zero_mul]
    · have hdim : relativeDimension C.dimensionFunction sU (π.base a) = k :=
        (mem_cyclesOfDimension_iff_forall_point C sU k b.1).1 b.2 _ hb
      have hdim' : relativeDimension C.dimensionFunction sP a = k + ((0 : ℕ) : ℤ) := by
        rw [← hsP, relativeDimension_comp_closedImmersion, hdim]
        simp
      rw [flatPullbackWeight_of_isOpenImmersion C sP π _ a hdim', mul_one]
  | succ n π L hπ' s hD hq htower haff ih =>
    intro sU _ sP _ hsP _ _ _ _ hπ k β
    have := hD.2
    set i := (Stacks.Divisors.zeroScheme _ L s).subschemeι with hi
    let : AlgebraicGeometry.SheafOfModules.IsInvertible _ _
        ((Scheme.Modules.pullback i).obj L) := isInvertible_presheaf_modulePullback L i
    have hstep := capOnChow_bundlePullback_eq C sU sP π hsP n hπ L s hD hq k β
    have hIH := ih sU (i ≫ sP) (by rw [Category.assoc, hsP]) hq k β
    simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply] at hIH ⊢
    rw [capPow_succ_apply]
    rw [capPow_capOnChow_cast C sP (invCap C sP L) n (a' := k + n) (by push_cast; ring) _ _ _
      (by push_cast; ring), hstep, ← properChowPushforward_invCap_capPow C sP i L,
      ← AddMonoidHom.comp_apply (properChowPushforward C sP sU π hsP k _),
      properChowPushforward_comp]
    exact hIH

/-! ### Surjectivity along a tower -/

/-- **Stacks 02TT**: flat pullback along an affine-space bundle is
surjective on Chow groups. -/
def AffineBundleSurjectivity (C : ChowSituation.{u}) : Prop :=
  ∀ {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (f : A ⟶ B) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sB = sA)
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension f r), IsAffineSpaceBundle f r → ∀ k : ℤ,
      Function.Surjective (flatPullbackChow C sA sB f hf r hr k
        (flatPullbackFactorsThroughRationalEquivalence_general C sA sB f hf r hr k))

/-- The flat pullback along an isomorphism, followed by the pushforward, is the identity on
cycles; and the other way round. -/
theorem flatPullback_properPushforward_self_of_isIso (C : ChowSituation.{u}) {P U : Scheme.{u}}
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (π : P ⟶ U) [IsIso π] (hsP : π ≫ sU = sP) (k : ℤ) (c : CycleGroup C sP (k + ((0 : ℕ) : ℤ))) :
    (flatPullback C sP sU π hsP 0 (relativeDimension_of_isIso π) k
      (properPushforward C sP sU π hsP k ((by simp : k + ((0 : ℕ) : ℤ) = k) ▸ c))) = c := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun a ↦ ?_)
  rw [flatPullback_apply, properPushforward_apply_of_isIso C sP sU π hsP k _ a,
    val_cycleGroup_cast]
  by_cases hc : c.1 a = 0
  · rw [hc, zero_mul]
  · have hdim : relativeDimension C.dimensionFunction sP a = k + ((0 : ℕ) : ℤ) :=
      (mem_cyclesOfDimension_iff_forall_point C sP _ c.1).1 c.2 _ hc
    rw [flatPullbackWeight_of_isOpenImmersion C sP π _ a hdim, mul_one]

/-- Flat pullback along `π` commutes with transport along an equality of degrees. -/
private theorem bundlePullback_chowGroupCast (C : ChowSituation.{u}) {P U : Scheme.{u}}
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sU = sP) (n : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π n) {a b : ℤ} (e : a = b) (z : chowGroup C sU a) :
    bundlePullback C sU sP π hsP n hπ b (chowGroupCast C sU e z) =
      chowGroupCast C sP (by rw [e]) (bundlePullback C sU sP π hsP n hπ a z) := by
  subst e; rfl

section SurjStep

variable (C : ChowSituation.{u}) {P U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (n + 1))
  (L : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π (Stacks.Divisors.zeroScheme P L s))
  [LocallyOfFiniteType ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)]
  [Flat ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π)]
  (hq : AlgebraicGeometry.RelativeDimension
    ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π) n)
  [AlgebraicGeometry.SheafOfModules.IsInvertible _ _
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme P L s).subschemeι).obj L)]

include hD in
omit [AlgebraicGeometry.SheafOfModules.IsInvertible _ _
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme P L s).subschemeι).obj L)] in
/-- **The summands of the tower over `D` push forward to summands over `P`.** For a class `y` on
the base, `i_*(ξ_D^j ∩ (π|_D)^* y) = ξ^{j+1} ∩ π^* y`. -/
theorem properChowPushforward_bundleTerm (k : ℤ) (j : ℕ) (y : chowGroup C sU (k + 1 + j)) :
    properChowPushforward C ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ sP) sP
        (Stacks.Divisors.zeroScheme P L s).subschemeι rfl (k + ((n + 1 : ℕ) : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP _ rfl _)
        (chowGroupCast _ _ (by push_cast; ring)
          (bundleTerm C sU ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ sP)
            ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ π) (by rw [Category.assoc, hsP]) n
            hq (invCap C _ ((Scheme.Modules.pullback
              (Stacks.Divisors.zeroScheme P L s).subschemeι).obj L)) (k + 1) j y)) =
      bundleTerm C sU sP π hsP (n + 1) hπ (invCap C sP L) k (j + 1)
        (chowGroupCast C sU (by push_cast; ring) y) := by
  set i := (Stacks.Divisors.zeroScheme P L s).subschemeι with hi
  simp only [bundleTerm, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [capPow_succ_apply, bundlePullback_chowGroupCast, chowGroupCast_chowGroupCast]
  rw [capPow_capOnChow_cast C sP (invCap C sP L) j (a' := k + 1 + j + n) (by push_cast; ring) _ _ _
      (by push_cast; ring), capOnChow_bundlePullback_eq C sU sP π hsP n hπ L s hD hq,
    ← properChowPushforward_invCap_capPow C sP i L j (k + 1 + j + n) (k + ((n + 1 : ℕ) : ℤ))
      (by push_cast; ring), chowGroupCast_capPow]
  push_cast; ring

end SurjStep

/-- The zeroth summand of the map of Stacks 02TX is the flat pullback. -/
theorem bundleTerm_zero (C : ChowSituation.{u}) {P U : Scheme.{u}} (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U)
    [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sU = sP) (n : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π n) (ξ : ChernCapOperator C sP) (k : ℤ)
    (x : chowGroup C sU k) :
    bundleTerm C sU sP π hsP n hπ ξ k 0 (chowGroupCast C sU (by simp) x) =
      bundlePullback C sU sP π hsP n hπ k x := by
  rw [bundleTerm, AddMonoidHom.comp_apply, bundlePullback_chowGroupCast, capPow_zero_apply,
    chowGroupCast_chowGroupCast, chowGroupCast_rfl]

/-- Every summand of the map of Stacks 02TX lies in its range. -/
theorem bundleTerm_mem_range (C : ChowSituation.{u}) {P U : Scheme.{u}} (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U)
    [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sU = sP) (n : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π n) (ξ : ChernCapOperator C sP) (k : ℤ)
    (i : Fin (n + 1)) (x : chowGroup C sU (k + (i : ℕ))) :
    bundleTerm C sU sP π hsP n hπ ξ k i x ∈ (bundleMap C sU sP π hsP n hπ ξ k).range := by
  classical
  refine ⟨Pi.single i x, ?_⟩
  rw [bundleMap_apply, Finset.sum_eq_single i (fun j _ hj ↦ by
    rw [Pi.single_eq_of_ne hj, map_zero]) (by simp), Pi.single_eq_same]

/-- Restriction to an open subscheme of a flat pullback along `π` is the flat pullback along the
restriction of `π`. -/
theorem chowGroupRestrict_bundlePullback (C : ChowSituation.{u}) {P U : Scheme.{u}}
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sU = sP) (n : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π n) (V : P.Opens)
    (hV : AlgebraicGeometry.RelativeDimension (V.ι ≫ π) n) (k : ℤ) (β : chowGroup C sU k) :
    chowGroupRestrict C sP (V.ι ≫ sP) V.ι rfl (k + n) (bundlePullback C sU sP π hsP n hπ k β) =
      bundlePullback C sU (V.ι ≫ sP) (V.ι ≫ π) (by rw [Category.assoc, hsP]) n hV k β := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ β
  rw [bundlePullback_mk, chowGroupRestrict_mk, bundlePullback_mk]
  congr 1
  have h := cycleGroupRestrict_flatPullback C sP sU (V.ι ≫ sP) sU π hsP n hπ V.ι rfl (𝟙 U)
    (by simp) (V.ι ≫ π) (by rw [Category.assoc, hsP]) (by simp) hV k b
  rw [h]
  congr 1

/-- **Surjectivity of the map of Stacks 02TX along a projective tower**, granted Stacks 02TT. By
induction along the tower: a class on `P` restricts on the complement of `D`, an affine-space
bundle, to a flat pullback (Stacks 02TT), so it differs from a flat pullback by a class pushed
forward from `D` (Stacks 02RX); the induction hypothesis writes that class through the tower of
`D`, and its summands push forward to summands of the tower of `P`. -/
theorem IsProjectiveTower.bundleMap_surjective (C : ChowSituation.{u})
    (hTT : AffineBundleSurjectivity C) {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules}
    (h : IsProjectiveTower n π L) :
    ∀ (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
      (hsP : π ≫ sU = sP)
      [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
      [LocallyOfFiniteType π] [Flat π]
      (hπ : AlgebraicGeometry.RelativeDimension π n) (k : ℤ),
      Function.Surjective (bundleMap C sU sP π hsP n hπ (invCap C sP L) k) := by
  induction h with
  | zero π L hiso hL =>
    intro sU _ sP _ hsP _ _ _ hπ k γ
    set y := properChowPushforward C sP sU π hsP k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP k)
      (chowGroupCast C sP (by simp) γ) with hy
    refine ⟨fun i ↦ chowGroupCast C sU (by rw [Fin.val_eq_zero i]; simp) y, ?_⟩
    rw [bundleMap_apply, Fin.sum_univ_one]
    simp only [bundleTerm, AddMonoidHom.coe_comp, Function.comp_apply, Fin.val_zero,
      capPow_zero_apply, bundlePullback_chowGroupCast, chowGroupCast_chowGroupCast]
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ γ
    rw [hy, chowGroupCast_mk, properChowPushforward_mk, bundlePullback_mk, chowGroupCast_mk]
    congr 1
    exact flatPullback_properPushforward_self_of_isIso C sU sP π hsP k c
  | succ n π L hπ' s hD hq htower haff ih =>
    intro sU _ sP _ hsP _ _ _ hπ k γ
    have := hD.2
    set i := (Stacks.Divisors.zeroScheme _ L s).subschemeι with hi
    let : AlgebraicGeometry.SheafOfModules.IsInvertible _ _
        ((Scheme.Modules.pullback i).obj L) := isInvertible_presheaf_modulePullback L i
    set V := zeroSchemeComplement _ L s with hVdef
    have hV : AlgebraicGeometry.RelativeDimension (V.ι ≫ π) (n + 1) :=
      relativeDimension_of_isAffineSpaceBundle _ _ haff
    obtain ⟨β0, hβ0⟩ := hTT (V.ι ≫ sP) sU (V.ι ≫ π) (by rw [Category.assoc, hsP]) (n + 1) hV
      haff k (chowGroupRestrict C sP (V.ι ≫ sP) V.ι rfl _ γ)
    have hcompl : Set.range i.base = (Set.range V.ι.base)ᶜ := by
      rw [Scheme.Opens.range_ι, hVdef, zeroSchemeComplement]
      simp [hi, Scheme.IdealSheafData.range_subschemeι]
    have hres : chowGroupOpensRestrictOfIsOpenImmersion C sP V _
        (γ - bundlePullback C sU sP π hsP (n + 1) hπ k β0) = 0 := by
      have heq : ∀ x, chowGroupOpensRestrictOfIsOpenImmersion C sP V (k + ((n + 1 : ℕ) : ℤ)) x =
          chowGroupRestrict C sP (V.ι ≫ sP) V.ι rfl _ x := by
        intro x
        obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
        rfl
      rw [heq, map_sub, chowGroupRestrict_bundlePullback C sU sP π hsP (n + 1) hπ V hV, ← hβ0]
      exact sub_self _
    obtain ⟨δ, hδ⟩ := (exact_chowPushforward_chowGroupOpensRestrict C sP (i ≫ sP) i rfl V
      hcompl _ _).1 hres
    obtain ⟨βD, hβD⟩ := ih sU (i ≫ sP) (by rw [Category.assoc, hsP]) hq (k + 1)
      (chowGroupCast _ _ (by push_cast; ring) δ)
    rw [bundleMap_apply] at hβD
    have hγ : γ = bundlePullback C sU sP π hsP (n + 1) hπ k β0 +
        chowPushforwardOfIsClosedImmersion C (i ≫ sP) sP i rfl _ δ := by
      rw [hδ]; abel
    rw [← AddMonoidHom.mem_range, hγ]
    refine AddSubgroup.add_mem _ ?_ ?_
    · have h0 := bundleTerm_mem_range C sU sP π hsP (n + 1) hπ (invCap C sP L) k 0
        (chowGroupCast C sU (by simp) β0)
      have hterm := bundleTerm_zero C sU sP π hsP (n + 1) hπ (invCap C sP L) k β0
      rw [← hterm]
      exact h0
    · have hδ' : δ = chowGroupCast _ _ (by push_cast; ring)
          (∑ j : Fin (n + 1), bundleTerm C sU (i ≫ sP) (i ≫ π) (by rw [Category.assoc, hsP]) n
            hq (invCap C (i ≫ sP) ((Scheme.Modules.pullback i).obj L)) (k + 1) j (βD j)) := by
        rw [hβD, chowGroupCast_chowGroupCast, chowGroupCast_rfl]
      rw [hδ', map_sum, map_sum]
      refine AddSubgroup.sum_mem _ fun j _ ↦ ?_
      have hj := properChowPushforward_bundleTerm C sU sP π hsP n hπ L s hD hq k j (βD j)
      have hmem := bundleTerm_mem_range C sU sP π hsP (n + 1) hπ (invCap C sP L) k j.succ
        (chowGroupCast C sU (by simp only [Fin.val_succ]; push_cast; ring) (βD j))
      have hmem' : bundleTerm C sU sP π hsP (n + 1) hπ (invCap C sP L) k ((j : ℕ) + 1)
          (chowGroupCast C sU (by push_cast; ring) (βD j)) ∈
          (bundleMap C sU sP π hsP (n + 1) hπ (invCap C sP L) k).range := hmem
      rw [← hj] at hmem'
      exact hmem'

end Stacks.Chow

end
