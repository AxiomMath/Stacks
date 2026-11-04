module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IteratedChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassCommute
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Map

/-!
# Powers of a first Chern class cap commute with pullback, pushforward and bivariant classes

For an invertible module `ℒ` the operation `ξ^s ∩ - = c₁(ℒ)^s ∩ -` on Chow groups
(`Stacks.Chow.capPow`) commutes with

* flat pullback, `f^*(c₁(ℒ)^s ∩ x) = c₁(f^*ℒ)^s ∩ f^*x` (Stacks 02SS, iterated);
* capping with a Chow cohomology class `c ∈ A^p(X)`, `c ∩ (c₁(ℒ)^s ∩ x) = c₁(ℒ)^s ∩ (c ∩ x)`
  (Stacks 0B7B, iterated).

Both are instances, as is the commutation with proper pushforward
(`Stacks.Chow.properChowPushforward_capPow`), of one formal statement,
`Stacks.Chow.capPow_comm_shift`: an additive
family `F_d : A_d(Q) ⟶ A_{d+r}(P)` intertwining one cap with another intertwines their powers.

## Main results

* `Stacks.Chow.capPow_comm_shift`: the formal statement.
* `Stacks.Chow.flatPullbackChowOfRelativeDimension_capPow`: flat pullback.
* `Stacks.Chow.chowCohomologyCap_invCap_capOnChow` and `Stacks.Chow.chowCohomologyCap_capPow`:
  capping with a Chow cohomology class.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Shift

variable (C : ChowSituation.{u}) {P Q : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ] (ξ : ChernCapOperator C sP) (η : ChernCapOperator C sQ)

/-- The cap operation at heterogeneously equal arguments in equal degrees. -/
theorem ChernCapOperator.capOnChow_heq {d d' : ℤ} (hd : d = d') {x : chowGroup C sP (d + 1)}
    {y : chowGroup C sP (d' + 1)} (hxy : x ≍ y) :
    ξ.capOnChow C sP d x ≍ ξ.capOnChow C sP d' y := by
  subst hd
  cases hxy
  rfl

/-- A power of a cap at heterogeneously equal arguments in equal source degrees. -/
theorem capPow_heq (s : ℕ) {a a' : ℤ} (m : ℤ) (h : a = m + s) (h' : a' = m + s) (ha : a = a')
    {x : chowGroup C sP a} {y : chowGroup C sP a'} (hxy : x ≍ y) :
    capPow C sP ξ s a m h x = capPow C sP ξ s a' m h' y := by
  subst ha
  cases hxy
  rfl

/-- A power of a cap at heterogeneously equal arguments in equal source and target degrees. -/
theorem capPow_heq_of_heq (s : ℕ) {a a' m m' : ℤ} (h : a = m + s) (h' : a' = m' + s)
    (ha : a = a') (hm : m = m') {x : chowGroup C sP a} {y : chowGroup C sP a'} (hxy : x ≍ y) :
    capPow C sP ξ s a m h x ≍ capPow C sP ξ s a' m' h' y := by
  subst ha hm
  cases hxy
  rfl

/-- **Powers of caps commute with a shifting family.** An additive family
`F_d : A_d(Q) ⟶ A_{d+r}(P)` carrying `η ∩ -` to `ξ ∩ -` carries `η^s ∩ -` to `ξ^s ∩ -`. -/
theorem capPow_comm_shift (r : ℤ) (F : ∀ d : ℤ, chowGroup C sQ d →+ chowGroup C sP (d + r))
    (hF : ∀ (d : ℤ) (x : chowGroup C sQ (d + 1)),
      F d (η.capOnChow C sQ d x) =
        ξ.capOnChow C sP (d + r) (chowGroupCast C sP (by ring) (F (d + 1) x)))
    (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C sQ a) :
    F m (capPow C sQ η s a m h x) = capPow C sP ξ s (a + r) (m + r) (by omega) (F a x) := by
  have hFheq : ∀ {d d' : ℤ} (e : d = d') {y : chowGroup C sQ d} {y' : chowGroup C sQ d'},
      y ≍ y' → F d y ≍ F d' y' := by
    intro d d' e y y' hy; subst e; cases hy; rfl
  induction s generalizing a with
  | zero =>
    rw [capPow_zero_apply, capPow_zero_apply]
    exact eq_of_heq ((hFheq (by simp at h; omega) (chowGroupCast_heq C sQ _ x)).trans
      (chowGroupCast_heq C sP _ _).symm)
  | succ s ih =>
    rw [capPow_succ_apply, ih, hF, capPow_succ_apply]
    refine capPow_heq C sP ξ s (m + r) _ _ (by ring) ?_
    refine ChernCapOperator.capOnChow_heq C sP ξ (by ring) ?_
    exact (chowGroupCast_heq C sP _ _).trans ((hFheq (by ring)
      (chowGroupCast_heq C sQ _ x)).trans (chowGroupCast_heq C sP _ _).symm)

end Shift

section Flat

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
  (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Flat pullback commutes with powers of a first Chern class cap** (Stacks 02SS, iterated):
`f^*(c₁(ℒ)^s ∩ x) = c₁(f^*ℒ)^s ∩ f^*x`. -/
theorem flatPullbackChowOfRelativeDimension_capPow (s : ℕ) (a m : ℤ) (h : a = m + s)
    (x : chowGroup C sX a) :
    haveI := GenuineChern.isInvertible_pullback f L
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf m
        (capPow C sX (invCap C sX L) s a m h x) =
      capPow C sX' (invCap C sX' ((Scheme.Modules.pullback f).obj L)) s (a + r) (m + r)
        (by omega) (flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf a x) := by
  have := GenuineChern.isInvertible_pullback f L
  refine capPow_comm_shift C sX' sX _ _ r
    (flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf)
    (fun d y ↦ ?_) s a m h x
  exact flatPullbackChowOfRelativeDimension_invCap_capOnChow C sX' sX f hbase r hf L d y _
    (chowGroupCast_heq C sX' _ _).symm

end Flat

section Cohomology

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- Transport along an equality of structure morphisms commutes with the first Chern class cap
of an invertible module. -/
theorem chowGroupCongr_invCap_capOnChow {q q' : X ⟶ C.S} [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (hq : q = q') (k : ℤ) (x : chowGroup C q (k + 1)) :
    chowGroupCongr C hq k ((invCap C q L).capOnChow C q k x) =
      (invCap C q' L).capOnChow C q' k (chowGroupCongr C hq (k + 1) x) := by
  subst hq
  rfl

/-- **Capping with a Chow cohomology class commutes with the first Chern class cap of an
invertible module** (Stacks 0B7B on `X` itself): `c ∩ (c₁(ℒ) ∩ x) = c₁(ℒ) ∩ (c ∩ x)` for
`c ∈ A^p(X)`. -/
theorem chowCohomologyCap_invCap_capOnChow {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) (k : ℤ)
    (x : chowGroup C sX (k + 1)) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX p c k ((invCap C sX L).capOnChow C sX k x) =
      (invCap C sX L).capOnChow C sX (k - p)
        (chowGroupCast C sX (by ring)
          (chowCohomologyCap C (gysinSystemOfInvertible C) sX p c (k + 1) x)) := by
  have hfs : pullback.fst (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) (𝟙 X) := by
    simpa using (pullback.condition (f := 𝟙 X) (g := 𝟙 X))
  have := GenuineChern.isInvertible_pullback (pullback.snd (𝟙 X) (𝟙 X)) L
  have := GenuineChern.isInvertible_pullback (pullback.fst (𝟙 X) (𝟙 X)) L
  simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [chowGroupCongr_invCap_capOnChow]
  have key := BivariantClass.cap_firstChernClassCapChow c (𝟙 X) L
    ((Scheme.Modules.pullback (pullback.snd (𝟙 X) (𝟙 X))).obj L) (Iso.refl _) k
    (chowGroupCongr C (Category.id_comp sX).symm (k + 1) x)
    (chowGroupCast C _ (by ring) (c.cap (𝟙 X) (k + 1)
      (chowGroupCongr C (Category.id_comp sX).symm (k + 1) x)))
    (chowGroupCast_heq C _ _ _)
  rw [← invCap_capOnChow_eq, ← invCap_capOnChow_eq] at key
  rw [key]
  have hL : (Scheme.Modules.pullback (pullback.snd (𝟙 X) (𝟙 X))).obj L ≅
      (Scheme.Modules.pullback (pullback.fst (𝟙 X) (𝟙 X))).obj L :=
    eqToIso (by rw [hfs])
  rw [invCap_capOnChow_congr C _ _ _ hL]
  rw [chowGroupEquivOfIso_apply, chowPushforwardOfIso,
    properChowPushforward_invCap C _ sX (pullback.fst (𝟙 X) (𝟙 X)) rfl L (k - p)]
  congr 1
  rw [chowGroupEquivOfIso_apply, chowPushforwardOfIso]
  refine eq_of_heq ((properChowPushforward_heq_congr C _ sX _ rfl (by ring) _ _ _ _
    (chowGroupCast_heq C _ _ _)).trans (chowGroupCast_heq C sX _ _).symm)

/-- **Capping with a Chow cohomology class commutes with powers of a first Chern class cap**:
`c ∩ (c₁(ℒ)^s ∩ x) = c₁(ℒ)^s ∩ (c ∩ x)` for `c ∈ A^p(X)`. -/
theorem chowCohomologyCap_capPow {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) (s : ℕ) (a m : ℤ)
    (h : a = m + s) (x : chowGroup C sX a) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX p c m
        (capPow C sX (invCap C sX L) s a m h x) =
      capPow C sX (invCap C sX L) s (a - p) (m - p) (by omega)
        (chowCohomologyCap C (gysinSystemOfInvertible C) sX p c a x) :=
  capPow_comm_shift C sX sX (invCap C sX L) (invCap C sX L) (-p)
    (fun d ↦ chowCohomologyCap C (gysinSystemOfInvertible C) sX p c d)
    (fun d y ↦ chowCohomologyCap_invCap_capOnChow C sX L c d y) s a m h x

end Cohomology

end Stacks.Chow

end
