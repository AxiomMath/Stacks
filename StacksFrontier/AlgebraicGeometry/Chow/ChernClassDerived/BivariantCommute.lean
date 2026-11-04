module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClassGenuine
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Independence
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.BirationalModification
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.NonhomogeneousComposite
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernPowerSumDescent

/-!
# The Chern classes of a perfect object commute with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E ∈ D(𝒪_X)` be perfect, with Chern classes defined (Stacks 0F9E).
**Stacks 0FAC** says that

1. `c_p(E)` is in the center of the algebra `A^*(X)`, and
2. if `g : X' ⟶ X` is locally of finite type and `c ∈ A^*(X' ⟶ X)`, then
   `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`.

Part (1) is part (2) for `g = 𝟙 X`. For part (2) the proof is the source's. By the criterion of
Stacks 02UC it suffices to compare the two composites on the fundamental class of a proper
birational modification of every integral scheme `T` over `X`. By Stacks 0GUF such a
modification `T'` factors through the envelope `Y ⟶ X` of a presentation of `E` by a locally
bounded complex `𝓔^•` of finite locally free modules; on the integral scheme `T'` the pullback of
`𝓔^•` is bounded with constant ranks, and there `c(E)` operates as
`∏_n c(𝓔^n|_{T'})^{(-1)^n}` and `c(Lg^*E)` as the same product for the pullback of `𝓔^•` to
`T' ×_X X'`. Capping with `c` intertwines the total Chern classes of the terms by Stacks 02UA
(`Stacks.Chow.genuineChernCap_bivariantClass_comm`), hence their alternating product.

The power sums `P_p(E)` of Stacks 0GUD satisfy Newton's identities in the Chern classes of `E`
(Stacks 0FAD), so for `p ≥ 1` they commute with `c` as well; `P_0(E)` is the rank, which is
handled on the integral modifications as the Chern classes are.

## Main definitions

* `Stacks.Chow.BivariantClass.IntertwinesTotal` — that `c ∈ A^q(X' ⟶ X)` carries a total class
  of `X` to a total class of `X'`: on every test scheme, capping with `c` intertwines their
  operations.

## Main results

* `Stacks.Chow.Intertwines.of_mul_eq_one` — an intertwiner of two graded cap families intertwines
  their inverses.
* `Stacks.Chow.BivariantClass.intertwines_chernFamily` — Stacks 02UA on a test scheme, for the
  total Chern classes of a module and its pullback.
* `Stacks.Chow.BivariantClass.intertwinesTotal_iff` — the intertwining is the identity
  `c ∘ x_p = x'_p ∘ c` of composites, in every degree.
* `Stacks.Chow.nonhomogeneousBivariantGroupCongr_compositeOfInvertible_perfectChernClass` —
  **Stacks 0FAC (2)**, and
  `Stacks.Chow.BivariantClass.heq_bivariantCompositeOfInvertible_perfectChernClass`, its case of
  a homogeneous `c`.
* `Stacks.Chow.nonhomogeneousBivariantGroupCongr_compositeOfInvertible_perfectChernClass_comm` —
  **Stacks 0FAC (1)**, and `Stacks.Chow.BivariantClass.heq_mulId_perfectChernClass`, its case of a
  homogeneous `c`.
* `Stacks.Chow.BivariantClass.heq_bivariantCompositeOfInvertible_perfectPowerSum`,
  `Stacks.Chow.BivariantClass.heq_mulId_perfectPowerSum` — the same for the power sums `P_p(E)`.

## Implementation notes

The two composites are classes for the equal morphisms `g ≫ 𝟙 X` and `𝟙 X' ≫ g`, of the equal
degrees `q + p` and `p + q`, so part (2) is a heterogeneous equality, and so is part (1) for the
two products in `A^*(X)`, for a homogeneous `c`. The source's `c ∈ A^*(X' ⟶ X)` is an element of
`⨁_q A^q(X' ⟶ X)`; for it the composition is its additive extension
`Stacks.Chow.nonhomogeneousBivariantCompositeOfInvertible`, the two degrees are the same summand,
and both composites are read as classes for `g` (for `𝟙 X` in part (1)) through
`Stacks.Chow.nonhomogeneousBivariantGroupCongr`, so that both parts are equalities in the graded
group. The class `c_p(E) ∈ A^p(X)` is the degree-`p` component of the total Chern class
`Stacks.Chow.perfectChernClass` of Stacks 0F9E (2).

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0GUF](https://stacks.math.columbia.edu/tag/0GUF)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0FAD](https://stacks.math.columbia.edu/tag/0FAD)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u v

namespace Stacks.Chow

/-! ### Intertwining graded cap families -/

section Intertwines

variable {G H : ℤ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)] {d : ℤ}
  {pull : ∀ k : ℤ, G k →+ H (k + d)}

/-- An intertwiner of two graded cap families intertwines their integer multiples. -/
theorem Intertwines.zsmul {a : GradedCapFamily G} {a' : GradedCapFamily H}
    (ha : Intertwines pull a a') (n : ℤ) : Intertwines pull (n • a) (n • a') := by
  intro k i x
  simp only [Pi.smul_apply, AddMonoidHom.smul_apply, map_zsmul, ha k i x]

/-- An intertwiner `pull` of two graded cap families carries `Stacks.Chow.capTo` of the first to
`Stacks.Chow.capTo` of the second, in the indices at which it intertwines them. -/
theorem capTo_of_intertwines_at {a : GradedCapFamily G} {a' : GradedCapFamily H} {j : ℕ}
    (ha : ∀ (k : ℤ) (x : G k), pull (k - (j : ℤ)) (a k j x) =
      gradedDegreeCast H (show k + d - (j : ℤ) = k - (j : ℤ) + d by omega)
        (a' (k + d) j (pull k x)))
    {k n : ℤ} (h : k - (j : ℤ) = n) (x : G k) :
    pull n (capTo a j h x) = capTo a' j (show k + d - (j : ℤ) = n + d by omega) (pull k x) := by
  subst h
  rw [capTo_def, capTo_def, gradedDegreeCast_rfl, ha k x]

/-- **An intertwiner of two graded cap families intertwines their inverses.** If `pull`
intertwines `a` and `a'`, and `b`, `b'` are right inverses of `a`, `a'`, the index-`0` component
of `a'` being the identity, then `pull` intertwines `b` and `b'`.

The proof is by induction on the index: the index-`i` component of `a * b = 1` expresses `b^i`
through the components `b^j`, `j < i`, and `a^0 = 1`, and so does that of `a' * b' = 1` for
`b'^i`. -/
theorem Intertwines.of_mul_eq_one {a b : GradedCapFamily G} {a' b' : GradedCapFamily H}
    (ha : Intertwines pull a a') (hab : a * b = 1) (ha'b' : a' * b' = 1)
    (ha' : ∀ k, a' k 0 = (1 : GradedCapFamily H) k 0) : Intertwines pull b b' := by
  intro k i
  induction i using Nat.strong_induction_on generalizing k with
  | _ i IH =>
  intro x
  have Hj : ∀ j < i, ∀ (k' n : ℤ) (h : k' - (j : ℤ) = n) (y : G k'),
      pull n (Stacks.Chow.capTo b j h y) =
        Stacks.Chow.capTo b' j (show k' + d - (j : ℤ) = n + d by omega) (pull k' y) :=
    fun j hj _ _ h y ↦ capTo_of_intertwines_at (fun k x ↦ IH j hj k x) h y
  -- the index-`i` components of `a * b = 1` and of `a' * b' = 1`
  have e1 : pull (k - (i : ℤ)) ((a * b) k i x) =
      pull (k - (i : ℤ)) ((1 : GradedCapFamily G) k i x) :=
    congrArg (fun F : GradedCapFamily G ↦ pull (k - (i : ℤ)) (F k i x)) hab
  have e2 : (a' * b') (k + d) i (pull k x) = (1 : GradedCapFamily H) (k + d) i (pull k x) :=
    congrArg (fun F : GradedCapFamily H ↦ F (k + d) i (pull k x)) ha'b'
  rw [Intertwines.one k i x, ← e2, gradedCap_mul_apply, Finset.sum_range_succ, map_add,
    map_sum, gradedCap_mul_apply, Finset.sum_range_succ, map_add, map_sum] at e1
  have hsum : ∑ j ∈ range i, pull (k - (i : ℤ)) (convolveTerm a b k i j x) =
      ∑ j ∈ range i, gradedDegreeCast H (show k + d - (i : ℤ) = k - (i : ℤ) + d by omega)
        (convolveTerm a' b' (k + d) i j (pull k x)) := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hji : j < i := mem_range.mp hj
    rw [convolveTerm_of_le _ _ _ hji.le, convolveTerm_of_le _ _ _ hji.le,
      ha.capTo (i - j) _ (b k j x),
      show b k j x = Stacks.Chow.capTo b j rfl x from rfl, Hj j hji k _ rfl x, capTo_capTo,
      gradedDegreeCast_capTo]
  rw [hsum, add_left_cancel_iff, convolveTerm_of_le _ _ _ le_rfl,
    convolveTerm_of_le _ _ _ le_rfl, ha.capTo (i - i) _ (b k i x)] at e1
  -- the last summands are `b^i` and `b'^i`, up to transport
  have hlast : ∀ {H : ℤ → Type v} [∀ k, AddCommGroup (H k)] (a' : GradedCapFamily H)
      (_ : ∀ k, a' k 0 = (1 : GradedCapFamily H) k 0) (m : ℤ) (y : H m),
      a' m (i - i) y ≍ y := by
    intro H _ a' ha' m y
    rw [Nat.sub_self, ha', gradedCap_one_apply_zero]
    exact gradedDegreeCast_heq _ y
  have hl : pull (k - (i : ℤ)) (b k i x) ≍ b' (k + d) i (pull k x) := by
    have h1 := heq_of_eq e1
    rw [capTo_def, capTo_def] at h1
    exact (hlast a' ha' _ _).symm.trans ((gradedDegreeCast_heq _ _).symm.trans (h1.trans
      ((gradedDegreeCast_heq _ _).trans ((gradedDegreeCast_heq _ _).trans
        (hlast a' ha' _ _)))))
  exact eq_of_heq (hl.trans (gradedDegreeCast_heq _ _).symm)

/-- An intertwiner of two units of the rings of graded cap families, the index-`0` component of
the second being the identity, intertwines all their integer powers. -/
theorem Intertwines.zpow {u : (GradedCapFamily G)ˣ} {u' : (GradedCapFamily H)ˣ}
    (hu : Intertwines pull (u : GradedCapFamily G) (u' : GradedCapFamily H))
    (hu' : ∀ k, (u' : GradedCapFamily H) k 0 = (1 : GradedCapFamily H) k 0) (n : ℤ) :
    Intertwines pull ((u ^ n : (GradedCapFamily G)ˣ) : GradedCapFamily G)
      ((u' ^ n : (GradedCapFamily H)ˣ) : GradedCapFamily H) := by
  have hpow : ∀ {v : (GradedCapFamily G)ˣ} {v' : (GradedCapFamily H)ˣ},
      Intertwines pull (v : GradedCapFamily G) (v' : GradedCapFamily H) → ∀ m : ℕ,
      Intertwines pull ((v ^ m : (GradedCapFamily G)ˣ) : GradedCapFamily G)
        ((v' ^ m : (GradedCapFamily H)ˣ) : GradedCapFamily H) := by
    intro v v' hv m
    induction m with
    | zero => simpa using Intertwines.one
    | succ m ih => simpa [pow_succ] using ih.mul hv
  have hinv : Intertwines pull ((u⁻¹ : (GradedCapFamily G)ˣ) : GradedCapFamily G)
      ((u'⁻¹ : (GradedCapFamily H)ˣ) : GradedCapFamily H) :=
    hu.of_mul_eq_one u.mul_inv u'.mul_inv hu'
  rcases n with m | m
  · simpa using hpow hu m
  · simpa [zpow_negSucc, inv_pow] using hpow hinv (m + 1)

/-- An intertwiner of finitely many pairs of units of the rings of graded cap families, the
index-`0` components of the second units being the identity, intertwines the ordered products of
their integer powers. -/
theorem Intertwines.list_prod_zpow {ι : Type*} (l : List ι) {u : ι → (GradedCapFamily G)ˣ}
    {u' : ι → (GradedCapFamily H)ˣ}
    (hu : ∀ n ∈ l, Intertwines pull (u n : GradedCapFamily G) (u' n : GradedCapFamily H))
    (hu' : ∀ n ∈ l, ∀ k, (u' n : GradedCapFamily H) k 0 = (1 : GradedCapFamily H) k 0)
    (e : ι → ℤ) :
    Intertwines pull (((l.map fun n ↦ u n ^ e n).prod : (GradedCapFamily G)ˣ) : GradedCapFamily G)
      (((l.map fun n ↦ u' n ^ e n).prod : (GradedCapFamily H)ˣ) : GradedCapFamily H) := by
  induction l with
  | nil => simpa using Intertwines.one
  | cons n l ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    exact ((hu n (List.mem_cons_self ..)).zpow (hu' n (List.mem_cons_self ..)) (e n)).mul
      (ih (fun m hm ↦ hu m (List.mem_cons_of_mem _ hm))
        (fun m hm ↦ hu' m (List.mem_cons_of_mem _ hm)))

end Intertwines

/-! ### Bivariant classes and total classes -/

section Bivariant

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {g : X' ⟶ X} [LocallyOfFiniteType g]
  {hg : g ≫ sX = sX'} {q : ℤ}

/-- A bivariant class transported along an equality of degrees is heterogeneously equal to the
class. -/
theorem bivariantClassDegreeCongr_heq {G : GysinSystem C} {p p' : ℤ} (h : p = p')
    (c : BivariantClass C G sX' sX g hg p) :
    bivariantClassDegreeCongr C G sX' sX g hg h c ≍ c := by
  subst h
  rfl

/-- **Stacks 02UA on a test scheme, for total Chern classes.** For `c ∈ A^q(X' ⟶ X)`, a test
scheme `t : T ⟶ X`, a finite locally free `ℱ` of rank `r` on `T` and a module `ℱ'` on
`T ×_X X'` isomorphic to its pullback, capping with `c` intertwines the total Chern classes
`c(ℱ)` and `c(ℱ')`. -/
theorem BivariantClass.intertwines_chernFamily
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (F : T.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (F' : (pullback g t).Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r]
    (eF : F' ≅ (Scheme.Modules.pullback (pullback.snd g t)).obj F) :
    Intertwines (d := -q) (fun k ↦ c.cap t k) (GenuineChern.chernFamily C (t ≫ sX) F r)
      (GenuineChern.chernFamily C (pullback.fst g t ≫ sX') F' r) := by
  intro k i α
  dsimp only [GenuineChern.chernFamily]
  by_cases hi : i ≤ r
  · rw [chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) _ F r k hi,
      chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) _ F' r (k + -q) hi]
    exact eq_of_heq ((genuineChernCap_bivariantClass_comm c t r F F' eF k
      ⟨i, Nat.lt_succ_of_le hi⟩ α).trans (gradedDegreeCast_heq _ _).symm)
  · rw [chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) _ F r k hi,
      chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) _ F' r (k + -q) hi]
    simp

/-- That a bivariant class `c ∈ A^q(X' ⟶ X)` **carries the total class `x` of `X` to the total
class `x'` of `X'`**: on every test scheme `t : T ⟶ X`, capping with `c` intertwines the
operation of `x` on `T` and the operation of `x'` on `T ×_X X' ⟶ X'`,

  `c ∩ (x_p ∩ α) = x'_p ∩ (c ∩ α)`   for every `p` and `α ∈ A_k(T)`.

By `Stacks.Chow.BivariantClass.intertwinesTotal_iff` this is the identity `c ∘ x_p = x'_p ∘ c` of
composites in every degree. -/
def BivariantClass.IntertwinesTotal
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q) (x : TotalChowClass C sX)
    (x' : TotalChowClass C sX') : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ X) [LocallyOfFiniteType t],
    Intertwines (d := -q) (fun k ↦ c.cap t k) (x.op t) (x'.op (pullback.fst g t))

variable {c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q}
  {x y : TotalChowClass C sX} {x' y' : TotalChowClass C sX'}

/-- **The intertwining is the commutation of composites.** A bivariant class `c` carries `x` to
`x'` exactly when `c ∘ x_p = x'_p ∘ c` for every `p`, the composites being classes for the equal
morphisms `g ≫ 𝟙 X` and `𝟙 X' ≫ g`. -/
theorem BivariantClass.intertwinesTotal_iff :
    c.IntertwinesTotal x x' ↔ ∀ p : ℕ,
      bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q p c (x p) ≍
        bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg p q
          (x' p) c :=
  ⟨fun h p ↦ (c.heq_bivariantCompositeOfInvertible_iff _ _).2 fun t _ k α ↦
    (heq_of_eq (h t k p α)).trans (gradedDegreeCast_heq _ _),
  fun h _ t _ k p α ↦ eq_of_heq
    (((c.heq_bivariantCompositeOfInvertible_iff _ _).1 (h p) t k α).trans
      (gradedDegreeCast_heq _ _).symm)⟩

/-- The unit total classes are carried to one another. -/
theorem BivariantClass.IntertwinesTotal.one :
    c.IntertwinesTotal (1 : TotalChowClass C sX) (1 : TotalChowClass C sX') := fun _ t _ ↦ by
  rw [TotalChowClass.op_one, TotalChowClass.op_one]
  exact Intertwines.one

/-- Products of total classes carried to one another are carried to one another. -/
theorem BivariantClass.IntertwinesTotal.mul (hx : c.IntertwinesTotal x x')
    (hy : c.IntertwinesTotal y y') : c.IntertwinesTotal (x * y) (x' * y') := fun _ t _ ↦ by
  rw [TotalChowClass.op_mul, TotalChowClass.op_mul]
  exact (hx t).mul (hy t)

/-- Sums of total classes carried to one another are carried to one another. -/
theorem BivariantClass.IntertwinesTotal.add (hx : c.IntertwinesTotal x x')
    (hy : c.IntertwinesTotal y y') : c.IntertwinesTotal (x + y) (x' + y') := fun _ t _ ↦ by
  rw [TotalChowClass.op_add, TotalChowClass.op_add]
  exact (hx t).add (hy t)

/-- Integer multiples of total classes carried to one another are carried to one another. -/
theorem BivariantClass.IntertwinesTotal.zsmul (hx : c.IntertwinesTotal x x') (n : ℤ) :
    c.IntertwinesTotal (n • x) (n • x') := fun _ t _ ↦ by
  rw [← TotalChowClass.opHom_apply, ← TotalChowClass.opHom_apply, map_zsmul, map_zsmul]
  exact (hx t).zsmul n

/-- Finite sums of total classes carried to one another are carried to one another. -/
theorem BivariantClass.IntertwinesTotal.sum {ι : Type*} (s : Finset ι)
    {x : ι → TotalChowClass C sX} {x' : ι → TotalChowClass C sX'}
    (hx : ∀ i ∈ s, c.IntertwinesTotal (x i) (x' i)) :
    c.IntertwinesTotal (∑ i ∈ s, x i) (∑ i ∈ s, x' i) := fun _ t _ ↦ by
  rw [TotalChowClass.op_sum, TotalChowClass.op_sum]
  exact Intertwines.sum s fun i hi ↦ hx i hi t

/-- Homogeneous components of total classes carried to one another are carried to one another. -/
theorem BivariantClass.IntertwinesTotal.homPart (hx : c.IntertwinesTotal x x') (n : ℕ) :
    c.IntertwinesTotal (TotalChowClass.homComponent n x) (TotalChowClass.homComponent n x') :=
  fun _ t _ ↦ by
    rw [TotalChowClass.op_homComponent, TotalChowClass.op_homComponent]
    exact (hx t).homComponent n

end Bivariant

/-! ### The criterion of Stacks 02UC for a commutation -/

section Criterion

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {g : X' ⟶ X} [LocallyOfFiniteType g]
  {hg : g ≫ sX = sX'} {q p : ℤ}

/-- **Stacks 02UC for `c ∘ x = x' ∘ c`.** Let `c ∈ A^q(X' ⟶ X)`, `x ∈ A^p(X)` and
`x' ∈ A^p(X')`. If every integral scheme `T` over `X` has a proper birational modification
`b : T' ⟶ T` with `c ∩ (x ∩ [T']) = x' ∩ (c ∩ [T'])` in every degree, then `c ∘ x = x' ∘ c`. -/
theorem BivariantClass.heq_bivariantCompositeOfInvertible_of_isBirational
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q)
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p)
    (x' : BivariantClass C (gysinSystemOfInvertible C) sX' sX' (𝟙 X') (Category.id_comp sX') p)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] [IsIntegral T],
      ∃ (T' : Scheme.{u}) (b : T' ⟶ T) (_ : IsProper b), IsBirational b ∧ ∀ k : ℤ,
        c.cap (b ≫ t) (k - p) (x.idRule C sX (gysinSystemOfInvertible C) (b ≫ t) k
          (fundamentalChowClass C ((b ≫ t) ≫ sX) k)) ≍
        x'.idRule C sX' (gysinSystemOfInvertible C) (pullback.fst g (b ≫ t)) (k - q)
          (c.cap (b ≫ t) k (fundamentalChowClass C ((b ≫ t) ≫ sX) k))) :
    bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q p c x ≍
      bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg p q x' c := by
  set L := bivariantClassCongr C (gysinSystemOfInvertible C) sX' sX (Category.comp_id g)
    (comp_comp_structureMorphism_eq hg (Category.id_comp sX)) hg (q + p)
    (bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q p c x)
  set R := bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sX' sX g hg (add_comm p q)
    (bivariantClassCongr C (gysinSystemOfInvertible C) sX' sX (Category.id_comp g)
      (comp_comp_structureMorphism_eq (Category.id_comp sX') hg) hg (p + q)
      (bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg p q x' c))
  have hL : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      L.cap t k α ≍ c.cap t (k - p) (x.idRule C sX (gysinSystemOfInvertible C) t k α) :=
    fun t _ k α ↦ (BivariantClass.cap_heq_of_heq (Category.comp_id g) rfl
      (bivariantClassCongr_heq_self _ _ _ _ _) t k α).trans
        (c.bivariantCompositeOfInvertible_id_cap_heq x t k α)
  have hR : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      R.cap t k α ≍ x'.idRule C sX' (gysinSystemOfInvertible C) (pullback.fst g t) (k - q)
        (c.cap t k α) :=
    fun t _ k α ↦ ((bivariantClassDegreeCongr_cap C _ sX' sX g hg _ _ t k α).trans
      (BivariantClass.cap_heq_of_heq (Category.id_comp g) rfl
        (bivariantClassCongr_heq_self _ _ _ _ _) t k α)).trans
        (x'.id_bivariantCompositeOfInvertible_cap_heq c t k α)
  have hLR : L = R := by
    refine eq_of_sub_eq_zero (BivariantClass.eq_zero_of_capsIntegralFundamentalClassesToZero C _
      sX' sX g hg (q + p)
        (BivariantClass.capsIntegralFundamentalClassesToZero_of_hasBirationalModification
          C _ sX' sX g hg (q + p) ?_))
    intro T t _ _
    obtain ⟨T', b, hb, hbir, hk⟩ := h t
    refine ⟨T', b, hb, hbir, fun k ↦ ?_⟩
    rw [BivariantClass.sub_cap, sub_eq_zero]
    exact eq_of_heq (((hL (b ≫ t) k _).trans (hk k)).trans (hR (b ≫ t) k _).symm)
  refine (bivariantClassCongr_heq_self _ _ _ _ _).symm.trans ((heq_of_eq hLR).trans ?_)
  exact (bivariantClassDegreeCongr_heq _ _).trans (bivariantClassCongr_heq_self _ _ _ _ _)

/-- **Stacks 02UC for the intertwining of two total classes.** If every integral scheme `T` over
`X` has a proper birational modification `b : T' ⟶ T` on which capping with `c` intertwines the
operations of `x` and of `x'`, then `c` carries `x` to `x'`. -/
theorem BivariantClass.intertwinesTotal_of_isBirational
    {c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q} {x : TotalChowClass C sX}
    {x' : TotalChowClass C sX'}
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] [IsIntegral T],
      ∃ (T' : Scheme.{u}) (b : T' ⟶ T) (_ : IsProper b), IsBirational b ∧
        Intertwines (d := -q) (fun k ↦ c.cap (b ≫ t) k) (x.op (b ≫ t))
          (x'.op (pullback.fst g (b ≫ t)))) :
    c.IntertwinesTotal x x' := by
  refine c.intertwinesTotal_iff.2 fun p ↦ ?_
  refine c.heq_bivariantCompositeOfInvertible_of_isBirational _ _ fun t _ _ ↦ ?_
  obtain ⟨T', b, hb, hbir, hI⟩ := h t
  exact ⟨T', b, hb, hbir, fun k ↦ (heq_of_eq (hI k p _)).trans (gradedDegreeCast_heq _ _)⟩

end Criterion

/-! ### The operations of the Chern classes of a perfect object on integral test schemes -/

section Operations

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- The operation of a total class on a test scheme `s = a ≫ f` is the operation on the identity
of the test scheme of its restriction along `f` and then along `a`. -/
theorem TotalChowClass.op_heq_op_id_res {Y W : Scheme.{u}} (x : TotalChowClass C sX)
    (f : Y ⟶ X) [LocallyOfFiniteType f] (a : W ⟶ Y) [LocallyOfFiniteType a] (s : W ⟶ X)
    [LocallyOfFiniteType s] (hsa : s = a ≫ f) :
    x.op s ≍ (TotalChowClass.res a rfl (TotalChowClass.res f rfl x)).op (𝟙 W) :=
  (TotalChowClass.op_heq_congr x hsa).trans ((TotalChowClass.op_res f rfl x a).symm.trans
    ((TotalChowClass.op_res a rfl _ (𝟙 W)).trans
      (TotalChowClass.op_heq_congr _ (Category.id_comp a))).symm)

/-- The ordered alternating product of the total Chern classes of finitely many modules on `T`
does not depend on how the structure morphism of `T` is spelled, up to heterogeneous equality. -/
theorem list_prod_chernFamilyUnit_zpow_heq {T : Scheme.{u}} {q₁ q₂ : T ⟶ C.S}
    [LocallyOfFiniteType q₁] [LocallyOfFiniteType q₂] (hq : q₁ = q₂) (l : List ℤ)
    (F : ℤ → T.Modules) (r : ℤ → ℕ)
    (hF : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F n) (r n))
    (e : ℤ → ℤ) :
    (((l.map fun n ↦ (haveI := hF n; GenuineChern.chernFamilyUnit C q₁ (F n) (r n)) ^ e n).prod :
        (GradedCapFamily (chowGroup C q₁))ˣ) : GradedCapFamily (chowGroup C q₁)) ≍
      (((l.map fun n ↦ (haveI := hF n; GenuineChern.chernFamilyUnit C q₂ (F n) (r n)) ^ e n).prod :
        (GradedCapFamily (chowGroup C q₂))ˣ) : GradedCapFamily (chowGroup C q₂)) := by
  subst hq
  rfl

/-- The integer multiples of the unit of the ring of graded cap families on the Chow groups of `T`
do not depend on how the structure morphism of `T` is spelled, up to heterogeneous equality. -/
theorem intCast_gradedCapFamily_heq {T : Scheme.{u}} {q₁ q₂ : T ⟶ C.S}
    [LocallyOfFiniteType q₁] [LocallyOfFiniteType q₂] (hq : q₁ = q₂) (N : ℤ) :
    ((N : GradedCapFamily (chowGroup C q₁))) ≍ ((N : GradedCapFamily (chowGroup C q₂))) := by
  subst hq
  rfl

attribute [local instance 10000] HasDerivedCategory.standard

variable {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)
  (H : EnvelopePresentation E) {W : Scheme.{u}} (s : W ⟶ X) [LocallyOfFiniteType s]
  (a : W ⟶ H.Y) [LocallyOfFiniteType a]

/-- **The operation of `c(E)` on a test scheme through the envelope, where the presenting complex
has constant ranks.** Let `(f : Y ⟶ X, 𝓔^•)` be a presentation of `E` and let `s = a ≫ f` be a
test scheme along which `𝓔^•` pulls back to a complex with constant ranks `σ`. Then `c(E)`
operates on `W` as the ordered alternating product `∏_n c(𝓔^n|_W)^{(-1)^n}`, over any window of
degrees outside of which the ranks vanish. -/
theorem op_perfectChernClass_of_isFiniteLocallyFreeOfRank (hsa : s = a ≫ H.f) (σ : ℤ →₀ ℕ)
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex a H.P).X n) (σ n)) (n₀ : ℤ) (m : ℕ)
    (hw : ∀ n, (n < n₀ ∨ n₀ + (m : ℤ) < n) → σ n = 0) :
    (perfectChernClass C sX hE).op s =
      (((((Finset.Icc n₀ (n₀ + (m : ℤ))).sort (· ≤ ·)).map fun n ↦
        (haveI := hσ n; GenuineChern.chernFamilyUnit C (s ≫ sX) ((pullbackComplex a H.P).X n)
          (σ n)) ^
          ((n.negOnePow : ℤˣ) : ℤ)).prod :
          (GradedCapFamily (chowGroup C (s ≫ sX)))ˣ) : GradedCapFamily (chowGroup C (s ≫ sX))) := by
  refine eq_of_heq ((TotalChowClass.op_heq_op_id_res _ H.f a s hsa).trans ?_)
  rw [res_perfectChernClass C sX hE H, res_complexChern_eq_complexChernBounded C (H.f ≫ sX)
    H.locallyBounded a rfl σ hσ, op_id_complexChernBounded C (a ≫ (H.f ≫ sX)) _ _ _ n₀ m hw]
  exact list_prod_chernFamilyUnit_zpow_heq (by rw [hsa, Category.id_comp, Category.assoc]) _ _ _
    hσ _

/-- **The operation of `P_0(E)` on a test scheme through the envelope, where the presenting
complex has constant ranks.** With the notation of
`Stacks.Chow.op_perfectChernClass_of_isFiniteLocallyFreeOfRank`, `P_0(E)` operates on `W` as the
integer `∑_n (-1)^n σ(n)`. -/
theorem op_perfectPowerSum_zero_of_isFiniteLocallyFreeOfRank (hsa : s = a ≫ H.f) (σ : ℤ →₀ ℕ)
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex a H.P).X n) (σ n)) :
    (perfectPowerSum C sX hE 0).op s =
      (((∑ n ∈ σ.support, ((n.negOnePow : ℤˣ) : ℤ) * (σ n : ℤ) : ℤ) :
        GradedCapFamily (chowGroup C (s ≫ sX)))) := by
  refine eq_of_heq ((TotalChowClass.op_heq_op_id_res _ H.f a s hsa).trans ?_)
  rw [res_perfectPowerSum_eq_powerSumComplex C sX hE H,
    res_powerSumComplex_eq_powerSumComplexBounded C (H.f ≫ sX) H.locallyBounded a rfl σ hσ]
  have hsum : powerSumComplexBounded C (a ≫ (H.f ≫ sX)) (pullbackComplex a H.P) σ hσ 0 =
      (((∑ n ∈ σ.support, ((n.negOnePow : ℤˣ) : ℤ) * (σ n : ℤ) : ℤ)) :
        TotalChowClass C (a ≫ (H.f ≫ sX))) := by
    simp only [powerSumComplexBounded, powerSumTotal_zero]
    push_cast
    simp only [zsmul_eq_mul]
  rw [hsum, ← TotalChowClass.opRingHom_apply, map_intCast]
  exact intCast_gradedCapFamily_heq (by rw [hsa, Category.id_comp, Category.assoc]) _

end Operations

/-! ### Stacks 0FAC -/

section Perfect

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {g : X' ⟶ X} [LocallyOfFiniteType g]
  {hg : g ≫ sX = sX'} {q : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q)
  {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)

omit [LocallyOfFiniteType g] in
/-- **A test scheme through the envelope of a presentation, after base change.** If the test
scheme `s : W ⟶ X` factors as `a ≫ f` through the envelope of a presentation of `E`, then
`W ×_X X' ⟶ X'` factors through the envelope `Y ×_X X' ⟶ X'` of the pulled-back presentation of
`Lg^*E`, by a morphism `a'` lying over `a`. -/
theorem EnvelopePresentation.exists_derivedPullback_lift (H : EnvelopePresentation E)
    {W : Scheme.{u}} (s : W ⟶ X) (a : W ⟶ H.Y) (hsa : s = a ≫ H.f) :
    ∃ a' : pullback g s ⟶ (H.derivedPullback g).Y,
      a' ≫ pullback.fst H.f g = pullback.snd g s ≫ a ∧
        pullback.fst g s = a' ≫ (H.derivedPullback g).f :=
  ⟨pullback.lift (pullback.snd g s ≫ a) (pullback.fst g s)
      (by rw [Category.assoc, ← hsa, pullback.condition]),
    pullback.lift_fst _ _ _, (pullback.lift_snd _ _ _).symm⟩

/-- **Constant ranks on an integral test scheme through the envelope, after base change.** For
`s = a ≫ f : W ⟶ X` with `W` integral, the pulled-back presenting complex on `W` has constant
ranks `σ`, and so does that on `W ×_X X'` along a lift `a'` of `a`, the terms being pulled back
from `W`. -/
private theorem EnvelopePresentation.exists_ranks_derivedPullback {X' : Scheme.{u}}
    (g : X' ⟶ X) (H : EnvelopePresentation E)
    {W : Scheme.{u}} [IsIntegral W] (s : W ⟶ X) [LocallyOfFiniteType s] (a : W ⟶ H.Y)
    [LocallyOfFiniteType a] (hsa : s = a ≫ H.f) :
    ∃ (σ : ℤ →₀ ℕ) (a' : pullback g s ⟶ (H.derivedPullback g).Y) (_ : LocallyOfFiniteType a'),
      pullback.fst g s = a' ≫ (H.derivedPullback g).f ∧
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((pullbackComplex a H.P).X n) (σ n)) ∧
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((pullbackComplex a' (H.derivedPullback g).P).X n) (σ n)) ∧
      ∀ n, Nonempty ((pullbackComplex a' (H.derivedPullback g).P).X n ≅
        (Scheme.Modules.pullback (pullback.snd g s)).obj ((pullbackComplex a H.P).X n)) := by
  obtain ⟨w⟩ : Nonempty W := inferInstance
  have hQ := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback a H.P
    H.locallyBounded
  have hσ := isFiniteLocallyFreeOfRank_complexRank hQ w
  obtain ⟨a', ha'f, ha's⟩ := H.exists_derivedPullback_lift (g := g) s a hsa
  have : LocallyOfFiniteType (a' ≫ (H.derivedPullback g).f) := by
    rw [← ha's]
    infer_instance
  have : LocallyOfFiniteType a' := locallyOfFiniteType_of_comp a' (H.derivedPullback g).f
  have eQ : ∀ n, (pullbackComplex a' (H.derivedPullback g).P).X n ≅
      (Scheme.Modules.pullback (pullback.snd g s)).obj ((pullbackComplex a H.P).X n) :=
    fun n ↦ pullbackPullbackIsoOfComp ha'f (H.P.X n)
  exact ⟨complexRank hQ w, a', this, ha's, hσ, fun n ↦
    have := hσ n
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (eQ n).symm
      (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.snd g s) _ _),
    fun n ↦ ⟨eQ n⟩⟩

/-- **Stacks 0FAC (2) on an integral test scheme through the envelope.** Capping with
`c ∈ A^q(X' ⟶ X)` intertwines the operations of `c(E)` on `W` and of `c(Lg^*E)` on `W ×_X X'`,
for a test scheme `s = a ≫ f : W ⟶ X` with `W` integral factoring through the envelope of a
presentation of `E`. Both are ordered alternating products of total Chern classes of the terms of
the pulled-back complexes, which are carried to one another by Stacks 02UA. -/
theorem BivariantClass.intertwines_perfectChernClass_of_isIntegral (H : EnvelopePresentation E)
    {W : Scheme.{u}} [IsIntegral W] (s : W ⟶ X) [LocallyOfFiniteType s] (a : W ⟶ H.Y)
    [LocallyOfFiniteType a] (hsa : s = a ≫ H.f) :
    Intertwines (d := -q) (fun k ↦ c.cap s k) ((perfectChernClass C sX hE).op s)
      ((perfectChernClass C sX' (hE.derivedPullback g)).op (pullback.fst g s)) := by
  obtain ⟨σ, a', _, ha's, hσ, hσ', eQ⟩ := H.exists_ranks_derivedPullback g s a hsa
  obtain ⟨n₀, m, hw, -⟩ := exists_window_of_finsupp σ σ
  rw [op_perfectChernClass_of_isFiniteLocallyFreeOfRank hE H s a hsa σ hσ n₀ m hw,
    op_perfectChernClass_of_isFiniteLocallyFreeOfRank (hE.derivedPullback g) (H.derivedPullback g)
      (pullback.fst g s) a' ha's σ hσ' n₀ m hw]
  refine Intertwines.list_prod_zpow _ (fun n _ ↦ ?_) (fun n _ k ↦ ?_) _
  · have := hσ n
    have := hσ' n
    exact c.intertwines_chernFamily s _ _ _ (eQ n).some
  · have := hσ' n
    exact GenuineChern.chernFamily_apply_zero C _ _ _ k

/-- **`P_0(E)` on an integral test scheme through the envelope.** Capping with
`c ∈ A^q(X' ⟶ X)` intertwines the operations of `P_0(E)` on `W` and of `P_0(Lg^*E)` on
`W ×_X X'`: both are the same integer, the alternating sum of the ranks of the terms of the
presenting complex. -/
theorem BivariantClass.intertwines_perfectPowerSum_zero_of_isIntegral
    (H : EnvelopePresentation E) {W : Scheme.{u}} [IsIntegral W] (s : W ⟶ X)
    [LocallyOfFiniteType s] (a : W ⟶ H.Y) [LocallyOfFiniteType a] (hsa : s = a ≫ H.f) :
    Intertwines (d := -q) (fun k ↦ c.cap s k) ((perfectPowerSum C sX hE 0).op s)
      ((perfectPowerSum C sX' (hE.derivedPullback g) 0).op (pullback.fst g s)) := by
  obtain ⟨σ, a', _, ha's, hσ, hσ', -⟩ := H.exists_ranks_derivedPullback g s a hsa
  rw [op_perfectPowerSum_zero_of_isFiniteLocallyFreeOfRank hE H s a hsa σ hσ,
    op_perfectPowerSum_zero_of_isFiniteLocallyFreeOfRank (hE.derivedPullback g)
      (H.derivedPullback g) (pullback.fst g s) a' ha's σ hσ']
  simpa only [zsmul_one] using
    (Intertwines.one (pull := fun k ↦ c.cap s k)).zsmul
      (∑ n ∈ σ.support, ((n.negOnePow : ℤˣ) : ℤ) * (σ n : ℤ))

/-- A bivariant class carries `x` to `x'` once it intertwines their operations on every integral
test scheme through the envelope of a presentation of `E`. -/
private theorem BivariantClass.intertwinesTotal_of_envelopePresentation
    (H : EnvelopePresentation E) {x : TotalChowClass C sX} {x' : TotalChowClass C sX'}
    (h : ∀ {W : Scheme.{u}} (s : W ⟶ X) [IsIntegral W] [LocallyOfFiniteType s] (a : W ⟶ H.Y)
      [LocallyOfFiniteType a], s = a ≫ H.f →
        Intertwines (d := -q) (fun k ↦ c.cap s k) (x.op s) (x'.op (pullback.fst g s))) :
    c.IntertwinesTotal x x' := by
  refine BivariantClass.intertwinesTotal_of_isBirational fun t _ _ ↦ ?_
  obtain ⟨T', b, a, hT', hb, hbir, hfac⟩ := H.envelope.exists_properBirational_modification t
  have := hT'
  have := hb
  have : LocallyOfFiniteType (a ≫ H.f) := by
    rw [← hfac]
    infer_instance
  have : LocallyOfFiniteType a := locallyOfFiniteType_of_comp a H.f
  exact ⟨T', b, hb, hbir, h (b ≫ t) a hfac⟩

/-- **Stacks 0FAC (2), in every degree at once.** A bivariant class `c ∈ A^q(X' ⟶ X)` carries
the total Chern class `c(E)` to the total Chern class `c(Lg^*E)`. -/
theorem BivariantClass.intertwinesTotal_perfectChernClass :
    c.IntertwinesTotal (perfectChernClass C sX hE)
      (perfectChernClass C sX' (hE.derivedPullback g)) :=
  c.intertwinesTotal_of_envelopePresentation hE.some fun s _ _ a _ hsa ↦
    c.intertwines_perfectChernClass_of_isIntegral hE hE.some s a hsa

/-- **Stacks 0FAC (2).** Let `X` be locally of finite type over the base, let `E ∈ D(𝒪_X)` be
perfect with Chern classes defined, let `g : X' ⟶ X` be locally of finite type and let
`c ∈ A^q(X' ⟶ X)`. Then for every `p`

  `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`,

the composites being those of Stacks 0B75, classes for the equal morphisms `g ≫ 𝟙 X` and
`𝟙 X' ≫ g` of the equal degrees `q + p` and `p + q`. -/
theorem BivariantClass.heq_bivariantCompositeOfInvertible_perfectChernClass (p : ℕ) :
    bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q p c
        (perfectChernClass C sX hE p) ≍
      bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg p q
        (perfectChernClass C sX' (hE.derivedPullback g) p) c :=
  c.intertwinesTotal_iff.1 (c.intertwinesTotal_perfectChernClass hE) p

/-- **The power sums of Stacks 0GUD commute with every bivariant class, in every degree at
once.** A bivariant class `c ∈ A^q(X' ⟶ X)` carries `P_p(E)` to `P_p(Lg^*E)`: for `p = 0` both
are the rank, and for `p ≥ 1` Newton's identities (Stacks 0FAD) express them by the same formula
in the Chern classes of `E` and of `Lg^*E`, which `c` carries to one another by Stacks 0FAC. -/
theorem BivariantClass.intertwinesTotal_perfectPowerSum (p : ℕ) :
    c.IntertwinesTotal (perfectPowerSum C sX hE p)
      (perfectPowerSum C sX' (hE.derivedPullback g) p) := by
  induction p using Nat.strong_induction_on with
  | _ p IH =>
  rcases p with _ | p
  · exact c.intertwinesTotal_of_envelopePresentation hE.some fun s _ _ a _ hsa ↦
      c.intertwines_perfectPowerSum_zero_of_isIntegral hE hE.some s a hsa
  · rw [isNewtonPowerSums_perfectPowerSum C sX hE p,
      isNewtonPowerSums_perfectPowerSum C sX' (hE.derivedPullback g) p]
    have hc := c.intertwinesTotal_perfectChernClass hE
    refine (BivariantClass.IntertwinesTotal.sum _ fun j _ ↦ ?_).add ((hc.homPart _).zsmul _)
    exact ((hc.homPart _).mul (IH (p - j) (Nat.sub_lt_succ p j))).zsmul _

/-- **The power sums of Stacks 0GUD commute with every bivariant class.** For `c ∈ A^q(X' ⟶ X)`,
`c ∘ P_p(E) = P_p(Lg^*E) ∘ c`, as classes for `g ≫ 𝟙 X` and `𝟙 X' ≫ g`. -/
theorem BivariantClass.heq_bivariantCompositeOfInvertible_perfectPowerSum (p : ℕ) :
    bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q p c
        (perfectPowerSumComponent C sX hE p) ≍
      bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg p q
        (perfectPowerSumComponent C sX' (hE.derivedPullback g) p) c :=
  c.intertwinesTotal_iff.1 (c.intertwinesTotal_perfectPowerSum hE p) p

end Perfect

section PerfectCenter

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {q : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) q)
  {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)

/-- **Stacks 0FAC (1).** Let `E ∈ D(𝒪_X)` be perfect with Chern classes defined. Then `c_p(E)` is
in the center of `A^*(X)`: for every `c ∈ A^q(X)`,

  `c · c_p(E) = c_p(E) · c`,

the two products lying in `A^{q+p}(X)` and `A^{p+q}(X)`. -/
theorem BivariantClass.heq_mulId_perfectChernClass (p : ℕ) :
    c.mulId C sX (perfectChernClass C sX hE p) ≍ (perfectChernClass C sX hE p).mulId C sX c := by
  have e : perfectChernClass C sX (hE.derivedPullback (𝟙 X)) = perfectChernClass C sX hE :=
    (res_perfectChernClass_derivedPullback_of_comp_eq C sX hE (𝟙 X) (Category.id_comp sX)
      _).symm.trans (TotalChowClass.res_id _)
  have h := c.heq_bivariantCompositeOfInvertible_perfectChernClass hE p
  rw [e] at h
  exact (bivariantClassCongr_heq_self _ _ _ _ _).trans
    (h.trans (bivariantClassCongr_heq_self _ _ _ _ _).symm)

/-- **The power sums of Stacks 0GUD are central.** For every `c ∈ A^q(X)`,
`c · P_p(E) = P_p(E) · c`, the two products lying in `A^{q+p}(X)` and `A^{p+q}(X)`. -/
theorem BivariantClass.heq_mulId_perfectPowerSum (p : ℕ) :
    c.mulId C sX (perfectPowerSumComponent C sX hE p) ≍
      (perfectPowerSumComponent C sX hE p).mulId C sX c := by
  have e : perfectPowerSum C sX (hE.derivedPullback (𝟙 X)) p = perfectPowerSum C sX hE p :=
    (res_perfectPowerSum_derivedPullback C sX hE (𝟙 X) (Category.id_comp sX) _ p).symm.trans
      (TotalChowClass.res_id _)
  have h := c.heq_bivariantCompositeOfInvertible_perfectPowerSum hE p
  simp only [perfectPowerSumComponent] at h
  rw [e] at h
  exact (bivariantClassCongr_heq_self _ _ _ _ _).trans
    (h.trans (bivariantClassCongr_heq_self _ _ _ _ _).symm)

end PerfectCenter

/-! ### Stacks 0FAC for nonhomogeneous classes -/

section PerfectNonhomogeneous

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {g : X' ⟶ X} [LocallyOfFiniteType g]
  {hg : g ≫ sX = sX'} {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)

/-- **Stacks 0FAC (2).** Let `X` be locally of finite type over the base, let `E ∈ D(𝒪_X)` be
perfect with Chern classes defined, let `g : X' ⟶ X` be locally of finite type and let
`c ∈ A^*(X' ⟶ X)`. Then for every `p`

  `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`   in   `A^*(X' ⟶ X)`,

the composites being those of Stacks 0B75, extended additively to the graded groups; they are
classes for the morphisms `g ≫ 𝟙 X` and `𝟙 X' ≫ g`, both read as classes for `g`. -/
@[stacks 0FAC "(2): c ∘ c_p(E) = c_p(Lg^*E) ∘ c in A^*(X' → X), for every c in A^*(X' → X), the \
Chern classes of Stacks 0F9E (2) and the composition of Stacks 0B75 at the Gysin system of the \
first Chern class of an invertible module, extended additively to the graded groups"]
theorem nonhomogeneousBivariantGroupCongr_compositeOfInvertible_perfectChernClass
    (c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) sX' sX g hg) (p : ℕ) :
    nonhomogeneousBivariantGroupCongr C (gysinSystemOfInvertible C) sX' sX (Category.comp_id g)
        (comp_comp_structureMorphism_eq hg (Category.id_comp sX)) hg
        (nonhomogeneousBivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg
          (Category.id_comp sX) c (DirectSum.of _ (p : ℤ) (perfectChernClass C sX hE p))) =
      nonhomogeneousBivariantGroupCongr C (gysinSystemOfInvertible C) sX' sX (Category.id_comp g)
        (comp_comp_structureMorphism_eq (Category.id_comp sX') hg) hg
        (nonhomogeneousBivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g
          (Category.id_comp sX') hg
          (DirectSum.of _ (p : ℤ) (perfectChernClass C sX' (hE.derivedPullback g) p)) c) := by
  induction c using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | of q x =>
    simp only [nonhomogeneousBivariantCompositeOfInvertible_of_of,
      nonhomogeneousBivariantGroupCongr_of]
    exact DirectSum.of_eq_of_heq (add_comm _ _)
      (((bivariantClassCongr_heq_self _ _ _ _ _).trans
        (x.heq_bivariantCompositeOfInvertible_perfectChernClass hE p)).trans
          (bivariantClassCongr_heq_self _ _ _ _ _).symm)
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]

/-- **Stacks 0FAC (1).** Let `E ∈ D(𝒪_X)` be perfect with Chern classes defined. Then `c_p(E)` is
in the center of `A^*(X)`: for every `c ∈ A^*(X)`,

  `c · c_p(E) = c_p(E) · c`,

the product of `A^*(X)` being the composition of Stacks 0B75, extended additively to the graded
groups, of classes for `𝟙 X ≫ 𝟙 X`, read as a class for `𝟙 X`; on homogeneous classes it is
`Stacks.Chow.BivariantClass.mulId`. -/
@[stacks 0FAC "(1): c_p(E) is in the center of A^*(X), c · c_p(E) = c_p(E) · c for every c in \
A^*(X), the product being the composition of Stacks 0B75 at the Gysin system of the first Chern \
class of an invertible module, extended additively to the graded groups, and the Chern classes of \
Stacks 0F9E (2)"]
theorem nonhomogeneousBivariantGroupCongr_compositeOfInvertible_perfectChernClass_comm
    (c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) sX sX (𝟙 X)
      (Category.id_comp sX)) (p : ℕ) :
    nonhomogeneousBivariantGroupCongr C (gysinSystemOfInvertible C) sX sX
        (Category.comp_id (𝟙 X))
        (comp_comp_structureMorphism_eq (Category.id_comp sX) (Category.id_comp sX))
        (Category.id_comp sX)
        (nonhomogeneousBivariantCompositeOfInvertible C sX sX sX (𝟙 X) (𝟙 X) (Category.id_comp sX)
          (Category.id_comp sX) c (DirectSum.of _ (p : ℤ) (perfectChernClass C sX hE p))) =
      nonhomogeneousBivariantGroupCongr C (gysinSystemOfInvertible C) sX sX
        (Category.comp_id (𝟙 X))
        (comp_comp_structureMorphism_eq (Category.id_comp sX) (Category.id_comp sX))
        (Category.id_comp sX)
        (nonhomogeneousBivariantCompositeOfInvertible C sX sX sX (𝟙 X) (𝟙 X) (Category.id_comp sX)
          (Category.id_comp sX) (DirectSum.of _ (p : ℤ) (perfectChernClass C sX hE p)) c) := by
  induction c using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | of q x =>
    simp only [nonhomogeneousBivariantCompositeOfInvertible_of_of,
      nonhomogeneousBivariantGroupCongr_of]
    exact DirectSum.of_eq_of_heq (add_comm _ _) (x.heq_mulId_perfectChernClass hE p)
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]

end PerfectNonhomogeneous

end Stacks.Chow

end
