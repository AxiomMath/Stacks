module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPoints

/-!
# The exterior product of rational points

Over a field `k`, the exterior product of Stacks 0FBV sends the classes of two rational points
`p` of `Y` and `q` of `X` to the class of the rational point `(p, q)` of `Y ×_k X`:

  `[p] × [q] = [(p, q)]` in `CH_0(Y ×_k X)`.

Consequently the exterior product of a signed sum of classes of rational points with a
difference `[x] - [x']` is again such a signed sum, which is what makes the iterated exterior
powers of `[x] - [x']` in the proof of Stacks 0FH9 explicit: the `n`-th power is the signed sum
over the `2^n` rational points of `X^n` with coordinates in `{x, x'}`.

## Main results

* `Stacks.Chow.exteriorProductIdeal_section_eq_ker`: the product of the reduced closures of two
  rational points is cut out by the kernel of the paired point.
* `Stacks.Chow.exteriorProduct_cycleAssociatedToClosedSubscheme_section`: `[p] × [q] = [(p, q)]`
  on cycles.
* `Stacks.Chow.chowExteriorProduct_rationalPointChowClass`: the same on Chow groups.
* `Stacks.Chow.chowExteriorProduct_sum_tmul_rationalPointChowClass_sub`: the exterior product of
  a signed sum of rational points with `[x] - [x']`.

## Implementation notes

The coefficient of `[p] × [q]` at a point `z` is `[p](pr₁ z) · [q](pr₂ z)` times the multiplicity
of `z` in the product of the reduced closures of `pr₁ z` and `pr₂ z`. The cycle of a rational
point is `1` at the point and `0` elsewhere, and the product of the two reduced point closures is
cut out by `pr₁⁻¹ ker p + pr₂⁻¹ ker q`, which is the kernel of `(p, q)`: one inclusion because
`(p, q)` composed with the projections is `p` and `q`, the other because the closed subscheme of
the sum factors through both points, hence through `(p, q)`. The multiplicity is therefore the
coefficient of the cycle of `(p, q)`.

No `@[stacks]` attribute is carried: this is a computation used in the proof of Stacks 0FH9, not
a tagged statement.

## References

* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-! ### The cycle of a rational point -/

/-- The dimension function of the base situation of a field vanishes at closed points, which is
the hypothesis of the exterior product of Stacks 0FBV. -/
theorem fieldChowSituation_dimensionFunction_of_isClosed (s : (fieldChowSituation k).S)
    (_ : IsClosed ({s} : Set (fieldChowSituation k).S)) :
    (fieldChowSituation k).dimensionFunction s = 0 :=
  rfl

/-- The relative dimension over `k` of the image of a rational point is zero. -/
theorem relativeDimension_section_eq_zero {Y : Scheme.{u}} (g : Y ⟶ (fieldChowSituation k).S)
    (p : (fieldChowSituation k).S ⟶ Y) (hp : p ≫ g = 𝟙 _) [IsClosedImmersion p]
    (s : (fieldChowSituation k).S) :
    relativeDimension (fieldChowSituation k).dimensionFunction g (p s) = 0 := by
  rw [← relativeDimension_comp_closedImmersion, hp, relativeDimension_id]
  rfl

/-- The cycle of a rational point has coefficient one at the point. -/
theorem cycleAssociatedToClosedSubscheme_section_apply_self {Y : Scheme.{u}}
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (p : (fieldChowSituation k).S ⟶ Y) (hp : p ≫ g = 𝟙 _) [IsClosedImmersion p]
    (s : (fieldChowSituation k).S) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) g p 0).1 (p s) = 1 := by
  obtain rfl : s = genericPoint (fieldChowSituation k).S := Subsingleton.elim _ _
  exact cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint _ g p 0
    (relativeDimension_section_eq_zero k g p hp _)

/-- The cycle of a rational point vanishes away from the point. -/
theorem cycleAssociatedToClosedSubscheme_section_apply_of_ne {Y : Scheme.{u}}
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (p : (fieldChowSituation k).S ⟶ Y) [IsClosedImmersion p]
    (s : (fieldChowSituation k).S) (j : ℤ) {y : Y} (hy : y ≠ p s) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) g p j).1 y = 0 := by
  obtain rfl : s = genericPoint (fieldChowSituation k).S := Subsingleton.elim _ _
  exact cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne _ g p j hy

/-- The vanishing ideal of the reduced closure of a rational point is the kernel of the point. -/
theorem vanishingIdeal_closure_section {Y : Scheme.{u}} (p : (fieldChowSituation k).S ⟶ Y)
    (s : (fieldChowSituation k).S) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p s} : Set Y)) = p.ker := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 2
  ext y
  simp only [Closeds.coe_top, Set.image_univ, Set.mem_singleton_iff, Set.mem_range]
  exact ⟨fun h ↦ ⟨s, h.symm⟩, fun ⟨t, ht⟩ ↦ by rw [← ht, Subsingleton.elim t s]⟩

/-- The product of the reduced closures of two rational points is the rational point of the
product: the ideal sheaf cutting it out is the kernel of the induced point. -/
theorem exteriorProductIdeal_section_eq_ker {X Y : Scheme.{u}}
    (g : Y ⟶ (fieldChowSituation k).S) (f : X ⟶ (fieldChowSituation k).S)
    (p : (fieldChowSituation k).S ⟶ Y) (hp : p ≫ g = 𝟙 _) [IsClosedImmersion p]
    (q : (fieldChowSituation k).S ⟶ X) (hq : q ≫ f = 𝟙 _) [IsClosedImmersion q]
    (s : (fieldChowSituation k).S) :
    exteriorProductIdeal g f (p s) (q s) =
      (pullback.lift (f := g) (g := f) p q (hp.trans hq.symm)).ker := by
  set r := pullback.lift (f := g) (g := f) p q (hp.trans hq.symm) with hr
  set I := exteriorProductIdeal g f (p s) (q s) with hI
  have hIe : I = p.ker.comap (pullback.fst g f) ⊔ q.ker.comap (pullback.snd g f) := by
    rw [hI, exteriorProductIdeal, vanishingIdeal_closure_section, vanishingIdeal_closure_section]
  have h1 : p.ker ≤ (I.subschemeι ≫ pullback.fst g f).ker :=
    Scheme.IdealSheafData.le_map_iff_comap_le.2 (hIe ▸ le_sup_left)
  have h2 : q.ker ≤ (I.subschemeι ≫ pullback.snd g f).ker :=
    Scheme.IdealSheafData.le_map_iff_comap_le.2 (hIe ▸ le_sup_right)
  set a := IsClosedImmersion.lift p _ h1
  set b := IsClosedImmersion.lift q _ h2
  have ha : a ≫ p = I.subschemeι ≫ pullback.fst g f := IsClosedImmersion.lift_fac _ _ _
  have hb : b ≫ q = I.subschemeι ≫ pullback.snd g f := IsClosedImmersion.lift_fac _ _ _
  have hab : a = b := by
    have e1 : a = a ≫ p ≫ g := by rw [hp, Category.comp_id]
    have e2 : b = b ≫ q ≫ f := by rw [hq, Category.comp_id]
    rw [e1, e2, reassoc_of% ha, reassoc_of% hb, pullback.condition]
  have hc : a ≫ r = I.subschemeι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr, pullback.lift_fst, ha]
    · rw [Category.assoc, hr, pullback.lift_snd, hab, hb]
  apply le_antisymm
  · rw [hIe]
    refine sup_le ?_ ?_ <;>
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, hr] <;>
      simp only [pullback.lift_fst, pullback.lift_snd, le_refl]
  · calc r.ker ≤ (a ≫ r).ker := Scheme.Hom.le_ker_comp _ _
      _ = I := by rw [hc, Scheme.IdealSheafData.ker_subschemeι]

/-- **The exterior product of two rational points is the rational point of the product**, on
cycles: `[p] × [q] = [(p, q)]` in `Z_0(Y ×_k X)`. -/
theorem exteriorProduct_cycleAssociatedToClosedSubscheme_section {X Y : Scheme.{u}}
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (p : (fieldChowSituation k).S ⟶ Y) (hp : p ≫ g = 𝟙 _) [IsClosedImmersion p]
    (q : (fieldChowSituation k).S ⟶ X) (hq : q ≫ f = 𝟙 _) [IsClosedImmersion q]
    [IsClosedImmersion (pullback.lift (f := g) (g := f) p q (hp.trans hq.symm))] :
    exteriorProduct (fieldChowSituation k) g f 0 0
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) g p 0)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f q 0) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst g f ≫ g)
        (pullback.lift (f := g) (g := f) p q (hp.trans hq.symm)) (0 + 0) := by
  set r := pullback.lift (f := g) (g := f) p q (hp.trans hq.symm) with hr
  set s₀ := genericPoint (fieldChowSituation k).S
  apply Subtype.ext
  ext z
  rw [exteriorProduct_apply]
  by_cases hz : pullback.fst g f z = p s₀ ∧ pullback.snd g f z = q s₀
  · obtain ⟨h1, h2⟩ := hz
    rw [h1, h2, cycleAssociatedToClosedSubscheme_section_apply_self k g p hp,
      cycleAssociatedToClosedSubscheme_section_apply_self k f q hq, one_mul, one_mul]
    change closedSubschemeCycleCoeff _ _ _ _ z = closedSubschemeCycleCoeff _ _ _ _ z
    have hI := exteriorProductIdeal_section_eq_ker k g f p hp q hq s₀
    let c := IsClosedImmersion.lift r (exteriorProductIdeal g f (p s₀) (q s₀)).subschemeι
      (by rw [hI, Scheme.IdealSheafData.ker_subschemeι])
    have hc : c ≫ r = (exteriorProductIdeal g f (p s₀) (q s₀)).subschemeι :=
      IsClosedImmersion.lift_fac _ _ _
    exact closedSubschemeCycleCoeff_eq_of_iso _ _ _ r
      (@asIso _ _ _ _ c (IsClosedImmersion.isIso_of_ker_eq _ r c hc
        (by rw [Scheme.IdealSheafData.ker_subschemeι, hI]))) hc _ z
  · have hzr : z ≠ r s₀ := by
      rintro rfl
      exact hz ⟨by rw [← Scheme.Hom.comp_apply, hr, pullback.lift_fst],
        by rw [← Scheme.Hom.comp_apply, hr, pullback.lift_snd]⟩
    rw [cycleAssociatedToClosedSubscheme_section_apply_of_ne k _ r s₀ _ hzr]
    rcases not_and_or.1 hz with h | h
    · rw [cycleAssociatedToClosedSubscheme_section_apply_of_ne k g p s₀ 0 h, zero_mul, zero_mul]
    · rw [cycleAssociatedToClosedSubscheme_section_apply_of_ne k f q s₀ 0 h, mul_zero, zero_mul]

/-- **The exterior product of the classes of two rational points is the class of the rational
point of the product**: `[p] × [q] = [(p, q)]` in `CH_0(Y ×_k X)`. -/
theorem chowExteriorProduct_rationalPointChowClass {X Y : Scheme.{u}}
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (p : (fieldChowSituation k).S ⟶ Y) (hp : p ≫ g = 𝟙 _)
    (q : (fieldChowSituation k).S ⟶ X) (hq : q ≫ f = 𝟙 _) :
    chowExteriorProduct (fieldChowSituation k) (fieldChowSituation_dimensionFunction_of_isClosed k)
        g f 0 0
        (rationalPointChowClass k g p hp ⊗ₜ rationalPointChowClass k f q hq) =
      rationalPointChowClass k (pullback.fst g f ≫ g)
        (pullback.lift (f := g) (g := f) p q (hp.trans hq.symm))
        (by rw [pullback.lift_fst_assoc, hp]) := by
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id g p hp
  have : IsClosedImmersion q := isClosedImmersion_of_comp_eq_id f q hq
  have : IsClosedImmersion (pullback.lift (f := g) (g := f) p q (hp.trans hq.symm)) :=
    isClosedImmersion_of_comp_eq_id (pullback.fst g f ≫ g) _ (by rw [pullback.lift_fst_assoc, hp])
  exact (chowExteriorProduct_tmul_mk _ _ g f 0 0 _ _).trans
    (congrArg QuotientAddGroup.mk
      (exteriorProduct_cycleAssociatedToClosedSubscheme_section k g f p hp q hq))

/-- A rational point is determined by its morphism: the class does not see the proof that it is a
section. -/
theorem rationalPointChowClass_congr {Y : Scheme.{u}} (g : Y ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType g] {p q : (fieldChowSituation k).S ⟶ Y} (h : p = q)
    (hp : p ≫ g = 𝟙 _) (hq : q ≫ g = 𝟙 _) :
    rationalPointChowClass k g p hp = rationalPointChowClass k g q hq := by
  subst h
  rfl

/-! ### Signed sums of rational points -/

/-- The sign `(-1)^{#{i | s i}}` of a word `s : Fin n → Bool`. -/
def boolSign {n : ℕ} (s : Fin n → Bool) : ℤ := ∏ i, cond (s i) (-1) 1

/-- The sign of `Fin.snoc s b` is the sign of `s` times `-1` if `b` is `true` and `1` otherwise. -/
@[simp]
theorem boolSign_snoc {n : ℕ} (s : Fin n → Bool) (b : Bool) :
    boolSign (Fin.snoc s b : Fin (n + 1) → Bool) = boolSign s * cond b (-1) 1 := by
  simp [boolSign, Fin.prod_univ_castSucc]

/-- The sign of the empty word is `1`. -/
@[simp]
theorem boolSign_zero (s : Fin 0 → Bool) : boolSign s = 1 := by
  simp [boolSign]

/-- **The exterior product of a signed sum of rational points with `[x] - [x']`.** If a class is
the signed sum `∑_s (-1)^{|s|} [P s]` of the classes of a family of rational points of `Y`
indexed by `s : Fin n → Bool`, its exterior product with `[x] - [x']` is the signed sum, indexed
by `t : Fin (n + 1) → Bool`, of the classes of the rational points `(P (init t), x_t)` of
`Y ×_k X`, where `x_t` is `x'` or `x` according as the last letter of `t` is `true` or not. -/
theorem chowExteriorProduct_sum_tmul_rationalPointChowClass_sub {X Y : Scheme.{u}}
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) {n : ℕ}
    (P : (Fin n → Bool) → ((fieldChowSituation k).S ⟶ Y)) (hP : ∀ s, P s ≫ g = 𝟙 _)
    (hxb : ∀ b : Bool, cond b x' x ≫ f = 𝟙 _) :
    chowExteriorProduct (fieldChowSituation k) (fieldChowSituation_dimensionFunction_of_isClosed k)
        g f 0 0 ((∑ s, boolSign s • rationalPointChowClass k g (P s) (hP s)) ⊗ₜ
          (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx')) =
      ∑ t : Fin (n + 1) → Bool, boolSign t • rationalPointChowClass k (pullback.fst g f ≫ g)
        (pullback.lift (P (Fin.init t)) (cond (t (Fin.last n)) x' x)
          ((hP _).trans (hxb _).symm))
        (by rw [pullback.lift_fst_assoc, hP]) := by
  rw [TensorProduct.sum_tmul, map_sum, ← (Fin.snocEquiv fun _ ↦ Bool).sum_comp,
    Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Fintype.sum_bool, ← TensorProduct.smul_tmul', map_zsmul, TensorProduct.tmul_sub, map_sub,
    chowExteriorProduct_rationalPointChowClass, chowExteriorProduct_rationalPointChowClass]
  have e : ∀ b : Bool, rationalPointChowClass k (pullback.fst g f ≫ g)
      (pullback.lift (P (Fin.init ((Fin.snocEquiv fun _ ↦ Bool) (b, s))))
        (cond (((Fin.snocEquiv fun _ ↦ Bool) (b, s)) (Fin.last n)) x' x)
        ((hP _).trans (hxb _).symm))
      (by rw [pullback.lift_fst_assoc, hP]) =
      rationalPointChowClass k (pullback.fst g f ≫ g)
        (pullback.lift (P s) (cond b x' x) ((hP _).trans (hxb _).symm))
        (by rw [pullback.lift_fst_assoc, hP]) := by
    intro b
    apply rationalPointChowClass_congr
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last]
  rw [e true, e false]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, boolSign_snoc, Bool.cond_true, Bool.cond_false,
    mul_neg, mul_one, neg_smul, smul_sub]
  abel

end Stacks.Chow

end
