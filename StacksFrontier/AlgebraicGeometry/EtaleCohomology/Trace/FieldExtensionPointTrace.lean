module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPointExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointsDegreeOne
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.SmoothUpperBound

/-!
# The point side of the trace formula after a finite extension of the base field

Let `X` be a scheme of finite type over a finite field `k`, `F` an ℓ-adic sheaf on `X`, and `k'`
an extension of `k` of degree `n`.  Write `X' = X ×_k k'` and `g : X' ⟶ X` for the projection.
Then
`∑_{y ∈ X'(k')} Tr(π_y | (g⁻¹F)_ȳ) = ∑_{d ∣ n} d ∑_{deg x = d} Tr(π_x ^ (n / d) | F_x̄)`.

Indeed the `k'`-rational points of `X'` are the `k'`-valued points of `X`, that is the pairs of a
closed point `x` and a `k`-embedding `κ(x) → k'`; there are `deg x` of them over `x` when
`deg x ∣ n` and none otherwise, and at each of them the residue field is `k'`, which has
`#κ(x) ^ (n / deg x)` elements, so that the geometric Frobenius at the point of `X'` is the
`(n / deg x)`-th power of the one at `x`
(`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_inverseImage`).

This is the left hand side of the reduction, in the proof of [Stacks, Tag 03V0], of the trace
formula for `(π_X^*) ^ n` to Tag 03V2 for `X ×_k k_n` over `k_n`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.finsum_rationalStalkFrobenius_fieldExtension`: the identity
  above.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- The point hit by the composite `Spec K ⟶ Y ⟶ X` is the image of the point hit by
`Spec K ⟶ Y`. -/
lemma SpecToEquivOfField_comp_fst (K : Type u) [Field K] {Y X : Scheme.{u}} (g : Y ⟶ X)
    (y : Spec (.of K) ⟶ Y) :
    (Scheme.SpecToEquivOfField K X (y ≫ g)).1 = g.base (Scheme.SpecToEquivOfField K Y y).1 :=
  rfl

/-- At a point with finite residue field of a scheme over a finite field `k`, the residue field
has `#k ^ deg x` elements. -/
lemma natCard_residueField_eq_pow_residueDegree {k : Type u} [Field k] [Fintype k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) [Finite (X.residueField x)] :
    Nat.card (X.residueField x) = Fintype.card k ^ residueDegree f x := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have : Module.Finite k (X.residueField x) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card]
  rfl

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f]
  (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
  [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1]

omit [Fintype k] [Fintype k'] in
/-- **The point side after a finite extension of the base field.**  If `k'` is an extension of
`k` of degree `n`, `X' = X ×_k k'` and `g : X' ⟶ X` is the projection, then
`∑_{y ∈ |X'|, deg_{k'} y = 1} Tr(π_y | (g⁻¹F)_ȳ)` equals
`∑_{x ∈ |X|, deg x ∣ n} deg x · Tr(π_x ^ (n / deg x) | F_x̄)`, the traces being taken on the
rational stalks. -/
theorem LAdicSheaf.finsum_rationalStalkFrobenius_fieldExtension (F : LAdicSheaf.{u, u + 1} B X ℓ)
    [Finite k] [Finite k'] (n : ℕ) (hn : Module.finrank k k' = n) (hn0 : n ≠ 0) :
    ∑ᶠ (y : closedPoints (fieldExtensionScheme B X f k').1)
        (_ : residueDegree (pullback.snd f (specAlgebraMap k k')) y.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
            (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) y.1
            (finite_residueField (pullback.snd f (specAlgebraMap k k')) y.1 y.2)) =
      ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ n),
        (residueDegree f x.1 : ℚ_[ℓ]) * LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
            (n / residueDegree f x.1)) := by
  have := Fintype.ofFinite k
  have := Fintype.ofFinite k'
  set f' := pullback.snd f (specAlgebraMap k k')
  have : Fintype (rationalPoints f') := @Fintype.ofFinite _ (finite_rationalPoints f')
  rw [finsum_residueDegree_eq_one_eq_sum f']
  set S := (closedPointsDegreeLE f n).filter (fun x => residueDegree f x.1 ∣ n)
  have hpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hmem : ∀ (x : X.1) (σ : residueEmbeddings f k' x),
      ∃ h : IsClosed ({x} : Set X.1), (⟨x, h⟩ : closedPoints X.1) ∈ S := by
    intro x σ
    obtain ⟨hc, hd⟩ := isClosed_and_dvd_of_residueEmbeddings f k' x σ
    rw [hn] at hd
    refine ⟨hc, Finset.mem_filter.2 ⟨?_, hd⟩⟩
    simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Nat.le_of_dvd hpos hd
  let e : (Σ x : X.1, residueEmbeddings f k' x) ≃ Σ y : S, residueEmbeddings f k' y.1.1 :=
    { toFun := fun c => ⟨⟨⟨c.1, (hmem c.1 c.2).1⟩, (hmem c.1 c.2).2⟩, c.2⟩
      invFun := fun c => ⟨c.1.1.1, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Φ : rationalPoints f' ≃ Σ y : S, residueEmbeddings f k' y.1.1 :=
    (rationalPointsEquivFieldValuedPoints f').trans
      (((Stacks.BombieriStepanov.fieldValuedPointsBaseChangeEquiv f k' k').trans
        (fieldValuedPointsEquiv f k')).trans e)
  have hS : ∀ y : S, residueDegree f y.1.1 ∣ n := fun y => (Finset.mem_filter.1 y.2).2
  have hfin : ∀ y : S, Finite (residueEmbeddings f k' y.1.1) := by
    intro y
    refine Nat.finite_of_card_ne_zero ?_
    rw [natCard_residueEmbeddings, hn, ite_eq_left (hS y)]
    intro h0
    have := hS y
    rw [h0, zero_dvd_iff] at this
    lia
  let : ∀ y : S, Fintype (residueEmbeddings f k' y.1.1) := fun y =>
    @Fintype.ofFinite _ (hfin y)
  let h : S → ℚ_[ℓ] := fun x => LinearMap.trace ℚ_[ℓ] _
    (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1.1 (finite_residueField f x.1.1 x.1.2) ^
      (n / residueDegree f x.1.1))
  have hpt : ∀ y : rationalPoints f',
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F)
          (rationalPointsEquivDegreeOne f' y).1.1
          (finite_residueField f' _ (rationalPointsEquivDegreeOne f' y).1.2)) = h (Φ y).1 := by
    intro y
    have hy := finite_residueField f' _ (rationalPointsEquivDegreeOne f' y).1.2
    have hx := finite_residueField f _ (Φ y).1.1.2
    have hd := hS (Φ y).1
    have hd0 : residueDegree f (Φ y).1.1.1 ≠ 0 := fun h0 => by
      rw [h0, zero_dvd_iff] at hd
      lia
    have he : Nat.card ((fieldExtensionScheme B X f k').1.residueField
        (rationalPointsEquivDegreeOne f' y).1.1) =
        Nat.card (X.1.residueField ((Φ y).1.1.1)) ^ (n / residueDegree f (Φ y).1.1.1 - 1 + 1) := by
      rw [Nat.sub_add_cancel (Nat.div_pos (Nat.le_of_dvd hpos hd) (Nat.pos_of_ne_zero hd0)),
        natCard_residueField_of_residueDegree_eq_one f' _ (rationalPointsEquivDegreeOne f' y).2,
        natCard_residueField_eq_pow_residueDegree f, ← pow_mul, Nat.mul_div_cancel' hd,
        Module.card_eq_pow_finrank (K := k) (V := k'), hn]
    have key := LAdicSheaf.trace_rationalStalkFrobenius_inverseImage B
      (fieldExtensionProj B X f k') F (rationalPointsEquivDegreeOne f' y).1.1 hy hx
      (n / residueDegree f (Φ y).1.1.1 - 1) he
    rwa [Nat.sub_add_cancel (Nat.div_pos (Nat.le_of_dvd hpos hd) (Nat.pos_of_ne_zero hd0))] at key
  rw [Fintype.sum_congr _ _ hpt, ← Equiv.sum_comp Φ.symm, Fintype.sum_sigma]
  simp only [Equiv.apply_symm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine Eq.trans ?_ (finsum_cond_eq_sum_of_cond_iff (t := S) _ fun {x} _ => ?_).symm
  · rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.card_eq_nat_card, natCard_residueEmbeddings, hn, ite_eq_left (hS y)]
  · rw [Finset.mem_filter]
    simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨fun hx => ⟨Nat.le_of_dvd hpos hx, hx⟩, And.right⟩

end Stacks.EtaleCohomology

end
