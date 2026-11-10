module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldExtensionPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusPointExtension

/-!
# The twisted point side of the trace formula after a finite extension of the base field

Let `X` be a scheme of finite type over a finite field `k`, `F` an ℓ-adic sheaf on `X` with an
endomorphism `ψ`, `k'` an extension of `k` of degree `n`, `X' = X ×_k k'` and `g : X' ⟶ X`. Then

`∑_{y ∈ X'(k')} Tr(g⁻¹ψ ∘ π_y | (g⁻¹F)_ȳ)`
  `= ∑_{d ∣ n} d ∑_{deg x = d} Tr(ψ ∘ π_x ^ (n / d) | F_x̄)`,

the traces being taken on the rational stalks.

## Main results

* `LAdicSheaf.finsum_rationalStalkMap_comp_rationalStalkFrobenius_fieldExtension`: the
  identity above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

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
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f]
  (k' : Type u) [Field k'] [Finite k'] [Algebra k k'] [Module.Finite k k']
  [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1]

/-- If `k'` is an extension of `k` of degree `n`, `X' = X ×_k k'` and `g : X' ⟶ X` is the
projection, then for an endomorphism `ψ` of `F`
`∑_{y ∈ |X'|, deg_{k'} y = 1} Tr(g⁻¹ψ ∘ π_y | (g⁻¹F)_ȳ)`
`= ∑_{x ∈ |X|, deg x ∣ n} deg x · Tr(ψ ∘ π_x ^ (n / deg x) | F_x̄)`,
the traces being taken on the rational stalks. -/
public theorem LAdicSheaf.finsum_rationalStalkMap_comp_rationalStalkFrobenius_fieldExtension
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (ψ : F ⟶ F) (n : ℕ) (hn : Module.finrank k k' = n)
    (hn0 : n ≠ 0) :
    ∑ᶠ (y : closedPoints (fieldExtensionScheme B X f k').1)
        (_ : residueDegree (pullback.snd f (specAlgebraMap k k')) y.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkMap (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') ψ)
              (geometricPointAt _ y.1) ∘ₗ
            LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
            (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) y.1
            (finite_residueField (pullback.snd f (specAlgebraMap k k')) y.1 y.2) ^ 1) =
      ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ n),
        (residueDegree f x.1 : ℚ_[ℓ]) * LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkMap ψ (geometricPointAt X.1 x.1) ∘ₗ
            LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
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
  have hdeg : ∀ y : S, 0 < residueDegree f y.1.1 := fun y => Nat.pos_of_dvd_of_pos (hS y) hpos
  have hfin : ∀ y : S, Finite (residueEmbeddings f k' y.1.1) := fun y =>
    Nat.finite_of_card_ne_zero <| by
      rw [natCard_residueEmbeddings, hn, ite_eq_left (hS y)]
      exact (hdeg y).ne'
  let : ∀ y : S, Fintype (residueEmbeddings f k' y.1.1) := fun y =>
    @Fintype.ofFinite _ (hfin y)
  let h : S → ℚ_[ℓ] := fun x => LinearMap.trace ℚ_[ℓ] _
    (LAdicSheaf.rationalStalkMap ψ (geometricPointAt X.1 x.1.1) ∘ₗ
      LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1.1 (finite_residueField f x.1.1 x.1.2) ^
      (n / residueDegree f x.1.1))
  have hpt : ∀ y : rationalPoints f',
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkMap (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') ψ)
            (geometricPointAt _ (rationalPointsEquivDegreeOne f' y).1.1) ∘ₗ
          LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F)
          (rationalPointsEquivDegreeOne f' y).1.1
          (finite_residueField f' _ (rationalPointsEquivDegreeOne f' y).1.2) ^ 1) = h (Φ y).1 := by
    intro y
    have hy := finite_residueField f' _ (rationalPointsEquivDegreeOne f' y).1.2
    have hx := finite_residueField f _ (Φ y).1.1.2
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero
      (Nat.div_pos (Nat.le_of_dvd hpos (hS (Φ y).1)) (hdeg (Φ y).1)).ne'
    have he : Nat.card ((fieldExtensionScheme B X f k').1.residueField
        (rationalPointsEquivDegreeOne f' y).1.1) =
        Nat.card (X.1.residueField ((Φ y).1.1.1)) ^ (m + 1) := by
      rw [← hm,
        natCard_residueField_of_residueDegree_eq_one f' _ (rationalPointsEquivDegreeOne f' y).2,
        natCard_residueField_eq_pow_residueDegree f, ← pow_mul, Nat.mul_div_cancel' (hS _),
        Module.card_eq_pow_finrank (K := k) (V := k'), hn]
    exact LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_inverseImage_of_eq B
      (fieldExtensionProj B X f k') F ψ (rationalPointsEquivDegreeOne f' y).1.1 hy hx
      m he 1 _ (by rw [mul_one, hm])
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
