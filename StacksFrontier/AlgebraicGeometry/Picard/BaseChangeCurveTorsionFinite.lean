module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClassGroupPicardBridge
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicardSequence
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusFixedTorsion

/-!
# The `n`-torsion of the Picard group of a curve over a separable closure is finite

For a smooth proper curve `Y` over an algebraically closed field and `n` invertible in the field,
`Pic(Y)[n]` is finite: it is the `n`-torsion of `Pic⁰(Y)`, the rational points of the Jacobian
(`AlgebraicGeometry.finite_schemePicard_torsion`), read in the model `Stacks.Picard.ofScheme`
through `Stacks.GluePicard.picardModelAddEquiv`. For a smooth proper geometrically irreducible
curve over any field `k`, the base change to `k̄` is again a smooth proper curve, so
`Pic(Y_k̄)[ℓⁿ]` is finite for `ℓ` invertible in `k`.

## Main results

* `Stacks.Picard.finite_torsionBy_ofScheme_of_isCurve`: `Pic(Y)[n]` is finite.
* `Stacks.Picard.isCurve_baseChange_of_geometricallyIrreducible`: `Y_K` is a curve over `K`.
* `Stacks.Picard.finite_torsionBy_ofScheme_baseChange_algebraicClosure`: `Pic(Y_k̄)[ℓⁿ]` is
  finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-- **`Pic(Y)[n]` is finite** for a smooth proper curve `Y` over an algebraically closed field `k`
and `n` invertible in `k`. -/
theorem finite_torsionBy_ofScheme_of_isCurve {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q] {n : ℕ}
    (hn : IsUnit (n : k)) : Finite (Submodule.torsionBy ℤ (ofScheme Y) (n : ℤ)) := by
  have h := Stacks.EtaleCohomology.finite_nsmul_torsion_of_addEquiv
    (Stacks.GluePicard.picardModelAddEquiv Y.toRingedSpace) (finite_schemePicard_torsion q hn)
  refine Finite.of_injective (fun c : Submodule.torsionBy ℤ (ofScheme Y) (n : ℤ) =>
    (⟨c.1, by rw [← natCast_zsmul]; exact c.2⟩ : {c : ofScheme Y // n • c = 0})) ?_
  intro c c' hc
  exact Subtype.ext (congrArg Subtype.val hc)

/-- **The base change of a smooth geometrically irreducible curve is a curve.** -/
theorem isCurve_baseChange_of_geometricallyIrreducible {k : Type u} [Field k]
    (Y : Over (Spec (.of k))) [IsCurve k Y.hom] [Smooth Y.hom] [GeometricallyIrreducible Y.hom]
    (K : Type u) [Field K] [Algebra k K] :
    IsCurve K (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have : GeometricallyReduced Y.hom := geometricallyReduced_of_smooth Y.hom
  have : GeometricallyIntegral Y.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible Y.hom
  have : IsIntegral (pullback Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  exact
    { topologicalKrullDim_eq_one := by
        rw [AlgebraicGeometry.topologicalKrullDim_baseChange k K (pullback.fst _ _) _ Y.hom
          (IsPullback.of_hasPullback _ _)]
        exact IsCurve.topologicalKrullDim_eq_one Y.hom }

/-- **`Pic(Y_k̄)[ℓⁿ]` is finite** for a smooth proper geometrically irreducible curve `Y` over a
field `k` and `ℓ` invertible in `k`. -/
theorem finite_torsionBy_ofScheme_baseChange_algebraicClosure {k : Type u} [Field k]
    (Y : Over (Spec (.of k))) [IsProper Y.hom] [Smooth Y.hom] [GeometricallyIrreducible Y.hom]
    [IsCurve k Y.hom] {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) (n : ℕ) :
    Finite (Submodule.torsionBy ℤ
      (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n)) := by
  have := isCurve_baseChange_of_geometricallyIrreducible Y (AlgebraicClosure k)
  have hn : IsUnit ((ℓ ^ n : ℕ) : AlgebraicClosure k) := by
    rw [Nat.cast_pow]
    exact (by simpa using hℓ.map (algebraMap k (AlgebraicClosure k)) :
      IsUnit (ℓ : AlgebraicClosure k)).pow n
  have h := finite_torsionBy_ofScheme_of_isCurve
    (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) hn
  rw [Nat.cast_pow] at h
  exact h

end Stacks.Picard
