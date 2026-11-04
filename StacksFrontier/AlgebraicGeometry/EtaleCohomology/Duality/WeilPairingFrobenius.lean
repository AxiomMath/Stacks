module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PicardDegreeZeroDivisible
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusFixedTorsion
public import StacksFrontier.AlgebraicGeometry.Picard.BaseChangeCurveTorsionFinite
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup

/-!
# The Weil pairing on `Pic(Ȳ)[ℓⁿ]` is `q`-equivariant for the Frobenius

Let `Y` be a smooth proper geometrically irreducible curve over a finite field `k₀` with `q`
elements, `Ȳ = Y ×_{k₀} k̄₀`, and `σ = id_Y × Spec(F)` the Galois twist by the Frobenius
`F x = x ^ q` of `k̄₀`. Pullback along `σ` is `Stacks.Picard.frobeniusPicardHom`. This file
constructs a left nondegenerate pairing `e` on `Pic(Ȳ)[ℓⁿ]` with `e(σ^* a, σ^* b) = q e(a, b)`.

## Main results

* `Stacks.Picard.picardDegree_schemePullbackClassHom_of_twist`: an automorphism `σ` of a proper
  curve over `K` lying over an automorphism of `Spec K` preserves degrees.
* `Stacks.Picard.exists_weilPairing_frobeniusPicardHom`: the `q`-equivariant Weil pairing on
  `Pic(Ȳ)[ℓⁿ]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **An automorphism of a proper curve lying over an automorphism of the base field preserves
degrees.** If `σ : Z ⟶ Z` is an isomorphism with `σ ≫ f = f ≫ Spec(τ)` for a ring automorphism
`τ` of `K`, the square is cartesian, so the dimensions of the cohomology of `σ^* L` and of `L`
agree (Tag 02KH), hence `deg σ^* L = deg L`. -/
theorem picardDegree_schemePullbackClassHom_of_twist {K : Type u} [Field K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] (hdim : topologicalKrullDim Z ≤ 1)
    (σ : Z ⟶ Z) [IsIso σ] (τ : K ≃+* K)
    (hσ : σ ≫ f = f ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) (y : ofScheme Z) :
    picardDegree f hdim (schemePullbackClassHom σ y) = picardDegree f hdim y := by
  have : IsIso (CommRingCat.ofHom τ.toRingHom) := (RingEquiv.toCommRingCatIso τ).isIso_hom
  have h : IsPullback σ f f (Spec.map (CommRingCat.ofHom τ.toRingHom)) :=
    IsPullback.of_horiz_isIso ⟨hσ⟩
  have e := @Stacks.PicardCurve.picardDegree_schemePullbackClass_of_isPullback K K _ _
    τ.toRingHom.toAlgebra Z Z σ f f h _ _ _ _ hdim hdim y
  rw [picardDegree_picardModelAddEquiv, picardDegree_picardModelAddEquiv] at e
  exact e

/-- A Galois twist of a base change is an isomorphism, with inverse the twist by the inverse. -/
instance isIso_galoisTwist (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (X : Over (Spec (.of R))) (σ : S ≃ₐ[R] S) : IsIso (galoisTwist R S X σ) :=
  ⟨⟨galoisTwist R S X σ⁻¹, by rw [← galoisTwist_mul, mul_inv_cancel, galoisTwist_one],
    by rw [← galoisTwist_mul, inv_mul_cancel, galoisTwist_one]⟩⟩

/-- **The Weil pairing on `Pic(Ȳ)[ℓⁿ]` is `q`-equivariant for the Frobenius.** Let `Y` be a
smooth proper geometrically irreducible curve over a finite field `k₀` with `q` elements, `ℓ` a
prime invertible in `k₀` and `Ȳ = Y ×_{k₀} k̄₀`. For every `n` there is a pairing
`e : Pic(Ȳ)[ℓⁿ] × Pic(Ȳ)[ℓⁿ] → ℤ/ℓⁿ`, left nondegenerate, with `e(F a, F b) = q e(a, b)` for the
Frobenius `F = Stacks.Picard.frobeniusPicardHom Y`. -/
theorem exists_weilPairing_frobeniusPicardHom {ℓ : ℕ} (hp : ℓ.Prime) (K₀ : Type u) [Field K₀]
    [Fintype K₀] (Y : Over (Spec (.of K₀))) [IsProper Y.hom] [Smooth Y.hom]
    [GeometricallyIrreducible Y.hom] [IsCurve K₀ Y.hom] (hℓ : IsUnit (ℓ : K₀)) (n : ℕ) :
    ∃ e : Submodule.torsionBy ℤ (ofScheme (SchemeOver.baseChange K₀ (AlgebraicClosure K₀) Y))
          ((ℓ : ℤ) ^ n) →+
        Submodule.torsionBy ℤ (ofScheme (SchemeOver.baseChange K₀ (AlgebraicClosure K₀) Y))
          ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (torsionByRestrict (frobeniusPicardHom Y) _ a)
          (torsionByRestrict (frobeniusPicardHom Y) _ b) = (Fintype.card K₀ : ℤ) • e a b := by
  have : Fact ℓ.Prime := ⟨hp⟩
  set K := AlgebraicClosure K₀
  have := isCurve_baseChange_of_geometricallyIrreducible Y K
  set f : SchemeOver.baseChange K₀ K Y ⟶ Spec (.of K) :=
    pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))
  set F := FiniteField.frobeniusAlgEquivOfAlgebraic K₀ K
  have hℓK : IsUnit (ℓ : K) := by
    simpa using hℓ.map (algebraMap K₀ K)
  have hg : galoisTwist K₀ K Y F ≫ f = f ≫ Spec.map (CommRingCat.ofHom F.toRingEquiv.toRingHom) :=
    galoisTwist_comp_snd K₀ K Y F
  obtain ⟨e, he0, he⟩ := exists_weilPairing_of_twist f hℓK (galoisTwist K₀ K Y F)
    F.toRingEquiv.toRingHom (Fintype.card K₀) hg (fun x => rfl) 1
    (fun L => by
      rw [one_mul]
      exact picardDegree_schemePullbackClassHom_of_twist f _ _ F.toRingEquiv hg L) n
  refine ⟨e, he0, fun a b => ?_⟩
  rw [show ((Fintype.card K₀ : ℕ) : ℤ) = ((Fintype.card K₀ : ℕ) : ℤ) * 1 by rw [mul_one]]
  exact he a b

end Stacks.Picard

end
