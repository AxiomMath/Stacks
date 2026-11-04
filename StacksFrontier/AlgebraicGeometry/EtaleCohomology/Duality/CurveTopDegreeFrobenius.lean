module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveExtWeilPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FrobeniusBaseChangeDegree

/-!
# The geometric Frobenius on `H²` of a smooth proper curve is multiplication by `q`

Let `k` be a finite field with `q = p^f` elements, `K` an algebraically closed extension of `k`,
`Y` a `k`-scheme such that `Y_K` is a smooth proper curve over `K`, and `ℓ` a prime invertible
in `K`. Restriction along the base change `π̄ = π_Y × id` of the geometric Frobenius is
multiplication by `q` on `H²(Y_K, ℤ/ℓⁿ)`
(`Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_two_of_curve`).

## Main results

* `Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_two_of_curve`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (K : Type u) [Field K]
  [Algebra k K] [IsAlgClosed K] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)
  [IsCurve K (pullback.snd Y.hom (specAlgebraMap k K))]
  [Smooth (pullback.snd Y.hom (specAlgebraMap k K))]
  [IsProper (pullback.snd Y.hom (specAlgebraMap k K))]

/-- **The geometric Frobenius on `H²` of a smooth proper curve is multiplication by `q`.** For a
finite field `k` with `p ^ f` elements, `K` algebraically closed over `k` with `Y_K` a smooth
proper curve over `K`, and `ℓ` a prime invertible in `K`, restriction along
`π̄ = π_Y × id` multiplies every class of `H²(Y_K, ℤ/ℓⁿ)` by `p ^ f`. -/
theorem constantExtRestriction_geometricFrobeniusBaseChange_two_of_curve {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
        (fieldBaseChange Y K).smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
        (fieldBaseChange Y K).smallEtaleTopology) 2) :
    constantExtRestriction (ZMod (ℓ ^ n)) (geometricFrobeniusBaseChange Y K p f hcard) 2 z =
      (p ^ f) • z := by
  have hp : ℓ.Prime := Fact.out
  have hN0 : ℓ ^ n ≠ 0 := (pow_pos hp.pos n).ne'
  have hNk : IsUnit (((ℓ ^ n : ℕ)) : K) := by rw [Nat.cast_pow]; exact hℓ.pow n
  have : NeZero (((ℓ ^ n : ℕ)) : K) := ⟨hNk.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (ℓ ^ n)
  let fY := pullback.snd Y.hom (specAlgebraMap k K)
  let g := geometricFrobeniusBaseChange Y K p f hcard
  have hg' : g ≫ fY = fY ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    rw [geometricFrobeniusBaseChange_comp_snd, show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ from rfl,
      Spec.map_id, Category.comp_id]
  have htw := rootsOfUnityPullbackMap_extForgetSheafH hζ hN0 fY fY g (RingHom.id K) 1 hg'
    (by simp) z
  rw [Nat.cast_one, one_smul] at htw
  have hdeg := picardDegree_schemePullbackClassHom_geometricFrobeniusBaseChange Y K p f hcard
  have htr := Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap fY fY hNk hNk g
    (Fintype.card k : ℤ) hdeg (Stacks.Picard.extRootsOfUnityAddEquiv fY hζ hN0 2 z)
  have e1 : Stacks.Picard.extRootsOfUnityAddEquiv fY hζ hN0 2
      (constantExtRestriction (ZMod (ℓ ^ n)) g 2 z) =
      Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} g (ℓ ^ n) 2
        (Stacks.Picard.extRootsOfUnityAddEquiv fY hζ hN0 2 z) := htw.symm
  apply (Stacks.Picard.extRootsOfUnityAddEquiv fY hζ hN0 2).injective
  apply (Stacks.Kummer.smoothProperCurveTrace fY hNk).injective
  rw [e1, htr, map_nsmul, map_nsmul, hcard, natCast_zsmul]

end Stacks.EtaleCohomology

end
