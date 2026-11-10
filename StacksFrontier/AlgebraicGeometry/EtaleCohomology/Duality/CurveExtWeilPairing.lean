module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingCurve
public import StacksFrontier.AlgebraicGeometry.Picard.BaseChangeCurveTorsionFinite

/-!
# The Weil pairing on `H¹(X, ℤ/ℓⁿ)` of a curve, equivariant under a self-map over the base

Let `X` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k` and `N = ℓⁿ`. The cup product `H¹(X, ℤ/N) × H¹(X, ℤ/N) → H²(X, ℤ/N)` followed by the
trace `H²(X, ℤ/N) ≅ H²(X, μ_N) ≅ ℤ/N` (through a primitive `N`-th root of unity) is a left
nondegenerate pairing (`Stacks.EtaleCohomology.LevelChange.exists_comp_ne_zero_of_ne_zero`). For
`g : X ⟶ X` over `k` whose pullback multiplies degrees of line bundles by `c`, restriction along
`g` multiplies it by `c` (`Stacks.Picard.exists_extPairing_of_comp_eq`): restriction commutes with
cup products and the trace of `g^* y` is `c` times the trace of `y`.

This is the form of the Weil pairing on `H¹(X_k̄, ℤ/ℓⁿ)` that the Frobenius `π̄ = π_X × id` of a
curve over a finite field acts on, as needed for
[Tag 03V8](https://stacks.math.columbia.edu/tag/03V8).

## Main results

* `Stacks.Picard.finite_ext_one_unitSheaf`: `H¹(X, ℤ/ℓⁿ)` is finite.
* `Stacks.Picard.exists_extPairing_of_comp_eq`: the pairing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.Picard

open Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] {ℓ : ℕ} [Fact ℓ.Prime]

/-- `ℓⁿ` is a unit in `k` and nonzero in `ℕ` when `ℓ` is a prime unit in `k`. -/
private theorem isUnit_natCast_pow_and_ne_zero {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (hp : IsUnit (p : K)) (n : ℕ) : IsUnit ((p ^ n : ℕ) : K) ∧ p ^ n ≠ 0 :=
  ⟨by simpa using hp.pow n, pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩

include f in
/-- **`H¹(X, ℤ/ℓⁿ)` is finite** for a smooth proper curve over an algebraically closed field in
which `ℓ` is invertible: it is `Pic(X)[ℓⁿ]` through the Kummer sequence. -/
theorem finite_ext_one_unitSheaf (hℓ : IsUnit (ℓ : k)) (n : ℕ) :
    Finite (Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
        X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n)) X.smallEtaleTopology)
      1) := by
  obtain ⟨hNk, hN0⟩ := isUnit_natCast_pow_and_ne_zero hℓ n
  set N := ℓ ^ n with hNdef
  have : NeZero (N : k) := ⟨hNk.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have hX : IsUnit ((N : ℕ) : Γ(X, ⊤)) := Stacks.Kummer.isUnit_globalSections f hNk
  have hsurj := Stacks.Kummer.surjective_sheafH_map_powMap_zero.{u + 1, u, u + 1} X (n := N)
    (Stacks.Kummer.exists_pow_eq_globalUnit.{u} X N f (Nat.pos_of_ne_zero hN0))
  have : Finite (Submodule.torsionBy ℤ (ofScheme X) (N : ℤ)) :=
    finite_torsionBy_ofScheme_of_isCurve f hNk
  have : Finite (AddSubgroup.torsionBy (ofScheme X) (N : ℤ)) :=
    Finite.of_injective (fun c : AddSubgroup.torsionBy (ofScheme X) (N : ℤ) =>
      (⟨c.1, c.2⟩ : Submodule.torsionBy ℤ (ofScheme X) (N : ℤ)))
      fun _ _ hc => Subtype.ext (congrArg Subtype.val hc)
  exact Finite.of_equiv _ ((extRootsOfUnityAddEquiv f hζ hN0 1).trans
    (Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion.{u + 1, u + 1, u} X N hN0 hX
      hsurj)).symm.toEquiv

include f in
/-- **The Weil pairing on `H¹(X, ℤ/ℓⁿ)`, equivariant under a self-map over `k`.** Let `X` be a
smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible in `k` and
`g : X ⟶ X` a morphism over `k` whose pullback multiplies degrees of line bundles by `c`. Then
there is a left nondegenerate pairing `e` on `H¹(X, ℤ/ℓⁿ) = Ext¹(ℤ/ℓⁿ_X, ℤ/ℓⁿ_X)` with values in
`ℤ/ℓⁿ` such that `e(g^* a, g^* b) = c e(a, b)`. -/
theorem exists_extPairing_of_comp_eq (hℓ : IsUnit (ℓ : k)) (g : X ⟶ X) (hg : g ≫ f = f)
    (c : ℤ)
    (hdeg : ∀ L : ofScheme X,
      picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le (schemePullbackClassHom g L) =
        c * picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L) (n : ℕ) :
    ∃ e : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
          X.smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
          X.smallEtaleTopology) 1 →+
        Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
          X.smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
          X.smallEtaleTopology) 1 →+ ZMod (ℓ ^ n),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (constantExtRestriction (ZMod (ℓ ^ n)) g 1 a)
          (constantExtRestriction (ZMod (ℓ ^ n)) g 1 b) = c • e a b := by
  obtain ⟨hNk, hN0⟩ := isUnit_natCast_pow_and_ne_zero hℓ n
  set N := ℓ ^ n with hNdef
  have : NeZero (N : k) := ⟨hNk.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N
  have hg' : g ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [hg, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  have htw : ∀ (y : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      X.smallEtaleTopology) (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
        X.smallEtaleTopology) 2),
      Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} g N 2
          (extRootsOfUnityAddEquiv f hζ hN0 2 y) =
        extRootsOfUnityAddEquiv f hζ hN0 2 (constantExtRestriction (ZMod N) g 2 y) :=
    fun y => by
      have := rootsOfUnityPullbackMap_extForgetSheafH hζ hN0 f f g (RingHom.id k) 1 hg'
        (by simp) y
      rwa [Nat.cast_one, one_smul] at this
  let T := (Stacks.Kummer.smoothProperCurveTrace f hNk).toAddMonoidHom.comp
    (extRootsOfUnityAddEquiv f hζ hN0 2).toAddMonoidHom
  obtain ⟨e, he0, he⟩ := exists_pairing_of_cup (AddEquiv.refl _) T
    ((Stacks.Kummer.smoothProperCurveTrace f hNk).injective.comp
      (extRootsOfUnityAddEquiv f hζ hN0 2).injective)
    (Ext.bilinearComp _ _ _ 1 1 2 rfl)
    (fun a ha => LevelChange.exists_comp_ne_zero_of_ne_zero f hℓ n a ha)
    (constantExtRestriction (ZMod N) g 1)
    (constantExtRestriction (ZMod N) g 1) (constantExtRestriction (ZMod N) g 2) 1 c
    (fun x y => (constantExtRestriction_comp (ZMod N) g x y rfl).symm)
    (fun a => by simp)
    (fun z => by
      change (1 : ℤ) • Stacks.Kummer.smoothProperCurveTrace f hNk
          (extRootsOfUnityAddEquiv f hζ hN0 2 (constantExtRestriction (ZMod N) g 2 z)) =
        c • Stacks.Kummer.smoothProperCurveTrace f hNk (extRootsOfUnityAddEquiv f hζ hN0 2 z)
      rw [one_smul, ← htw]
      exact Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap f f hNk hNk g c hdeg _)
  exact ⟨e, he0, fun a b => by rw [he, one_mul]⟩

end Stacks.Picard

end
