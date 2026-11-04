module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomologyNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnityFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePullbackDegree
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairing

/-!
# Pullback by an endomorphism on `Hⁱ(C, μ_n)` of a smooth proper curve

Let `C` be a smooth proper curve over an algebraically closed field `k`, `φ : C ⟶ C` a
nonconstant endomorphism over `k` and `n` invertible in `k`. The pullback
`φ^* = Stacks.EtaleCohomology.rootsOfUnityPullbackMap φ n i` on `Hⁱ(C, μ_n)` is, in the
coordinates of [Stacks, Tag 03RQ]:

* on `H⁰(C, μ_n) ≅ ℤ/n`, the identity;
* on `H¹(C, μ_n) ≅ Pic(C)[n]`, pullback of line bundles (Tag 03P8 and its naturality);
* on `H²(C, μ_n) ≅ ℤ/n`, multiplication by the degree of `φ` (Tag 0AMB, with
  `deg φ^*L = deg φ · deg L`);
* `Hⁱ(C, μ_n) = 0` for `i ≥ 3`.

## Main results

* `Stacks.EtaleCohomology.exists_h0_addEquiv_rootsOfUnityPullbackMap`,
  `Stacks.EtaleCohomology.exists_h1_addEquiv_rootsOfUnityPullbackMap`,
  `Stacks.EtaleCohomology.exists_h2_addEquiv_rootsOfUnityPullbackMap`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Kummer

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (g : C ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g]

omit [Smooth g] [IsProper g] in
/-- **`φ^*` on `H⁰(C, μ_n) ≅ ℤ/n` is the identity** for every endomorphism `φ` over `k`. -/
theorem exists_h0_addEquiv_rootsOfUnityPullbackMap {n : ℕ} (hn : IsUnit (n : k)) :
    ∃ e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C n) 0 ≃+ ZMod n,
      ∀ (φ : C ⟶ C) (_ : φ ≫ g = g) x,
        e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ n 0 x) = e x := by
  have hn0 : n ≠ 0 := neZero_of_isUnit hn
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : k) := ⟨hn.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  have : IsIntegral C := IsCurve.toIsVariety.toIsIntegral (k := k) (f := g)
  exact ⟨h0RootsOfUnityAddEquivZMod.{u, u + 1, u + 1} g hζ, fun φ w x => by
    rw [rootsOfUnityPullbackMap_zero_eq_self.{u, u + 1, u + 1} g hζ φ w x]⟩

omit [Smooth g] in
include g in
/-- **`φ^*` on `H¹(C, μ_{ℓ^m}) ≅ Pic(C)[ℓ^m]` is pullback of line bundles.** -/
theorem exists_h1_addEquiv_rootsOfUnityPullbackMap {ℓ m : ℕ} (hn : IsUnit ((ℓ ^ m : ℕ) : k)) :
    ∃ e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C (ℓ ^ m)) 1 ≃+
        Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ m),
      ∀ (φ : C ⟶ C) x, e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ (ℓ ^ m) 1 x) =
        Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme C)
          (Stacks.Picard.schemePullbackClassHom φ) ((ℓ : ℤ) ^ m) (e x) := by
  have hn0 : ℓ ^ m ≠ 0 := neZero_of_isUnit hn
  have : IsIntegral C := IsCurve.toIsVariety.toIsIntegral (k := k) (f := g)
  have hX := isUnit_natCast_globalSections C (ℓ ^ m) g hn
  have hsurj := surjective_sheafH_map_powMap_zero.{u + 1, u, u + 1} C (n := ℓ ^ m)
    (exists_pow_eq_globalUnit C (ℓ ^ m) g (Nat.pos_of_ne_zero hn0))
  have hsub : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) (((ℓ ^ m : ℕ) : ℤ)) =
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ m) := by
    rw [Nat.cast_pow]
  let e := (h1RootsOfUnityAddEquivPicardTorsion.{u + 1, u + 1, u} C (ℓ ^ m) hn0 hX hsurj).trans
    (LinearEquiv.ofEq _ _ hsub).toAddEquiv
  refine ⟨e, fun φ x => Subtype.ext ?_⟩
  exact h1RootsOfUnityAddEquivPicardTorsion_naturality.{u + 1, u + 1, u} φ (ℓ ^ m) hn0 hX hX
    hsurj hsurj x

/-- **`φ^*` on `H²(C, μ_n) ≅ ℤ/n` is multiplication by the degree of `φ`** (Tag 0AMB). -/
theorem exists_h2_addEquiv_rootsOfUnityPullbackMap {n : ℕ} (hn : IsUnit (n : k)) :
    ∃ e : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, u + 1} C n) 2 ≃+ ZMod n,
      ∀ (φ : C ⟶ C) (w : φ ≫ g = g) (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y) x,
        e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ n 2 x) =
          ((@degreeOver C C φ _ _ (locallyOfFiniteType_of_isCurve_comp k g g φ w)
            (isDominant_of_not_constant k g g φ hnc) : ℕ) : ZMod n) * e x := by
  refine ⟨smoothProperCurveTrace g hn, fun φ w hnc x => ?_⟩
  rw [smoothProperCurveTrace_rootsOfUnityPullbackMap g g hn hn φ _
    (fun L => Stacks.Picard.picardDegree_schemePullbackClassHom g g _ _ φ w hnc L) x,
    zsmul_eq_mul]
  push_cast
  rfl

end Stacks.EtaleCohomology

end
