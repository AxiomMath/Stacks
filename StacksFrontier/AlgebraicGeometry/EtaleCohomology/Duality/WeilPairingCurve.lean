module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RootOfUnityTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCupProductLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingAlgebra
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurvePicardBaseCase
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairing

/-!
# The Weil pairing on `Pic(X)[ℓⁿ]` of a curve, equivariant under a twisted morphism

Let `X` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k`, `N = ℓⁿ`. Through the Kummer isomorphism `Pic(X)[N] ≅ H¹(X, μ_N)` and `μ_N ≅ ℤ/N`
(a primitive root `ζ`), the cup product `H¹(X, ℤ/N) × H¹(X, ℤ/N) → H²(X, ℤ/N) ≅ H²(X, μ_N) ≅ ℤ/N`
gives a left nondegenerate pairing `e` on `Pic(X)[N]`
(`Stacks.EtaleCohomology.LevelChange.exists_comp_ne_zero_of_ne_zero`). For a morphism
`g : X ⟶ X` with `g ≫ f = f ≫ Spec(τ)`, `τ x = x ^ w` on `k`, whose pullback multiplies degrees
by `c`, `e(g^* a, g^* b) = (w c) e(a, b)`.

## Main definitions

* `Stacks.Picard.extRootsOfUnityAddEquiv`: `Hⁱ(X, ℤ/N) ≃+ Hⁱ(X, μ_N)`, through `1 ↦ ζ`.

## Main results

* `Stacks.Picard.exists_weilPairing_of_twist`: a left nondegenerate pairing on `Pic(X)[ℓⁿ]` with
  `e(g^* a, g^* b) = (w c) e(a, b)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.Picard

open Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {N : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)

/-- `Hⁱ(X, ℤ/N) ≃+ Hⁱ(X, μ_N)`: through the forgetful functor and `UΛ_X ≅ μ_N`, `1 ↦ ζ`. -/
def extRootsOfUnityAddEquiv (i : ℕ) :
    Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) i ≃+
      Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X N) i :=
  (extForgetSheafHAddEquiv (ZMod N) X _ i).trans
    (AlgebraicGeometry.SmallEtale.extPostcompIsoAddEquiv
      (Stacks.Kummer.etaleModuleConstantUnderlyingIso f hζ hN) i)

/-- `extRootsOfUnityAddEquiv` is the map induced by `UΛ_X ≅ μ_N` on `extForgetSheafH`. -/
theorem extRootsOfUnityAddEquiv_apply {i : ℕ}
    (e : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) i) :
    extRootsOfUnityAddEquiv f hζ hN i e =
      Sheaf.H.map (Stacks.Kummer.etaleModuleConstantUnderlyingIso f hζ hN).hom i
        (extForgetSheafH (ZMod N) X _ i e) :=
  rfl

/-- **The Weil pairing on `Pic(X)[ℓⁿ]`, equivariant under a twisted morphism.** Let `X` be a
smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible in `k`, and
`g : X ⟶ X` with `g ≫ f = f ≫ Spec(τ)` for a ring endomorphism `τ` of `k` with `τ x = x ^ w`,
whose pullback multiplies degrees by `c`. Then for every `n` there is a pairing
`e : Pic(X)[ℓⁿ] × Pic(X)[ℓⁿ] → ℤ/ℓⁿ`, left nondegenerate, with `e(g^* a, g^* b) = (w c) e(a, b)`.
-/
theorem exists_weilPairing_of_twist [IsAlgClosed k] [IsCurve k f] [Smooth f] [IsProper f]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) (g : X ⟶ X) (τ : k →+* k) (w : ℕ)
    (hg : g ≫ f = f ≫ Spec.map (CommRingCat.ofHom τ)) (hτ : ∀ x : k, τ x = x ^ w) (c : ℤ)
    (hdeg : ∀ L : ofScheme X,
      picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le (schemePullbackClassHom g L) =
        c * picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L) (n : ℕ) :
    ∃ e : Submodule.torsionBy ℤ (ofScheme X) ((ℓ : ℤ) ^ n) →+
        Submodule.torsionBy ℤ (ofScheme X) ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b : Submodule.torsionBy ℤ (ofScheme X) ((ℓ : ℤ) ^ n),
          e (torsionByRestrict (A := ofScheme X) (schemePullbackClassHom g) ((ℓ : ℤ) ^ n) a)
          (torsionByRestrict (A := ofScheme X) (schemePullbackClassHom g) ((ℓ : ℤ) ^ n) b) =
            ((w : ℤ) * c) • e a b := by
  have hp : ℓ.Prime := Fact.out
  set N := ℓ ^ n with hNdef
  have hN0 : N ≠ 0 := (pow_pos hp.pos n).ne'
  have hNk : IsUnit (N : k) := by rw [hNdef, Nat.cast_pow]; exact hℓ.pow n
  have : NeZero (N : k) := ⟨hNk.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have hX : IsUnit ((N : ℕ) : Γ(X, ⊤)) := Stacks.Kummer.isUnit_globalSections f hNk
  have hsurj := Stacks.Kummer.surjective_sheafH_map_powMap_zero.{u + 1, u, u + 1} X (n := N)
    (Stacks.Kummer.exists_pow_eq_globalUnit.{u} X N f (Nat.pos_of_ne_zero hN0))
  have hsub : AddSubgroup.torsionBy (ofScheme X) (N : ℤ) =
      (Submodule.torsionBy ℤ (ofScheme X) ((ℓ : ℤ) ^ n)).toAddSubgroup := by
    rw [hNdef, Nat.cast_pow]
  let κ := ((extRootsOfUnityAddEquiv f hζ hN0 1).trans
    (Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion.{u + 1, u + 1, u} X N hN0 hX hsurj)).trans
      (AddEquiv.addSubgroupCongr hsub)
  have hκ : ∀ y, ((κ y : Submodule.torsionBy ℤ (ofScheme X) ((ℓ : ℤ) ^ n)) : ofScheme X) =
      Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion.{u + 1, u + 1, u} X N hN0 hX hsurj
        (extRootsOfUnityAddEquiv f hζ hN0 1 y) := fun y => rfl
  have htw : ∀ {i : ℕ} (y : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      X.smallEtaleTopology) (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
        X.smallEtaleTopology) i),
      Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} g N i
          (extRootsOfUnityAddEquiv f hζ hN0 i y) =
        (w : ℤ) • extRootsOfUnityAddEquiv f hζ hN0 i (constantExtRestriction (ZMod N) g i y) :=
    fun y => rootsOfUnityPullbackMap_extForgetSheafH hζ hN0 f f g τ w hg (hτ ζ) y
  let T := (Stacks.Kummer.smoothProperCurveTrace f hNk).toAddMonoidHom.comp
    (extRootsOfUnityAddEquiv f hζ hN0 2).toAddMonoidHom
  exact exists_pairing_of_cup κ T
    ((Stacks.Kummer.smoothProperCurveTrace f hNk).injective.comp
      (extRootsOfUnityAddEquiv f hζ hN0 2).injective)
    (Ext.bilinearComp _ _ _ 1 1 2 rfl)
    (fun a ha => LevelChange.exists_comp_ne_zero_of_ne_zero f hℓ n a ha)
    (torsionByRestrict (A := ofScheme X) (schemePullbackClassHom g) ((ℓ : ℤ) ^ n))
    (constantExtRestriction (ZMod N) g 1) (constantExtRestriction (ZMod N) g 2) (w : ℤ) c
    (fun x y => (constantExtRestriction_comp (ZMod N) g x y rfl).symm)
    (fun a => by
      apply κ.injective
      rw [AddEquiv.apply_symm_apply, map_zsmul]
      obtain ⟨x, rfl⟩ := κ.surjective a
      rw [AddEquiv.symm_apply_apply]
      apply Subtype.ext
      show schemePullbackClassHom g ((κ x : Submodule.torsionBy ℤ (ofScheme X) _) : ofScheme X) =
        (w : ℤ) • ((κ (constantExtRestriction (ZMod N) g 1 x) :
          Submodule.torsionBy ℤ (ofScheme X) _) : ofScheme X)
      rw [hκ, hκ, ← Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion_naturality.{u + 1, u + 1, u}
        g N hN0 hX hX hsurj hsurj, htw, map_zsmul]
      rfl)
    (fun z => by
      show (w : ℤ) • Stacks.Kummer.smoothProperCurveTrace f hNk
          (extRootsOfUnityAddEquiv f hζ hN0 2 (constantExtRestriction (ZMod N) g 2 z)) =
        c • Stacks.Kummer.smoothProperCurveTrace f hNk (extRootsOfUnityAddEquiv f hζ hN0 2 z)
      rw [← map_zsmul, ← htw]
      exact Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap f f hNk hNk g c hdeg _)

end Stacks.Picard

end
