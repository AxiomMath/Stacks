module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# The local input to the support of a pullback

The support of a module of finite type on a scheme is computed stalkwise by
`SheafOfModules.mem_supp_iff_nontrivial_stalk`, and the stalk is a finite module over the local
ring at the point by `SheafOfModules.finite_stalk`. Comparing the support of a pullback with the
inverse image of the support therefore reduces, at a point, to the behaviour of a nonzero finite
module over a local ring under base change along a local homomorphism. This file supplies that
local statement, and the geometric reading of it on a scheme.

## Main results

* `Stacks.Support.exists_surjective_toResidueField`: a nonzero module of finite type over a
  local ring surjects onto the residue field.
* `Stacks.Support.nontrivial_tensorProduct_of_isLocalHom`: base change of a nonzero module of
  finite type along a local homomorphism of local rings is nonzero.
* `Stacks.Support.nontrivial_of_nontrivial_tensorProduct` is the converse direction, which needs
  no hypotheses at all.
* `Stacks.Support.exists_surjective_stalk_toResidueField` reads the first statement at a point
  of the support of a module of finite type on a scheme.

## Implementation notes

`Stacks.Support.nontrivial_tensorProduct_of_isLocalHom` is proved without base-change towers:
a surjection of the module onto the residue field `κ_R` of the source base-changes to a
surjection onto `κ_R ⊗_R S = S ⧸ 𝔪_R S`, and the latter is nonzero precisely because `𝔪_R`
lands in `𝔪_S`. In particular no faithful flatness of a residue field extension is used.

The two statements are exactly the local halves of the stalkwise argument for
[Stacks Project, Tag 056J] "pullback_support": for a morphism of schemes `f : Y ⟶ X`, a point
`y` of `Y` and a module `F` of finite type on `X`, the stalk `F_{f y}` is a finite module over
`𝒪_{X, f y}`, the ring map `𝒪_{X, f y} ⟶ 𝒪_{Y, y}` induced by `f` is local, and so the base
change of the stalk is nonzero exactly when the stalk is. What is *not* available in the library
is the identification of `(f^* F)_y` with that base change: `AlgebraicGeometry.Scheme.Modules`'
pullback is Mathlib's abstract left adjoint of pushforward, while the only tensor-formula stalk
computation in the library, `PullbackStalkTensor.stalkPullbackTensorIso` (Tag 0098), computes
the stalk of the *explicit* model `𝒪_X ⊗_{f^{-1}𝒪_Y} f^{-1}G` of Tag 0095 (2), and nothing
identifies the two. See the discussion in
`StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewisePoint`.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u

namespace Stacks.Support

/-- A nonzero module of finite type over a local ring admits a surjection onto the residue
field: its reduction modulo the maximal ideal is a nonzero vector space, hence carries a
surjective linear functional. -/
theorem exists_surjective_toResidueField {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    ∃ φ : M →ₗ[R] ResidueField R, Function.Surjective φ := by
  have hV : Nontrivial (ResidueField R ⊗[R] M) := by
    rw [← not_subsingleton_iff_nontrivial, IsLocalRing.subsingleton_tensorProduct]
    exact not_subsingleton M
  let b := Module.Basis.ofVectorSpace (ResidueField R) (ResidueField R ⊗[R] M)
  obtain ⟨i⟩ := b.index_nonempty
  let φ : M →ₗ[R] ResidueField R :=
    ((b.coord i).restrictScalars R).comp (TensorProduct.mk R (ResidueField R) M 1)
  have hφ : ∀ m : M, φ m = b.coord i (1 ⊗ₜ[R] m) := fun _ => rfl
  refine ⟨φ, ?_⟩
  have hne : ∃ m : M, φ m ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not, hφ] at hall
    have hzero : ∀ z : ResidueField R ⊗[R] M, b.coord i z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c m =>
          have hc : c ⊗ₜ[R] m = c • (1 : ResidueField R) ⊗ₜ[R] m := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [hc, map_smul, hall m, smul_zero]
      | add z w hz hw => rw [map_add, hz, hw, add_zero]
    have hone : b.coord i (b i) = 1 := by simp
    exact one_ne_zero (hone.symm.trans (hzero (b i)))
  obtain ⟨m, hm⟩ := hne
  intro c
  obtain ⟨r, hr⟩ := residue_surjective (c * (φ m)⁻¹)
  refine ⟨r • m, ?_⟩
  rw [map_smul, Algebra.smul_def, show algebraMap R (ResidueField R) r = residue R r from rfl, hr,
    inv_mul_cancel_right₀ hm]

/-- The maximal ideal of the source of a local homomorphism generates a proper submodule of the
target. -/
theorem maximalIdeal_smul_top_ne_top_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    (maximalIdeal R • (⊤ : Submodule R S)) ≠ ⊤ := by
  have hle : maximalIdeal R • (⊤ : Submodule R S) ≤ (maximalIdeal S).restrictScalars R := by
    refine Submodule.smul_le.mpr fun r hr s _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (map_nonunit (algebraMap R S) r hr)
  intro htop
  have h1 : (1 : S) ∈ maximalIdeal S := hle (by rw [htop]; exact Submodule.mem_top)
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- **Base change of a nonzero module of finite type along a local homomorphism of local rings
is nonzero.** A surjection of the module onto the residue field of the source base-changes to a
surjection onto `S ⧸ 𝔪_R S`, which is nonzero because `𝔪_R` lands in `𝔪_S`. -/
@[ega "0 1.7.5" "Nakayama step"]
theorem nontrivial_tensorProduct_of_isLocalHom {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [IsLocalRing R] [IsLocalRing S]
    [Module.Finite R M] [IsLocalHom (algebraMap R S)] [Nontrivial M] :
    Nontrivial (M ⊗[R] S) := by
  obtain ⟨φ, hφ⟩ := exists_surjective_toResidueField (R := R) (M := M)
  have hquot : Nontrivial (S ⧸ maximalIdeal R • (⊤ : Submodule R S)) :=
    Submodule.Quotient.nontrivial_iff.mpr maximalIdeal_smul_top_ne_top_of_isLocalHom
  have hks : Nontrivial (ResidueField R ⊗[R] S) :=
    (TensorProduct.quotTensorEquivQuotSMul S (maximalIdeal R)).nontrivial_congr.mpr hquot
  have hid : Function.Surjective ⇑(LinearMap.id : S →ₗ[R] S) := fun s => ⟨s, rfl⟩
  exact (TensorProduct.map_surjective hφ hid).nontrivial

/-- If a tensor product is nonzero then so is its left factor. -/
theorem nontrivial_of_nontrivial_tensorProduct {R S M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid S] [Module R S]
    (h : Nontrivial (M ⊗[R] S)) : Nontrivial M := by
  by_contra hM
  have hM' : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
  refine (not_nontrivial_iff_subsingleton.mpr ⟨fun a b => ?_⟩) h
  have hz (z : M ⊗[R] S) : z = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m s => rw [hM'.elim m 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, zero_add]
  exact (hz a).trans (hz b).symm

/-- At a point in the support of a module of finite type on a scheme, the stalk admits a
surjection onto the residue field of the local ring at that point. The stalk is a finite
module over that local ring by `SheafOfModules.finite_stalk`, and it is nonzero because the
point lies in the support. -/
theorem exists_surjective_stalk_toResidueField {X : AlgebraicGeometry.Scheme.{u}}
    (F : X.Modules) [F.IsFiniteType] (x : X) (hx : x ∈ SheafOfModules.supp F) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    ∃ φ : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] ResidueField (X.presheaf.stalk x),
      Function.Surjective φ := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  have : Nontrivial (F.presheaf.stalk x) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp hx
  exact exists_surjective_toResidueField

end Stacks.Support

end
