module

public import Mathlib
public import StacksCore.RingTheory.Nakayama
public import StacksFrontier.Algebra.Homology.CochainComplexPlusTruncation
public import StacksFrontier.Algebra.Module.Projective.Nakayama
public import StacksFrontier.Homology.Perfect.NilpotentLifting

/-!
# Objects whose derived reduction is the base ring

Let `φ : B → k` be a surjective map of commutative rings with nilpotent kernel. An object `M` of
`D(B)` whose derived extension of scalars `k ⊗ᴸ_B M` is `k`, placed in degree `0`, is itself `B`
placed in degree `0`.

## Main results

* `StacksDraft.Perfect.nonempty_iso_singleFunctor_self_of_totalDerivedExtensionScalars_iso`:
  the statement above.

## Implementation notes

The complex `k[0]` is a bounded above complex of projective `k`-modules, so by [stacks 09AR]
(`exists_boundedAbove_projective_lift_representing_of_surjective`) `M` is represented by a bounded
above complex `P` of projective `B`-modules with `k ⊗_B P ≅ k[0]` termwise. Writing `I` for the
kernel of `φ`, the module `k ⊗_B N` is `N / I N` for every `B`-module `N`. So for `i ≠ 0` the
term `P^i` satisfies `P^i = I P^i`, hence vanishes because `I` is nilpotent; and `P^0 / I P^0` is
isomorphic to `B / I`, so `P^0` is finite by Nakayama's lemma for a nilpotent ideal, and then
isomorphic to `B` by [stacks 0BC6] (`quot_iso_lift`), both being finite projective. No hypothesis
on `k` is needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

variable {B k : Type u} [CommRing B] [CommRing k]

/-- For a surjection `φ : B → k`, the `B`-module underlying `k ⊗_B N` is `N / (ker φ) N`. -/
private noncomputable def restrictExtendScalarsEquivQuotSMul (φ : B →+* k)
    (hφ : Function.Surjective φ) (N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj N) ≃ₗ[B]
      N ⧸ (RingHom.ker φ • (⊤ : Submodule B N)) :=
  letI : Algebra B k := φ.toAlgebra
  let eLin : (B ⧸ RingHom.ker φ) ≃ₗ[B] k :=
    (RingHom.quotientKerEquivOfSurjective hφ).toAddEquiv.toLinearEquiv fun r x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact map_mul φ r x
  letI : Module B ((ModuleCat.extendScalars φ).obj N : Type u) := Module.compHom _ φ
  haveI : IsScalarTower B k ((ModuleCat.extendScalars φ).obj N : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (TensorProduct.AlgebraTensorModule.congr eLin.symm (LinearEquiv.refl B N)).trans
    (TensorProduct.quotTensorEquivQuotSMul N (RingHom.ker φ))

/-- A `B`-module killed by extension of scalars along a surjection with nilpotent kernel is
zero. -/
private theorem subsingleton_of_isZero_extendScalars (φ : B →+* k)
    (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ)) (N : ModuleCat.{u} B)
    (hN : IsZero ((ModuleCat.extendScalars φ).obj N)) : Subsingleton N := by
  have : Subsingleton ((ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj N)) :=
    (ModuleCat.isZero_iff_subsingleton.mp hN :
      Subsingleton ((ModuleCat.extendScalars φ).obj N : Type u))
  have : Subsingleton (N ⧸ (RingHom.ker φ • (⊤ : Submodule B N))) :=
    (restrictExtendScalarsEquivQuotSMul φ hφ N).symm.injective.subsingleton
  have htop : (⊤ : Submodule B N) ≤ RingHom.ker φ • ⊤ := fun x _ => by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact Subsingleton.elim _ _
  have hz := Submodule.eq_bot_of_le_smul_of_isNilpotent (RingHom.ker φ) ⊤ hnil htop
  exact ⟨fun x y => sub_eq_zero.mp (by
    have hxy : x - y ∈ (⊤ : Submodule B N) := trivial
    rw [hz] at hxy
    exact hxy)⟩

/-- A projective `B`-module whose extension of scalars along a surjection `φ : B → k` with
nilpotent kernel is `k` is isomorphic to `B`. -/
private theorem nonempty_linearEquiv_self_of_extendScalars_iso (φ : B →+* k)
    (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ)) (N : ModuleCat.{u} B)
    [Module.Projective B N] (e : (ModuleCat.extendScalars φ).obj N ≅ ModuleCat.of k k) :
    Nonempty (N ≃ₗ[B] B) := by
  classical
  set I := RingHom.ker φ
  let eLin : (ModuleCat.restrictScalars φ).obj (ModuleCat.of k k) ≃ₗ[B] B ⧸ I :=
    ((show (B ⧸ I) ≃+ (ModuleCat.restrictScalars φ).obj (ModuleCat.of k k) from
      (RingHom.quotientKerEquivOfSurjective hφ).toAddEquiv).toLinearEquiv fun r x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact map_mul φ r x).symm
  let eQ : (N ⧸ (I • (⊤ : Submodule B N))) ≃ₗ[B] (B ⧸ (I • (⊤ : Submodule B B))) :=
    (restrictExtendScalarsEquivQuotSMul φ hφ N).symm.trans <|
      ((ModuleCat.restrictScalars φ).mapIso e).toLinearEquiv.trans <|
        eLin.trans (Submodule.quotEquivOfEq _ _ (by simp [I]))
  have : Module.Finite B N := by
    have : Module.Finite B (N ⧸ (I • (⊤ : Submodule B N))) := Module.Finite.equiv eQ.symm
    rw [Module.finite_def] at *
    obtain ⟨s, hs⟩ := ‹(⊤ : Submodule B (N ⧸ (I • (⊤ : Submodule B N)))).FG›
    let lift : N ⧸ I • (⊤ : Submodule B N) → N :=
      Function.surjInv (I • (⊤ : Submodule B N)).mkQ_surjective
    refine ⟨s.image lift, ?_⟩
    apply Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_isNilpotent I hnil
    rw [Finset.coe_image, Set.image_image]
    have himage :
        ((I • (⊤ : Submodule B N)).mkQ ∘ lift) '' (s : Set _) = (s : Set _) := by
      ext x
      simp [lift]
    have hspan : Submodule.span B
        (((I • (⊤ : Submodule B N)).mkQ ∘ lift) '' (s : Set _)) = ⊤ := by
      rw [himage, hs]
    exact hspan
  refine quot_iso_lift I (fun x hx => ?_) ⟨eQ⟩
  obtain ⟨n, hn⟩ := hnil
  refine IsNilpotent.isUnit_one_add ⟨n, ?_⟩
  have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at this
  exact (Submodule.mem_bot B).mp this

/-- Let `φ : B → k` be a surjective map of commutative rings with nilpotent kernel. An object `M`
of `D(B)` whose derived extension of scalars along `φ` is `k` in degree `0` is `B` in
degree `0`. -/
theorem nonempty_iso_singleFunctor_self_of_totalDerivedExtensionScalars_iso (φ : B →+* k)
    (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ))
    (M : DerivedCategory (ModuleCat.{u} B))
    (e : (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj M ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) :
    Nonempty (M ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) := by
  let E := (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of k k)
  have hEproj (i : ℤ) : Module.Projective k (E.X i) := by
    by_cases hi : i = 0
    · subst hi
      exact Module.Projective.of_equiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of k k)).symm.toLinearEquiv
    · have := ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k k) i hi)
      exact Module.Projective.of_free
  obtain ⟨P, -, hPproj, ⟨eM⟩, ⟨eRed⟩⟩ :=
    exists_boundedAbove_projective_lift_representing_of_surjective.{u, u, u} φ hφ E M
      ⟨0, inferInstance⟩ hEproj
      ⟨((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} k) 0).app _).symm ≪≫ e.symm⟩ hnil
  have hred (i : ℤ) : (ModuleCat.extendScalars φ).obj (P.X i) ≅ E.X i :=
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i).mapIso eRed
  have hzero (i : ℤ) (hi : i ≠ 0) : IsZero (P.X i) := by
    have := subsingleton_of_isZero_extendScalars φ hφ hnil (P.X i)
      ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k k) i
        hi).of_iso (hred i))
    exact ModuleCat.isZero_of_subsingleton _
  have : P.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => hzero i (by omega)
  have : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hzero i (by omega)
  obtain ⟨eB⟩ := nonempty_linearEquiv_self_of_extendScalars_iso φ hφ hnil (P.X 0)
    (hred 0 ≪≫ HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of k k))
  exact ⟨eM.symm ≪≫ DerivedCategory.Q.mapIso (CochainComplex.isoSingleOfIsStrictly P 0 ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (eB.toModuleIso : P.X 0 ≅ ModuleCat.of B B)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} B) 0).app _).symm⟩

end StacksDraft.Perfect

end
