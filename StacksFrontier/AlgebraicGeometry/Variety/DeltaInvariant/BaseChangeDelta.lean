module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.BaseChangeNormalization
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.RingTheory.Length.FlatLocalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta invariant of a flat local base change

For a reduced one-dimensional Nagata local ring the delta invariant is unchanged by
henselization, by strict henselization, and by completion at the maximal ideal. Here the delta
invariant of `A` is the length of `A'/A`, where `A' = integralClosure A (FractionRing A)`.

## Main results

* `Stacks.Curves.deltaInvariant_henselization`,
  `Stacks.Curves.deltaInvariant_strictHenselization` and
  `Stacks.Curves.deltaInvariant_adicCompletion_maximalIdeal`: the delta invariant is unchanged
  by henselization, by strict henselization and by completion at the maximal ideal.

## References

* [Stacks Project, Tag 0C3W](https://stacks.math.columbia.edu/tag/0C3W)
* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
-/

@[expose] public section

namespace Stacks.Curves

open IsLocalRing
open scoped TensorProduct

universe u v

/-- The residue field of a local ring has length one. -/
private theorem length_quotient_maximalIdeal_eq_one (R : Type*) [CommRing R] [IsLocalRing R] :
    Module.length R (R ⧸ maximalIdeal R) = 1 := by
  change Module.length R (ResidueField R) = 1
  rw [Module.length_eq_of_surjective (M := ResidueField R) (residue_surjective (R := R))]
  simp

/-- Length is unchanged by a flat local base change whose fibre has length one. -/
private theorem length_eq_of_tensor_quotient_equiv
    (A B N M : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [AddCommGroup N] [Module A N] [AddCommGroup M] [Module B M]
    (f : A →ₗ[A] N)
    (e : B ⊗[A] (N ⧸ LinearMap.range f) ≃ₗ[B] M)
    (hfiber : Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) = 1) :
    Module.length B M = Module.length A (N ⧸ LinearMap.range f) := by
  rw [← e.length_eq, IsLocalRing.length_baseChange]
  simp [hfiber]

/-- Let `N` be an `A`-algebra, `B` an `A`-algebra, and `g : N ⊗[A] B → K` an injective
`A`-algebra map into a `B`-algebra `K` which restricts to the canonical map on `B` and whose image
is exactly the integral closure of `B` in `K`. Then `B ⊗[A] (N/A)` is `B`-linearly isomorphic to
`(integralClosure B K)/B`. -/
private noncomputable def tensorProduct_quotient_equiv_quotient
    (A B K N : Type*) [CommRing A] [CommRing B] [CommRing K] [CommRing N]
    [Algebra A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K] [Algebra A N]
    (g : (N ⊗[A] B) →ₐ[A] K) (hg : Function.Injective g)
    (hcomp : g.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] N ⊗[A] B) =
      IsScalarTower.toAlgHom A B K)
    (hrange : ∀ x : K, x ∈ integralClosure B K ↔ ∃ y, g y = x) :
    B ⊗[A] (N ⧸ LinearMap.range (Algebra.linearMap A N)) ≃ₗ[B]
      (integralClosure B K) ⧸ LinearMap.range (Algebra.linearMap B (integralClosure B K)) := by
  let c := Algebra.TensorProduct.comm A N B
  let h : (B ⊗[A] N) →ₐ[A] K := g.comp c.symm.toAlgHom
  have hcompB : h.comp (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := N) : B →ₐ[A] B ⊗[A] N) =
      IsScalarTower.toAlgHom A B K := by
    ext b
    change g (c.symm (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := N) b)) = IsScalarTower.toAlgHom A B K b
    have hc : c.symm (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := N) b) =
        Algebra.TensorProduct.includeRight b := by
      apply c.injective
      simp [c, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.comm_tmul]
    exact hc ▸ DFunLike.congr_fun hcomp b
  let hlin : (B ⊗[A] N) →ₗ[B] K :=
    { toFun := h
      map_add' := fun x y => map_add h x y
      map_smul' := by
        intro b x
        rw [Algebra.smul_def, Algebra.smul_def]
        change h (algebraMap B (B ⊗[A] N) b * x) = algebraMap B K b * h x
        have hb : h (algebraMap B (B ⊗[A] N) b) = algebraMap B K b :=
          DFunLike.congr_fun hcompB b
        rw [map_mul, hb] }
  let hB : (B ⊗[A] N) →ₐ[B] K :=
    AlgHom.ofLinearMap hlin (map_one h) (fun x y => map_mul h x y)
  have hmem (x : B ⊗[A] N) : hB x ∈ integralClosure B K := by
    exact (hrange (h x)).mpr ⟨c.symm x, rfl⟩
  let hC : (B ⊗[A] N) →ₐ[B] integralClosure B K :=
    hB.codRestrict (integralClosure B K) hmem
  have hC_bij : Function.Bijective hC := by
    refine ⟨fun x y hxy ↦ c.symm.injective (hg ?_), fun y ↦ ?_⟩
    · exact (by simpa [hC, hB, hlin] using congrArg Subtype.val hxy : h x = h y)
    · obtain ⟨x, hx⟩ := (hrange (y : K)).mp y.property
      exact ⟨c x, Subtype.ext (by simpa [hC, hB, hlin, h] using hx)⟩
  let e : (B ⊗[A] N) ≃ₐ[B] integralClosure B K := AlgEquiv.ofBijective hC hC_bij
  let f : A →ₗ[A] N := Algebra.linearMap A N
  let lf : (B ⊗[A] A) →ₗ[B] (B ⊗[A] N) := TensorProduct.AlgebraTensorModule.lTensor B B f
  let P : Submodule B (B ⊗[A] N) := lf.range
  let Q : Submodule B (integralClosure B K) :=
    LinearMap.range (Algebra.linearMap B (integralClosure B K))
  have hecomp : e.toLinearEquiv.toLinearMap.comp lf =
      (Algebra.linearMap B (integralClosure B K)).comp
        (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b a
    have hleft : e (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := N) b) = algebraMap B (integralClosure B K) b := by
      apply Subtype.ext
      change hB (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := N) b) = algebraMap B K b
      simpa [hB, hlin] using DFunLike.congr_fun hcompB b
    have hright : e (Algebra.TensorProduct.includeRight (algebraMap A N a)) =
        algebraMap B (integralClosure B K) (algebraMap A B a) := by
      apply Subtype.ext
      change h (Algebra.TensorProduct.includeRight (algebraMap A N a)) =
        algebraMap B K (algebraMap A B a)
      have ht : Algebra.TensorProduct.includeRight (algebraMap A N a) =
          algebraMap A (B ⊗[A] N) a :=
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := N)).commutes a
      rw [ht, ← IsScalarTower.algebraMap_apply A B K]
      exact h.commutes a
    have hmul : lf (b ⊗ₜ[A] a) =
        Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := N) b *
          Algebra.TensorProduct.includeRight (algebraMap A N a) := by
      calc
        lf (b ⊗ₜ[A] a) = b ⊗ₜ[A] algebraMap A N a := by
          simp [lf, f, TensorProduct.AlgebraTensorModule.lTensor_tmul]
        _ = Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := N) b *
              Algebra.TensorProduct.includeRight (algebraMap A N a) := by
          symm
          rw [Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change e (lf (b ⊗ₜ[A] a)) = _
    rw [hmul, map_mul, hleft, hright]
    change algebraMap B (integralClosure B K) b *
        algebraMap B (integralClosure B K) (algebraMap A B a) =
      algebraMap B (integralClosure B K) (a • b)
    simp [Algebra.smul_def, map_mul, mul_comm]
  have hPQ : Submodule.map e.toLinearEquiv.toLinearMap P = Q := by
    dsimp [P, Q]
    rw [← LinearMap.range_comp, hecomp,
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr (TensorProduct.AlgebraTensorModule.rid A B B).surjective)]
  have hP : LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor B B
      (Submodule.subtype (LinearMap.range f))) = P := by
    apply Submodule.restrictScalars_injective A
    exact (LinearMap.lTensor_range (Q := B) (g := f)).symm
  let et := (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
    (R := A) (A := B) (B := A) (M := B) (N := N) (LinearMap.range f)).trans
      (Submodule.quotEquivOfEq _ _ hP)
  exact et.trans (Submodule.Quotient.equiv P Q e.toLinearEquiv hPQ)

/-- Let `A → B` be a flat local homomorphism of local rings, with `B` Noetherian, carrying the
maximal ideal of `A` to the maximal ideal of `B`, such that the base change to `B` of the
integral closure of `A` in its total ring of fractions maps isomorphically onto the integral
closure of `B` in its total ring of fractions. Then `A` and `B` have the same delta invariant. -/
private theorem deltaInvariant_eq_of_flat_local_baseChange
    {A : Type u} [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [Module.Flat A B] [IsLocalHom (algebraMap A B)]
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hcomparison : ∃ q : FractionRing A →ₐ[A] FractionRing B,
      ∃ g : (integralClosure A (FractionRing A) ⊗[A] B) →ₐ[A] FractionRing B,
        Function.Injective g ∧
          g.range = (integralClosure B (FractionRing B)).restrictScalars A ∧
          g.comp
              (Algebra.TensorProduct.includeLeft :
                integralClosure A (FractionRing A) →ₐ[A]
                  (integralClosure A (FractionRing A) ⊗[A] B)) =
            q.comp (integralClosure A (FractionRing A)).val ∧
          g.comp
              (Algebra.TensorProduct.includeRight :
                B →ₐ[A] (integralClosure A (FractionRing A) ⊗[A] B)) =
            IsScalarTower.toAlgHom A B (FractionRing B)) :
    Ring.deltaInvariant B = Ring.deltaInvariant A := by
  obtain ⟨-, g, hg, hrange, -, hcompRight⟩ := hcomparison
  have hmem (x : FractionRing B) : x ∈ integralClosure B (FractionRing B) ↔ ∃ y, g y = x := by
    rw [← Subalgebra.mem_restrictScalars (R := A), ← hrange]
    exact Iff.rfl
  let e := tensorProduct_quotient_equiv_quotient A B (FractionRing B)
    ↥(integralClosure A (FractionRing A)) g hg hcompRight hmem
  exact length_eq_of_tensor_quotient_equiv A B
    ↥(integralClosure A (FractionRing A))
    (↥(integralClosure B (FractionRing B)) ⧸
      LinearMap.range (Algebra.linearMap B ↥(integralClosure B (FractionRing B))))
    (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) e
    (hmax ▸ length_quotient_maximalIdeal_eq_one B)

/-- Henselization preserves the delta invariant of a reduced
one-dimensional Nagata local ring. -/
@[stacks 0C3W "henselization"]
public theorem deltaInvariant_henselization
    (A Ah : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    Ring.deltaInvariant Ah = Ring.deltaInvariant A := by
  have : Module.Flat A Ah := IsLocalRing.IsHenselization.flat (L := ResidueField A)
  have : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (R := A) (L := ResidueField A) (Rh := Ah)
  have : IsNoetherianRing Ah :=
    (IsLocalRing.IsHenselization.isNagataRing (A := A) (Ah := Ah) hA).1
  exact deltaInvariant_eq_of_flat_local_baseChange Ah
    (IsLocalRing.IsHenselization.map_maximalIdeal (L := ResidueField A))
    (IsLocalRing.exists_integralClosure_henselization_map A Ah hA hdim)

/-- Strict henselization preserves the delta invariant of a reduced
one-dimensional Nagata local ring. -/
@[stacks 0C3W "strict henselization"]
public theorem deltaInvariant_strictHenselization
    (A Ash : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    (ksep : Type v) [Field ksep] [Algebra (ResidueField A) ksep]
    [IsSepClosure (ResidueField A) ksep] [IsLocalRing.IsHenselization A ksep Ash]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    Ring.deltaInvariant Ash = Ring.deltaInvariant A := by
  have : Module.Flat A Ash := IsLocalRing.IsHenselization.flat (L := ksep)
  have : IsLocalHom (algebraMap A Ash) :=
    IsLocalRing.IsHenselization.isLocalHom (R := A) (L := ksep) (Rh := Ash)
  have : IsNoetherianRing Ash :=
    (IsLocalRing.strictHenselization_isNagataRing (A := A) (Ash := Ash) ksep hA).1
  exact deltaInvariant_eq_of_flat_local_baseChange Ash
    (IsLocalRing.IsHenselization.map_maximalIdeal (L := ksep))
    (IsLocalRing.tensorProduct_integralClosure_isIntegralClosure_strictHenselization
      ksep hA hdim)

/-- Completion at the maximal ideal preserves the delta invariant of a reduced one-dimensional
Nagata local ring. -/
@[stacks 0C3W "completion", sga "7 X 2.26" "partial"]
public theorem deltaInvariant_adicCompletion_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    Ring.deltaInvariant (AdicCompletion (maximalIdeal A) A) = Ring.deltaInvariant A := by
  have : IsNoetherianRing A := hA.1
  let B := AdicCompletion (maximalIdeal A) A
  have : IsNoetherianRing B := AdicCompletion.isNoetherianRing (maximalIdeal A)
  have : Module.Flat A B := AdicCompletion.flat_of_isNoetherian (maximalIdeal A)
  exact deltaInvariant_eq_of_flat_local_baseChange B
    (AdicCompletion.maximalIdeal_eq_map (R := A)).symm
    (IsLocalRing.exists_fractionRing_map_and_tensorProduct_range_eq_integralClosure_completion
      hA hdim)

end Stacks.Curves

end
