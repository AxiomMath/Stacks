module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Algebra isomorphisms of endomorphism algebras as conjugations

Linear algebra over a commutative ring behind
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BrauerGroupScheme/EndomorphismAlgebra.lean`.
An algebra isomorphism `Module.End R P ≃ₐ[R] Module.End R Q` between endomorphism algebras of
modules with bases is conjugation by a linear equivalence once a matrix coefficient of the image of
a rank-one projection is a unit, and such a coefficient exists after mapping to a local ring. Also
the uniqueness of a scalar intertwiner and the transport of coordinates along a map of bases.
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.EtaleCohomology

/-- The core of the local calculation: once a rank-one operator has a unimodular vector in its
image, an algebra equivalence of endomorphism algebras is implemented by a linear equivalence. -/
private theorem algEquiv_eq_conjugate_of_dual
    {R : Type u} [CommRing R] {P Q : Type u}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (α : Module.End R P ≃ₐ[R] Module.End R Q)
    (u : P) (v : P →ₗ[R] R) (hvu : IsUnit (v u))
    (z : Q)
    (hz : ∃ d : Q →ₗ[R] R, d (α (LinearMap.smulRight v u) z) = 1) :
    ∃ T : P ≃ₗ[R] Q, α = T.conjAlgEquiv R := by
  simp_rw [AlgEquiv.ext_iff, LinearEquiv.conjAlgEquiv_apply,
    ← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
  let T := LinearMap.applyₗ z ∘ₗ α.toLinearMap ∘ₗ LinearMap.smulRightₗ v
  have hT (x : P) : T x = α (LinearMap.smulRight v x) z := rfl
  have hcomm (A : Module.End R P) (x : P) : T (A x) = α A (T x) := by
    simp only [hT, ← Module.End.mul_apply, ← map_mul]
    congr
    ext
    simp
  have hsurj : Function.Surjective T := by
    intro w
    obtain ⟨d, hd⟩ := hz
    refine ⟨α.symm (LinearMap.smulRight d w) u, ?_⟩
    rw [hcomm]
    simp [hT, hd]
  have hinj : Function.Injective T := by
    intro x y hxy
    have hsmul : LinearMap.smulRightₗ v x = LinearMap.smulRightₗ v y := by
      apply α.injective
      apply LinearMap.ext fun w => ?_
      obtain ⟨w', rfl⟩ := hsurj w
      calc
        α (LinearMap.smulRight v x) (T w') =
            T ((LinearMap.smulRight v x) w') := (hcomm _ _).symm
        _ = T (v w' • x) := rfl
        _ = v w' • T x := map_smul T (v w') x
        _ = v w' • T y := by rw [hxy]
        _ = T (v w' • y) := (map_smul T (v w') y).symm
        _ = T ((LinearMap.smulRight v y) w') := rfl
        _ = α (LinearMap.smulRight v y) (T w') := hcomm _ _
    simpa [hvu.smul_left_cancel] using congr($(hsmul) u)
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, fun A =>
    LinearMap.ext fun x => (hcomm A x).symm⟩

/-- A ring homomorphism out of the endomorphism ring of a finite free module into a nontrivial
ring does not kill a diagonal rank-one projection: the projections sum to the identity and are
conjugate to one another, so if one dies they all do. -/
private lemma ringHom_rankOne_ne_zero
    {R P B I : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    [Ring B] [Nontrivial B] [Finite I] (b : Module.Basis I R P)
    (β : Module.End R P →+* B) (i : I) :
    β (LinearMap.smulRight (b.coord i) (b i)) ≠ 0 := by
  let := Fintype.ofFinite I
  intro h
  have he (j : I) : β (LinearMap.smulRight (b.coord j) (b j)) = 0 := by
    have hmul : LinearMap.smulRight (b.coord i) (b j) *
        LinearMap.smulRight (b.coord i) (b i) *
        LinearMap.smulRight (b.coord j) (b i) =
        LinearMap.smulRight (b.coord j) (b j) := by
      ext x
      simp [Module.End.mul_apply]
    rw [← hmul, map_mul, map_mul, h, mul_zero, zero_mul]
  have hsum : ∑ j : I, LinearMap.smulRight (b.coord j) (b j) =
      (1 : Module.End R P) := by
    ext x
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, Module.End.one_apply] using b.sum_repr x
  have hc := congrArg β hsum
  simp [map_sum, he] at hc

/-- After an algebra isomorphism of endomorphism algebras, some matrix coefficient of the image of
a rank-one projection is a unit in a local ring receiving the base ring. Otherwise every
coefficient lies in the maximal ideal and the image vanishes modulo it. -/
lemma exists_isUnit_coord_smulRight_coord
    {R P Q A I K : Type u} [CommRing R] [CommRing A] [IsLocalRing A]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Finite I] [Finite K] [Nonempty K]
    (b : Module.Basis I R P) (c : Module.Basis K R Q)
    (α : Module.End R P ≃ₐ[R] Module.End R Q) (φ : R →+* A) (i : I) :
    ∃ j k : K, IsUnit (φ (c.coord j (α (LinearMap.smulRight (b.coord i) (b i)) (c k)))) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite K
  let ψ := (IsLocalRing.residue A).comp φ
  let β := ψ.mapMatrix.comp ((LinearMap.toMatrixAlgEquiv c).toRingHom.comp α.toRingHom)
  have h := ringHom_rankOne_ne_zero b β i
  by_contra hn
  apply h
  ext j k
  simp only [β, RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  change ψ ((LinearMap.toMatrixAlgEquiv c)
    (α (LinearMap.smulRight (b.coord i) (b i))) j k) = 0
  rw [LinearMap.toMatrixAlgEquiv_apply]
  change ψ (c.coord j (α (LinearMap.smulRight (b.coord i) (b i)) (c k))) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr fun hu => hn ⟨j, k, hu⟩

/-- An algebra isomorphism of endomorphism algebras of modules with bases is conjugation by a
linear equivalence as soon as one matrix coefficient of the image of a rank-one projection is a
unit. -/
theorem exists_linearEquiv_conjAlgEquiv_of_isUnit_coord
    {R P Q I K : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (b : Module.Basis I R P) (c : Module.Basis K R Q)
    (α : Module.End R P ≃ₐ[R] Module.End R Q) (i : I) (j k : K)
    (h : IsUnit (c.coord j
      (α (LinearMap.smulRight (b.coord i) (b i)) (c k)))) :
    ∃ T : P ≃ₗ[R] Q, α = T.conjAlgEquiv R := by
  let d : Q →ₗ[R] R := (↑h.unit⁻¹ : R) • c.coord j
  have hd : d (α (LinearMap.smulRight (b.coord i) (b i)) (c k)) = 1 := h.val_inv_mul
  exact algEquiv_eq_conjugate_of_dual α (b i) (b.coord i)
    (by simp) (c k) ⟨d, hd⟩

/-- A linear map which is intertwined with a linear equivalence by every endomorphism of the source
is a unique scalar multiple of that equivalence. -/
private lemma existsUnique_scalar_of_intertwines
    {R P Q I : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [Nonempty I]
    (b : Module.Basis I R P) (T : P ≃ₗ[R] Q) (s : P →ₗ[R] Q)
    (hs : ∀ A : Module.End R P, ∃ B : Module.End R Q,
      B.comp T.toLinearMap = T.toLinearMap.comp A ∧ B.comp s = s.comp A) :
    ∃! r : R, s = r • T.toLinearMap := by
  classical
  let i : I := Classical.arbitrary I
  let C := T.symm.toLinearMap.comp s
  have hC (A : Module.End R P) : A.comp C = C.comp A := by
    obtain ⟨B, hT, hs⟩ := hs A
    ext x
    apply T.injective
    have hT' := congrArg (fun f : P →ₗ[R] Q => f (C x)) hT
    have hs' := congrArg (fun f : P →ₗ[R] Q => f x) hs
    simpa [C] using (by simpa [C] using hT'.symm : T (A (C x)) = B (s x)).trans hs'
  have hscalar : s = (b.coord i (C (b i))) • T.toLinearMap := by
    ext x
    have h := congrArg (fun f : Module.End R P => T (f (b i)))
      (hC (LinearMap.smulRight (b.coord i) x))
    simpa [C] using h.symm
  refine ⟨b.coord i (C (b i)), hscalar, ?_⟩
  intro r hr
  have h := congrArg (fun f : P →ₗ[R] Q => b.coord i (T.symm (f (b i))))
    (hr.symm.trans hscalar)
  simpa using h

/-- Coordinates transport along a map carrying one basis to another: if `ψ` is additive,
`φ`-semilinear, and sends the `i`-th member of `b` to the `i`-th member of `c`, then the `i`-th
coordinate of `ψ x` is the image under `φ` of the `i`-th coordinate of `x`. -/
private lemma basis_coord_map_of_apply {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    {I : Type u} [Finite I] (φ : R →+* S)
    (b : Module.Basis I R M) (c : Module.Basis I S N) (ψ : M →+ N)
    (hsmul : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m)
    (hb : ∀ i, ψ (b i) = c i) (x : M) (i : I) :
    c.coord i (ψ x) = φ (b.coord i x) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  simp only [Module.Basis.coord_apply]
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, hsmul, hb, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/-- A rank-one projection of a basis commutes with a map carrying that basis to another one. -/
private lemma basis_smulRight_map {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    {I : Type u} [Finite I] (φ : R →+* S)
    (b : Module.Basis I R M) (c : Module.Basis I S N) (ψ : M →+ N)
    (hsmul : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m)
    (hb : ∀ i, ψ (b i) = c i) (x : M) (i : I) :
    (LinearMap.smulRight (c.coord i) (c i)) (ψ x) =
      ψ ((LinearMap.smulRight (b.coord i) (b i)) x) := by
  simp only [LinearMap.smulRight_apply, hsmul, hb,
    basis_coord_map_of_apply φ b c ψ hsmul hb]

end Stacks.EtaleCohomology
