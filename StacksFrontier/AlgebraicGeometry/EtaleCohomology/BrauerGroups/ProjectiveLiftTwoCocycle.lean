module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology

/-!
# The two-cocycle attached to a lift of a projective cocycle

Let a group `G` act on a field `K` by ring automorphisms and let `g : G → PGL_n(K)` be a crossed
homomorphism. Choosing for each `σ` a lift `g̃_σ ∈ GL_n(K)` of `g_σ` breaks the crossed
homomorphism identity by a scalar, and the resulting defect

`(σ, τ) ↦ g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹) ∈ Kˣ`

is a multiplicative two-cocycle. That is what this file constructs and proves.

For `K = Kˢᵉᵖ` and `G = Gal(Kˢᵉᵖ/K)` the projective cocycle of a central simple algebra is the
one classifying it, so this is the cocycle representing the image of a Brauer class under the
connecting map of the central extension
`1 → (Kˢᵉᵖ)ˣ → GL_n(Kˢᵉᵖ) → PGL_n(Kˢᵉᵖ) → 1`.

## Main definitions

* `Stacks.GaloisCohomology.centerScalar`: the scalar of a central element of `GL n R`.
* `Stacks.GaloisCohomology.liftDefect`: the element `g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹)` of `GL n K`.
* `Stacks.GaloisCohomology.twoCocycleOfLift`: that element read as a scalar in `Kˣ`.
* `Stacks.GaloisCohomology.twoCocycleOfPGLCocycle`: the same scalar for a lift of a continuous
  projective cocycle of the absolute Galois group.

## Main results

* `Stacks.GaloisCohomology.scalar_twoCocycleOfLift` is the displayed formula: the scalar matrix
  of `twoCocycleOfLift` is `g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹)`.
* `Stacks.GaloisCohomology.twoCocycleOfLift_mul` and
  `Stacks.GaloisCohomology.isMulCocycle₂_twoCocycleOfLift` are the two-cocycle identity, first
  with the action written as `Units.map`, then as Mathlib's `IsMulCocycle₂`.
* `Stacks.GaloisCohomology.isMulCocycle₂_twoCocycleOfPGLCocycle` is the Galois case, stated for
  the action of `Gal(Kˢᵉᵖ/K)` on `(Kˢᵉᵖ)ˣ` used by the crossed product construction.

## Implementation notes

The defect is a scalar matrix because it becomes trivial in `PGL_n(K)`, and the centre of
`GL_n(K)` is exactly the group of scalar matrices. The scalar is therefore read off a diagonal
entry, which makes the two-cocycle an explicit function of the lift instead of an unspecified
solution of `scalar u = g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹)`. Which diagonal entry is used is immaterial, by
`centerScalar_eq` — the index is an argument rather than a choice, so no nonemptiness hypothesis
on the index type is needed and in the Galois case the index is `0`.

The group acting is given by a `MulSemiringAction`, whose induced ring homomorphisms are written
`MulSemiringAction.toRingHom`, transported to matrices by `Matrix.GeneralLinearGroup.map` and to
`PGL_n` by `Matrix.ProjGenLinGroup.map`. On `Kˣ` the action is `Units.map`; for the absolute
Galois group that is Mathlib's instance on units of a field, so the cocycles produced here are
cocycles in the sense used by `Stacks.GaloisCohomology.CrossedProduct`.

## References

* [Stacks Project, Tag 0A2I](https://stacks.math.columbia.edu/tag/0A2I)
* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7)
-/

@[expose] public section

open scoped MatrixGroups

open groupCohomology

namespace Stacks.GaloisCohomology

section Center

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Distinct units give distinct scalar matrices, as soon as the index type has an element. -/
theorem scalar_injective (i : n) :
    Function.Injective (Matrix.GeneralLinearGroup.scalar n : Rˣ → GL n R) := by
  intro a b h
  apply Units.ext
  simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using
    congrArg (fun M : GL n R => (M : Matrix n n R) i i) h

/-- The scalar of a central element of `GL n R`: the centre consists of the scalar matrices, so
the `i`-th diagonal entry of `M` is a unit, independent of `i`, whose scalar matrix is `M`. -/
def centerScalar (i : n) (M : GL n R) (hM : M ∈ Subgroup.center (GL n R)) : Rˣ where
  val := (M : Matrix n n R) i i
  inv := ((M⁻¹ : GL n R) : Matrix n n R) i i
  val_inv := by
    obtain ⟨u, rfl⟩ := Matrix.GeneralLinearGroup.center_eq_range_scalar.le hM
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq, ← map_inv]
  inv_val := by
    obtain ⟨u, rfl⟩ := Matrix.GeneralLinearGroup.center_eq_range_scalar.le hM
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq, ← map_inv]

/-- The scalar matrix of `centerScalar i M hM` is `M` itself. -/
@[simp]
theorem scalar_centerScalar (i : n) (M : GL n R) (hM : M ∈ Subgroup.center (GL n R)) :
    Matrix.GeneralLinearGroup.scalar n (centerScalar i M hM) = M := by
  obtain ⟨u, hu⟩ := Matrix.GeneralLinearGroup.center_eq_range_scalar.le hM
  have hval : centerScalar i M hM = u := by
    apply Units.ext
    change (M : Matrix n n R) i i = (u : R)
    rw [← hu]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  rw [hval, hu]

/-- The scalar of a central element does not depend on the diagonal entry it is read from. -/
theorem centerScalar_eq (i j : n) (M : GL n R) (hM : M ∈ Subgroup.center (GL n R)) :
    centerScalar i M hM = centerScalar j M hM :=
  scalar_injective i (by rw [scalar_centerScalar, scalar_centerScalar])

end Center

section Defect

variable {G : Type*} [Group G] {K : Type*} [Field K] [MulSemiringAction G K]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The defect `g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹)` of a family `g̃` of elements of `GL n K`, measuring how
far `g̃` is from being a crossed homomorphism. -/
def liftDefect (lift : G → GL n K) (σ τ : G) : GL n K :=
  (lift σ)⁻¹ * lift (σ * τ) *
    Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K σ) (lift τ)⁻¹

/-- A lift of a projective crossed homomorphism has central defect: the defect becomes trivial
in `PGL n K`, whose kernel is the centre of `GL n K`. -/
theorem liftDefect_mem_center (g : G → PGL(n, K))
    (hg : ∀ σ τ, g (σ * τ) =
      g σ * Matrix.ProjGenLinGroup.map (MulSemiringAction.toRingHom G K σ) (g τ))
    (lift : G → GL n K) (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = g σ) (σ τ : G) :
    liftDefect lift σ τ ∈ Subgroup.center (GL n K) := by
  rw [← Matrix.ProjGenLinGroup.mk_eq_one]
  have h : Matrix.ProjGenLinGroup.mk (liftDefect lift σ τ) =
      (g σ)⁻¹ * g (σ * τ) *
        (Matrix.ProjGenLinGroup.map (MulSemiringAction.toRingHom G K σ) (g τ))⁻¹ := by
    simp only [liftDefect, map_mul, map_inv, ← Matrix.ProjGenLinGroup.map_mk, hlift]
  rw [h, hg σ τ]
  group

/-- **Equation 59.61.5.1.** The two-cocycle attached to a family of lifts with central defect:
the scalar `g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹) ∈ Kˣ`. -/
@[stacks 0A2I "the two-cocycle"]
def twoCocycleOfLift (i : n) (lift : G → GL n K)
    (hc : ∀ σ τ, liftDefect lift σ τ ∈ Subgroup.center (GL n K)) : G × G → Kˣ :=
  fun στ => centerScalar i (liftDefect lift στ.1 στ.2) (hc στ.1 στ.2)

/-- **Equation 59.61.5.1**, as displayed: the scalar matrix of the two-cocycle at `(σ, τ)` is
`g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹)`. -/
@[stacks 0A2I "the displayed formula"]
theorem scalar_twoCocycleOfLift (i : n) (lift : G → GL n K)
    (hc : ∀ σ τ, liftDefect lift σ τ ∈ Subgroup.center (GL n K)) (σ τ : G) :
    Matrix.GeneralLinearGroup.scalar n (twoCocycleOfLift i lift hc (σ, τ)) =
      (lift σ)⁻¹ * lift (σ * τ) *
        Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K σ) (lift τ)⁻¹ :=
  scalar_centerScalar i _ (hc σ τ)

/-- The two-cocycle is central as a scalar matrix, which is what makes the lifts commute with it
in the computation of the cocycle identity. -/
theorem scalar_twoCocycleOfLift_mem_center (i : n) (lift : G → GL n K)
    (hc : ∀ σ τ, liftDefect lift σ τ ∈ Subgroup.center (GL n K)) (σ τ : G) :
    Matrix.GeneralLinearGroup.scalar n (twoCocycleOfLift i lift hc (σ, τ)) ∈
      Subgroup.center (GL n K) := by
  rw [scalar_twoCocycleOfLift]
  exact hc σ τ

/-- The two-cocycle commutes with everything, as a scalar matrix. -/
private theorem scalar_twoCocycleOfLift_comm (i : n) (lift : G → GL n K)
    (hc : ∀ σ τ, liftDefect lift σ τ ∈ Subgroup.center (GL n K)) (σ τ : G) (x : GL n K) :
    x * Matrix.GeneralLinearGroup.scalar n (twoCocycleOfLift i lift hc (σ, τ)) =
      Matrix.GeneralLinearGroup.scalar n (twoCocycleOfLift i lift hc (σ, τ)) * x :=
  Subgroup.mem_center_iff.mp (scalar_twoCocycleOfLift_mem_center i lift hc σ τ) x

/-- The multiplication rule for the lifts: `g̃_{σ τ} = g̃_σ σ(g̃_τ) c(σ, τ)`, with the scalar on
the right because it is central. -/
theorem lift_mul_eq (i : n) (lift : G → GL n K)
    (hc : ∀ σ τ, liftDefect lift σ τ ∈ Subgroup.center (GL n K)) (σ τ : G) :
    lift (σ * τ) = lift σ *
      Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K σ) (lift τ) *
      Matrix.GeneralLinearGroup.scalar n (twoCocycleOfLift i lift hc (σ, τ)) := by
  rw [mul_assoc, scalar_twoCocycleOfLift_comm, ← mul_assoc, scalar_twoCocycleOfLift]
  simp only [Matrix.GeneralLinearGroup.map_inv]
  group

/-- Acting by `σ τ` on matrices is acting by `τ` and then by `σ`. -/
theorem map_toRingHom_mul (σ τ : G) (x : GL n K) :
    Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K (σ * τ)) x =
      Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K σ)
        (Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K τ) x) := by
  have hcomp : MulSemiringAction.toRingHom G K (σ * τ) =
      (MulSemiringAction.toRingHom G K σ).comp (MulSemiringAction.toRingHom G K τ) :=
    RingHom.ext fun a => mul_smul σ τ a
  rw [hcomp, Matrix.GeneralLinearGroup.map_comp]
  rfl

/-- **Stacks Project, Tag 0A2I.** The scalar defect of a lift of a projective crossed
homomorphism satisfies the multiplicative two-cocycle identity
`c(σ τ, υ) c(σ, τ) = σ(c(τ, υ)) c(σ, τ υ)`. -/
@[stacks 0A2I "the two-cocycle identity"]
theorem twoCocycleOfLift_mul (i : n) (lift : G → GL n K)
    (hc : ∀ σ τ, liftDefect lift σ τ ∈ Subgroup.center (GL n K)) (σ τ υ : G) :
    twoCocycleOfLift i lift hc (σ * τ, υ) * twoCocycleOfLift i lift hc (σ, τ) =
      Units.map (MulSemiringAction.toRingHom G K σ : K →* K)
          (twoCocycleOfLift i lift hc (τ, υ)) *
        twoCocycleOfLift i lift hc (σ, τ * υ) := by
  set c := twoCocycleOfLift i lift hc with hcdef
  set S := (Matrix.GeneralLinearGroup.scalar n : Kˣ →* GL n K) with hSdef
  set A := lift σ with hA
  set B := Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K σ) (lift τ) with hB
  set C := Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G K (σ * τ)) (lift υ)
    with hC
  have hx : C * S (c (σ, τ)) = S (c (σ, τ)) * C := scalar_twoCocycleOfLift_comm i lift hc σ τ C
  -- the two ways of expanding `lift ((σ * τ) * υ) = lift (σ * (τ * υ))`
  have hleft : lift (σ * τ * υ) = A * B * C * S (c (σ, τ)) * S (c (σ * τ, υ)) := by
    rw [lift_mul_eq i lift hc (σ * τ) υ, lift_mul_eq i lift hc σ τ]
    calc
      A * B * S (c (σ, τ)) * C * S (c (σ * τ, υ))
          = A * B * (S (c (σ, τ)) * C) * S (c (σ * τ, υ)) := by group
      _ = A * B * (C * S (c (σ, τ))) * S (c (σ * τ, υ)) := by rw [← hx]
      _ = A * B * C * S (c (σ, τ)) * S (c (σ * τ, υ)) := by group
  have hright : lift (σ * (τ * υ)) = A * B * C *
      S (Units.map (MulSemiringAction.toRingHom G K σ : K →* K) (c (τ, υ))) *
      S (c (σ, τ * υ)) := by
    rw [lift_mul_eq i lift hc σ (τ * υ), lift_mul_eq i lift hc τ υ]
    simp only [Matrix.GeneralLinearGroup.map_mul]
    rw [← map_toRingHom_mul σ τ (lift υ), Matrix.GeneralLinearGroup.map_scalar]
    simp only [hA, hB, hC, hSdef, hcdef, mul_assoc]
  have hprod : A * B * C * (S (c (σ, τ)) * S (c (σ * τ, υ))) =
      A * B * C * (S (Units.map (MulSemiringAction.toRingHom G K σ : K →* K) (c (τ, υ))) *
        S (c (σ, τ * υ))) := by
    calc
      A * B * C * (S (c (σ, τ)) * S (c (σ * τ, υ)))
          = A * B * C * S (c (σ, τ)) * S (c (σ * τ, υ)) := by group
      _ = lift (σ * τ * υ) := hleft.symm
      _ = lift (σ * (τ * υ)) := by rw [mul_assoc]
      _ = A * B * C * S (Units.map (MulSemiringAction.toRingHom G K σ : K →* K) (c (τ, υ))) *
            S (c (σ, τ * υ)) := hright
      _ = _ := by group
  apply scalar_injective i
  rw [map_mul, map_mul]
  calc
    S (c (σ * τ, υ)) * S (c (σ, τ)) = S (c (σ, τ)) * S (c (σ * τ, υ)) :=
      (scalar_twoCocycleOfLift_comm i lift hc (σ * τ) υ _).symm
    _ = _ := mul_left_cancel hprod

section IsMulCocycle

attribute [local instance] Units.mulDistribMulActionRight

/-- **Stacks Project, Tag 0A2I**, in the form of Mathlib's multiplicative two-cocycle condition
for the action of `G` on `Kˣ`. -/
theorem isMulCocycle₂_twoCocycleOfLift (i : n) (lift : G → GL n K)
    (hc : ∀ σ τ, liftDefect lift σ τ ∈ Subgroup.center (GL n K)) :
    IsMulCocycle₂ (twoCocycleOfLift i lift hc) :=
  fun σ τ υ => twoCocycleOfLift_mul i lift hc σ τ υ

end IsMulCocycle

end Defect

section Galois

variable {K : Type*} [Field K] {Ksep : Type*} [Field Ksep] [Algebra K Ksep] {d : ℕ}

/-- The defect of a lift of a continuous projective cocycle of the absolute Galois group is
central. -/
theorem pglCocycle_liftDefect_mem_center (g : PGLCocycle K Ksep d)
    (lift : (Ksep ≃ₐ[K] Ksep) → GL (Fin d) Ksep)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = g.toFun σ) (σ τ : Ksep ≃ₐ[K] Ksep) :
    liftDefect lift σ τ ∈ Subgroup.center (GL (Fin d) Ksep) :=
  liftDefect_mem_center g.toFun g.map_mul lift hlift σ τ

/-- **Equation 59.61.5.1** for the absolute Galois group: the scalar two-cocycle
`(σ, τ) ↦ g̃_σ⁻¹ g̃_{σ τ} σ(g̃_τ⁻¹)` attached to a lift of the projective cocycle classifying a
central simple algebra of degree `d`. -/
@[stacks 0A2I "the Galois two-cocycle"]
def twoCocycleOfPGLCocycle (hd : 0 < d) (g : PGLCocycle K Ksep d)
    (lift : (Ksep ≃ₐ[K] Ksep) → GL (Fin d) Ksep)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = g.toFun σ) :
    (Ksep ≃ₐ[K] Ksep) × (Ksep ≃ₐ[K] Ksep) → Ksepˣ :=
  twoCocycleOfLift ⟨0, hd⟩ lift (pglCocycle_liftDefect_mem_center g lift hlift)

/-- The displayed formula for the Galois two-cocycle. -/
theorem scalar_twoCocycleOfPGLCocycle (hd : 0 < d) (g : PGLCocycle K Ksep d)
    (lift : (Ksep ≃ₐ[K] Ksep) → GL (Fin d) Ksep)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = g.toFun σ)
    (σ τ : Ksep ≃ₐ[K] Ksep) :
    Matrix.GeneralLinearGroup.scalar (Fin d) (twoCocycleOfPGLCocycle hd g lift hlift (σ, τ)) =
      (lift σ)⁻¹ * lift (σ * τ) *
        Matrix.GeneralLinearGroup.map
          (MulSemiringAction.toRingHom (Ksep ≃ₐ[K] Ksep) Ksep σ) (lift τ)⁻¹ :=
  scalar_twoCocycleOfLift _ lift _ σ τ

/-- **Stacks Project, Tag 0A2I.** The scalar defect of a lift of the projective cocycle of a
central simple algebra is a two-cocycle of the absolute Galois group with values in `(Kˢᵉᵖ)ˣ`,
for the action of `Gal(Kˢᵉᵖ/K)` on units used by the crossed product construction. -/
@[stacks 0A2I "the Galois two-cocycle identity"]
theorem isMulCocycle₂_twoCocycleOfPGLCocycle (hd : 0 < d) (g : PGLCocycle K Ksep d)
    (lift : (Ksep ≃ₐ[K] Ksep) → GL (Fin d) Ksep)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = g.toFun σ) :
    IsMulCocycle₂ (twoCocycleOfPGLCocycle hd g lift hlift) :=
  fun σ τ υ => twoCocycleOfLift_mul _ lift _ σ τ υ

end Galois

end Stacks.GaloisCohomology
