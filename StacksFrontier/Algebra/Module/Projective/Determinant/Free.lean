module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic

/-!
# The determinant line of a finite free module and its ordered-basis trivializations

Let `R` be a commutative ring and let `M` and `N` be finite projective `R`-modules carrying
bases `b` and `b'` indexed by `Fin n`. The two modules then have the same rank at every prime,
so every `R`-linear map `M → N` induces a map `det M → det N`, and the basis-matching
isomorphism `b i ↦ b' i` induces an isomorphism `det M ≃ det N`. Measured against that
isomorphism, the map induced by `f : M → N` is multiplication by the determinant of the matrix
of `f` in the two bases. Consequently `Hom_R(det M, det N)` is free of rank one on the
basis-matching isomorphism, and the resulting coordinate is a trivialization of it normalized by
the two ordered bases.

## Main definitions

* `ProjectiveDeterminant.basisEquiv`: the isomorphism of determinant lines induced by the
  basis-matching isomorphism of two free modules of the same finite rank.
* `ProjectiveDeterminant.homEquivOfBases`: the trivialization of `Hom_R(det M, det N)` normalized
  by two ordered bases.
* `ProjectiveDeterminant.basisHom`: `Hom_R(det M, det N)` as a free module of rank one.

## Main results

* `ProjectiveDeterminant.map_eq_det_toMatrix_smul_basisEquiv`: the determinant map induced by a
  linear map is the determinant of its matrix times the basis-matching isomorphism.
* `ProjectiveDeterminant.homEquivOfBases_map`: the normalized trivialization sends the
  determinant map induced by `f` to the determinant of the matrix of `f`.
* `ProjectiveDeterminant.coe_basisEquiv_apply`: inside the exterior algebra the basis-matching
  isomorphism of determinant lines is the induced map of exterior algebras.

## Implementation notes

The determinant line is written as `Hom_R(det M, det N)` rather than as
`det N ⊗ (det M)⁻¹`, matching `TwoTermComplex.determinantLine`. Freeness of rank one is obtained
from the invertibility of `det M`, which makes the endomorphism ring of `det M` the ground ring,
rather than from the identification of `det` with a top exterior power; this keeps the trivial
ring in scope, where the two bases have length `n` but the rank is `0`.

## References

* [Stacks Project, Section 15.120 (Tag 0FJ9)](https://stacks.math.columbia.edu/tag/0FJ9)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

namespace ProjectiveDeterminant

universe u v w

@[expose] public section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- An endomorphism of a finite projective module acts on the determinant line by its
determinant. -/
public theorem map_eq_det_smul_id (f : M →ₗ[R] M) :
    map (M := M) (N := M) (fun _ => rfl) f = det f • LinearMap.id :=
  (Classical.choose_spec (existsUnique_scalar (M := M) (map (fun _ => rfl) f))).1

/-- Inside the exterior algebra, the determinant map induced by a linear map is the induced map
of exterior algebras. -/
public theorem coe_map_apply
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (f : M →ₗ[R] N) (x : module (R := R) (M := M)) :
    (map h f x : ExteriorAlgebra R N) = ExteriorAlgebra.map f (x : ExteriorAlgebra R M) :=
  rfl

variable {n : ℕ}

/-- Finite projective modules with bases of the same finite length have the same rank at every
prime. -/
public theorem rankAtStalk_eq_of_bases (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.rankAtStalk N p :=
  rankAtStalk_congr (b.equiv b' (Equiv.refl (Fin n))) p

/-- The isomorphism of determinant lines induced by the isomorphism `b i ↦ b' i` of two finite
projective modules with bases indexed by `Fin n`. -/
public noncomputable def basisEquiv (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) :
    module (R := R) (M := M) ≃ₗ[R] module (R := R) (M := N) :=
  mapEquiv (b.equiv b' (Equiv.refl (Fin n)))

/-- Inside the exterior algebra, the basis-matching isomorphism of determinant lines is the
induced map of exterior algebras. -/
public theorem coe_basisEquiv_apply (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) (x : module (R := R) (M := M)) :
    (basisEquiv b b' x : ExteriorAlgebra R N) =
      ExteriorAlgebra.map (b.equiv b' (Equiv.refl (Fin n))).toLinearMap
        (x : ExteriorAlgebra R M) :=
  rfl

/-- The determinant map induced by a linear map is the determinant of its matrix in two ordered
bases times the basis-matching isomorphism of determinant lines. -/
public theorem map_eq_det_toMatrix_smul_basisEquiv (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) (f : M →ₗ[R] N) :
    map (rankAtStalk_eq_of_bases b b') f =
      (LinearMap.toMatrix b b' f).det • (basisEquiv b b').toLinearMap := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R (module (R := R) (M := N))
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  · set e := b.equiv b' (Equiv.refl (Fin n)) with he
    have hef : f = e.toLinearMap ∘ₗ (e.symm.toLinearMap ∘ₗ f) := by ext x; simp
    have hcomp := map_comp (M := M) (N := M) (P := N) (fun _ => rfl)
      (rankAtStalk_eq_of_bases b b') (e.symm.toLinearMap ∘ₗ f) e.toLinearMap
    have hmat : LinearMap.toMatrix b b (e.symm.toLinearMap ∘ₗ f) =
        LinearMap.toMatrix b b' f := by
      rw [LinearMap.toMatrix_comp b b' b]
      have hone : LinearMap.toMatrix b' b e.symm.toLinearMap = 1 := by
        ext i j
        rw [LinearMap.toMatrix_apply]
        simp [he, Matrix.one_apply, Finsupp.single_apply, eq_comm]
      rw [hone, Matrix.one_mul]
    conv_lhs => rw [hef]
    rw [hcomp, map_eq_det_smul_id, det_eq_linearMap_det_of_basis b,
      ← LinearMap.det_toMatrix b, hmat]
    ext x
    simp [basisEquiv, mapEquiv, he]

/-- Scalar multiples of an isomorphism of determinant lines exhaust the module of maps between
them, and are distinct. -/
public theorem toSpanSingleton_bijective
    (E : module (R := R) (M := M) ≃ₗ[R] module (R := R) (M := N)) :
    Function.Bijective (LinearMap.toSpanSingleton R
      (module (R := R) (M := M) →ₗ[R] module (R := R) (M := N)) E.toLinearMap) := by
  have := invertible (R := R) (M := M)
  have hfun : ⇑(LinearMap.toSpanSingleton R
      (module (R := R) (M := M) →ₗ[R] module (R := R) (M := N)) E.toLinearMap) =
      (LinearEquiv.arrowCongr (LinearEquiv.refl R (module (R := R) (M := M))) E) ∘
        (Module.toModuleEnd R (module (R := R) (M := M))) := by
    funext c
    ext x
    simp [LinearMap.toSpanSingleton, LinearEquiv.arrowCongr]
  rw [hfun]
  exact (LinearEquiv.arrowCongr (LinearEquiv.refl R (module (R := R) (M := M))) E).bijective.comp
    (Module.Invertible.toModuleEnd_bijective R (module (R := R) (M := M)))

/-- The trivialization of the module of maps between the determinant lines of two finite
projective modules, normalized by a pair of ordered bases indexed by `Fin n`. -/
public noncomputable def homEquivOfBases (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) :
    (module (R := R) (M := M) →ₗ[R] module (R := R) (M := N)) ≃ₗ[R] R :=
  (LinearEquiv.ofBijective _ (toSpanSingleton_bijective (basisEquiv b b'))).symm

/-- The normalized trivialization sends a scalar to that multiple of the basis-matching
isomorphism of determinant lines. -/
public theorem homEquivOfBases_symm_apply (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) (c : R) :
    (homEquivOfBases b b').symm c = c • (basisEquiv b b').toLinearMap := by
  rw [homEquivOfBases, LinearEquiv.symm_symm]
  rfl

/-- The normalized trivialization sends the determinant map induced by a linear map to the
determinant of the matrix of that map in the two ordered bases. -/
public theorem homEquivOfBases_map (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) (f : M →ₗ[R] N) :
    homEquivOfBases b b' (map (rankAtStalk_eq_of_bases b b') f) =
      (LinearMap.toMatrix b b' f).det :=
  (LinearEquiv.eq_symm_apply (homEquivOfBases b b')).mp <| by
    rw [homEquivOfBases_symm_apply, map_eq_det_toMatrix_smul_basisEquiv]

/-- The module of maps between the determinant lines of two finite projective modules with bases
indexed by `Fin n` is free of rank one on the basis-matching isomorphism. -/
public noncomputable def basisHom (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) :
    Module.Basis (Fin 1) R (module (R := R) (M := M) →ₗ[R] module (R := R) (M := N)) :=
  (Module.Basis.singleton (Fin 1) R).map (homEquivOfBases b b').symm

/-- The rank-one basis of the module of maps between two determinant lines is the basis-matching
isomorphism. -/
public theorem basisHom_apply (b : Module.Basis (Fin n) R M)
    (b' : Module.Basis (Fin n) R N) (i : Fin 1) :
    basisHom b b' i = (basisEquiv b b').toLinearMap := by
  rw [basisHom, Module.Basis.map_apply, Module.Basis.singleton_apply,
    homEquivOfBases_symm_apply, one_smul]

end

end ProjectiveDeterminant
