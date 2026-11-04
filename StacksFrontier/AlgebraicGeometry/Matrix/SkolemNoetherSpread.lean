module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra

/-!
# Skolem--Noether on a scheme: spreading a conjugation out from a stalk

Over a commutative local ring every algebra automorphism of a matrix algebra is conjugation by a
unit of that matrix algebra; this is `Stacks.Matrix.exists_units_conj_eq_of_algEquiv`. On a scheme
the ring of sections `Γ(X, U)` over an open set is not local, so an automorphism of the sheaf of
`d × d` matrices is not a conjugation. It is one *locally*: given a family of algebra
automorphisms of `Matrix (Fin d) (Fin d) Γ(X, U)`, one for each open `U` and compatible with
restriction, every point has a neighbourhood `U` on which the family is conjugation by a single
invertible matrix of sections of `𝒪_X` over `U`, compatibly with all further restriction.

## Main results

* `Stacks.AlgebraicGeometry.exists_units_conj_eq_of_algEquiv_sheaf`: the local conjugation on a
  scheme described above.
* `Stacks.AlgebraicGeometry.exists_units_conj_eq_of_isUnit_entry`: Skolem--Noether over an
  arbitrary commutative ring from a single unimodular entry -- an algebra automorphism of
  `Matrix (Fin d) (Fin d) R` is conjugation by a unit as soon as one entry of the image of one
  diagonal matrix unit `Matrix.single i i 1` is a unit of `R`.
* `Stacks.AlgebraicGeometry.exists_isUnit_entry_of_algEquiv`: such an entry always becomes
  unimodular in a local ring receiving `R`, which over a scheme is the stalk.

## Implementation notes

The automorphism of `Matrix (Fin d) (Fin d) 𝒪_{X, x}` that the family induces on the stalk is
never constructed, and no matrix over the stalk is ever lifted to a matrix of sections. Both are
avoidable because `Stacks.EtaleCohomology.exists_isUnit_coord_smulRight_coord` already takes a ring
homomorphism `φ : R →+* A` into a local ring and asks for the automorphism over `R` only: with
`φ` the germ map at `x`, it names an entry of `α ⊤ (Matrix.single i i 1)` whose germ at `x` is a
unit. Mathlib's `AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ` then shrinks the open
set until that one *section* is a unit, and over the smaller open set
`Stacks.EtaleCohomology.exists_linearEquiv_conjAlgEquiv_of_isUnit_coord` produces the conjugating
matrix outright. So the only shrinking step in the file is the one for a single section, in place
of an intersection of the `d ^ 2` opens on which the images of the matrix units would have to be
compared.

The two results quoted from
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BrauerGroupScheme/EndomorphismAlgebra.lean` require
the base ring, the module and the index type to lie in a single universe, whereas here the base ring
`Γ(X, U)` lies in `Type u` and `Fin d` in `Type 0`. The module is not lifted: `Fin d → R` is given
the basis `uliftBasisFun` indexed by `ULift.{u} (Fin d)`, so only the index type moves, which is all
those results need. `algEquivMatrix'` translates between that basis and matrices, and
`uliftBasisFun_coord_apply` together with `algEquivMatrix'_uliftBasisFun_rankOne` record the only
two translations used -- a basis coefficient is a matrix entry, and the rank-one projection attached
to a basis vector is a diagonal matrix unit.

Compatibility of the conjugation with further restriction is not a separate argument: it is the
restriction-compatibility hypothesis on the family together with the multiplicativity of
`Matrix.map` along the restriction homomorphism.

## References

The consumer of this file is Stacks Tag 0A2L. Skolem--Noether has no Stacks tag of its own, and
no tag is claimed here.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite AlgebraicGeometry Stacks.EtaleCohomology

namespace Stacks.AlgebraicGeometry

/-- The standard basis of `Fin d → R` reindexed so that its index type `ULift.{u} (Fin d)` lies
in the universe of `R`. Lifting the index type rather than the module keeps the module itself
equal to `Fin d → R`, which is what the consumers of the basis need. -/
noncomputable def uliftBasisFun (R : Type u) [CommRing R] (d : ℕ) :
    Module.Basis (ULift.{u} (Fin d)) R (Fin d → R) :=
  (Pi.basisFun R (Fin d)).reindex (Equiv.ulift.{u, 0}).symm

/-- A basis coefficient of an endomorphism of `Fin d → R` with respect to `uliftBasisFun` is the
corresponding entry of its matrix. -/
theorem uliftBasisFun_coord_apply {R : Type u} [CommRing R] {d : ℕ}
    (f : Module.End R (Fin d → R)) (j k : ULift.{u} (Fin d)) :
    (uliftBasisFun R d).coord j (f ((uliftBasisFun R d) k)) =
      algEquivMatrix' f j.down k.down := by
  simp [uliftBasisFun, Module.Basis.coord_apply, algEquivMatrix']

/-- The rank-one projection onto the `i`-th vector of `uliftBasisFun` has as its matrix the
diagonal matrix unit `Matrix.single i i 1`. -/
theorem algEquivMatrix'_uliftBasisFun_rankOne (R : Type u) [CommRing R] {d : ℕ}
    (i : Fin d) :
    algEquivMatrix' (LinearMap.smulRight ((uliftBasisFun R d).coord ⟨i⟩)
      (uliftBasisFun R d ⟨i⟩)) = Matrix.single i i (1 : R) := by
  ext a b
  simp [uliftBasisFun, Module.Basis.coord_apply, algEquivMatrix', Matrix.single, Pi.single_apply]
  split_ifs <;> tauto

/-- An algebra automorphism of a matrix algebra whose endomorphism-algebra form is conjugation by
a linear automorphism is conjugation by a unit of the matrix algebra. -/
theorem exists_units_conj_eq_of_conjAlgEquiv {R : Type u} [CommRing R] {n : Type v}
    [Fintype n] [DecidableEq n] (α : Matrix n n R ≃ₐ[R] Matrix n n R)
    {T : (n → R) ≃ₗ[R] (n → R)}
    (hT : algEquivMatrix'.trans (α.trans (algEquivMatrix' (R := R) (n := n)).symm)
      = T.conjAlgEquiv R) :
    ∃ u : (Matrix n n R)ˣ, ∀ M : Matrix n n R,
      α M = (u : Matrix n n R) * M * ((u⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) := by
  have h1 : T.toLinearMap * T.symm.toLinearMap = (1 : Module.End R (n → R)) :=
    LinearMap.ext fun y => by simp [Module.End.mul_apply]
  have h2 : T.symm.toLinearMap * T.toLinearMap = (1 : Module.End R (n → R)) :=
    LinearMap.ext fun y => by simp [Module.End.mul_apply]
  obtain ⟨u, hu1, hu2⟩ : ∃ u : (Matrix n n R)ˣ,
      (u : Matrix n n R) = algEquivMatrix' T.toLinearMap ∧
        ((u⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) = algEquivMatrix' T.symm.toLinearMap :=
    ⟨⟨_, _, by rw [← map_mul, h1, map_one], by rw [← map_mul, h2, map_one]⟩, rfl, rfl⟩
  refine ⟨u, fun M => ?_⟩
  have h := DFunLike.congr_fun hT ((algEquivMatrix' (R := R) (n := n)).symm M)
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at h
  have h' := congrArg (algEquivMatrix' (R := R) (n := n)) h
  rw [AlgEquiv.apply_symm_apply, LinearEquiv.conjAlgEquiv_apply, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp, map_mul, map_mul, AlgEquiv.apply_symm_apply] at h'
  rw [hu1, hu2, h', ← mul_assoc]

/-- A basis coefficient of the transport of `α` to `Module.End R (Fin d → R)`, applied to the
rank-one projection onto the `i`-th basis vector, is an entry of `α (single i i 1)`. -/
private theorem coord_conj_rankOne_apply {R : Type u} [CommRing R] {d : ℕ}
    (α : Matrix (Fin d) (Fin d) R ≃ₐ[R] Matrix (Fin d) (Fin d) R) (i j k : Fin d) :
    (uliftBasisFun R d).coord ⟨j⟩
      ((algEquivMatrix'.trans (α.trans (algEquivMatrix' (R := R) (n := Fin d)).symm))
        (LinearMap.smulRight ((uliftBasisFun R d).coord ⟨i⟩) (uliftBasisFun R d ⟨i⟩))
        (uliftBasisFun R d ⟨k⟩)) = α (Matrix.single i i 1) j k := by
  have key : ∀ g : Module.End R (Fin d → R),
      algEquivMatrix' ((algEquivMatrix'.trans
        (α.trans (algEquivMatrix' (R := R) (n := Fin d)).symm)) g) = α (algEquivMatrix' g) :=
    fun g => by simp [AlgEquiv.trans_apply]
  rw [uliftBasisFun_coord_apply, key, algEquivMatrix'_uliftBasisFun_rankOne]

/-- **Skolem--Noether from one unimodular entry.** An algebra automorphism of
`Matrix (Fin d) (Fin d) R`, for `R` any commutative ring, is conjugation by a unit of that matrix
algebra as soon as a single entry of the image of a single diagonal matrix unit
`Matrix.single i i 1` is a unit of `R`. -/
theorem exists_units_conj_eq_of_isUnit_entry {R : Type u} [CommRing R] {d : ℕ}
    (α : Matrix (Fin d) (Fin d) R ≃ₐ[R] Matrix (Fin d) (Fin d) R) {i j k : Fin d}
    (h : IsUnit (α (Matrix.single i i 1) j k)) :
    ∃ u : (Matrix (Fin d) (Fin d) R)ˣ, ∀ M : Matrix (Fin d) (Fin d) R,
      α M = (u : Matrix (Fin d) (Fin d) R) * M *
        ((u⁻¹ : (Matrix (Fin d) (Fin d) R)ˣ) : Matrix (Fin d) (Fin d) R) := by
  obtain ⟨T, hT⟩ := exists_linearEquiv_conjAlgEquiv_of_isUnit_coord (uliftBasisFun R d)
    (uliftBasisFun R d) (algEquivMatrix'.trans
      (α.trans (algEquivMatrix' (R := R) (n := Fin d)).symm)) ⟨i⟩ ⟨j⟩ ⟨k⟩
    (coord_conj_rankOne_apply α i j k ▸ h)
  exact exists_units_conj_eq_of_conjAlgEquiv α hT

/-- An algebra automorphism of `Matrix (Fin d) (Fin d) R` sends some diagonal matrix unit to a
matrix with an entry which is a unit in any local ring receiving `R`. Over a scheme the local ring
is a stalk and the ring homomorphism is a germ map, which is how the hypothesis of
`Stacks.AlgebraicGeometry.exists_units_conj_eq_of_isUnit_entry` is met after shrinking. -/
theorem exists_isUnit_entry_of_algEquiv {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing A]
    {d : ℕ} [NeZero d] (α : Matrix (Fin d) (Fin d) R ≃ₐ[R] Matrix (Fin d) (Fin d) R)
    (φ : R →+* A) (i : Fin d) :
    ∃ j k : Fin d, IsUnit (φ (α (Matrix.single i i 1) j k)) := by
  have : Nonempty (ULift.{u} (Fin d)) := ⟨⟨i⟩⟩
  obtain ⟨j, k, hjk⟩ := exists_isUnit_coord_smulRight_coord (uliftBasisFun R d) (uliftBasisFun R d)
    (algEquivMatrix'.trans (α.trans (algEquivMatrix' (R := R) (n := Fin d)).symm)) φ ⟨i⟩
  rw [coord_conj_rankOne_apply] at hjk
  exact ⟨j.down, k.down, hjk⟩

/-- A section of the structure sheaf of a scheme whose germ at `x` is a unit restricts to a unit
on a neighbourhood of `x`. This is Mathlib's
`AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ` with the restriction recorded as a
relation `V ≤ U` between opens of the scheme rather than as a morphism of the underlying ringed
space. -/
theorem exists_isUnit_res_of_isUnit_germ {X : Scheme.{u}} (x : X) (U : X.Opens) (hx : x ∈ U)
    (f : Γ(X, U)) (h : IsUnit ((X.presheaf.germ U x hx).hom f)) :
    ∃ (V : X.Opens) (hVU : V ≤ U) (_ : x ∈ V),
      IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  obtain ⟨V, i, hxV, hu⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ U f x hx h
  exact ⟨V, i.le, hxV, hu⟩

variable {d : ℕ} [NeZero d] {X : Scheme.{u}}
  (α : ∀ U : X.Opens, Matrix (Fin d) (Fin d) Γ(X, U) ≃ₐ[Γ(X, U)]
    Matrix (Fin d) (Fin d) Γ(X, U))
  (hα : ∀ (U V : X.Opens) (h : V ≤ U) (M : Matrix (Fin d) (Fin d) Γ(X, U)),
    α V (M.map (X.presheaf.map (homOfLE h).op).hom) =
      (α U M).map (X.presheaf.map (homOfLE h).op).hom)

include hα in
/-- **Skolem--Noether spreads from a stalk to a Zariski neighbourhood.** Let `X` be a scheme and
let `α` assign to every open set `U` of `X` an algebra automorphism of
`Matrix (Fin d) (Fin d) Γ(X, U)`, compatibly with restriction. Then every point of `X` has an
open neighbourhood `U` carrying an invertible matrix `u` of sections of `𝒪_X` over `U` such that
on `U`, and on every smaller open set, `α` is conjugation by `u`. -/
theorem exists_units_conj_eq_of_algEquiv_sheaf (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (u : (Matrix (Fin d) (Fin d) Γ(X, U))ˣ),
      ∀ (V : X.Opens) (h : V ≤ U) (M : Matrix (Fin d) (Fin d) Γ(X, U)),
        α V (M.map (X.presheaf.map (homOfLE h).op).hom) =
          (u : Matrix (Fin d) (Fin d) Γ(X, U)).map (X.presheaf.map (homOfLE h).op).hom *
            M.map (X.presheaf.map (homOfLE h).op).hom *
            ((u⁻¹ : (Matrix (Fin d) (Fin d) Γ(X, U))ˣ) :
              Matrix (Fin d) (Fin d) Γ(X, U)).map (X.presheaf.map (homOfLE h).op).hom := by
  obtain ⟨j, k, hjk⟩ :=
    exists_isUnit_entry_of_algEquiv (α ⊤) (X.presheaf.germ ⊤ x trivial).hom (0 : Fin d)
  obtain ⟨V, hVtop, hxV, hVunit⟩ := exists_isUnit_res_of_isUnit_germ x ⊤ trivial
    (α ⊤ (Matrix.single (0 : Fin d) (0 : Fin d) 1) j k) hjk
  have hsingle : (Matrix.single (0 : Fin d) (0 : Fin d) (1 : Γ(X, ⊤))).map
      (X.presheaf.map (homOfLE hVtop).op).hom
      = Matrix.single (0 : Fin d) (0 : Fin d) (1 : Γ(X, V)) := by
    rw [Matrix.map_single]; simp
  have hres := hα ⊤ V hVtop (Matrix.single (0 : Fin d) (0 : Fin d) 1)
  rw [hsingle] at hres
  have hV : IsUnit (α V (Matrix.single (0 : Fin d) (0 : Fin d) 1) j k) := by
    rw [hres]; exact hVunit
  obtain ⟨u, hu⟩ := exists_units_conj_eq_of_isUnit_entry (α V) hV
  exact ⟨V, hxV, u, fun W h M => by rw [hα V W h M, hu M, Matrix.map_mul, Matrix.map_mul]⟩

end Stacks.AlgebraicGeometry
