module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GlobalFunctionGerm
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.InertSlotTwist
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionParametrisation
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionSource

/-!
# The linear system of the classifying morphism of Tag 0B1S

The incidence correspondence of Tag 0B1S is to be exhibited as the image of the source
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSource`, which carries the two points of
`X` and `Y` and the parameters `(c, u, u', w, h)` of the bilinear parametrisation
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd`, under the morphism to
`𝐏 = 𝐏((End V)ᵛ)` sending a point of the source to the parameter point of the endomorphism
`G = transitionEnd f f' c u u' w h`. This file assembles the **linear system** of that morphism:
the `k`-linear map

`ψ : (End V)ᵛ → Γ(𝒪(1,1), ⊤)`, `φ ↦ ∑ p, ∑ q, P_φ(p, q) · (bₚ ⊗ b_q)`,

whose coefficients `P_φ(p, q)` are global *functions* on the source and whose basis sections are
the tensors of tautological sections
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautGlobal`. Feeding `ψ` to
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections` is what
produces the classifying morphism.

The shape of `ψ` is forced by two already-proved expansions. By
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_eq_sum_basis` each coordinate of
the parametrisation is `∑ p, ∑ q, f (bₚ) · f' (b_q) · φ(G(εₚ, ε_q))`, and the products
`f (bₚ) · f' (b_q)` are the values of `pairTautGlobal bₚ b_q`; by
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_coord_eq_cubic` the remaining
coefficient `φ(G(εₚ, ε_q))` is a cubic in the coordinates of `(c, u, u', w, h)` whose own
coefficients are the constants `φ(E i t)`. Substituting the coordinate functions
`AlgebraicGeometry.AffineSpace.coord` of the affine parameter factor into that cubic turns it into
a global function on the source, and that function is the coefficient `P_φ(p, q)`.

## Implementation notes

**Why the cubic cannot be avoided.** `AlgebraicGeometry.AffineSpace.coord` indexes the parameters
by *coordinates*, while `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd` takes honest
elements of `k`, `V` and `End V`. There is therefore no way to substitute coordinate functions
into the compact formula for `G`: the expansion into coordinates has to happen on the `k` side
first, which is what the cubic is, and only then may each coordinate be replaced by its
coordinate function. The one-line summary — the cubic shape itself — is isolated as
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCubic`, a polynomial over an arbitrary
commutative ring, so that the substitution is the single lemma
`AlgebraicGeometry.ProjectiveSpaceOfModule.map_transitionCubic` and nothing is expanded twice.

**The two `k`-actions agree.** The `k`-module structure on `Γ(𝒪(1,1), ⊤)` is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule`, restriction of
scalars along `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom`, and that
ring map is the *same term* as `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarTop` at the
structure morphism `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSourceToSpec`; the
agreement is
`AlgebraicGeometry.ProjectiveSpaceOfModule.baseRingHom_transitionSource_eq_scalarTop`, by `rfl`.
This is worth recording because affine space carries a second `OverClass` instance, over
`AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosed` rather than over `Spec k`, so `↘ Spec k`
could silently have meant the composite of that one with the base's structure morphism; it does
not, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSource_over_eq_transitionSourceToSpec`
records it.

Coefficients are therefore written with `baseRingHom` rather than with `scalarTop`: the two have
the same value, but `scalarTop` is stated in the `RingCat` spelling
`T.ringCatSheaf.obj.obj (op ⊤)`, whose head is not `Γ(T, ⊤)`, so arithmetic instances are not
found on it even though its carrier is the same type.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCubic`: the cubic shape of the
  coefficient, over an arbitrary commutative ring.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.tsParamC`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tsParamU`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tsParamU'`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tsParamW` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tsParamH`: the coordinate functions of the five
  parameter slots, as global functions on the source.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCoeff`: the coefficient `P_φ(p, q)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSections`: the linear system `ψ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionParamCoords`: the coordinates of a value
  of the parameters, arranged along the index type of the affine factor.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSourcePoint`: the `k`-point of the source
  carrying a given point of `X × Y` and a given value of the parameters.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.map_transitionCubic`: a ring map carries the cubic
  to the cubic of the carried data. This is what substitutes coordinate functions for
  coordinates, and what evaluates the result at a point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_coord_eq_transitionCubic`:
  the already-proved cubic expansion, folded into
  `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCubic`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSections_apply`: the value of the linear
  system, which is the double sum above.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.appTop_transitionCoeff`: **the value of a
  coefficient at a `k`-point of the source is the coefficient of the parametrisation at the data
  that point carries.** Both sides are the cubic, reached from opposite ends by
  `AlgebraicGeometry.ProjectiveSpaceOfModule.map_transitionCubic`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.ringGerm_transitionCoeff_sub_scalarTop_mem`:
  that value read as a germ, which is the hypothesis `hP` of
  `AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_sum_smul_sub_smul_mem` — the step that lets
  the germ calculus, whose coefficients are constants, be applied to the linear system, whose
  coefficients are global functions.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_transitionSections_sub_sum_smul_mem`: **the
  germ of the linear system**, modulo `𝔪ₜ · 𝒪(1,1)ₜ`, as the combination of the germs of the
  basis tensors with those values as coefficients. This is the form
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pairGerm_sum_sub_smul_mem` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_pair_iff_of_germ_sub_smul_mem`
  consume.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_transitionSections_sub_smul_mem`: that germ
  against the reference tensor, which is the hypothesis of the vanishing criterion.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.sum_transitionEnd_coord_mul_eq`: the total of the
  coefficients against a pair of functionals is the coordinate of the parametrisation at that
  pair — the bilinearity of the parametrisation, read off its expansion in the basis.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingOpen_transitionSections_iff`:
  **the nonvanishing criterion.** `ψ(φ)` is nonvanishing at `t` exactly when that total is
  nonzero, so — by the previous item — exactly where `φ` does not kill the endomorphism the
  parametrisation produces at `t`. This is what makes the nonvanishing opens of the `ψ(φ)` cover
  the locus on which the classifying morphism of Tag 0B1S is defined.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingOpen_transitionSections_point_iff`:
  **that criterion at a `k`-point of the source, in closed form**: at the point carrying the pair
  of `k`-points `(f, f')` and the parameters `(c, u, u', w, h)`, the section `ψ(φ)` is
  nonvanishing exactly when `φ(G(f, f')) ≠ 0`. This is the geometric content of the whole
  construction, and it exhibits the locus the classifying morphism is defined on as the locus
  where the parametrisation is nonzero — not all of the source, `G` vanishing at `c = 0, w = 0`.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (baseRingHom globalSectionsModule)
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-! ### The cubic shape of the coefficient -/

section Cubic

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

/-- **The cubic shape of the coefficient of the parametrisation.** Over any commutative ring, for
a scalar `c`, three families `u, u', w`, a matrix `h` and a matrix `E` of coefficients,

`transitionCubic c u u' w h E p q`
`  = c · u_p · ∑ⱼ u'ⱼ · E_{q j}`
`  + w_q · (u_p · ∑ᵢ ∑ₜ h_{it} · E_{t i} − ∑ᵢ uᵢ · ∑ₜ h_{pt} · E_{t i})`.

This is exactly the right-hand side of
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_coord_eq_cubic` with the
coordinates of the parameters abstracted. Writing it once over an arbitrary ring is what lets the
same expression be read in `k` (where it is a value of the parametrisation), in the global
functions of the source (where it is the coefficient of the linear system) and in the global
functions of a point (where it is the evaluation of that coefficient), with the passage between
them the single lemma `AlgebraicGeometry.ProjectiveSpaceOfModule.map_transitionCubic`. -/
public def transitionCubic (c : R) (u u' w : n → R) (h E : n → n → R) (p q : n) : R :=
  c * u p * ∑ j, u' j * E q j +
    w q * ((u p * ∑ i, ∑ t, h i t * E t i) - ∑ i, u i * ∑ t, h p t * E t i)

/-- **A ring map carries the cubic to the cubic of the carried data.** Used three times: to
substitute the coordinate functions of the affine parameter factor for the coordinates of the
parameters, to evaluate the resulting global function at a point of the source, and to move the
value across the identification of the global functions of `Spec k` with `k`. -/
public theorem map_transitionCubic {R' : Type*} [CommRing R'] (F : R →+* R') (c : R)
    (u u' w : n → R) (h E : n → n → R) (p q : n) :
    F (transitionCubic c u u' w h E p q) =
      transitionCubic (F c) (fun i => F (u i)) (fun j => F (u' j)) (fun i => F (w i))
        (fun i t => F (h i t)) (fun t i => F (E t i)) p q := by
  simp only [transitionCubic]
  simp only [_root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_sum]

/-- **The cubic is additive in its coefficient matrix.** Each monomial contains exactly one
entry of `E`, so the whole expression is linear in it; this is the additivity in `φ` of the
coefficient of the linear system. -/
public theorem transitionCubic_add_coeff (c : R) (u u' w : n → R) (h E₁ E₂ : n → n → R)
    (p q : n) :
    transitionCubic c u u' w h (fun t i => E₁ t i + E₂ t i) p q =
      transitionCubic c u u' w h E₁ p q + transitionCubic c u u' w h E₂ p q := by
  simp only [transitionCubic, mul_add, Finset.sum_add_distrib]
  ring

/-- **The cubic is homogeneous in its coefficient matrix.** This is the homogeneity in `φ` of the
coefficient of the linear system. -/
public theorem transitionCubic_smul_coeff (c : R) (u u' w : n → R) (h E : n → n → R) (r : R)
    (p q : n) :
    transitionCubic c u u' w h (fun t i => r * E t i) p q =
      r * transitionCubic c u u' w h E p q := by
  have hsum : ∀ v W : n → R, ∑ j, v j * (r * W j) = r * ∑ j, v j * W j := fun v W => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h₁ : ∑ j, u' j * (r * E q j) = r * ∑ j, u' j * E q j := hsum u' fun j => E q j
  have h₂ : ∑ i, ∑ t, h i t * (r * E t i) = r * ∑ i, ∑ t, h i t * E t i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hsum (h i) fun t => E t i
  have h₃ : ∑ i, u i * ∑ t, h p t * (r * E t i) = r * ∑ i, u i * ∑ t, h p t * E t i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum (h p) fun t => E t i]
    ring
  simp only [transitionCubic]
  rw [h₁, h₂, h₃]
  ring

end Cubic

/-! ### The cubic expansion of the parametrisation, folded -/

section Expansion

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The cubic expansion of a coordinate of the parametrisation**, with the right-hand side
folded into `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCubic`. The coefficient matrix
is `E_{t i} = φ(LinearMap.smulRight εₜ bᵢ)`, the value of `φ` on the elementary endomorphism
carrying `b t` to `b i`. -/
public theorem apply_transitionEnd_coord_eq_transitionCubic {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k V) (φ : Module.Dual k (V →ₗ[k] V)) (p q : ι) (c : k) (u u' w : V)
    (h : V →ₗ[k] V) :
    φ (transitionEnd k V (b.coord p) (b.coord q) c u u' w h) =
      transitionCubic c (fun i => b.coord i u) (fun j => b.coord j u')
        (fun i => b.coord i w) (fun i t => b.coord i (h (b t)))
        (fun t i => φ (LinearMap.smulRight (b.coord t) (b i))) p q :=
  apply_transitionEnd_coord_eq_cubic k V b φ p q c u u' w h

end Expansion

/-! ### The coordinate functions of the parameters -/

section Coordinates

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)

/-- **The scalar parameter `c`**, as a global function on the source. -/
public abbrev tsParamC : Γ(transitionSource k V X Y hXc hYc, ⊤) :=
  AffineSpace.coord (prodOfClosed k V X Y hXc hYc) (ULift.up (Sum.inl ()))

/-- **The `i`-th coordinate of the vector parameter `u`**, as a global function on the source. -/
public abbrev tsParamU (i : Fin (Module.finrank k V)) :
    Γ(transitionSource k V X Y hXc hYc, ⊤) :=
  AffineSpace.coord (prodOfClosed k V X Y hXc hYc) (ULift.up (Sum.inr (Sum.inl i)))

/-- **The `j`-th coordinate of the vector parameter `u'`**, as a global function on the
source. -/
public abbrev tsParamU' (j : Fin (Module.finrank k V)) :
    Γ(transitionSource k V X Y hXc hYc, ⊤) :=
  AffineSpace.coord (prodOfClosed k V X Y hXc hYc) (ULift.up (Sum.inr (Sum.inr (Sum.inl j))))

/-- **The `i`-th coordinate of the vector parameter `w`**, as a global function on the source. -/
public abbrev tsParamW (i : Fin (Module.finrank k V)) :
    Γ(transitionSource k V X Y hXc hYc, ⊤) :=
  AffineSpace.coord (prodOfClosed k V X Y hXc hYc)
    (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))

/-- **The `(i, t)` entry of the endomorphism parameter `h`**, as a global function on the
source. -/
public abbrev tsParamH (i t : Fin (Module.finrank k V)) :
    Γ(transitionSource k V X Y hXc hYc, ⊤) :=
  AffineSpace.coord (prodOfClosed k V X Y hXc hYc)
    (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, t))))))

/-- **`↘ Spec k` on the source is the structure morphism it was given**, not the composite of
affine space's canonical morphism to `X × Y` with the base's structure morphism. Affine space
carries `CategoryTheory.CanonicallyOverClass` over its base, and `CategoryTheory.OverClass` has a
transitivity instance, so the two readings are both available to instance search; the explicit
`AlgebraicGeometry.ProjectiveSpaceOfModule.over_transitionSource` has the higher priority and
wins. Recorded because everything stated with `↘ Spec k` below — in particular the `k`-action on
global sections — would otherwise silently mean the other morphism. -/
public theorem transitionSource_over_eq_transitionSourceToSpec :
    (transitionSource k V X Y hXc hYc) ↘ Spec (CommRingCat.of k) =
      transitionSourceToSpec k V X Y hXc hYc := rfl

/-- **The base ring map of the source is the constant-function map of its structure morphism.**
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom`, through which `k` acts
on global sections of any module on the source, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.scalarTop`, through which the tautological germ
calculus reads constants, are the same term. The two are stated in different spellings of the
ring of global functions — `Γ(T, ⊤)` in `CommRingCat` against `T.ringCatSheaf.obj.obj (op ⊤)` in
`RingCat` — whose carriers coincide; coefficients below are written with `baseRingHom`, because
arithmetic instances are found only on that spelling. -/
public theorem baseRingHom_transitionSource_eq_scalarTop (r : k) :
    baseRingHom k (transitionSource k V X Y hXc hYc) r =
      scalarTop k (transitionSourceToSpec k V X Y hXc hYc) r := rfl

end Coordinates

/-! ### The coefficients and the linear system -/

section Sections

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)
  (b : Module.Basis (Fin (Module.finrank k V)) k V)

attribute [local instance] isInvertible_tautologicalModule globalSectionsModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The invertible module `𝒪(1,1)` on the source** of the parametrisation, for the two
projections to `𝐏(V)`. -/
public abbrev transitionPairTaut : (transitionSource k V X Y hXc hYc).Modules :=
  pairTaut k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
    (transitionSourceToSpec k V X Y hXc hYc)

/-- **The tensor `bₚ ⊗ b_q` of two tautological sections on the source**, a global section of
`𝒪(1,1)` and the basis of the linear system. -/
public abbrev transitionPairGlobal (p q : Fin (Module.finrank k V)) :
    Γ(transitionPairTaut k V X Y hXc hYc, ⊤) :=
  pairTautGlobal k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
    (transitionSourceToSpec k V X Y hXc hYc) (b p) (b q)

/-- **The coefficient `P_φ(p, q)` of the linear system**: the cubic
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCubic` with the coordinate functions of the
affine parameter factor in place of the coordinates of the parameters, and the constants
`φ(E_{t i})` in place of the coefficient matrix. By
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_coord_eq_transitionCubic` its
value at a point of the source is `φ(G(εₚ, ε_q))` for the parameters that point carries. -/
public def transitionCoeff (φ : Module.Dual k (V →ₗ[k] V))
    (p q : Fin (Module.finrank k V)) : Γ(transitionSource k V X Y hXc hYc, ⊤) :=
  transitionCubic (tsParamC k V X Y hXc hYc) (tsParamU k V X Y hXc hYc)
    (tsParamU' k V X Y hXc hYc) (tsParamW k V X Y hXc hYc) (tsParamH k V X Y hXc hYc)
    (fun t i => baseRingHom k (transitionSource k V X Y hXc hYc)
      (φ (LinearMap.smulRight (b.coord t) (b i)))) p q

/-- **The coefficient is additive in the functional.** -/
public theorem transitionCoeff_add (φ φ' : Module.Dual k (V →ₗ[k] V))
    (p q : Fin (Module.finrank k V)) :
    transitionCoeff k V X Y hXc hYc b (φ + φ') p q =
      transitionCoeff k V X Y hXc hYc b φ p q + transitionCoeff k V X Y hXc hYc b φ' p q := by
  simp only [transitionCoeff, LinearMap.add_apply, _root_.map_add]
  exact transitionCubic_add_coeff _ _ _ _ _ _ _ p q

/-- **The coefficient is homogeneous in the functional**, the scalar entering through the
constant function it names. -/
public theorem transitionCoeff_smul (r : k) (φ : Module.Dual k (V →ₗ[k] V))
    (p q : Fin (Module.finrank k V)) :
    transitionCoeff k V X Y hXc hYc b (r • φ) p q =
      baseRingHom k (transitionSource k V X Y hXc hYc) r *
        transitionCoeff k V X Y hXc hYc b φ p q := by
  simp only [transitionCoeff, LinearMap.smul_apply, smul_eq_mul, _root_.map_mul]
  exact transitionCubic_smul_coeff _ _ _ _ _ _ _ p q

/-- **The linear system of the classifying morphism of Tag 0B1S.** The `k`-linear map carrying a
functional `φ` on `End V` to the global section

`ψ(φ) = ∑ p, ∑ q, P_φ(p, q) · (bₚ ⊗ b_q)`

of `𝒪(1,1)` on the source. Its coefficients are the global functions
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCoeff`, and its basis sections the tensors
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautGlobal`; by
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_eq_sum_basis` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_coord_eq_transitionCubic` the value
of `ψ(φ)` at a point of the source is `φ` applied to the endomorphism the parametrisation produces
from the data that point carries.

The source of the map is `(End V)ᵛ`, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.ParameterModule k V`, the module whose projective space
is the ambient space `𝐏` of the parameter points of Tag 0B1S. -/
public def transitionSections :
    Module.Dual k (V →ₗ[k] V) →ₗ[k] Γ(transitionPairTaut k V X Y hXc hYc, ⊤) where
  toFun φ := ∑ p, ∑ q, transitionCoeff k V X Y hXc hYc b φ p q •
    transitionPairGlobal k V X Y hXc hYc b p q
  map_add' φ φ' := by
    simp only [transitionCoeff_add, add_smul]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [← Finset.sum_add_distrib]
  map_smul' r φ := by
    simp only [transitionCoeff_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_smul]
    rfl

/-- The value of the linear system, which is the double sum its definition names. -/
public theorem transitionSections_apply (φ : Module.Dual k (V →ₗ[k] V)) :
    transitionSections k V X Y hXc hYc b φ =
      ∑ p, ∑ q, transitionCoeff k V X Y hXc hYc b φ p q •
        transitionPairGlobal k V X Y hXc hYc b p q := rfl

end Sections

/-! ### The value of the linear system at a `k`-point of the source -/

section Values

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)
  (b : Module.Basis (Fin (Module.finrank k V)) k V)

attribute [local instance] isInvertible_tautologicalModule globalSectionsModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The parameter vector of a value of the parameters.** The coordinates of
`(c, u, u', w, h)` arranged along
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionParamIndex`, which is the datum a morphism
into the affine parameter factor is, by `AlgebraicGeometry.AffineSpace.homOfVector`. -/
public def transitionParamCoords (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    transitionParamIndex k V → k
  | ⟨.inl ()⟩ => c
  | ⟨.inr (.inl i)⟩ => b.coord i u
  | ⟨.inr (.inr (.inl j))⟩ => b.coord j u'
  | ⟨.inr (.inr (.inr (.inl i)))⟩ => b.coord i w
  | ⟨.inr (.inr (.inr (.inr it)))⟩ => b.coord it.1 (h (b it.2))

@[simp]
public theorem transitionParamCoords_c (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    transitionParamCoords k V b c u u' w h (ULift.up (Sum.inl ())) = c := rfl

/-- The coordinate of `transitionParamCoords` at the `i`-th index of `u` is the `i`-th coordinate
of `u` in the basis `b`. -/
@[simp]
public theorem transitionParamCoords_u (c : k) (u u' w : V) (h : V →ₗ[k] V)
    (i : Fin (Module.finrank k V)) :
    transitionParamCoords k V b c u u' w h (ULift.up (Sum.inr (Sum.inl i))) = b.coord i u := rfl

/-- The coordinate of `transitionParamCoords` at the `j`-th index of `u'` is the `j`-th coordinate
of `u'` in the basis `b`. -/
@[simp]
public theorem transitionParamCoords_u' (c : k) (u u' w : V) (h : V →ₗ[k] V)
    (j : Fin (Module.finrank k V)) :
    transitionParamCoords k V b c u u' w h (ULift.up (Sum.inr (Sum.inr (Sum.inl j)))) =
      b.coord j u' := rfl

/-- The coordinate of `transitionParamCoords` at the `i`-th index of `w` is the `i`-th coordinate
of `w` in the basis `b`. -/
@[simp]
public theorem transitionParamCoords_w (c : k) (u u' w : V) (h : V →ₗ[k] V)
    (i : Fin (Module.finrank k V)) :
    transitionParamCoords k V b c u u' w h
        (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) = b.coord i w := rfl

/-- The coordinate of `transitionParamCoords` at the index `(i, t)` of `h` is the `i`-th coordinate
of `h (b t)` in the basis `b`, the `(i, t)` matrix entry of `h`. -/
@[simp]
public theorem transitionParamCoords_h (c : k) (u u' w : V) (h : V →ₗ[k] V)
    (i t : Fin (Module.finrank k V)) :
    transitionParamCoords k V b c u u' w h
        (ULift.up (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, t)))))) = b.coord i (h (b t)) := rfl

/-- **The `k`-point of the source carrying a given point of `X × Y` and given parameters.** A
morphism into affine space over a base is its composite to the base together with a family of
global functions, by `AlgebraicGeometry.AffineSpace.homOfVector`; here the base component is the
given point of `X × Y` and the functions are the constants naming the parameters. -/
public def transitionSourcePoint (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    Spec (CommRingCat.of k) ⟶ transitionSource k V X Y hXc hYc :=
  AffineSpace.homOfVector pt fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (transitionParamCoords k V b c u u' w h i)

/-- The `k`-point of the source lies over the point of the base it was built from. -/
private theorem transitionSourcePoint_comp_toBase
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    transitionSourcePoint k V X Y hXc hYc b pt c u u' w h ≫
      transitionSourceToBase k V X Y hXc hYc = pt :=
  AffineSpace.homOfVector_over _ _

/-- **The `k`-point of the source splits the structure morphism**, as soon as the point of the
base does. This is the hypothesis `hp` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.ringGerm_sub_scalarTop_mem_maximalIdeal`. -/
public theorem transitionSourcePoint_comp_toSpec
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    transitionSourcePoint k V X Y hXc hYc b pt c u u' w h ≫
      transitionSourceToSpec k V X Y hXc hYc = 𝟙 _ := by
  have hkey : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫
      closedSubschemeOfι k V X hXc ≫ projectiveSpaceOfModuleToSpec k V = 𝟙 _ := hpt
  have hexp : transitionSourcePoint k V X Y hXc hYc b pt c u u' w h ≫
      transitionSourceToSpec k V X Y hXc hYc =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h ≫
          transitionSourceToBase k V X Y hXc hYc) ≫
        pullback.fst (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc) ≫
          closedSubschemeOfι k V X hXc ≫ projectiveSpaceOfModuleToSpec k V := by
    simp only [transitionSourceToSpec, tsSource, Category.assoc]
    rfl
  rw [hexp,
    transitionSourcePoint_comp_toBase k V X Y hXc hYc b pt c u u' w h]
  exact hkey

/-- **The constants are the pullbacks of themselves along a `k`-point**: the global function
`baseRingHom k S r` has, at a `k`-point splitting the structure morphism, the value `r`. -/
public theorem appTop_baseRingHom_of_comp_eq_id
    (p : Spec (CommRingCat.of k) ⟶ transitionSource k V X Y hXc hYc)
    (hp : p ≫ transitionSourceToSpec k V X Y hXc hYc = 𝟙 _) (r : k) :
    p.appTop.hom (baseRingHom k (transitionSource k V X Y hXc hYc) r) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r := by
  rw [baseRingHom_transitionSource_eq_scalarTop,
    appTop_scalarTop k p (transitionSourceToSpec k V X Y hXc hYc) r, hp]
  simp [scalarTop]

/-- **The value of a coefficient of the linear system at a `k`-point of the source** is the
coefficient of the parametrisation at the data that point carries:

`P_φ(p, q)(x) = φ(G(εₚ, ε_q))` for `G = transitionEnd (εₚ) (ε_q) c u u' w h`.

Both sides are the cubic `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionCubic`; the left
reaches it by pushing the pullback along `x` through the coefficient, the right by
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_coord_eq_transitionCubic` followed
by the identification of the global functions of `Spec k` with `k`. Both passages are
`AlgebraicGeometry.ProjectiveSpaceOfModule.map_transitionCubic`. -/
public theorem appTop_transitionCoeff
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (φ : Module.Dual k (V →ₗ[k] V))
    (p q : Fin (Module.finrank k V)) :
    (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).appTop.hom
        (transitionCoeff k V X Y hXc hYc b φ p q) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        (φ (transitionEnd k V (b.coord p) (b.coord q) c u u' w h)) := by
  set x := transitionSourcePoint k V X Y hXc hYc b pt c u u' w h with hx
  have hsplit : x ≫ transitionSourceToSpec k V X Y hXc hYc = 𝟙 _ :=
    transitionSourcePoint_comp_toSpec k V X Y hXc hYc b pt hpt c u u' w h
  have hcoord : ∀ i : transitionParamIndex k V,
      x.appTop.hom (AffineSpace.coord (prodOfClosed k V X Y hXc hYc) i) =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
          (transitionParamCoords k V b c u u' w h i) := fun i =>
    AffineSpace.homOfVector_appTop_coord _ _ i
  have hconst : ∀ r : k, x.appTop.hom (baseRingHom k (transitionSource k V X Y hXc hYc) r) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r := fun r =>
    appTop_baseRingHom_of_comp_eq_id k V X Y hXc hYc x hsplit r
  rw [transitionCoeff, map_transitionCubic x.appTop.hom,
    apply_transitionEnd_coord_eq_transitionCubic k V b φ p q c u u' w h,
    map_transitionCubic (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom]
  simp only [tsParamC, tsParamU, tsParamU', tsParamW, tsParamH, hcoord, hconst,
    transitionParamCoords_c, transitionParamCoords_u, transitionParamCoords_u',
    transitionParamCoords_w, transitionParamCoords_h]

/-- **A coefficient of the linear system has, at a `k`-point of the source, the germ of the
constant it evaluates to.** This is the hypothesis `hP` that
`AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_sum_smul_sub_smul_mem` consumes, with the
reference constant the value
`AlgebraicGeometry.ProjectiveSpaceOfModule.appTop_transitionCoeff` computes. -/
public theorem ringGerm_transitionCoeff_sub_scalarTop_mem
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (φ : Module.Dual k (V →ₗ[k] V)) (p q : Fin (Module.finrank k V)) :
    ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace
          ((transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a) ⊤
          (Opens.mem_top _) (transitionCoeff k V X Y hXc hYc b φ p q) -
        ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace
          ((transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a) ⊤
          (Opens.mem_top _)
          (scalarTop k (transitionSourceToSpec k V X Y hXc hYc)
            (φ (transitionEnd k V (b.coord p) (b.coord q) c u u' w h))) ∈
      IsLocalRing.maximalIdeal (ringStalk (transitionSource k V X Y hXc hYc).toRingedSpace
        ((transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a)) :=
  ringGerm_sub_scalarTop_mem_maximalIdeal k (transitionSourceToSpec k V X Y hXc hYc)
    (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h)
    (transitionSourcePoint_comp_toSpec k V X Y hXc hYc b pt hpt c u u' w h) a
    (transitionCoeff k V X Y hXc hYc b φ p q)
    (φ (transitionEnd k V (b.coord p) (b.coord q) c u u' w h))
    (appTop_transitionCoeff k V X Y hXc hYc b pt hpt c u u' w h φ p q)

/-- **The germ of the linear system**, modulo `𝔪ₜ · 𝒪(1,1)ₜ`: the combination of the germs of the
basis tensors whose coefficients are the *constants* `D` that the coefficients of the linear
system take as values at `t`.

This is the one step the germ calculus of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TripleTautologicalGerm` could not take by
itself: its coefficients are constants of `k`, and those of the linear system are global
functions. `AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_sum_smul_sub_smul_mem` trades the
latter for the former given values at the point, and at a `k`-point of the source those values
are supplied by
`AlgebraicGeometry.ProjectiveSpaceOfModule.ringGerm_transitionCoeff_sub_scalarTop_mem`, with
`D (p, q) = φ(G(εₚ, ε_q))` the coordinates of the parametrisation at the data the point carries.

Stated at an arbitrary point with the values as a hypothesis rather than at the `k`-point itself:
the germ calculus does not care where the values come from, and the statement is then light enough
to elaborate. The double sum of the linear system is flattened to a single sum over pairs, which
is the shape `AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_sum_smul_sub_smul_mem` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairGerm_sum_sub_smul_mem` are both stated at. -/
public theorem grpGerm_transitionSections_sub_sum_smul_mem
    (t : transitionSource k V X Y hXc hYc) (φ : Module.Dual k (V →ₗ[k] V))
    (D : Fin (Module.finrank k V) × Fin (Module.finrank k V) → k)
    (hD : ∀ pq, ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace t ⊤
          (Opens.mem_top _) (transitionCoeff k V X Y hXc hYc b φ pq.1 pq.2) -
        ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace t ⊤ (Opens.mem_top _)
          (scalarTop k (transitionSourceToSpec k V X Y hXc hYc) (D pq)) ∈
      IsLocalRing.maximalIdeal
        (ringStalk (transitionSource k V X Y hXc hYc).toRingedSpace t)) :
    grpGerm (transitionSource k V X Y hXc hYc).toRingedSpace
          (pairSh k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
            (transitionSourceToSpec k V X Y hXc hYc)).val t ⊤ (Opens.mem_top _)
          (transitionSections k V X Y hXc hYc b φ) -
        ∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
          scalarGerm k (transitionSourceToSpec k V X Y hXc hYc) t (D pq) •
            pairGerm k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
              (transitionSourceToSpec k V X Y hXc hYc) t (b pq.1) (b pq.2) ∈
      pairMax k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
        (transitionSourceToSpec k V X Y hXc hYc) t := by
  have key := grpGerm_sum_smul_sub_smul_mem
    (pairSh k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
      (transitionSourceToSpec k V X Y hXc hYc)).val t ⊤ (Opens.mem_top _)
    (fun pq : Fin (Module.finrank k V) × Fin (Module.finrank k V) =>
      transitionCoeff k V X Y hXc hYc b φ pq.1 pq.2)
    (fun pq => scalarTop k (transitionSourceToSpec k V X Y hXc hYc) (D pq)) hD
    (fun pq : Fin (Module.finrank k V) × Fin (Module.finrank k V) =>
      transitionPairGlobal k V X Y hXc hYc b pq.1 pq.2)
  have hflat : transitionSections k V X Y hXc hYc b φ =
      ∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
        transitionCoeff k V X Y hXc hYc b φ pq.1 pq.2 •
          transitionPairGlobal k V X Y hXc hYc b pq.1 pq.2 := by
    rw [transitionSections_apply]
    exact (Fintype.sum_prod_type
      (fun pq : Fin (Module.finrank k V) × Fin (Module.finrank k V) =>
        transitionCoeff k V X Y hXc hYc b φ pq.1 pq.2 •
          transitionPairGlobal k V X Y hXc hYc b pq.1 pq.2)).symm
  simp only [ringGerm_scalarTop] at key
  rw [hflat]
  exact key

/-! ### The germ of the linear system against the reference tensor -/

/-- **The total of the coefficients against a pair of functionals is the coordinate of the
parametrisation at that pair.** This is
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_eq_sum_basis` with the double sum
flattened to a single sum over pairs and the factors in the order the germ formula produces them:
the bilinearity of the parametrisation in `(f, f')` read off its expansion in the basis. It is
what turns the scalar the germ formula computes into the number whose nonvanishing is the
geometric condition. -/
public theorem sum_transitionEnd_coord_mul_eq (φ : Module.Dual k (V →ₗ[k] V))
    (f f' : Module.Dual k V) (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    ∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
        φ (transitionEnd k V (b.coord pq.1) (b.coord pq.2) c u u' w h) *
          f (b pq.1) * f' (b pq.2) =
      φ (transitionEnd k V f f' c u u' w h) := by
  have hsum := apply_transitionEnd_eq_sum_basis k V b φ f f' c u u' w h
  have hflip : ∑ p, ∑ q, f (b p) * f' (b q) *
        φ (transitionEnd k V (b.coord p) (b.coord q) c u u' w h) =
      ∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
        φ (transitionEnd k V (b.coord pq.1) (b.coord pq.2) c u u' w h) *
          f (b pq.1) * f' (b pq.2) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [← hflip, ← hsum]

/-- **The germ of the linear system against the reference tensor.** Modulo `𝔪ₜ · 𝒪(1,1)ₜ` the
germ of `ψ(φ)` at `t` is the germ of the reference tensor `a₀ ⊗ b₀` times the scalar

`(∑ p, ∑ q, D(p, q) · f(bₚ) · f'(b_q)) / (f(a₀) · f'(b₀))`,

for `D` the values the coefficients of the linear system take at `t`. This is exactly the
hypothesis `hS` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_pair_iff_of_germ_sub_smul_mem`,
whose conclusion is that `ψ(φ)` is nonvanishing at `t` precisely when the numerator is nonzero.
At a `k`-point of the source `D(p, q) = φ(G(εₚ, ε_q))` and the numerator is `φ(G(f, f'))`, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.sum_transitionEnd_coord_mul_eq`.

The proof adds two memberships. The first,
`AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_transitionSections_sub_sum_smul_mem`, trades
the global-function coefficients for the constants `D`. The second is
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairGerm_sum_sub_smul_mem` with the scalars absorbed
into the first slot — `D(p, q) • bₚ` against `0`, the subtracted family being zero and
contributing nothing, by `AlgebraicGeometry.ProjectiveSpaceOfModule.tripleGerm_smul_one`, which
applies to `pairGerm` unchanged because the latter is an abbreviation. -/
public theorem grpGerm_transitionSections_sub_smul_mem
    (t : transitionSource k V X Y hXc hYc) (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (tsSource k V X Y hXc hYc).base t = linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (tsTarget k V X Y hXc hYc).base t = linearFunctionalPoint k V f' hf')
    (a₀ : V) (ha₀ : f a₀ ≠ 0) (b₀ : V) (hb₀ : f' b₀ ≠ 0)
    (φ : Module.Dual k (V →ₗ[k] V))
    (D : Fin (Module.finrank k V) × Fin (Module.finrank k V) → k)
    (hD : ∀ pq, ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace t ⊤
          (Opens.mem_top _) (transitionCoeff k V X Y hXc hYc b φ pq.1 pq.2) -
        ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace t ⊤ (Opens.mem_top _)
          (scalarTop k (transitionSourceToSpec k V X Y hXc hYc) (D pq)) ∈
      IsLocalRing.maximalIdeal
        (ringStalk (transitionSource k V X Y hXc hYc).toRingedSpace t)) :
    grpGerm (transitionSource k V X Y hXc hYc).toRingedSpace
          (pairSh k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
            (transitionSourceToSpec k V X Y hXc hYc)).val t ⊤ (Opens.mem_top _)
          (transitionSections k V X Y hXc hYc b φ) -
        scalarGerm k (transitionSourceToSpec k V X Y hXc hYc) t
            ((∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
              D pq * f (b pq.1) * f' (b pq.2)) / (f a₀ * f' b₀)) •
          pairGerm k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
            (transitionSourceToSpec k V X Y hXc hYc) t a₀ b₀ ∈
      pairMax k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
        (transitionSourceToSpec k V X Y hXc hYc) t := by
  have hzero : pairGerm k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
      (transitionSourceToSpec k V X Y hXc hYc) t 0 0 = 0 := by
    have hs := tripleGerm_smul_one k V V k (tsSource k V X Y hXc hYc)
      (tsTarget k V X Y hXc hYc) (inertSlot k (transitionSourceToSpec k V X Y hXc hYc))
      (transitionSourceToSpec k V X Y hXc hYc) (tsSource_comp_toSpec k V X Y hXc hYc) t
      (0 : k) (0 : V) (0 : V) (1 : k)
    simpa using hs
  have hsmul : ∀ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
      pairGerm k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
          (transitionSourceToSpec k V X Y hXc hYc) t (D pq • b pq.1) (b pq.2) =
        scalarGerm k (transitionSourceToSpec k V X Y hXc hYc) t (D pq) •
          pairGerm k V V (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
            (transitionSourceToSpec k V X Y hXc hYc) t (b pq.1) (b pq.2) := fun pq =>
    tripleGerm_smul_one k V V k (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
      (inertSlot k (transitionSourceToSpec k V X Y hXc hYc))
      (transitionSourceToSpec k V X Y hXc hYc) (tsSource_comp_toSpec k V X Y hXc hYc) t
      (D pq) (b pq.1) (b pq.2) (1 : k)
  have hpair := pairGerm_sum_sub_smul_mem k V V (tsSource k V X Y hXc hYc)
    (tsTarget k V X Y hXc hYc) (transitionSourceToSpec k V X Y hXc hYc) t f hf e₁ f' hf' e₂
    (tsSource_comp_toSpec k V X Y hXc hYc) (tsTarget_comp_toSpec k V X Y hXc hYc) a₀ ha₀ b₀ hb₀
    (fun pq : Fin (Module.finrank k V) × Fin (Module.finrank k V) => D pq • b pq.1)
    (fun _ => (0 : V)) (fun pq => b pq.2) (fun _ => (0 : V))
  have hscal : ∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
        (f (D pq • b pq.1) / f a₀ * (f' (b pq.2) / f' b₀) -
          f (0 : V) / f a₀ * (f' (0 : V) / f' b₀)) =
      (∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
        D pq * f (b pq.1) * f' (b pq.2)) / (f a₀ * f' b₀) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [map_zero, zero_div, zero_mul, sub_zero, _root_.map_smul, smul_eq_mul]
    exact div_mul_div_comm _ _ _ _
  simp only [hsmul, hzero, sub_zero, hscal] at hpair
  have key := grpGerm_transitionSections_sub_sum_smul_mem k V X Y hXc hYc b t φ D hD
  have hadd := Submodule.add_mem _ key hpair
  rw [sub_add_sub_cancel] at hadd
  exact hadd

/-- **The nonvanishing criterion for the linear system.** `ψ(φ)` is nonvanishing at `t` exactly
when the total of the coefficients against the two functionals of `t` is nonzero. Together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.sum_transitionEnd_coord_mul_eq` — which identifies
that total, at a `k`-point of the source, with `φ(G(f, f'))` — this says that `ψ(φ)` vanishes at
a point precisely where `φ` kills the endomorphism the parametrisation produces there. That is
the statement that makes the nonvanishing opens of the `ψ(φ)` cover exactly the locus where the
parametrisation is nonzero, which is where the classifying morphism of Tag 0B1S is defined.

The reference tensor's two vectors `a₀, b₀` are auxiliary: the criterion does not mention them,
their ratios having cancelled against the denominator `f(a₀) · f'(b₀)` of the germ formula. -/
public theorem mem_nonvanishingOpen_transitionSections_iff
    (t : transitionSource k V X Y hXc hYc) (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (tsSource k V X Y hXc hYc).base t = linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (tsTarget k V X Y hXc hYc).base t = linearFunctionalPoint k V f' hf')
    (a₀ : V) (ha₀ : f a₀ ≠ 0) (b₀ : V) (hb₀ : f' b₀ ≠ 0)
    (φ : Module.Dual k (V →ₗ[k] V))
    (D : Fin (Module.finrank k V) × Fin (Module.finrank k V) → k)
    (hD : ∀ pq, ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace t ⊤
          (Opens.mem_top _) (transitionCoeff k V X Y hXc hYc b φ pq.1 pq.2) -
        ringGerm (transitionSource k V X Y hXc hYc).toRingedSpace t ⊤ (Opens.mem_top _)
          (scalarTop k (transitionSourceToSpec k V X Y hXc hYc) (D pq)) ∈
      IsLocalRing.maximalIdeal
        (ringStalk (transitionSource k V X Y hXc hYc).toRingedSpace t)) :
    t ∈ Stacks.NonvanishingOpen.nonvanishingOpen (transitionSource k V X Y hXc hYc)
        (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ) ↔
      (∑ pq : Fin (Module.finrank k V) × Fin (Module.finrank k V),
        D pq * f (b pq.1) * f' (b pq.2)) ≠ 0 := by
  have hev : ((Stacks.NonvanishingSpelling.sectionsEquiv (transitionSource k V X Y hXc hYc)
          (transitionPairTaut k V X Y hXc hYc)).symm
        (transitionSections k V X Y hXc hYc b φ)).eval (op ⊤) =
      transitionSections k V X Y hXc hYc b φ :=
    (Stacks.NonvanishingSpelling.sectionsEquiv (transitionSource k V X Y hXc hYc)
      (transitionPairTaut k V X Y hXc hYc)).apply_symm_apply _
  have hloc := Set.ext_iff.mp (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq
    (transitionSource k V X Y hXc hYc) (transitionPairTaut k V X Y hXc hYc)
    (transitionSections k V X Y hXc hYc b φ)) t
  refine hloc.symm.trans ?_
  refine mem_nonvanishingLocus_pair_iff_of_germ_sub_smul_mem k V V
    (tsSource k V X Y hXc hYc) (tsTarget k V X Y hXc hYc)
    (transitionSourceToSpec k V X Y hXc hYc) t f hf e₁ f' hf' e₂ a₀ ha₀ b₀ hb₀ _ _ ?_
  rw [hev]
  exact grpGerm_transitionSections_sub_smul_mem k V X Y hXc hYc b t f hf e₁ f' hf' e₂ a₀ ha₀
    b₀ hb₀ φ D hD

/-! ### The criterion at a `k`-point of the source -/

/-- **The first projection of the `k`-point of the source is the first component of the base
point.** `AlgebraicGeometry.AffineSpace.homOfVector_over` says the point lies over `pt`, and the
first projection factors through the base. -/
public theorem transitionSourcePoint_comp_tsSource
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    transitionSourcePoint k V X Y hXc hYc b pt c u u' w h ≫ tsSource k V X Y hXc hYc =
      pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc := by
  rw [tsSource, ← Category.assoc,
    transitionSourcePoint_comp_toBase k V X Y hXc hYc b pt c u u' w h]

/-- **The second projection of the `k`-point of the source is its second component.** -/
public theorem transitionSourcePoint_comp_tsTarget
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    transitionSourcePoint k V X Y hXc hYc b pt c u u' w h ≫ tsTarget k V X Y hXc hYc =
      pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc := by
  rw [tsTarget, ← Category.assoc,
    transitionSourcePoint_comp_toBase k V X Y hXc hYc b pt c u u' w h]

/-- **The nonvanishing criterion at a `k`-point of the source, in closed form.** At the point of
the source carrying the pair of `k`-points `(f, f')` of `X` and `Y` and the parameters
`(c, u, u', w, h)`, the section `ψ(φ)` is nonvanishing exactly when

`φ(G(f, f')) ≠ 0`, `G = transitionEnd f f' c u u' w h`,

that is exactly when `φ` does not kill the endomorphism the parametrisation produces from that
data. **This is the geometric content of the construction**: the linear system of the classifying
morphism of Tag 0B1S vanishes at a point precisely where the parametrisation's coordinate does,
so the nonvanishing opens of the `ψ(φ)` cover exactly the locus on which the classifying morphism
is defined — which is the locus where `G ≠ 0`, and not all of the source, `G` being zero at
`c = 0, w = 0`.

The reference vectors of the germ formula are chosen inside: a nonzero functional has a vector it
does not kill, and the criterion does not depend on the choice, their ratios having cancelled
against the denominator of
`AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_transitionSections_sub_smul_mem`. -/
public theorem mem_nonvanishingOpen_transitionSections_point_iff
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf')
    (φ : Module.Dual k (V →ₗ[k] V)) :
    (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a ∈
        Stacks.NonvanishingOpen.nonvanishingOpen (transitionSource k V X Y hXc hYc)
          (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ) ↔
      φ (transitionEnd k V f f' c u u' w h) ≠ 0 := by
  obtain ⟨a₀, ha₀⟩ := DFunLike.ne_iff.mp hf
  obtain ⟨b₀, hb₀⟩ := DFunLike.ne_iff.mp hf'
  have e₁' : (tsSource k V X Y hXc hYc).base
      ((transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a) =
      linearFunctionalPoint k V f hf :=
    (congrArg (·.base a)
      (transitionSourcePoint_comp_tsSource k V X Y hXc hYc b pt c u u' w h)).trans
      e₁
  have e₂' : (tsTarget k V X Y hXc hYc).base
      ((transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a) =
      linearFunctionalPoint k V f' hf' :=
    (congrArg (·.base a)
      (transitionSourcePoint_comp_tsTarget k V X Y hXc hYc b pt c u u' w h)).trans
      e₂
  have hiff := mem_nonvanishingOpen_transitionSections_iff k V X Y hXc hYc b
    ((transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a) f hf e₁' f' hf' e₂'
    a₀ ha₀ b₀ hb₀ φ
    (fun pq : Fin (Module.finrank k V) × Fin (Module.finrank k V) =>
      φ (transitionEnd k V (b.coord pq.1) (b.coord pq.2) c u u' w h))
    (fun pq => ringGerm_transitionCoeff_sub_scalarTop_mem k V X Y hXc hYc b pt hpt c u u' w h a
      φ pq.1 pq.2)
  rw [sum_transitionEnd_coord_mul_eq k V b φ f f' c u u' w h] at hiff
  exact hiff

end Values

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
