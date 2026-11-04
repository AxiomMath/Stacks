module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# A regular variety that is not geometrically reduced

For a prime `p`, the affine hypersurface cut out by `xᵖ - t` over the rational function field
`𝔽ₚ(t)` is a regular variety which is not geometrically reduced: after adjoining a `p`-th root
of `t` the equation acquires a multiple root.

## Main definitions

* `AlgebraicGeometry.hypersurfaceEquation`: the polynomial `xᵖ - t` over `𝔽ₚ(t)`.
* `AlgebraicGeometry.hypersurfaceRing`: its coordinate ring `𝔽ₚ(t)[x]/(xᵖ - t)`.
* `AlgebraicGeometry.hypersurface`: the affine scheme it defines, with structure morphism
  `AlgebraicGeometry.hypersurfaceToBase`.

## Main results

* `AlgebraicGeometry.hypersurface_isVariety`, `AlgebraicGeometry.hypersurface_isRegular` and
  `AlgebraicGeometry.hypersurface_not_geometricallyReduced`: the hypersurface is a variety, is
  regular, and is not geometrically reduced.

## Implementation notes

The characteristic is an arbitrary prime `p`, so the example applies to every prime. The three
independent conclusions of the source are stated separately. Failure of geometric reducedness
is witnessed by the nonzero nilpotent `x ⊗ 1 - 1 ⊗ x` in the self-tensor product of the
coordinate ring, which exists because the coordinate ring is a purely inseparable extension of
degree `p`.

## References

* [Stacks Project, Tag 038Y](https://stacks.math.columbia.edu/tag/038Y)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry


variable (p : ℕ) [Fact p.Prime]

/-- The polynomial `xᵖ - t` over `𝔽ₚ(t)`. -/
noncomputable def hypersurfaceEquation : Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.C RatFunc.X

/-- The coordinate ring `𝔽ₚ(t)[x]/(xᵖ - t)`. -/
abbrev hypersurfaceRing :=
  Polynomial (RatFunc (ZMod p)) ⧸ Ideal.span {hypersurfaceEquation p}

/-- The affine hypersurface `xᵖ - t = 0`. -/
noncomputable abbrev hypersurface : Scheme := Spec (.of (hypersurfaceRing p))

/-- The canonical structure morphism over `𝔽ₚ(t)`. -/
noncomputable def hypersurfaceToBase :
    hypersurface p ⟶ Spec (.of (RatFunc (ZMod p))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (RatFunc (ZMod p)) (hypersurfaceRing p)))

private theorem ratFunc_X_not_pth_power :
    ∀ b : RatFunc (ZMod p), b ^ p ≠ RatFunc.X := by
  intro b hb
  let v := IsDedekindDomain.HeightOneSpectrum.valuation
    (RatFunc (ZMod p)) (Polynomial.idealX (ZMod p))
  have hv : v b ^ p = WithZero.exp (-1) := by
    rw [← Valuation.map_pow, hb]
    exact Polynomial.valuation_X_eq_neg_one (ZMod p)
  have hlog := congrArg WithZero.log hv
  rw [WithZero.log_pow, WithZero.log_exp] at hlog
  have hmul : (p : ℤ) * WithZero.log (v b) = -1 := by
    simpa [nsmul_eq_mul] using hlog
  have hd : (p : ℤ) ∣ (1 : ℤ) := ⟨-WithZero.log (v b), by linear_combination hmul⟩
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd))

private theorem hypersurfaceEquation_irreducible :
    Irreducible (hypersurfaceEquation p) := by
  simpa [hypersurfaceEquation] using
    (X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
      (ratFunc_X_not_pth_power p))

private theorem hypersurfaceEquation_monic : (hypersurfaceEquation p).Monic := by
  rw [hypersurfaceEquation]
  exact Polynomial.monic_X_pow_sub_C RatFunc.X (Nat.ne_of_gt (Fact.out : p.Prime).pos)

/-- The defining polynomial `xᵖ - t` is irreducible, as a `Fact`. -/
private instance fact_irreducible : Fact (Irreducible (hypersurfaceEquation p)) :=
  ⟨hypersurfaceEquation_irreducible p⟩

/-- The coordinate ring is a field, since `xᵖ - t` is irreducible. -/
private noncomputable instance hypersurfaceRingField : Field (hypersurfaceRing p) :=
  AdjoinRoot.instField

/-- **Stacks Project, Tag 038Y.** The hypersurface is a variety over `𝔽ₚ(t)`. -/
@[stacks 038Y "regular_not_geometrically_reduced"]
theorem hypersurface_isVariety :
    IsVariety (RatFunc (ZMod p)) (hypersurfaceToBase p) := by
  have : Module.Finite (RatFunc (ZMod p)) (hypersurfaceRing p) :=
    Polynomial.Monic.finite_adjoinRoot (hypersurfaceEquation_monic p)
  have : IsFinite (hypersurfaceToBase p) := by
    show IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap (RatFunc (ZMod p)) (hypersurfaceRing p))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact {}

/-- **Stacks Project, Tag 038Y.** The hypersurface is regular. -/
@[stacks 038Y "regular_not_geometrically_reduced"]
theorem hypersurface_isRegular :
    IsRegular (hypersurface p) := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ?_, ?_⟩
  · simp
  · let e : Γ(hypersurface p, ⊤) ≃+* hypersurfaceRing p :=
      (Scheme.ΓSpecIso (.of (hypersurfaceRing p))).commRingCatIsoToRingEquiv
    have : IsRegularRing (hypersurfaceRing p) := by
      let := (Field.toIsField (hypersurfaceRing p)).toField
      infer_instance
    exact IsRegularRing.of_ringEquiv e.symm

/-- **Stacks Project, Tag 038Y.** The hypersurface is not geometrically reduced. -/
@[stacks 038Y "regular_not_geometrically_reduced"]
theorem hypersurface_not_geometricallyReduced :
    ¬ GeometricallyReduced (hypersurfaceToBase p) := by
  let A := hypersurfaceRing p
  let k := RatFunc (ZMod p)
  let α : A := AdjoinRoot.root (hypersurfaceEquation p)
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hdegree : (hypersurfaceEquation p).natDegree = p := by
    simp [hypersurfaceEquation]
  let pb := AdjoinRoot.powerBasis' (hypersurfaceEquation_monic p)
  let bas := pb.basis
  have hdim : pb.dim = p := by simpa [pb] using hdegree
  let i : Fin pb.dim := ⟨1, by rw [hdim]; omega⟩
  let ell : A →ₗ[k] k := bas.coord i
  have hbas0 : bas ⟨0, by rw [hdim]; omega⟩ = 1 := by
    show pb.basis ⟨0, by rw [hdim]; omega⟩ = pb.gen ^ (0 : ℕ)
    rw [pb.basis_eq_pow]
  have hbasα : bas i = α := by
    show pb.basis i = α
    rw [pb.basis_eq_pow]
    simp only [i, pow_one]
    rw [AdjoinRoot.powerBasis'_gen]
  have hell0 : ell 1 = 0 := by
    show bas.coord i (1 : AdjoinRoot (hypersurfaceEquation p)) = 0
    rw [← hbas0]
    simp [i, Module.Basis.coord]
  have hellα : ell α = 1 := by
    show bas.coord i (AdjoinRoot.root (hypersurfaceEquation p)) = 1
    have hroot : bas i = AdjoinRoot.root (hypersurfaceEquation p) := hbasα
    rw [← hroot]
    simp [i, Module.Basis.coord]
  have hαpow : α ^ p = algebraMap k A RatFunc.X := by
    show AdjoinRoot.root (hypersurfaceEquation p) ^ p =
      algebraMap k (AdjoinRoot (hypersurfaceEquation p)) RatFunc.X
    simp only [AdjoinRoot.root]
    exact AdjoinRoot.mk_eq_mk.mpr <| by simp [hypersurfaceEquation, k]
  let z : TensorProduct k A A := TensorProduct.tmul k α (1 : A) -
    TensorProduct.tmul k (1 : A) α
  have : CharP k p := inferInstance
  have : Nontrivial (TensorProduct k A A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k A A
      (algebraMap k A).injective (algebraMap k A).injective
  have : CharP (TensorProduct k A A) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k (TensorProduct k A A)) p
      (Fact.out : p.Prime).ne_zero
  have hznil : z ^ p = 0 := by
    dsimp [z]
    have hcomm : Commute (TensorProduct.tmul k α (1 : A))
        (TensorProduct.tmul k (1 : A) α) :=
      (Commute.one_right α).tmul (Commute.one_left α)
    rw [sub_pow_char_of_commute p hcomm]
    simp [hαpow, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul]
  have hzne : z ≠ 0 := by
    intro hz
    let ψ : TensorProduct k A A →ₗ[k] TensorProduct k A k :=
      TensorProduct.map LinearMap.id ell
    have hh := congrArg (TensorProduct.rid k A) (congrArg ψ hz)
    simp [z, ψ, hell0, hellα] at hh
  intro hgeom
  have hpb : IsReduced (Limits.pullback (hypersurfaceToBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp
      ((geometricallyReduced_iff (hypersurfaceToBase p)).mp hgeom)) A
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  have hspec : IsReduced (Spec (.of (TensorProduct k A A))) :=
    CategoryTheory.ObjectProperty.prop_of_iso IsReduced (pullbackSpecIso k A A) hpb
  exact hzne ((_root_.isReduced_iff _).mp
    ((affine_isReduced_iff (.of (TensorProduct k A A))).mp hspec) z ⟨p, hznil⟩)

end AlgebraicGeometry

end
