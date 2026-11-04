module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericResidueField
import all StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericResidueField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta-dimension of the relative projective line over a field

Let `C = (S, δ)` be a Chow situation whose base is the spectrum of a field `k` and whose
dimension function vanishes identically. This file computes

  `schemeDeltaDimension C (ℙ¹_S ⟶ S) = 1`,

the one hypothesis beyond the graph data that the non-dominant branch of Stacks 02RU needs
(`Stacks.Chow.principalDivisorCycle_eq_zero_of_not_isDominant`) and one of the three remaining
hypotheses of the reduction to the projective line.

The computation is the transcendence degree of the function field of `ℙ¹_k` over `k`. The route
has four steps, none of which touches the arithmetic of `ℙ¹_k`:

* `ℙ¹_S` is irreducible, so its delta-dimension is the relative dimension at its generic point
  (`Stacks.Chow.schemeDeltaDimension_eq_genericPoint`);
* the generic point lies on the affine chart `𝔸¹_S ⟶ ℙ¹_S`, which is an open immersion, so it
  induces an isomorphism on residue fields and the relative dimension there is the same
  (`Stacks.Chow.relativeDimension_eq_of_residueFieldMap_isIso`);
* `𝔸¹_S` is Mathlib's affine space on a one-element index type
  (`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoAffineSpace`), which over
  `S = Spec k` is `Spec k[T]` (`AlgebraicGeometry.AffineSpace.SpecIso`), and the relative dimension
  is an isomorphism invariant (`Stacks.Chow.relativeDimension_of_iso`);
* over an affine base the computation is a transcendence degree of residue fields of spectra of
  domains, and `Stacks.Chow.trdeg_residueField_genericPoint_eq_trdeg` identifies it with the
  transcendence degree of the ring extension itself. For the polynomial ring that is
  `Cardinal.mk PUnit = 1`.

## Main results

* `Stacks.Chow.functionFieldAlgEquivResidueField` — for a domain `A`, the residue field of
  `Spec A` at the generic point is the function field.
* `Stacks.Chow.trdeg_residueField_genericPoint_eq_trdeg` — for an injective `R ⟶ A` of domains,
  the transcendence degree of `κ(η_A)` over `κ(η_R)` is that of `A` over `R`.
* `Algebra.trdeg_ratFunc` — `trdeg_k k(T) = 1`, which Mathlib does not state.
* `Stacks.Chow.relativeDimension_specMap_genericPoint` — the relative dimension of the generic
  point of `Spec A` over `Spec R`.
* `Stacks.Chow.relativeDimension_relativeProjectiveLine_genericPoint` — the relative dimension
  of the generic point of `ℙ¹_{Spec k}`.
* `Stacks.Chow.schemeDeltaDimension_relativeProjectiveLine_eq_one` — **the delta-dimension of
  `ℙ¹_k` is one.**
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine''` —
  the reduction of Stacks 02RU to the projective line with the delta-dimension hypothesis
  discharged as well as the integrality hypothesis.

## Implementation notes

### The algebra instance on a residue field of a spectrum

`Stacks.Chow.algebraResidueFieldSpec` makes `(Spec A).residueField x` an `A`-algebra by
evaluation of global sections, that is by `A ≅ Γ(Spec A, ⊤) ⟶ κ(x)`. Mathlib has the
corresponding instance only for the function field (the stalk at the generic point), and no
instance of this shape, so there is no diamond; it is needed because the two towers
`k ⊂ κ(η_R) ⊂ κ(η_A)` and `k ⊂ A ⊂ κ(η_A)` are what compare the two transcendence degrees.

### Why the base must be the spectrum of a field, and not merely integral

Only the last of the four steps uses it: `AlgebraicGeometry.AffineSpace.SpecIso` identifies
`𝔸(n; Spec R)` with `Spec R[n]`, and there is no such identification for a general base. For an
integral base `S` the same argument would compute the delta-dimension of `ℙ¹_S` on an affine
open of `S`, which needs the function field of `S` and the compatibility of the generic points;
that is strictly more work and no consumer in chapter 42 needs it.

### `Cardinal.toNat` and the hypothesis `hδ`

`Stacks.Chow.relativeDimension` adds the value of the base dimension function at the image
point to the transcendence degree, so the statements below keep that summand symbolically and
only the final theorem uses `hδ` to discharge it. That keeps every intermediate statement free
of hypotheses on `δ`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 030H](https://stacks.math.columbia.edu/tag/030H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Algebra

universe u

/-! ### The transcendence degree of a field of rational functions -/

/-- The field of rational functions in one variable has transcendence degree one: the polynomial
ring has transcendence degree one, and its fraction field is algebraic over it. -/
theorem Algebra.trdeg_ratFunc (k : Type u) [Field k] : Algebra.trdeg k (RatFunc k) = 1 := by
  rw [← trdeg_add_eq k (Polynomial k) (A := RatFunc k), Polynomial.trdeg_of_isDomain,
    trdeg_eq_zero_iff.2 (IsLocalization.isAlgebraic _ (nonZeroDivisors (Polynomial k))), add_zero]

namespace Stacks.Chow

/-! ### Residue fields of the spectrum of a ring -/

/-- The residue field of `Spec A` at a point is an `A`-algebra, by evaluation of global sections
at that point. -/
instance algebraResidueFieldSpec (A : CommRingCat.{u}) (x : Spec A) :
    Algebra A ((Spec A).residueField x) :=
  ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation x).hom.toAlgebra

/-- The structure map of `Stacks.Chow.algebraResidueFieldSpec`, as a morphism of rings. -/
theorem ofHom_algebraMap_residueFieldSpec (A : CommRingCat.{u}) (x : Spec A) :
    CommRingCat.ofHom (algebraMap A ((Spec A).residueField x)) =
      (Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation x :=
  rfl

/-- On an integral scheme the residue map at the generic point is bijective: the stalk there is
already a field, so its maximal ideal is zero. -/
theorem bijective_residue_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    Function.Bijective (X.residue (genericPoint X)).hom := by
  have hiso : IsIso (X.residue (genericPoint X)) := by
    rw [← genericStalkResidueFieldIso_hom]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (C := CommRingCat) _

/-- For a domain `A` the residue field of `Spec A` at the generic point is the function field of
`Spec A`, as an `A`-algebra. -/
def functionFieldAlgEquivResidueField (A : CommRingCat.{u}) [IsDomain A] :
    (Spec A).functionField ≃ₐ[A] (Spec A).residueField (genericPoint (Spec A)) :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective _ (bijective_residue_genericPoint (Spec A))) (fun _ => rfl)

/-- The residue field of `Spec A` at the generic point is algebraic over `A` for `A` a domain:
it is the fraction field of `A`. -/
theorem trdeg_residueField_genericPoint_eq_zero (A : CommRingCat.{u}) [IsDomain A] :
    Algebra.trdeg A ((Spec A).residueField (genericPoint (Spec A))) = 0 := by
  rw [← (functionFieldAlgEquivResidueField A).trdeg_eq]
  exact trdeg_eq_zero_iff.2 (IsLocalization.isAlgebraic _ (nonZeroDivisors A))

/-- A domain embeds in the residue field of its spectrum at the generic point. -/
instance faithfulSMul_residueField_genericPoint (A : CommRingCat.{u}) [IsDomain A] :
    FaithfulSMul A ((Spec A).residueField (genericPoint (Spec A))) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h : (algebraMap A ((Spec A).residueField (genericPoint (Spec A)))) =
      (functionFieldAlgEquivResidueField A).toRingEquiv.toRingHom.comp
        (algebraMap A ((Spec A).functionField)) := by
    ext a
    exact ((functionFieldAlgEquivResidueField A).commutes a).symm
  rw [h]
  exact (functionFieldAlgEquivResidueField A).injective.comp
    (FaithfulSMul.algebraMap_injective A ((Spec A).functionField))

/-- `Stacks.Chow.trdeg_residueField_genericPoint_eq_zero` at a point presented as the generic
point by an equation rather than definitionally. -/
theorem trdeg_residueField_eq_zero_of_eq_genericPoint (A : CommRingCat.{u}) [IsDomain A]
    {x : Spec A} (hx : x = genericPoint (Spec A)) :
    Algebra.trdeg A ((Spec A).residueField x) = 0 := by
  subst hx
  exact trdeg_residueField_genericPoint_eq_zero A

/-- `Stacks.Chow.faithfulSMul_residueField_genericPoint` at a point presented as the generic
point by an equation rather than definitionally. -/
theorem faithfulSMul_residueField_of_eq_genericPoint (A : CommRingCat.{u}) [IsDomain A]
    {x : Spec A} (hx : x = genericPoint (Spec A)) :
    FaithfulSMul A ((Spec A).residueField x) := by
  subst hx
  infer_instance

/-- An injective ring map carries the generic point of the spectrum of a domain to the generic
point: the contraction of the zero ideal is the kernel. -/
theorem specMap_base_genericPoint {R A : CommRingCat.{u}} [IsDomain R] [IsDomain A] (psi : R ⟶ A)
    (hinj : Function.Injective psi.hom) :
    (Spec.map psi).base (genericPoint (Spec A)) = genericPoint (Spec R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap psi.hom (⊥ : Ideal ↑A) = ⊥
  exact (RingHom.ker_eq_comap_bot _).symm.trans ((RingHom.injective_iff_ker_eq_bot _).mp hinj)

/-- **The transcendence degree of the residue field extension at the generic points.** For an
injective map `R ⟶ A` of domains the extension `κ(η_R) ⊂ κ(η_A)` has the same transcendence
degree as the ring extension `R ⊂ A`.

Both towers `R ⊂ κ(η_R) ⊂ κ(η_A)` and `R ⊂ A ⊂ κ(η_A)` have the same composite transcendence
degree by Stacks 030H, and the first step of the first tower and the second step of the second
are algebraic, being fraction fields. -/
@[ega "IV 5.5.7"]
theorem trdeg_residueField_genericPoint_eq_trdeg {R A : CommRingCat.{u}} [IsDomain R]
    [IsDomain A] [Algebra R A] (psi : R ⟶ A) (hpsi : psi.hom = algebraMap ↑R ↑A)
    (hinj : Function.Injective (algebraMap ↑R ↑A)) :
    letI : Algebra ((Spec R).residueField ((Spec.map psi).base (genericPoint (Spec A))))
        ((Spec A).residueField (genericPoint (Spec A))) :=
      ((Spec.map psi).residueFieldMap (genericPoint (Spec A))).hom.toAlgebra
    Algebra.trdeg ((Spec R).residueField ((Spec.map psi).base (genericPoint (Spec A))))
      ((Spec A).residueField (genericPoint (Spec A))) = Algebra.trdeg ↑R ↑A := by
  have hη := specMap_base_genericPoint psi (hpsi ▸ hinj)
  set η : Spec A := genericPoint (Spec A)
  -- the two residue fields, and the three algebra structures relating them to `R` and `A`
  let _ : Algebra ((Spec R).residueField ((Spec.map psi).base η))
      ((Spec A).residueField η) := ((Spec.map psi).residueFieldMap η).hom.toAlgebra
  let _ : Algebra ↑R ((Spec A).residueField η) :=
    (((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation ((Spec.map psi).base η)) ≫
      (Spec.map psi).residueFieldMap η).hom.toAlgebra
  have htowerK : IsScalarTower ↑R ((Spec R).residueField ((Spec.map psi).base η))
      ((Spec A).residueField η) := IsScalarTower.of_algebraMap_eq' rfl
  have htowerA : IsScalarTower ↑R ↑A ((Spec A).residueField η) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation ((Spec.map psi).base η)) ≫
          (Spec.map psi).residueFieldMap η =
        psi ≫ ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation η) := by
      rw [Category.assoc, Scheme.Γevaluation_naturality, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rw [← hpsi]
    exact congrArg CommRingCat.Hom.hom h
  -- the faithfulness hypotheses of Stacks 030H
  have _ : FaithfulSMul ↑R ((Spec R).residueField ((Spec.map psi).base η)) :=
    faithfulSMul_residueField_of_eq_genericPoint R hη
  have _ : FaithfulSMul ↑R ↑A := (faithfulSMul_iff_algebraMap_injective ↑R ↑A).mpr hinj
  -- the two towers
  have h1 := trdeg_add_eq ↑R ((Spec R).residueField ((Spec.map psi).base η))
    (A := (Spec A).residueField η)
  have h2 := trdeg_add_eq ↑R ↑A (A := (Spec A).residueField η)
  rw [trdeg_residueField_eq_zero_of_eq_genericPoint R hη,
    zero_add] at h1
  rw [trdeg_residueField_genericPoint_eq_zero A, add_zero] at h2
  exact h1.trans h2.symm

/-! ### The relative dimension at the generic point of an affine scheme -/

/-- **The relative dimension is unchanged by a morphism inducing an isomorphism of residue
fields.** This is `Stacks.Chow.relativeDimension_eq_of_residueFieldMap_isIso` and
`Stacks.Chow.relativeDimension_opensι_comp` for an arbitrary dimension function on an arbitrary
base rather than for a Chow situation or for the inclusion of an open subscheme; the case needed
here is the affine chart of the projective line, which is neither. -/
theorem relativeDimension_comp_of_isIso_residueFieldMap {X Y S : Scheme.{u}}
    (δ : DimensionFunction S) (f : Y ⟶ X) (p : X ⟶ S) (y : Y)
    (hy : IsIso (f.residueFieldMap y)) :
    relativeDimension δ (f ≫ p) y = relativeDimension δ p (f.base y) := by
  unfold relativeDimension
  congr 1
  refine congrArg (fun c : Cardinal.{u} => ((Cardinal.toNat c : ℕ) : ℤ)) ?_
  refine @Algebra.trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (_) (_) (RingEquiv.refl _)
    ((asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv.symm) fun a => ?_
  rw [RingEquiv.symm_apply_eq]
  simp only [RingHom.algebraMap_toAlgebra, Scheme.residueFieldMap_comp]
  rfl

/-- The relative dimension of the generic point of `Spec A` over `Spec R`, for an injective map
`R ⟶ A` of domains: the transcendence degree of `A` over `R`. -/
theorem relativeDimension_specMap_genericPoint {R A : CommRingCat.{u}} [IsDomain R] [IsDomain A]
    [Algebra R A] (psi : R ⟶ A) (hpsi : psi.hom = algebraMap ↑R ↑A)
    (hinj : Function.Injective (algebraMap ↑R ↑A)) (δ : DimensionFunction (Spec R)) :
    relativeDimension δ (Spec.map psi) (genericPoint (Spec A))
      = δ (genericPoint (Spec R)) + (Cardinal.toNat (Algebra.trdeg ↑R ↑A) : ℤ) := by
  unfold relativeDimension
  rw [trdeg_residueField_genericPoint_eq_trdeg psi hpsi hinj,
    specMap_base_genericPoint psi (hpsi ▸ hinj)]

/-- The affine line over `Spec R`, for `R` a domain, has relative dimension one at its generic
point. It is Mathlib's affine space on a one-element index type, which over an affine base is the
spectrum of a polynomial ring in one variable, and the relative dimension at a generic point of
an affine scheme is the transcendence degree of the ring extension. -/
theorem relativeDimension_affineLineOver_genericPoint (R : CommRingCat.{u}) [IsDomain R]
    (δ : DimensionFunction (Spec R)) :
    relativeDimension δ (pullback.fst (terminal.from (Spec R))
          (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ))))))
        (genericPoint (affineLineOver (Spec R)))
      = δ (genericPoint (Spec R)) + 1 := by
  have hirr : IrreducibleSpace (AffineSpace PUnit.{u + 1} (Spec R)) := inferInstance
  set p := pullback.fst (terminal.from (Spec R))
    (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))))
  set ψ := CommRingCat.ofHom (MvPolynomial.C (σ := PUnit.{u + 1}) (R := ↑R))
  -- the affine line over `Spec R` is the spectrum of a polynomial ring, over `Spec R`
  let φ : affineLineOver (Spec R) ≅ Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} ↑R)) :=
    affineLineOverIsoAffineSpace (Spec R) ≪≫ AffineSpace.SpecIso PUnit.{u + 1} R
  have h0 : (AffineSpace.SpecIso PUnit.{u + 1} R).hom ≫ Spec.map ψ =
      (AffineSpace PUnit.{u + 1} (Spec R) ↘ Spec R) := by
    rw [← AffineSpace.SpecIso_inv_over (n := PUnit.{u + 1}) R, Iso.hom_inv_id_assoc]
  have hφ : φ.hom ≫ Spec.map ψ = p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g : AffineSpace PUnit.{u + 1} (Spec R) ⟶ Spec R =>
          toAffineSpace (Spec R) ≫ g) h0).trans (toAffineSpace_fst (Spec R)))
  have h1 := relativeDimension_of_iso δ p (Spec.map ψ) φ hφ (genericPoint (affineLineOver (Spec R)))
  rw [genericPoint_eq_of_isOpenImmersion φ.hom] at h1
  rw [← h1, relativeDimension_specMap_genericPoint ψ
      (MvPolynomial.algebraMap_eq ..).symm (MvPolynomial.C_injective _ _) δ,
    MvPolynomial.trdeg_of_isDomain]
  simp

/-! ### The delta-dimension of the relative projective line -/

/-- The relative projective line over `Spec R`, for `R` a domain, has relative dimension one at
its generic point: that point lies on the affine chart, which is an open immersion, so the
transcendence degree there is the one computed on the affine line. -/
theorem relativeDimension_relativeProjectiveLine_genericPoint (R : CommRingCat.{u}) [IsDomain R]
    (δ : DimensionFunction (Spec R)) :
    relativeDimension δ (relativeProjectiveLine (Spec R) ↘ Spec R)
        (genericPoint (relativeProjectiveLine (Spec R)))
      = δ (genericPoint (Spec R)) + 1 := by
  rw [← genericPoint_eq_of_isOpenImmersion (affineChart (Spec R)),
    ← relativeDimension_comp_of_isIso_residueFieldMap δ (affineChart (Spec R))
      (relativeProjectiveLine (Spec R) ↘ Spec R) _ inferInstance, affineChart_comp]
  exact relativeDimension_affineLineOver_genericPoint R δ

/-- **The delta-dimension of the relative projective line over a field is one.** This is the
hypothesis `hPdim` of `Stacks.Chow.principalDivisorCycle_eq_zero_of_not_isDominant` and of the
reduction of Stacks 02RU to the projective line.

`ℙ¹_k` is irreducible, so its delta-dimension is the relative dimension at its generic point;
the dimension function of the base vanishes, so that is the transcendence degree of the function
field of `ℙ¹_k` over `k`, which is one. -/
theorem schemeDeltaDimension_relativeProjectiveLine_eq_one (k : Type u) [Field k]
    (C : ChowSituation.{u}) (hS : C.S = Spec (CommRingCat.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0) :
    schemeDeltaDimension C (relativeProjectiveLine C.S ↘ C.S) = (1 : EInt) := by
  obtain ⟨S, hUC, δ⟩ := C
  subst hS
  rw [schemeDeltaDimension_eq_genericPoint,
    relativeDimension_relativeProjectiveLine_genericPoint (CommRingCat.of k) δ, hδ, zero_add]
  rfl

/-- **The degree of a principal divisor on a proper curve, reduced to the projective line**, with
both the integrality of `ℙ¹_S` and the value of its delta-dimension discharged.

Two hypotheses that Tag 02RU does not state remain: the statement itself for `ℙ¹_S`, and
dominance of the second projection out of the graph closure of every unit section representing
`f`. So this is still a reduction and not the tag, and bears no attribute; see the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Graph`. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine''
    (k : Type u) [Field k] (C : ChowSituation.{u}) [IsIntegral C.S]
    (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    (hdim : schemeDeltaDimension C c = (1 : EInt))
    (hP : ∀ h : (relativeProjectiveLine C.S).functionField, h ≠ 0 →
      principalDivisorDegree (relativeProjectiveLine C.S ↘ C.S) h = 0)
    (f : (rationalFunctions X)ˣ)
    (hdom : ∀ (U : X.Opens) (hU : Dense (U : Set X)) (g : (Γ(X, U))ˣ),
      ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X) →
        IsDominant (graphLineProjection c U ↑g)) :
    properPushforward C c (𝟙 C.S) c (by simp) 0
      (principalDivisorCycle C c hdim ((rationalFunctionsEquivFunctionField X).1 ↑f)) = 0 :=
  properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine' k C hS hδ c hdim
    (schemeDeltaDimension_relativeProjectiveLine_eq_one k C hS hδ) hP f hdom

end Stacks.Chow

end
