module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantBaseChange
public import StacksFrontier.Homology.TwoTermComplex.DeterminantIsoBaseChange
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLineHomBaseChange
import all StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor

/-!
# The two base changes of the determinant agree along a flat ring map

Let `φ : R → A` be a flat homomorphism of commutative rings and let `K` be a perfect object of
`D(R)` of Tor-amplitude in `[-1, 0]`. The determinant of More on Algebra, Section 0FJI has two
ring-level base-change constructions:

* `TwoTermDeterminant.baseChangeMap`, the `φ`-semilinear map `det(K) → det(L)` attached to an
  isomorphism `e : A ⊗ᴸ_R K ≅ L`, built from termwise extension of scalars of a presentation;
* `TwoTermDeterminant.detBaseChange`, the `A`-linear comparison
  `A ⊗_R det(K) ≅ det(A ⊗ᴸ_R K)`, built from the base change of the determinant line of a
  presentation.

This file proves that they agree: the base change map at `e` sends `x` to the determinant of `e`
applied to the comparison at `1 ⊗ x`.

## Main results

* `TwoTermDeterminant.baseChangeMap_refl_eq_detBaseChange`: at the identity of `A ⊗ᴸ_R K`, the
  base change map is `x ↦ detBaseChange (1 ⊗ x)`.
* `TwoTermDeterminant.baseChangeMap_eq_detIsoEquiv_detBaseChange`: at an arbitrary
  isomorphism `e`, it is `x ↦ det(e) (detBaseChange (1 ⊗ x))`.

## Implementation notes

The two constructions present `A ⊗ᴸ_R K` by the same complex written in two ways: through
`ModuleCat.extendScalars` (`TwoTermDeterminant.bcComplex`) and as `A ⊗[R] P^i`
(`TwoTermDeterminant.presentationBaseChangeComplex`). Their determinant lines are not compared
directly. Instead the identity chain map between the two spellings is a degreewise-surjective
quasi-isomorphism, the transport between the two presentations is its determinant equivalence,
and `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_isBaseChange` moves that equivalence
past the base change of determinant lines, reducing everything to the identity
`TwoTermComplex.detLineMap_mk_eq_determinantLineBaseChange` between two base changes of the
determinant line of a single two-term complex of `R`-modules.

## References

* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace ProjectiveDeterminant

variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- On `1 ⊗ x`, the comparison `A ⊗_R det(M) ≅ det(A ⊗_R M)` is the map of determinant lines
induced by the canonical base change `m ↦ 1 ⊗ m`. -/
theorem baseChangeEquiv_one_tmul (x : module (R := R) (M := M)) :
    baseChangeEquiv (R := R) (A := A) (M := M) (1 ⊗ₜ[R] x) =
      detMap (TensorProduct.mk R A M 1)
        (span_range_eq_top_of_isBaseChange (TensorProduct.isBaseChange R M A)) x :=
  Subtype.ext ((coe_baseChangeEquiv_tmul (1 : A) x).trans
    (exteriorMap_mk_one (S := A) (x : ExteriorAlgebra R M)).symm)

end ProjectiveDeterminant

namespace TwoTermComplex

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
  {K₁ K₀ : Type u} [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
  [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]

/-- Along the canonical base changes `m ↦ 1 ⊗ m`, the base change of determinant lines
`TwoTermComplex.detLineMap` is the comparison `TwoTermComplex.determinantLineBaseChange` on
`1 ⊗ φ`. -/
theorem detLineMap_mk_eq_determinantLineBaseChange (f : K₁ →ₗ[R] K₀) (φ : determinantLine f) :
    detLineMap (TensorProduct.isBaseChange R K₁ A) (TensorProduct.isBaseChange R K₀ A) f
        (f.baseChange A) φ = determinantLineBaseChange A f (1 ⊗ₜ[R] φ) := by
  refine detLine_ext (TensorProduct.isBaseChange R K₁ A) fun x => ?_
  rw [detLineMap_apply, determinantLineBaseChange_one_tmul, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    ← ProjectiveDeterminant.baseChangeEquiv_one_tmul (A := A) x,
    ← ProjectiveDeterminant.baseChangeEquiv_one_tmul (A := A) (φ x),
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

end TwoTermComplex

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)

/-- **The transport from the termwise extension of scalars of a presentation to its base change
is the comparison of determinant lines.** The two presentations have the same complex, spelled
through `ModuleCat.extendScalars` and as `A ⊗[R] P^i`; transporting the base change
`TwoTermDeterminant.bcLine` of a section along the identity lands on
`TwoTermDeterminant.presentationDeterminantBaseChange` of `1 ⊗` that section. -/
theorem presentationTransport_bcLine (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K)
    (x : presentationDeterminant P) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    presentationTransport ((P.bcPresentation φ).ofIso (Iso.refl _)) (P.baseChange φ)
        (Iso.refl _) (bcLine φ P x) =
      presentationDeterminantBaseChange φ hφ P (1 ⊗ₜ[R] x) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  let Q := (P.bcPresentation φ).ofIso (Iso.refl ((Lext φ).obj K))
  let g : Q.complex ⟶ (P.baseChange φ).complex := 𝟙 Q.complex
  have hQ : Q.iso.hom = (P.baseChange φ).iso.hom := Category.id_comp _
  have hg : Q.iso.hom ≫ DerivedCategory.Q.map g ≫ (P.baseChange φ).iso.inv =
      (Iso.refl ((Lext φ).obj K)).hom := by
    rw [show DerivedCategory.Q.map g = 𝟙 _ from DerivedCategory.Q.map_id _]
    refine (congrArg (Q.iso.hom ≫ ·) (Category.id_comp (P.baseChange φ).iso.inv)).trans ?_
    rw [hQ]
    exact (P.baseChange φ).iso.hom_inv_id
  have hs : (Q.hom (P.baseChange φ) g).IsDegreewiseSurjective :=
    ⟨Function.surjective_id, Function.surjective_id⟩
  have : IsIso (DerivedCategory.Q.map g) := inferInstanceAs (IsIso (DerivedCategory.Q.map (𝟙 _)))
  have hq := twoTerm_quasiIso_of_isIso_Q_map Q (P.baseChange φ) g
  rw [presentationTransport_eq_surjectiveDeterminant Q (P.baseChange φ) (Iso.refl _) g hg hs hq]
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := (P.bcPresentation φ).finite (-1)
  let := (P.bcPresentation φ).projective (-1)
  let := (P.bcPresentation φ).finite 0
  let := (P.bcPresentation φ).projective 0
  let := isScalarTower_bc φ P.complex (-1)
  let := isScalarTower_bc φ P.complex 0
  have key := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_isBaseChange (S := A)
    (P.complex.d (-1) 0).hom (P.complex.d (-1) 0).hom
    ((bcComplex φ P.complex).d (-1) 0).hom ((P.complex.d (-1) 0).hom.baseChange A)
    (isBaseChange_bcUnit φ P.complex (-1)) (isBaseChange_bcUnit φ P.complex 0)
    (TensorProduct.isBaseChange R _ A) (TensorProduct.isBaseChange R _ A)
    (LinearMap.ext fun _ => rfl) (TwoTermComplex.Hom.id _) (Q.hom (P.baseChange φ) g)
    (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)
    (TwoTermComplex.Hom.isDegreewiseSurjective_id _) (TwoTermComplex.Hom.isQuasiIso_id _) hs hq x
  have hid := LinearEquiv.congr_fun (TwoTermComplex.Hom.detEquiv_id (P.complex.d (-1) 0).hom
    (TwoTermComplex.Hom.isDegreewiseSurjective_id _) (TwoTermComplex.Hom.isQuasiIso_id _)) x
  refine key.trans ((congrArg (TwoTermComplex.detLineMap (TensorProduct.isBaseChange R _ A)
    (TensorProduct.isBaseChange R _ A) (P.complex.d (-1) 0).hom
    ((P.complex.d (-1) 0).hom.baseChange A)) hid).trans ?_)
  exact TwoTermComplex.detLineMap_mk_eq_determinantLineBaseChange A (P.complex.d (-1) 0).hom x

/-- **The two base changes of the determinant agree, at the identity.** For a flat `φ`, the base
change map `TwoTermDeterminant.baseChangeMap` attached to the identity of `A ⊗ᴸ_R K` sends `x` to
the comparison `TwoTermDeterminant.detBaseChange` at `1 ⊗ x`. -/
theorem baseChangeMap_refl_eq_detBaseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A) (K : PerfectTwoTermComplex R)
    (x : ((det R).obj ⟨K⟩).of.obj) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    baseChangeMap φ K (PerfectTwoTermComplex.baseChange φ K) (Iso.refl _) x =
      detBaseChange φ hφ K (1 ⊗ₜ[R] x) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  have hA := presentationTransport_bcLine φ hφ (presentation R K) x
  have hP : detPresentationIso K (presentation R K) x = x :=
    LinearEquiv.congr_fun (presentationTransport_id (presentation R K)) x
  have hd : detBaseChange φ hφ K (1 ⊗ₜ[R] x) =
      presentationTransport ((presentation R K).baseChange φ)
        (presentation A (PerfectTwoTermComplex.baseChange φ K)) (Iso.refl _)
        (presentationDeterminantBaseChange φ hφ (presentation R K) (1 ⊗ₜ[R] x)) := rfl
  have h1 : baseChangeMap φ K (PerfectTwoTermComplex.baseChange φ K) (Iso.refl _) x =
      (detPresentationIso (PerfectTwoTermComplex.baseChange φ K)
        (((presentation R K).bcPresentation φ).ofIso (Iso.refl _))).symm
        (bcLine φ (presentation R K) (detPresentationIso K (presentation R K) x)) := rfl
  rw [h1, LinearEquiv.symm_apply_eq, hP, hd]
  have h2 := (presentationTransport_comp_apply ((presentation R K).baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K))
      (((presentation R K).bcPresentation φ).ofIso (Iso.refl _)) (Iso.refl _) (Iso.refl _)
      (presentationDeterminantBaseChange φ hφ (presentation R K) (1 ⊗ₜ[R] x))).trans
    (congrArg (fun a => presentationTransport ((presentation R K).baseChange φ)
      (((presentation R K).bcPresentation φ).ofIso (Iso.refl _)) a
      (presentationDeterminantBaseChange φ hφ (presentation R K) (1 ⊗ₜ[R] x)))
      (Iso.refl_trans _))
  have h3 := (presentationTransport_comp_apply
      (((presentation R K).bcPresentation φ).ofIso (Iso.refl _)) ((presentation R K).baseChange φ)
      (((presentation R K).bcPresentation φ).ofIso (Iso.refl _)) (Iso.refl _) (Iso.refl _)
      (bcLine φ (presentation R K) x)).trans
    ((congrArg (fun a => presentationTransport
      (((presentation R K).bcPresentation φ).ofIso (Iso.refl _))
      (((presentation R K).bcPresentation φ).ofIso (Iso.refl _)) a
      (bcLine φ (presentation R K) x)) (Iso.refl_trans _)).trans
      (LinearEquiv.congr_fun (presentationTransport_id _) _))
  exact h3.symm.trans ((congrArg (fun w => presentationTransport ((presentation R K).baseChange φ)
    (((presentation R K).bcPresentation φ).ofIso (Iso.refl _)) (Iso.refl _) w) hA).trans h2.symm)

/-- **The two base changes of the determinant agree.** For a flat `φ` and an isomorphism
`e : A ⊗ᴸ_R K ≅ L`, the base change map `TwoTermDeterminant.baseChangeMap` at `e` sends `x` to the
determinant of `e` applied to the comparison `TwoTermDeterminant.detBaseChange` at `1 ⊗ x`. -/
theorem baseChangeMap_eq_detIsoEquiv_detBaseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A) (K : PerfectTwoTermComplex R)
    (L : PerfectTwoTermComplex A) (e : (Lext φ).obj K.obj ≅ L.obj)
    (x : ((det R).obj ⟨K⟩).of.obj) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    baseChangeMap φ K L e x =
      detIsoEquiv (K := PerfectTwoTermComplex.baseChange φ K) e
        (detBaseChange φ hφ K (1 ⊗ₜ[R] x)) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  let b : (⟨PerfectTwoTermComplex.baseChange φ K⟩ : Core (PerfectTwoTermComplex A)) ⟶ ⟨L⟩ :=
    ⟨ObjectProperty.isoMk (perfectTwoTermComplexProperty A) e⟩
  have he : Iso.refl _ ≪≫ (perfectTwoTermComplexProperty A).ι.mapIso b.iso = e :=
    (Iso.refl_trans _).trans (ι_mapIso_isoMk (K := PerfectTwoTermComplex.baseChange φ K) e)
  rw [← baseChangeMap_refl_eq_detBaseChange]
  refine (congrArg (fun e' => baseChangeMap φ K L e' x) he.symm).trans ?_
  exact baseChangeMap_trans φ (L := PerfectTwoTermComplex.baseChange φ K) (Iso.refl _) b x


end TwoTermDeterminant

end
