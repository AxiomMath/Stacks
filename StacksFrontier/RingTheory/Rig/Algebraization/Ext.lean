module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Homology.TwoTermComplex.Determinant
public import StacksFrontier.Homology.TwoTermComplex.Morphisms
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# The Jacobian determinant on a truncated presentation complex

Let `B` be the quotient of a polynomial algebra `A[x₀, …, xₙ₋₁]` by `m` relations
`f₀, …, fₘ₋₁`, where `m ≤ n`.  Writing the degree-zero term of the presentation model for the
naive cotangent complex in the basis of polynomial differentials and truncating it to the
first `m` coordinates gives a two-term complex `L` with a square Jacobian matrix for its
differential.  The adjugate of that Jacobian provides a null homotopy of multiplication by its
determinant, so the determinant acts by zero on `L` in the derived category of `B`-modules.

## Main definitions

* `Rig.PresentationQuotient` — the quotient `A[x₀, …, xₙ₋₁] / (f₀, …, fₘ₋₁)`.
* `Rig.presentation` — its polynomial presentation by the images of the variables.
* `Rig.coordinatePresentation` — the presentation complex, with the degree-zero term written in
  the basis of polynomial differentials.
* `Rig.truncatedPresentation` — the two-term complex with conormal module in degree `1` and the
  first `m` polynomial differentials in degree `0`.
* `Rig.truncatedPresentationCochain` — the same complex in cohomological degrees `-1` and `0`.
* `Rig.jacobian` — the square Jacobian formed from the first `m` variables.

## Main results

* `Rig.coordinatePresentationComparison_isQuasiIso` — the full coordinate presentation
  represents the naive cotangent complex.
* `Rig.coordinatePresentationToPresentation_isHomotopyEquiv` — passing to the basis of
  polynomial differentials is a homotopy equivalence.
* `Rig.truncatedPresentation_eq_coordinatePresentation` — when the number of equations equals
  the number of variables, the truncated and full presentation complexes agree.
* `Rig.jacobianDet_smul_truncatedPresentation_eq_zero` — the Jacobian determinant acts by zero
  in the derived category.

## Implementation notes

The comparison from the coordinate presentation to
`NaiveCotangent.NL (NaiveCotangent.canonicalGenerators ..)` is the basis isomorphism followed
by the canonical comparison of presentations.  Its quasi-isomorphism assertion is the precise
meaning of saying that the coordinate complex represents `Algebra.naiveCotangentComplex A B`.
Restricting the coordinates of the differential to `Fin m` gives the truncated complex `L` of
the source.

## References

* [Stacks Project, Section 92.11 (tag 08R6)](https://stacks.math.columbia.edu/tag/08R6)
-/

@[expose] public section

open CategoryTheory MvPolynomial
open ComplexShape (upIntRelNegOneZero)

attribute [local instance] HasDerivedCategory.standard

namespace Rig

universe u

variable {A : Type u} [CommRing A] {n m : ℕ}

/-- The quotient `A[x₀, …, xₙ₋₁] / (f₀, …, fₘ₋₁)`. -/
public abbrev PresentationQuotient (f : Fin m → MvPolynomial (Fin n) A) :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)

/-- The presentation of the quotient by the images of the polynomial variables. -/
public noncomputable def presentation (f : Fin m → MvPolynomial (Fin n) A) :
    Algebra.Generators A (PresentationQuotient f) (Fin n) :=
  Algebra.Generators.ofSurjective
    (fun i ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X i))
    (by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨p, ?_⟩
      change MvPolynomial.aeval
          (fun i ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X i)) p =
        (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f))) p
      congr 1
      apply MvPolynomial.algHom_ext
      intro i
      simp)

/-- The full presentation complex `J/J² → ⊕ᵢ B dxᵢ`, with its degree-zero term
written in the basis of polynomial differentials. -/
public noncomputable def coordinatePresentation
    (f : Fin m → MvPolynomial (Fin n) A) :
    NaiveCotangent.TwoTerm (PresentationQuotient f) where
  X₁ := (presentation f).toExtension.Cotangent
  X₀ := Fin n → PresentationQuotient f
  d := LinearMap.pi fun i ↦
    (Finsupp.lapply i) ∘ₗ
      (presentation f).cotangentSpaceBasis.repr.toLinearMap ∘ₗ
      (presentation f).toExtension.cotangentComplex

/-- The basis isomorphism from the coordinate presentation to the presentation complex
whose degree-zero term is the cotangent space. -/
public noncomputable def coordinatePresentationToPresentation
    (f : Fin m → MvPolynomial (Fin n) A) :
    NaiveCotangent.ChainMap (coordinatePresentation f)
      (NaiveCotangent.NL (presentation f)) where
  f₁ := LinearMap.id
  f₀ := (presentation f).cotangentSpaceBasis.equivFun.symm.toLinearMap
  comm := by
    ext x
    change (presentation f).toExtension.cotangentComplex x =
      (presentation f).cotangentSpaceBasis.equivFun.symm
        (fun i ↦ (presentation f).cotangentSpaceBasis.repr
          ((presentation f).toExtension.cotangentComplex x) i)
    rw [show (fun i ↦ (presentation f).cotangentSpaceBasis.repr
      ((presentation f).toExtension.cotangentComplex x) i) =
        (presentation f).cotangentSpaceBasis.equivFun
          ((presentation f).toExtension.cotangentComplex x) by rfl]
    exact ((presentation f).cotangentSpaceBasis.equivFun.symm_apply_apply
      ((presentation f).toExtension.cotangentComplex x)).symm

/-- The comparison from the full coordinate presentation to the canonical naive
cotangent complex. -/
public noncomputable def coordinatePresentationComparison
    (f : Fin m → MvPolynomial (Fin n) A) :
    NaiveCotangent.ChainMap (coordinatePresentation f)
      (NaiveCotangent.NL (NaiveCotangent.canonicalGenerators A (PresentationQuotient f))) :=
  (NaiveCotangent.nlMap (presentation f)
    (NaiveCotangent.canonicalGenerators A (PresentationQuotient f))
    ((presentation f).defaultHom
      (NaiveCotangent.canonicalGenerators A (PresentationQuotient f)))).comp
    (coordinatePresentationToPresentation f)

private lemma isQuasiIso_comp {S : Type*} [CommRing S]
    {X Y Z : NaiveCotangent.TwoTerm S}
    (g : NaiveCotangent.ChainMap Y Z) (h : NaiveCotangent.IsQuasiIso g)
    (f : NaiveCotangent.ChainMap X Y) (hf : NaiveCotangent.IsQuasiIso f) :
    NaiveCotangent.IsQuasiIso (g.comp f) := by
  constructor
  · rw [NaiveCotangent.ChainMap.onH₁_comp]
    exact h.1.comp hf.1
  · rw [NaiveCotangent.ChainMap.onH₀_comp]
    exact h.2.comp hf.2

/-- Equal chain maps of two-term complexes are homotopic, via the zero homotopy. -/
public lemma homotopic_of_eq {S : Type*} [CommRing S]
    {X Y : NaiveCotangent.TwoTerm S} {f g : NaiveCotangent.ChainMap X Y} (h : f = g) :
    NaiveCotangent.Homotopic f g := by
  subst g
  refine ⟨0, ?_, ?_⟩ <;> simp

/-- The inverse of the basis isomorphism `coordinatePresentationToPresentation`. -/
public noncomputable def presentationToCoordinatePresentation
    (f : Fin m → MvPolynomial (Fin n) A) :
    NaiveCotangent.ChainMap (NaiveCotangent.NL (presentation f))
      (coordinatePresentation f) where
  f₁ := LinearMap.id
  f₀ := (presentation f).cotangentSpaceBasis.equivFun.toLinearMap
  comm := LinearMap.ext fun _ ↦ funext fun _ ↦ rfl

/-- Writing the degree-zero term of the presentation complex in the basis of polynomial
differentials is a homotopy equivalence, with inverse
`presentationToCoordinatePresentation`. -/
public lemma coordinatePresentationToPresentation_isHomotopyEquiv
    (f : Fin m → MvPolynomial (Fin n) A) :
    NaiveCotangent.IsHomotopyEquiv (coordinatePresentationToPresentation f) := by
  refine ⟨presentationToCoordinatePresentation f,
    homotopic_of_eq (NaiveCotangent.ChainMap.ext rfl (LinearMap.ext fun x ↦ ?_)),
    homotopic_of_eq (NaiveCotangent.ChainMap.ext rfl (LinearMap.ext fun x ↦ ?_))⟩
  · exact (presentation f).cotangentSpaceBasis.equivFun.apply_symm_apply x
  · exact (presentation f).cotangentSpaceBasis.equivFun.symm_apply_apply x

/-- The full coordinate presentation represents the naive cotangent complex of the
quotient algebra. -/
public lemma coordinatePresentationComparison_isQuasiIso
    (f : Fin m → MvPolynomial (Fin n) A) :
    NaiveCotangent.IsQuasiIso (coordinatePresentationComparison f) :=
  isQuasiIso_comp _
    (NaiveCotangent.nlMap_canonical_isQuasiIso _ _) _
    (NaiveCotangent.isQuasiIso_of_isHomotopyEquiv
      (coordinatePresentationToPresentation_isHomotopyEquiv f))

/-- The differential of the truncated presentation complex: the conormal module
`J/J² = (presentation f).toExtension.Cotangent` maps to the first `m` coordinates of the
polynomial differentials.

This is the differential of `truncatedPresentation` below, named separately so that the
Jacobian computations can be carried out on the underlying modules. -/
public noncomputable def truncatedDifferential (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (presentation f).toExtension.Cotangent →ₗ[PresentationQuotient f]
      (Fin m → PresentationQuotient f) :=
  LinearMap.pi fun i ↦
    (Finsupp.lapply (Fin.castLE hm i)) ∘ₗ
      (presentation f).cotangentSpaceBasis.repr.toLinearMap ∘ₗ
      (presentation f).toExtension.cotangentComplex

/-- The presentation complex truncated in degree zero to the first `m` differentials.
Its degree-one term is `J/J²`, represented by the cotangent module of the presentation. -/
public noncomputable def truncatedPresentation (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    NaiveCotangent.TwoTerm (PresentationQuotient f) where
  X₁ := (presentation f).toExtension.Cotangent
  X₀ := Fin m → PresentationQuotient f
  d := truncatedDifferential hm f

/-- For a square presentation, truncating to the first `n` coordinates recovers the
full coordinate presentation. -/
public lemma truncatedPresentation_eq_coordinatePresentation
    (f : Fin n → MvPolynomial (Fin n) A) :
    truncatedPresentation (le_refl n) f = coordinatePresentation f :=
  rfl

/-- The truncated presentation as a cochain complex in degrees `-1` and `0`.

This is `@[reducible]` so that the degree isomorphisms of the underlying
`HomologicalComplex.double` apply to it directly. -/
@[reducible]
public noncomputable def truncatedPresentationCochain (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    CochainComplex (ModuleCat (PresentationQuotient f)) ℤ :=
  HomologicalComplex.double
    (ModuleCat.ofHom (truncatedDifferential hm f))
    upIntRelNegOneZero

/-- The square Jacobian formed from the first `m` variables. -/
public noncomputable def jacobian (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) A) :=
  Matrix.of fun i j ↦ MvPolynomial.pderiv (Fin.castLE hm i) (f j)

private lemma presentation_aeval (f : Fin m → MvPolynomial (Fin n) A) :
    MvPolynomial.aeval (presentation f).val =
      Ideal.Quotient.mkₐ A (Ideal.span (Set.range f)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [presentation]

private lemma presentation_ker (f : Fin m → MvPolynomial (Fin n) A) :
    (presentation f).toExtension.ker = Ideal.span (Set.range f) := by
  rw [show (presentation f).toExtension.ker = (presentation f).ker by rfl,
    (presentation f).ker_eq_ker_aeval_val, presentation_aeval f]
  exact Ideal.Quotient.mkₐ_ker (R₁ := A) (Ideal.span (Set.range f))

private def relation (f : Fin m → MvPolynomial (Fin n) A) (j : Fin m) :
    (presentation f).toExtension.ker :=
  ⟨f j, (presentation_ker f).symm ▸ Ideal.subset_span ⟨j, rfl⟩⟩

private noncomputable def relationMap (f : Fin m → MvPolynomial (Fin n) A) :
    (Fin m → PresentationQuotient f) →ₗ[PresentationQuotient f]
      (presentation f).toExtension.Cotangent :=
  Fintype.linearCombination _ (fun j ↦ Algebra.Extension.Cotangent.mk (relation f j))

private lemma relationMap_surjective (f : Fin m → MvPolynomial (Fin n) A) :
    Function.Surjective (relationMap f) := by
  apply (span_range_eq_top_iff_surjective_fintypeLinearCombination
    (PresentationQuotient f)
    (fun j ↦ Algebra.Extension.Cotangent.mk (relation f j))).mp
  simpa only [relationMap, relation] using
    (Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
      (P := (presentation f).toExtension) f (presentation_ker f).symm)

private lemma truncated_d_relation (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) (j i : Fin m) :
    truncatedDifferential hm f
        (Algebra.Extension.Cotangent.mk (relation f j)) i =
      Ideal.Quotient.mk (Ideal.span (Set.range f))
        (MvPolynomial.pderiv (Fin.castLE hm i) (f j)) := by
  have h := (presentation f).cotangentRestrict_mk (Fin.castLE_injective hm) (relation f j)
  have hi := congrArg (fun v : Fin m → PresentationQuotient f ↦ v i) h
  rwa [presentation_aeval f] at hi

private lemma truncated_d_comp_relationMap (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (truncatedDifferential hm f) ∘ₗ relationMap f =
      ((jacobian hm f).map
        (Ideal.Quotient.mk (Ideal.span (Set.range f)))).mulVecLin := by
  apply LinearMap.pi_ext
  intro j r
  funext i
  change truncatedDifferential hm f (relationMap f (Pi.single j r)) i =
    (((jacobian hm f).map
      (Ideal.Quotient.mk (Ideal.span (Set.range f)))).mulVecLin (Pi.single j r)) i
  rw [show relationMap f (Pi.single j r) =
      r • Algebra.Extension.Cotangent.mk (relation f j) by
        exact Fintype.linearCombination_apply_single _ _ _ _]
  rw [map_smul, Pi.smul_apply, truncated_d_relation]
  simp only [jacobian, smul_eq_mul, Matrix.mulVecBilin_apply, Matrix.mulVec_single,
    Pi.smul_apply, Matrix.col_apply, Matrix.map_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  exact mul_comm _ _

private noncomputable def jacobianHomotopy (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (Fin m → PresentationQuotient f) →ₗ[PresentationQuotient f]
      (presentation f).toExtension.Cotangent :=
  (relationMap f).comp
    (((jacobian hm f).map
      (Ideal.Quotient.mk (Ideal.span (Set.range f)))).adjugate.mulVecLin)

private lemma jacobianHomotopy_comp_d (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (truncatedDifferential hm f) ∘ₗ jacobianHomotopy hm f =
      (((jacobian hm f).map
        (Ideal.Quotient.mk (Ideal.span (Set.range f)))).det) • LinearMap.id := by
  let M := (jacobian hm f).map
    (Ideal.Quotient.mk (Ideal.span (Set.range f)))
  apply LinearMap.ext
  intro v
  have hd := LinearMap.congr_fun (truncated_d_comp_relationMap hm f)
    (M.adjugate.mulVecLin v)
  change truncatedDifferential hm f ((relationMap f) (M.adjugate.mulVecLin v)) =
    M.mulVecLin (M.adjugate.mulVecLin v) at hd
  change truncatedDifferential hm f ((relationMap f) (M.adjugate.mulVecLin v)) =
    (M.det • LinearMap.id) v
  rw [hd]
  change M.mulVec (M.adjugate.mulVec v) = M.det • v
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec]

private lemma d_comp_jacobianHomotopy (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    jacobianHomotopy hm f ∘ₗ truncatedDifferential hm f =
      (((jacobian hm f).map
        (Ideal.Quotient.mk (Ideal.span (Set.range f)))).det) • LinearMap.id := by
  let M := (jacobian hm f).map
    (Ideal.Quotient.mk (Ideal.span (Set.range f)))
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := relationMap_surjective f x
  change (relationMap f) (M.adjugate.mulVecLin
    (truncatedDifferential hm f ((relationMap f) v))) =
    (M.det • LinearMap.id) ((relationMap f) v)
  have hd := LinearMap.congr_fun (truncated_d_comp_relationMap hm f) v
  change truncatedDifferential hm f ((relationMap f) v) = M.mulVecLin v at hd
  rw [hd]
  change (relationMap f) (M.adjugate.mulVec (M.mulVec v)) =
    M.det • (relationMap f) v
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, map_smul]

private lemma jacobianHomotopy_comp_d_ofHom (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    ModuleCat.ofHom (truncatedDifferential hm f) ≫
      ModuleCat.ofHom (jacobianHomotopy hm f) =
        (((jacobian hm f).map
          (Ideal.Quotient.mk (Ideal.span (Set.range f)))).det) •
          𝟙 (ModuleCat.of (PresentationQuotient f)
            (presentation f).toExtension.Cotangent) := by
  rw [← ModuleCat.ofHom_comp, d_comp_jacobianHomotopy]
  rfl

private lemma d_comp_jacobianHomotopy_ofHom (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    ModuleCat.ofHom (jacobianHomotopy hm f) ≫
      ModuleCat.ofHom (truncatedDifferential hm f) =
        (((jacobian hm f).map
          (Ideal.Quotient.mk (Ideal.span (Set.range f)))).det) •
          𝟙 (ModuleCat.of (PresentationQuotient f) (Fin m → PresentationQuotient f)) := by
  rw [← ModuleCat.ofHom_comp, jacobianHomotopy_comp_d]
  rfl

private noncomputable def jacobianHomotopyComponent (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) (i j : ℤ) :
    (truncatedPresentationCochain hm f).X i ⟶
      (truncatedPresentationCochain hm f).X j :=
  if hi : i = 0 then
    if hj : j = -1 then by
      subst hi hj
      exact (HomologicalComplex.doubleXIso₁
        (ModuleCat.ofHom (truncatedDifferential hm f))
        upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫
        ModuleCat.ofHom (jacobianHomotopy hm f) ≫
        (HomologicalComplex.doubleXIso₀
          (ModuleCat.ofHom (truncatedDifferential hm f))
          upIntRelNegOneZero).inv
    else 0
  else 0

private lemma jacobianHomotopyComponent_eq_zero (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) {i j : ℤ}
    (h : ¬(i = 0 ∧ j = -1)) : jacobianHomotopyComponent hm f i j = 0 := by
  unfold jacobianHomotopyComponent
  by_cases hi : i = 0
  · by_cases hj : j = -1
    · exact False.elim (h ⟨hi, hj⟩)
    · simp [hi, hj]
  · simp [hi]

private lemma iso_hom_smul_id_comp_inv {S : Type*} [CommRing S]
    {X Y : ModuleCat S} (e : X ≅ Y) (s : S) :
    e.hom ≫ (s • 𝟙 Y) ≫ e.inv = s • 𝟙 X := by
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp,
    e.hom_inv_id]

private noncomputable def jacobianNullHomotopy (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    Homotopy
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) (jacobian hm f).det •
        𝟙 (truncatedPresentationCochain hm f)) 0 where
  hom := jacobianHomotopyComponent hm f
  zero i j h := jacobianHomotopyComponent_eq_zero hm f (by
    rintro ⟨rfl, rfl⟩
    exact h rfl)
  comm i := by
    rw [show HomologicalComplex.Hom.f
      (0 : truncatedPresentationCochain hm f ⟶ truncatedPresentationCochain hm f) i = 0
      from rfl, add_zero]
    rw [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    rw [dNext_eq (jacobianHomotopyComponent hm f)
        (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq (jacobianHomotopyComponent hm f)
        (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1)]
    by_cases hi1 : i = -1
    · subst hi1
      change _ = (truncatedPresentationCochain hm f).d (-1) 0 ≫
          jacobianHomotopyComponent hm f 0 (-1) +
          jacobianHomotopyComponent hm f (-1) (-2) ≫
          (truncatedPresentationCochain hm f).d (-2) (-1)
      rw [jacobianHomotopyComponent_eq_zero hm f
          (i := -1) (j := -2) (by decide), Limits.zero_comp, add_zero]
      change _ = (HomologicalComplex.double
        (ModuleCat.ofHom (truncatedDifferential hm f))
        upIntRelNegOneZero).d (-1) 0 ≫
          jacobianHomotopyComponent hm f 0 (-1)
      rw [HomologicalComplex.double_d
        (ModuleCat.ofHom (truncatedDifferential hm f))
        upIntRelNegOneZero
        NaiveCotangent.TwoTerm.negOne_ne_zero]
      simp only [jacobianHomotopyComponent, dite_true, Category.assoc,
        Iso.inv_hom_id_assoc]
      simp only [← Category.assoc, jacobianHomotopy_comp_d_ofHom]
      rw [RingHom.map_det]
      exact (iso_hom_smul_id_comp_inv _ _).symm
    by_cases hi0 : i = 0
    · subst hi0
      change _ = (truncatedPresentationCochain hm f).d 0 1 ≫
          jacobianHomotopyComponent hm f 1 0 +
          jacobianHomotopyComponent hm f 0 (-1) ≫
          (truncatedPresentationCochain hm f).d (-1) 0
      rw [jacobianHomotopyComponent_eq_zero hm f
          (i := 1) (j := 0) (by decide), Limits.comp_zero, zero_add]
      change _ = jacobianHomotopyComponent hm f 0 (-1) ≫
        (HomologicalComplex.double
          (ModuleCat.ofHom (truncatedDifferential hm f))
          upIntRelNegOneZero).d (-1) 0
      rw [HomologicalComplex.double_d
        (ModuleCat.ofHom (truncatedDifferential hm f))
        upIntRelNegOneZero
        NaiveCotangent.TwoTerm.negOne_ne_zero]
      simp only [jacobianHomotopyComponent, dite_true, Category.assoc,
        Iso.inv_hom_id_assoc]
      simp only [← Category.assoc, d_comp_jacobianHomotopy_ofHom]
      rw [RingHom.map_det]
      exact (iso_hom_smul_id_comp_inv _ _).symm
    have hz := HomologicalComplex.isZero_double_X
      (ModuleCat.ofHom (truncatedDifferential hm f))
      upIntRelNegOneZero i hi1 hi0
    exact hz.eq_of_src _ _

/-- The determinant of the first square Jacobian, mapped to the presentation quotient,
acts trivially on the truncated presentation complex in the derived category. -/
public lemma jacobianDet_smul_truncatedPresentation_eq_zero (hm : m ≤ n)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (DerivedCategory.Q (C := ModuleCat (PresentationQuotient f))).map
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) (jacobian hm f).det •
          𝟙 (truncatedPresentationCochain hm f)) = 0 := by
  rw [DerivedCategory.Q_map_eq_of_homotopy _ (jacobianNullHomotopy hm f)]
  simp

end Rig

end
