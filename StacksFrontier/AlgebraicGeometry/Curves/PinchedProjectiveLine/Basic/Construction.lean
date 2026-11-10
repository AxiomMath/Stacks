module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.CoordinateRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineFiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSections
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSeparated
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.Separated
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Irreducible.GenericPoints
import all StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSections

/-!
# The pinched projective line: construction

The gluing of `Spec A`, for `A` the subring of `K[X]` of polynomials whose constant
coefficient lies in `k`, to `Spec K[Y]` along `Spec K[T, T⁻¹]`; its two charts and their
gluing relations, its structure morphism to `Spec k`, and the morphism to it from the
projective line over `K`. All declarations except the general `eqToHom` lemma
`AlgebraicGeometry.eqToHom_comp_comp_eqToHom_trans` are private; they are used by
`AlgebraicGeometry.exists_pinchedProjectiveLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- `LocallyOfFiniteType` is local at the source. The instance is reconstructed by hand because
the generic `HasRingHomProperty` instance leaves the ring-hom property undetermined. -/
private theorem isZariskiLocalAtSource_locallyOfFiniteType :
    IsZariskiLocalAtSource @LocallyOfFiniteType :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)

attribute [local instance] isZariskiLocalAtSource_locallyOfFiniteType

/-- `LocallyQuasiFinite` is local at the source, for the same reason. -/
private theorem isZariskiLocalAtSource_locallyQuasiFinite :
    IsZariskiLocalAtSource @LocallyQuasiFinite :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.QuasiFinite)

attribute [local instance] isZariskiLocalAtSource_locallyQuasiFinite

/-- A bridge for the `eqToHom` plumbing produced by `CategoryTheory.GlueData.ofGlueData'`:
a morphism conjugated by two mutually inverse object identifications is unchanged. -/
theorem eqToHom_comp_comp_eqToHom_trans {C : Type*} [Category C] {X Y Z W : C}
    (f : Y ⟶ Z) (p : X = Y) (q : Z = W) (r : W = Z) (s : X = Y) :
    eqToHom p ≫ f ≫ eqToHom q ≫ eqToHom r = eqToHom s ≫ f := by
  subst p q
  simp

open scoped Classical in
private noncomputable def pinchedGluingData' : CategoryTheory.GlueData' Scheme.{u} where
  J := ULift.{u} Bool
  U i := match i with
    | ⟨false⟩ => Spec (.of (pinchedPolynomialRing k K))
    | ⟨true⟩ => Spec (.of (Polynomial K))
  V _ _ _ := Spec (.of (LaurentPolynomial K))
  f i _ _ := match i with
    | ⟨false⟩ => pinchedPuncturedChart k K
    | ⟨true⟩ => projectiveLinePuncturedChart K
  f_mono := by
    intro i j hij
    obtain ⟨i⟩ := i
    cases i <;> infer_instance
  t i _ _ := match i with
    | ⟨false⟩ => (projectiveLineInversionIso K).hom
    | ⟨true⟩ => (projectiveLineInversionIso K).inv
  t' i j m hij hik hjk := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain ⟨m⟩ := m
    cases i <;> cases j <;> cases m
    all_goals first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim
  t_fac i j m hij hik hjk := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain ⟨m⟩ := m
    cases i <;> cases j <;> cases m
    all_goals first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim
  t_inv i j hij := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact projectiveLineInversionIso K |>.hom_inv_id
    · exact projectiveLineInversionIso K |>.inv_hom_id
    · exact (hij rfl).elim
  cocycle i j m hij hik hjk := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain ⟨m⟩ := m
    cases i <;> cases j <;> cases m
    all_goals first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim

private theorem pinchedGluingData'_f_open (i j : (pinchedGluingData' k K).J)
    (h : i ≠ j) : IsOpenImmersion ((pinchedGluingData' k K).f i j h) := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  cases i <;> cases j
  · exact (h rfl).elim
  · exact isOpenImmersion_pinchedPuncturedChart k K
  · change IsOpenImmersion
      (projectiveLinePuncturedChart K)
    infer_instance
  · exact (h rfl).elim

open scoped Classical in
private noncomputable def pinchedGluingData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (pinchedGluingData' k K)
  f_open := by
    intro i j
    change IsOpenImmersion ((pinchedGluingData' k K).f' i j)
    by_cases hij : i = j
    · subst j
      dsimp only [CategoryTheory.GlueData'.f']
      split_ifs <;> first | infer_instance | contradiction
    · dsimp only [CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact (hij h).elim
      · let : IsOpenImmersion ((pinchedGluingData' k K).f i j h) :=
          pinchedGluingData'_f_open k K i j h
        infer_instance

private abbrev pinchedIndexA : ULift.{u} Bool := ULift.up false

private abbrev pinchedIndexB : ULift.{u} Bool := ULift.up true

private abbrev pinchedCurve : Scheme.{u} := (pinchedGluingData k K).glued

private abbrev pinchedChartA : Spec (.of (pinchedPolynomialRing k K)) ⟶ pinchedCurve k K :=
  (pinchedGluingData k K).ι (pinchedIndexA)

private abbrev pinchedChartB : Spec (.of (Polynomial K)) ⟶ pinchedCurve k K :=
  (pinchedGluingData k K).ι (pinchedIndexB)

private theorem pinchedOverlap_type :
    (pinchedGluingData k K).V
      (pinchedIndexA, pinchedIndexB) = Spec (.of (LaurentPolynomial K)) := by
  dsimp [pinchedGluingData, CategoryTheory.GlueData.ofGlueData',
    pinchedGluingData', pinchedIndexA, pinchedIndexB]
  simp

private theorem pinchedOverlap_type_symm :
    (pinchedGluingData k K).V
      (pinchedIndexB, pinchedIndexA) = Spec (.of (LaurentPolynomial K)) := by
  dsimp [pinchedGluingData, CategoryTheory.GlueData.ofGlueData',
    pinchedGluingData', pinchedIndexA, pinchedIndexB]
  simp

private noncomputable def pinchedOverlapIsoA :
    (pinchedGluingData k K).V (pinchedIndexA, pinchedIndexB) ≅
      Spec (.of (LaurentPolynomial K)) := eqToIso (pinchedOverlap_type k K)

private noncomputable def pinchedOverlapIsoB :
    (pinchedGluingData k K).V (pinchedIndexB, pinchedIndexA) ≅
      Spec (.of (LaurentPolynomial K)) := eqToIso (pinchedOverlap_type_symm k K)

private theorem pinchedOverlap_f_A :
    (pinchedGluingData k K).f (pinchedIndexA) (pinchedIndexB) =
      (pinchedOverlapIsoA k K).hom ≫ pinchedPuncturedChart k K := by
  change (CategoryTheory.GlueData'.f' (pinchedGluingData' k K)
    (pinchedIndexA) (pinchedIndexB)) = _
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with h
  · cases h
  · change eqToHom (dite_eq_right h) ≫ pinchedPuncturedChart k K =
      eqToHom (pinchedOverlap_type k K) ≫ pinchedPuncturedChart k K
    exact congrArg (· ≫ pinchedPuncturedChart k K) (congrArg eqToHom (Subsingleton.elim _ _))

private theorem pinchedOverlap_f_B :
    (pinchedGluingData k K).f (pinchedIndexB) (pinchedIndexA) =
      (pinchedOverlapIsoB k K).hom ≫
        projectiveLinePuncturedChart K := by
  change (CategoryTheory.GlueData'.f' (pinchedGluingData' k K)
    (pinchedIndexB) (pinchedIndexA)) = _
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with h
  · cases h
  · change eqToHom (dite_eq_right h) ≫
        projectiveLinePuncturedChart K =
      eqToHom (pinchedOverlap_type_symm k K) ≫
        projectiveLinePuncturedChart K
    exact congrArg (· ≫ projectiveLinePuncturedChart K) (congrArg eqToHom (Subsingleton.elim _ _))

private theorem pinchedOverlap_transition :
    (pinchedGluingData k K).t (pinchedIndexA) (pinchedIndexB) ≫
        (pinchedOverlapIsoB k K).hom =
      (pinchedOverlapIsoA k K).hom ≫
        (projectiveLineInversionIso K).hom := by
  simp only [pinchedOverlapIsoA, pinchedOverlapIsoB, eqToIso.hom]
  simp only [pinchedGluingData, pinchedGluingData', ne_eq, GlueData.ofGlueData', dite_eq_ite,
    pinchedIndexA, pinchedIndexB, ULift.up.injEq, Bool.false_eq_true, ↓reduceDIte,
    Category.assoc]
  exact eqToHom_comp_comp_eqToHom_trans _ _ _ _ _

private theorem pinchedCharts_cover :
    Set.range (pinchedChartA k K).base ∪ Set.range (pinchedChartB k K).base = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨⟨i⟩, y, hy⟩ := (pinchedGluingData k K).ι_jointly_surjective x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

private theorem pinchedCharts_glue :
    pinchedPuncturedChart k K ≫ pinchedChartA k K =
      (projectiveLineInversionIso K).hom ≫
        projectiveLinePuncturedChart K ≫
          pinchedChartB k K := by
  apply (cancel_epi (pinchedOverlapIsoA k K).hom).mp
  have h := (pinchedGluingData k K).glue_condition pinchedIndexA pinchedIndexB
  rw [pinchedOverlap_f_A, pinchedOverlap_f_B] at h
  calc (pinchedOverlapIsoA k K).hom ≫ pinchedPuncturedChart k K ≫ pinchedChartA k K
      = ((pinchedOverlapIsoA k K).hom ≫ pinchedPuncturedChart k K) ≫ pinchedChartA k K :=
        (Category.assoc _ _ _).symm
    _ = (pinchedGluingData k K).t pinchedIndexA pinchedIndexB ≫
          ((pinchedOverlapIsoB k K).hom ≫ projectiveLinePuncturedChart K) ≫
            pinchedChartB k K := h.symm
    _ = ((pinchedGluingData k K).t pinchedIndexA pinchedIndexB ≫
            (pinchedOverlapIsoB k K).hom) ≫
          projectiveLinePuncturedChart K ≫ pinchedChartB k K := by
        simp only [Category.assoc]
    _ = ((pinchedOverlapIsoA k K).hom ≫ (projectiveLineInversionIso K).hom) ≫
          projectiveLinePuncturedChart K ≫ pinchedChartB k K := by
        rw [pinchedOverlap_transition]
    _ = (pinchedOverlapIsoA k K).hom ≫ (projectiveLineInversionIso K).hom ≫
          projectiveLinePuncturedChart K ≫ pinchedChartB k K := Category.assoc _ _ _

private theorem pinchedCharts_isPullback :
    IsPullback (pinchedPuncturedChart k K)
      ((projectiveLineInversionIso K).hom ≫
        projectiveLinePuncturedChart K)
      (pinchedChartA k K) (pinchedChartB k K) := by
  have h := IsPullback.of_isLimit
    ((pinchedGluingData k K).vPullbackConeIsLimit pinchedIndexA pinchedIndexB)
  refine h.of_iso (pinchedOverlapIsoA k K) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · change (pinchedGluingData k K).f pinchedIndexA pinchedIndexB ≫ 𝟙 _ =
      (pinchedOverlapIsoA k K).hom ≫ pinchedPuncturedChart k K
    exact (Category.comp_id _).trans (pinchedOverlap_f_A k K)
  · change ((pinchedGluingData k K).t pinchedIndexA pinchedIndexB ≫
        (pinchedGluingData k K).f pinchedIndexB pinchedIndexA) ≫ 𝟙 _ =
      (pinchedOverlapIsoA k K).hom ≫
        ((projectiveLineInversionIso K).hom ≫ projectiveLinePuncturedChart K)
    rw [Category.comp_id, pinchedOverlap_f_B]
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun m => m ≫ projectiveLinePuncturedChart K)
      (pinchedOverlap_transition k K)) ?_
    exact Category.assoc _ _ _
  · change (pinchedGluingData k K).ι pinchedIndexA ≫ 𝟙 _ = 𝟙 _ ≫ pinchedChartA k K
    rw [Category.comp_id, Category.id_comp]
  · change (pinchedGluingData k K).ι pinchedIndexB ≫ 𝟙 _ = 𝟙 _ ≫ pinchedChartB k K
    rw [Category.comp_id, Category.id_comp]

private theorem pinchedCharts_lift_isIso :
    IsIso (pullback.lift (pinchedPuncturedChart k K)
      ((projectiveLineInversionIso K).hom ≫
        projectiveLinePuncturedChart K)
      (pinchedCharts_glue k K)) := by
  have he : pullback.lift (pinchedPuncturedChart k K)
      ((projectiveLineInversionIso K).hom ≫
        projectiveLinePuncturedChart K)
      (pinchedCharts_glue k K) = (pinchedCharts_isPullback k K).isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans
        (pinchedCharts_isPullback k K).isoPullback_hom_fst.symm
    · exact (pullback.lift_snd _ _ _).trans
        (pinchedCharts_isPullback k K).isoPullback_hom_snd.symm
  rw [he]
  infer_instance

/-- The compatibility condition of a family of maps out of the charts of a two-chart glue datum
only needs to be checked for the two ordered pairs of distinct charts. -/
private theorem glueData_compat_of_two {D : Scheme.GlueData.{u}} {Y : Scheme.{u}}
    (g : ∀ i, D.U i ⟶ Y) (a b : D.J) (hJ : ∀ i, i = a ∨ i = b)
    (hab : D.f a b ≫ g a = D.t a b ≫ D.f b a ≫ g b)
    (hba : D.f b a ≫ g b = D.t b a ≫ D.f a b ≫ g a) (ij : D.J × D.J) :
    D.f ij.1 ij.2 ≫ g ij.1 = D.t ij.1 ij.2 ≫ D.f ij.2 ij.1 ≫ g ij.2 := by
  obtain ⟨i, j⟩ := ij
  rcases hJ i with rfl | rfl <;> rcases hJ j with rfl | rfl <;> first | assumption | simp

private noncomputable def pinchedStructureMorphism :
    { f : pinchedCurve k K ⟶ Spec (.of k) //
      pinchedChartA k K ≫ f =
        Spec.map (CommRingCat.ofHom (pinchedPolynomialConstant k K)) ∧
      pinchedChartB k K ≫ f = Spec.map (CommRingCat.ofHom
        ((Polynomial.C : K →+* Polynomial K).comp (algebraMap k K))) } := by
  let D := pinchedGluingData k K
  let g : ∀ i : D.J, D.U i ⟶ Spec (.of k) := fun ⟨i⟩ =>
    match i with
    | false => Spec.map (CommRingCat.ofHom (pinchedPolynomialConstant k K))
    | true => Spec.map (CommRingCat.ofHom
        ((Polynomial.C : K →+* Polynomial K).comp (algebraMap k K)))
  have hg : ∀ a : D.J × D.J,
      D.f a.1 a.2 ≫ g a.1 = D.t a.1 a.2 ≫ D.f a.2 a.1 ≫ g a.2 := by
    refine glueData_compat_of_two g pinchedIndexA pinchedIndexB
      (by rintro ⟨_ | _⟩ <;> [exact .inl rfl; exact .inr rfl]) ?_ ?_
    · simp only [pinchedGluingData, pinchedGluingData', ne_eq, pinchedPuncturedChart,
        projectiveLinePuncturedChart, projectiveLineInversionIso, Functor.mapIso_hom,
        Scheme.Spec_map, Functor.mapIso_inv, GlueData.ofGlueData', dite_eq_ite, GlueData'.f',
        ULift.up.injEq, Bool.false_eq_true, ↓reduceDIte, CommRingCat.ofHom_comp,
        Category.assoc, ← Spec.map_comp, Bool.true_eq_false, Iso.op_hom,
        RingEquiv.toCommRingCatIso_hom, AlgEquiv.toRingEquiv_toRingHom, Quiver.Hom.unop_op,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_comp_iff, D, g]
      apply Spec.map_inj.mpr
      ext a
      simp [pinchedPolynomialConstant, pinchedToLaurent, Polynomial.toLaurent_C,
        LaurentPolynomial.invert_C]
    · simp only [pinchedGluingData, pinchedGluingData', ne_eq, pinchedPuncturedChart,
        projectiveLinePuncturedChart, projectiveLineInversionIso, Functor.mapIso_hom,
        Scheme.Spec_map, Functor.mapIso_inv, GlueData.ofGlueData', dite_eq_ite, GlueData'.f',
        ULift.up.injEq, Bool.true_eq_false, ↓reduceDIte, CommRingCat.ofHom_comp,
        Category.assoc, ← Spec.map_comp, Bool.false_eq_true, Iso.op_inv,
        RingEquiv.toCommRingCatIso_inv, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
        AlgEquiv.symm_toEquiv_eq_symm, LaurentPolynomial.invert_symm, Quiver.Hom.unop_op,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_comp_iff, D, g]
      apply Spec.map_inj.mpr
      ext a
      simp [pinchedPolynomialConstant, pinchedToLaurent, Polynomial.toLaurent_C,
        LaurentPolynomial.invert_C]
  refine ⟨Multicoequalizer.desc D.toGlueData.diagram _ g hg, ?_, ?_⟩
  · exact Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _ pinchedIndexA
  · exact Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _ pinchedIndexB

private noncomputable def projectiveLineDesc {Y : Scheme.{u}}
    (a b : Spec (.of (Polynomial K)) ⟶ Y)
    (hab : projectiveLinePuncturedChart K ≫ a =
      (projectiveLineInversionIso K).hom ≫
        projectiveLinePuncturedChart K ≫ b) :
    {ν : projectiveLine K ⟶ Y //
      projectiveLineXChart K ≫ ν = a ∧
      projectiveLineYChart K ≫ ν = b} := by
  let D := projectiveLineGluingData K
  let g : ∀ i : D.J, D.U i ⟶ Y := fun ⟨i⟩ => if i then b else a
  have hg : ∀ ij : D.J × D.J,
      D.f ij.1 ij.2 ≫ g ij.1 = D.t ij.1 ij.2 ≫ D.f ij.2 ij.1 ≫ g ij.2 := by
    refine glueData_compat_of_two g (projectiveLineXIndex K) (projectiveLineYIndex K)
      (by rintro ⟨_ | _⟩ <;> [exact .inl rfl; exact .inr rfl]) ?_ ?_
    · simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
        GlueData.ofGlueData', dite_eq_ite, GlueData'.f', ULift.up.injEq, Bool.false_eq_true,
        ↓reduceDIte, ↓reduceIte, Category.assoc, Bool.true_eq_false, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, eqToHom_comp_iff, D, g]
      exact hab
    · simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
        GlueData.ofGlueData', dite_eq_ite, GlueData'.f', ULift.up.injEq, Bool.true_eq_false,
        ↓reduceDIte, ↓reduceIte, Category.assoc, Bool.false_eq_true, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, eqToHom_comp_iff, D, g]
      rw [hab, Iso.inv_hom_id_assoc]
  refine ⟨Multicoequalizer.desc D.toGlueData.diagram _ g hg, ?_, ?_⟩
  · exact Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _
      (projectiveLineXIndex K)
  · exact Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _
      (projectiveLineYIndex K)

private noncomputable def pinchedNormalizationMorphism :
    {ν : projectiveLine K ⟶ pinchedCurve k K //
      projectiveLineXChart K ≫ ν =
        pinchedNormalizationAffineChart k K ≫ pinchedChartA k K ∧
      projectiveLineYChart K ≫ ν =
        pinchedChartB k K} :=
  projectiveLineDesc K
    (pinchedNormalizationAffineChart k K ≫ pinchedChartA k K)
    (pinchedChartB k K) (by
      rw [← Category.assoc, projectiveLinePuncturedChart_comp_pinchedNormalizationAffineChart]
      exact pinchedCharts_glue k K)

end AlgebraicGeometry

end
