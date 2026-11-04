module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.Criteria
public import StacksFrontier.Homology.TwoTermComplex.Representative
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

@[expose] public section

/-!
# Projective zero-th cohomology from Ext vanishing

For a derived object with cohomology concentrated in degrees `-1` and `0`, vanishing of its
degree-one Ext groups against every module is equivalent to vanishing of its degree-minus-one
cohomology and projectivity of its zero-th cohomology. Over a Noetherian ring, when both
possibly nonzero cohomology modules are finite, it suffices to test against finite modules.

Applied to the naive cotangent complex of a ring map, this is an Ext characterization of
smoothness and of formal smoothness.

## Main results

* `TwoTermComplex.projective_homology_iff_ext_one_vanishing` (Stacks 0G9C).
* `TwoTermComplex.smooth_and_formallySmooth_iff_ext_one_vanishing` (Stacks 0G9D).

## Implementation notes

Modules occurring as the second argument of Ext are placed in degree zero, and vanishing of an
Ext group is expressed by its underlying type being a subsingleton.

The naive cotangent complex is represented by the canonical polynomial presentation. Its
homological degrees `1` and `0` are placed in cohomological degrees `-1` and `0`, respectively,
before passing to the derived category.

The two-term hypothesis turns the conditions of
`StacksDraft.ProjectiveDimension.hasProjectiveAmplitude_iff_ext_vanishing` (Stacks 0A5P) at
`a = b = 0` into the statement at hand, once the degree-minus-one vanishing and the degree-zero
projectivity are recognized as projective amplitude in `[0, 0]`.

The reduction to finite test modules does not need a separate Ext-vanishing criterion: taking
the unit ideal in `TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization` (Stacks 0G9F),
annihilation of `Ext¹` by every element of `R` is the same as its vanishing, because `1` acts as
the identity, and that lemma already provides the passage between arbitrary and finite test
modules under the Noetherian and finiteness hypotheses.

## References

* [Stacks Project, Tag 0G9C](https://stacks.math.columbia.edu/tag/0G9C)
* [Stacks Project, Tag 0G9D](https://stacks.math.columbia.edu/tag/0G9D)
-/

open CategoryTheory Limits

namespace TwoTermComplex

universe u v

attribute [local instance] HasDerivedCategory.standard

open StacksDraft.ProjectiveDimension in
/-- A derived object of projective amplitude in `[0, 0]` has vanishing cohomology in degree `-1`
and projective cohomology in degree `0`. -/
private lemma projectiveHomology_of_hasProjectiveAmplitude
    {R : Type u} [CommRing R] {K : DerivedCategory (ModuleCat.{v} R)}
    (h : HasProjectiveAmplitude K 0 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) ∧
      Module.Projective R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K) := by
  obtain ⟨P, ⟨e⟩, hP, _, _⟩ := h
  obtain ⟨X, ⟨eP⟩⟩ := CochainComplex.exists_iso_single P 0
  let ePX : P.X 0 ≅ X :=
    { hom := eP.hom.f 0
      inv := eP.inv.f 0
      hom_inv_id := congrArg (fun f ↦ f.f 0) eP.hom_inv_id
      inv_hom_id := congrArg (fun f ↦ f.f 0) eP.inv_hom_id }
  have : Module.Projective R (P.X 0) := hP 0
  have : Module.Projective R X := .of_equiv ePX.toLinearEquiv
  let eH (i : ℤ) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app P ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).mapIso eP
  exact ⟨IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) 0 X (-1) (by omega)) (eH (-1)),
    Module.Projective.of_equiv
      (eH 0 ≪≫
        HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).symm.toLinearEquiv⟩

open StacksDraft.ProjectiveDimension in
/-- A two-term derived object with vanishing cohomology in degree `-1` and projective cohomology
in degree `0` has projective amplitude in `[0, 0]`. -/
private lemma hasProjectiveAmplitude_of_projectiveHomology
    {R : Type u} [CommRing R] {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (hneg : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K))
    [Module.Projective R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K)] :
    HasProjectiveAmplitude K 0 0 := by
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 fun i hi => by
    by_cases hi' : i = -1
    · simpa [hi'] using hneg
    · exact hK i hi' (by omega)
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun i hi =>
    hK i (by omega) (by omega)
  obtain ⟨X, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K ≅ X :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) 0).app X
  have : Module.Projective R X := Module.Projective.of_equiv eH.toLinearEquiv
  refine ⟨(CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj X, ?_,
    fun i => ?_, inferInstance, inferInstance⟩
  · exact ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).app X ≪≫ e.symm⟩
  · by_cases hi : i = 0
    · exact Module.Projective.of_equiv
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X i hi).symm.toLinearEquiv
    · have : Subsingleton
            (((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj X).X i) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X i hi)
      exact Module.Projective.of_free

open StacksDraft.ProjectiveDimension in
/-- For a two-term derived object, vanishing in degree `-1` together with projectivity in
degree `0` is exactly projective amplitude in `[0, 0]`. -/
private lemma projectiveHomology_iff_hasProjectiveAmplitude
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    (IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) ∧
        Module.Projective R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K)) ↔
      HasProjectiveAmplitude K 0 0 :=
  ⟨fun ⟨hneg, _⟩ => hasProjectiveAmplitude_of_projectiveHomology hK hneg,
    projectiveHomology_of_hasProjectiveAmplitude⟩

/-- Vanishing of an Ext group is annihilation of it by every element of the unit ideal: `1`
acts as the identity. -/
private lemma subsingleton_iff_top_annihilates
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{v} R))
    (N : ModuleCat.{v} R) :
    Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1) ↔
      ∀ a : R, a ∈ (⊤ : Ideal R) →
        ∀ ξ : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0 := by
  refine ⟨fun _ _ _ _ => Subsingleton.elim _ _, fun h => ⟨fun x y => ?_⟩⟩
  rw [← one_smul R x, ← one_smul R y, h 1 Submodule.mem_top x, h 1 Submodule.mem_top y]

open StacksDraft.ProjectiveDimension in
/-- **Stacks 0G9C.** For a derived object with cohomology concentrated in degrees `-1` and `0`,
vanishing of degree-one Ext against every module is equivalent to vanishing of degree-minus-one
cohomology and projectivity of zero-th cohomology. If the ring is Noetherian and these two
cohomology modules are finite, the same condition can be tested on finite modules. -/
@[stacks 0G9C]
public theorem projective_homology_iff_ext_one_vanishing
    {R : Type u} [CommRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    let moduleObject := fun N : ModuleCat.{v} R ↦
      (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N
    let projectiveHomology :=
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) ∧
        Module.Projective R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K)
    let extVanishes := ∀ N : ModuleCat.{v} R,
      Subsingleton (DerivedCategory.Ext K (moduleObject N) 1)
    let finiteExtVanishes := ∀ N : ModuleCat.{v} R, Module.Finite R N →
      Subsingleton (DerivedCategory.Ext K (moduleObject N) 1)
    (projectiveHomology ↔ extVanishes) ∧
      (IsNoetherianRing R →
        Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) →
        Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K) →
        (projectiveHomology ↔ finiteExtVanishes)) := by
  dsimp only
  have hA := hasProjectiveAmplitude_iff_ext_vanishing K 0 0
  have hEV : (IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) ∧
      Module.Projective R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K)) ↔
      ∀ N : ModuleCat.{v} R, Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1) := by
    refine (projectiveHomology_iff_hasProjectiveAmplitude K hK).trans
      (hA.1.trans (hA.2.1.trans (hA.2.2.trans ?_)))
    refine ⟨fun ⟨_, h⟩ => by simpa using h, fun h => ⟨fun n hn => ?_, by simpa using h⟩⟩
    apply hK n <;> rintro rfl <;> exact hn ⟨by norm_num, by norm_num⟩
  refine ⟨hEV, fun hnoeth hfinneg hfinzero => hEV.trans ?_⟩
  have hann := (ext_one_annihilated_iff_twoTerm_factorization (⊤ : Ideal R) K hK).2.2
    hnoeth hfinneg hfinzero |>.1
  exact ⟨fun h N hN => (subsingleton_iff_top_annihilates K N).2 (hann.mp
      (fun N' a ha ξ => (subsingleton_iff_top_annihilates K N').1 (h N') a ha ξ) N hN),
    fun h N => (subsingleton_iff_top_annihilates K N).2 (hann.mpr
      (fun N' hN' a ha ξ => (subsingleton_iff_top_annihilates K N').1 (h N' hN') a ha ξ) N)⟩

section NaiveCotangent

universe u' v'

/-- The cohomology of the two-term complex of the canonical presentation vanishes outside
degrees `-1` and `0`. -/
private theorem derived_homology_vanishes_outside {R : Type u'} {S : Type v'}
    [CommRing R] [CommRing S] (f : R →+* S) :
    letI := f.toAlgebra
    let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
      (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
    let K : DerivedCategory (ModuleCat.{max u' v'} S) := DerivedCategory.Q.obj C
    ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u' v'} S) i).obj K) := by
  let _ := f.toAlgebra
  dsimp only
  intro i hi hzero
  exact IsZero.of_iso (HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_double_X _ _ i hi hzero)).isZero_homology
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u' v'} S) i).app _)

/-- Degree-minus-one cohomology of the two-term complex of the canonical presentation vanishes
exactly when the first cotangent homology does. -/
private theorem degree_neg_one_iff {R : Type u'} {S : Type v'}
    [CommRing R] [CommRing S] (f : R →+* S) :
    letI := f.toAlgebra
    let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
      (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
    let K : DerivedCategory (ModuleCat.{max u' v'} S) := DerivedCategory.Q.obj C
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u' v'} S) (-1)).obj K) ↔
      Subsingleton (Algebra.H1Cotangent R S) := by
  let _ := f.toAlgebra
  dsimp only
  let P := (Algebra.Generators.self R S).toExtension
  let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
    (ModuleCat.ofHom P.cotangentComplex)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
  show IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u' v'} S) (-1)).obj
    (DerivedCategory.Q.obj C)) ↔ _
  refine ((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{max u' v'} S) (-1)).app C).isZero_iff.trans ?_
  show IsZero (C.homology (-1)) ↔ _
  rw [← C.exactAt_iff_isZero_homology,
    C.exactAt_iff' (j := (-1)) (-2) 0 (by simp) (by simp), ShortComplex.exact_iff_mono]
  · show Mono (C.d (-1) 0) ↔ _
    rw [HomologicalComplex.double_d _ _ (by norm_num), mono_comp_iff_of_isIso,
      mono_comp_iff_of_mono, ModuleCat.mono_iff_injective]
    exact (Algebra.Extension.subsingleton_h1Cotangent P).symm
  · show C.d (-2) (-1) = 0
    exact HomologicalComplex.double_d_eq_zero₀ _ _ (-2) (-1) (by norm_num)

-- Elaborating the universe-lifted cokernel comparison requires a higher heartbeat limit.
/-- Degree-zero cohomology of the two-term complex of the canonical presentation is the module
of differentials, lifted into the module universe. -/
private noncomputable def degree_zero_iso {R : Type u'} {S : Type v'}
    [CommRing R] [CommRing S] (f : R →+* S) :
    letI := f.toAlgebra
    let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
      (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
    let K : DerivedCategory (ModuleCat.{max u' v'} S) := DerivedCategory.Q.obj C
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u' v'} S) 0).obj K) ≅
      ModuleCat.of S (ULift.{max u' v'} Ω[S⁄R]) := by
  letI := f.toAlgebra
  dsimp only
  let P := (Algebra.Generators.self R S).toExtension
  let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
    (ModuleCat.ofHom P.cotangentComplex)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
  let e₀ := HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom P.cotangentComplex)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
  let e₁ := HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom P.cotangentComplex)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) (by norm_num)
  let q : P.CotangentSpace →ₗ[S] ULift.{max u' v'} Ω[S⁄R] :=
    ULift.moduleEquiv.symm.toLinearMap.comp P.toKaehler
  let A := ModuleCat.shortComplexOfCompEqZero P.cotangentComplex q
    (LinearMap.ext fun x ↦ congr_arg ULift.up
      (P.exact_cotangentComplex_toKaehler.apply_apply_eq_zero x))
  let g : C.X 0 ⟶ ModuleCat.of S (ULift.{max u' v'} Ω[S⁄R]) :=
    e₁.hom ≫
      ModuleCat.ofHom q
  let T := ShortComplex.mk (C.d (-1) 0) g (by
    rw [HomologicalComplex.double_d _ _ (by norm_num)]
    dsimp only [g]
    simp only [Category.assoc]
    ext x
    simpa [q] using congr_arg (ULift.up.{max u' v', v'})
      (P.exact_cotangentComplex_toKaehler.apply_apply_eq_zero
        (e₀.hom x)))
  have hA : A.Exact := ModuleCat.shortComplex_exact A <| by
    change Function.Exact P.cotangentComplex q
    apply Function.Exact.of_ladder_linearEquiv_of_exact
      (g₁₂ := P.cotangentComplex) (g₂₃ := q)
      (f₁₂ := P.cotangentComplex) (f₂₃ := P.toKaehler)
      (e₁ := LinearEquiv.refl S P.Cotangent)
      (e₂ := LinearEquiv.refl S P.CotangentSpace)
      (e₃ := ULift.moduleEquiv.symm)
    · ext; rfl
    · ext; rfl
    · exact P.exact_cotangentComplex_toKaehler
  have e : A ≅ T := ShortComplex.isoMk
    e₀.symm e₁.symm
    (Iso.refl _) (by
      dsimp only [T, A, ShortComplex.mk, ModuleCat.shortComplexOfCompEqZero]
      rw [HomologicalComplex.double_d _ _ (by norm_num)]
      simp [e₀, e₁]) (by simp [A, T, g, e₁])
  have hT : T.Exact := ShortComplex.exact_of_iso e hA
  have : Epi T.g := by
    rw [ModuleCat.epi_iff_surjective]
    rintro ⟨x⟩
    obtain ⟨y, rfl⟩ := P.toKaehler_surjective x
    exact ⟨e₁.inv y, by simp [T, g, q]⟩
  let eQ : C.opcycles 0 ≅ ModuleCat.of S (ULift.{max u' v'} Ω[S⁄R]) :=
    IsColimit.coconePointUniqueUpToIso
      (C.opcyclesIsCokernel (-1) 0 (by simp)) hT.gIsCokernel
  let eH : C.homology 0 ≅ ModuleCat.of S (ULift.{max u' v'} Ω[S⁄R]) :=
    C.isoHomologyι 0 1 (by simp)
      (HomologicalComplex.double_d_eq_zero₀ _ _ 0 1 (by norm_num)) ≪≫ eQ
  exact (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u' v'} S) 0).app C ≪≫ eH

private theorem degree_zero_projective_iff {R : Type u'} {S : Type v'}
    [CommRing R] [CommRing S] (f : R →+* S) :
    letI := f.toAlgebra
    let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
      (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
    let K : DerivedCategory (ModuleCat.{max u' v'} S) := DerivedCategory.Q.obj C
    Module.Projective S
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u' v'} S) 0).obj K) ↔
      Module.Projective S Ω[S⁄R] := by
  let _ := f.toAlgebra
  dsimp only
  let e := (degree_zero_iso f).toLinearEquiv
  refine ⟨fun _ => ?_, fun _ => .of_equiv' e.symm⟩
  have : Module.Projective S (ULift.{max u' v'} Ω[S⁄R]) := .of_equiv' e
  exact .of_ulift

/-- Formal smoothness is exactly the two cohomology conditions on the two-term complex of the
canonical presentation. -/
private theorem projective_homology_iff_formallySmooth {R : Type u'} {S : Type v'}
    [CommRing R] [CommRing S] (f : R →+* S) :
    letI := f.toAlgebra
    let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
      (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
    let K : DerivedCategory (ModuleCat.{max u' v'} S) := DerivedCategory.Q.obj C
    (IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u' v'} S) (-1)).obj K) ∧
      Module.Projective S
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u' v'} S) 0).obj K)) ↔
      f.FormallySmooth := by
  let _ := f.toAlgebra
  dsimp only
  show _ ↔ Algebra.FormallySmooth R S
  rw [Algebra.formallySmooth_iff]
  exact (and_congr (degree_neg_one_iff f) (degree_zero_projective_iff f)).trans and_comm

/-- **Stacks 0G9D.** A ring map is smooth if and only if it is of finite presentation and
degree-one Ext from its naive cotangent complex to every module vanishes. It is formally smooth
if and only if the same Ext groups vanish, without a finite-presentation condition. -/
@[stacks 0G9D]
public theorem smooth_and_formallySmooth_iff_ext_one_vanishing
    {R : Type u'} {S : Type v'} [CommRing R] [CommRing S] (f : R →+* S) :
    letI := f.toAlgebra
    let naiveCotangentObject : DerivedCategory (ModuleCat.{max u' v'} S) :=
      DerivedCategory.Q.obj
        (HomologicalComplex.double
          (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl))
    let extOneVanishes := ∀ N : ModuleCat.{max u' v'} S,
      Subsingleton
        (DerivedCategory.Ext naiveCotangentObject
          ((DerivedCategory.singleFunctor (ModuleCat.{max u' v'} S) 0).obj N) 1)
    (f.Smooth ↔ f.FinitePresentation ∧ extOneVanishes) ∧
      (f.FormallySmooth ↔ extOneVanishes) := by
  let _ := f.toAlgebra
  dsimp only
  let C := HomologicalComplex.double (i₀ := (-1 : ℤ)) (i₁ := 0)
    (ModuleCat.ofHom (Algebra.Generators.self R S).toExtension.cotangentComplex)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
  let K : DerivedCategory (ModuleCat.{max u' v'} S) := DerivedCategory.Q.obj C
  have hformal : f.FormallySmooth ↔ ∀ N : ModuleCat.{max u' v'} S,
      Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{max u' v'} S) 0).obj N) 1) :=
    (projective_homology_iff_formallySmooth f).symm.trans
      (projective_homology_iff_ext_one_vanishing K (derived_homology_vanishes_outside f)).1
  exact ⟨by rw [RingHom.smooth_def, hformal, and_comm], hformal⟩

end NaiveCotangent

end TwoTermComplex
