module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.SquareZeroExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.WeakRelativeNoetherNormalization
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBoundUpper
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChangeVanishing
public import StacksFrontier.RingTheory.Module.FinitePresentation.Colimit
public import StacksFrontier.RingTheory.RelativeDimension.BaseChange

/-!
# Tor amplitude of a relative dualizing complex

Let `R → A` be a flat finite type homomorphism of Noetherian rings all of whose fibres have
dimension at most `d`.  Then the relative dualizing complex `ω^•_{A/R}` has Tor amplitude in
`[-d, 0]` as a complex of `R`-modules, which is the Tor-amplitude clause of [Stacks, Tag 0E9Q].

## Main results

* `Dualizing.isZero_homology_derivedTensor_upperShriekFunctor_of_finitePresentation` — the Tor
  test at a finitely presented module.
* `Dualizing.upperShriekFunctor_hasTorAmplitude_of_relativeDimension_le` — the Tor-amplitude
  clause with the bound on the fibres read as `dim(A/R) ≤ d`.
* `Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le` — the Tor-amplitude
  clause of [Stacks, Tag 0E9Q], with the source's hypothesis on the fibres.

## Implementation notes

As everywhere in `StacksDraft.RingTheory.Dualizing.UpperShriek` the relative dualizing complex is
read at an arbitrary polynomial presentation.

The argument is the source's.  Base change along the square-zero thickening `R' = R ⊕ M` by a
finite module, of which `M` is a direct summand as an `R`-module, reduces the Tor test at `M` to
the cohomology of `ω^•_{A/R} ⊗_R^L R'`, and the projection formula reads the result as a derived
tensor product over `R`.  In degrees above `0` the test is the bound `[-n, 0]` of
`Dualizing.PolynomialPresentation.relativeDualizingComplex_hasTorAmplitude_neg_variableCount`;
below `-d` it is
`Dualizing.isZero_homology_totalDerivedExtensionScalars_upperShriekFunctor_of_lt` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChangeVanishing`, which
computes the base change on a finite projective resolution of `A` over the polynomial algebra and
so needs only the cohomological concentration of `ω^•_{A'/R'}`, the fibres of `R' → A'` having
dimension at most `d` as well.  The source quotes [Stacks, Tag 0BZV] for that step; only the
cohomology modules of the base change are used, and those are computed without identifying
`ω^•_{A/R} ⊗_A^L A'` with `ω^•_{A'/R'}` as complexes of `A'`-modules.  Arbitrary modules are
filtered colimits of finitely presented ones — [Stacks, Tag 00HA] — and the homology of a
termwise tensor product commutes with those colimits.

## References

* [Stacks Project, Tag 0E9Q](https://stacks.math.columbia.edu/tag/0E9Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  RingTheory.TorIndependence
open Stacks.HomologyColimit
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- A functor kills an object that retracts onto an object it kills. -/
private theorem isZero_functor_of_retract {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] (F : C ⥤ D) {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) (hY : IsZero (F.obj Y)) : IsZero (F.obj X) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ← h, F.map_comp, hY.eq_zero_of_tgt (F.map i), zero_comp]

/-- Every complex of `R`-modules admits a K-flat resolution. -/
private lemma exists_kFlat_resolution_with_quasiIso {R : Type u} [CommRing R]
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (pr : P ⟶ X), P.KFlat ∧ QuasiIso pr := by
  obtain ⟨P, pr, hP, -, hpr, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution X
  exact ⟨P, pr, hP, hpr⟩

/-- Every object of the derived category of `R` is represented by a K-flat complex. -/
private lemma exists_kFlat_iso_derived {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    ∃ E : CochainComplex (ModuleCat.{u} R) ℤ, E.KFlat ∧ Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  obtain ⟨E, pr, hE, hpr⟩ := exists_kFlat_resolution_with_quasiIso (DerivedCategory.Q.objPreimage K)
  exact ⟨E, hE, ⟨asIso (DerivedCategory.Q.map pr) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- A module placed in degree zero has a K-flat resolution representing it in the derived
category. -/
private lemma exists_kFlat_resolution_single0 {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (s : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M), P.KFlat ∧ QuasiIso s ∧
      Nonempty (DerivedCategory.Q.obj P ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  obtain ⟨P, s, hP, hs⟩ := exists_kFlat_resolution_with_quasiIso
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
  exact ⟨P, s, hP, hs, ⟨asIso (DerivedCategory.Q.map s) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M).symm⟩⟩

/-- **The projection formula for a derived base change.** Derived extension of scalars along
`f : R → S` followed by restriction of scalars is derived tensoring over `R` with the `R`-module
underlying the test `S`-module: the two sides are computed on a K-flat representative of the
complex and of the module, where derived tensoring is the total tensor product. -/
private lemma nonempty_projectionFormulaIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q (C := ModuleCat.{u} R) ⋙ L ⟶
      (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat.{u} S))
    (hL : L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (T' : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct S)
    (K : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} S) :
    Nonempty ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
          ((T.tensor.obj (L.obj K)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M)) ≅
        (T'.tensor.obj K).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars f).obj M))) := by
  classical
  obtain ⟨sR, -⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R
  obtain ⟨sS, -⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory S
  let _ := sR.toBraidedCategory
  let _ := sS.toBraidedCategory
  obtain ⟨P, hP, ⟨eK⟩⟩ := exists_kFlat_iso_derived K
  have hcomp : IsIso (comparison.app P) :=
    @CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat.{u, u, u}
      R S _ _ f _ _ L comparison hL P hP
  let EP : CochainComplex (ModuleCat.{u} S) ℤ := (CochainComplex.extendScalars f).obj P
  let eL := L.mapIso eK.symm ≪≫ asIso (comparison.app P)
  have hEP : EP.KFlat := kFlat_baseChange f P hP
  let S_R : ModuleCat.{u} R := (ModuleCat.restrictScalars f).obj M
  obtain ⟨V, s, hV, hs, ⟨eV⟩⟩ := exists_kFlat_resolution_single0 M
  let UV : CochainComplex (ModuleCat.{u} R) ℤ :=
    (CochainComplex.restrictScalars f).obj V
  obtain ⟨VV, q, hVV, hq⟩ := exists_kFlat_resolution_with_quasiIso UV
  have hUs : QuasiIso ((CochainComplex.restrictScalars f).map s) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology s
      (ModuleCat.restrictScalars f)).2 hs
  let eUV : DerivedCategory.Q.obj UV ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S_R :=
    asIso (DerivedCategory.Q.map ((CochainComplex.restrictScalars f).map s)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars f)
          (ComplexShape.up ℤ) 0).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app S_R).symm
  let eVV : DerivedCategory.Q.obj VV ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S_R :=
    asIso (DerivedCategory.Q.map q) ≪≫ eUV
  let e6 : ((ModuleCat.restrictScalars f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (EP ⊗ V) ≅ (tensorLeft P).obj UV :=
    (CochainComplex.restrictScalars f).mapIso
        (CochainComplex.DerivedTensor.tensorFlipIso EP V) ≪≫
      CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso f P V ≪≫
      CochainComplex.DerivedTensor.tensorFlipIso UV P
  have := StacksDraft.TorAmplitude.quasiIso_tensorLeft_map P hP q
  exact ⟨(ModuleCat.restrictScalars f).mapDerivedCategory.mapIso
        ((T.tensor.mapIso eL).app _ ≪≫
          (T.tensor.obj (DerivedCategory.Q.obj EP)).mapIso eV.symm ≪≫
          T.comparison EP V hEP hV) ≪≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app (EP ⊗ V) ≪≫
      DerivedCategory.Q.mapIso e6 ≪≫
      (asIso (DerivedCategory.Q.map ((tensorLeft P).map q))).symm ≪≫
      (T'.comparison P VV hP hVV).symm ≪≫
      (T'.tensor.obj (DerivedCategory.Q.obj P)).mapIso eVV ≪≫
      (T'.tensor.mapIso eK).app _⟩

/-- **The Tor test at a finitely presented module.**  For a flat finite type homomorphism of
Noetherian rings whose fibres have dimension at most `d`, the derived tensor product
`ω^•_{A/R} ⊗_R^L M` has cohomology only in degrees `[-d, 0]` for every finitely presented
`R`-module `M`.  Following the source, the base change is performed at the square-zero thickening
`R ⊕ M`, of which `M` is a direct summand as an `R`-module, and the projection formula reads the
resulting vanishing as the vanishing of a derived tensor product over `R`. -/
theorem isZero_homology_derivedTensor_upperShriekFunctor_of_finitePresentation
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ q : PrimeSpectrum A, Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞))
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (i : ℤ) (hi : i ∉ Set.Icc (-(d : ℤ)) 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R R))))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) := by
  by_cases hpos : 0 < i
  · exact p.relativeDualizingComplex_hasTorAmplitude_neg_variableCount M i
      fun h => absurd h.2 (not_le.2 hpos)
  have hneg : i < -(d : ℤ) := by
    by_contra hge
    exact hi ⟨by omega, by omega⟩
  let S := TrivSqZeroExt R (M : Type u)
  let oppHom : Rᵐᵒᵖ →+* R :=
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y => by simp [mul_comm]
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let instOpp : Module Rᵐᵒᵖ (M : Type u) := Module.compHom (M : Type u) oppHom
  let instCentral : IsCentralScalar R (M : Type u) := ⟨fun _ _ => rfl⟩
  let : CommRing S := inferInstance
  let : Algebra R S := (TrivSqZeroExt.inlHom R (M : Type u)).toAlgebra
  let : Module.Finite R (M : Type u) := inferInstance
  let : IsNoetherianRing S := TrivSqZeroExt.isNoetherianRing
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let TS := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct S
  let K := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
    (p.upperShriekFunctor.{u, 0}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  let L := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
    (algebraMap R S)
  let : L.functor.IsLeftDerivedFunctor L.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := L.isLeftDerived
  have hS := isZero_homology_totalDerivedExtensionScalars_upperShriekFunctor_of_lt (R' := S) p d hd
    i hneg
  let F := ModuleCat.restrictScalars (algebraMap R S)
  let : Module R S := Module.compHom S (algebraMap R S)
  have hbase : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (F.mapDerivedCategory.obj (L.functor.obj K))) :=
    (F.map_isZero hS).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app
        (L.functor.obj K))
  have hbase' : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R S)))) :=
    hbase.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((nonempty_projectionFormulaIso (algebraMap R S) L.functor L.comparison L.isLeftDerived
          T TS K (ModuleCat.of S S)).some.symm ≪≫
        F.mapDerivedCategory.mapIso (TS.rightUnitor.app (L.functor.obj K))))
  let inc : (M : Type u) →ₗ[R] S :=
    { toFun := TrivSqZeroExt.inr
      map_add' := by
        intro x y
        change TrivSqZeroExt.inr (x + y) = _
        rw [TrivSqZeroExt.inr_add]
      map_smul' := by
        intro r x
        change TrivSqZeroExt.inr (r • x) = algebraMap R S r * TrivSqZeroExt.inr x
        rw [show algebraMap R S r = TrivSqZeroExt.inl r from rfl, TrivSqZeroExt.inl_mul_inr] }
  let proj : S →ₗ[R] (M : Type u) :=
    { toFun := TrivSqZeroExt.snd
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change TrivSqZeroExt.snd (algebraMap R S r * x) = r • TrivSqZeroExt.snd x
        rw [show algebraMap R S r = TrivSqZeroExt.inl r from rfl]
        change (TrivSqZeroExt.inl r * x).snd = r • x.snd
        rw [TrivSqZeroExt.snd_mul]
        simp }
  have hsplitCat : ModuleCat.ofHom inc ≫ ModuleCat.ofHom proj = 𝟙 M := by
    ext x
    rfl
  exact isZero_functor_of_retract
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0) ⋙ T.tensor.obj K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) i)
    (ModuleCat.ofHom inc) (ModuleCat.ofHom proj) hsplitCat hbase'

/-! ### Filtered colimits of the test module -/

/-- A K-flat representative computes derived tensoring with a module by the ordinary total
tensor product with that module in degree zero. -/
private lemma nonempty_derivedTensor_kFlatRepresentativeIso
    {R : Type u} [CommRing R]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat)
    (K : DerivedCategory (ModuleCat.{u} R)) (eK : DerivedCategory.Q.obj E ≅ K)
    (M : ModuleCat.{u} R) :
    Nonempty ((T.tensor.obj K).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      DerivedCategory.Q.obj ((tensorLeft E).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))) := by
  classical
  obtain ⟨s, -⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R
  let _ := s.toBraidedCategory
  obtain ⟨P, π, hP, hπ, ⟨eP⟩⟩ := exists_kFlat_resolution_single0 M
  have := StacksDraft.TorAmplitude.quasiIso_tensorLeft_map E hE π
  exact ⟨(T.tensor.mapIso eK.symm).app _ ≪≫
    (T.tensor.obj (DerivedCategory.Q.obj E)).mapIso eP.symm ≪≫
    T.comparison E P hE hP ≪≫ asIso (DerivedCategory.Q.map ((tensorLeft E).map π))⟩

/-- Termwise tensoring a fixed complex by a varying module, as a functor to cochain
complexes. -/
private noncomputable def moduleTermwiseTensorComplexFunctor
    {R : Type u} [CommRing R] (E : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := (((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E
  map f := (NatTrans.mapHomologicalComplex
    ((tensoringRight (ModuleCat.{u} R)).map f) (ComplexShape.up ℤ)).app E
  map_id M := by simp
  map_comp f g := by simp

/-- Termwise tensoring evaluated in a degree is tensoring with the term in that degree. -/
private noncomputable def moduleTermwiseTensorComplex_evalIso
    {R : Type u} [CommRing R] (E : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    moduleTermwiseTensorComplexFunctor E ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n ≅
      (tensoringLeft (ModuleCat.{u} R)).obj (E.X n) := by
  refine NatIso.ofComponents (fun M => Iso.refl _) ?_
  intro M N f
  ext x
  rfl

/-- Termwise tensoring by a varying module commutes with colimits, being degreewise a left
adjoint. -/
private lemma preservesColimitsOfShape_moduleTermwiseTensorComplexFunctor
    {R : Type u} [CommRing R] {J : Type*} [Category J]
    [HasColimitsOfShape J (ModuleCat.{u} R)] (E : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (moduleTermwiseTensorComplexFunctor E) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let : Functor.IsLeftAdjoint ((tensoringLeft (ModuleCat.{u} R)).obj (E.X n)) :=
    (MonoidalClosed.closed (E.X n)).adj.isLeftAdjoint
  exact preservesColimitsOfShape_of_natIso (moduleTermwiseTensorComplex_evalIso E n).symm

/-- The degree-`n` inclusion of the termwise tensor product into the total tensor product with a
module placed in degree zero. -/
private noncomputable def moduleTermwiseTensorInclusion
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ⟶
      (tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj E where
  f n := HomologicalComplex.ιTensorObj E
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) n 0 n (add_zero n)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    change HomologicalComplex.ιMapBifunctor E _ (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
      (HomologicalComplex.mapBifunctor E _ (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ)).d n (n + 1) = _
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show n + 1 = n + 1 from rfl) 0 (n + 1) (add_zero _),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ n
        (show (0 : ℤ) + 1 = 1 from rfl) (n + 1) rfl]
    simp
    rfl

/-- The termwise tensor product with a module placed in degree zero is the total one. -/
private lemma moduleTermwiseTensorInclusion_isIso
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (moduleTermwiseTensorInclusion M E) := by
  have hn : ∀ n, IsIso ((moduleTermwiseTensorInclusion M E).f n) := by
    intro n
    let pr : ((tensorRight
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj E).X n ⟶ E.X n ⊗ M :=
      HomologicalComplex.mapBifunctorDesc (K₁ := E)
        (K₂ := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
        (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ) (fun i j h =>
        if hj : j = 0 then eqToHom (by
          subst hj
          have hi : i = n := by simpa using h
          subst hi
          rfl)
        else 0)
    have hp : (moduleTermwiseTensorInclusion M E).f n ≫ pr = 𝟙 _ :=
      (HomologicalComplex.ι_mapBifunctorDesc (K₁ := E)
        (K₂ := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
        (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ) _ n 0
        (add_zero n)).trans (by rfl)
    refine ⟨pr, hp, ?_⟩
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    by_cases hj : j = 0
    · subst hj
      have hi : i = n := by simpa using h
      subst hi
      have key : (moduleTermwiseTensorInclusion M E).f i ≫ pr ≫
          (moduleTermwiseTensorInclusion M E).f i =
          (moduleTermwiseTensorInclusion M E).f i := by
        rw [← Category.assoc, hp, Category.id_comp]
      exact key.trans (Category.comp_id _).symm
    · exact (((tensoringLeft (ModuleCat.{u} R)).obj (E.X i)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M j hj)).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The termwise tensor product with a module placed in degree zero is the total one. -/
private noncomputable def moduleTermwiseTensorInclusionIso
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
      (tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj E := by
  let := moduleTermwiseTensorInclusion_isIso M E
  exact asIso (moduleTermwiseTensorInclusion M E)

/-- Vanishing of the derived tensor product on finitely presented modules extends to arbitrary
modules.  A fixed K-flat representative turns derived tensoring into the total tensor product,
whose homology commutes with the filtered colimit writing an arbitrary module as a colimit of
finitely presented ones — [Stacks, Tag 00HA]. -/
private theorem tensor_isZero_of_finitePresentation
    {R : Type u} [CommRing R] (a b : ℤ)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R))
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat)
    (eK : DerivedCategory.Q.obj E ≅ K)
    (hfp : ∀ (M : ModuleCat.{u} R) [Module.FinitePresentation R M] (i : ℤ), i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))))
    (M : ModuleCat.{u} R) (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) := by
  classical
  obtain ⟨J, hPre, hDir, hNonempty, hDecEq, G, hAdd, hMod, f, hDS, hG, ⟨eM⟩⟩ :=
    Module.exists_linearEquiv_directLimit_finitePresentation_max.{u, u} R (M : Type u)
  let : IsFiltered J := inferInstance
  let F := moduleTermwiseTensorComplexFunctor E
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  have eHomology (N : ModuleCat.{u} R) : Nonempty
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj K).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
        H.obj (F.obj N)) := by
    obtain ⟨e⟩ := nonempty_derivedTensor_kFlatRepresentativeIso T E hE K eK N
    exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (e ≪≫ DerivedCategory.Q.mapIso (moduleTermwiseTensorInclusionIso N E).symm) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app (F.obj N)⟩
  let D : J ⥤ ModuleCat.{u} R := ModuleCat.directLimitDiagram G f
  let c : Cocone D := ModuleCat.directLimitCocone G f
  have hc : IsColimit c := ModuleCat.directLimitIsColimit G f
  let hF : PreservesColimitsOfShape J F :=
    preservesColimitsOfShape_moduleTermwiseTensorComplexFunctor E
  let hH : PreservesColimitsOfShape J H :=
    preservesColimitsOfShape_homologyFunctor (ComplexShape.up ℤ) i
  have hcFH : IsColimit ((F ⋙ H).mapCocone c) := isColimitOfPreserves (F ⋙ H) hc
  have hcolimZero : IsZero (colimit (D ⋙ F ⋙ H)) := by
    rw [IsZero.iff_id_eq_zero]
    apply colimit.hom_ext
    intro j
    let Mj : ModuleCat.{u} R := ModuleCat.of R (G j)
    let : Module.FinitePresentation R Mj := hG j
    rw [Category.comp_id, comp_zero]
    exact ((hfp Mj i hi).of_iso (eHomology Mj).some.symm).eq_of_src _ _
  have htotal : IsZero (H.obj (F.obj c.pt)) :=
    hcolimZero.of_iso
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (D ⋙ F ⋙ H)) hcFH).symm
  have htotalM : IsZero (H.obj (F.obj (ModuleCat.of R (M : Type u)))) :=
    htotal.of_iso ((F ⋙ H).mapIso eM.toModuleIso)
  exact htotalM.of_iso (eHomology M).some

/-- **The Tor amplitude clause of [Stacks, Tag 0E9Q], with the fibre-dimension bound read as a
bound on the relative dimension.**  Let `R → A` be a flat finite type homomorphism of Noetherian
rings with `dim(A/R) ≤ d`.  Then `ω^•_{A/R}` has Tor amplitude in `[-d, 0]` as a complex of
`R`-modules.  The relative dimension is the supremum of the local dimensions of the fibres, so this
is the statement of the source; the form with the source's own hypothesis on the fibres is
`Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le`. -/
theorem upperShriekFunctor_hasTorAmplitude_of_relativeDimension_le
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : Algebra.relativeDimension R A ≤ (d : WithBot ℕ∞)) :
    StacksDraft.TorAmplitude.HasTorAmplitude
      (StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R).tensor
      (StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R).comparison
      (StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R).isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
      (-(d : ℤ)) 0 := by
  have hd' : ∀ q : PrimeSpectrum A,
      Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞) := fun q =>
    (le_iSup (fun q : PrimeSpectrum A => Algebra.relativeDimensionAt R q.asIdeal) q).trans hd
  let K := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
    (p.upperShriekFunctor.{u, 0}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  obtain ⟨E, hE, ⟨eK⟩⟩ := exists_kFlat_iso_derived K
  have hAmp : StacksDraft.TorAmplitude.HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K (-(d : ℤ)) 0 := by
    intro M i hi
    exact tensor_isZero_of_finitePresentation (-(d : ℤ)) 0
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) K E hE eK
      (fun N _ j hj => isZero_homology_derivedTensor_upperShriekFunctor_of_finitePresentation
        p d hd' N j hj) M i hi
  exact (StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff R K (-(d : ℤ)) 0).2
    ((StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K
        (-(d : ℤ)) 0).2
      ((StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
        (StacksDraft.TorAmplitude.canonicalTensorComparison R)
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K (-(d : ℤ)) 0).1 hAmp))

/-- **[Stacks, Tag 0E9Q], the Tor amplitude clause.**  Let `R → A` be a flat finite type
homomorphism of Noetherian rings.  If all fibres of `Spec(A) → Spec(R)` have dimension at most
`d`, then `ω^•_{A/R}` has Tor amplitude in `[-d, 0]` as a complex of `R`-modules.

Here `ω^•_{A/R} = f^!(R)` is read at an arbitrary polynomial presentation of `R → A`, being
defined only up to isomorphism, and Tor amplitude is read at the canonical certified derived
tensor product of `R`.  Nothing is carried.  Following the source, the Tor test at a finitely
presented module `M` is the cohomology of `ω^•_{A/R} ⊗_R^L (R ⊕ M)`, a base change to a Noetherian
ring whose fibres have dimension at most `d`: that is
`Dualizing.isZero_homology_totalDerivedExtensionScalars_upperShriekFunctor_of_lt`, proved by
computing the base change on a finite projective resolution of `A` over the polynomial algebra,
which needs no comparison of `A`-linear structures; arbitrary modules are filtered colimits of
finitely presented ones. -/
@[stacks 0E9Q "the Tor amplitude clause: if all fibres of Spec(A) -> Spec(R) have dimension at \
most d then the relative dualizing complex has Tor amplitude in [-d, 0] over R; the relative \
dualizing complex is read at the upper shriek functor of an arbitrary polynomial presentation of \
the homomorphism, being well defined only up to isomorphism"]
theorem upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ 𝔭 : AlgebraicGeometry.Spec (.of R),
      topologicalKrullDim ((AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R A))).fiber 𝔭) ≤ (d : WithBot ℕ∞)) :
    StacksDraft.TorAmplitude.HasTorAmplitude
      (StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R).tensor
      (StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R).comparison
      (StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R).isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
      (-(d : ℤ)) 0 :=
  upperShriekFunctor_hasTorAmplitude_of_relativeDimension_le p d
    ((Algebra.relativeDimension_le_natCast_iff_forall_topologicalKrullDim_fiber_le d).mpr hd)

end Dualizing

end
