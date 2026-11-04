module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.RelativelyPerfect
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Perfect objects and derived tensor products are relatively perfect

Let `R → A` be a flat ring map of finite presentation. Every perfect object of `D(A)` is perfect
relative to `R` (Stacks 0DHS), and the derived tensor product over `A` of a perfect object with a
relatively perfect object is again relatively perfect.

## Main results

* `PseudoCoherence.isRelativelyPerfect_of_isPerfect` and
  `PseudoCoherence.isRelativelyPerfect_derivedTensor` (Stacks 0DHU): the two assertions of the
  tag.
* `PseudoCoherence.exists_bounded_relativelyFlat_representative`: a relatively perfect object is
  represented by a bounded complex whose terms are flat over `R` and finitely presented over `A`.
* `PseudoCoherence.hasFiniteTorDimension_of_bounded_relativelyFlat`: the converse Tor-dimension
  half, for an arbitrary bounded complex with terms flat over `R`.

## Implementation notes

Relative perfectness is `PseudoCoherence.IsRelativelyPerfect` (Stacks 0DHS), which carries the
derived tensor product over `R` unbundled, as the bifunctor together with its comparison with
termwise tensoring and the universal property making each `- ⊗ᴸ N[0]` a total left derived
functor. The derived tensor product over `A` is supplied in the same unbundled style: the
bifunctor together with the isomorphism identifying it with the total tensor product of complexes
on K-flat representatives, which is the property by which the source characterises it. No
canonical derived tensor product is constructed in this tree, so both are hypotheses.

The ring, algebra and module carrier universes are independent; both module categories use the
carrier universe `max u v w`. Mathlib's monoidal structure on `ModuleCat` needs the carriers and
the ring to share a universe, so the tensor product used here is the large-universe one of
`ModuleCat.liftedModuleMonoidalStruct` and K-flatness is `CochainComplex.KFlat`; at a
coinciding universe both are the usual notions on the nose.

The private material falls into three groups. First, the identification of the cohomology of a
certified derived tensor product `Q(P) ⊗ᴸ N[0]` with the cohomology of the termwise tensor
complex `P ⊗ N`, for `P` bounded above with flat terms and at independent universes: this is the
content of `StacksDraft.TorAmplitude.isIso_comparison_app_of_flat`, which is stated with the ring
and the modules in one universe, transported along `StacksDraft.TorAmplitude.scalarLift` by
uniqueness of total left derived functors, with the derived functor of termwise tensoring over
the lifted coefficient ring as the comparison datum. It gives both the Tor amplitude of a
bounded complex of flat modules and the termwise vanishing that Stacks 0653 consumes.

Second, the bounded relatively flat representative of a relatively perfect object: a
bounded-above finite free representative truncated at the lower Tor bound, whose terms are flat
over `R` — above the bound because finite free modules over `A` are flat over `R` by transitivity
of flatness, and at the bound by Stacks 0653
(`StacksDraft.TorAmplitude.cokernel_flat_of_termwise_isZero_homology`). Its terms are finitely
presented over `A` for the same reason, the term at the bound being the cokernel of a map of
finite free modules. This is the one piece of the file that Stacks 0DHV consumes, so it is
public rather than private, and untagged.

Third, the total tensor product of complexes: its bounds, that it has finite free terms when both
factors do, and that it is flat over `R` when one factor is flat over `A` and the other flat
over `R`.

Pseudo-coherence over `A` is `StacksDraft.PseudoCoherence.IsPseudoCoherent`, the notion Stacks
0DHS is stated with, and `StacksFrontier.Homology.PseudoCoherent.Characterization` supplies the
criterion turning the finite projective representative of a perfect object into a finite free
one. That file `export`s the notion into the root `PseudoCoherence` namespace, so the short name
`PseudoCoherence.IsPseudoCoherent` abbreviates the same constant rather than naming a second
notion; there is nothing to convert between.

## References

* [The Stacks Project, Lemma 15.85.3 (0DHU)](https://stacks.math.columbia.edu/tag/0DHU)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped TensorProduct

namespace PseudoCoherence

universe u v w

attribute [local instance] HasDerivedCategory.standard

open StacksDraft.TorAmplitude

/-! ### Cohomology of a certified derived tensor product at a bounded above flat complex -/

section ScalarLift

variable {R : Type u} [CommRing R]

/-- Changing the coefficient ring along `ULift.ringEquiv` neither creates nor destroys the
vanishing of the cohomology of a cochain complex: it is exact and changes no carrier. -/
private lemma isZero_homology_scalarLift_iff
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ) :
    IsZero ((((scalarLift.{u, v} (R := R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).homology i) ↔ IsZero (C.homology i) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact IsZero.of_full_of_faithful_of_isZero (scalarLift.{u, v} (R := R)) _
      (h.of_iso ((C.sc i).mapHomologyIso (scalarLift.{u, v} (R := R))).symm)
  · exact ((scalarLift.{u, v} (R := R)).map_isZero h).of_iso
      ((C.sc i).mapHomologyIso (scalarLift.{u, v} (R := R)))

/-- Termwise tensoring commutes with the change of coefficient ring, on cochain complexes. -/
noncomputable def tensorScalarLiftComplexIso (N : ModuleCat.{max u v} R) :
    (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight ((scalarLift.{u, v} (R := R)).obj N)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (scalarLift.{u, v} (R := R) ⋙
        tensorModuleRight ((scalarLift.{u, v} (R := R)).obj N))) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (tensorScalarLiftIso N) (ComplexShape.up ℤ)).symm

/-- Uniqueness of total left derived functors identifies any certified derived tensoring by a
module with the total left derived functor of termwise tensoring over the lifted coefficient
ring, where the ring and its modules share a universe. -/
noncomputable def derivedTensorScalarLiftIso
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
    (N : ModuleCat.{max u v} R)
    (α : DerivedCategory.Q ⋙ L ⟶
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))] :
    L ⋙ (scalarLift.{u, v} (R := R)).mapDerivedCategory ≅
      (scalarLift.{u, v} (R := R)).mapDerivedCategory ⋙
        termwiseDerived ((scalarLift.{u, v} (R := R)).obj N) := by
  let G := scalarLift.{u, v} (R := R)
  let L' := termwiseDerived (G.obj N)
  let α' := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α G.mapDerivedCategory
  let β : DerivedCategory.Q ⋙ (G.mapDerivedCategory ⋙ L') ⟶
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight (G.obj N)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight G.mapDerivedCategoryFactors.hom L' ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (termwiseDerivedCounit (G.obj N))
  have : (G.mapDerivedCategory ⋙ L').IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := by
    apply (LocalizerMorphism.isLeftDerivedFunctor_iff_precomp
      (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory G.mapDerivedCategoryFactors.symm
      β (termwiseDerivedCounit (G.obj N)) (Iso.refl _) (Iso.refl _) ?_).1 inferInstance
    ext X
    dsimp [β, L', Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism]
    simp only [Category.id_comp, Category.comp_id]
  let τ :
      ((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        G.mapDerivedCategory ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight (G.obj N)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tensorScalarLiftComplexIso N).symm _ ≪≫
      Functor.associator _ _ _
  exact Functor.leftDerivedNatIso _ _ α' β
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) τ

variable
  (derivedTensor : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
  (comparison : ∀ N : ModuleCat.{max u v} R,
    DerivedCategory.Q ⋙ derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) ⟶
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ N : ModuleCat.{max u v} R,
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))

include comparison isLeftDerived in
/-- For a bounded above complex `P` of flat modules, the cohomology of the certified derived
tensor product `Q(P) ⊗ᴸ N[0]` vanishes exactly when the cohomology of the termwise tensor complex
`P ⊗ N` does. The ring universe and the module universe are independent: the comparison is
transported along `StacksDraft.TorAmplitude.scalarLift`, over which the derived functor of
termwise tensoring is available, and both sides of the equivalence are detected there. -/
private lemma isZero_homology_derivedTensor_iff
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hbounded : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (P.X j))
    (hflat : ∀ j : ℤ, Module.Flat R (P.X j)) (N : ModuleCat.{max u v} R) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((derivedTensor.obj (DerivedCategory.Q.obj P)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N))) ↔
      IsZero ((((tensorModuleRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i) := by
  have := isLeftDerived N
  let G := scalarLift.{u, v} (R := R)
  let P' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hb' : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (P'.X j) := by
    obtain ⟨n, hn⟩ := hbounded
    exact ⟨n, fun j hj => G.map_isZero (hn j hj)⟩
  have hf' : ∀ j : ℤ, Module.Flat (ULift.{v} R) (P'.X j) := by
    intro j
    show Module.Flat (ULift.{v} R) (P.X j)
    rw [Module.Flat.ulift_left_iff]
    exact hflat j
  have hcounit := isIso_termwiseDerivedCounit_app_of_flat (G.obj N) P' hb' hf'
  let e : G.mapDerivedCategory.obj
        ((derivedTensor.obj (DerivedCategory.Q.obj P)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N)) ≅
      DerivedCategory.Q.obj
        (((tensorModuleRight (G.obj N)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P') :=
    (derivedTensorScalarLiftIso
        (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N)) N
        (comparison N)).app (DerivedCategory.Q.obj P) ≪≫
      (termwiseDerived (G.obj N)).mapIso (G.mapDerivedCategoryFactors.app P) ≪≫
      asIso ((termwiseDerivedCounit (G.obj N)).app P')
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} (ULift.{v} R)) i).app _ ≪≫
    HomologicalComplex.homologyMapIso ((tensorScalarLiftComplexIso N).app P) i
  rw [← scalarLift_map_isZero_homology_iff, ← isZero_homology_scalarLift_iff]
  exact ⟨fun h => h.of_iso E.symm, fun h => h.of_iso E⟩

/-- A bounded complex of flat modules has Tor amplitude in the interval of its degrees, for every
certified derived tensor product. -/
@[sga "6 I 5.8.4" "special case"]
private lemma hasTorAmplitude_of_bounded_flat
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hflat : ∀ j : ℤ, Module.Flat R (P.X j)) :
    HasTorAmplitude derivedTensor comparison isLeftDerived (DerivedCategory.Q.obj P) a b := by
  intro N i hi
  refine (isZero_homology_derivedTensor_iff derivedTensor comparison isLeftDerived P
    ⟨b, fun j hj => P.isZero_of_isStrictlyLE b j hj⟩ hflat N i).2 ?_
  have hi' : i < a ∨ b < i := by simpa only [Set.mem_Icc, not_and_or, not_le] using hi
  have hz : IsZero (P.X i) := by
    rcases hi' with h | h
    · exact P.isZero_of_isStrictlyGE a i h
    · exact P.isZero_of_isStrictlyLE b i h
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ ((tensorModuleRight N).map_isZero hz)

/-- Derived Tor amplitude of a bounded above complex of flat modules gives the vanishing of the
cohomology of its termwise tensor products, which is the hypothesis Stacks 0653 consumes. -/
private lemma isZero_homology_tensor_of_torAmplitude
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (a b : ℤ)
    (hbounded : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (P.X j))
    (hflat : ∀ j : ℤ, Module.Flat R (P.X j))
    (hamp : HasTorAmplitude derivedTensor comparison isLeftDerived (DerivedCategory.Q.obj P) a b)
    (N : ModuleCat.{max u v} R) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((((tensorModuleRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i) :=
  (isZero_homology_derivedTensor_iff derivedTensor comparison isLeftDerived P hbounded hflat
      N i).1
    (hamp N i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi))

/-- Tor amplitude only depends on the isomorphism class of the object. -/
private lemma hasTorAmplitude_of_iso
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (e : X ≅ Y) {a b : ℤ}
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived X a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived Y a b := fun N i hi =>
  (h N i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso
      ((derivedTensor.mapIso e).app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N))).symm

end ScalarLift

/-! ### Relatively flat representatives -/

/-- A module flat over `A` is flat over `R` when `A` is flat over `R`. -/
private lemma flat_restrictScalars {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (X : ModuleCat.{w} A) [Module.Flat A X] :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj X) := by
  let Y := (ModuleCat.restrictScalars (algebraMap R A)).obj X
  have : Module.Flat A Y := ‹Module.Flat A X›
  have : IsScalarTower R A Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.trans R A Y

/-- Truncating below does not affect an upper bound: the truncation receives an epimorphism from
the complex in each degree. -/
lemma truncGE_isStrictlyLE {C : Type*} [Category C] [Abelian C]
    (P : CochainComplex C ℤ) (a b : ℤ) [P.IsStrictlyLE b] :
    (P.truncGE a).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have : Epi ((P.πTruncGE a).f i) := by
    unfold CochainComplex.πTruncGE
    infer_instance
  exact IsZero.of_epi ((P.πTruncGE a).f i) (P.isZero_of_isStrictlyLE b i hi)

/-- The truncation of a complex at `a` has in degree `a` the cokernel of the incoming
differential. -/
private noncomputable def truncGEXIsoCokernel {C : Type*} [Category C] [Abelian C]
    (P : CochainComplex C ℤ) (a : ℤ) : (P.truncGE a).X a ≅ cokernel (P.d (a - 1) a) :=
  P.truncGEXIsoOpcycles a ≪≫
    IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel (a - 1) a (by simp))
      (colimit.isColimit _)

/-- The cokernel of a map from a finite module to a finitely presented module is finitely
presented. -/
lemma finitePresentation_cokernel {A : Type u} [Ring A]
    {M N : ModuleCat.{v} A} [Module.Finite A M] [Module.FinitePresentation A N] (f : M ⟶ N) :
    Module.FinitePresentation A (cokernel f : ModuleCat.{v} A) := by
  have : Module.FinitePresentation A (N ⧸ LinearMap.range f.hom) :=
    Module.finitePresentation_of_surjective (LinearMap.range f.hom).mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range f.hom)
  exact Module.FinitePresentation.of_equiv
    (ModuleCat.cokernelIsoRangeQuotient f).symm.toLinearEquiv

/-- Truncating below a complex of finite free modules leaves finitely presented terms: the term
at the truncation degree is the cokernel of a map of finite free modules. -/
private lemma finitePresentation_truncGE_X {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{v} A) ℤ)
    (hP : ∀ i, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) (a i : ℤ) :
    Module.FinitePresentation A ((P.truncGE a).X i) := by
  rcases lt_trichotomy i a with hi | hiEq | hi
  · have : Subsingleton ((P.truncGE a).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((P.truncGE a).isZero_of_isStrictlyGE a i hi)
    infer_instance
  · subst hiEq
    have := (hP (i - 1)).1
    have := (hP i).1
    have := (hP i).2
    have := Module.finitePresentation_of_projective A (P.X i)
    have := finitePresentation_cokernel (P.d (i - 1) i)
    exact Module.FinitePresentation.of_equiv (truncGEXIsoCokernel P i).symm.toLinearEquiv
  · have := (hP i).1
    have := (hP i).2
    have := Module.finitePresentation_of_projective A (P.X i)
    exact Module.FinitePresentation.of_equiv (P.truncGEXIso a i hi).symm.toLinearEquiv

/-! ### Total tensor products of complexes -/

section TensorComplex

variable {A : Type u} [CommRing A]

/-- A bounded above complex of flat modules is K-flat (Stacks 064K), at a carrier universe above
the ring's. -/
private lemma kFlat_of_isStrictlyLE_flat
    (E : CochainComplex (ModuleCat.{max u v} A) ℤ) (d : ℤ) [E.IsStrictlyLE d]
    (hflat : ∀ n : ℤ, Module.Flat A (E.X n)) : CochainComplex.KFlat.{u, v} E :=
  have : ∀ n : ℤ, Module.Flat A (E.X n) := hflat
  CochainComplex.KFlat.kFlat_of_flat.{u, v} E d

/-- A tensor product of objects one of which is zero is zero. -/
private lemma isZero_tensorObj_of_left_or_right {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] {X Y : C} (h : IsZero X ∨ IsZero Y) :
    IsZero (X ⊗ Y) :=
  h.elim (fun hX => (tensorRight Y).map_isZero hX) fun hY => (tensorLeft X).map_isZero hY

/-- A term of the total tensor product vanishes when in every bidegree one of the two factors
does. -/
private lemma isZero_tensorLeftLarge_X
    (E X : CochainComplex (ModuleCat.{max u v} A) ℤ) (i : ℤ)
    (h : ∀ p q : ℤ, p + q = i → IsZero (E.X p) ∨ IsZero (X.X q)) :
    IsZero (((CochainComplex.tensorLeftLarge.{u, v} E).obj X).X i) := by
  let _ := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := A)
  let _ := ModuleCat.liftedModuleMonoidal.{u, v} (R := A)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  exact (isZero_tensorObj_of_left_or_right (h p q hpq)).eq_of_src _ _

/-- The total tensor product of two complexes vanishing above `a` and above `b` vanishes above
`a + b`. -/
private lemma tensorLeftLarge_isStrictlyLE
    (E X : CochainComplex (ModuleCat.{max u v} A) ℤ) (a b : ℤ)
    [E.IsStrictlyLE a] [X.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE ((CochainComplex.tensorLeftLarge.{u, v} E).obj X) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine isZero_tensorLeftLarge_X E X i fun p q hpq => ?_
  by_cases hp : a < p
  · exact Or.inl (E.isZero_of_isStrictlyLE a p hp)
  · exact Or.inr (X.isZero_of_isStrictlyLE b q (by omega))

/-- The total tensor product of two complexes vanishing below `a` and below `b` vanishes below
`a + b`. -/
private lemma tensorLeftLarge_isStrictlyGE
    (E X : CochainComplex (ModuleCat.{max u v} A) ℤ) (a b : ℤ)
    [E.IsStrictlyGE a] [X.IsStrictlyGE b] :
    CochainComplex.IsStrictlyGE ((CochainComplex.tensorLeftLarge.{u, v} E).obj X) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine isZero_tensorLeftLarge_X E X i fun p q hpq => ?_
  by_cases hp : p < a
  · exact Or.inl (E.isZero_of_isStrictlyGE a p hp)
  · exact Or.inr (X.isZero_of_isStrictlyGE b q (by omega))

/-- A coproduct of finite modules all but finitely many of which vanish is finite. -/
private lemma finite_coproduct_of_isZero {ι : Type} (F : ι → ModuleCat.{max u v} A)
    [∀ j, Module.Finite A (F j)] [HasCoproduct F] (s : Finset ι)
    (hs : ∀ j, j ∉ s → IsZero (F j)) : Module.Finite A (∐ F : ModuleCat.{max u v} A) := by
  classical
  let G : s → ModuleCat.{max u v} A := fun j => F j
  have : Module.Finite A (∐ G : ModuleCat.{max u v} A) :=
    Module.Finite.equiv (ModuleCat.coprodIsoDirectSum G).symm.toLinearEquiv
  let f : (∐ G : ModuleCat.{max u v} A) ⟶ ∐ F := Sigma.desc (fun j => Sigma.ι F j)
  have : Epi f := by
    constructor
    intro Z g h heq
    apply Sigma.hom_ext
    intro j
    by_cases hj : j ∈ s
    · simpa only [f, Category.assoc, Sigma.ι_desc_assoc] using
        congrArg (fun k => Sigma.ι G ⟨j, hj⟩ ≫ k) heq
    · exact (hs j hj).eq_of_src _ _
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)

/-- The total tensor product of two bounded above complexes of finite free modules has finite
free terms: in each degree only finitely many bidegrees contribute, and each contribution is a
tensor product of finite free modules. -/
private lemma tensorLeftLarge_finiteFree
    (E X : CochainComplex (ModuleCat.{max u v} A) ℤ) (a b : ℤ)
    [E.IsStrictlyLE a] [X.IsStrictlyLE b]
    (hE : ∀ i : ℤ, Module.Finite A (E.X i) ∧ Module.Free A (E.X i))
    (hX : ∀ i : ℤ, Module.Finite A (X.X i) ∧ Module.Free A (X.X i)) (i : ℤ) :
    Module.Finite A (((CochainComplex.tensorLeftLarge.{u, v} E).obj X).X i) ∧
      Module.Free A (((CochainComplex.tensorLeftLarge.{u, v} E).obj X).X i) := by
  classical
  let _ := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := A)
  let _ := ModuleCat.liftedModuleMonoidal.{u, v} (R := A)
  let F : {pq : ℤ × ℤ // pq.1 + pq.2 = i} → ModuleCat.{max u v} A :=
    fun pq => E.X pq.1.1 ⊗ X.X pq.1.2
  have : ∀ j, Module.Finite A (F j) := fun j => by
    have := (hE j.1.1).1
    have := (hX j.1.2).1
    exact Module.Finite.tensorProduct A _ _
  have : ∀ j, Module.Free A (F j) := fun j => by
    have := (hE j.1.1).2
    have := (hX j.1.2).2
    show Module.Free A (TensorProduct A (E.X j.1.1) (X.X j.1.2))
    infer_instance
  show Module.Finite A (∐ F : ModuleCat.{max u v} A) ∧
    Module.Free A (∐ F : ModuleCat.{max u v} A)
  refine ⟨?_, Module.Free.of_equiv (ModuleCat.coprodIsoDirectSum F).symm.toLinearEquiv⟩
  let s : Finset {pq : ℤ × ℤ // pq.1 + pq.2 = i} :=
    (Finset.Icc (i - b) a).map
      ⟨fun p => ⟨(p, i - p), by omega⟩, fun p q h => congrArg (fun z => z.1.1) h⟩
  apply finite_coproduct_of_isZero F s
  intro j hj
  have hj' : ¬(i - b ≤ j.1.1 ∧ j.1.1 ≤ a) := by
    intro h
    apply hj
    apply Finset.mem_map.mpr
    refine ⟨j.1.1, Finset.mem_Icc.mpr h, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl (show i - j.1.1 = j.1.2 by have := j.2; omega)
  by_cases hp : a < j.1.1
  · exact isZero_tensorObj_of_left_or_right (Or.inl (E.isZero_of_isStrictlyLE a _ hp))
  · exact isZero_tensorObj_of_left_or_right
      (Or.inr (X.isZero_of_isStrictlyLE b _ (by have := j.2; omega)))

end TensorComplex

/-! ### Relative flatness of a total tensor product -/

/-- Flatness over the base is preserved when tensoring over the algebra a module flat over the
algebra with a module flat over the base. -/
@[ega "IV 2.1.5" "special case"]
private lemma flat_tensorProduct {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (P Q : Type*) [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module A P] [IsScalarTower R A P]
    [Module R Q] [Module A Q] [IsScalarTower R A Q]
    [Module.Flat A P] [Module.Flat R Q] : Module.Flat R (P ⊗[A] Q) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ f hf
  let g := TensorProduct.AlgebraTensorModule.lTensor A Q f
  have hg : Function.Injective g := Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hgP : Function.Injective (g.lTensor P) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  let eX := TensorProduct.AlgebraTensorModule.assoc R A A P Q X
  let eY := TensorProduct.AlgebraTensorModule.assoc R A A P Q Y
  have he : eY.toLinearMap.restrictScalars R ∘ₗ f.lTensor (P ⊗[A] Q) =
      (g.lTensor P).restrictScalars R ∘ₗ eX.toLinearMap.restrictScalars R := by
    apply TensorProduct.ext'
    intro z x
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => rfl
    | add z z' hz hz' =>
        simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hz hz'
  intro x y h
  apply eX.injective
  apply hgP
  exact (LinearMap.congr_fun he x).symm.trans ((congrArg eY h).trans (LinearMap.congr_fun he y))

/-- Restriction of scalars to `R` of a tensor product over `A` is flat when the left factor is
flat over `A` and the right factor is flat over `R`. This is `flat_tensorProduct` with the module
structures in the shape `ModuleCat.restrictScalars` produces them. -/
@[ega "IV 2.1.5" "special case"]
private lemma flat_restrictScalars_tensorProduct {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] (Y Z : ModuleCat.{w} A) [Module.Flat A Y]
    (hZ : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj Z)) :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj
      (ModuleCat.of A (TensorProduct A Y Z))) := by
  let _ : Module R Y := ((ModuleCat.restrictScalars (algebraMap R A)).obj Y).isModule
  let _ : Module R Z := ((ModuleCat.restrictScalars (algebraMap R A)).obj Z).isModule
  have : IsScalarTower R A Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A Z := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R Z := hZ
  exact flat_tensorProduct Y Z

section Relative

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Flat R A] [Algebra.FinitePresentation R A]
  (derivedTensor : DerivedCategory (ModuleCat.{max u v w} R) ⥤
      DerivedCategory (ModuleCat.{max u v w} R) ⥤ DerivedCategory (ModuleCat.{max u v w} R))
  (comparison : ∀ N : ModuleCat.{max u v w} R,
    DerivedCategory.Q ⋙ derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj N) ⟶
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ N : ModuleCat.{max u v w} R,
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R) (ComplexShape.up ℤ)))

omit [Module.Flat R A] [Algebra.FinitePresentation R A] in
/-- A bounded complex whose terms are flat over `R` after restriction of scalars represents an
object of `D(A)` whose restriction to `R` has finite Tor dimension. -/
theorem hasFiniteTorDimension_of_bounded_relativelyFlat
    (K : DerivedCategory (ModuleCat.{max u v w} A))
    (P : CochainComplex (ModuleCat.{max u v w} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i)))
    (e : K ≅ DerivedCategory.Q.obj P) :
    HasFiniteTorDimension derivedTensor comparison isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) := by
  let U := ModuleCat.restrictScalars (algebraMap R A)
  let PR : CochainComplex (ModuleCat.{max u v w} R) ℤ :=
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : PR.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff PR a).mpr
    (fun i hi => U.map_isZero (P.isZero_of_isStrictlyGE a i hi))
  have : PR.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff PR b).mpr
    (fun i hi => U.map_isZero (P.isZero_of_isStrictlyLE b i hi))
  exact ⟨a, b, hasTorAmplitude_of_iso.{u, max v w} derivedTensor comparison isLeftDerived
    (U.mapDerivedCategory.mapIso e ≪≫ U.mapDerivedCategoryFactors.app P).symm
    (hasTorAmplitude_of_bounded_flat.{u, max v w} derivedTensor comparison isLeftDerived PR a b
      hflat)⟩

/-- Truncating a relatively perfect object's finite free representative at the lower bound of its
Tor amplitude gives a bounded representative whose terms are flat over `R`. Above the truncation
degree the terms are the finite free ones, flat over `R` by transitivity of flatness; at the
truncation degree the term is a cokernel, flat over `R` by Stacks 0653; and the truncation is
quasi-isomorphic to the representative because Tor amplitude forces the cohomology to vanish
below the bound. -/
theorem exists_bounded_relativelyFlat_representative
    (K : DerivedCategory (ModuleCat.{max u v w} A))
    (hK : IsRelativelyPerfect derivedTensor comparison isLeftDerived K) :
    ∃ (P : CochainComplex (ModuleCat.{max u v w} A) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Flat R
        ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i))) ∧
      (∀ i : ℤ, Module.FinitePresentation A (P.X i)) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨⟨P, hP, ⟨eP⟩⟩, a, b, htor⟩ := hK
  obtain ⟨d, hd⟩ := hP.upperBound
  have : P.IsStrictlyLE d := hd
  let U := ModuleCat.restrictScalars (algebraMap R A)
  let PR : CochainComplex (ModuleCat.{max u v w} R) ℤ :=
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hflat : ∀ i : ℤ, Module.Flat R (PR.X i) := by
    intro i
    have := (hP.finiteFree i).2
    exact flat_restrictScalars (P.X i)
  have hPR : HasTorAmplitude derivedTensor comparison isLeftDerived
      (DerivedCategory.Q.obj PR) a b :=
    hasTorAmplitude_of_iso.{u, max v w} derivedTensor comparison isLeftDerived
      ((U.mapDerivedCategory.mapIso eP).symm ≪≫ U.mapDerivedCategoryFactors.app P) htor
  have ht := isZero_homology_tensor_of_torAmplitude.{u, max v w} derivedTensor comparison
    isLeftDerived PR a b
    ⟨d, fun j hj => U.map_isZero (P.isZero_of_isStrictlyLE d j hj)⟩ hflat hPR
  have hGE : P.IsGE a := by
    let _ := ModuleCat.liftedModuleMonoidalStruct.{u, max v w} (R := R)
    let _ := ModuleCat.liftedModuleMonoidal.{u, max v w} (R := R)
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff]
    apply ((P.sc i).exact_map_iff_of_faithful U).mp
    apply (HomologicalComplex.exactAt_iff_isZero_homology PR i).mpr
    let eU : ((tensorModuleRight (𝟙_ (ModuleCat.{max u v w} R))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj PR ≅ PR :=
      HomologicalComplex.Hom.isoOfComponents (fun j => ρ_ (PR.X j))
        (fun j k _ => (rightUnitor_naturality (PR.d j k)).symm)
    exact (ht _ i (Or.inl hi)).of_iso (HomologicalComplex.homologyMapIso eU i).symm
  refine ⟨P.truncGE a, a, d, inferInstance, truncGE_isStrictlyLE P a d, ?_, ?_,
    ⟨eP.symm ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE a))⟩⟩
  · intro i
    rcases lt_trichotomy i a with hi | hiEq | hi
    · have : Subsingleton (U.obj ((P.truncGE a).X i)) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (U.map_isZero ((P.truncGE a).isZero_of_isStrictlyGE a i hi))
      infer_instance
    · subst hiEq
      have : Module.Flat R (cokernel (U.map (P.d (i - 1) i)) : ModuleCat.{max u v w} R) :=
        cokernel_flat_of_termwise_isZero_homology.{u, max v w} PR i b hflat ht
      exact Module.Flat.of_linearEquiv
        (U.mapIso (truncGEXIsoCokernel P i) ≪≫
          PreservesCokernel.iso U (P.d (i - 1) i)).toLinearEquiv
    · have : Module.Flat R (U.obj (P.X i)) := hflat i
      exact Module.Flat.of_linearEquiv (U.mapIso (P.truncGEXIso a i hi)).toLinearEquiv
  · exact finitePresentation_truncGE_X P hP.finiteFree a

/-! ### The two assertions of Stacks 0DHU -/

/-- **Stacks 0DHU.** For a flat, finitely presented ring map `R → A`, a perfect object of `D(A)`
is perfect relative to `R`: a bounded complex of finite projective `A`-modules representing it is
pseudo-coherent by Stacks 064U, and its terms are flat over `R` by transitivity of flatness, so
its restriction to `R` has finite Tor dimension. -/
@[stacks 0DHU]
theorem isRelativelyPerfect_of_isPerfect (K : DerivedCategory (ModuleCat.{max u v w} A))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    IsRelativelyPerfect.{u, v, w} derivedTensor comparison isLeftDerived K := by
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hK
  have := hGE
  have := hLE
  have hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i)) := by
    intro i
    have : Module.Projective A (P.X i) := hprojective i
    exact flat_restrictScalars (P.X i)
  have hpc := pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective.{v, max u v w} K 0
  exact ⟨hpc.2.1.2 ⟨P, ⟨b, hLE⟩, fun i => ⟨hfinite i, hprojective i⟩, ⟨e.symm⟩⟩,
    hasFiniteTorDimension_of_bounded_relativelyFlat derivedTensor comparison isLeftDerived K P a b
      hflat e⟩

omit [Module.Flat R A] [Algebra.FinitePresentation R A] in
/-- The terms of a total tensor product are flat over `R` when the left factor has terms flat
over `A` and the right factor has terms flat over `R`: each term is a coproduct of tensor
products `E^p ⊗_A X^q`, and flatness over `R` passes to those and to coproducts. -/
private lemma tensorLeftLarge_flat_restrictScalars
    (E X : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (hE : ∀ n : ℤ, Module.Flat A (E.X n))
    (hX : ∀ n : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (X.X n))) (i : ℤ) :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj
      (((CochainComplex.tensorLeftLarge.{v, max u w} E).obj X).X i)) := by
  classical
  let _ := ModuleCat.liftedModuleMonoidalStruct.{v, max u w} (R := A)
  let _ := ModuleCat.liftedModuleMonoidal.{v, max u w} (R := A)
  let U := ModuleCat.restrictScalars (algebraMap R A)
  let F : {pq : ℤ × ℤ // pq.1 + pq.2 = i} → ModuleCat.{max u v w} A :=
    fun pq => E.X pq.1.1 ⊗ X.X pq.1.2
  have hFflat : ∀ j, Module.Flat R (U.obj (F j)) := by
    intro j
    have := hE j.1.1
    exact flat_restrictScalars_tensorProduct (E.X j.1.1) (X.X j.1.2) (hX j.1.2)
  show Module.Flat R (U.obj (∐ F : ModuleCat.{max u v w} A))
  have hds : Module.Flat R
      (U.obj (ModuleCat.of A (DirectSum _ fun j => (F j : Type (max u v w))))) := by
    have : Module.Flat R (DirectSum _ fun j => (U.obj (F j) : Type (max u v w))) :=
      Module.Flat.directSum
    exact this
  exact Module.Flat.of_linearEquiv (U.mapIso (ModuleCat.coprodIsoDirectSum F)).toLinearEquiv

variable
  (derivedTensorA : DerivedCategory (ModuleCat.{max u v w} A) ⥤
      DerivedCategory (ModuleCat.{max u v w} A) ⥤ DerivedCategory (ModuleCat.{max u v w} A))
  (kFlatComparison : ∀ (E X : CochainComplex (ModuleCat.{max u v w} A) ℤ),
    CochainComplex.KFlat.{v, max u w} E →
      ((derivedTensorA.obj (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj X) ≅
        DerivedCategory.Q.obj ((CochainComplex.tensorLeftLarge.{v, max u w} E).obj X)))

include kFlatComparison in
/-- **Stacks 0DHU.** For a flat, finitely presented ring map `R → A`, the derived tensor product
over `A` of a perfect object of `D(A)` with an `R`-perfect object is `R`-perfect.

Pseudo-coherence: a bounded-above finite free representative of the perfect object is K-flat, so
the derived tensor product is computed by the total tensor product with a bounded-above finite
free representative of the `R`-perfect object, and that has bounded-above finite free terms.

Finite Tor dimension: a *bounded* finite projective representative of the perfect object is also
K-flat, and the `R`-perfect object has a bounded representative whose terms are flat over `R`
(Stacks 0653); the total tensor product of the two is bounded with terms flat over `R`. -/
@[stacks 0DHU]
theorem isRelativelyPerfect_derivedTensor
    (K M : DerivedCategory (ModuleCat.{max u v w} A))
    (hK : StacksDraft.Perfect.IsPerfect K)
    (hM : IsRelativelyPerfect.{u, v, w} derivedTensor comparison isLeftDerived M) :
    IsRelativelyPerfect.{u, v, w} derivedTensor comparison isLeftDerived
      ((derivedTensorA.obj K).obj M) := by
  obtain ⟨E, a, b, hEGE, hELE, hEfinite, hEprojective, ⟨eE⟩⟩ := hK
  have := hEGE
  have := hELE
  have hEflat : ∀ n : ℤ, Module.Flat A (E.X n) := fun n =>
    have : Module.Projective A (E.X n) := hEprojective n
    inferInstance
  have hEkFlat : CochainComplex.KFlat.{v, max u w} E :=
    kFlat_of_isStrictlyLE_flat.{v, max u w} E b hEflat
  refine ⟨?_, ?_⟩
  · have hKpc : IsPseudoCoherent K :=
      (pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective.{v, max u v w} K 0).2.1.2
        ⟨E, ⟨b, hELE⟩, fun i => ⟨hEfinite i, hEprojective i⟩, ⟨eE.symm⟩⟩
    obtain ⟨E', hE', ⟨eE'⟩⟩ := hKpc
    obtain ⟨c, hc⟩ := hE'.upperBound
    have := hc
    have hE'flat : ∀ n : ℤ, Module.Flat A (E'.X n) := fun n =>
      have : Module.Free A (E'.X n) := (hE'.finiteFree n).2
      inferInstance
    have hE'kFlat : CochainComplex.KFlat.{v, max u w} E' :=
      kFlat_of_isStrictlyLE_flat.{v, max u w} E' c hE'flat
    obtain ⟨F, hF, ⟨eF⟩⟩ := hM.1
    obtain ⟨d, hd⟩ := hF.upperBound
    have := hd
    have hLE := tensorLeftLarge_isStrictlyLE.{v, max u w} E' F c d
    refine ⟨(CochainComplex.tensorLeftLarge.{v, max u w} E').obj F, ⟨⟨c + d, hLE⟩,
      tensorLeftLarge_finiteFree.{v, max u w} E' F c d hE'.finiteFree hF.finiteFree⟩, ⟨?_⟩⟩
    exact (kFlatComparison E' F hE'kFlat).symm ≪≫
      (derivedTensorA.obj (DerivedCategory.Q.obj E')).mapIso eF ≪≫
      (derivedTensorA.mapIso eE').app M
  · obtain ⟨P, a', b', hPGE, hPLE, hPflat, -, ⟨eP⟩⟩ :=
      exists_bounded_relativelyFlat_representative derivedTensor comparison isLeftDerived M hM
    have := hPGE
    have := hPLE
    have := tensorLeftLarge_isStrictlyGE.{v, max u w} E P a a'
    have := tensorLeftLarge_isStrictlyLE.{v, max u w} E P b b'
    exact hasFiniteTorDimension_of_bounded_relativelyFlat derivedTensor comparison isLeftDerived
      ((derivedTensorA.obj K).obj M) ((CochainComplex.tensorLeftLarge.{v, max u w} E).obj P)
      (a + a') (b + b')
      (tensorLeftLarge_flat_restrictScalars E P hEflat hPflat)
      ((derivedTensorA.mapIso eE).app M ≪≫
        (derivedTensorA.obj (DerivedCategory.Q.obj E)).mapIso eP ≪≫
        kFlatComparison E P hEkFlat)

end Relative

end PseudoCoherence
