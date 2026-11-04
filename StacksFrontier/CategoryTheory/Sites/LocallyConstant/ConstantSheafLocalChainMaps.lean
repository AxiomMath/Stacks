module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafLocalSections
public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# Chain maps out of single complexes of constant sheaves

This file carries the degreewise half of the induction of Stacks Tag 094G: the criterion for a
chain map out of a single complex to be surjective on cohomology in its degree, the resulting
local realization of a surjection onto the top cohomology sheaf by a chain map, and the
bookkeeping on mapping cones and cocones — their cohomological amplitude, their finiteness, and
their compatibility with an exact functor — by which the induction step reduces the amplitude.

## Main results

* `Stacks.ConstantSheaf.epi_homologyMap_from_single`: when a chain map out of a single complex
  is, in its own degree and read through cycles, surjective onto the cohomology, it is
  surjective on cohomology.
* `Stacks.ConstantSheaf.exists_cover_homology_epi_of_constantFree_epi`: a surjection from a
  constant finite free sheaf onto the degree-`b` cohomology is locally realized by a chain map.
* `Stacks.ConstantSheaf.mappingCone_isGE_isLE_and_prop`: the mapping cone of such a chain map
  has amplitude one less, with cohomology still in the weak Serre class.
* `Stacks.ConstantSheaf.exists_chainMap_to_single_of_derived`: a derived morphism to a single
  complex in the top degree comes from a chain map.

## References

* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.ConstantSheaf

universe v u w m

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] constantSheaf Functor.sheafPushforwardContinuous
  HomologicalComplex.homologyFunctor HomologicalComplex.homology
  ShortComplex.LeftHomologyData.map

attribute [local instance] overPullback_preservesFiniteLimits
  overPullback_preservesFiniteColimits overPullback_preservesZeroMorphisms
/-- For an exact functor `F` and a left homology datum `hl` of a short complex `S`, the
projection to homology commutes with the comparison isomorphisms that `hl` induces between the
homology and the cycles of `S.map F` and the images under `F` of those of `S`. Stated at a
general `hl` so that every object occurring is a projection of `hl` and no comparison of a
structure field with its definition is needed. -/
private lemma homologyπ_comp_mapHomologyIso_of_leftHomologyData
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex A) (hl : S.LeftHomologyData) :
    (S.map F).homologyπ ≫ ((hl.map F).homologyIso ≪≫ F.mapIso hl.homologyIso.symm).hom =
      ((hl.map F).cyclesIso ≪≫ F.mapIso hl.cyclesIso.symm).hom ≫ F.map S.homologyπ := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [show (hl.map F).π = F.map hl.π from rfl, ← F.map_comp, ← F.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

/-- **The projection to homology commutes with the comparison isomorphisms of an exact functor.**
For an exact functor `F` and a short complex `S`, the square formed by
`CategoryTheory.ShortComplex.mapCyclesIso` and `CategoryTheory.ShortComplex.mapHomologyIso`
together with the two projections `homologyπ` commutes. -/
private lemma homologyπ_comp_mapHomologyIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex A) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.homologyData.left.mapHomologyIso_eq F, S.homologyData.left.mapCyclesIso_eq F]
  exact homologyπ_comp_mapHomologyIso_of_leftHomologyData F S S.homologyData.left

/-- A chain map from a single complex in degree `b` to the degreewise image of `T` under an exact
functor `F` is surjective on degree-`b` cohomology as soon as its degree-`b` component, read
through the cycles of `T`, is surjective onto `F` of the degree-`b` cohomology of `T`. -/
private lemma epi_homologyMap_from_single
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : CochainComplex A ℤ) (b : ℤ) (E : B)
    (t : E ⟶ F.obj (T.cycles b))
    (α : (HomologicalComplex.single B (.up ℤ) b).obj E ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj T)
    (hα : α.f b = (HomologicalComplex.singleObjXSelf _ _ _).hom ≫ t ≫ F.map (T.iCycles b))
    [Epi (t ≫ F.map (T.homologyπ b))] : Epi (HomologicalComplex.homologyMap α b) := by
  -- The comparison isomorphisms, with their endpoints ascribed in the `HomologicalComplex`
  -- spelling, so that every composite written below is type-correct on the nose.
  let eZ : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T).cycles b ≅
      F.obj (T.cycles b) := (T.sc b).mapCyclesIso F
  let eH : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T).homology b ≅
      F.obj (T.homology b) := (T.sc b).mapHomologyIso F
  have hZ : eZ.hom ≫ F.map (T.iCycles b) =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T).iCycles b :=
    ShortComplex.mapCyclesIso_hom_iCycles (T.sc b) F
  have hπ : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T).homologyπ b ≫ eH.hom =
      eZ.hom ≫ F.map (T.homologyπ b) :=
    homologyπ_comp_mapHomologyIso F (T.sc b)
  have ht : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) b E).inv ≫
      HomologicalComplex.cyclesMap α b ≫ eZ.hom = t := by
    refine (cancel_mono (F.map (T.iCycles b))).mp ?_
    rw [Category.assoc, Category.assoc, hZ, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles, hα,
      Iso.inv_hom_id_assoc]
  have h : (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b E).inv ≫
      HomologicalComplex.homologyMap α b ≫ eH.hom = t ≫ F.map (T.homologyπ b) := by
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
      Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
      hπ, ← Category.assoc, ← Category.assoc]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ F.map (T.homologyπ b)) ht
  have h1 : Epi ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b E).inv ≫
      HomologicalComplex.homologyMap α b ≫ eH.hom) := by rw [h]; infer_instance
  have h2 : Epi (HomologicalComplex.homologyMap α b ≫ eH.hom) :=
    epi_of_epi (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b E).inv _
  exact (epi_comp_iff_of_isIso _ eH.hom).mp h2

/-- Restriction of sheaves of modules to a slice site is additive. -/
lemma overPullback_additive
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] (U : C) :
    (J.overPullback (ModuleCat.{max u v w} Λ) U).Additive where
  map_add := by intros; rfl

attribute [local instance] overPullback_additive

/-- A surjection from a constant finite free sheaf onto the degree-`b` cohomology of a complex is,
over a covering family, realized by a chain map out of the single complex in degree `b` which
is surjective on degree-`b` cohomology. -/
lemma exists_cover_homology_epi_of_constantFree_epi
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ)
    (b : ℤ) (n : ℕ)
    (g : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj
      (freeMod.{v, u, w} Λ n) ⟶ T.homology b) [Epi g] (X : C) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ α : (HomologicalComplex.single _ (.up ℤ) b).obj
            ((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj
              (freeMod.{v, u, w} Λ n)) ⟶
            ((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex (.up ℤ)).obj T,
          Epi (HomologicalComplex.homologyMap α b) := by
  obtain ⟨I, U, f, hf, ht⟩ := exists_cover_lift_constantFree J (T.homologyπ b) n g X
  refine ⟨I, U, f, hf, fun i => ?_⟩
  obtain ⟨t, ht⟩ := ht i
  let F := J.overPullback (ModuleCat.{max u v w} Λ) (U i)
  have : Epi (t ≫ F.map (T.homologyπ b)) := by rw [ht]; infer_instance
  have hz (k : ℤ) (_ : (ComplexShape.up ℤ).Rel b k) :
      (t ≫ F.map (T.iCycles b)) ≫ F.map (T.d b k) = 0 := by
    rw [Category.assoc, ← F.map_comp, T.iCycles_d, F.map_zero, comp_zero]
  let α : (HomologicalComplex.single _ (.up ℤ) b).obj
      ((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj
        (freeMod.{v, u, w} Λ n)) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj T :=
    HomologicalComplex.mkHomFromSingle (t ≫ F.map (T.iCycles b)) hz
  refine ⟨α, epi_homologyMap_from_single F T b _ t α ?_⟩
  simp [α]

private lemma epi_derived_homologyMap
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {T T' : CochainComplex A ℤ} (α : T ⟶ T') (b : ℤ)
    [Epi (HomologicalComplex.homologyMap α b)] :
    Epi ((DerivedCategory.homologyFunctor A b).map (DerivedCategory.Q.map α)) := by
  rw [← epi_comp_iff_of_isIso _ ((DerivedCategory.homologyFunctorFactors A b).hom.app T'),
    DerivedCategory.homologyFunctorFactors_hom_naturality]
  refine epi_comp' ?_ ?_ <;> infer_instance

private lemma weakSerre_homology_single
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] (E : A) (hE : P E) (b : ℤ) :
    ∀ n, P ((DerivedCategory.homologyFunctor A n).obj
      ((DerivedCategory.singleFunctor A b).obj E)) := by
  intro n
  by_cases hn : n = b
  · subst n
    exact P.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app E).symm hE
  · apply P.prop_of_isZero
    by_cases h : n < b
    · exact DerivedCategory.isZero_of_isGE _ b n h
    · exact DerivedCategory.isZero_of_isLE _ b n (by omega)

/-- The mapping cone of a chain map from a complex concentrated in degree `b`
which is surjective on degree-`b` cohomology has cohomology in `[a, b - 1]`, and
its cohomology keeps a weak Serre property shared by the source and the target. -/
lemma mappingCone_isGE_isLE_and_prop
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    (T : CochainComplex A ℤ) (a b : ℤ) (hab : a < b)
    [T.IsStrictlyGE a] [T.IsStrictlyLE b]
    (hT : ∀ n, P ((DerivedCategory.homologyFunctor A n).obj (DerivedCategory.Q.obj T)))
    (E : A) (hE : P E)
    (α : (CochainComplex.singleFunctor A b).obj E ⟶ T)
    [Epi (HomologicalComplex.homologyMap α b)] :
    (DerivedCategory.Q.obj (CochainComplex.mappingCone α)).IsGE a ∧
      (DerivedCategory.Q.obj (CochainComplex.mappingCone α)).IsLE (b - 1) ∧
      ∀ n, P ((DerivedCategory.homologyFunctor A n).obj
        (DerivedCategory.Q.obj (CochainComplex.mappingCone α))) := by
  have hdist := DerivedCategory.mappingCone_triangle_distinguished α
  have : (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle α)).obj₁.IsGE b :=
    inferInstanceAs (((DerivedCategory.singleFunctor A b).obj E).IsGE b)
  have : (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle α)).obj₁.IsLE b :=
    inferInstanceAs (((DerivedCategory.singleFunctor A b).obj E).IsLE b)
  have : (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle α)).obj₂.IsGE a :=
    inferInstanceAs ((DerivedCategory.Q.obj T).IsGE a)
  have : (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle α)).obj₂.IsLE b :=
    inferInstanceAs ((DerivedCategory.Q.obj T).IsLE b)
  have : Epi ((DerivedCategory.homologyFunctor A b).map
      (DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle α)).mor₁) :=
    epi_derived_homologyMap α b
  exact ⟨isGE_obj₃_of_distinguished _ hdist a b hab,
    isLE_obj₃_of_distinguished_of_epi _ hdist b,
    weakSerre_homology_obj₃ P _ hdist (weakSerre_homology_single P E hE b) hT⟩

/-- The cohomology sheaves of the restriction of a complex to a slice site are locally constant of
finite type as soon as those of the complex are. -/
lemma finiteTypeLocallyConstant_homology_over
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (n : ℤ)
    (hT : IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology n)) (U : C) :
    IsFiniteTypeLocallyConstantModuleSheaf (J.over U) Λ
      ((((J.overPullback (ModuleCat.{max u v w} Λ) U).mapHomologicalComplex
        (.up ℤ)).obj T).homology n) :=
  finiteTypeLocallyConstant_of_iso (J.over U) Λ
    ((T.sc n).mapHomologyIso (J.overPullback (ModuleCat.{max u v w} Λ) U)).symm
    (finiteTypeLocallyConstant_over J _ hT U)

private lemma mappingCone_isFG
    {Λ : Type w} [CommRing Λ]
    {P Q : CochainComplex (ModuleCat.{m} Λ) ℤ} (f : P ⟶ Q)
    (hP : ∀ n, ModuleCat.isFG Λ (P.X n))
    (hQ : ∀ n, ModuleCat.isFG Λ (Q.X n)) (n : ℤ) :
    ModuleCat.isFG Λ ((CochainComplex.mappingCone f).X n) := by
  rw [ModuleCat.isFG_iff]
  let : Module.Finite Λ (P.X (n + 1)) := (ModuleCat.isFG_iff _).mp (hP (n + 1))
  let : Module.Finite Λ (Q.X n) := (ModuleCat.isFG_iff _).mp (hQ n)
  show Module.Finite Λ
    (HomologicalComplex.homotopyCofiber.X (C := ModuleCat.{m} Λ) f n)
  rw [Module.Finite.equiv_iff
    (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) (by simp)).toLinearEquiv,
    Module.Finite.equiv_iff (ModuleCat.biprodIsoProd _ _).toLinearEquiv]
  infer_instance

private lemma mappingCocone_isFG
    {Λ : Type w} [CommRing Λ]
    {P Q : CochainComplex (ModuleCat.{m} Λ) ℤ} (f : P ⟶ Q)
    (hP : ∀ n, ModuleCat.isFG Λ (P.X n))
    (hQ : ∀ n, ModuleCat.isFG Λ (Q.X n)) (n : ℤ) :
    ModuleCat.isFG Λ ((CochainComplex.mappingCocone f).X n) := by
  simpa only [CochainComplex.mappingCocone, CochainComplex.shiftFunctor_obj_X',
    sub_eq_add_neg] using
    mappingCone_isFG f hP hQ (n - 1)

private lemma mappingCocone_isZero_outside
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q)
    (a b c d : ℤ)
    (hP : ∀ n, n ∉ Set.Icc a b → IsZero (P.X n))
    (hQ : ∀ n, n ∉ Set.Icc c d → IsZero (Q.X n))
    (n : ℤ) (hn : n ∉ Set.Icc (min a (c + 1)) (max b (d + 1))) :
    IsZero ((CochainComplex.mappingCocone f).X n) := by
  show IsZero ((CochainComplex.mappingCone f).X (n - 1))
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · simpa only [sub_add_cancel] using hP n (by simp only [Set.mem_Icc] at *; omega)
  · exact hQ (n - 1) (by simp only [Set.mem_Icc] at *; omega)

/-- An additive functor preserving finite biproducts commutes with the mapping cocone of a chain
map. -/
noncomputable def mapMappingCoconeIso
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {B : Type*} [Category* B] [Preadditive B] [HasBinaryBiproducts B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteBiproducts F]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) :
    (F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCocone f) ≅
      CochainComplex.mappingCocone ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let e₁ := (F.mapCochainComplexShiftIso (-1)).app (CochainComplex.mappingCone f)
  let e₂ := (shiftFunctor (CochainComplex B ℤ) (-1)).mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f F)
  exact e₁ ≪≫ e₂

/-- The mapping cocone of a chain map from a complex supported in `[a, b - 1]` with finitely
generated terms to the single complex on a finitely generated module in degree `b - 1` is
supported in `[a, b]` and has finitely generated terms. -/
lemma mappingCocone_single_finite_bounded
    {Λ : Type w} [CommRing Λ]
    {P : CochainComplex (ModuleCat.{m} Λ) ℤ}
    (a b : ℤ) (hab : a ≤ b)
    (hP : ∀ n, n ∉ Set.Icc a (b - 1) → IsZero (P.X n))
    (hfgP : ∀ n, ModuleCat.isFG Λ (P.X n))
    (E : ModuleCat.{m} Λ) (hE : ModuleCat.isFG Λ E)
    (f : P ⟶ (CochainComplex.singleFunctor _ (b - 1)).obj E) :
    (∀ n, n ∉ Set.Icc a b → IsZero ((CochainComplex.mappingCocone f).X n)) ∧
      (∀ n, ModuleCat.isFG Λ ((CochainComplex.mappingCocone f).X n)) := by
  have hs (n : ℤ) (hn : n ∉ Set.Icc (b - 1) (b - 1)) :
      IsZero (((CochainComplex.singleFunctor _ (b - 1)).obj E).X n) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simpa using hn)
  have hfgs (n : ℤ) :
      ModuleCat.isFG Λ (((CochainComplex.singleFunctor _ (b - 1)).obj E).X n) := by
    by_cases hn : n = b - 1
    · subst n
      show ModuleCat.isFG Λ
        (((HomologicalComplex.single _ (.up ℤ) (b - 1)).obj E).X (b - 1))
      simpa only [HomologicalComplex.single_obj_X_self] using hE
    · rw [ModuleCat.isFG_iff]
      let : Subsingleton (((CochainComplex.singleFunctor _ (b - 1)).obj E).X n) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) (b - 1) E n hn)
      infer_instance
  exact ⟨fun n hn => mappingCocone_isZero_outside f a (b - 1) (b - 1) (b - 1) hP hs n
    (by simpa only [sub_add_cancel, min_eq_left hab,
      max_eq_right (by omega : b - 1 ≤ b)] using hn),
    mappingCocone_isFG f hfgP hfgs⟩

private noncomputable def topHomologyMapToSingle
    {A : Type*} [Category* A] [Abelian A]
    (P : CochainComplex A ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (E : A) (h : P.homology b ⟶ E) :
    P ⟶ (CochainComplex.singleFunctor A b).obj E := by
  have hz : P.d b (b + 1) = 0 :=
    (P.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_zero_of_tgt _
  let e := P.iCyclesIso b (b + 1) (by simp) hz
  let p : P.X b ⟶ E := e.inv ≫ P.homologyπ b ≫ h
  have hp (i : ℤ) (_ : (ComplexShape.up ℤ).Rel i b) :
      P.d i b ≫ p = 0 := by
    have he : P.d i b ≫ e.inv = P.toCycles i b := by
      rw [← cancel_mono (P.iCycles b), Category.assoc]
      simp only [e, HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id,
        HomologicalComplex.toCycles_i]
    dsimp [p]
    rw [← Category.assoc (P.d i b) e.inv (P.homologyπ b ≫ h), he]
    simp only [← Category.assoc, P.toCycles_comp_homologyπ, zero_comp]
  exact HomologicalComplex.mkHomToSingle p hp

private lemma homologyMap_topHomologyMapToSingle
    {A : Type*} [Category* A] [Abelian A]
    (P : CochainComplex A ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (E : A) (h : P.homology b ⟶ E) :
    HomologicalComplex.homologyMap (topHomologyMapToSingle P b E h) b ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b E).hom = h := by
  let α : P ⟶ (HomologicalComplex.single A (.up ℤ) b).obj E :=
    topHomologyMapToSingle P b E h
  apply (cancel_epi (P.homologyπ b)).mp
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
  show P.cyclesMap α b ≫
    (((HomologicalComplex.single A (.up ℤ) b).obj E).homologyπ b ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b E).hom) = _
  rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
    HomologicalComplex.cyclesMap_i]
  unfold α topHomologyMapToSingle
  simp only [HomologicalComplex.mkHomToSingle_f, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simp only [← Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id,
    Category.id_comp]

private lemma homologyFunctor_map_injective_of_isLE_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (X Y : DerivedCategory A) (b : ℤ) [X.IsLE b] [Y.IsGE b] :
    Function.Injective (fun f : X ⟶ Y => (DerivedCategory.homologyFunctor A b).map f) := by
  let e := (shiftFunctorZero (DerivedCategory A) ℤ).app Y
  have h := (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    X Y b b 0 b (by omega) le_rfl).1
  intro f g hfg
  have heq : f ≫ e.inv = g ≫ e.inv := by
    apply h
    show (DerivedCategory.homologyFunctor A b).map (f ≫ e.inv) ≫
        ((DerivedCategory.homologyFunctor A 0).shiftIso 0 b b (by omega)).hom.app Y =
      (DerivedCategory.homologyFunctor A b).map (g ≫ e.inv) ≫
        ((DerivedCategory.homologyFunctor A 0).shiftIso 0 b b (by omega)).hom.app Y
    simp only [Functor.map_comp, hfg]
  exact (cancel_mono e.inv).mp heq

/-- A morphism in the derived category from a complex supported in degrees `≤ b` to the single
complex in degree `b` is the image of a chain map. -/
lemma exists_chainMap_to_single_of_derived
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (P : CochainComplex A ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (E : A)
    (γ : DerivedCategory.Q.obj P ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor A b).obj E)) :
    ∃ f : P ⟶ (CochainComplex.singleFunctor A b).obj E,
      DerivedCategory.Q.map f = γ := by
  let S := (CochainComplex.singleFunctor A b).obj E
  let H := DerivedCategory.homologyFunctor A b
  let p := (DerivedCategory.homologyFunctorFactors A b).app P
  let q := (DerivedCategory.homologyFunctorFactors A b).app S
  let e := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b E
  let h : P.homology b ⟶ E := p.inv ≫ H.map γ ≫ q.hom ≫ e.hom
  refine ⟨topHomologyMapToSingle P b E h, ?_⟩
  apply homologyFunctor_map_injective_of_isLE_isGE
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj S) b
  -- Presenting the composite as the `hom` of a single isomorphism keeps instance search
  -- from having to unfold the `let`-bound isomorphisms to see that it is one.
  have hqe : Mono (q.hom ≫ e.hom) := inferInstanceAs (Mono (q ≪≫ e).hom)
  apply (cancel_mono (q.hom ≫ e.hom)).mp
  let f := topHomologyMapToSingle P b E h
  calc
    H.map (DerivedCategory.Q.map f) ≫ q.hom ≫ e.hom =
        (p.hom ≫ HomologicalComplex.homologyMap f b) ≫ e.hom := by
      simpa only [H, p, q, S, Iso.app_hom, Category.assoc] using
        congrArg (fun z => z ≫ e.hom) (DerivedCategory.homologyFunctorFactors_hom_naturality f b)
    _ = p.hom ≫ h := by
      rw [Category.assoc, homologyMap_topHomologyMapToSingle]
    _ = H.map γ ≫ q.hom ≫ e.hom := by
      simp only [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Over a covering family, the degree-`b` cohomology of the restriction of a complex receives a
surjection from the constant sheaf on a finite free module. -/
lemma exists_cover_constantFree_epi_homology
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ) (b : ℤ)
    (hT : IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology b)) (X : C) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ (n : ℕ) (g : (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj
          (freeMod.{v, u, w} Λ n) ⟶
          ((((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex
            (.up ℤ)).obj T).homology b)), Epi g := by
  obtain ⟨I, U, f, hf, h⟩ := exists_cover_constantFree_epi J Λ (T.homology b) hT X
  refine ⟨I, U, f, hf, fun i => ?_⟩
  obtain ⟨E, e, n, g, hg, _, hc⟩ := h i
  -- Presenting `e.hom ≫ φ.inv` as the `hom` of a single isomorphism lets instance search see
  -- that it is an isomorphism.
  let φ := e ≪≫ ((T.sc b).mapHomologyIso
    (J.overPullback (ModuleCat.{max u v w} Λ) (U i))).symm
  exact ⟨n, (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).map g ≫ φ.hom,
    epi_comp' hc (inferInstanceAs (Epi φ.hom))⟩

/-- A complex whose class in the derived category is concentrated in a single degree `b`, with
locally constant finite type cohomology, has over a covering family a model by the constant
sheaf complex of a single finitely generated module. -/
lemma exists_cover_constantComplex_model_of_isGE_of_isLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (X : C) (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ)
    (b : ℤ) [(DerivedCategory.Q.obj T).IsGE b] [(DerivedCategory.Q.obj T).IsLE b]
    (hT : IsFiniteTypeLocallyConstantModuleSheaf J Λ (T.homology b)) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ (P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ),
          (∀ n, n ∉ Set.Icc b b → IsZero (P.X n)) ∧
          (∀ n, ModuleCat.isFG Λ (P.X n)) ∧
          Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex
              (.up ℤ)).obj T) ≅
            DerivedCategory.Q.obj
              (((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
                (.up ℤ)).obj P)) := by
  have hT' := finiteTypeLocallyConstant_of_iso J Λ
    ((DerivedCategory.homologyFunctorFactors _ b).app T).symm hT
  obtain ⟨T', e, I, U, f, hf, h⟩ :=
    exists_cover_constantComplex_representation_of_isGE_of_isLE J Λ X
      (DerivedCategory.Q.obj T) b hT'
  refine ⟨I, U, f, hf, fun i => ?_⟩
  obtain ⟨P, hP, hfg, ⟨eP⟩⟩ := h i
  let F := J.overPullback (ModuleCat.{max u v w} Λ) (U i)
  exact ⟨P, hP, hfg, ⟨(F.mapDerivedCategoryFactors.app T).symm ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app T' ≪≫ eP⟩⟩

end Stacks.ConstantSheaf

end
