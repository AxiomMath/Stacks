module

public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Countability of the bounded derived category

A category is *essentially countable* when all of its morphism sets and its set of isomorphism
classes of objects are countable. The bounded derived category of an essentially countable
abelian category is again essentially countable: a bounded object is represented by a bounded
complex over the skeleton, of which there are countably many, and every morphism of the derived
category is represented by a roof between two such complexes.

## Main definitions

* `CategoryTheory.EssentiallyCountableCategory`: countability of morphisms and of isomorphism
  classes of objects.

## Main results

* `AlgebraicGeometry.boundedDerivedCategory_essentiallyCountable`: the bounded derived category of
  an essentially countable abelian category is essentially countable.

## References

* [Stacks Project, Tag 0G0V](https://stacks.math.columbia.edu/tag/0G0V)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

/-- A category is essentially countable if all of its morphism sets and its set of
isomorphism classes of objects are countable. -/
public class EssentiallyCountableCategory (C : Type u) [Category.{v} C] : Prop where
  /-- Every morphism set is countable. -/
  countableHom : ∀ X Y : C, Countable (X ⟶ Y)
  /-- The set of isomorphism classes of objects is countable. -/
  countableSkeleton : Countable (Skeleton C)

attribute [instance] EssentiallyCountableCategory.countableHom
attribute [instance] EssentiallyCountableCategory.countableSkeleton

end CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [Category.{v} A] [Abelian A]
  [EssentiallyCountableCategory A]
open CategoryTheory.Limits

/-- Morphisms between objects of the skeleton are countable. -/
private noncomputable local instance skeletonHomCountable (X Y : Skeleton A) :
    Countable (X ⟶ Y) :=
  Countable.of_equiv _ (Functor.FullyFaithful.ofFullyFaithful (fromSkeleton A)).homEquiv.symm

/-- The preadditive structure on the skeleton transferred from the category along the
equivalence. -/
noncomputable local instance : Preadditive (Skeleton A) :=
  Preadditive.ofFullyFaithful (skeletonEquivalence A).fullyFaithfulFunctor

/-- The skeleton has an initial object. -/
noncomputable local instance : HasInitial (Skeleton A) :=
  hasInitial_of_equivalence (skeletonEquivalence A).functor

/-- The skeleton has a zero object. -/
noncomputable local instance : HasZeroObject (Skeleton A) := hasZeroObject_of_hasInitial_object

local notation "Sk" => Skeleton A

/-- The integers between `a` and `b`, as a subtype. -/
private abbrev Interval (a b : ℤ) := {i : ℤ // i ∈ Set.Icc a b}

/-- A code for a complex supported in degrees `a` to `b`: its terms and all maps between them. -/
private abbrev BCode (C : Type*) [Category C] (a b : ℤ) :=
  Σ X : Interval a b → C, ∀ i j : Interval a b, X i ⟶ X j

/-- The property of a cochain complex of being strictly bounded. -/
private abbrev BoundedComplexOver (C : Type*) [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (K : CochainComplex C ℤ) : Prop :=
  ∃ a b, K.IsStrictlyGE a ∧ K.IsStrictlyLE b

/-- The property of a cochain complex over the skeleton of being strictly bounded. -/
private abbrev IsBoundedComplex (K : CochainComplex Sk ℤ) := BoundedComplexOver Sk K

/-- Bounds for a bounded complex, packaged as a single pair. -/
private lemma existsBoundsPairOver {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (K : CochainComplex C ℤ) (hK : BoundedComplexOver C K) :
    ∃ p : ℤ × ℤ, K.IsStrictlyGE p.1 ∧ K.IsStrictlyLE p.2 := by
  rcases hK with ⟨a, b, hGE, hLE⟩
  exact ⟨(a, b), hGE, hLE⟩

/-- The code of a bounded complex over the skeleton. -/
private noncomputable def encodeBounded (K : {K : CochainComplex Sk ℤ // IsBoundedComplex K}) :
    Σ p : ℤ × ℤ, BCode Sk p.1 p.2 := by
  let p := Classical.choose (existsBoundsPairOver K.1 K.2)
  let hp := Classical.choose_spec (existsBoundsPairOver K.1 K.2)
  letI : K.1.IsStrictlyGE p.1 := hp.1
  letI : K.1.IsStrictlyLE p.2 := hp.2
  exact ⟨p, ⟨fun i ↦ K.1.X i.val, fun i j ↦ K.1.d i.val j.val⟩⟩

/-- Two families of maps between equal families of objects, equal up to the transport of the
object equality, commute with that transport. -/
private lemma diff_comm_of_heq {ι : Type*} {C : Type*} [Category C]
    {X Y : ι → C} {dX : ∀ i j, X i ⟶ X j} {dY : ∀ i j, Y i ⟶ Y j}
    (hX : X = Y) (hd : HEq dX dY) :
    ∀ i j, dX i j ≫ eqToHom (congrFun hX j) = eqToHom (congrFun hX i) ≫ dY i j := by
  intro i j
  cases hX
  cases hd
  simp

omit [EssentiallyCountableCategory A] in
/-- A bounded complex over the skeleton is determined by its code. -/
private lemma encodeBounded_injective :
    Function.Injective (encodeBounded (A := A)) := by
  classical
  intro K L h
  set pK : ℤ × ℤ := Classical.choose (existsBoundsPairOver K.1 K.2)
  set pL : ℤ × ℤ := Classical.choose (existsBoundsPairOver L.1 L.2)
  rcases (Sigma.ext_iff (x := encodeBounded K) (y := encodeBounded L)).mp h with
    ⟨hp, hcode⟩
  have hcode' : HEq
      (⟨fun i ↦ K.1.X i.val, fun i j ↦ K.1.d i.val j.val⟩ : BCode Sk pK.1 pK.2)
      (⟨fun i ↦ L.1.X i.val, fun i j ↦ L.1.d i.val j.val⟩ : BCode Sk pL.1 pL.2) := by
    simpa [encodeBounded, pK, pL] using hcode
  have hbound : pK = pL := by simpa [encodeBounded, pK, pL] using hp
  have hK : K.1.IsStrictlyGE pK.1 ∧ K.1.IsStrictlyLE pK.2 :=
    Classical.choose_spec (existsBoundsPairOver K.1 K.2)
  have hL : L.1.IsStrictlyGE pK.1 ∧ L.1.IsStrictlyLE pK.2 := by
    rw [hbound]
    exact Classical.choose_spec (existsBoundsPairOver L.1 L.2)
  have hz : ∀ {M : CochainComplex Sk ℤ} {i : ℤ}, M.IsStrictlyGE pK.1 → M.IsStrictlyLE pK.2 →
      i ∉ Set.Icc pK.1 pK.2 → IsZero (M.X i) := by
    intro M i ha hb hi
    rcases not_and_or.mp hi with h | h
    · exact (CochainComplex.isStrictlyGE_iff M pK.1).1 ha i (by omega)
    · exact (CochainComplex.isStrictlyLE_iff M pK.2).1 hb i (by omega)
  rw [← hbound] at hcode'
  let dataK : BCode Sk pK.1 pK.2 :=
    ⟨fun i ↦ K.1.X i.val, fun i j ↦ K.1.d i.val j.val⟩
  let dataL : BCode Sk pK.1 pK.2 :=
    ⟨fun i ↦ L.1.X i.val, fun i j ↦ L.1.d i.val j.val⟩
  have hdata : dataK = dataL := eq_of_heq hcode'
  have hterms : (fun i : Interval pK.1 pK.2 ↦ K.1.X i.val) =
      (fun i : Interval pK.1 pK.2 ↦ L.1.X i.val) := congrArg Sigma.fst hdata
  have htermsAll : K.1.X = L.1.X := by
    funext i
    by_cases hi : i ∈ Set.Icc pK.1 pK.2
    · exact congrFun hterms ⟨i, hi⟩
    · exact skeleton_skeletal (C := A)
        ⟨(hz hK.1 hK.2 hi).iso (hz hL.1 hL.2 hi)⟩
  have hdf : HEq (fun (i j : Interval pK.1 pK.2) ↦ K.1.d i.val j.val)
      (fun (i j : Interval pK.1 pK.2) ↦ L.1.d i.val j.val) :=
    (Sigma.mk.inj_iff.mp hdata).2
  apply Subtype.ext
  refine HomologicalComplex.ext (V := Sk) (C₁ := K.1) (C₂ := L.1) htermsAll fun i j _ ↦ ?_
  by_cases hi : i ∈ Set.Icc pK.1 pK.2
  · by_cases hj : j ∈ Set.Icc pK.1 pK.2
    · exact diff_comm_of_heq hterms hdf ⟨i, hi⟩ ⟨j, hj⟩
    · exact (hz hL.1 hL.2 hj).eq_of_tgt _ _
  · exact (hz hK.1 hK.2 hi).eq_of_src _ _

/-- There are countably many bounded complexes over the skeleton. -/
private lemma countableBoundedComplexes :
    Countable {K : CochainComplex Sk ℤ // IsBoundedComplex K} :=
  encodeBounded_injective.countable

/-- There are countably many maps between two bounded complexes. -/
private lemma boundedMapCountableA (K L : CochainComplex A ℤ)
    (hK : BoundedComplexOver A K) (hL : BoundedComplexOver A L) : Countable (K ⟶ L) := by
  classical
  let pK := Classical.choose (existsBoundsPairOver K hK)
  let pL := Classical.choose (existsBoundsPairOver L hL)
  let a := min pK.1 pL.1
  let b := max pK.2 pL.2
  let : Fintype (Interval a b) := (Set.finite_Icc a b).fintype
  let enc : (K ⟶ L) → (∀ i : Interval a b, K.X i.val ⟶ L.X i.val) :=
    fun f i ↦ f.f i.val
  have : Countable (∀ i : Interval a b, K.X i.val ⟶ L.X i.val) := by infer_instance
  refine Function.Injective.countable (f := enc) ?_
  intro f g h
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i ∈ Set.Icc a b
  · exact congrFun h ⟨i, hi⟩
  · have hpK := Classical.choose_spec (existsBoundsPairOver K hK)
    rcases not_and_or.mp hi with hlt | hgt
    · exact ((CochainComplex.isStrictlyGE_iff K pK.1).1 hpK.1 i (by omega)).eq_of_src _ _
    · exact ((CochainComplex.isStrictlyLE_iff K pK.2).1 hpK.2 i (by omega)).eq_of_src _ _

/-- The equivalence from the skeleton is additive. -/
private noncomputable local instance skeletonFunctorAdditive : (fromSkeleton A).Additive :=
  (skeletonEquivalence A).fullyFaithfulFunctor.additive_ofFullyFaithful
/-- The equivalence onto the skeleton is additive. -/
private noncomputable local instance skeletonInverseAdditive :
    (skeletonEquivalence A).inverse.Additive :=
  Equivalence.additive_inverse_of_FullyFaithful (skeletonEquivalence A)

/-- The equivalence between complexes over the skeleton and complexes over the category. -/
private noncomputable def skeletonComplexEquiv :
    CochainComplex Sk ℤ ≌ CochainComplex A ℤ :=
  (skeletonEquivalence A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- An additive functor preserves strict lower bounds of complexes. -/
private lemma isStrictlyGE_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
    {X : CochainComplex C ℤ} {m n : ℤ}
    (h : X.IsStrictlyGE n) (hmn : m ≤ n) :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) m := by
  apply (CochainComplex.isStrictlyGE_iff _ m).2
  intro i hi
  simpa only [Functor.mapHomologicalComplex_obj_X] using
    Functor.map_isZero F ((CochainComplex.isStrictlyGE_iff X n).1 h i (by omega))

/-- An additive functor preserves strict upper bounds of complexes. -/
private lemma isStrictlyLE_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
    {X : CochainComplex C ℤ} {m n : ℤ}
    (h : X.IsStrictlyLE n) (hnm : n ≤ m) :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) m := by
  apply (CochainComplex.isStrictlyLE_iff _ m).2
  intro i hi
  simpa only [Functor.mapHomologicalComplex_obj_X] using
    Functor.map_isZero F ((CochainComplex.isStrictlyLE_iff X n).1 h i (by omega))

omit [EssentiallyCountableCategory A] in
/-- A fully faithful additive functor neither creates nor destroys boundedness of a complex. -/
private lemma bounded_mapComplex_iff (F : Sk ⥤ A) [F.Additive] [F.Full] [F.Faithful]
    (K : CochainComplex Sk ℤ) :
    BoundedComplexOver A ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ↔
      BoundedComplexOver Sk K := by
  constructor
  · rintro ⟨a, b, hGE, hLE⟩
    refine ⟨a, b, ?_, ?_⟩
    · apply (CochainComplex.isStrictlyGE_iff K a).2
      intro i hi
      apply IsZero.of_full_of_faithful_of_isZero F (K.X i)
      simpa only [Functor.mapHomologicalComplex_obj_X] using
        (CochainComplex.isStrictlyGE_iff _ a).1 hGE i hi
    · apply (CochainComplex.isStrictlyLE_iff K b).2
      intro i hi
      apply IsZero.of_full_of_faithful_of_isZero F (K.X i)
      simpa only [Functor.mapHomologicalComplex_obj_X] using
        (CochainComplex.isStrictlyLE_iff _ b).1 hLE i hi
  · rintro ⟨a, b, hGE, hLE⟩
    exact ⟨a, b, isStrictlyGE_map F hGE le_rfl, isStrictlyLE_map F hLE le_rfl⟩

/-- The functor on cochain complexes induced by the equivalence from the skeleton. -/
private noncomputable abbrev FHC : CochainComplex Sk ℤ ⥤ CochainComplex A ℤ :=
  (fromSkeleton A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- A code for a morphism of the derived category: a bounded complex over the skeleton together
with a roof out of it. -/
private abbrev FractionCode (K L : CochainComplex A ℤ) :=
  Σ K' : {X : CochainComplex Sk ℤ // IsBoundedComplex X},
    ((FHC.obj K'.1 ⟶ K) × (FHC.obj K'.1 ⟶ L))

/-- There are countably many codes for morphisms of the derived category. -/
private lemma countableFractionCode (K L : CochainComplex A ℤ)
    (hK : BoundedComplexOver A K) (hL : BoundedComplexOver A L) :
    Countable (FractionCode K L) := by
  classical
  have hfib : ∀ K' : {X : CochainComplex Sk ℤ // IsBoundedComplex X},
      Countable ((FHC.obj K'.1 ⟶ K) × (FHC.obj K'.1 ⟶ L)) := by
    intro K'
    have hK' : BoundedComplexOver A (FHC.obj K'.1) :=
      (bounded_mapComplex_iff (F := fromSkeleton A) K'.1).2 K'.2
    have : Countable (FHC.obj K'.1 ⟶ K) := boundedMapCountableA _ _ hK' hK
    have : Countable (FHC.obj K'.1 ⟶ L) := boundedMapCountableA _ _ hK' hL
    infer_instance
  have := countableBoundedComplexes (A := A)
  infer_instance

omit [EssentiallyCountableCategory A] in
/-- A strictly bounded complex is isomorphic to the image of a bounded complex over the
skeleton. -/
private lemma exists_boundedComplex_iso (M : CochainComplex A ℤ) {a b : ℤ}
    (hGE : M.IsStrictlyGE a) (hLE : M.IsStrictlyLE b) :
    ∃ K : {K : CochainComplex Sk ℤ // IsBoundedComplex K}, Nonempty (FHC.obj K.1 ≅ M) := by
  let Msk := (skeletonComplexEquiv).inverse.obj M
  have e : FHC.obj Msk ≅ M := by
    simpa [FHC, Msk, skeletonComplexEquiv] using (skeletonComplexEquiv).counitIso.app M
  exact ⟨⟨Msk, (bounded_mapComplex_iff (F := fromSkeleton A) Msk).1
    ⟨a, b, CochainComplex.isStrictlyGE_of_iso e.symm (n := a),
      CochainComplex.isStrictlyLE_of_iso e.symm (n := b)⟩⟩, ⟨e⟩⟩

/-- There are countably many morphisms in the derived category between the images of two
bounded complexes over the skeleton. -/
private lemma derivedHom_countableSk (K L : CochainComplex Sk ℤ)
    (hK : IsBoundedComplex K) (hL : IsBoundedComplex L) :
    Countable (DerivedCategory.Q.obj (FHC.obj K) ⟶ DerivedCategory.Q.obj (FHC.obj L)) := by
  classical
  let pK := Classical.choose (existsBoundsPairOver K hK)
  let pL := Classical.choose (existsBoundsPairOver L hL)
  let a := min pK.1 pL.1
  let b := max pK.2 pL.2
  have : Countable (FractionCode (FHC.obj K) (FHC.obj L)) :=
    countableFractionCode _ _ ((bounded_mapComplex_iff (F := fromSkeleton A) K).2 hK)
      ((bounded_mapComplex_iff (F := fromSkeleton A) L).2 hL)
  let codeToHom : FractionCode (FHC.obj K) (FHC.obj L) →
      (DerivedCategory.Q.obj (FHC.obj K) ⟶ DerivedCategory.Q.obj (FHC.obj L)) := fun c ↦
    if hs : IsIso (DerivedCategory.Q.map c.2.1) then
      have := hs
      inv (DerivedCategory.Q.map c.2.1) ≫ DerivedCategory.Q.map c.2.2
    else 0
  refine Function.Surjective.countable (f := codeToHom) fun f ↦ ?_
  have hpK := Classical.choose_spec (existsBoundsPairOver K hK)
  have hpL := Classical.choose_spec (existsBoundsPairOver L hL)
  have : (FHC.obj K).IsStrictlyGE a := isStrictlyGE_map (fromSkeleton A) hpK.1 (min_le_left _ _)
  have : (FHC.obj K).IsStrictlyLE b := isStrictlyLE_map (fromSkeleton A) hpK.2 (le_max_left _ _)
  have : (FHC.obj L).IsStrictlyGE a := isStrictlyGE_map (fromSkeleton A) hpL.1 (min_le_right _ _)
  obtain ⟨M, hGEM, hLEM, s, hs, g, hf⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE a b f
  have : M.IsStrictlyGE a := hGEM
  have : M.IsStrictlyLE b := hLEM
  obtain ⟨Msk, ⟨e⟩⟩ := exists_boundedComplex_iso M hGEM hLEM
  let c : FractionCode (FHC.obj K) (FHC.obj L) := ⟨Msk, (e.hom ≫ s, e.hom ≫ g)⟩
  refine ⟨c, ?_⟩
  have hs' : IsIso (DerivedCategory.Q.map (e.hom ≫ s)) := by
    rw [Functor.map_comp]
    infer_instance
  calc
    codeToHom c = inv (DerivedCategory.Q.map (e.hom ≫ s)) ≫
        DerivedCategory.Q.map (e.hom ≫ g) := by
      simp only [codeToHom, c, dite_eq_left hs']
    _ = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by
      simp only [Functor.map_comp, IsIso.inv_comp, Category.assoc,
        IsIso.inv_hom_id_assoc]
    _ = f := hf.symm

omit [EssentiallyCountableCategory A] in
/-- A strictly bounded-below complex is bounded below. -/
private lemma strictGE_to_GE (K : CochainComplex A ℤ) (n : ℤ)
    (hK : K.IsStrictlyGE n) : K.IsGE n := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact HomologicalComplex.ExactAt.of_isZero
    ((CochainComplex.isStrictlyGE_iff K n).1 hK i hi)

omit [EssentiallyCountableCategory A] in
/-- A strictly bounded-above complex is bounded above. -/
private lemma strictLE_to_LE (K : CochainComplex A ℤ) (n : ℤ)
    (hK : K.IsStrictlyLE n) : K.IsLE n := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact HomologicalComplex.ExactAt.of_isZero
    ((CochainComplex.isStrictlyLE_iff K n).1 hK i hi)

omit [EssentiallyCountableCategory A] in
/-- Bounds for a bounded derived object, packaged as a single pair. -/
private lemma derivedBounds (X : DerivedCategory.Bounded A) :
    ∃ p : ℤ × ℤ, X.1.IsGE p.1 ∧ X.1.IsLE p.2 := by
  rcases X.2 with ⟨⟨a, hGE⟩, ⟨b, hLE⟩⟩
  exact ⟨(a, b), hGE, hLE⟩

/-- A representative of a bounded derived object by a bounded complex over the skeleton. -/
private noncomputable def boundedDerivedRepresentative
    (X : DerivedCategory.Bounded A) :
    Σ K : {K : CochainComplex Sk ℤ // IsBoundedComplex K},
      (DerivedCategory.Q.obj (FHC.obj K.1) ≅ X.1) := by
  classical
  let p := Classical.choose (derivedBounds X)
  have hp := Classical.choose_spec (derivedBounds X)
  haveI : X.1.IsGE p.1 := hp.1
  haveI : X.1.IsLE p.2 := hp.2
  choose M hGEM hLEM eX using
    DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE X.1 p.1 p.2
  let hM := exists_boundedComplex_iso M hGEM hLEM
  exact ⟨hM.choose, asIso (DerivedCategory.Q.map (Classical.choice hM.choose_spec).hom) ≪≫
    (Classical.choice eX).symm⟩

/-- There are countably many morphisms between two bounded derived objects. -/
private lemma derivedBoundedHom_countable (X Y : DerivedCategory.Bounded A) :
    Countable (X ⟶ Y) := by
  classical
  let rX := boundedDerivedRepresentative X
  let rY := boundedDerivedRepresentative Y
  have : Countable
      (DerivedCategory.Q.obj (FHC.obj rX.1.1) ⟶
        DerivedCategory.Q.obj (FHC.obj rY.1.1)) :=
    derivedHom_countableSk rX.1.1 rY.1.1 rX.1.2 rY.1.2
  have : Countable (X.1 ⟶ Y.1) :=
    Countable.of_equiv _ (Iso.homCongr rX.2 rY.2)
  exact Function.Injective.countable (f := fun f : X ⟶ Y ↦ f.hom)
    fun _ _ h ↦ ObjectProperty.hom_ext (DerivedCategory.TStructure.t.bounded) h

/-- The bounded derived object of a bounded complex over the skeleton. -/
private noncomputable def boundedDerivedObjectOfSk
    (K : {K : CochainComplex Sk ℤ // IsBoundedComplex K}) :
    DerivedCategory.Bounded A := by
  classical
  let h := (bounded_mapComplex_iff (F := fromSkeleton A) K.1).2 K.2
  let p := Classical.choose (existsBoundsPairOver _ h)
  have hp := Classical.choose_spec (existsBoundsPairOver _ h)
  haveI : (DerivedCategory.Q.obj (FHC.obj K.1)).IsGE p.1 :=
    (DerivedCategory.isGE_Q_obj_iff _ p.1).2 (strictGE_to_GE _ _ hp.1)
  haveI : (DerivedCategory.Q.obj (FHC.obj K.1)).IsLE p.2 :=
    (DerivedCategory.isLE_Q_obj_iff _ p.2).2 (strictLE_to_LE _ _ hp.2)
  exact ⟨DerivedCategory.Q.obj (FHC.obj K.1),
    ⟨⟨p.1, inferInstance⟩, ⟨p.2, inferInstance⟩⟩⟩

/-- The isomorphism class of the bounded derived object of a bounded complex over the skeleton. -/
private noncomputable def boundedDerivedObjectSkeletonMap :
    {K : CochainComplex Sk ℤ // IsBoundedComplex K} →
      Skeleton (DerivedCategory.Bounded A) := fun K ↦
  toSkeleton (boundedDerivedObjectOfSk K)

omit [EssentiallyCountableCategory A] in
/-- Every isomorphism class of a bounded derived object comes from a bounded complex over the
skeleton. -/
private lemma boundedDerivedObjectSkeletonMap_surjective :
    Function.Surjective (boundedDerivedObjectSkeletonMap (A := A)) := by
  classical
  intro S
  let X := (fromSkeleton (DerivedCategory.Bounded A)).obj S
  let r := boundedDerivedRepresentative X
  let Ksk := r.1
  let Y := boundedDerivedObjectOfSk Ksk
  have eY : Y.1 ≅ X.1 := by simpa [Y, boundedDerivedObjectOfSk] using r.2
  have eFull : Y ≅ X := ObjectProperty.isoMk
    (P := DerivedCategory.TStructure.t.bounded) eY
  refine ⟨Ksk, ?_⟩
  change toSkeleton Y = S
  rw [CategoryTheory.congr_toSkeleton_of_iso eFull]
  simp [X, toSkeleton_fromSkeleton_obj]

/-- There are countably many isomorphism classes of bounded derived objects. -/
private lemma countableBoundedDerivedSkeleton :
    Countable (Skeleton (DerivedCategory.Bounded A)) := by
  have := countableBoundedComplexes (A := A)
  exact (boundedDerivedObjectSkeletonMap_surjective (A := A)).countable

end

/-- The bounded derived category of an essentially countable abelian category is essentially
countable. -/
@[stacks 0G0V]
public instance boundedDerivedCategory_essentiallyCountable
    (A : Type u) [Category.{v} A] [Abelian A] [EssentiallyCountableCategory A] :
    EssentiallyCountableCategory (DerivedCategory.Bounded A) :=
  ⟨fun X Y ↦ derivedBoundedHom_countable X Y, countableBoundedDerivedSkeleton⟩

end AlgebraicGeometry
