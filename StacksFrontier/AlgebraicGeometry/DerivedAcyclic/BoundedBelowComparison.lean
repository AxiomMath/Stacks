module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Right derived functors on unbounded complexes with acyclic terms

Let `F : A ⥤ B` be an additive functor between abelian categories with `A` Grothendieck
abelian, and let `RF : D(A) ⥤ D(B)` be a right derived functor of `K(F)` followed by
localization, with canonical comparison `α`. This file collects what is needed to decide
whether `α` is invertible at a complex all of whose terms are right acyclic for `F`.

Two reductions are provided.

For a complex that is bounded below, Leray's acyclicity criterion
(`CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`) answers the question
for the *bounded below* derived functor, and
`Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic` transports that answer to the
unbounded one: a bounded-below complex admits a bounded-below resolution by termwise injectives,
hence a K-injective one, and on a K-injective complex both comparisons are invertible.

For a general complex, the stupid truncations `σ^{≥a}K` are bounded below and the maps
`σ^{≥a}K → K` become invertible in a given degree once `a` is small enough. The degreewise split
short exact sequence `σ^{≥a+1}K → K → σ^{≤a}K` gives a distinguished triangle in `K(A)`
(`Stacks.DerivedAcyclic.stupidTruncTriangleh`), which is how a bound on the cohomological
dimension of `RF` turns the truncations into a computation of `RF K` degree by degree.

## Main results

* `Stacks.DerivedAcyclic.stupidTruncTriangleh_distinguished`: the stupid truncation triangle of a
  cochain complex is distinguished in the homotopy category.
* `Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor`: a right derived functor on the
  unbounded derived category is triangulated.
* `Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic`: the comparison into a right derived
  functor is invertible at a bounded-below complex with right-acyclic terms.
* `Stacks.DerivedAcyclic.isIso_homologyFunctor_map_termwise_stupidTrunc`: the termwise functor
  sees `σ^{≥a}K → K` as an isomorphism on cohomology in degrees above `a`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.DerivedAcyclic

export CategoryTheory.Functor (stupidTruncTriangleh stupidTruncTriangleh_distinguished)

section Truncations

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]

/-- Above the truncation level the inclusion of a stupid truncation is a degreewise
isomorphism. -/
lemma isIso_ιStupidTrunc_f (K : CochainComplex A ℤ) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f i) :=
  K.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE a)
    (i := (i - a).toNat) (by change a + ((i - a).toNat : ℤ) = i; omega)

/-- A stupid truncation in degrees `≥ a` is bounded below. -/
lemma plus_stupidTruncGE (K : CochainComplex A ℤ) (a : ℤ) :
    CochainComplex.plus A (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)) := by
  refine ⟨a, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) i
    (by rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]; omega)

end Truncations

/-- A stupid truncation in degrees `≤ a` lies in `D^{≤a}`. -/
lemma isLE_stupidTruncLE {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (K : CochainComplex A ℤ) (a : ℤ) :
    (DerivedCategory.Q.obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).IsLE a := by
  show DerivedCategory.TStructure.t.IsLE _ a
  refine ⟨K.stupidTrunc (ComplexShape.embeddingUpIntLE a), Iso.refl _, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) i
    (by rw [ComplexShape.notMem_range_embeddingUpIntLE_iff]; omega)

/-- Shifting a cohomology vanishing statement: if `H^i(K[a]) = 0` then `H^{a+i}(K) = 0`. -/
lemma isZero_homology_shift_of_isZero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (a i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((shiftFunctor (DerivedCategory C) a).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor C (a + i)).obj K) := by
  set F := DerivedCategory.homologyFunctor C 0
  have e : (F.shift i).obj ((shiftFunctor (DerivedCategory C) a).obj K) ≅
      (F.shift (a + i)).obj K := (F.shiftIso a i (a + i) rfl).app K
  exact h.of_iso e.symm

section RightDerived

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]

/-- Degreewise application of an additive functor to bounded-below complexes, followed by
localization, has a pointwise right derived functor: the K-injective complexes are a derivability
structure for the quasi-isomorphisms.

This is the general instance of `HomotopyCategory.Plus` specialized to the functors this file
works with, so that instance search matches it syntactically instead of unfolding the
composite. -/
instance mapHomotopyCategoryPlus_hasPointwiseRightDerivedFunctor
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).hasPointwiseRightDerivedFunctor

/-- Degreewise application of an additive functor to bounded-below complexes, followed by
localization, has a right derived functor. -/
instance mapHomotopyCategoryPlus_hasRightDerivedFunctor
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **A right derived functor on the unbounded derived category is triangulated.** The
comparison `α` is invertible at every K-injective complex, and every morphism of `D(A)` is
represented by a morphism of K-injective complexes, whose cone is again K-injective; so the
criterion `CategoryTheory.Functor.isTriangulated_of_leftExtension` applies. -/
theorem isTriangulated_of_isRightDerivedFunctor [IsGrothendieckAbelian A]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    letI := Functor.IsRightDerivedFunctor.commShift RF α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
    RF.IsTriangulated := by
  let := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have hα :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A)).2
      DerivedCategory.Qh RF α
  have reps (X : DerivedCategory A) : ∃ I : CochainComplex A ℤ,
      I.IsKInjective ∧
        Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ X) := by
    obtain ⟨I, f, hI, hf⟩ :=
      Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A
        (DerivedCategory.Q.objPreimage X)
    exact ⟨I, hI, ⟨(DerivedCategory.quotientCompQhIso A).app I ≪≫
      (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩
  apply Functor.isTriangulated_of_leftExtension RF α
  intro X Y f
  obtain ⟨I, hI, ⟨eI⟩⟩ := reps X
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := reps Y
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J).surjective (eI.hom ≫ f ≫ eJ.inv)
  obtain ⟨Z, k, δ, hT⟩ := distinguished_cocone_triangle g
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have hZ : CochainComplex.IsKInjective Z := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT
      (CochainComplex.IsKInjective.rightOrthogonal I)
      (CochainComplex.IsKInjective.rightOrthogonal J)
  refine ⟨Triangle.mk g k δ, hT, hα I hI, hα J hJ, hα Z hZ,
    ⟨Arrow.isoMk eI eJ ?_⟩⟩
  simp [hg]

/-- Right acyclicity for `F` is inherited by the terms of a stupid truncation: each of them is
either a term of the original complex or zero. -/
lemma rightAcyclic_stupidTruncGE [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ)
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) (a n : ℤ) :
    F.rightAcyclic ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X n) := by
  have : ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).IsTriangulated :=
    Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))
  by_cases hn : ∃ i, (ComplexShape.embeddingUpIntGE a).f i = n
  · obtain ⟨i, hi⟩ := hn
    exact (NatTrans.isIso_app_iff_of_iso _
      ((HomotopyCategory.Plus.singleFunctor A 0).mapIso
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a) hi).symm)).1
        (hacyclic n)
  · exact Functor.isIso_app_of_isZero _
      ((HomotopyCategory.Plus.singleFunctor A 0).map_isZero
        (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) n
          (by simpa using hn)))

/-- An additive functor applied degreewise turns `σ^{≥a}K → K` into a cohomology isomorphism in
every degree above `a`: the map is already a degreewise isomorphism there. -/
lemma isIso_homologyMap_map_ιStupidTrunc
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (a q : ℤ) (ha : a < q) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a))) q) := by
  let g := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a))
  show IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℤ) q).map g))
  have key (i : ℤ) (hi : a ≤ i) : IsIso (g.f i) := by
    have := isIso_ιStupidTrunc_f K a i hi
    dsimp [g]
    infer_instance
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · show Epi (g.f ((ComplexShape.up ℤ).prev q))
    rw [CochainComplex.prev]
    have := key (q - 1) (by omega)
    infer_instance
  · exact key q (by omega)
  · show Mono (g.f ((ComplexShape.up ℤ).next q))
    rw [CochainComplex.next]
    have := key (q + 1) (by omega)
    infer_instance

omit [HasDerivedCategory A] in
/-- The termwise functor, read in the derived category, inverts `σ^{≥a}K → K` on cohomology in
degrees above `a`. -/
lemma isIso_homologyFunctor_map_termwise_stupidTrunc
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ)
    (a q : ℤ) (ha : a < q) :
    IsIso ((DerivedCategory.homologyFunctor B q).map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a))))) := by
  let g := K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)
  let e := (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm) ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _
  have h : IsIso ((DerivedCategory.homologyFunctor B q).map
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors B q) _).2
      (isIso_homologyMap_map_ιStupidTrunc F K a q ha)
  exact (NatIso.isIso_map_iff
    (Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor B q)) g).1 h

end RightDerived

section PlusToUnbounded

variable {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category B] [Abelian B] [HasDerivedCategory B]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- A bounded-below complex with injective terms is K-injective. -/
lemma isKInjective_of_injective_of_plus {L : CochainComplex A ℤ}
    (hL : CochainComplex.plus A L) [∀ n, Injective (L.X n)] : L.IsKInjective := by
  obtain ⟨d, hd⟩ := hL
  have : L.IsStrictlyGE d := hd
  exact CochainComplex.isKInjective_of_injective L d

/-- The inclusion of bounded-below homotopy categories commutes with a degreewise functor. -/
def mapHomotopyCategoryPlusCompιIso (F : A ⥤ B) [F.Additive] :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) :=
  ObjectProperty.liftCompιIso ..

/-- The comparison `α` of a right derived functor, read on cochain complexes rather than on the
homotopy category. -/
def complexDerivedUnit (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm).hom ≫
    (Functor.isoWhiskerRight
      (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ)) α ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) RF).hom

/-- On a K-injective complex the comparison into a right derived functor is invertible. -/
lemma complexDerivedUnit_isIso [IsGrothendieckAbelian A]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((complexDerivedUnit F RF α).app I) := by
  have :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A)).2
      DerivedCategory.Qh RF α I inferInstance
  dsimp [complexDerivedUnit]
  infer_instance

/-- **The comparison into a right derived functor is invertible at a bounded-below complex with
right-acyclic terms.** Leray's acyclicity criterion gives this for the bounded-below derived
functor; the transport to the unbounded one goes through a bounded-below resolution by termwise
injectives, which is K-injective, and on which both comparisons are invertible. -/
@[sga "4½ Etat_0 4.2.3.2" "Bounded-below part"]
theorem isIso_app_of_plus_of_rightAcyclic
    [IsGrothendieckAbelian A] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : CochainComplex A ℤ) (hK : CochainComplex.plus A K)
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  let H' := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι
  let R₂ := DerivedCategory.Plus.ι ⋙ RF
  let e₁ : H' ≅ HomotopyCategory.Plus.ι A ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus
        (DerivedCategory.Plus.QhCompιIsoιCompQh B) ≪≫
      (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight (mapHomotopyCategoryPlusCompιIso F) _ ≪≫
      Functor.associator ..
  let e₂ : DerivedCategory.Plus.Qh ⋙ R₂ ≅
      HomotopyCategory.Plus.ι A ⋙ DerivedCategory.Qh ⋙ RF :=
    (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh A) RF ≪≫
      Functor.associator ..
  let β : H' ⟶ DerivedCategory.Plus.Qh ⋙ R₂ :=
    e₁.hom ≫ Functor.whiskerLeft (HomotopyCategory.Plus.ι A) α ≫ e₂.inv
  obtain ⟨lo, hlo⟩ := hK
  let Kp : CochainComplex.Plus A := ⟨K, ⟨lo, hlo⟩⟩
  have : Kp.obj.IsStrictlyGE lo := hlo
  obtain ⟨J, hJ, s, hs⟩ := CochainComplex.Plus.exists_quasiIso_injective Kp lo
  let Ip := (InjectiveObject.ι A).mapCochainComplexPlus.obj J
  let P := (HomotopyCategory.Plus.quotient A).obj Kp
  let Q := (HomotopyCategory.Plus.quotient A).obj Ip
  let g : P ⟶ Q := (HomotopyCategory.Plus.quotient A).map s
  have hIinj (n : ℤ) : Injective (Ip.obj.X n) :=
    inferInstanceAs (Injective ((InjectiveObject.ι A).obj (J.obj.X n)))
  have hacyclicI (n : ℤ) : F.rightAcyclic (Ip.obj.X n) :=
    ((F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus (Ip.obj.X n)).2 inferInstance).2
      fun i hi => F.isZero_rightDerivedPlus_obj_injective i (ne_of_gt hi) (Ip.obj.X n)
  have hgW : HomotopyCategory.Plus.quasiIso A g := by
    rw [HomotopyCategory.Plus.quasiIso_iff, HomotopyCategory.Plus.quotient_map_hom]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s.hom).2 hs
  have hgH' : IsIso (H'.map g) := by
    let η := (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)
    have : IsIso (η.app P) :=
      Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic F K Kp.property hacyclic
    have : IsIso (η.app Q) :=
      Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic F Ip.obj Ip.property hacyclicI
    have : IsIso (DerivedCategory.Plus.Qh.map g) :=
      Localization.inverts DerivedCategory.Plus.Qh _ g hgW
    have : IsIso ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map g ≫ η.app Q) := by
      rw [η.naturality g, Functor.comp_map]
      infer_instance
    have : IsIso ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map g) :=
      IsIso.of_isIso_comp_right _ (η.app Q)
    exact Functor.map_isIso DerivedCategory.Plus.ι
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map g)
  have hgR₂ : IsIso ((DerivedCategory.Plus.Qh ⋙ R₂).map g) := by
    have := Localization.inverts DerivedCategory.Plus.Qh _ g hgW
    dsimp
    infer_instance
  have hβQ : IsIso (β.app Q) := by
    show IsIso (e₁.hom.app Q ≫
      (Functor.whiskerLeft (HomotopyCategory.Plus.ι A) α).app Q ≫ e₂.inv.app Q)
    have : Ip.obj.IsKInjective := isKInjective_of_injective_of_plus Ip.property
    have h : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Ip.obj)) := by
      simpa [complexDerivedUnit] using complexDerivedUnit_isIso F RF α Ip.obj
    have : IsIso ((Functor.whiskerLeft (HomotopyCategory.Plus.ι A) α).app Q) :=
      (α.isIso_app_iff_of_iso ((HomotopyCategory.Plus.quotientCompιIso A).app Ip)).2 h
    infer_instance
  have hβP : IsIso (β.app P) := by
    have hcomp : IsIso (H'.map g ≫ β.app Q) := inferInstance
    rw [β.naturality g] at hcomp
    exact IsIso.of_isIso_comp_right (β.app P) ((DerivedCategory.Plus.Qh ⋙ R₂).map g)
  have hmid : IsIso
      ((Functor.whiskerLeft (HomotopyCategory.Plus.ι A) α).app P) := by
    rw [show (Functor.whiskerLeft (HomotopyCategory.Plus.ι A) α).app P =
      e₁.inv.app P ≫ β.app P ≫ e₂.hom.app P by simp [β]]
    infer_instance
  exact (α.isIso_app_iff_of_iso
    ((HomotopyCategory.Plus.quotientCompιIso A).app Kp)).1 hmid

end PlusToUnbounded

end Stacks.DerivedAcyclic

end
