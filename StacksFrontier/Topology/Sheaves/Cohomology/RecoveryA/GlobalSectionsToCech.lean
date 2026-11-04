module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Topology.Category.TopCat.Opens
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.TotalComplexRefinement
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections and the total Čech complex

Let `X` be a topological space and let `U : ι → Opens X` be a family of open subsets. Applying
the Čech construction of the family degreewise to a complex of abelian presheaves on `X` and
totalizing gives the total Čech complex, and a global section of a presheaf restricts to a
Čech cochain of degree zero. This file builds the resulting map from the complex of global
sections to the total Čech complex, and shows that it is compatible with the restriction map
attached to a refinement of the family.

## Main definitions

* `Stacks.Cech.globalSectionsComplexFunctor`: sections over the whole space, degreewise.
* `Stacks.Cech.globalSectionsCechRestriction` and
  `Stacks.Cech.globalSectionsCechRestrictionInt`: restriction of a global section into Čech
  degree `n`, for the nonnegatively graded and for the integer-indexed Čech complex.
* `Stacks.Cech.globalSectionsToCech`: the natural map from the complex of global sections to
  the total Čech complex.

## Main results

* `Stacks.Cech.globalSectionsToCech_app_f` characterizes the components of the map.
* `Stacks.Cech.globalSectionsToCech_refinement_map` and
  `Stacks.Cech.globalSectionsToCech_refinement`: compatibility with the refinement map of
  Stacks 08BM.
* `Stacks.Cech.ιTotalZero_comm`, `Stacks.Cech.ιTotalZero_naturality` and
  `Stacks.Cech.ιTotalZero_comp`: the three compatibilities of a degreewise map into the
  degree-zero row of a double complex with the total differential, with a totalized map, and
  with naturality, over an arbitrary preadditive category.

## Implementation notes

The Čech construction itself is not redefined here: `cechComplexFunctorInt`,
`cechBicomplexFunctor`, `cechTotalComplexFunctor` and `CechRefinementTransformation` are taken
from `StacksFrontier.Topology.Sheaves.Cohomology.Cech.TotalComplexRefinement`, where they are
available for an arbitrary category with finite products; the present file instantiates them at
`TopologicalSpace.Opens X`. Consequently a complex of abelian presheaves is written out as a
complex in `(Opens X)ᵒᵖ ⥤ AddCommGrpCat`, which is also what `TopCat.Presheaf Ab X` denotes:
spelling it through `TopCat.Presheaf` would introduce a second, parallel `Preadditive`
instance on the same category and every identification across it would then have to be made
by hand.

The space and the coefficient universes are independent, and the index type of the family
lies in the coefficient universe, as the Čech product API requires.

Two kinds of identification recur. Degree `0` and degree `1` of the integer-indexed Čech
complex are degree `0` and degree `1` of the nonnegatively graded one; these are named
`cechExtendXIsoZero` and `cechExtendXIsoOne` so that the comparison isomorphism is one fixed
term wherever it occurs, rather than a fresh instance of `HomologicalComplex.extendXIso`
carrying its own proof. And degree-zero row of the Čech bicomplex of a complex `K` is the
family of Čech complexes of the terms of `K`; this identification is discharged once, at the
point of use, by stating the three facts that `globalSectionsToCech` needs — compatibility
with differentials, naturality, and compatibility with a totalized map — for abstract data in
`ιTotalZero_comm`, `ιTotalZero_naturality` and `ιTotalZero_comp`.

## References

* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 08BM](https://stacks.math.columbia.edu/tag/08BM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite

universe u v

namespace Stacks.Cech

variable (X : TopCat.{u}) {ι : Type v} (U : ι → TopologicalSpace.Opens X)

/-- The Čech-complex functor of a family of opens preserves zero morphisms. -/
instance cechComplexFunctor_preservesZeroMorphisms :
    (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{v}) U).PreservesZeroMorphisms :=
  ⟨by
    intro P Q
    apply HomologicalComplex.Hom.ext
    funext n
    simp only [HomologicalComplex.zero_f]
    change Limits.Pi.map (fun i ↦ (0 : P.obj _ ⟶ Q.obj _)) = 0
    ext j
    simp⟩

/-- The functor taking a complex of abelian presheaves on `X` to its complex of sections
over the whole space. -/
noncomputable def globalSectionsComplexFunctor :
    CochainComplex ((TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ ⥤
      CochainComplex AddCommGrpCat.{v} ℤ :=
  ((evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat.{v}).obj (op ⊤)).mapHomologicalComplex
    (up ℤ)

/-- Degree zero of the integer-indexed Čech complex is degree zero of the nonnegatively
graded one. -/
noncomputable def cechExtendXIsoZero (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    ((cechComplexFunctorInt U).obj P).X 0 ≅ ((CategoryTheory.cechComplexFunctor U).obj P).X 0 :=
  ((CategoryTheory.cechComplexFunctor U).obj P).extendXIso embeddingUpNat (i := 0) (i' := 0) rfl

/-- Degree one of the integer-indexed Čech complex is degree one of the nonnegatively graded
one. -/
noncomputable def cechExtendXIsoOne (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    ((cechComplexFunctorInt U).obj P).X 1 ≅ ((CategoryTheory.cechComplexFunctor U).obj P).X 1 :=
  ((CategoryTheory.cechComplexFunctor U).obj P).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl

/-- Restrict a global section to each intersection in Čech degree `n`. -/
noncomputable def globalSectionsCechRestriction
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) (n : ℕ) :
    P.obj (op ⊤) ⟶ ((CategoryTheory.cechComplexFunctor U).obj P).X n :=
  Pi.lift (fun _ ↦ P.map (homOfLE le_top).op)

/-- Restriction of global sections into Čech degree `n` is natural in the presheaf. -/
@[reassoc]
lemma globalSectionsCechRestriction_naturality
    {P Q : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}} (f : P ⟶ Q) (n : ℕ) :
    f.app (op ⊤) ≫ globalSectionsCechRestriction X U Q n =
      globalSectionsCechRestriction X U P n ≫
        ((CategoryTheory.cechComplexFunctor U).map f).f n := by
  show f.app (op ⊤) ≫ Pi.lift _ = Pi.lift _ ≫ Limits.Pi.map _
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc]
  exact (f.naturality _).symm

/-- Restricting a global section to each piece commutes with restriction along a morphism of
formal coproducts. -/
private lemma pi_lift_restrict_comp_evalOp_map
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v})
    {A B : FormalCoproduct.{v} (TopologicalSpace.Opens X)} (f : A ⟶ B) :
    (Pi.lift (fun _ : B.I ↦ P.map (homOfLE le_top).op)) ≫
        ((FormalCoproduct.evalOp _ AddCommGrpCat.{v}).obj P).map f.op =
      Pi.lift (fun _ : A.I ↦ P.map (homOfLE le_top).op) := by
  change (Pi.lift _) ≫ (Pi.lift _) = Pi.lift _
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_π, Pi.lift_π_assoc, ← P.map_comp]
  congr 1

/-- A global section restricted into Čech degree zero is a cocycle: its Čech differential
vanishes. -/
@[reassoc]
lemma globalSectionsCechRestriction_d (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    globalSectionsCechRestriction X U P 0 ≫ ((CategoryTheory.cechComplexFunctor U).obj P).d 0 1 =
      0 := by
  let E := (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P
  have hd : AlgebraicTopology.AlternatingCofaceMapComplex.objD E 0 = E.δ 0 - E.δ 1 := by
    simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two,
      sub_eq_add_neg]
  have hcomp : ∀ r : P.obj (op ⊤) ⟶ E.obj (SimplexCategory.mk 0), r ≫ E.δ 0 = r ≫ E.δ 1 →
      r ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD E 0 = 0 := by
    intro r hr
    rw [hd, Preadditive.comp_sub, sub_eq_zero, hr]
  refine hcomp (globalSectionsCechRestriction X U P 0) ?_
  exact (pi_lift_restrict_comp_evalOp_map X P _).trans
    (pi_lift_restrict_comp_evalOp_map X P _).symm

/-- The augmentation in degree zero of the integer-indexed Čech complex. -/
noncomputable def globalSectionsCechRestrictionInt
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    P.obj (op ⊤) ⟶ ((cechComplexFunctorInt U).obj P).X 0 :=
  globalSectionsCechRestriction X U P 0 ≫ (cechExtendXIsoZero X U P).inv

/-- The differential of the integer-indexed Čech complex out of degree zero, read through the
comparison isomorphisms with the nonnegatively graded complex. -/
lemma cechComplexFunctorInt_d_zero_one
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    ((cechComplexFunctorInt U).obj P).d 0 1 =
      (cechExtendXIsoZero X U P).hom ≫
        ((CategoryTheory.cechComplexFunctor U).obj P).d 0 1 ≫ (cechExtendXIsoOne X U P).inv :=
  HomologicalComplex.extend_d_eq _ embeddingUpNat rfl rfl

/-- The degree-zero component of the integer-indexed Čech complex of a map of presheaves,
read through the comparison isomorphisms. -/
lemma cechComplexFunctorInt_map_f_zero
    {P Q : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}} (f : P ⟶ Q) :
    ((cechComplexFunctorInt U).map f).f 0 =
      (cechExtendXIsoZero X U P).hom ≫ ((CategoryTheory.cechComplexFunctor U).map f).f 0 ≫
        (cechExtendXIsoZero X U Q).inv :=
  HomologicalComplex.extendMap_f _ embeddingUpNat rfl

/-- The augmentation into the integer-indexed Čech complex is killed by the differential out of
degree zero. -/
@[reassoc]
lemma globalSectionsCechRestrictionInt_d
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    globalSectionsCechRestrictionInt X U P ≫ ((cechComplexFunctorInt U).obj P).d 0 1 = 0 := by
  rw [globalSectionsCechRestrictionInt, cechComplexFunctorInt_d_zero_one, Category.assoc,
    Iso.inv_hom_id_assoc, globalSectionsCechRestriction_d_assoc, zero_comp]

/-- The augmentation into the integer-indexed Čech complex is natural in the presheaf. -/
@[reassoc]
lemma globalSectionsCechRestrictionInt_naturality
    {P Q : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}} (f : P ⟶ Q) :
    f.app (op ⊤) ≫ globalSectionsCechRestrictionInt X U Q =
      globalSectionsCechRestrictionInt X U P ≫ ((cechComplexFunctorInt U).map f).f 0 := by
  rw [globalSectionsCechRestrictionInt, globalSectionsCechRestrictionInt,
    cechComplexFunctorInt_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc,
    globalSectionsCechRestriction_naturality_assoc]

/-- The compatibility with differentials of a map into Čech degree zero of a double complex,
stated for abstract data so that the identification of the two descriptions of the degree-zero
row happens once, where the lemma is applied. -/
lemma ιTotalZero_comm {A : Type u} [Category.{v} A] [Preadditive A]
    (M : HomologicalComplex₂ A (up ℤ) (up ℤ)) [M.HasTotal (up ℤ)]
    (L : CochainComplex A ℤ) (r : ∀ n : ℤ, L.X n ⟶ (M.X 0).X n)
    (hr : ∀ n : ℤ, r n ≫ (M.d 0 1).f n = 0)
    (hd : ∀ n : ℤ, L.d n (n + 1) ≫ r (n + 1) = r n ≫ (M.X 0).d n (n + 1)) (n : ℤ) :
    (r n ≫ M.ιTotal (up ℤ) 0 n n (by simp)) ≫ (M.total (up ℤ)).d n (n + 1) =
      L.d n (n + 1) ≫ r (n + 1) ≫ M.ιTotal (up ℤ) 0 (n + 1) (n + 1) (by simp) := by
  rw [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ]
  simp only [Int.negOnePow_zero, one_smul, Preadditive.comp_add, ← Category.assoc]
  have hr' : r n ≫ (M.d 0 (0 + 1)).f n = 0 := by rw [zero_add]; exact hr n
  rw [hr', zero_comp, zero_add, hd]

/-- Naturality of a map into Čech degree zero of a double complex, stated for abstract
data. -/
lemma ιTotalZero_naturality {A : Type u} [Category.{v} A] [Preadditive A]
    (M N : HomologicalComplex₂ A (up ℤ) (up ℤ)) [M.HasTotal (up ℤ)] [N.HasTotal (up ℤ)]
    (φ : M ⟶ N) (L L' : CochainComplex A ℤ) (ψ : L ⟶ L')
    (r : ∀ n : ℤ, L.X n ⟶ (M.X 0).X n) (s : ∀ n : ℤ, L'.X n ⟶ (N.X 0).X n)
    (h : ∀ n : ℤ, ψ.f n ≫ s n = r n ≫ (φ.f 0).f n) (n : ℤ) :
    ψ.f n ≫ s n ≫ N.ιTotal (up ℤ) 0 n n (by simp) =
      (r n ≫ M.ιTotal (up ℤ) 0 n n (by simp)) ≫
        (HomologicalComplex₂.total.map φ (up ℤ)).f n := by
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc, h]

/-- The composite of a map into Čech degree zero with a totalized map of double complexes,
stated for abstract data. -/
lemma ιTotalZero_comp {A : Type u} [Category.{v} A] [Preadditive A]
    (M N : HomologicalComplex₂ A (up ℤ) (up ℤ)) [M.HasTotal (up ℤ)] [N.HasTotal (up ℤ)]
    (φ : M ⟶ N) (L : CochainComplex A ℤ)
    (r : ∀ n : ℤ, L.X n ⟶ (M.X 0).X n) (s : ∀ n : ℤ, L.X n ⟶ (N.X 0).X n)
    (h : ∀ n : ℤ, r n ≫ (φ.f 0).f n = s n) (n : ℤ) :
    (r n ≫ M.ιTotal (up ℤ) 0 n n (by simp)) ≫
        (HomologicalComplex₂.total.map φ (up ℤ)).f n =
      s n ≫ N.ιTotal (up ℤ) 0 n n (by simp) := by
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, h]

/-- **Stacks Project, Tag 07M9.** Restriction into Čech degree zero, followed by
inclusion into the total complex. -/
@[stacks 07M9]
noncomputable def globalSectionsToCech :
    globalSectionsComplexFunctor X ⟶ cechTotalComplexFunctor U where
  app K :=
    { f := fun n ↦ globalSectionsCechRestrictionInt X U (K.X n) ≫
        ((cechBicomplexFunctor U).obj K).ιTotal (up ℤ) 0 n n (by simp)
      comm' := by
        intro n m h
        obtain rfl : m = n + 1 := h.symm
        exact ιTotalZero_comm ((cechBicomplexFunctor U).obj K)
          ((globalSectionsComplexFunctor X).obj K)
          (fun n ↦ globalSectionsCechRestrictionInt X U (K.X n))
          (fun n ↦ globalSectionsCechRestrictionInt_d X U (K.X n))
          (fun n ↦ globalSectionsCechRestrictionInt_naturality X U (K.d n (n + 1))) n }
  naturality K L f := by
    ext n : 1
    exact ιTotalZero_naturality ((cechBicomplexFunctor U).obj K)
      ((cechBicomplexFunctor U).obj L) ((cechBicomplexFunctor U).map f)
      ((globalSectionsComplexFunctor X).obj K) ((globalSectionsComplexFunctor X).obj L)
      ((globalSectionsComplexFunctor X).map f)
      (fun n ↦ globalSectionsCechRestrictionInt X U (K.X n))
      (fun n ↦ globalSectionsCechRestrictionInt X U (L.X n))
      (fun n ↦ globalSectionsCechRestrictionInt_naturality X U (f.f n)) n

/-- In degree `n`, the augmentation restricts to Čech degree zero and includes that summand
into the total complex. -/
@[simp]
lemma globalSectionsToCech_app_f
    (K : CochainComplex ((TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ) (n : ℤ) :
    ((globalSectionsToCech X U).app K).f n =
      globalSectionsCechRestrictionInt X U (K.X n) ≫
        ((cechBicomplexFunctor U).obj K).ιTotal (up ℤ) 0 n n (by simp) := rfl

/-- Global restriction commutes with the Čech map of a refinement in each degree. -/
@[reassoc]
lemma globalSectionsCechRestriction_refinement {κ : Type v}
    (V : κ → TopologicalSpace.Opens X)
    (t : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
    (e : CechRefinementTransformation U V t)
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) (n : ℕ) :
    globalSectionsCechRestriction X U P n ≫ (e.cechMap.app P).f n =
      globalSectionsCechRestriction X V P n := by
  rw [e.cechMap_f]
  exact pi_lift_restrict_comp_evalOp_map X P (FormalCoproduct.powerMap t (Fin (n + 1)))

/-- The augmentation into the integer-indexed Čech complex commutes with the Čech map of a
refinement. -/
@[reassoc]
lemma globalSectionsCechRestrictionInt_refinement {κ : Type v}
    (V : κ → TopologicalSpace.Opens X)
    (t : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
    (e : CechRefinementTransformation U V t)
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    globalSectionsCechRestrictionInt X U P ≫
        (HomologicalComplex.extendMap (e.cechMap.app P) embeddingUpNat).f 0 =
      globalSectionsCechRestrictionInt X V P := by
  have hmap : (HomologicalComplex.extendMap (e.cechMap.app P) embeddingUpNat).f 0 =
      (cechExtendXIsoZero X U P).hom ≫ (e.cechMap.app P).f 0 ≫
        (cechExtendXIsoZero X V P).inv :=
    HomologicalComplex.extendMap_f _ embeddingUpNat rfl
  have h2 : globalSectionsCechRestrictionInt X U P ≫
      ((cechExtendXIsoZero X U P).hom ≫ (e.cechMap.app P).f 0 ≫
        (cechExtendXIsoZero X V P).inv) = globalSectionsCechRestrictionInt X V P := by
    rw [globalSectionsCechRestrictionInt, globalSectionsCechRestrictionInt, Category.assoc,
      Iso.inv_hom_id_assoc, globalSectionsCechRestriction_refinement_assoc]
  exact (congrArg (fun g ↦ globalSectionsCechRestrictionInt X U P ≫ g) hmap).trans h2

/-- The augmentation commutes with any refinement transformation having the restriction
formula of Tag 08BM. -/
@[reassoc]
lemma globalSectionsToCech_refinement_map {κ : Type v} (V : κ → TopologicalSpace.Opens X)
    (t : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
    (e : CechRefinementTransformation U V t) :
    globalSectionsToCech X U ≫
        (e.map : cechTotalComplexFunctor U ⟶ cechTotalComplexFunctor V) =
      globalSectionsToCech X V := by
  have hmap : (e.map : cechTotalComplexFunctor U ⟶ cechTotalComplexFunctor V) =
      totalMapOfCechMap U V e.cechMap := e.map_eq
  rw [hmap]
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  have htot : (totalMapOfCechMap U V e.cechMap).app K =
      HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{v} (up ℤ) (up ℤ)).map
          (((e.cechMap.hcomp
            (𝟙 (embeddingUpNat.extendFunctor AddCommGrpCat.{v}))).mapHomologicalComplex
              (up ℤ)).app K)) (up ℤ) := by
    simp only [totalMapOfCechMap, NatTrans.hcomp_id_app]
    rfl
  rw [NatTrans.comp_app, htot]
  refine ιTotalZero_comp ((cechBicomplexFunctor U).obj K) ((cechBicomplexFunctor V).obj K)
    ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{v} (up ℤ) (up ℤ)).map
      (((e.cechMap.hcomp
        (𝟙 (embeddingUpNat.extendFunctor AddCommGrpCat.{v}))).mapHomologicalComplex
          (up ℤ)).app K))
    ((globalSectionsComplexFunctor X).obj K)
    (fun n ↦ globalSectionsCechRestrictionInt X U (K.X n))
    (fun n ↦ globalSectionsCechRestrictionInt X V (K.X n)) (fun m ↦ ?_) n
  have hf : (((HomologicalComplex₂.flipFunctor AddCommGrpCat.{v} (up ℤ) (up ℤ)).map
      (((e.cechMap.hcomp
        (𝟙 (embeddingUpNat.extendFunctor AddCommGrpCat.{v}))).mapHomologicalComplex
          (up ℤ)).app K)).f 0).f m =
      (HomologicalComplex.extendMap (e.cechMap.app (K.X m)) embeddingUpNat).f 0 := by
    simp only [HomologicalComplex₂.flipFunctor_map_f_f, NatTrans.mapHomologicalComplex_app_f,
      NatTrans.hcomp_id_app, Embedding.extendFunctor_map]
    rfl
  exact (congrArg (fun g ↦ globalSectionsCechRestrictionInt X U (K.X m) ≫ g) hf).trans
    (globalSectionsCechRestrictionInt_refinement X U V t e (K.X m))

/-- The augmentation is compatible with the canonical refinement map of Tag 08BM. -/
@[reassoc]
lemma globalSectionsToCech_refinement {κ : Type v} (V : κ → TopologicalSpace.Opens X)
    (t : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) :
    globalSectionsToCech X U ≫
        ((cechTotalComplexRefinement U V t).map :
          cechTotalComplexFunctor U ⟶ cechTotalComplexFunctor V) =
      globalSectionsToCech X V :=
  globalSectionsToCech_refinement_map X U V t _

end Stacks.Cech
