module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology

/-!
# The degree-zero comparison of a locally covering augmented simplicial presheaf, as a map

Let `C` be a category carrying a Grothendieck topology `J`, let `A` be an augmented simplicial
presheaf of sets on `C` whose degree-zero augmentation and relation map are locally surjective,
and let `s(**Z**_A^♯)` be the complex of free abelian sheaves it generates.  Tag 01GE identifies
the degree-zero homology sheaf of that complex with the free abelian sheaf on the presheaf of
augmentation points; the identification already in the library,
`CategoryTheory.SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees`,
is an *abstract* isomorphism, assembled from the comparison with the first coskeleton, the
comparison of that coskeleton with a Čech nerve, and the Čech nerve's augmentation.

This file proves that the isomorphism is the one *induced by the augmentation*: the free abelian
sheaf functor applied to the degree-zero component of the augmentation is a cokernel of the first
differential of the complex.  Applying `Hom(-, F)` for a sheaf of abelian groups `F` then turns
it into the canonical restriction map, which induces an isomorphism from the sections of `F` over
the presheaf of augmentation points onto the kernel of the first differential of the complex of
sections.  That is the degree-zero statement of Tag 09VV in canonical-map form, and it is what
the first spectral sequence of the double complex of Tag 09VX consumes, in the shape
`StacksDraft.TotalComplexQuasiIso.Hypotheses.inducesIsoKernel`.

## Main definitions

* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafAugmentation`: the augmentation of
  the free abelian sheaf complex towards the free abelian sheaf on the presheaf of augmentation
  points, placed in degree zero.
* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafAugZero`: its degree-zero
  component, namely the free abelian sheaf functor applied to the degree-zero augmentation.
* `CategoryTheory.SimplicialObject.Augmented.cechNerveFreeAbelianSheafAugZero`: the same for a
  Čech nerve, written at the spelling of the degree-zero term of its complex.
* `CategoryTheory.SimplicialObject.Augmented.isColimitCokernelCoforkFreeAbelianSheafAugZero`:
  the degree-zero augmentation exhibited as a cokernel.

## Main results

* `CategoryTheory.Limits.isIso_kernelLift_map_op_of_isColimit`: morphisms out of a cokernel are
  the kernel of the morphisms out of the source, for any limit-preserving functor on the
  opposite category.
* `CategoryTheory.SimplicialObject.Augmented.descOpcycles_freeAbelianSheafAugZero_eq`: the
  canonical degree-zero augmentation, descended through `opcycles`, is the three-step composite
  out of which Tag 01GE's abstract isomorphism is built.  This is the comparison that was
  missing.
* `CategoryTheory.SimplicialObject.Augmented.isIso_kernelLift_freeAbelianSheafAugZero` and its
  `∃`-form `exists_isIso_kernelLift_freeAbelianSheafAugZero`: the canonical restriction map
  induces an isomorphism onto the kernel of the first differential of the complex of sections.
* `Stacks.CategoryTheory.Hypercovering.isIso_kernelLift_freeAbelianSheafAugZero_toAugmentedULift`:
  the same for the augmented simplicial presheaf of a hypercovering of a presheaf (Tag 09VU), for
  which the two local surjectivity hypotheses are conditions (1) and (2) of a hypercovering and
  so need not be assumed.

## Implementation notes

This module carries no Stacks tag.  The statements here are the canonical-map refinement of the
degree-zero half of Tag 01GE and of Tag 09VV, but they are expressed for the complex
`s(**Z**_A^♯)` of an augmented simplicial presheaf, not for the Čech complex of Tag 01GX and the
group `presheafCohomologyZero` in which Tag 09VV is stated; the transports identifying the two —
`Stacks.CategoryTheory.Hypercovering.HypercoveringOf.toAugmentedULiftLeftIso`,
`liftedPresheafULiftIso`, `SemiRepresentable.sectionsComplexIsoHomFreeAbelianSheafComplex` and
the sheafification adjunction — are not carried out here.  The existing carriers of those two
tags are therefore left as they are.

Two spelling decisions are forced rather than chosen, both instances of the fact that a term
built from a morphism whose type is written in the "free abelian sheaf of the degree-zero object"
spelling rather than the "degree-zero term of the complex" spelling is not type-correct at
`implicit` transparency, so that every `rw` and `simp` over it is refused.

First, `freeAbelianSheafAugZero` and `cechNerveFreeAbelianSheafAugZero` are `def`s with an
ascribed result type in the complex spelling, and the Čech nerve's augmentation is fed to
`CategoryTheory.Presheaf.cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles`
through its `k` parameter, which is what keeps the resulting term rewritable.

Second, the comparison is proved at the level of `opcycles` rather than of homology.  The
homology-level statement has to mention `SimplicialObject.sheafHomologyFunctor`, and rewriting a
morphism of that functor into a `HomologicalComplex.homologyMap` leaves the surrounding objects
written through the functor; the resulting term is again not type-correct at `implicit`
transparency and `homologyπ_naturality` stops firing.  At the `opcycles` level the functor does
not appear, `p_opcyclesMap` and `p_descOpcycles` suffice, and the degree-zero isomorphy of
`homologyι` for a chain complex of non-negative degrees (`ChainComplex.isIso_homologyι₀`,
an instance) converts the library's homology-level invertibility statements into the
`opcycles`-level ones that are needed.

Four lines of `sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees`'s proof are re-derived
here — the invertibility of the degree-zero homology map of the first coskeleton unit — because
that `def` is an opaque composite and its factors are not separately available.  If it is ever
refactored to expose them, this duplication should go.

## References

* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 01GC](https://stacks.math.columbia.edu/tag/01GC)
* [Stacks Project, Tag 09VV](https://stacks.math.columbia.edu/tag/09VV)
* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

/-- **Morphisms out of a cokernel are the kernel of the morphisms out of the source.**  If
`π : X ⟶ Z` is a cokernel of `d : W ⟶ X` and `Y` is a limit-preserving functor on the opposite
category, then `Y π` induces an isomorphism from `Y Z` onto the kernel of `Y d`. -/
lemma isIso_kernelLift_map_op_of_isColimit
    {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
    {B : Type*} [Category B] [HasZeroMorphisms B] [HasKernels B]
    (Y : Aᵒᵖ ⥤ B) [Y.PreservesZeroMorphisms] [PreservesLimits Y]
    {W X Z : A} (d : W ⟶ X) (π : X ⟶ Z) (w : d ≫ π = 0)
    (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsIso (kernel.lift (Y.map d.op) (Y.map π.op)
      (by rw [← Y.map_comp, ← op_comp, w, op_zero, Y.map_zero])) := by
  have h2 := KernelFork.mapIsLimit _ (CokernelCofork.IsColimit.ofπOp π w h) Y
  have heq (hw) : kernel.lift (Y.map d.op) (Y.map π.op) hw =
      (IsLimit.conePointUniqueUpToIso h2 (kernelIsKernel (Y.map d.op))).hom := by
    refine (cancel_mono (kernel.ι (Y.map d.op))).1 ?_
    rw [kernel.lift_ι]
    exact (IsLimit.conePointUniqueUpToIso_hom_comp h2 (kernelIsKernel (Y.map d.op))
      WalkingParallelPair.zero).symm
  rw [heq]
  infer_instance

end CategoryTheory.Limits

namespace CategoryTheory.SimplicialObject.Augmented

open AlgebraicTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The augmentation of the free abelian sheaf complex of an augmented simplicial presheaf of
sets, towards the free abelian sheaf on its presheaf of augmentation points placed in degree
zero. -/
noncomputable def freeAbelianSheafAugmentation
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    (SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left ⟶
      (ChainComplex.single₀ (Sheaf J AddCommGrpCat.{w})).obj
        ((Presheaf.freeAbelianSheaf J).obj A.right) :=
  AlternatingFaceMapComplex.ε.app
    (((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Sheaf J AddCommGrpCat.{w})).obj
      (Presheaf.freeAbelianSheaf J)).obj A)

/-- The canonical degree-zero augmentation: the free abelian sheaf functor applied to the
degree-zero component of the augmentation. -/
noncomputable def freeAbelianSheafAugZero
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).X 0 ⟶
      (Presheaf.freeAbelianSheaf J).obj A.right :=
  (Presheaf.freeAbelianSheaf J).map (A.hom.app (op (SimplexCategory.mk 0)))

/-- In degree zero, `freeAbelianSheafAugmentation` is `freeAbelianSheafAugZero`. -/
lemma freeAbelianSheafAugmentation_f_zero_comp_singleObjXSelf_hom
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    (freeAbelianSheafAugmentation J A).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
          ((Presheaf.freeAbelianSheaf J).obj A.right)).hom =
      freeAbelianSheafAugZero J A := by
  rw [freeAbelianSheafAugmentation, AlternatingFaceMapComplex.ε_app_f_zero]
  simp only [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj,
    NatTrans.comp_app, Functor.whiskerRight_app, ChainComplex.single₀ObjXSelf, Iso.refl_hom,
    Category.comp_id, Functor.constComp_hom_app]
  exact Category.comp_id _

/-- The canonical degree-zero augmentation annihilates every incoming differential. -/
lemma d_comp_freeAbelianSheafAugZero
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) (j : ℕ) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).d j 0 ≫
      freeAbelianSheafAugZero J A = 0 := by
  rw [← freeAbelianSheafAugmentation_f_zero_comp_singleObjXSelf_hom J A, ← Category.assoc,
    ← (freeAbelianSheafAugmentation J A).comm j 0, HomologicalComplex.single_obj_d, comp_zero,
    zero_comp]

/-- The degree-zero component of `toCechNerve`, followed by the base map of the Čech nerve, is
the degree-zero augmentation: the first is a section of the degree-zero projection and the base
map factors through that projection. -/
lemma coskOne_cechNerve_base_app_zero
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    ((SimplicialObject.coskAdj 1).unit.app A.left).app (op (SimplexCategory.mk 0)) ≫
        (coskOneToCechNerve A).app (op (SimplexCategory.mk 0)) ≫
          WidePullback.base (fun _ : Fin 1 ↦ A.hom.app (op (SimplexCategory.mk 0))) =
      A.hom.app (op (SimplexCategory.mk 0)) := by
  have hπ : (toCechNerve A).app (op (SimplexCategory.mk 0)) ≫
      WidePullback.π (fun _ : Fin 1 ↦ A.hom.app (op (SimplexCategory.mk 0))) 0 = 𝟙 _ :=
    toCechNerve_app_zero_comp_π A
  rw [← NatTrans.comp_app_assoc, coskAdj_unit_app_comp_coskOneToCechNerve,
    ← WidePullback.π_arrow (fun _ : Fin 1 ↦ A.hom.app (op (SimplexCategory.mk 0))) 0,
    ← Category.assoc, hπ]
  simp

/-- The canonical degree-zero augmentation is the free abelian sheaf functor applied to the
degree-zero component of `toCechNerve`, followed by the base map of the Čech nerve. -/
lemma freeAbelianSheafAugZero_eq_comp
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    freeAbelianSheafAugZero J A =
      (Presheaf.freeAbelianSheaf J).map
          (((SimplicialObject.coskAdj 1).unit.app A.left).app (op (SimplexCategory.mk 0))) ≫
        (Presheaf.freeAbelianSheaf J).map
            ((coskOneToCechNerve A).app (op (SimplexCategory.mk 0))) ≫
          (Presheaf.freeAbelianSheaf J).map
            (WidePullback.base fun _ : Fin 1 ↦ A.hom.app (op (SimplexCategory.mk 0))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (Presheaf.freeAbelianSheaf J).congr_map (coskOne_cechNerve_base_app_zero A).symm

/-- The canonical degree-zero augmentation of the Čech nerve of a morphism of presheaves of
sets, written at the spelling of the degree-zero term of the free abelian sheaf complex.  The
ascription is what keeps terms built from it type-correct at `implicit` transparency, so that
they can be rewritten. -/
noncomputable def cechNerveFreeAbelianSheafAugZero {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk f).cechNerve).X 0 ⟶
      (Presheaf.freeAbelianSheaf J).obj Q :=
  (Presheaf.freeAbelianSheaf J).map (WidePullback.base fun _ : Fin 1 ↦ f)

/-- The degree-zero component of the augmentation of the free abelian sheaf complex of the Čech
nerve of `f`, followed by the identification of the degree-zero term of the single complex, is
`cechNerveFreeAbelianSheafAugZero J f`. -/
lemma cechNerveSheafAugmentation_f_zero_eq {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q) :
    (Presheaf.cechNerveSheafAugmentation J f).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
          ((Presheaf.freeAbelianSheaf J).obj Q)).hom =
      cechNerveFreeAbelianSheafAugZero J f :=
  Presheaf.cechNerveSheafAugmentation_f_zero_comp_singleObjXSelf_hom J f

/-- The degree-`n` homology sheaf functor acts on morphisms as the homology map of the free
abelian sheaf complex. -/
lemma sheafHomologyFunctor_map {X Y : SimplicialObject (Cᵒᵖ ⥤ Type w)} (φ : X ⟶ Y) (n : ℕ) :
    (SimplicialObject.sheafHomologyFunctor J n).map φ =
      HomologicalComplex.homologyMap
        ((SimplicialObject.freeAbelianSheafComplexFunctor J).map φ) n :=
  rfl


/-- A morphism out of degree-zero `opcycles` of a chain complex is invertible as soon as its
composite with `homologyι` is, since in degree zero `homologyι` is an isomorphism. -/
private theorem isIso_of_isIso_homologyι_comp {V : Type*} [Category V] [Abelian V]
    {K : ChainComplex V ℕ} {Y : V} (g : K.opcycles 0 ⟶ Y) (h : IsIso (K.homologyι 0 ≫ g)) :
    IsIso g :=
  IsIso.of_isIso_comp_left (K.homologyι 0) _

/-- A morphism of chain complexes which is invertible on degree-zero homology is invertible on
degree-zero `opcycles`: in degree zero `homologyι` is an isomorphism at both ends. -/
lemma isIso_opcyclesMap_zero_of_isIso_homologyMap {V : Type*} [Category V] [Abelian V]
    {K L : ChainComplex V ℕ} (φ : K ⟶ L)
    (h : IsIso (HomologicalComplex.homologyMap φ 0)) :
    IsIso (HomologicalComplex.opcyclesMap φ 0) :=
  isIso_of_isIso_homologyι_comp _ (by
    rw [← HomologicalComplex.homologyι_naturality]
    infer_instance)

/-- The canonical degree-zero augmentation, descended through `opcycles`, is the composite of
the comparison with the first coskeleton, the comparison of that coskeleton with the Čech nerve,
and the descended degree-zero augmentation of the Čech nerve.  This is what makes the abstract
degree-zero isomorphism of Tag 01GE an isomorphism *induced by the augmentation*. -/
lemma descOpcycles_freeAbelianSheafAugZero_eq
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).descOpcycles
        (freeAbelianSheafAugZero J A) 1 (by simp)
        (d_comp_freeAbelianSheafAugZero J A 1) =
      HomologicalComplex.opcyclesMap ((SimplicialObject.freeAbelianSheafComplexFunctor J).map
          ((SimplicialObject.coskAdj 1).unit.app A.left)) 0 ≫
        HomologicalComplex.opcyclesMap ((SimplicialObject.freeAbelianSheafComplexFunctor J).map
            (coskOneToCechNerve A)) 0 ≫
          ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
              (Arrow.mk (A.hom.app (op (SimplexCategory.mk 0)))).cechNerve).descOpcycles
            (cechNerveFreeAbelianSheafAugZero J (A.hom.app (op (SimplexCategory.mk 0))))
            1 (by simp)
            (Presheaf.d_comp_cechNerveSheafAugmentation_f_zero J
              (A.hom.app (op (SimplexCategory.mk 0)))
              (cechNerveSheafAugmentation_f_zero_eq J
                (A.hom.app (op (SimplexCategory.mk 0)))) 1) := by
  refine (cancel_epi
    (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).pOpcycles 0)).1 ?_
  simp only [HomologicalComplex.p_descOpcycles, HomologicalComplex.p_opcyclesMap_assoc]
  rw [freeAbelianSheafAugZero_eq_comp]
  rfl

variable (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))

/-- The descended canonical degree-zero augmentation of a locally covering augmented simplicial
presheaf is an isomorphism.  Only the degree-zero augmentation and the relation map are needed,
as in `sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees`. -/
lemma isIso_descOpcycles_freeAbelianSheafAugZero
    (h₀ : Presheaf.IsLocallySurjective J
      (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A)) :
    IsIso (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).descOpcycles
      (freeAbelianSheafAugZero J A) 1 (by simp)
      (d_comp_freeAbelianSheafAugZero J A 1)) := by
  have hη : IsIso (HomologicalComplex.homologyMap
      ((SimplicialObject.freeAbelianSheafComplexFunctor J).map
        ((SimplicialObject.coskAdj 1).unit.app A.left)) 0) :=
    SimplicialObject.isIso_sheafHomologyFunctor_map_of_isIso_lowDegrees J _ 0
      fun j hj ↦ SimplicialObject.isIso_coskAdj_unit_app_app_of_le A.left 1 j hj
  have hc : IsIso (HomologicalComplex.homologyMap
      ((SimplicialObject.freeAbelianSheafComplexFunctor J).map (coskOneToCechNerve A)) 0) :=
    isIso_sheafHomologyFunctor_map_coskOneToCechNerve J A h₁ 0
  have h1 := isIso_opcyclesMap_zero_of_isIso_homologyMap _ hη
  have h2 := isIso_opcyclesMap_zero_of_isIso_homologyMap _ hc
  rw [descOpcycles_freeAbelianSheafAugZero_eq]
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 (isIso_of_isIso_homologyι_comp _
    (Presheaf.isIso_homologyι_descOpcycles_cechNerve_of_isLocallySurjective J
      (A.hom.app (op (SimplexCategory.mk 0))) h₀
      (cechNerveSheafAugmentation_f_zero_eq J (A.hom.app (op (SimplexCategory.mk 0)))) 1
      (by simp)
      (Presheaf.d_comp_cechNerveSheafAugmentation_f_zero J
        (A.hom.app (op (SimplexCategory.mk 0)))
        (cechNerveSheafAugmentation_f_zero_eq J
          (A.hom.app (op (SimplexCategory.mk 0)))) 1))))

/-- **The canonical degree-zero augmentation of a locally covering augmented simplicial presheaf
is a cokernel of the first differential of its free abelian sheaf complex.**  This is the
degree-zero statement of Tag 01GE in the form that identifies the comparison map, rather than
only asserting that an isomorphism exists. -/
noncomputable def isColimitCokernelCoforkFreeAbelianSheafAugZero
    (h₀ : Presheaf.IsLocallySurjective J
      (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A)) :
    IsColimit (CokernelCofork.ofπ (freeAbelianSheafAugZero J A)
      (d_comp_freeAbelianSheafAugZero J A 1)) := by
  have := isIso_descOpcycles_freeAbelianSheafAugZero J A h₀ h₁
  refine IsColimit.ofIsoColimit
    (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).opcyclesIsCokernel
      (i := 1) (j := 0) (by simp))
    (Cofork.ext (asIso
      (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).descOpcycles
        (freeAbelianSheafAugZero J A) 1 (by simp)
        (d_comp_freeAbelianSheafAugZero J A 1))) ?_)
  exact HomologicalComplex.p_descOpcycles _ (freeAbelianSheafAugZero J A) 1 (by simp)
    (d_comp_freeAbelianSheafAugZero J A 1)

/-- **Tag 09VV in canonical-map form, for a locally covering augmented simplicial presheaf.**
Sections of a sheaf of abelian groups over the presheaf of augmentation points, restricted along
the degree-zero augmentation, give an isomorphism onto the kernel of the first differential of
the complex of sections.

This is the statement the first spectral sequence of the double complex of Tag 09VX consumes:
it is `StacksDraft.TotalComplexQuasiIso.Hypotheses.inducesIsoKernel` for the Hom complex, and
unlike `nonempty_cechCohomologyZeroIso` it pins the comparison to the canonical restriction and
is therefore natural in the sheaf by construction. -/
theorem isIso_kernelLift_freeAbelianSheafAugZero
    (h₀ : Presheaf.IsLocallySurjective J
      (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (F : Sheaf J AddCommGrpCat.{w}) :
    IsIso (kernel.lift
      ((preadditiveYoneda.obj F).map
        (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).d 1 0).op)
      ((preadditiveYoneda.obj F).map (freeAbelianSheafAugZero J A).op)
      (by rw [← Functor.map_comp, ← op_comp, d_comp_freeAbelianSheafAugZero, op_zero,
        Functor.map_zero])) :=
  isIso_kernelLift_map_op_of_isColimit (preadditiveYoneda.obj F) _ _ _
    (isColimitCokernelCoforkFreeAbelianSheafAugZero J A h₀ h₁)

/-- `isIso_kernelLift_freeAbelianSheafAugZero` in the `∃`-form of
`StacksDraft.TotalComplexQuasiIso.Hypotheses.inducesIsoKernel`. -/
theorem exists_isIso_kernelLift_freeAbelianSheafAugZero
    (h₀ : Presheaf.IsLocallySurjective J
      (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (F : Sheaf J AddCommGrpCat.{w}) :
    ∃ hα : (preadditiveYoneda.obj F).map (freeAbelianSheafAugZero J A).op ≫
        (preadditiveYoneda.obj F).map
          (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).d 1 0).op = 0,
      IsIso (kernel.lift
        ((preadditiveYoneda.obj F).map
          (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).d 1 0).op)
        ((preadditiveYoneda.obj F).map (freeAbelianSheafAugZero J A).op) hα) :=
  ⟨_, isIso_kernelLift_freeAbelianSheafAugZero J A h₀ h₁ F⟩

end Augmented

end SimplicialObject

end CategoryTheory

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialObject.Augmented

universe q

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

/-- **Tag 09VV in canonical-map form, for a hypercovering of a presheaf.**  The two local
surjectivity hypotheses of `isIso_kernelLift_freeAbelianSheafAugZero` are conditions (1) and (2)
of a hypercovering (Tag 09VU), so for `HypercoveringOf.toAugmentedULift` they need not be
assumed.

The sheafification hypothesis is automatic, by `hasSheafify_addCommGrpCat`; it is an instance
binder only because the free abelian sheaf complex mentions it, exactly as for
`SemiRepresentable.homFreeAbelianSheafComplex`. -/
theorem isIso_kernelLift_freeAbelianSheafAugZero_toAugmentedULift
    (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    IsIso (kernel.lift
      ((preadditiveYoneda.obj F).map
        (((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
          (K.toAugmentedULift.{q, w, v, u} J G).left).d 1 0).op)
      ((preadditiveYoneda.obj F).map
        (freeAbelianSheafAugZero J.toGrothendieck
          (K.toAugmentedULift.{q, w, v, u} J G)).op)
      (by rw [← Functor.map_comp, ← op_comp, d_comp_freeAbelianSheafAugZero, op_zero,
        Functor.map_zero])) :=
  isIso_kernelLift_freeAbelianSheafAugZero J.toGrothendieck
    (K.toAugmentedULift.{q, w, v, u} J G)
    (isLocallySurjective_toAugmentedULift_hom_app_zero.{q, w, v, u} J G K)
    (isLocallySurjective_edgesToFiberProduct_toAugmentedULift.{q, w, v, u} J G K) F

end Stacks.CategoryTheory.Hypercovering

end
