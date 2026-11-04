module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution

/-!
# The absolute Čech augmentation is a kernel in degree zero

Let `X` be a scheme, let `𝒰` be the affine open covering given by an affine open cover `T` of `X`
and let `ℱ` be a quasi-coherent `𝒪_X`-module.  The absolute Čech complex `𝔠 ⁼(𝒰, ℱ)` of
[Stacks, Tag 01XL] has, in degree `n`, the product over the `(n + 1)`-tuples `i` of indices of
`j_{i *} (ℱ|_{U_i})`, where `U_i` is the intersection of the members of `𝒰` named by `i`.  This
file states the exactness of

`0 ⟶ ℱ ⟶ 𝔠 ⁰(𝒰, ℱ) ⟶ 𝔠 ¹(𝒰, ℱ)`

in the two places it holds: the augmentation `ℱ ⟶ 𝔠 ⁰(𝒰, ℱ)` is a monomorphism, and it is a
kernel of the first differential.  This is the sheaf condition for `ℱ` written as a complex, and
it is read off the quasi-isomorphism `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 02FU]: a quasi-isomorphism
out of a complex concentrated in degree zero exhibits, in degree zero, a kernel of the outgoing
differential, the complex being `ℕ`-indexed so that no differential enters degree zero.  Both the
augmentation and the first differential are natural transformations of functors of `ℱ`, so the
whole sequence is natural in `ℱ`.

## Main results

* `Stacks.HomologicalComplex.evalNatTransOfToSingle`: the degree-`j` component of a morphism from
  a complex concentrated in degree `j`, as a natural transformation.
* `Stacks.HomologicalComplex.isLimitKernelForkFromSingle`: a morphism out of a complex
  concentrated in degree `j` which is a quasi-isomorphism in degree `j`, into a complex with no
  differential entering degree `j`, is a kernel of the differential leaving degree `j`.
* `Stacks.CechSiteChange.absoluteCechAugZero` and `Stacks.CechSiteChange.absoluteCechDiffZero`:
  the augmentation `ℱ ⟶ 𝔠 ⁰(𝒰, ℱ)` and the first differential `𝔠 ⁰(𝒰, ℱ) ⟶ 𝔠 ¹(𝒰, ℱ)`, as
  natural transformations in the quasi-coherent module.
* `Stacks.CechSiteChange.absoluteCechAugZero_comp_diffZero`: the two compose to zero.
* `Stacks.CechSiteChange.isLimitKernelFork_absoluteCechAugZero`: **the augmentation is a kernel of
  the first differential.**
* `Stacks.CechSiteChange.mono_absoluteCechAugZero`: in particular it is a monomorphism.

## Implementation notes

`Stacks.HomologicalComplex.isLimitKernelForkFromSingle` takes the morphism whose kernel property
is asserted as a variable together with an equation identifying it, because the proof that it
kills the differential occurs inside the type of the conclusion and so cannot be rewritten there.

The sheaf of rings of a scheme is reached from `X.Modules` through the semireducible definitions
`AlgebraicGeometry.Scheme.Modules` and `TopCat.Sheaf`, so the category of `𝒪_X`-modules carries
two spellings whose `HasZeroMorphisms` instances are not syntactically equal, and a zero morphism
between the two is not elaborated; the two definitions are therefore declared `implicit_reducible`
for the two statements that write such a zero morphism.  The general statements above take the
functors and the morphism between them as implicit variables, to be read off the morphism of
complexes rather than resynthesized, for the same reason.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe v u

/-! ### Degree-`j` exactness of a quasi-isomorphism out of a single complex -/

namespace Stacks.HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}

/-- The degree-`j` component of a morphism out of a complex concentrated in degree `j` kills the
differential leaving degree `j`. -/
public theorem fromSingle_comp_d (A : C) {K : _root_.HomologicalComplex C c} {j : ι}
    (a : (single C c j).obj A ⟶ K) (j' : ι) :
    ((singleObjXSelf c j A).inv ≫ a.f j) ≫ K.d j j' = 0 := by
  rw [Category.assoc, a.comm j j', single_obj_d, zero_comp, comp_zero]

variable {D : Type*} [Category* D] {G : D ⥤ C} {Φ : D ⥤ _root_.HomologicalComplex C c} {j : ι}

/-- **The degree-`j` component of a morphism from a complex concentrated in degree `j`**, as a
natural transformation from the object placed in degree `j` to the degree-`j` term. -/
public noncomputable def evalNatTransOfToSingle (α : G ⋙ single C c j ⟶ Φ) :
    G ⟶ Φ ⋙ _root_.HomologicalComplex.eval C c j where
  app F := (singleObjXSelf c j (G.obj F)).inv ≫ (α.app F).f j
  naturality F F' φ := by
    have h := congrArg (fun ψ => _root_.HomologicalComplex.Hom.f ψ j) (α.naturality φ)
    simp only [_root_.HomologicalComplex.comp_f, Functor.comp_map, single_map_f_self] at h
    simp only [Functor.comp_map, _root_.HomologicalComplex.eval_map, Category.assoc]
    rw [← h]
    simp

/-- The components of `Stacks.HomologicalComplex.evalNatTransOfToSingle`. -/
@[simp]
public theorem evalNatTransOfToSingle_app (α : G ⋙ single C c j ⟶ Φ) (F : D) :
    (evalNatTransOfToSingle α).app F = (singleObjXSelf c j (G.obj F)).inv ≫ (α.app F).f j :=
  rfl

/-- The degree-`j` component of a morphism from a complex concentrated in degree `j` kills the
differential leaving degree `j`. -/
public theorem evalNatTransOfToSingle_comp_d (α : G ⋙ single C c j ⟶ Φ) (j' : ι) (F : D) :
    (evalNatTransOfToSingle α).app F ≫ (Φ.obj F).d j j' = 0 :=
  fromSingle_comp_d (G.obj F) (α.app F) j'

/-- The same, as an identity of natural transformations. -/
public theorem evalNatTransOfToSingle_comp_dNatTrans (α : G ⋙ single C c j ⟶ Φ) (j' : ι) :
    evalNatTransOfToSingle α ≫
      Functor.whiskerLeft Φ (_root_.HomologicalComplex.dNatTrans C c j j') = 0 := by
  ext F
  simp

variable [CategoryWithHomology C]

/-- A quasi-isomorphism in degree `j` out of a complex concentrated in degree `j`, into a complex
with no differential entering degree `j`, induces an isomorphism onto the cycles in degree `j`. -/
public theorem isIso_liftCycles_fromSingle (A : C) {K : _root_.HomologicalComplex C c} {j' : ι}
    (a : (single C c j).obj A ⟶ K) (hnext : c.next j = j')
    (hprev : K.d (c.prev j) j = 0) [QuasiIsoAt a j] :
    IsIso (K.liftCycles ((singleObjXSelf c j A).inv ≫ a.f j) j' hnext
      (fromSingle_comp_d A a j')) := by
  have hd : ∀ k l : ι, ((single C c j).obj A).d k l = 0 := single_obj_d c j A
  have hiC : IsIso (((single C c j).obj A).iCycles j) := isIso_iCycles _ j j' hnext (hd j j')
  have hz : (singleObjXSelf c j A).inv ≫ ((single C c j).obj A).d j j' = 0 := by
    rw [hd, comp_zero]
  have hu : IsIso (((single C c j).obj A).liftCycles (singleObjXSelf c j A).inv j' hnext hz) := by
    have heq : ((single C c j).obj A).liftCycles (singleObjXSelf c j A).inv j' hnext hz =
        (singleObjXSelf c j A).inv ≫ (asIso (((single C c j).obj A).iCycles j)).inv := by
      rw [← cancel_mono (((single C c j).obj A).iCycles j), liftCycles_i]
      simp
    rw [heq]
    infer_instance
  have hKπ : IsIso (K.homologyπ j) := isIso_homologyπ K _ j rfl hprev
  have hSπ : IsIso (((single C c j).obj A).homologyπ j) := isIso_homologyπ _ _ j rfl (hd _ j)
  have hmap : IsIso (homologyMap a j) := (quasiIsoAt_iff_isIso_homologyMap a j).mp inferInstance
  have heu : K.liftCycles ((singleObjXSelf c j A).inv ≫ a.f j) j' hnext
        (fromSingle_comp_d A a j') =
      ((single C c j).obj A).liftCycles (singleObjXSelf c j A).inv j' hnext hz ≫ cyclesMap a j := by
    rw [← cancel_mono (K.iCycles j), liftCycles_i, Category.assoc, cyclesMap_i,
      ← Category.assoc, liftCycles_i]
  have : IsIso (K.liftCycles ((singleObjXSelf c j A).inv ≫ a.f j) j' hnext
      (fromSingle_comp_d A a j') ≫ K.homologyπ j) := by
    rw [heu, Category.assoc, ← homologyπ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (K.homologyπ j)

/-- **A quasi-isomorphism in degree `j` out of a complex concentrated in degree `j` exhibits that
degree's object as a kernel of the differential leaving degree `j`**, provided no differential
enters degree `j`. -/
public noncomputable def isLimitKernelForkFromSingle (A : C)
    {K : _root_.HomologicalComplex C c} {j' : ι} (a : (single C c j).obj A ⟶ K)
    (hnext : c.next j = j') (hprev : K.d (c.prev j) j = 0) [QuasiIsoAt a j] {w : A ⟶ K.X j}
    (hw : w = (singleObjXSelf c j A).inv ≫ a.f j) (hwd : w ≫ K.d j j' = 0) :
    IsLimit (KernelFork.ofι w hwd) := by
  subst hw
  haveI := isIso_liftCycles_fromSingle A a hnext hprev
  exact IsLimit.ofIsoLimit (K.cyclesIsKernel j j' hnext)
    (Fork.ext (asIso (K.liftCycles ((singleObjXSelf c j A).inv ≫ a.f j) j' hnext
      (fromSingle_comp_d A a j'))).symm (by simp))

end Stacks.HomologicalComplex

/-! ### The absolute Čech augmentation of a quasi-coherent module -/

namespace Stacks.CechSiteChange

open Stacks.AlgebraicGeometry.CechPushforwardComplex

variable (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u})

/-- **The augmentation `ℱ ⟶ 𝔠 ⁰(𝒰, ℱ)` of the absolute Čech complex of [Stacks, Tag 01XL]**, as a
natural transformation in the quasi-coherent `𝒪_X`-module `ℱ`. -/
public noncomputable def absoluteCechAugZero :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⟶
      (absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        _root_.HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) 0 :=
  Stacks.HomologicalComplex.evalNatTransOfToSingle (absoluteCechAug X T)

/-- **The first differential `𝔠 ⁰(𝒰, ℱ) ⟶ 𝔠 ¹(𝒰, ℱ)` of the absolute Čech complex of
[Stacks, Tag 01XL]**, as a natural transformation in the quasi-coherent `𝒪_X`-module `ℱ`. -/
public noncomputable def absoluteCechDiffZero :
    (absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        _root_.HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) 0 ⟶
      (absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        _root_.HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) 1 :=
  Functor.whiskerLeft
    (absoluteCechPresheaf X ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)))
    (_root_.HomologicalComplex.dNatTrans X.Modules (ComplexShape.up ℕ) 0 1)

/-- The components of `absoluteCechAugZero`. -/
public theorem absoluteCechAugZero_app
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (absoluteCechAugZero X T).app F =
      (singleObjXSelf (ComplexShape.up ℕ) 0 F.obj).inv ≫ ((absoluteCechAug X T).app F).f 0 :=
  Stacks.HomologicalComplex.evalNatTransOfToSingle_app (absoluteCechAug X T) F

/-- The components of `absoluteCechDiffZero`. -/
public theorem absoluteCechDiffZero_app
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (absoluteCechDiffZero X T).app F =
      ((absoluteCechPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))).obj F).d 0 1 :=
  rfl

section ZeroComposite

-- the sheaf of rings of a scheme is reached from `X.Modules` through these two semireducible
-- definitions, and a zero morphism between the two resulting spellings is written below
attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules

/-- The augmentation followed by the first differential is zero, at a fixed quasi-coherent
`𝒪_X`-module. -/
public theorem absoluteCechAugZero_comp_diffZero_app
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (absoluteCechAugZero X T).app F ≫ (absoluteCechDiffZero X T).app F = 0 :=
  Stacks.HomologicalComplex.evalNatTransOfToSingle_comp_d (absoluteCechAug X T) 1 F

/-- **`ℱ ⟶ 𝔠 ⁰(𝒰, ℱ) ⟶ 𝔠 ¹(𝒰, ℱ)` is a complex**, naturally in the quasi-coherent
`𝒪_X`-module `ℱ`. -/
public theorem absoluteCechAugZero_comp_diffZero :
    absoluteCechAugZero X T ≫ absoluteCechDiffZero X T =
      (0 : (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) :
            (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ X.Modules) ⟶
          (absoluteCechPresheaf X ⋙
              CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
            _root_.HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) 1) :=
  Stacks.HomologicalComplex.evalNatTransOfToSingle_comp_dNatTrans (absoluteCechAug X T) 1

end ZeroComposite

/-- No differential of the absolute Čech complex enters degree zero, that complex being
`ℕ`-indexed. -/
public theorem absoluteCechComplex_d_prev_zero
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))).obj F).d
        ((ComplexShape.up ℕ).prev 0) 0 = 0 := by
  rw [CochainComplex.prev_nat_zero]
  exact _root_.HomologicalComplex.shape _ 0 0 (by simp)

/-- **The sheaf condition for `ℱ` written as a complex**: the augmentation `ℱ ⟶ 𝔠 ⁰(𝒰, ℱ)` of the
absolute Čech complex of [Stacks, Tag 01XL] is a kernel of the first differential
`𝔠 ⁰(𝒰, ℱ) ⟶ 𝔠 ¹(𝒰, ℱ)`. -/
public noncomputable def isLimitKernelFork_absoluteCechAugZero
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsLimit (KernelFork.ofι ((absoluteCechAugZero X T).app F)
      (absoluteCechAugZero_comp_diffZero_app X T F)) :=
  haveI := quasiIso_absoluteCechAug_app X T F
  Stacks.HomologicalComplex.isLimitKernelForkFromSingle _ ((absoluteCechAug X T).app F)
    (ComplexShape.next_eq' (ComplexShape.up ℕ) rfl) (absoluteCechComplex_d_prev_zero X T F)
    (absoluteCechAugZero_app X T F) (absoluteCechAugZero_comp_diffZero_app X T F)

/-- **The augmentation `ℱ ⟶ 𝔠 ⁰(𝒰, ℱ)` of the absolute Čech complex is a monomorphism.** -/
public theorem mono_absoluteCechAugZero
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Mono ((absoluteCechAugZero X T).app F) :=
  mono_of_isLimit_fork (isLimitKernelFork_absoluteCechAugZero X T F)

end Stacks.CechSiteChange

end
