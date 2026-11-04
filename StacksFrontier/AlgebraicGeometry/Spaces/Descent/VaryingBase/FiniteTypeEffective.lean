module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.FiniteTypeAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.SheafGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveDescentRefinement

/-!
# The stack of finite-type algebraic spaces over varying bases (Stacks 04UD, 04UE)

Stacks 04UD asserts the three conditions of Stacks 026F for the projection
`AlgebraicGeometry.finiteTypeSpacesProjection` from algebraic spaces of finite type over varying
base schemes to the big fppf site of `S`. Conditions (1) and (2) are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeStack.lean`. This file proves condition (3), from
the bootstrap theorem Stacks 04S6 condition (3),
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`, and assembles the whole of
`CategoryTheory.Functor.IsStack`. Stacks 04UE, the set-sized replacement of that stack, follows.

## Main results

* `AlgebraicGeometry.finiteTypeSpacesProjection_isStack_of_bootstrap`: **Stacks 04UD**, the
  projection from finite-type algebraic spaces over varying bases is a stack.
* `AlgebraicGeometry.exists_small_finiteTypeSpaces_stack_unconditional`: **Stacks 04UE**.
* `AlgebraicGeometry.SpacesDescent.locallyClosed_isFiniteTypeSpace`: condition (3) of Stacks 04TU
  for the finite-type subcategory, i.e. finite type is fppf local on the base.

## Implementation notes

Both theorems sit here rather than next to the definitions of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeStack.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeStackSmall.lean` because those files are
upstream of the proof of Stacks 04S6 condition (3).

## References

* [Stacks Project, Tag 04UD](https://stacks.math.columbia.edu/tag/04UD)
* [Stacks Project, Tag 04UE](https://stacks.math.columbia.edu/tag/04UE)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.SpacesDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The normalized structure morphism of an object of the fibre of `spacesProjection` is of finite
type exactly when its structure morphism is. -/
private theorem isFiniteType_fiberHom_iff {V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber V) :
    Space.IsFiniteType B S hS (fiberHom X) ↔ isFiniteTypeSpace B S hS X.1 := by
  obtain ⟨X0, hX0⟩ := X
  subst hX0
  simp [fiberHom, isFiniteTypeSpace]

/-- The normalized structure morphism of an object of the fibre of `spacesProjection` whose
structure morphism is of finite type is of finite type. -/
theorem isFiniteType_fiberHom {V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber V)
    (h : isFiniteTypeSpace B S hS X.1) : Space.IsFiniteType B S hS (fiberHom X) :=
  (isFiniteType_fiberHom_iff X).2 h

/-- Finite typeness of the structure morphism is invariant under isomorphism in the comma category
of algebraic spaces over varying bases. -/
theorem isFiniteTypeSpace_of_iso
    {y y' : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (e : y ≅ y') (hy' : isFiniteTypeSpace B S hS y') : isFiniteTypeSpace B S hS y := by
  have : IsIso e.hom.left.hom :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map (Comma.leftIso e).hom))
  have : IsIso (yoneda.map e.hom.right) :=
    inferInstanceAs (IsIso (yoneda.map (Comma.rightIso e).hom))
  have sq : IsPullback e.hom.left.hom y.hom y'.hom (yoneda.map e.hom.right) :=
    IsPullback.of_horiz_isIso ⟨e.hom.w⟩
  exact isFiniteType_of_isPullback_of_isFiniteType y.left.property
    (isAlgebraicSpace_yoneda B S hS _) y'.left.property (isAlgebraicSpace_yoneda B S hS _) sq hy'

/-- **Being of finite type over the base is fppf local on the base**, as condition (3) of
Stacks 04TU for the full subcategory of finite-type algebraic spaces: an object whose chosen
pullbacks along a covering family are of finite type is of finite type. -/
theorem locallyClosed_isFiniteTypeSpace :
    haveI := spacesProjection_isFibered B S hS
    Functor.LocallyClosed (spacesProjection B S hS) (isFiniteTypeSpace B S hS)
      (BigFppfOver.topology B S hS) := by
  have := spacesProjection_isFibered B S hS
  intro U ι Ui fi hgen x hx
  apply Functor.isoOverId_of_prop
  obtain ⟨I, Wb, m, hmR, hflat, hlfp, hsurj⟩ := exists_family_of_mem_topology B S hS hgen
  let W : I → BigFppfOver B S hS := fun i => Over.mk (m i ≫ U.hom)
  let g : ∀ i, W i ⟶ U := fun i => Over.homMk (m i)
  have hfac : ∀ i, ∃ (k : ι) (h : W i ⟶ Ui k), h ≫ fi k = g i := fun i => by
    obtain ⟨Y, h, gk, ⟨k⟩, hcomp⟩ := hmR i
    exact ⟨k, h, hcomp⟩
  choose k h hh using hfac
  have hpb : ∀ i, Space.IsFiniteType B S hS
      (fiberHom (Functor.pullbackFiber (spacesProjection B S hS) x (fi (k i)))) := fun i =>
    isFiniteType_fiberHom _ (by
      obtain ⟨y', hy', e, -⟩ := hx (k i)
      exact isFiniteTypeSpace_of_iso e hy')
  let X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun i =>
    pullback (fiberHom (Functor.pullbackFiber (spacesProjection B S hS) x (fi (k i))))
      (yoneda.map (h i))
  have hX : ∀ i, IsAlgebraicSpace B S hS (X i) := fun i =>
    isAlgebraicSpace_pullback B S hS _ _
      (Functor.pullbackFiber (spacesProjection B S hS) x (fi (k i))).1.left.property
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
  have hsq : ∀ i, IsPullback
      (pullback.fst _ _ ≫ (Functor.IsPreFibered.pullbackMap x.2 (fi (k i))).left.hom)
      (pullback.snd _ _ : X i ⟶ yoneda.obj (W i)) (fiberHom x) (yoneda.map (g i)) := by
    intro i
    rw [← hh i, Functor.map_comp]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_pullbackMap x (fi (k i)))
  have hft : ∀ i, Space.IsFiniteType B S hS (pullback.snd _ _ : X i ⟶ yoneda.obj (W i)) :=
    fun i => isFiniteType_of_isPullback_of_isFiniteType (hX i) (isAlgebraicSpace_yoneda B S hS _)
      (Functor.pullbackFiber (spacesProjection B S hS) x (fi (k i))).1.left.property
      (isAlgebraicSpace_yoneda B S hS _) (IsPullback.of_hasPullback _ _) (hpb i)
  exact (isFiniteType_fiberHom_iff x).1 <| isFiniteType_of_forall_isPullback
    x.1.left.property (fiberHom x) W g hflat hlfp hsurj X hX _ _ hsq hft

end AlgebraicGeometry.SpacesDescent

namespace AlgebraicGeometry

open SpacesDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04UD.** The projection from finite-type algebraic spaces over varying base schemes
is a stack over the big fppf site of `S`: it satisfies all three conditions of Stacks 026F.

Conditions (1) and (2) are `AlgebraicGeometry.finiteTypeSpacesProjection_isFibered` and
`AlgebraicGeometry.finiteTypeSpacesProjection_isMorSheaf`. For condition (3), a descent datum is
read in the ambient comma category, where its underlying sheaves glue
(`AlgebraicGeometry.SpacesDescent.nonempty_sheafGlueing`, Stacks 04TR). The glued sheaf is an
algebraic space by Stacks 04U0 over the base of the datum
(`AlgebraicGeometry.SpacesDescent.isAlgebraicSpace_of_isPullback_of_isFiniteType`), which is where
Stacks 04S6 condition (3) and the finite-type hypothesis are spent, so the datum is effective there
(`AlgebraicGeometry.SpacesDescent.SheafGlueing.isEffective`). The descended object is of finite
type over the base because finite type is fppf local on the base
(`AlgebraicGeometry.SpacesDescent.locallyClosed_isFiniteTypeSpace`, Stacks 041U), which brings the
effectivity back to the full subcategory
(`CategoryTheory.Functor.SieveDescentDatum.isEffective_of_isEffective_mapι`). -/
@[stacks 04UD]
theorem finiteTypeSpacesProjection_isStack_of_bootstrap :
    (finiteTypeSpacesProjection B S hS).IsStack (BigFppfOver.topology B S hS) := by
  have := spacesProjection_isFibered B S hS
  refine ⟨finiteTypeSpacesProjection_isFibered B S hS,
    finiteTypeSpacesProjection_isMorSheaf B S hS, fun U R hR D => ?_⟩
  have := finiteTypeSpacesProjection_isFibered B S hS
  refine Functor.SieveDescentDatum.isEffective_of_isEffective_mapι (spacesProjection B S hS)
    (BigFppfOver.topology B S hS) (isFiniteTypeSpace B S hS)
    (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS) locallyClosed_isFiniteTypeSpace hR D ?_
  obtain ⟨G⟩ := nonempty_sheafGlueing (Functor.SieveDescentDatum.mapι (spacesProjection B S hS)
    (isFiniteTypeSpace B S hS) (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS) D) hR
  refine SheafGlueing.isEffective _ G ?_
  obtain ⟨K, W, V, j, f, hfR, hWaff, -, hflat, hlfp, hcov, hK, hsize⟩ :=
    exists_affine_refinement hR
  have hR' : ∀ k, R.arrows (j k ≫ f k) := fun k => R.downward_closed (hfR k) (j k)
  have hUcut : ((BigFppfOver.toScheme B S hS).obj U).size < B.cutoff := U.left.property
  exact isAlgebraicSpace_of_isPullback_of_isFiniteType G.isSheaf G.π W
    (fun k => j k ≫ f k) hWaff hflat hlfp hcov
    ((Scheme.aleph0_le_size _).trans (Cardinal.cantor _).le)
    (B.cutoff_isStrongPrelimit hUcut) hK (Cardinal.cantor _).le
    (fun k => (hsize k).trans (Cardinal.cantor _).le)
    (fun k => (D.obj _ (hR' k)).1.1.left.obj) (fun k => (D.obj _ (hR' k)).1.1.left.property)
    (fun k => G.ι _ (hR' k)) _ (fun k => G.isPullback _ (hR' k))
    (fun k => isFiniteType_fiberHom _ (D.obj _ (hR' k)).1.property)

/-- **Stacks 04UE.** There is a strictly full subcategory of the stack of finite-type
algebraic spaces over varying base schemes with set-sized fibres whose inclusion is essentially
surjective (and fully faithful, being the inclusion of a full subcategory) and whose restricted
projection is still a stack over the big fppf site of `S`.

The source deduces this from Stacks 04UD,
`AlgebraicGeometry.finiteTypeSpacesProjection_isStack_of_bootstrap`, and the replacement of
Stacks 03ZZ, `CategoryTheory.Functor.IsStack.exists_small_fullSubcategory`, which applies because
the category of finite-type algebraic spaces is essentially small; that deduction is
`AlgebraicGeometry.exists_small_finiteTypeSpaces_stack`, whose Stacks 04UD input is discharged
here. -/
@[stacks 04UE "the small stack of finite-type algebraic spaces"]
theorem exists_small_finiteTypeSpaces_stack_unconditional :
    ∃ P : ObjectProperty (FiniteTypeSpaces B S hS),
      (∀ T : BigFppfOver B S hS,
        Small.{u} ((P.ι ⋙ finiteTypeSpacesProjection B S hS).Fiber T)) ∧
        P.ι.EssSurj ∧
        (P.ι ⋙ finiteTypeSpacesProjection B S hS).IsStack
          (BigFppfOver.topology B S hS) :=
  exists_small_finiteTypeSpaces_stack B S hS
    (finiteTypeSpacesProjection_isStack_of_bootstrap B S hS)

end AlgebraicGeometry

end
