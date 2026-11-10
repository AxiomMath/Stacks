module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.JointlySurjectiveFamilyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentOfBaseChange
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

/-!
# SheafDescentProperBaseChangeUnconditional

Effective descent of small étale sheaves along a surjective proper morphism of a big étale
site, deduced from the proper base change theorem for sheaves of sets in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- The inverse image of the small étale sheaf pseudofunctor along a morphism of a big étale site
is left adjoint to the direct image along it: this is the adjunction
`AlgebraicGeometry.BigEtaleSite.smallPullbackAdjunction`, with its left adjoint spelled as the
value of the pseudofunctor. -/
public abbrev smallEtaleSheafPseudofunctorAdjunctionGeneral {X Y : B.Scheme} (h : X ⟶ Y) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map h.op.toLoc).toFunctor ⊣
      B.smallPushforward h (Type (u + 1)) :=
  B.smallPullbackAdjunction h (Type (u + 1))

/-- The composition comparison of the small étale sheaf pseudofunctor, read on functors, is the
inverse of `AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`. -/
private theorem mapComp_hom_toNatTrans_general {X Y Z : B.Scheme} (h : X ⟶ Y) (k : Y ⟶ Z) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.mapComp k.op.toLoc
        h.op.toLoc).hom.toNatTrans =
      (smallEtaleMorphism_comp_inverseImageIso B X Y Z h k).inv := by
  rw [eq_of_heq ((smallEtaleSheafPullbackSystemGeneral B).mapComp_canonical h k)]
  rfl

/-- The inverse of the composition comparison of the small étale sheaf pseudofunctor, read on
functors, is `AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`. -/
private theorem mapComp_inv_toNatTrans_general {X Y Z : B.Scheme} (h : X ⟶ Y) (k : Y ⟶ Z) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.mapComp k.op.toLoc
        h.op.toLoc).inv.toNatTrans =
      (smallEtaleMorphism_comp_inverseImageIso B X Y Z h k).hom := by
  rw [eq_of_heq ((smallEtaleSheafPullbackSystemGeneral B).mapComp_canonical h k)]
  rfl

/-- The image under the small étale sheaf pseudofunctor of the identification of two equal
morphisms is the identification of their inverse images. -/
private theorem map₂_eqToHom_toNatTrans_general {X Y : B.Scheme} {k k' : X ⟶ Y} (e : k = k') :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map₂
        (eqToHom (congrArg (fun m : X ⟶ Y => m.op.toLoc) e))).toNatTrans =
      eqToHom (congrArg (fun m : X ⟶ Y => B.smallInverseImage m (Type (u + 1))) e) := by
  subst e
  simp only [eqToHom_refl, PrelaxFunctor.map₂_id]
  rfl

/-- The comparison of the two composite inverse images around a commutative square, for the small
étale sheaf pseudofunctor, is the composite of the two composition comparisons of inverse images
with the identification of the inverse images along the two equal composites. -/
public theorem commSqTwoSquare_smallEtaleSheafPullbackSystem {X X' Y Y' : B.Scheme}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (w : i ≫ f = f' ≫ g) :
    (Pseudofunctor.commSqTwoSquare (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor w :
        _ ⟶ _) =
      (smallEtaleMorphism_comp_inverseImageIso B X' Y' Y f' g).hom ≫
        eqToHom (congrArg (fun m : X' ⟶ Y => B.smallInverseImage m (Type (u + 1))) w.symm) ≫
          (smallEtaleMorphism_comp_inverseImageIso B X' X Y i f).inv := by
  have hw : g.op.toLoc ≫ f'.op.toLoc = f.op.toLoc ≫ i.op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← Quiver.Hom.comp_toLoc, ← op_comp, ← op_comp, w]
  rw [show Pseudofunctor.commSqTwoSquare (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor w =
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.mapComp g.op.toLoc
          f'.op.toLoc).inv.toNatTrans ≫
        ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map₂ (eqToHom
          (congrArg (fun m : X' ⟶ Y => m.op.toLoc) w.symm))).toNatTrans ≫
        ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.mapComp f.op.toLoc
          i.op.toLoc).hom.toNatTrans
      from by
        simp only [Pseudofunctor.commSqTwoSquare, Pseudofunctor.isoMapOfCommSq,
          Pseudofunctor.mapComp', Iso.trans_hom, Iso.symm_hom, PrelaxFunctor.map₂Iso_hom,
          eqToIso.hom, Cat.Hom.toNatIso, Cat.Hom.toNatTrans_comp]
        rfl,
    mapComp_inv_toNatTrans_general, mapComp_hom_toNatTrans_general,
    map₂_eqToHom_toNatTrans_general B w.symm]
  rfl

/-- **The base-change `2`-cell of the small étale sheaf pseudofunctor is the base change map.**
For a commutative square `i ≫ f = f' ≫ g` of a big étale site, the mate along the two vertical
inverse-image/direct-image adjunctions of the comparison of the two composite inverse images is
the base change comparison `g⁻¹ f_* ⟶ f'_* i⁻¹` of
`AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`, which is built as the mate along the two
horizontal adjunctions of the comparison of the two composite direct images. -/
public theorem mateEquiv_commSqTwoSquare_smallEtaleSheafPullbackSystem {X X' Y Y' : B.Scheme}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (w : i ≫ f = f' ≫ g) :
    (mateEquiv (smallEtaleSheafPseudofunctorAdjunctionGeneral B f)
        (smallEtaleSheafPseudofunctorAdjunctionGeneral B f')
        (Pseudofunctor.commSqTwoSquare (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor
          w)) =
      smallEtaleBaseChangeNatTransUniv.{u, 0} B i f' f g w := by
  rw [smallEtaleBaseChangeNatTransUniv]
  refine (Equiv.eq_symm_apply _).2 ?_
  refine (iterated_mateEquiv_conjugateEquiv
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B f)
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B f')
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B g)
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B i)
    _).trans ?_
  rw [commSqTwoSquare_smallEtaleSheafPullbackSystem]
  have h₁ : conjugateEquiv (B.smallPullbackAdjunction (f' ≫ g) (Type (u + 1)))
      ((B.smallPullbackAdjunction g (Type (u + 1))).comp
        (B.smallPullbackAdjunction f' (Type (u + 1))))
      (smallEtaleMorphism_comp_inverseImageIso B X' Y' Y f' g).hom =
      (smallEtaleMorphism_comp_pushforwardIso B X' Y' Y f' g).inv := by
    change conjugateEquiv _ _ ((conjugateEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have h₂ : conjugateEquiv ((B.smallPullbackAdjunction f (Type (u + 1))).comp
      (B.smallPullbackAdjunction i (Type (u + 1))))
      (B.smallPullbackAdjunction (i ≫ f) (Type (u + 1)))
      (smallEtaleMorphism_comp_inverseImageIso B X' X Y i f).inv =
      (smallEtaleMorphism_comp_pushforwardIso B X' X Y i f).hom :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have h₃ := conjugateEquiv_smallInverseImage_eqToHom B w.symm
  let A₁ := (B.smallPullbackAdjunction f (Type (u + 1))).comp
    (B.smallPullbackAdjunction i (Type (u + 1)))
  let A₂ := B.smallPullbackAdjunction (f' ≫ g) (Type (u + 1))
  let A₂' := B.smallPullbackAdjunction (i ≫ f) (Type (u + 1))
  let A₃ := (B.smallPullbackAdjunction g (Type (u + 1))).comp
    (B.smallPullbackAdjunction f' (Type (u + 1)))
  calc conjugateEquiv A₁ A₃ ((smallEtaleMorphism_comp_inverseImageIso B X' Y' Y f' g).hom ≫
        eqToHom (congrArg (fun m : X' ⟶ Y => B.smallInverseImage m (Type (u + 1))) w.symm) ≫
          (smallEtaleMorphism_comp_inverseImageIso B X' X Y i f).inv)
      = conjugateEquiv A₁ A₂
          (eqToHom (congrArg (fun m : X' ⟶ Y => B.smallInverseImage m (Type (u + 1))) w.symm) ≫
            (smallEtaleMorphism_comp_inverseImageIso B X' X Y i f).inv) ≫
          conjugateEquiv A₂ A₃ (smallEtaleMorphism_comp_inverseImageIso B X' Y' Y f' g).hom :=
        (conjugateEquiv_comp A₁ A₂ A₃ _ _).symm
    _ = (conjugateEquiv A₁ A₂' (smallEtaleMorphism_comp_inverseImageIso B X' X Y i f).inv ≫
          conjugateEquiv A₂' A₂
            (eqToHom (congrArg (fun m : X' ⟶ Y => B.smallInverseImage m (Type (u + 1))) w.symm))) ≫
          conjugateEquiv A₂ A₃ (smallEtaleMorphism_comp_inverseImageIso B X' Y' Y f' g).hom :=
        congrArg (· ≫ _) (conjugateEquiv_comp A₁ A₂' A₂ _ _).symm
    _ = _ := by
      rw [h₁, h₂, h₃, smallEtaleSheafPushforwardCompIso_type,
        smallEtaleSheafPushforwardCompIso_type, eqToIso.hom, Category.assoc]
/-- **Effective descent of small étale sheaves along a surjection, from base change.** Let
`f : X ⟶ Y` be a morphism of a big étale site which is surjective on underlying points, and
suppose that the base change map `g⁻¹ f_* ⟶ f'_* i⁻¹` of sheaves of sets
(`AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`) is invertible for the square of `f` against
itself and for the square of the structure morphism `X ×_Y X ⟶ Y` against `f`, the two fibre
products being given as chosen fibre products `XX` and `ZZ`. Then the functor
from sheaves on the small étale site of `Y` to descent data for `{X ⟶ Y}` is an equivalence.

For a proper surjection these two base change maps are invertible by the proper base change
theorem in degree zero, Stacks 0A3U, and the statement is then Stacks 0GF0; for an integral
surjection they are invertible by Stacks 0EYP, and the statement is Stacks 0GEZ. The proof is
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_isIso_mateEquiv`: the two
base-change `2`-cells it asks for are the two base change maps, by
`AlgebraicGeometry.mateEquiv_commSqTwoSquare_smallEtaleSheafPullbackSystem`, inverse image along
`f` is left exact, and it reflects isomorphisms because `f` is surjective. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans
    {X Y : B.Scheme} (f : X ⟶ Y) (hf : Function.Surjective (B.inclusion.map f).base)
    (XX : ChosenPullback f f) (ZZ : ChosenPullback XX.p f)
    (hβ : ∀ M, IsIso ((smallEtaleBaseChangeNatTransUniv.{u, 0} B XX.p₁ XX.p₂ f f
      XX.condition).app M))
    (hγ : ∀ N, IsIso ((smallEtaleBaseChangeNatTransUniv.{u, 0} B ZZ.p₁ ZZ.p₂ XX.p f
      ZZ.condition).app N)) :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence := by
  rw [isEquivalence_smallEtaleSheafDescentFunctor_iff_general]
  have : HasEqualizers ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.obj (.mk (.op Y))) :=
    inferInstanceAs (HasEqualizers (Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1))))
  have : HasEqualizers ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.obj (.mk (.op X))) :=
    inferInstanceAs (HasEqualizers (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))))
  have : PreservesFiniteLimits
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map f.op.toLoc).toFunctor := by
    have : RepresentablyFlat (smallEtaleBaseChange B f) := flat_of_preservesFiniteLimits _
    exact inferInstanceAs (PreservesFiniteLimits (B.smallInverseImage f (Type (u + 1))))
  have : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
      f.op.toLoc).toFunctor.ReflectsIsomorphisms :=
    reflectsIsomorphisms_smallEtaleSetPullbackFunctor B f hf
  refine Pseudofunctor.isEquivalence_toDescentData_of_isIso_mateEquiv _ f XX ZZ
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B f)
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B XX.p)
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B XX.p₂)
    (smallEtaleSheafPseudofunctorAdjunctionGeneral B ZZ.p₂) (fun M => ?_) (fun N => ?_)
  · rw [mateEquiv_commSqTwoSquare_smallEtaleSheafPullbackSystem]
    exact hβ M
  · rw [mateEquiv_commSqTwoSquare_smallEtaleSheafPullbackSystem]
    exact hγ N

/-- **Effective descent of small étale sheaves along a proper surjection, from the proper base
change theorem in degree zero.** Let `f : X ⟶ Y` be a surjective proper morphism of a big étale
site. Granted the conclusion of the proper base change theorem for sheaves of sets, Stacks 0A3U
— for every cartesian square of schemes with proper right-hand side, the base change map
`g⁻¹ f_* ⟶ f'_* (g')⁻¹` of `Stacks.EtaleCohomology.smallEtaleSetBaseChange` is an isomorphism —
the functor from sheaves on the small étale site of `Y` to descent data for `{X ⟶ Y}` is an
equivalence. This is Stacks 0GF0 with Stacks 0A3U as its single input.
-/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
    {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  let XX := ChosenPullback.ofHasPullback f f
  let ZZ := ChosenPullback.ofHasPullback XX.p f
  have h₁ : IsProper (B.inclusion.map XX.p₁) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (B.inclusion.map_isPullback XX.isPullback.flip) ‹_›
  have hp : IsProper (B.inclusion.map XX.p) := by
    rw [← XX.hp₁, B.inclusion.map_comp]
    infer_instance
  refine smallEtaleSheafDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans B f
    (B.inclusion.map f).surjective XX ZZ (fun M => ?_) (fun N => ?_)
  · have := SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange_general
      B f f XX.p₁ XX.p₂ XX.condition
      (h0A3U _ _ _ _ (B.inclusion.map_isPullback XX.isPullback) ‹_›)
    infer_instance
  · have := SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange_general
      B XX.p f ZZ.p₁ ZZ.p₂ ZZ.condition
      (h0A3U _ _ _ _ (B.inclusion.map_isPullback ZZ.isPullback) hp)
    infer_instance

end AlgebraicGeometry

end
