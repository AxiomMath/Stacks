module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationCoordinateIdeal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExactInterior
public import StacksFrontier.Deformation.Examples.Geometric.SchemesCofibered
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceEquivTangent

/-!
# The second display of Stacks 0DY9 as a `k`-linear equivalence: the class map at `k[V]`

For every finite-dimensional `k`-vector space `V`, a flat deformation of `X` over `k[V]` has a
class in `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)`: the difference class of
[Stacks Project, Tag 08UC] of its solution of the deformation problem of
[Stacks Project, Tag 08U7] against that of the trivial deformation, read with coefficients
`𝒪_X ⊗_k V` (`Deformation.Examples.coordPulledIdealIso`).

## Main definitions

* `Deformation.Examples.squareZeroInclusion`: the inclusion `k → k[V]`.
* `Deformation.Examples.trivialFiberAt`: the trivial deformation `X ×_k Spec k[V]`.
* `Deformation.Examples.fiberExtClassAt`: the class of a deformation over `k[V]`.
* `Deformation.Examples.tangentExtClassAt`: the same on isomorphism classes.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (X : Over (Spec (CommRingCat.of k)))

/-- The inclusion `k → k[V]` of the residue field into the square-zero extension. -/
noncomputable def squareZeroInclusion (V : FGModuleCat.{u} k) :
    residueFieldObject.{u, u, u} Λ k ⟶ coordBase (Λ := Λ) V :=
  homOfAugComm
    { toFun := fun c => TrivSqZeroExt.inl (ULift.down c)
      map_one' := rfl
      map_mul' := fun x y => by
        refine TrivSqZeroExt.ext rfl ?_
        change (0 : V) = ULift.down x • (0 : V) + ULift.down y • (0 : V)
        simp
      map_zero' := rfl
      map_add' := fun x y => by
        refine TrivSqZeroExt.ext rfl ?_
        change (0 : V) = 0 + 0
        simp
      commutes' := fun _ => rfl }
    (fun c => by
      rw [← aug_spec]
      refine (squareZeroExtensionArtinian_residue Λ k V _).trans ?_
      exact (residueFieldCoordinates_residue.{u, u, u} c).symm.trans
        (aug_spec (residueFieldObject.{u, u, u} Λ k) c))

/-- The inclusions `k → k[V]` are compatible with the maps `k[g] : k[V] → k[W]`. -/
theorem squareZeroInclusion_comp {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    squareZeroInclusion (Λ := Λ) V ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map g =
      squareZeroInclusion W := by
  let (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
    Module.compHom V {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let (V : FGModuleCat.{u} k) : IsCentralScalar k V := ⟨fun _ _ => rfl⟩
  ext c
  rw [ArtinianLocalAlgCat.comp_hom]
  refine TrivSqZeroExt.ext ?_ ?_
  · show TrivSqZeroExt.fst (TrivSqZeroExt.map g.hom.hom
      (TrivSqZeroExt.inl (ULift.down c) : TrivSqZeroExt k V)) = ULift.down c
    rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_inl]
  · show TrivSqZeroExt.snd (TrivSqZeroExt.map g.hom.hom
      (TrivSqZeroExt.inl (ULift.down c) : TrivSqZeroExt k V)) = (0 : W)
    rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_inl, map_zero]

/-- The trivial deformation `X ×_k Spec k[V]`. -/
noncomputable def trivialDeformationAt (V : FGModuleCat.{u} k) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X :=
  baseChangeDeformation (residueTrivialDeformation X) (squareZeroInclusion V)

/-- The trivial deformation as a point of the fibre over `k[V]`. -/
abbrev trivialFiberAt (V : FGModuleCat.{u} k) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V) :=
  ⟨trivialDeformationAt X V, rfl⟩

/-- The arrow `X ×_k Spec k[V] → X ×_k Spec k[W]` over `k[g]`. -/
noncomputable def trivialDeformationMap {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    trivialDeformationAt (Λ := Λ) X V ⟶ trivialDeformationAt X W :=
  (existsUnique_factor_of_isHomLift
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation.cofibered
    (baseChangeDeformationHom (residueTrivialDeformation X) (squareZeroInclusion V))
    (baseChangeDeformationHom (residueTrivialDeformation X) (squareZeroInclusion W))
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)
    (squareZeroInclusion_comp g)).exists.choose

/-- The arrow `trivialDeformationMap X g` lies over `k[g] : k[V] → k[W]`. -/
theorem trivialDeformationMap_base {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).map (trivialDeformationMap X g) =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).map g := by
  unfold trivialDeformationMap
  generalize_proofs h
  exact h.choose_spec.1

/-! ### The class of a deformation over `k[V]` -/

section Std

attribute [local instance 10000] HasDerivedCategory.standard

/-- Changing the coefficients of `Ext¹_{𝒪_X}(NL_{X/k}, -)` along `f^* 𝒥 ≅ 𝒪_X ⊗_k V`. -/
noncomputable def coordExtCoefficientsAddEquiv (V : FGModuleCat.{u} k) :
    extOneNaiveCotangent X.hom.toLRSHom.toShHom
        (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) X) ≃+
      schemeTangentExtAt X V :=
  Stacks.Injectives.homCongrAddEquiv (Iso.refl _)
    ((shiftFunctor _ (1 : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (coordPulledIdealIso (Λ := Λ) V X)))

end Std

/-- The solutions over `k[V]`. -/
abbrev CoordSolution (V : FGModuleCat.{u} k) :=
  DeformationSolution (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom
    (residueSpecMap_isFirstOrderThickening (coordBase V)
      (maximalIdeal_squareZeroExtensionArtinian_pow_two V))
    X.hom.toLRSHom.toShHom (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) X) (𝟙 _)

/-- **The class of a deformation of `X` over `k[V]`** in `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)`: the
difference class of its solution against that of the trivial deformation. -/
noncomputable def fiberExtClassAt (V : FGModuleCat.{u} k)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :
    schemeTangentExtAt X V :=
  coordExtCoefficientsAddEquiv X V
    (AlgebraicGeometry.RingedSpaceThickening.differenceClass
      (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two V) x)
      (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two V) (trivialFiberAt X V)))

/-- The difference class only depends on the isomorphism class of the first solution. -/
theorem differenceClass_congr_left {X' S S' : RingedSpace.{u, u}} {t : S ⟶ S'}
    {ht : IsFirstOrderThickening t} {f : X' ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X')}
    {c : (RingedSpaceModuleAdjunction.modulePullback f).obj
      ((RingedSpaceModuleAdjunction.modulePullback t).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
    {Q₁ Q₁' : DeformationSolution t ht f G c} (Q₂ : DeformationSolution t ht f G c)
    (h : Isomorphic Q₁ Q₁') :
    AlgebraicGeometry.RingedSpaceThickening.differenceClass Q₁ Q₂ =
      AlgebraicGeometry.RingedSpaceThickening.differenceClass Q₁' Q₂ := by
  have : Nonempty (DeformationSolution t ht f G c) := ⟨Q₂⟩
  let := solutionClassesAddTorsor (t := t) (ht := ht) (f := f) (G := G) (c := c)
  exact (AlgebraicGeometry.RingedSpaceThickening.vsub_mk_mk
      (t := t) (ht := ht) (f := f) (G := G) (c := c) Q₁ Q₂).symm.trans
    ((congrArg (· -ᵥ (⟦Q₂⟧ : SolutionClasses t ht f G c))
      (Quotient.sound h : (⟦Q₁⟧ : SolutionClasses t ht f G c) = ⟦Q₁'⟧)).trans
      (AlgebraicGeometry.RingedSpaceThickening.vsub_mk_mk
        (t := t) (ht := ht) (f := f) (G := G) (c := c) Q₁' Q₂))

/-- The class of a deformation over `k[V]` only depends on its isomorphism class. -/
theorem fiberExtClassAt_congr (V : FGModuleCat.{u} k)
    (x x' : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V))
    (h : IsIsomorphic x x') : fiberExtClassAt X V x = fiberExtClassAt X V x' := by
  obtain ⟨e⟩ := h
  exact congrArg (coordExtCoefficientsAddEquiv X V) (differenceClass_congr_left _
    (isomorphic_fiberSolution_of_hom (maximalIdeal_squareZeroExtensionArtinian_pow_two V) e.inv))

/-- The deformation category of `X`, as a based category. -/
abbrev schemeDeformationBased : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k) :=
  BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)

/-- **The class map on isomorphism classes of deformations over `k[V]`.** -/
noncomputable def tangentExtClassAt (V : FGModuleCat.{u} k)
    (z : (associatedTangentSpaceSetFunctor (schemeDeformationBased (Λ := Λ) X)
      (schemeDeformation_cofibered X)).obj V) : schemeTangentExtAt X V :=
  Quotient.liftOn
    (cast (isomorphismClasses_obj (schemeDeformationBased (Λ := Λ) X)
      (schemeDeformation_cofibered X) ((squareZeroExtensionArtinian Λ k).obj V)) z)
    (fiberExtClassAt X V) (fiberExtClassAt_congr X V)

/-- The class map on the class of a point of the fibre. -/
theorem tangentExtClassAt_classOf (V : FGModuleCat.{u} k)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase (Λ := Λ) V)) :
    tangentExtClassAt X V (classOf (schemeDeformationBased (Λ := Λ) X)
      (schemeDeformation_cofibered X) x) = fiberExtClassAt X V x :=
  congrArg (fun q => Quotient.liftOn q (fiberExtClassAt X V) (fiberExtClassAt_congr X V))
    (classOf_eq (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X) x)

/-- The deformation problem over `k[V]` has a solution, that of the trivial deformation. -/
instance nonempty_coordSolution (V : FGModuleCat.{u} k) :
    Nonempty (CoordSolution (Λ := Λ) X V) :=
  ⟨fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two V) (trivialFiberAt X V)⟩

/-- **The class map at `k[V]` is a bijection**: it is the composite of the identification of the
fibre classes with the classes of solutions, the difference with the trivial deformation in the
principal homogeneous space of [Stacks Project, Tag 08UC], and the change of coefficients. -/
theorem bijective_tangentExtClassAt (V : FGModuleCat.{u} k) :
    Function.Bijective (tangentExtClassAt (Λ := Λ) X V) := by
  let := solutionClassesAddTorsor (t := (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom)
    (ht := residueSpecMap_isFirstOrderThickening (coordBase V)
      (maximalIdeal_squareZeroExtensionArtinian_pow_two V))
    (f := X.hom.toLRSHom.toShHom) (G := SchemeDeformationCategory.pulledIdeal (coordBase V) X)
    (c := 𝟙 _)
  let E := ((Equiv.cast (isomorphismClasses_obj (schemeDeformationBased (Λ := Λ) X)
      (schemeDeformation_cofibered X) ((squareZeroExtensionArtinian Λ k).obj V))).trans
    (fiberClassesEquivSolutionClasses (maximalIdeal_squareZeroExtensionArtinian_pow_two V)
      isomorphicSetoid (fun _ _ => Iff.rfl))).trans
    ((Equiv.vaddConst (Quotient.mk isomorphicSetoid (fiberSolution
      (maximalIdeal_squareZeroExtensionArtinian_pow_two V) (trivialFiberAt X V)))).symm.trans
      (coordExtCoefficientsAddEquiv X V).toEquiv)
  have hE (z) : E z = tangentExtClassAt X V z := by
    obtain ⟨x, rfl⟩ := classOf_surjective (schemeDeformationBased (Λ := Λ) X)
      (schemeDeformation_cofibered X) _ z
    refine Eq.trans ?_ (tangentExtClassAt_classOf X V x).symm
    exact congrArg (fun q => coordExtCoefficientsAddEquiv X V ((Equiv.vaddConst _).symm
      (fiberClassesEquivSolutionClasses _ isomorphicSetoid (fun _ _ => Iff.rfl) q)))
      (classOf_eq (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X) x)
  rw [show tangentExtClassAt (Λ := Λ) X V = E from (funext hE).symm]
  exact E.bijective

end Deformation.Examples

end
