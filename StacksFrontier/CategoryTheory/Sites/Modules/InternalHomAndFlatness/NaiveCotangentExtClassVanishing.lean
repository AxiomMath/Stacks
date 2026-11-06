module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble

/-!
# When the first Ext class of a conormal homomorphism vanishes

Let `α : E ⟶ B` be a locally surjective polynomial presentation of a sheaf of rings `B` over
`A`, with naive cotangent complex `NL(α) = (I/I² ⟶ Ω)` in degrees `-1` and `0`, and let `G` be
a `B`-module. The class `presentationConormalExtClass f ∈ Ext¹_B(NL(α), G)` of a homomorphism
`f : I/I² ⟶ G` vanishes exactly when `f` factors through the differential `I/I² ⟶ Ω`.

The class is the chain map `NL(α) ⟶ G[1]` that is `f` in degree `-1`. Up to sign it is the class
`P.proj ≫ f[1]` of the two-term structure
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.ofDoubleNegOne` of `NL(α)`. That
structure comes with a distinguished triangle and with the vanishing criterion
`NaiveCotangentTwoTerm.conormalExtClass_eq_zero_iff`. The comparison is a computation of the
mapping cone in degree `-1`, and works in any abelian category.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.Q_map_mkHomToSingle_comp`: in
  an abelian category, the class of the chain map `double d ⟶ G[1]` given by `f` in degree `-1`
  is minus the class of `f` for `ofDoubleNegOne d`.
* `Stacks.SheafOfModules.presentationConormalExtClass_eq_neg`: the same for
  `presentationConormalExtClass`.
* `Stacks.SheafOfModules.presentationConormalExtClass_eq_zero_iff`: the vanishing criterion.
* `Stacks.SheafOfModules.presentationConormalExtClass_add`: the class is additive.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ComplexShape (upIntRelNegOneZero)

universe t w v u

namespace AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm

variable {C : Type u} [Category.{v} C] [Abelian C] {X₀ X₁ : C} (d : X₀ ⟶ X₁) (G : C)

/-- In degree `-1`, the chain map `double d ⟶ G[1]` given by `f` in degree `-1` is minus the
composite of the comparison with the mapping cone, the third map of the mapping cone triangle,
and the shift of `f`. -/
theorem mkHomToSingle_comp_shiftIso_inv (f : X₀ ⟶ G)
    (hf : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i (-1) →
      (double d upIntRelNegOneZero).d i (-1) ≫ ((doubleXIso₀ d upIntRelNegOneZero).hom ≫ f) = 0) :
    mkHomToSingle ((doubleXIso₀ d upIntRelNegOneZero).hom ≫ f) hf ≫
        ((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by decide)).inv.app G =
      -(CochainComplex.doubleToMappingCone d upIntRelNegOneZero ≫
        (CochainComplex.mappingCone.triangle
          ((single C (ComplexShape.up ℤ) 0).map d)).mor₃ ≫
        (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map
          ((single C (ComplexShape.up ℤ) 0).map f)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = -1
  · subst hn
    show _ = -((CochainComplex.doubleToMappingCone d upIntRelNegOneZero).f (-1) ≫
      (CochainComplex.mappingCone.triangle
        ((single C (ComplexShape.up ℤ) 0).map d)).mor₃.f (-1) ≫
      (((single C (ComplexShape.up ℤ) 0).map f)⟦(1 : ℤ)⟧').f (-1))
    rw [CochainComplex.doubleToMappingCone, mkHomFromDouble_f₀, Category.assoc, Category.assoc]
    have h3 := CochainComplex.mappingCone.inl_v_triangle_mor₃_f_assoc
      ((single C (ComplexShape.up ℤ) 0).map d) 0 (-1) (by omega)
      ((((single C (ComplexShape.up ℤ) 0).map f)⟦(1 : ℤ)⟧').f (-1))
    refine Eq.trans ?_ (congrArg (fun k => -((doubleXIso₀ d upIntRelNegOneZero).hom ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 X₀).inv ≫ k)) h3).symm
    have h4 : (doubleXIso₀ d upIntRelNegOneZero).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 X₀).inv ≫
        (-(CochainComplex.shiftFunctorObjXIso ((single C (ComplexShape.up ℤ) 0).obj X₀)
          1 (-1) 0 (by omega)).inv) ≫
        (((single C (ComplexShape.up ℤ) 0).map f)⟦(1 : ℤ)⟧').f (-1) =
      -((doubleXIso₀ d upIntRelNegOneZero).hom ≫ f ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫
        (CochainComplex.shiftFunctorObjXIso ((single C (ComplexShape.up ℤ) 0).obj G)
          1 (-1) 0 (by omega)).inv) := by
      rw [CochainComplex.shiftFunctor_map_f',
        show ((single C (ComplexShape.up ℤ) 0).map f).f (-1 + 1) =
          ((single C (ComplexShape.up ℤ) 0).map f).f 0 from rfl, single_map_f_self]
      simp [Preadditive.neg_comp, Preadditive.comp_neg]
    have h5 : (mkHomToSingle ((doubleXIso₀ d upIntRelNegOneZero).hom ≫ f) hf ≫
        ((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by decide)).inv.app G).f (-1) =
      (doubleXIso₀ d upIntRelNegOneZero).hom ≫ f ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫
        (CochainComplex.shiftFunctorObjXIso ((single C (ComplexShape.up ℤ) 0).obj G)
          1 (-1) 0 (by omega)).inv := by
      simp [CochainComplex.singleFunctors, singleObjXSelf, singleObjXIsoOfEq,
        CochainComplex.shiftFunctorObjXIso]
    exact h5.trans ((neg_neg _).symm.trans (congrArg Neg.neg h4.symm))
  · exact (show IsZero (((single C (ComplexShape.up ℤ) 0).obj G).X (n + 1)) from
      isZero_single_obj_X _ _ _ _ (by omega)).eq_of_tgt _ _

variable [HasDerivedCategory.{w} C]

/-- The shift isomorphism of the single functors into the derived category, in terms of that of
the single functors into cochain complexes. -/
theorem singleFunctors_shiftIso_inv_app :
    ((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by decide)).inv.app G =
      DerivedCategory.Q.map
          (((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by decide)).inv.app G) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single C (ComplexShape.up ℤ) 0).obj G) := by
  simp [DerivedCategory.singleFunctors, SingleFunctors.postcomp]

/-- **The class of the chain map given by `f` in degree `-1` is minus the class of `f`.** In the
derived category of an abelian category, the chain map `double d ⟶ G[1]` that is `f` in degree
`-1` is minus the class `P.proj ≫ f[1]` of `f` for the two-term structure `ofDoubleNegOne d`. -/
theorem Q_map_mkHomToSingle_comp (f : X₀ ⟶ G)
    (hf : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i (-1) →
      (double d upIntRelNegOneZero).d i (-1) ≫ ((doubleXIso₀ d upIntRelNegOneZero).hom ≫ f) = 0) :
    DerivedCategory.Q.map (mkHomToSingle ((doubleXIso₀ d upIntRelNegOneZero).hom ≫ f) hf) ≫
        ((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by decide)).inv.app G =
      -((ofDoubleNegOne d).conormalExtClass G f) := by
  rw [singleFunctors_shiftIso_inv_app, ← Category.assoc, ← Functor.map_comp,
    mkHomToSingle_comp_shiftIso_inv, Functor.map_neg, Preadditive.neg_comp]
  congr 1
  have e2 := DerivedCategory.Q.commShiftIso_hom_naturality
    ((single C (ComplexShape.up ℤ) 0).map f) (1 : ℤ)
  rw [Functor.map_comp]
  erw [Functor.map_comp]
  rw [Category.assoc, Category.assoc]
  erw [e2]
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

/-- The class `P.proj ≫ f[1]` of `ofDoubleNegOne d` is additive in `f`. -/
theorem ofDoubleNegOne_conormalExtClass_add (f g : X₀ ⟶ G) :
    (ofDoubleNegOne d).conormalExtClass G (f + g) =
      (ofDoubleNegOne d).conormalExtClass G f + (ofDoubleNegOne d).conormalExtClass G g := by
  have h : (DerivedCategory.singleFunctor C 0).map (f + g) =
      (DerivedCategory.singleFunctor C 0).map f + (DerivedCategory.singleFunctor C 0).map g :=
    (DerivedCategory.singleFunctor C 0).map_add
  exact (congrArg (fun k => (ofDoubleNegOne d).proj ≫ k⟦(1 : ℤ)⟧') h).trans
    ((congrArg (fun k => (ofDoubleNegOne d).proj ≫ k)
      ((shiftFunctor (DerivedCategory C) (1 : ℤ)).map_add)).trans
      (Preadditive.comp_add _ _ _ _ _ _))

end AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra AlgebraicGeometry.RingedSpaceThickening

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]
  (A B : Sheaf J CommRingCat.{max w u v}) (a : A ⟶ B)
  (E : Cᵒᵖ ⥤ Type (max w u v)) (α : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]
  [HasSheafify J AddCommGrpCat.{max w u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  [HasDerivedCategory.{t}
    (_root_.SheafOfModules.{max w u v} (Stacks.SheafOfModules.Tensor.ringSheaf B))]
  (G : _root_.SheafOfModules.{max w u v} (Stacks.SheafOfModules.Tensor.ringSheaf B))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The first Ext class of a conormal homomorphism `f : I/I² ⟶ G` is minus its class for the
two-term structure `ofDoubleNegOne` of `NL(α)`. -/
theorem presentationConormalExtClass_eq_neg
    (f : (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).X₁ ⟶ G) :
    presentationConormalExtClass.{v, u, w, t} J A B a E α G f =
      -((NaiveCotangentTwoTerm.ofDoubleNegOne
        (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).f).conormalExtClass G f) :=
  NaiveCotangentTwoTerm.Q_map_mkHomToSingle_comp _ G f _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The first Ext class of a conormal homomorphism vanishes exactly when the homomorphism
factors through the differential.** For a locally surjective polynomial presentation `α`, the
class of `f : I/I² ⟶ G` in `Ext¹_B(NL(α), G)` is zero if and only if `f` is the composite of
`I/I² ⟶ Ω_{A[E]/A} ⊗ B` with a homomorphism `Ω_{A[E]/A} ⊗ B ⟶ G`. -/
theorem presentationConormalExtClass_eq_zero_iff
    (f : (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).X₁ ⟶ G) :
    presentationConormalExtClass.{v, u, w, t} J A B a E α G f = 0 ↔
      ∃ θ : (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).X₂ ⟶ G,
        (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).f ≫ θ = f := by
  refine Iff.trans ?_ (NaiveCotangentTwoTerm.conormalExtClass_ofDouble_eq_zero_iff
    (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).f upIntRelNegOneZero G f)
  rw [presentationConormalExtClass_eq_neg]
  exact neg_eq_zero

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The first Ext class of a conormal homomorphism is additive in the homomorphism. -/
theorem presentationConormalExtClass_add
    (f g : (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).X₁ ⟶ G) :
    presentationConormalExtClass.{v, u, w, t} J A B a E α G (f + g) =
      presentationConormalExtClass.{v, u, w, t} J A B a E α G f +
        presentationConormalExtClass.{v, u, w, t} J A B a E α G g := by
  rw [presentationConormalExtClass_eq_neg.{t, w, v, u} J A B a E α G (f + g),
    presentationConormalExtClass_eq_neg.{t, w, v, u} J A B a E α G f,
    presentationConormalExtClass_eq_neg.{t, w, v, u} J A B a E α G g,
    NaiveCotangentTwoTerm.ofDoubleNegOne_conormalExtClass_add]
  exact neg_add _ _

end Stacks.SheafOfModules

end
