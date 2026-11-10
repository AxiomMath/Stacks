module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidualNaturality

/-!
# Naturality of the double dual isomorphism on an algebraic space

Let `X` be an algebraic space.  For a perfect object `K` of `D(𝒪_X)` the canonical map
`K ⟶ (K^∨)^∨` is an isomorphism (Stacks 08JJ,
`AlgebraicGeometry.Space.smallEtaleDerivedBidualIso`).  This file proves that this isomorphism is
natural: for a morphism `u : K ⟶ K'` of perfect objects, `u^∨∨ ≫ (K'^∨∨ ≅ K') = (K^∨∨ ≅ K) ≫ u`.

The proof is on the equi-universe model `AlgebraicGeometry.Space.smallEtaleModelRingedSite`,
through which the derived dual of `X` is defined: the identification
`AlgebraicGeometry.Space.smallEtaleModelDerivedDualIso` of the dual of `X` with the dual of the
model is natural, and the canonical map to the double dual of the model is natural
(`AlgebraicGeometry.RingedSite.derivedBidual_naturality`).

## Main results

* `AlgebraicGeometry.Space.smallEtaleModelDerivedDualIso_hom_naturality`.
* `AlgebraicGeometry.Space.smallEtaleDerivedBidualIso_hom_naturality`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The derived dual of a morphism of `D(𝒪_X)`: `u : K ⟶ K'` gives `u^∨ : K'^∨ ⟶ K^∨`. -/
abbrev smallEtaleDerivedDualMap
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : K ⟶ K') : smallEtaleDerivedDual B S hS X K' ⟶ smallEtaleDerivedDual B S hS X K :=
  ((smallEtaleDerivedSheafHom B S hS X).map u.op).app
    ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))

/-- The dual of a morphism of `D(𝒪_X)` is the dual of its image on the model, brought back. -/
theorem smallEtaleDerivedDualMap_eq
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : K ⟶ K') :
    smallEtaleDerivedDualMap B S hS X u =
      (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
        (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map u).op).app
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))))) :=
  rfl

/-! ### Transport along an equivalence -/

section Transport

variable {C D : Type*} [Category C] [Category D] (e : C ≌ D) (H : Dᵒᵖ ⥤ D ⥤ D) (O : C) (OM : D)
  (s : e.functor.obj O ≅ OM)

/-- The identification `e(A^∨) ≅ (eA)^∨` for the dual on `C` transported from the dual `H(-, OM)`
on `D` along the equivalence `e`. -/
def transportedDualIso (A : C) :
    e.functor.obj (e.inverse.obj ((H.obj (op (e.functor.obj A))).obj (e.functor.obj O))) ≅
      (H.obj (op (e.functor.obj A))).obj OM :=
  e.counitIso.app _ ≪≫ (H.obj (op (e.functor.obj A))).mapIso s

/-- The transported identification of duals is natural. -/
theorem transportedDualIso_hom_naturality {A A' : C} (u : A ⟶ A') :
    e.functor.map (e.inverse.map ((H.map (e.functor.map u).op).app (e.functor.obj O))) ≫
        (transportedDualIso e H O OM s A).hom =
      (transportedDualIso e H O OM s A').hom ≫ (H.map (e.functor.map u).op).app OM := by
  simp only [transportedDualIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.comp_map, e.counitIso.hom.naturality, Category.assoc,
    Category.assoc, Functor.id_map]
  congr 1
  exact ((H.map (e.functor.map u).op).naturality s.hom).symm

/-- **A natural double dual on `D` transports to a natural double dual isomorphism on `C`.** -/
theorem transportedBidualIso_hom_naturality
    (b : ∀ A : D, A ⟶ (H.obj (op ((H.obj (op A)).obj OM))).obj OM)
    (hb : ∀ {A A' : D} (f : A ⟶ A'),
      f ≫ b A' = b A ≫ (H.map ((H.map f.op).app OM).op).app OM)
    {K K' : C} (u : K ⟶ K') [IsIso (b (e.functor.obj K))] [IsIso (b (e.functor.obj K'))] :
    e.inverse.map ((H.map (e.functor.map (e.inverse.map ((H.map (e.functor.map u).op).app
        (e.functor.obj O)))).op).app (e.functor.obj O)) ≫
      (e.fullyFaithfulFunctor.preimageIso
        (transportedDualIso e H O OM s
            (e.inverse.obj ((H.obj (op (e.functor.obj K'))).obj (e.functor.obj O))) ≪≫
          (H.mapIso (transportedDualIso e H O OM s K').op.symm).app OM ≪≫
          (asIso (b (e.functor.obj K'))).symm)).hom =
    (e.fullyFaithfulFunctor.preimageIso
        (transportedDualIso e H O OM s
            (e.inverse.obj ((H.obj (op (e.functor.obj K))).obj (e.functor.obj O))) ≪≫
          (H.mapIso (transportedDualIso e H O OM s K).op.symm).app OM ≪≫
          (asIso (b (e.functor.obj K))).symm)).hom ≫ u := by
  let dM : ∀ {A A' : D}, (A ⟶ A') → ((H.obj (op A')).obj OM ⟶ (H.obj (op A)).obj OM) :=
    fun a => (H.map a.op).app OM
  have hdM : ∀ {A A' A'' : D} (a : A ⟶ A') (a' : A' ⟶ A''), dM (a ≫ a') = dM a' ≫ dM a :=
    fun a a' => by simp only [dM, op_comp, Functor.map_comp, NatTrans.comp_app]
  let DI := transportedDualIso e H O OM s
  let du := e.inverse.map ((H.map (e.functor.map u).op).app (e.functor.obj O))
  have hEu : e.functor.map du = (DI K').hom ≫ dM (e.functor.map u) ≫ (DI K).inv := by
    rw [← Category.assoc, ← transportedDualIso_hom_naturality e H O OM s u, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  apply e.functor.map_injective
  simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, Iso.op_inv, Category.assoc]
  change _ ≫ (DI _).hom ≫ dM (DI K').inv ≫ _ = (DI _).hom ≫ dM (DI K).inv ≫ _ ≫ _
  rw [← Category.assoc, transportedDualIso_hom_naturality e H O OM s du, Category.assoc]
  change (DI _).hom ≫ dM (e.functor.map du) ≫ dM (DI K').inv ≫ _ = _
  rw [← Category.assoc (dM _), ← hdM, hEu, Iso.inv_hom_id_assoc, hdM]
  simp only [Category.assoc]
  congr 2
  have h := hb (e.functor.map u)
  rw [IsIso.eq_inv_comp, ← Category.assoc]
  change (b (e.functor.obj K) ≫ (H.map ((H.map (e.functor.map u).op).app OM).op).app OM) ≫ _ = _
  rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Transport

/-- **The identification of the dual of `X` with the dual of the model is natural.** -/
theorem smallEtaleModelDerivedDualIso_hom_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : K ⟶ K') :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.map
        (smallEtaleDerivedDualMap B S hS X u) ≫
      (smallEtaleModelDerivedDualIso B S hS X K).hom =
    (smallEtaleModelDerivedDualIso B S hS X K').hom ≫
      ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.map u).op).app
          (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) :=
  transportedDualIso_hom_naturality (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))
    (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedStructureSheafIso B S hS X) u

/-- **The double dual isomorphism of a perfect object is natural.**  For a morphism `u : K ⟶ K'`
of perfect objects of `D(𝒪_X)`, `u^∨∨ ≫ (K'^∨∨ ≅ K') = (K^∨∨ ≅ K) ≫ u`. -/
theorem smallEtaleDerivedBidualIso_hom_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) K)
    (hK' : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) K') (u : K ⟶ K') :
    smallEtaleDerivedDualMap B S hS X (smallEtaleDerivedDualMap B S hS X u) ≫
        (smallEtaleDerivedBidualIso B S hS X K' hK').hom =
      (smallEtaleDerivedBidualIso B S hS X K hK).hom ≫ u := by
  have := RingedSite.isIso_derivedBidual_of_isPerfect
    (smallEtaleModelRingedSite B S hS X.1 X.2)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct _) _
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X K hK)
  have := RingedSite.isIso_derivedBidual_of_isPerfect
    (smallEtaleModelRingedSite B S hS X.1 X.2)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct _) _
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X K' hK')
  exact transportedBidualIso_hom_naturality (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))
    (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedStructureSheafIso B S hS X)
    (RingedSite.derivedBidual (smallEtaleModelRingedSite B S hS X.1 X.2)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2)))
    (fun f => RingedSite.derivedBidual_naturality _ _ f) u

end AlgebraicGeometry.Space

end
