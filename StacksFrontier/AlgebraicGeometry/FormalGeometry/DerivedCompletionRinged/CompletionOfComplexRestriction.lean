module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionUnitRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalCechReflector

/-!
# The completion map of a complex restricts to the completion map of the restriction

Let `(𝒞, 𝒪)` be a ringed site, `a : K ⟶ 𝒪` a map of complexes of `𝒪`-modules and `U` an object
of `𝒞`. The completion map `E ⟶ R𝑆heafHom_𝒪(K, E)` attached to `a`,
`AlgebraicGeometry.RingedSite.completionUnitOfComplex`, restricts to the completion map
`E|_U ⟶ R𝑆heafHom_{𝒪_U}(K|_U, E|_U)` attached to the restriction `a|_U : K|_U ⟶ 𝒪_U`, under the
isomorphism `AlgebraicGeometry.RingedSite.completionFunctorOfComplexOverIso` of
[Stacks, Tag 08JB].

This is `AlgebraicGeometry.RingedSite.overFunctor_map_completionUnit_comp` of
`CompletionUnitRestriction.lean` with the extended alternating Čech complex replaced by an
arbitrary complex, and the proof is the same: the completion map is the identification
`E = R𝑆heafHom(𝒪, E)` followed by the map `a` induces, the first commutes with restriction by
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_restrict`, and the second by the
first-variable naturality of [Stacks, Tag 08JB].

## Main results

* `RingedSite.overFunctor_map_completionUnitOfComplex_comp`: the compatibility.
* `RingedSite.completionUnitOfComplex_comp_completionFunctorOfComplexOverIso_inv`: the same
  with the isomorphism inverted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] (U : X.C)
  {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (a : K ⟶ structureSheafComplex X)

/-- The restriction of `Q(a)`, read through the identifications of the restricted classes with
the classes of the restricted complexes, is `Q(a|_U)`: the naturality of
`AlgebraicGeometry.RingedSite.restrictionComparison`. -/
theorem overFunctor_mapDerivedCategory_map_Q_map_comp :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          (DerivedCategory.Q.map a) ≫ (derivedStructureSheafRestrictIso X U).hom =
      (restrictionComparison X U K).hom ≫
        DerivedCategory.Q.map (restrictStructureSheafMap X U a) := by
  have h : DerivedCategory.Q.map
          (((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map a) ≫
        DerivedCategory.Q.map (restrictStructureSheafComplexOverIso X U).hom =
      DerivedCategory.Q.map (restrictStructureSheafMap X U a) :=
    (DerivedCategory.Q.map_comp _ _).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg
    (fun morphism ↦ morphism ≫ DerivedCategory.Q.map (restrictStructureSheafComplexOverIso X U).hom)
      (restrictionComparison_naturality X U a)).trans ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (fun morphism ↦ (restrictionComparison X U K).hom ≫ morphism) h)

/-- `overFunctor_mapDerivedCategory_map_Q_map_comp` with both identifications inverted. -/
theorem restrictionComparison_inv_comp_overFunctor_map_Q_map :
    (restrictionComparison X U K).inv ≫
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          (DerivedCategory.Q.map a) =
      DerivedCategory.Q.map (restrictStructureSheafMap X U a) ≫
        (derivedStructureSheafRestrictIso X U).inv :=
  inv_comp_eq_comp_inv_of _ _ (overFunctor_mapDerivedCategory_map_Q_map_comp X U a)

variable [HasSheafify (X.over U).J AddCommGrpCat.{u}]

/-- **The completion map of `a` restricts to the completion map of `a|_U`.** Under the
isomorphism `R𝑆heafHom_𝒪(K, E)|_U ≅ R𝑆heafHom_{𝒪_U}(K|_U, E|_U)` of [Stacks, Tag 08JB], the
restriction of the completion map `E ⟶ R𝑆heafHom_𝒪(K, E)` attached to `a` is the completion map
attached to `a|_U`. -/
theorem overFunctor_map_completionUnitOfComplex_comp
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          ((completionUnitOfComplex X a).app E) ≫
        (completionFunctorOfComplexOverIso X U K E).hom =
      (completionUnitOfComplex (X.over U) (restrictStructureSheafMap X U a)).app
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) := by
  have hii : ((derivedHomRestriction X U).iso
            (DerivedCategory.Q.obj (structureSheafComplex X)) E).hom ≫
        ((derivedSheafHomBifunctor (X.over U)).map
            (derivedStructureSheafRestrictIso X U).inv.op).app
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          (derivedStructureSheafHomIso X E).hom ≫
        (@Iso.inv _ _ _ _ (derivedStructureSheafHomIso (X.over U)
          ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E))) :=
    comp_eq_comp_inv_of_comp_comp _ (derivedStructureSheafHomIso_restrict X U E)
  have haug : ((derivedSheafHomBifunctor (X.over U)).map
            ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
              (DerivedCategory.Q.map a)).op).app
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) ≫
        ((derivedSheafHomBifunctor (X.over U)).map
            (restrictionComparison X U K).inv.op).app
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) =
      ((derivedSheafHomBifunctor (X.over U)).map
            (derivedStructureSheafRestrictIso X U).inv.op).app
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) ≫
        ((derivedSheafHomBifunctor (X.over U)).map
            (DerivedCategory.Q.map (restrictStructureSheafMap X U a)).op).app
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp,
      restrictionComparison_inv_comp_overFunctor_map_Q_map X U a]
  change (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          ((derivedStructureSheafHomIso X E).inv ≫
            ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map a).op).app E) ≫
        (((derivedHomRestriction X U).iso (DerivedCategory.Q.obj K) E).hom ≫
          ((derivedSheafHomBifunctor (X.over U)).map
              (restrictionComparison X U K).inv.op).app
            ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)) =
      (@Iso.inv _ _ _ _ (derivedStructureSheafHomIso (X.over U)
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E))) ≫
        ((derivedSheafHomBifunctor (X.over U)).map
            (DerivedCategory.Q.map (restrictStructureSheafMap X U a)).op).app
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% ((derivedHomRestriction X U).natural_left (DerivedCategory.Q.map a)),
    haug, reassoc_of% hii, Iso.inv_hom_id_map_assoc]

/-- `overFunctor_map_completionUnitOfComplex_comp` with the isomorphism inverted: the completion
map of `a|_U`, followed by the identification
`R𝑆heafHom_{𝒪_U}(K|_U, E|_U) ≅ R𝑆heafHom_𝒪(K, E)|_U`, is the restriction of the completion map
of `a`. -/
theorem completionUnitOfComplex_comp_completionFunctorOfComplexOverIso_inv
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (completionUnitOfComplex (X.over U) (restrictStructureSheafMap X U a)).app
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) ≫
        (completionFunctorOfComplexOverIso X U K E).inv =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        ((completionUnitOfComplex X a).app E) :=
  (Iso.comp_inv_eq (completionFunctorOfComplexOverIso X U K E)).2
    (overFunctor_map_completionUnitOfComplex_comp X U a E).symm

end AlgebraicGeometry.RingedSite

end
