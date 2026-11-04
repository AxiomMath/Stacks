module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

/-!
# The cohomology of a proper scheme over `k̄` as `Ext` out of the constant sheaf

Let `X` be proper over a field `k`, so that `X` is its own compactification
(`AlgebraicGeometry.CompactificationOf.ofProper`), and let `k̄` be an extension of `k`. For a
sheaf `K` of `Λ`-modules on `X_étale` the canonical `RΓ_c(X_k̄, K)` of
`Stacks.EtaleCohomology.compactSupportFrobeniusFunctor` is `RΓ(X_k̄, K|_{X_k̄})`, and

`Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ_{X_k̄}, K|_{X_k̄})`.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.ofProper`: a proper scheme as its own compactification.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroIdIso`: `(𝟙 X)_! ≅ 𝟭`.
* `Stacks.EtaleCohomology.compactSupportCohomologyExtNatIso`:
  `Hⁱ_c(X_k̄, -) ≅ Ext^i(Λ_{X_k̄}, -|_{X_k̄})` as functors, for `X` proper.
* `Stacks.EtaleCohomology.extConstantAddEquivCompactSupportCohomology`:
  `Hⁱ_c(X_k̄, K) ≃+ Ext^i(Λ_{X_k̄}, K|_{X_k̄})` for `X` proper.

## References

* [Stacks Project, Tag 03V8](https://stacks.math.columbia.edu/tag/03V8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace AlgebraicGeometry

/-- **A proper scheme is its own compactification**: the identity of `X` is an open immersion and
the structure morphism `f : X ⟶ Y` is proper. -/
def CompactificationOf.ofProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CompactificationOf (Over.mk f) :=
  ⟨StructuredArrow.mk (𝟙 (Over.mk f)), ⟨inferInstanceAs (IsOpenImmersion (𝟙 X)),
    inferInstanceAs (IsProper f)⟩⟩

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Extension by zero along the identity is the identity**, on étale sheaves of
`Λ`-modules. -/
def etaleModuleExtensionByZeroIdIso (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    etaleModuleExtensionByZero.{u, r} Λ (𝟙 X) ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq (etaleModuleExtensionByZeroAdj.{u, r} Λ (𝟙 X))
    (Adjunction.id.ofNatIsoRight ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (𝟙 X)).symm ≪≫
      etaleModuleInverseImageIdIso Λ X).symm)

section Proper

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- A functor preserving zero morphisms commutes with placing an object in degree zero, as a
natural isomorphism of functors into bounded below complexes. -/
def singlePlusFunctorCompMapCochainComplexPlusIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (G : A ⥤ B) [G.PreservesZeroMorphisms] :
    Stacks.DerivedIndexing.singlePlusFunctor A 0 ⋙ G.mapCochainComplexPlus ≅
      G ⋙ Stacks.DerivedIndexing.singlePlusFunctor B 0 :=
  NatIso.ofComponents (fun M => mapCochainComplexPlusSinglePlusIso G M) fun {M M'} φ => by
    refine ObjectProperty.hom_ext _ ?_
    exact (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.naturality φ

/-- **`Hⁱ_c(X_k̄, -) ≅ Ext^i(Λ_{X_k̄}, -|_{X_k̄})` as functors**, for a proper `X` over `k`
compactified by itself, on sheaves of `Λ`-modules on `X_étale` placed in degree zero. -/
def compactSupportCohomologyExtNatIso (i : ℕ) :
    Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0 ⋙
        compactSupportFrobeniusFunctor.{u, 0} Λ f (CompactificationOf.ofProper f) kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar) ⋙
        extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i :=
  let E := etaleModuleExtensionByZero.{u, 0} Λ (𝟙 X)
  let I := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)
  let π := pullback.snd f (specAlgebraMap k kbar)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i ⋙
    forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let e₂ := rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, 0} Λ π)
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar))
    (etaleModuleGlobalSectionsDirectImageIso π Λ)
  let SX := Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0
  let SY := Stacks.DerivedIndexing.singlePlusFunctor
    (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)) 0
  let D := DerivedCategory.Plus.Q ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ π ⋙
    etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)) ⋙ H
  let c₀ : SX ⋙ compactSupportFrobeniusFunctor.{u, 0} Λ f (CompactificationOf.ofProper f) kbar ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      (SX ⋙ E.mapCochainComplexPlus) ⋙ I.mapCochainComplexPlus ⋙ D := Iso.refl _
  let c₁ : (SX ⋙ E.mapCochainComplexPlus) ⋙ I.mapCochainComplexPlus ⋙ D ≅
      E ⋙ (SX ⋙ I.mapCochainComplexPlus) ⋙ D :=
    Functor.isoWhiskerRight (singlePlusFunctorCompMapCochainComplexPlusIso E) _
  let c₂ : E ⋙ (SX ⋙ I.mapCochainComplexPlus) ⋙ D ≅ E ⋙ I ⋙ SY ⋙ D :=
    Functor.isoWhiskerLeft E (Functor.isoWhiskerRight
      (singlePlusFunctorCompMapCochainComplexPlusIso I) D)
  let c₃ : SY ⋙ D ≅ (etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk f) kbar)).rightDerivedPlus (i : ℤ) ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
    Functor.isoWhiskerLeft (SY ⋙ DerivedCategory.Plus.Q) (Functor.isoWhiskerRight e₂.symm H)
  let c₄ : ((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk f) kbar)).rightDerivedPlus (i : ℤ) ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i :=
    Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)) i).symm _ ≪≫
      (Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived Λ
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology i).symm
  let c₅ : E ⋙ I ⋙ extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i ≅
      I ⋙ extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i :=
    Functor.isoWhiskerRight (etaleModuleExtensionByZeroIdIso Λ X) _ ≪≫ Functor.leftUnitor _
  c₀ ≪≫ c₁ ≪≫ c₂ ≪≫ Functor.isoWhiskerLeft (E ⋙ I) (c₃ ≪≫ c₄) ≪≫ c₅

/-- **`Hⁱ_c(X_k̄, K) ≃+ Ext^i(Λ_{X_k̄}, K|_{X_k̄})`** for a proper `X` over `k`, compactified by
itself, and a sheaf of `Λ`-modules `K` on `X_étale` placed in degree zero. -/
def extConstantAddEquivCompactSupportCohomology (K : EtaleModules.{u, 0} Λ X) (i : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f (CompactificationOf.ofProper f) kbar).obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K)) ≃+
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).obj K) :=
  ((compactSupportCohomologyExtNatIso Λ f kbar i).app K).addCommGroupIsoToAddEquiv

/-- **Naturality of `Hⁱ_c(X_k̄, -) ≃+ Ext^i(Λ_{X_k̄}, -|_{X_k̄})`**: a morphism `φ : K ⟶ K'` acts
on the right by composition with the restriction of `φ` to `X_k̄`. -/
theorem extConstantAddEquivCompactSupportCohomology_map {K K' : EtaleModules.{u, 0} Λ X}
    (φ : K ⟶ K') (i : ℕ)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f (CompactificationOf.ofProper f) kbar).obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K))) :
    extConstantAddEquivCompactSupportCohomology Λ f kbar K' i
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          ((compactSupportFrobeniusFunctor.{u, 0} Λ f (CompactificationOf.ofProper f) kbar).map
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map φ)) x) =
      (extConstantAddEquivCompactSupportCohomology Λ f kbar K i x).comp
        (Ext.mk₀ ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk f) kbar)).map φ)) (add_zero i) :=
  congrArg (fun g => g.hom x) ((compactSupportCohomologyExtNatIso Λ f kbar i).hom.naturality φ)

end Proper

end Stacks.EtaleCohomology

end
