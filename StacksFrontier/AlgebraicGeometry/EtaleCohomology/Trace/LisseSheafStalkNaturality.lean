module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalk
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkFunctoriality

/-!
# The stalks of a lisse sheaf are natural in the module

For a finite `Λ`-module `P` with a continuous action of `π₁(X, x̄)` and a path `t` from a geometric
point `s̄` to `x̄`, the stalk of the lisse sheaf `ℱ_P` at `s̄` is `P`
(`Stacks.EtaleCohomology.lisseSheafStalkAddEquiv`,
`Stacks.EtaleCohomology.lisseEtaleSheafFiberIso`). This file shows that this identification is
natural in `P`: it is built from the comparison of the stalks of a sheaf of modules and of its
underlying abelian sheaf (`Stacks.EtaleCohomology.etaleStalkForget₂Iso_hom_naturality`), the
natural identification of the stalk of a finite locally constant abelian sheaf with the
`π₁`-module of Tag 0DV5 (2), and the counit of the equivalence of Tag 0DV5 (3).

## Main results

* `Stacks.EtaleCohomology.lisseSheafStalkAddEquiv_naturality`.
* `Stacks.EtaleCohomology.lisseEtaleSheafFiberIso_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]

/-- The morphism of the finite locally constant abelian sheaves underlying `ℱ_P ⟶ ℱ_{P'}`. -/
abbrev lisseSheafAbelianMap
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (g : P ⟶ P') : lisseSheafAbelian B X x Λ P ⟶ lisseSheafAbelian B X x Λ P' :=
  ((Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence
    (SmallEtale.topology B X.1 X.2) Λ).functor.map
      ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.map
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.map g))).hom.app
    (SingleObj.star Λ)

/-- On underlying groups, the functor of Tag 0DV5 (3) is the canonical functor of Tag 0DV5 (2)
applied to the underlying abelian sheaves. -/
theorem finiteTypeLocallyConstantModuleSheafEquivalence_functor_map_apply
    {M M' : ObjectProperty.FullSubcategory
      (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)}
    (m : M ⟶ M') (v) :
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.map m).hom.hom.hom.hom.hom
        v =
      ((((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor ⋙
        ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map
          (((Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence
            (SmallEtale.topology B X.1 X.2) Λ).functor.map
              ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.map m)).hom.app
            (SingleObj.star Λ)))).hom v :=
  rfl

/-- **The stalk of `ℱ_P` at `s̄` is `P`, naturally in `P`.** -/
theorem lisseSheafStalkAddEquiv_naturality {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (g : P ⟶ P')
    (y : (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj) :
    lisseSheafStalkAddEquiv B X x Λ t P'
        (((etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).map
          ((lisseSheaf B X x Λ).map g).hom).hom y) =
      g.hom.hom.hom.hom.hom (lisseSheafStalkAddEquiv B X x Λ t P y) := by
  have s1 : lisseSheafForget₂StalkAddEquiv B X x Λ s P'
      (((etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).map
        ((lisseSheaf B X x Λ).map g).hom).hom y) =
      ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        (lisseSheafAbelianMap B X x Λ g).hom).hom (lisseSheafForget₂StalkAddEquiv B X x Λ s P y) :=
    ConcreteCategory.congr_hom
      (etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s Λ ((lisseSheaf B X x Λ).map g)) y
  have s2 : lisseSheafAbelianStalkAddEquiv B X x Λ t P'
      (((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        (lisseSheafAbelianMap B X x Λ g).hom).hom (lisseSheafForget₂StalkAddEquiv B X x Λ s P y)) =
      ((((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor ⋙
        ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map
          (lisseSheafAbelianMap B X x Λ g))).hom
        (lisseSheafAbelianStalkAddEquiv B X x Λ t P
          (lisseSheafForget₂StalkAddEquiv B X x Λ s P y)) := by
    have h := ConcreteCategory.congr_hom
      ((finiteLocallyConstantAbelianStalkIso B X t).hom.naturality (lisseSheafAbelianMap B X x Λ g))
      (lisseSheafForget₂StalkAddEquiv B X x Λ s P y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h
  have s3 : finiteTypeContinuousModuleAddEquiv Λ
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app P')
      (((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.map
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.map
          g)).hom.hom.hom.hom.hom
        (lisseSheafAbelianStalkAddEquiv B X x Λ t P
          (lisseSheafForget₂StalkAddEquiv B X x Λ s P y))) =
      g.hom.hom.hom.hom.hom (finiteTypeContinuousModuleAddEquiv Λ
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app P)
        (lisseSheafAbelianStalkAddEquiv B X x Λ t P
          (lisseSheafForget₂StalkAddEquiv B X x Λ s P y))) :=
    congrArg (fun φ => φ.hom.hom.hom.hom.hom
      (lisseSheafAbelianStalkAddEquiv B X x Λ t P (lisseSheafForget₂StalkAddEquiv B X x Λ s P y)))
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.hom.naturality g)
  rw [finiteTypeLocallyConstantModuleSheafEquivalence_functor_map_apply] at s3
  simp only [lisseSheafStalkAddEquiv, AddEquiv.trans_apply]
  rw [s1, s2, s3]

section ZMod

variable (m : ℕ) [NeZero m]

omit [NeZero m] in
/-- An additive equivalence of `ℤ/m`-modules natural for two maps is natural as an isomorphism of
modules. -/
theorem zmodModuleCatIsoOfAddEquiv_naturality {M N M' N' : ModuleCat.{u + 1} (ZMod m)}
    (e : M ≃+ N) (e' : M' ≃+ N') (f : M ⟶ M') (g : N ⟶ N')
    (h : ∀ v, e' (f.hom v) = g.hom (e v)) :
    f ≫ (zmodModuleCatIsoOfAddEquiv m e').hom = (zmodModuleCatIsoOfAddEquiv m e).hom ≫ g := by
  ext v
  exact h v

/-- **The stalk of `ℱ_P` on Mathlib's small étale site is `P`, naturally in `P`.** -/
theorem lisseEtaleSheafFiberIso_hom_naturality {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup X.1 x)}
    (g : P ⟶ P') :
    (Scheme.pointSmallEtale s.hom).sheafFiber.map ((lisseEtaleSheaf B X x (ZMod m)).map g) ≫
        (lisseEtaleSheafFiberIso B X x m t P').hom =
      (lisseEtaleSheafFiberIso B X x m t P).hom ≫ g.hom.hom.hom.hom := by
  have h1 : (Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod m))).functor.map
          ((lisseSheaf B X x (ZMod m)).map g)) ≫
        (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod m) s).hom.app
          ((lisseSheaf B X x (ZMod m)).obj P') =
      (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod m) s).hom.app
          ((lisseSheaf B X x (ZMod m)).obj P) ≫
        (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} (ZMod m))).map
          ((lisseSheaf B X x (ZMod m)).map g).hom :=
    (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod m) s).hom.naturality
      ((lisseSheaf B X x (ZMod m)).map g)
  have h2 := zmodModuleCatIsoOfAddEquiv_naturality m (lisseSheafStalkAddEquiv B X x (ZMod m) t P)
    (lisseSheafStalkAddEquiv B X x (ZMod m) t P')
    ((etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} (ZMod m))).map
      ((lisseSheaf B X x (ZMod m)).map g).hom)
    g.hom.hom.hom.hom (lisseSheafStalkAddEquiv_naturality B X x (ZMod m) t g)
  change (Scheme.pointSmallEtale s.hom).sheafFiber.map
      ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod m))).functor.map
        ((lisseSheaf B X x (ZMod m)).map g)) ≫
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod m) s).hom.app
          ((lisseSheaf B X x (ZMod m)).obj P') ≫
        (zmodModuleCatIsoOfAddEquiv m (lisseSheafStalkAddEquiv B X x (ZMod m) t P')).hom) =
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod m) s).hom.app
          ((lisseSheaf B X x (ZMod m)).obj P) ≫
        (zmodModuleCatIsoOfAddEquiv m (lisseSheafStalkAddEquiv B X x (ZMod m) t P)).hom) ≫
      g.hom.hom.hom.hom
  rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc]

end ZMod

end Stacks.EtaleCohomology

end
