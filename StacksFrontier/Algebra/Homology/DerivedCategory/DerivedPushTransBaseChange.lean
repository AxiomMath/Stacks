module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusPasting
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.FaithfulConservativePlus
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Derived transformations along an exact functor, and base change

Let `Φ₀ : 𝒞₀ ⥤ ℳ` and `Φ : 𝒞 ⥤ ℳ` be additive functors, `P : 𝒞₀ ⥤ 𝒞` exact, and
`τ : Φ₀ ⟶ P ⋙ Φ` a natural transformation ("restriction of global sections along `P`").  Its
derived form is the natural transformation

`derivedPushTrans P τ : RΦ₀ ⟶ P̄ ⋙ RΦ`

of functors `D⁺(𝒞₀) ⥤ D⁺(ℳ)`, characterised on complexes by `derivedPushTrans_fac_app`.

The main result, `derivedPushTrans_baseChange`, compares two such derived transformations along
exact "forgetful" functors `U₀ : 𝒞₀ ⥤ 𝒞₀'`, `U : 𝒞 ⥤ 𝒞'`, `V : ℳ ⥤ ℳ'`: given a second
transformation `σ : Ψ₀ ⟶ P' ⋙ Ψ` downstairs and base change squares `β₀ : Φ₀ ⋙ V ⟶ U₀ ⋙ Ψ₀`,
`β : Φ ⋙ V ⟶ U ⋙ Ψ` and `e : P ⋙ U ≅ U₀ ⋙ P'` compatible with `τ` and `σ`, the derived square
commutes.  Together with `rightAcyclic_of_rightAcyclic_baseChange` — an object is acyclic for `F`
when its image is acyclic for `F'`, along a faithful exact `β` — this is what lets a statement
about derived functors of `A`-linear functors be checked on underlying abelian groups.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChangePlus.derivedPushTrans` — the derived transformation.
* `Stacks.Cohomology.DerivedBaseChangePlus.derivedCompTrans` — the transformation
  `P̄ ⋙ Ū ⟶ Ū₀ ⋙ P̄'` induced by `P ⋙ U ⟶ U₀ ⋙ P'`.

## Main results

* `Stacks.Cohomology.DerivedBaseChangePlus.derivedPushTrans_baseChange` — the derived square
  commutes.
* `Stacks.Cohomology.DerivedBaseChangePlus.rightAcyclic_of_rightAcyclic_baseChange` — acyclicity
  descends along a base change square with faithful exact target functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.Cohomology.DerivedBaseChangePlus

/-! ### The degreewise action of an isomorphism -/

section IsoHelper

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]

/-- The degreewise action of an isomorphism of additive functors is invertible. -/
instance isIso_mapHomotopyCategoryPlusNatTrans_app {G G' : A ⥤ B} [G.Additive] [G'.Additive]
    (φ : G ⟶ G') [IsIso φ] (K : HomotopyCategory.Plus A) :
    IsIso ((Functor.mapHomotopyCategoryPlusNatTrans φ).app K) :=
  ⟨(Functor.mapHomotopyCategoryPlusNatTrans (inv φ)).app K, by
    rw [← Functor.mapHomotopyCategoryPlusNatTrans_comp_app, IsIso.hom_inv_id]
    apply (HomotopyCategory.Plus.ι B).map_injective
    change (NatTrans.mapHomotopyCategory (𝟙 G) (ComplexShape.up ℤ)).app K.obj = 𝟙 _
    rw [NatTrans.mapHomotopyCategory_id]
    rfl, by
    rw [← Functor.mapHomotopyCategoryPlusNatTrans_comp_app, IsIso.inv_hom_id]
    apply (HomotopyCategory.Plus.ι B).map_injective
    change (NatTrans.mapHomotopyCategory (𝟙 G') (ComplexShape.up ℤ)).app K.obj = 𝟙 _
    rw [NatTrans.mapHomotopyCategory_id]
    rfl⟩

end IsoHelper

/-! ### The derived transformation -/

section Push

variable {C₀ C M : Type*} [Category* C₀] [Category* C] [Category* M]
  [Abelian C₀] [Abelian C] [Abelian M]
  [HasDerivedCategory C₀] [HasDerivedCategory C] [HasDerivedCategory M]
  [EnoughInjectives C₀] [EnoughInjectives C]
  {Φ₀ : C₀ ⥤ M} {Φ : C ⥤ M} [Φ₀.Additive] [Φ.Additive]
  (P : C₀ ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- The comparison out of which `derivedPushTrans` is derived: on a bounded below complex `K`,
`τ` applied degreewise, then the unit `Φ(P K) ⟶ RΦ(P K)`, then the identification of `P K` with
`P̄ K` in the derived category. -/
def derivedPushComparison (τ : Φ₀ ⟶ P ⋙ Φ) :
    Φ₀.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ P.mapDerivedCategoryPlus ⋙ Φ.rightDerivedFunctorPlus :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans τ) DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl _)).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft P.mapHomotopyCategoryPlus Φ.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight P.mapDerivedCategoryPlusFactorsh.inv Φ.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- The degreewise action of `τ : Φ₀ ⟶ P ⋙ Φ` on a bounded below complex, with its target spelled
through the induced functors of `P` and `Φ`. -/
abbrev pushHmap (τ : Φ₀ ⟶ P ⋙ Φ) (K : HomotopyCategory.Plus C₀) :
    Φ₀.mapHomotopyCategoryPlus.obj K ⟶
      Φ.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K) :=
  (Functor.mapHomotopyCategoryPlusNatTrans τ).app K

omit [EnoughInjectives C₀] in
/-- `derivedPushComparison` at a complex. -/
theorem derivedPushComparison_app (τ : Φ₀ ⟶ P ⋙ Φ) (K : HomotopyCategory.Plus C₀) :
    (derivedPushComparison P τ).app K =
      DerivedCategory.Plus.Qh.map (pushHmap P τ K) ≫
        Φ.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj K) ≫
          Φ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [derivedPushComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    qh_map_mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.comp_obj, Category.id_comp,
    Category.comp_id]

/-- **The derived transformation `RΦ₀ ⟶ P̄ ⋙ RΦ` of `τ : Φ₀ ⟶ P ⋙ Φ`**, for an exact `P`: the
natural transformation out of the right derived functor `RΦ₀` restricting to
`derivedPushComparison` on complexes. -/
def derivedPushTrans (τ : Φ₀ ⟶ P ⋙ Φ) :
    Φ₀.rightDerivedFunctorPlus ⟶ P.mapDerivedCategoryPlus ⋙ Φ.rightDerivedFunctorPlus :=
  Φ₀.rightDerivedFunctorPlus.rightDerivedDesc Φ₀.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C₀) _ (derivedPushComparison P τ)

/-- **The characterisation of `derivedPushTrans` on complexes.** -/
theorem derivedPushTrans_fac_app (τ : Φ₀ ⟶ P ⋙ Φ) (K : HomotopyCategory.Plus C₀) :
    Φ₀.rightDerivedFunctorPlusUnith.app K ≫
        (derivedPushTrans P τ).app (DerivedCategory.Plus.Qh.obj K) =
      (derivedPushComparison P τ).app K :=
  Φ₀.rightDerivedFunctorPlus.rightDerived_fac_app Φ₀.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C₀) _ (derivedPushComparison P τ) K

end Push

/-! ### The transformation of induced functors of a square of exact functors -/

section CompTrans

variable {C₀ C C₀' C' : Type*} [Category* C₀] [Category* C] [Category* C₀'] [Category* C']
  [Abelian C₀] [Abelian C] [Abelian C₀'] [Abelian C']
  [HasDerivedCategory C₀] [HasDerivedCategory C] [HasDerivedCategory C₀'] [HasDerivedCategory C']
  (P : C₀ ⥤ C) (U : C ⥤ C') (U₀ : C₀ ⥤ C₀') (P' : C₀' ⥤ C')
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [P'.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']

/-- **The transformation `P̄ ⋙ Ū ⟶ Ū₀ ⋙ P̄'` of induced functors** of a transformation
`e : P ⋙ U ⟶ U₀ ⋙ P'` of exact functors: `e` applied degreewise, lifted along the
localization. -/
def derivedCompTrans (e : P ⋙ U ⟶ U₀ ⋙ P') :
    P.mapDerivedCategoryPlus ⋙ U.mapDerivedCategoryPlus ⟶
      U₀.mapDerivedCategoryPlus ⋙ P'.mapDerivedCategoryPlus :=
  Localization.liftNatTrans DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C₀)
    ((P.mapHomotopyCategoryPlus ⋙ U.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh)
    ((U₀.mapHomotopyCategoryPlus ⋙ P'.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh)
    (P.mapDerivedCategoryPlus ⋙ U.mapDerivedCategoryPlus)
    (U₀.mapDerivedCategoryPlus ⋙ P'.mapDerivedCategoryPlus)
    (Functor.whiskerRight ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ U))).hom ≫
      Functor.mapHomotopyCategoryPlusNatTrans e ≫
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (U₀ ⋙ P'))).inv)
      DerivedCategory.Plus.Qh)

/-- The degreewise action of `e : P ⋙ U ⟶ U₀ ⋙ P'` on a bounded below complex, with source and
target spelled through the induced functors of the four sides. -/
abbrev compHmap (e : P ⋙ U ⟶ U₀ ⋙ P') (K : HomotopyCategory.Plus C₀) :
    U.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K) ⟶
      P'.mapHomotopyCategoryPlus.obj (U₀.mapHomotopyCategoryPlus.obj K) :=
  (Functor.mapHomotopyCategoryPlusNatTrans e).app K

/-- `derivedCompTrans` at a complex. -/
theorem derivedCompTrans_app (e : P ⋙ U ⟶ U₀ ⋙ P') (K : HomotopyCategory.Plus C₀) :
    (derivedCompTrans P U U₀ P' e).app (DerivedCategory.Plus.Qh.obj K) =
      U.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        U.mapDerivedCategoryPlusFactorsh.hom.app (P.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map (compHmap P U U₀ P' e K) ≫
        P'.mapDerivedCategoryPlusFactorsh.inv.app (U₀.mapHomotopyCategoryPlus.obj K) ≫
        P'.mapDerivedCategoryPlus.map (U₀.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  rw [derivedCompTrans, Localization.liftNatTrans_app]
  change (Functor.mapDerivedCategoryPlusCompFactorsh P U).hom.app K ≫
      DerivedCategory.Plus.Qh.map (((Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (P ⋙ U))).hom ≫ Functor.mapHomotopyCategoryPlusNatTrans e ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (U₀ ⋙ P'))).inv).app K) ≫
      (Functor.mapDerivedCategoryPlusCompFactorsh U₀ P').inv.app K = _
  simp only [Functor.mapDerivedCategoryPlusCompFactorsh, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, qh_map_mapHomotopyCategoryPlusCompIso_refl_inv_app,
    qh_map_mapHomotopyCategoryPlusCompIso_refl_hom_app, Category.assoc, Category.id_comp,
    Category.comp_id]

/-- The transformation induced by an isomorphism `P ⋙ U ≅ U₀ ⋙ P'` is invertible. -/
theorem isIso_derivedCompTrans_app (e : P ⋙ U ⟶ U₀ ⋙ P') [IsIso e]
    (X : DerivedCategory.Plus C₀) : IsIso ((derivedCompTrans P U U₀ P' e).app X) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Plus.Qh.objObjPreimageIso X),
    derivedCompTrans_app]
  have : IsIso (compHmap P U U₀ P' e (DerivedCategory.Plus.Qh.objPreimage X)) :=
    isIso_mapHomotopyCategoryPlusNatTrans_app e _
  infer_instance

end CompTrans

/-! ### The derived square commutes -/

section Square

variable {C₀ C M C₀' C' M' : Type*} [Category* C₀] [Category* C] [Category* M]
  [Category* C₀'] [Category* C'] [Category* M']
  [Abelian C₀] [Abelian C] [Abelian M] [Abelian C₀'] [Abelian C'] [Abelian M']
  [HasDerivedCategory C₀] [HasDerivedCategory C] [HasDerivedCategory M]
  [HasDerivedCategory C₀'] [HasDerivedCategory C'] [HasDerivedCategory M']
  [EnoughInjectives C₀] [EnoughInjectives C] [EnoughInjectives C₀'] [EnoughInjectives C']
  {Φ₀ : C₀ ⥤ M} {Φ : C ⥤ M} {Ψ₀ : C₀' ⥤ M'} {Ψ : C' ⥤ M'}
  [Φ₀.Additive] [Φ.Additive] [Ψ₀.Additive] [Ψ.Additive]
  (P : C₀ ⥤ C) (U : C ⥤ C') (U₀ : C₀ ⥤ C₀') (P' : C₀' ⥤ C') (V : M ⥤ M')
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [P'.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
  [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (τ : Φ₀ ⟶ P ⋙ Φ) (σ : Ψ₀ ⟶ P' ⋙ Ψ) (β₀ : Φ₀ ⋙ V ⟶ U₀ ⋙ Ψ₀) (β : Φ ⋙ V ⟶ U ⋙ Ψ)
  (e : P ⋙ U ⟶ U₀ ⋙ P')

omit [HasDerivedCategory C₀] [HasDerivedCategory C] [HasDerivedCategory M]
  [HasDerivedCategory C₀'] [HasDerivedCategory C'] [HasDerivedCategory M']
  [EnoughInjectives C₀] [EnoughInjectives C] [EnoughInjectives C₀'] [EnoughInjectives C']
  [PreservesFiniteLimits P] [PreservesFiniteColimits P] [PreservesFiniteLimits U]
  [PreservesFiniteColimits U] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits P'] [PreservesFiniteColimits P'] [PreservesFiniteLimits V]
  [PreservesFiniteColimits V] in
/-- The homotopy-level form of the compatibility of the four underived squares. -/
lemma hmap_square
    (h : ∀ X : C₀, V.map (τ.app X) ≫ β.app (P.obj X) ≫ Ψ.map (e.app X) =
      β₀.app X ≫ σ.app (U₀.obj X))
    (K : HomotopyCategory.Plus C₀) :
    V.mapHomotopyCategoryPlus.map (pushHmap P τ K) ≫ hmap V U β (P.mapHomotopyCategoryPlus.obj K) ≫
        Ψ.mapHomotopyCategoryPlus.map (compHmap P U U₀ P' e K) =
      hmap V U₀ β₀ K ≫ pushHmap P' σ (U₀.mapHomotopyCategoryPlus.obj K) := by
  have hnat : (Functor.whiskerRight τ V ≫ Functor.whiskerLeft P β ≫ Functor.whiskerRight e Ψ :
      Φ₀ ⋙ V ⟶ (U₀ ⋙ P') ⋙ Ψ) = β₀ ≫ Functor.whiskerLeft U₀ σ := by
    ext X
    simpa using h X
  have := congrArg (fun t => (Functor.mapHomotopyCategoryPlusNatTrans t).app K) hnat
  simp only [Functor.mapHomotopyCategoryPlusNatTrans_comp_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerLeft_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerRight_app] at this
  exact this

/-- **The derived square commutes.**  For transformations `τ : Φ₀ ⟶ P ⋙ Φ` and
`σ : Ψ₀ ⟶ P' ⋙ Ψ`, base change squares `β₀ : Φ₀ ⋙ V ⟶ U₀ ⋙ Ψ₀` and `β : Φ ⋙ V ⟶ U ⋙ Ψ`, and
`e : P ⋙ U ⟶ U₀ ⋙ P'`, compatible in the sense that `V τ` followed by `β` and `Ψ e` is `β₀`
followed by `σ`, the derived transformation of `τ` followed by the base change map of `β` and by
`RΨ` of the transformation induced by `e` is the base change map of `β₀` followed by the derived
transformation of `σ`, at every object of `D⁺(𝒞₀)`. -/
theorem derivedPushTrans_baseChange
    (h : ∀ X : C₀, V.map (τ.app X) ≫ β.app (P.obj X) ≫ Ψ.map (e.app X) =
      β₀.app X ≫ σ.app (U₀.obj X))
    (X : DerivedCategory.Plus C₀) :
    V.mapDerivedCategoryPlus.map ((derivedPushTrans P τ).app X) ≫
        (derivedBaseChangePlus Φ Ψ V U β).app (P.mapDerivedCategoryPlus.obj X) ≫
        Ψ.rightDerivedFunctorPlus.map ((derivedCompTrans P U U₀ P' e).app X) =
      (derivedBaseChangePlus Φ₀ Ψ₀ V U₀ β₀).app X ≫
        (derivedPushTrans P' σ).app (U₀.mapDerivedCategoryPlus.obj X) := by
  let lhs : Φ₀.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ⟶
      U₀.mapDerivedCategoryPlus ⋙ P'.mapDerivedCategoryPlus ⋙ Ψ.rightDerivedFunctorPlus :=
    { app X := V.mapDerivedCategoryPlus.map ((derivedPushTrans P τ).app X) ≫
        (derivedBaseChangePlus Φ Ψ V U β).app (P.mapDerivedCategoryPlus.obj X) ≫
        Ψ.rightDerivedFunctorPlus.map ((derivedCompTrans P U U₀ P' e).app X)
      naturality X Y f := by
        have h1 := (derivedPushTrans P τ).naturality f
        have h2 := (derivedBaseChangePlus Φ Ψ V U β).naturality (P.mapDerivedCategoryPlus.map f)
        have h3 := (derivedCompTrans P U U₀ P' e).naturality f
        simp only [Functor.comp_obj, Functor.comp_map] at h1 h2 h3 ⊢
        rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, reassoc_of% h2,
          ← Functor.map_comp, h3, Functor.map_comp]
        simp only [Category.assoc] }
  let rhs : Φ₀.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ⟶
      U₀.mapDerivedCategoryPlus ⋙ P'.mapDerivedCategoryPlus ⋙ Ψ.rightDerivedFunctorPlus :=
    derivedBaseChangePlus Φ₀ Ψ₀ V U₀ β₀ ≫
      Functor.whiskerLeft U₀.mapDerivedCategoryPlus (derivedPushTrans P' σ)
  suffices hlr : lhs = rhs from NatTrans.congr_app hlr X
  refine (Φ₀.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus).rightDerived_ext
    (derivedBaseChangePlusUnit Φ₀ V) (HomotopyCategory.Plus.quasiIso C₀) _ _ _
    (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, lhs, rhs,
    Functor.comp_obj]
  have l1 := derivedPushTrans_fac_app P τ K
  rw [derivedPushComparison_app] at l1
  have l2 : V.mapDerivedCategoryPlus.map
        (Φ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
      (derivedBaseChangePlus Φ Ψ V U β).app
        (P.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (derivedBaseChangePlus Φ Ψ V U β).app
          (DerivedCategory.Plus.Qh.obj (P.mapHomotopyCategoryPlus.obj K)) ≫
        Ψ.rightDerivedFunctorPlus.map
          (U.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K)) :=
    (derivedBaseChangePlus Φ Ψ V U β).naturality (P.mapDerivedCategoryPlusFactorsh.inv.app K)
  have l3 := derivedBaseChangePlus_fac Φ Ψ V U β (P.mapHomotopyCategoryPlus.obj K)
  rw [derivedBaseChangePlusAux_app'] at l3
  have l4 : V.mapDerivedCategoryPlus.map
        (DerivedCategory.Plus.Qh.map (pushHmap P τ K)) ≫
      V.mapDerivedCategoryPlusFactorsh.hom.app
        (Φ.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)) =
      V.mapDerivedCategoryPlusFactorsh.hom.app (Φ₀.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map (V.mapHomotopyCategoryPlus.map (pushHmap P τ K)) :=
    V.mapDerivedCategoryPlusFactorsh.hom.naturality (pushHmap P τ K)
  have l5 : Ψ.rightDerivedFunctorPlusUnith.app
        (U.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)) ≫
      Ψ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (compHmap P U U₀ P' e K)) =
      DerivedCategory.Plus.Qh.map (Ψ.mapHomotopyCategoryPlus.map (compHmap P U U₀ P' e K)) ≫
        Ψ.rightDerivedFunctorPlusUnith.app
          (P'.mapHomotopyCategoryPlus.obj (U₀.mapHomotopyCategoryPlus.obj K)) :=
    (Ψ.rightDerivedFunctorPlusUnith.naturality (compHmap P U U₀ P' e K)).symm
  have l6 : Ψ.rightDerivedFunctorPlus.map
        (U.mapDerivedCategoryPlusFactorsh.inv.app (P.mapHomotopyCategoryPlus.obj K)) ≫
      Ψ.rightDerivedFunctorPlus.map
        (U.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
      Ψ.rightDerivedFunctorPlus.map
        ((derivedCompTrans P U U₀ P' e).app (DerivedCategory.Plus.Qh.obj K)) =
      Ψ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (compHmap P U U₀ P' e K)) ≫
        Ψ.rightDerivedFunctorPlus.map
          (P'.mapDerivedCategoryPlusFactorsh.inv.app (U₀.mapHomotopyCategoryPlus.obj K)) ≫
        Ψ.rightDerivedFunctorPlus.map
          (P'.mapDerivedCategoryPlus.map (U₀.mapDerivedCategoryPlusFactorsh.inv.app K)) := by
    simp only [← Functor.map_comp]
    congr 1
    rw [derivedCompTrans_app, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    refine Eq.trans (whisker_eq _ ?_) (Iso.inv_hom_id_app_assoc _ _ _)
    refine Eq.trans (eq_whisker (U.mapDerivedCategoryPlus.map_id _) _) ?_
    exact Category.id_comp _
  have r1 := derivedBaseChangePlus_fac Φ₀ Ψ₀ V U₀ β₀ K
  rw [derivedBaseChangePlusAux_app'] at r1
  have r2 : Ψ₀.rightDerivedFunctorPlus.map (U₀.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
      (derivedPushTrans P' σ).app
        (U₀.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (derivedPushTrans P' σ).app
          (DerivedCategory.Plus.Qh.obj (U₀.mapHomotopyCategoryPlus.obj K)) ≫
        Ψ.rightDerivedFunctorPlus.map
          (P'.mapDerivedCategoryPlus.map (U₀.mapDerivedCategoryPlusFactorsh.inv.app K)) :=
    (derivedPushTrans P' σ).naturality (U₀.mapDerivedCategoryPlusFactorsh.inv.app K)
  have r3 := derivedPushTrans_fac_app P' σ (U₀.mapHomotopyCategoryPlus.obj K)
  rw [derivedPushComparison_app] at r3
  have hsq := congrArg DerivedCategory.Plus.Qh.map (hmap_square P U U₀ P' V τ σ β₀ β e h K)
  simp only [Functor.map_comp] at hsq
  rw [← Functor.map_comp_assoc, l1]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% l2, reassoc_of% l3, reassoc_of% l4, l6, reassoc_of% l5, reassoc_of% r1, r2,
    reassoc_of% r3]
  simp only [← Category.assoc]
  congr 3
  simp only [Category.assoc]
  rw [hsq]

end Square

/-! ### Acyclicity along a base change square -/

section Acyclic

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [EnoughInjectives A] [EnoughInjectives A'] [EnoughInjectives B]
  (α : A ⥤ A') [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (β : B ⥤ B') [β.Additive] [PreservesFiniteLimits β] [PreservesFiniteColimits β] [β.Faithful]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]

/-- **Acyclicity descends along a base change square with faithful exact target functor.**  Let
`e : α ⋙ F' ≅ F ⋙ β` with `α`, `β` exact, `β` faithful, and `α` carrying injectives to objects
acyclic for `F'`.  An object `X` of `𝒜` whose image `α X` is acyclic for `F'` is acyclic for `F`:
the image under `β` of the unit of `RF` at `X[0]` is, up to isomorphisms, the unit of `RF'` at
`(α X)[0]`, and `β` is conservative on `D⁺`. -/
theorem rightAcyclic_of_rightAcyclic_baseChange (e : α ⋙ F' ≅ F ⋙ β)
    (hacyclic : ∀ I : A, Injective I → F'.rightAcyclic (α.obj I)) (X : A)
    (hX : F'.rightAcyclic (α.obj X)) : F.rightAcyclic X := by
  let K := (HomotopyCategory.Plus.singleFunctor A 0).obj X
  have hu : IsIso (F'.rightDerivedFunctorPlusUnith.app (α.mapHomotopyCategoryPlus.obj K)) :=
    (NatTrans.isIso_app_iff_of_iso _ (α.mapHomotopyCategoryPlusObjSingleIso 0 X)).2 hX
  have hb : IsIso ((derivedBaseChangePlus F F' β α e.inv).app (DerivedCategory.Plus.Qh.obj K)) := by
    rw [← derivedBaseChangePlusIso_inv α β F F' e hacyclic]
    infer_instance
  have hfac := derivedBaseChangePlus_fac F F' β α e.inv K
  rw [derivedBaseChangePlusAux_app'] at hfac
  have : IsIso (hmap β α e.inv K) := isIso_mapHomotopyCategoryPlusNatTrans_app e.inv K
  have : IsIso (β.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K)) := by
    have h' : IsIso (β.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        (derivedBaseChangePlus F F' β α e.inv).app (DerivedCategory.Plus.Qh.obj K)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((derivedBaseChangePlus F F' β α e.inv).app (DerivedCategory.Plus.Qh.obj K))
  exact Stacks.Cohomology.isIso_of_isIso_mapDerivedCategoryPlus_map_of_faithful β _ this

end Acyclic

end Stacks.Cohomology.DerivedBaseChangePlus

end
