module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.RestrictionComparisonCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChange

/-!
# A system of locally given derived objects from a global one

Situation 0D67 is packaged as `Stacks.DerivedGlueing.LocallyGiven`, and every statement about
glueing takes such a system as an argument.  This file exhibits one: for a ringed space `X` and
an object `K` of the derived category of `X`, the collection of *all* open subsets, carrying the
restrictions of `K`, is a system of locally given derived objects.

## Main definitions

* `Stacks.DerivedGlueing.mapDerivedCategoryComp`: for exact functors `F`, `G`, `H` and an
  isomorphism `F ⋙ G ≅ H`, the induced isomorphism
  `H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`, lifted from the
  corresponding isomorphism on complexes.
* `Stacks.DerivedGlueing.locallyGivenOfGlobal`: the system of locally given derived objects
  obtained by restricting a single global object to the members of a collection of opens.
* `Stacks.DerivedGlueing.locallyGivenOfTop`: that system for the collection of all opens.

## Main results

* `Stacks.DerivedGlueing.isIso_openModuleRestrictionComparison`: the comparison of restriction in
  two steps with direct restriction is an isomorphism.
* `Stacks.DerivedGlueing.mapDerivedCategoryComp_factors`: the coherence that the field
  `restrictionCompFactors` of `Stacks.DerivedGlueing.LocallyGiven` asks for, proved once for
  `Stacks.DerivedGlueing.mapDerivedCategoryComp`.

## Implementation notes

The comparison `openModuleRestrictionComparison` for `W ≤ V ≤ U` is the counit of `j_! ⊣ j^*` on
the middle open `V`, evaluated at an extension by zero from `U` and then restricted to `W`.  That
counit is *not* invertible at such an argument — the extension by zero from `U` has nonzero
stalks on `U ∖ V` — but it becomes invertible after restriction to `W ≤ V`, because `j_V^*` of
the counit is invertible by the triangle identity and restriction to `W` only sees stalks inside
`V`.  This is `Stacks.DerivedGlueing.isIso_jStar_map_counit_of_le`.

The field `restrictionCompFactors` is the defining equation of a transformation lifted through
the localization functor, so `Stacks.DerivedGlueing.mapDerivedCategoryComp` is built as a single
`CategoryTheory.Localization.liftNatIso` whose complex-level datum is exactly the composite
appearing in that field; the coherence is then `CategoryTheory.Localization.liftNatTrans_app`
followed by two cancellations.  Building the comparison instead as a composite of
`Stacks.DerivedGlueing.mapDerivedCategoryCompIso` with
`Stacks.DerivedGlueing.mapDerivedCategoryCongr` would leave the same equation to be proved
through two liftings instead of one.

The collection of the system is arbitrary: the restriction of `K` to each of its members is
prescribed, the transition isomorphisms are the comparisons of restriction, and the cocycle
condition is their associativity,
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`.  That associativity is a theorem
about a system, so the restriction half of the system is written down first, with the empty
collection, as `Stacks.DerivedGlueing.restrictionDatum`; the systems of interest reuse its
fields.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

/-! ### A square of isomorphisms -/

/-- In a square of isomorphisms `a ≫ b = c ≫ d`, the inverse of `a` is `b ≫ d⁻¹ ≫ c⁻¹`. -/
theorem Iso.inv_eq_of_sq {D : Type u₁} [Category.{v₁} D] {w x y z : D} (a : w ≅ x) (b : x ≅ y)
    (c : w ≅ z) (d : z ≅ y) (h : a.hom ≫ b.hom = c.hom ≫ d.hom) :
    a.inv = b.hom ≫ d.inv ≫ c.inv := by
  refine (cancel_epi a.hom).mp ?_
  rw [a.hom_inv_id, ← Category.assoc, h]
  simp

/-! ### A lifted comparison of the functors induced on derived categories -/

section Generic

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : C₁ ⥤ C₃) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (θ : F ⋙ G ≅ H)

/-- The comparison of the two routes from complexes over `C₁` to the derived category of `C₃`:
apply `F` degreewise, localize and apply the functor induced by `G`, or apply `H` degreewise and
localize. -/
def mapDerivedCategoryCompFactorsIso :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory ≅
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
            (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ))
            DerivedCategory.Q ≪≫
          Functor.isoWhiskerRight (NatIso.mapHomologicalComplex θ (ComplexShape.up ℤ))
            DerivedCategory.Q

/-- **The functor induced by `H` on derived categories is the composite of those induced by `F`
and `G`**, for an isomorphism `θ : F ⋙ G ≅ H` of exact functors.  This is the lifting through the
localization functor of `Stacks.DerivedGlueing.mapDerivedCategoryCompFactorsIso`. -/
def mapDerivedCategoryComp : H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory)
    H.mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (mapDerivedCategoryCompFactorsIso F G H θ).symm

/-- The identification of the two readings of a composite prolongation is the identity in the
inverse direction too, the prolongation acting degreewise. -/
@[simp]
theorem mapHomologicalComplexCompIso_refl_inv_app {V₁ V₂ V₃ : Type*} [Category V₁] [Category V₂]
    [Category V₃] [Preadditive V₁] [Preadditive V₂] [Preadditive V₃] {ι : Type*}
    (F' : V₁ ⥤ V₂) (G' : V₂ ⥤ V₃) [F'.Additive] [G'.Additive] (c : ComplexShape ι)
    (C : HomologicalComplex V₁ c) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).inv.app C = 𝟙 _ := by
  ext n
  simp

/-- The chosen lifting of the degreewise prolongation of an exact functor through the localization
functor is `CategoryTheory.Functor.mapDerivedCategory`, and the comparison is
`CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
@[simp]
theorem lifting_iso_mapDerivedCategory :
    Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
        (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        F.mapDerivedCategory =
      F.mapDerivedCategoryFactors :=
  rfl

/-- **The defining equation of `Stacks.DerivedGlueing.mapDerivedCategoryComp`.** Read at the class
of a complex and transported along the comparisons of each induced functor with the degreewise
one, the comparison of `H.mapDerivedCategory` with the composite is `θ` applied degreewise. -/
theorem mapDerivedCategoryComp_factors
    (C : HomologicalComplex C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryComp F G H θ).hom.app (DerivedCategory.Q.obj C) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app C) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.up ℤ)).hom.app C) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app C) =
      H.mapDerivedCategoryFactors.hom.app C := by
  have hθ : (NatIso.mapHomologicalComplex θ (ComplexShape.up ℤ)).inv.app C ≫
      (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app C = 𝟙 _ :=
    (NatIso.mapHomologicalComplex θ (ComplexShape.up ℤ)).inv_hom_id_app C
  simp only [Functor.comp_obj, mapDerivedCategoryComp, mapDerivedCategoryCompFactorsIso,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Localization.liftNatIso_hom, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Localization.liftNatTrans_app, lifting_iso_mapDerivedCategory, NatTrans.comp_app,
    Functor.whiskerRight_app, mapHomologicalComplexCompIso_refl_inv_app,
    CategoryTheory.Functor.map_id, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp,
    Localization.Lifting.compRight_iso, Category.assoc, mapHomologicalComplexCompIso_refl_hom_app,
    cancelIso, Iso.inv_hom_id_app_assoc]
  rw [← DerivedCategory.Q.map_comp, hθ, DerivedCategory.Q.map_id, Category.comp_id]

end Generic

/-! ### Restriction to a smaller open inverts the counit of extension by zero -/

/-- **Restriction to `W` makes the counit of `j_{V,!} ⊣ j_V^*` invertible, for `W ≤ V`.** The
counit itself need not be invertible: that asks for vanishing stalks off `V`.  But `j_V^*` of it
is invertible by the triangle identity, hence it is invertible on every stalk inside `V`, hence
on every stalk inside `W`, hence after restriction to `W`. -/
theorem isIso_jStar_map_counit_of_le {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W V : Opens Z) (hWV : W ≤ V)
    (G : SheafOfModules.{u} O) :
    IsIso ((jStar W O).map ((jShriekAdjunction V O).counit.app G)) :=
  Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_of_stalk_isIso O W _ fun z hz =>
    Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_stalk_of_isIso_jStar_map O V _
      (Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_counit O V G) z (hWV hz)

/-- **The comparison of restriction in two steps with direct restriction is an isomorphism.** Its
component at a sheaf of modules is the counit of extension by zero on the middle open, restricted
to the smallest of the three, which is
`Stacks.DerivedGlueing.isIso_jStar_map_counit_of_le`. -/
instance isIso_openModuleRestrictionComparison (X : RingedSpace.{u, u})
    (W V U : Opens X.carrier) (hWV : W ≤ V) (hVU : V ≤ U) :
    IsIso (openModuleRestrictionComparison X W V U hWV hVU) :=
  (NatTrans.isIso_iff_isIso_app _).mpr fun _ =>
    isIso_jStar_map_counit_of_le (underlyingRingSheaf X) W V hWV _

/-! ### The system of locally given derived objects attached to a global object -/

section Datum

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- **The restriction half of Situation 0D67 on a ringed space**, with the empty collection of
opens: restriction on derived categories is the functor induced by restriction of complexes of
sheaves of modules, and the comparison of restriction in two steps with direct restriction is
induced by `Stacks.DerivedGlueing.openModuleRestrictionComparison`.

This carries no objects, and is a system only in a degenerate sense: it prescribes nothing, so
every statement about the members of its collection holds of it vacuously. -/
def restrictionDatum : LocallyGiven X where
  opens := ∅
  restriction V U hVU := (openModuleRestriction X V U hVU).mapDerivedCategory
  restrictionFactors V U hVU := (openModuleRestriction X V U hVU).mapDerivedCategoryFactors
  restrictionComp W V U hWV hVU :=
    mapDerivedCategoryComp _ _ _ (asIso (openModuleRestrictionComparison X W V U hWV hVU))
  restrictionCompFactors W V U hWV hVU C :=
    mapDerivedCategoryComp_factors _ _ _
      (asIso (openModuleRestrictionComparison X W V U hWV hVU)) C
  obj _ hU := hU.elim
  rho _ _ _ hU _ := hU.elim
  cocycle _ _ _ _ _ hU _ _ := hU.elim

/-- Restriction in `restrictionDatum X` is the functor on derived categories induced by
restriction of complexes of sheaves of modules. -/
@[simp]
theorem restrictionDatum_restriction (V U : Opens X.carrier) (hVU : V ≤ U) :
    (restrictionDatum X).restriction V U hVU =
      (openModuleRestriction X V U hVU).mapDerivedCategory :=
  rfl

/-- **Situation 0D67 from a single global object.** Let `X` be a ringed space, let `𝒞` be any
collection of open subsets of `X` and let `K` be an object of the derived category of `X`.
Prescribing, on each member of `𝒞`, the restriction of `K` to it, and taking for the transition
isomorphisms the comparisons of restriction in two steps with direct restriction, is a system of
locally given derived objects.

The cocycle condition is the associativity of those comparisons,
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`, along `W ≤ V ≤ U ≤ ⊤`. -/
def locallyGivenOfGlobal (𝒞 : Set (Opens X.carrier)) (K : OpenDerivedCategory X ⊤) :
    LocallyGiven X :=
  { restrictionDatum X with
    opens := 𝒞
    obj := fun U _ => ((restrictionDatum X).restriction U ⊤ le_top).obj K
    rho := fun V U hVU _ _ =>
      (((restrictionDatum X).restrictionComp V U ⊤ hVU le_top).app K).symm
    cocycle := fun W V U hWV hVU _ _ _ =>
      Iso.inv_eq_of_sq
        (((restrictionDatum X).restrictionComp W U ⊤ (hWV.trans hVU) le_top).app K)
        (((restrictionDatum X).restrictionComp W V U hWV hVU).app
          (((restrictionDatum X).restriction U ⊤ le_top).obj K))
        (((restrictionDatum X).restrictionComp W V ⊤ hWV le_top).app K)
        (((restrictionDatum X).restriction W V hWV).mapIso
          (((restrictionDatum X).restrictionComp V U ⊤ hVU le_top).app K))
        ((restrictionDatum X).restrictionComp_pentagon W V U ⊤ hWV hVU le_top K) }

/-- The collection of opens of `locallyGivenOfGlobal X 𝒞 K` is `𝒞`. -/
@[simp]
theorem locallyGivenOfGlobal_opens (𝒞 : Set (Opens X.carrier))
    (K : OpenDerivedCategory X ⊤) :
    (locallyGivenOfGlobal X 𝒞 K).opens = 𝒞 :=
  rfl

/-- Restriction in `locallyGivenOfGlobal X 𝒞 K` is the functor on derived categories induced by
restriction of complexes of sheaves of modules. -/
@[simp]
theorem locallyGivenOfGlobal_restriction (𝒞 : Set (Opens X.carrier))
    (K : OpenDerivedCategory X ⊤) (V U : Opens X.carrier) (hVU : V ≤ U) :
    (locallyGivenOfGlobal X 𝒞 K).restriction V U hVU =
      (openModuleRestriction X V U hVU).mapDerivedCategory :=
  rfl

/-- The object of `locallyGivenOfGlobal X 𝒞 K` on a member `U` of `𝒞` is the restriction of `K`
to `U`. -/
@[simp]
theorem locallyGivenOfGlobal_obj (𝒞 : Set (Opens X.carrier)) (K : OpenDerivedCategory X ⊤)
    (U : Opens X.carrier) (hU : U ∈ 𝒞) :
    (locallyGivenOfGlobal X 𝒞 K).obj U hU =
      (openModuleRestriction X U ⊤ le_top).mapDerivedCategory.obj K :=
  rfl

/-- **Situation 0D67 from a single global object, on every open subset.** The collection is all of
`Opens X`, so `⊤` belongs to it and the system is covered by a single member. -/
def locallyGivenOfTop (K : OpenDerivedCategory X ⊤) : LocallyGiven X :=
  locallyGivenOfGlobal X Set.univ K

/-- The collection of opens of `locallyGivenOfTop X K` is all of `Opens X`. -/
@[simp]
theorem locallyGivenOfTop_opens (K : OpenDerivedCategory X ⊤) :
    (locallyGivenOfTop X K).opens = Set.univ :=
  rfl

/-- The whole space `⊤` is a member of the collection of opens of `locallyGivenOfTop X K`. -/
theorem top_mem_locallyGivenOfTop_opens (K : OpenDerivedCategory X ⊤) :
    (⊤ : Opens X.carrier) ∈ (locallyGivenOfTop X K).opens :=
  Set.mem_univ _

end Datum

end Stacks.DerivedGlueing

end
