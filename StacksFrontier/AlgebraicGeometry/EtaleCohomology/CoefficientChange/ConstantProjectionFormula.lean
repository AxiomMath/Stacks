module

public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ConstantProjectionDerived
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# The projection formula against constant coefficients on derived categories

Let `g : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring.  This file collects the
ingredients of the projection-formula map `Rg_*E ⊗^L_Λ M̲ ⟶ Rg_*(E ⊗^L_Λ M̲)`, natural in
`E ∈ D(X_étale, Λ)` and `M ∈ D(Λ)`.  On a complex `K` and a complex `N` whose constant sheaf
complexes are K-flat it is, after the unit `g_*K ⟶ Rg_*K`, the projection map of total complexes
`Tot(g_*K ⊗ c_Y N) ⟶ g_* Tot(K ⊗ c_X N)` followed by the unit of `Rg_*`
(`Stacks.EtaleCohomology.etaleModuleProjectionMapAux`).

## Main results

* `Stacks.EtaleCohomology.etaleModuleConstantDerivedTensor_isRightDerivedFunctor`.
* `Stacks.EtaleCohomology.etaleModuleConstantRestrictFullyFaithful`.
* `Stacks.EtaleCohomology.etaleModuleDerivedProjectionMap`: the projection-formula map.
* `Stacks.EtaleCohomology.etaleModuleDerivedProjectionMap_fac`: its value on complexes.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedProjectionMap`: it is an isomorphism
  ([Stacks, Remark 0GL6]).

## Implementation notes

`M ↦ Rg_*E ⊗^L M̲` is, uniformly in `M`, the right derived functor of `K ↦ g_*K ⊗^L M̲`
(the unit of `Rg_*` being invertible at K-injective complexes), so the map is first obtained by
the universal property of right derived functors on the complexes `N` with K-flat constant sheaf
complexes, and then descended along the localization
`constantSheafKFlatComplexes_isLocalization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the coefficient universe `u + 1`;
instance search would try to unify the coefficient universe `max (u + 1) r` with it and fail on
the universe constraint, so it is switched off here. -/
attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale

/- The instance proofs `F.Additive`, `(F.obj X).Additive` and `HasMapBifunctor` for the tensor
product over `Λ` are the named ones of `ModuleTensor.TensorBifunctorInstances`, stated as
`etaleModuleDerivedTensor` records them, so that every `derivedBifunctor (etaleModuleTensor Λ X)`
written here is the unfolding of `etaleModuleDerivedTensor Λ X` up to proofs of the same
propositions; with independently synthesized proofs the kernel compares the two by evaluating the
derived bifunctor, which is prohibitively slow. -/
attribute [local instance high] etaleModuleTensor_additive etaleModuleTensor_obj_additive
  etaleModuleTensor_hasTotal_mapBifunctor

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

open CochainComplex.KFlatBifunctor

/-- `E ↦ (N ↦ E ⊗^L c_Z N)`, with `N` among the complexes whose constant sheaf complexes are
K-flat. -/
abbrev etaleModuleConstantDerivedTensor (Z : Scheme.{u}) :
    DerivedCategory (EtaleModules.{u, r} Λ Z) ⥤
      (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory ⥤
        DerivedCategory (EtaleModules.{u, r} Λ Z) :=
  etaleModuleDerivedTensor.{u, r} Λ Z ⋙ (Functor.whiskeringLeft _ _ _).obj
    ((constantSheafKFlatComplexes.{u, r} Λ).ι ⋙ DerivedCategory.Q ⋙
      etaleModuleDerivedConstantSheaf.{u, r} Λ Z)

/-- `etaleModuleProjectionMapAux`, as a natural transformation in both variables. -/
def etaleModuleProjectionMapHomotopy :
    ((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ etaleModuleConstantDerivedTensor.{u, r} Λ Y ⟶
      DerivedCategory.Q ⋙ etaleModuleConstantDerivedTensor.{u, r} Λ X ⋙
        (Functor.whiskeringRight _ _ _).obj
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g) where
  app K :=
    { app N := etaleModuleProjectionMapAux Λ g K N
      naturality _ _ f := etaleModuleProjectionMapAux_naturality_right Λ g K f }
  naturality _ _ f :=
    NatTrans.ext (funext fun N => etaleModuleProjectionMapAux_naturality_left Λ g f N)



/-- `K ↦ g_*K ⊗^L -` inverts the quasi-isomorphisms between K-injective complexes, the unit
`g_*K ⟶ Rg_*K` being invertible on them. -/
theorem invertsQuasiIsoOfIsKInjective_etaleModuleConstantDerivedTensor :
    InvertsQuasiIsoOfIsKInjective
      (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ etaleModuleConstantDerivedTensor.{u, r} Λ Y) := by
  intro K L f hK hL hf
  have hu := (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).naturality f
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app Λ g K hK
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app Λ g L hL
  have : IsIso (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).map f) := by
    have e : ((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).map f =
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app K ≫
          (DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map f ≫
          inv ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app L) := by
      rw [← Category.assoc, ← hu, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have : IsIso (DerivedCategory.Q.map f) := Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso _ _) f ((HomologicalComplex.mem_quasiIso_iff _).2 hf)
    have : IsIso ((DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map f) :=
      by dsimp only [Functor.comp_map]; infer_instance
    rw [e]
    infer_instance
  exact Functor.map_isIso (etaleModuleConstantDerivedTensor.{u, r} Λ Y) _

/-- **`E ↦ (N ↦ Rg_*E ⊗^L c_Y N)` is the right derived functor of `K ↦ (N ↦ g_*K ⊗^L c_Y N)`**:
its unit is invertible at every K-injective complex. -/
instance etaleModuleConstantDerivedTensor_isRightDerivedFunctor :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
        etaleModuleConstantDerivedTensor.{u, r} Λ Y).IsRightDerivedFunctor
      (Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g)
          (etaleModuleConstantDerivedTensor.{u, r} Λ Y) ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIsoOfIsKInjective_etaleModuleConstantDerivedTensor Λ g)]
  intro K hK
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app Λ g K hK
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
  infer_instance

/-- The projection-formula map with its second variable restricted to the complexes whose
constant sheaf complexes are K-flat. -/
def etaleModuleProjectionMapRestricted :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
        etaleModuleConstantDerivedTensor.{u, r} Λ Y ⟶
      etaleModuleConstantDerivedTensor.{u, r} Λ X ⋙
        (Functor.whiskeringRight _ _ _).obj (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g) :=
  (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
      etaleModuleConstantDerivedTensor.{u, r} Λ Y).rightDerivedDesc
    (Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g)
      (etaleModuleConstantDerivedTensor.{u, r} Λ Y) ≫ (Functor.associator _ _ _).hom)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) _
    (etaleModuleProjectionMapHomotopy Λ g)



/-- Restriction of the second variable to the complexes with K-flat constant sheaf complexes is
fully faithful on bifunctors, `constantSheafKFlatComplexes` being a localization of `D(Λ)`. -/
def etaleModuleConstantRestrictFullyFaithful :
    ((Functor.whiskeringRight (DerivedCategory (EtaleModules.{u, r} Λ X)) _ _).obj
      ((Functor.whiskeringLeft _ _ (DerivedCategory (EtaleModules.{u, r} Λ Y))).obj
        ((constantSheafKFlatComplexes.{u, r} Λ).ι ⋙ DerivedCategory.Q))).FullyFaithful :=
  (Localization.fullyFaithfulWhiskeringLeft
    ((constantSheafKFlatComplexes.{u, r} Λ).ι ⋙ DerivedCategory.Q)
    (constantSheafKFlatComplexesQuasiIso.{u, r} Λ) _).whiskeringRight _

/-- **The projection-formula map against constant coefficients**,
`Rg_*E ⊗^L_Λ M̲ ⟶ Rg_*(E ⊗^L_Λ M̲)`, natural in `E ∈ D(X_étale, Λ)` and `M ∈ D(Λ)`. -/
def etaleModuleDerivedProjectionMap :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙ etaleModuleDerivedTensor.{u, r} Λ Y ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedConstantSheaf.{u, r} Λ Y) ⟶
      etaleModuleDerivedTensor.{u, r} Λ X ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedConstantSheaf.{u, r} Λ X) ⋙
          (Functor.whiskeringRight _ _ _).obj (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g) :=
  (etaleModuleConstantRestrictFullyFaithful Λ (X := X) (Y := Y)).preimage
    (X := etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙ etaleModuleDerivedTensor.{u, r} Λ Y ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedConstantSheaf.{u, r} Λ Y))
    (Y := etaleModuleDerivedTensor.{u, r} Λ X ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedConstantSheaf.{u, r} Λ X) ⋙
          (Functor.whiskeringRight _ _ _).obj (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g))
    (etaleModuleProjectionMapRestricted Λ g)

/-- The projection-formula map at the class of a complex of modules with K-flat constant sheaf
complexes is the restricted one. -/
theorem etaleModuleDerivedProjectionMap_app_app_Q (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory) :
    ((etaleModuleDerivedProjectionMap Λ g).app E).app (DerivedCategory.Q.obj N.obj) =
      ((etaleModuleProjectionMapRestricted Λ g).app E).app N :=
  NatTrans.congr_app (NatTrans.congr_app
    ((etaleModuleConstantRestrictFullyFaithful Λ (X := X) (Y := Y)).map_preimage
      (X := etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
        etaleModuleDerivedTensor.{u, r} Λ Y ⋙
          (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedConstantSheaf.{u, r} Λ Y))
      (Y := etaleModuleDerivedTensor.{u, r} Λ X ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedConstantSheaf.{u, r} Λ X) ⋙
          (Functor.whiskeringRight _ _ _).obj
            (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g))
      (etaleModuleProjectionMapRestricted Λ g)) E) N

/-- The restricted projection-formula map on complexes, precomposed with the unit
`g_*K ⟶ Rg_*K`, is `etaleModuleProjectionMapAux`. -/
theorem etaleModuleProjectionMapRestricted_fac (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory) :
    ((etaleModuleDerivedTensor.{u, r} Λ Y).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app K)).app
        ((etaleModuleDerivedConstantSheaf.{u, r} Λ Y).obj (DerivedCategory.Q.obj N.obj)) ≫
      ((etaleModuleProjectionMapRestricted Λ g).app (DerivedCategory.Q.obj K)).app N =
    etaleModuleProjectionMapAux Λ g K N := by
  have h := NatTrans.congr_app (Functor.rightDerived_fac_app
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
      etaleModuleConstantDerivedTensor.{u, r} Λ Y)
    (Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g)
      (etaleModuleConstantDerivedTensor.{u, r} Λ Y) ≫ (Functor.associator _ _ _).hom)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) _
    (etaleModuleProjectionMapHomotopy Λ g) K) N
  have e1 : ((Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g)
      (etaleModuleConstantDerivedTensor.{u, r} Λ Y) ≫ (Functor.associator _ _ _).hom).app K).app N =
      ((etaleModuleDerivedTensor.{u, r} Λ Y).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app K)).app
        ((etaleModuleDerivedConstantSheaf.{u, r} Λ Y).obj (DerivedCategory.Q.obj N.obj)) := by
    rw [NatTrans.comp_app, NatTrans.comp_app, Functor.associator_hom_app, NatTrans.id_app,
      Category.comp_id]
    rfl
  rw [← e1]
  exact h

/-- **The projection-formula map on complexes**: at the class of a complex `K` and of a complex
`N` with K-flat constant sheaf complexes, precomposed with the unit `g_*K ⟶ Rg_*K`, it is
`etaleModuleProjectionMapAux`. -/
theorem etaleModuleDerivedProjectionMap_fac (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory) :
    ((etaleModuleDerivedTensor.{u, r} Λ Y).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app K)).app
        ((etaleModuleDerivedConstantSheaf.{u, r} Λ Y).obj (DerivedCategory.Q.obj N.obj)) ≫
      ((etaleModuleDerivedProjectionMap Λ g).app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj N.obj) =
    etaleModuleProjectionMapAux Λ g K N := by
  rw [etaleModuleDerivedProjectionMap_app_app_Q]
  exact etaleModuleProjectionMapRestricted_fac Λ g K N

section Shift

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

/-- The sheaf-level projection map is invertible at a module isomorphic to the monoidal unit. -/
theorem isIso_etaleModuleConstantProjectionMapApp_of_iso (F : EtaleModules.{u, r} Λ X)
    {M : ModuleCat.{max (u + 1) r} Λ} (e : M ≅ 𝟙_ (ModuleCat.{max (u + 1) r} Λ)) :
    IsIso (etaleModuleConstantProjectionMapApp Λ g F M) := by
  have h := etaleModuleConstantProjectionMapApp_naturality_right Λ g F e.hom
  have := isIso_etaleModuleConstantProjectionMap_app_unit Λ g F
  rw [etaleModuleConstantProjectionMap_app_app] at this
  exact IsIso.of_isIso_fac_right h.symm

/-- The sheaf-level projection map is invertible at a zero module, both sides being zero. -/
theorem isIso_etaleModuleConstantProjectionMapApp_of_isZero (F : EtaleModules.{u, r} Λ X)
    {M : ModuleCat.{max (u + 1) r} Λ} (hM : IsZero M) :
    IsIso (etaleModuleConstantProjectionMapApp Λ g F M) := by
  have h1 : IsZero (((etaleModuleConstantTensor.{u, r} Λ Y).obj
      ((etaleModuleDirectImage.{u, r} Λ g).obj F)).obj M) := Functor.map_isZero _ hM
  have h2 : IsZero ((etaleModuleDirectImage.{u, r} Λ g).obj
      (((etaleModuleConstantTensor.{u, r} Λ X).obj F).obj M)) :=
    Functor.map_isZero _ (Functor.map_isZero _ hM)
  exact ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩

/-- **The projection map on total complexes is an isomorphism** when the complex of modules is
concentrated in one degree, with value isomorphic to the monoidal unit: the bicomplex map is
then invertible termwise, and the comparison of total complexes involves finite sums only. -/
theorem isIso_etaleModuleTotalProjectionMap (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (q₀ : ℤ)
    (hN : ∀ q, q ≠ q₀ → IsZero (N.X q)) (e : N.X q₀ ≅ 𝟙_ (ModuleCat.{max (u + 1) r} Λ)) :
    IsIso (etaleModuleTotalProjectionMap Λ g K N) := by
  have hε : ∀ p q, IsIso (etaleModuleConstantProjectionMapApp Λ g (K.X p) (N.X q)) := by
    intro p q
    by_cases hq : q = q₀
    · subst hq
      exact isIso_etaleModuleConstantProjectionMapApp_of_iso Λ g _ e
    · exact isIso_etaleModuleConstantProjectionMapApp_of_isZero Λ g _ (hN q hq)
  have key : ∀ {Z Z' : HomologicalComplex₂ (EtaleModules.{u, r} Λ Y) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)} (φ : Z ⟶ Z') [Z.HasTotal (ComplexShape.up ℤ)]
      [Z'.HasTotal (ComplexShape.up ℤ)], IsIso φ →
        IsIso (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) :=
    fun φ _ _ _ => (HomologicalComplex₂.total.mapIso (asIso φ) _).isIso_hom
  unfold etaleModuleTotalProjectionMap Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap
  refine IsIso.comp_isIso' (key _ (@HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _
    fun p => @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun q => hε p q)) ?_
  refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun n => ?_
  have hn : IsIso (HomologicalComplex₂.TotalMap.totalMapf (c₁₂ := ComplexShape.up ℤ)
      (etaleModuleDirectImage.{u, r} Λ g)
      (((etaleModuleConstantTensor.{u, r} Λ X).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K |>.obj N) n) := by
    refine HomologicalComplex₂.TotalMap.isIso_totalMapf_of_finite _ _ n ?_
    refine (Set.finite_singleton (n - q₀, q₀)).subset ?_
    rintro ⟨p, q⟩ ⟨hpq, hz⟩
    have hq : q = q₀ := by
      by_contra hq
      have hz' : IsZero (((etaleModuleConstantTensor.{u, r} Λ X).obj (K.X p)).obj (N.X q)) :=
        Functor.map_isZero _ (hN q hq)
      exact hz hz'
    have hpq' : p + q = n := hpq
    rw [Set.mem_singleton_iff, Prod.mk.injEq]
    exact ⟨by omega, hq⟩
  exact hn

/-- **`Tot(K ⊗ c_X N)` is K-injective** for `K` K-injective and `N` a module isomorphic to the
monoidal unit placed in one degree `q`: it is isomorphic to the shift `K⟦-q⟧`. -/
theorem isKInjective_totalComplex_single (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    [K.IsKInjective] (q : ℤ) (S : ModuleCat.{max (u + 1) r} Λ)
    (e : S ≅ 𝟙_ (ModuleCat.{max (u + 1) r} Λ)) :
    (totalComplex (etaleModuleTensor.{u, r} Λ X) K
      (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj S))).IsKInjective := by
  have eS : (etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S ≅ 𝟙_ (EtaleModules.{u, r} Λ X) :=
    (etaleModuleConstantSheafFunctor.{u, r} Λ X).mapIso e ≪≫ etaleModuleConstantSheafUnitIso Λ X
  have eRow : rowComplex (etaleModuleTensor.{u, r} Λ X) K
      ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S) ≅ K :=
    HomologicalComplex.Hom.isoOfComponents (fun p => whiskerLeftIso (K.X p) eS ≪≫ ρ_ (K.X p))
      (fun p p' _ => by
        change (K.X p ◁ eS.hom ≫ (ρ_ (K.X p)).hom) ≫ K.d p p' =
          (K.d p p' ▷ (etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S) ≫
            (K.X p' ◁ eS.hom ≫ (ρ_ (K.X p')).hom)
        rw [Category.assoc, ← whisker_exchange_assoc, rightUnitor_naturality])
  have e1 : totalComplex (etaleModuleTensor.{u, r} Λ X) K
      (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj S)) ≅
      totalComplex (etaleModuleTensor.{u, r} Λ X) K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
          ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S)) :=
    (((etaleModuleTensor.{u, r} Λ X).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (etaleModuleConstantSheafFunctor.{u, r} Λ X)
        (ComplexShape.up ℤ) q).app S)
  have e2 : totalComplex (etaleModuleTensor.{u, r} Λ X) K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
          ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S)) ≅
      (CategoryTheory.shiftFunctor (CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (-q)).obj
        (rowComplex (etaleModuleTensor.{u, r} Λ X) K
          ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S)) := by
    have e := mapBifunctorSingleIso (etaleModuleTensor.{u, r} Λ X) K
      ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S) q
    have := HomologicalComplex₂.hasTotal_of_iso e (ComplexShape.up ℤ)
    exact HomologicalComplex₂.total.mapIso e (ComplexShape.up ℤ) ≪≫
      (@asIso _ _ _ _ (StacksDraft.TotalSingleRow.totalSingleRowUnit
          (rowComplex (etaleModuleTensor.{u, r} Λ X) K
            ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S)) q)
        (StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit
          (rowComplex (etaleModuleTensor.{u, r} Λ X) K
            ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj S)) q)).symm
  rw [CochainComplex.isKInjective_iff_of_iso
    (e1 ≪≫ e2 ≪≫ (CategoryTheory.shiftFunctor _ (-q)).mapIso eRow)]
  infer_instance

/-- `etaleModuleProjectionMapAux` is invertible when the projection map on total complexes is,
and `Tot(K ⊗ c_X N)` is K-injective. -/
theorem isIso_etaleModuleProjectionMapAux (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory)
    (h₁ : IsIso (etaleModuleTotalProjectionMap Λ g K N.obj))
    (h₂ : (totalComplex (etaleModuleTensor.{u, r} Λ X) K
      (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).obj
        N.obj)).IsKInjective) :
    IsIso (etaleModuleProjectionMapAux Λ g K N) := by
  rw [etaleModuleProjectionMapAux]
  have hu : IsIso (etaleModuleDirectImageUnboundedUnitApp Λ g
      (totalComplex (etaleModuleTensor.{u, r} Λ X) K
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).obj N.obj))) :=
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app Λ g _ h₂
  have hQ : IsIso (DerivedCategory.Q.map (etaleModuleTotalProjectionMap Λ g K N.obj)) :=
    Functor.map_isIso _ _
  infer_instance

/-- **The projection-formula map is invertible at the shifts of `Λ`.** -/
theorem isIso_etaleModuleDerivedProjectionMap_app_shift
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (k : ℤ) :
    IsIso (((etaleModuleDerivedProjectionMap Λ g).app E).app
      (((DerivedCategory.singleFunctor (ModuleCat.{max (u + 1) r} Λ) 0).obj
        (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ)))⟦k⟧)) := by
  have eS : ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ) ≅ 𝟙_ (ModuleCat.{max (u + 1) r} Λ) :=
    ((Shrink.linearEquiv Λ Λ).trans ULift.moduleEquiv.symm).toModuleIso
  have hS : Module.Flat Λ (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ)) :=
    Module.Flat.of_linearEquiv (Shrink.linearEquiv Λ Λ)
  have : CochainComplex.IsStrictlyLE ((HomologicalComplex.single (ModuleCat.{max (u + 1) r} Λ)
      (ComplexShape.up ℤ) (-k)).obj (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ))) (-k) :=
    inferInstanceAs (((CochainComplex.singleFunctor _ (-k)).obj
      (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ))).IsStrictlyLE (-k))
  have hL := constantSheafKFlatComplexes_of_isStrictlyLE.{u, r} Λ
    ((HomologicalComplex.single (ModuleCat.{max (u + 1) r} Λ) (ComplexShape.up ℤ) (-k)).obj
      (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ))) (-k) (fun i => by
        by_cases hi : i = -k
        · subst hi
          exact Module.Flat.of_linearEquiv (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) (-k) (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ))).toLinearEquiv
        · have := ModuleCat.subsingleton_of_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-k)
              (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ)) i hi)
          infer_instance)
  let N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory := ⟨_, hL⟩
  have eM : ((DerivedCategory.singleFunctor (ModuleCat.{max (u + 1) r} Λ) 0).obj
      (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ)))⟦k⟧ ≅ DerivedCategory.Q.obj N.obj :=
    ((DerivedCategory.singleFunctors (ModuleCat.{max (u + 1) r} Λ)).shiftIso k (-k) 0
      (by omega)).app _ ≪≫
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max (u + 1) r} Λ) (-k)).app _
  rw [NatTrans.isIso_app_iff_of_iso ((etaleModuleDerivedProjectionMap Λ g).app E) eM]
  have := etaleModules_isGrothendieckAbelian.{u, r} Λ X
  obtain ⟨A, f, hA, hf⟩ := Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
    _ (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  have eE : DerivedCategory.Q.obj A ≅ E :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hu := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app Λ g A hA
  have hAux : IsIso (etaleModuleProjectionMapAux Λ g A N) :=
    isIso_etaleModuleProjectionMapAux Λ g A N
      (isIso_etaleModuleTotalProjectionMap Λ g A _ (-k)
        (fun q hq => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-k)
          (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ)) q hq)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-k)
          (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ)) ≪≫ eS))
      (isKInjective_totalComplex_single Λ A (-k) _ eS)
  rw [← etaleModuleDerivedProjectionMap_fac Λ g A N] at hAux
  have hQA : IsIso (((etaleModuleDerivedProjectionMap Λ g).app (DerivedCategory.Q.obj A)).app
      (DerivedCategory.Q.obj N.obj)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hAux
  have hn := NatTrans.congr_app ((etaleModuleDerivedProjectionMap Λ g).naturality eE.hom)
    (DerivedCategory.Q.obj N.obj)
  rw [NatTrans.comp_app, NatTrans.comp_app] at hn
  exact IsIso.of_isIso_fac_left hn


end Shift

/-- **The projection formula against constant coefficients** ([Stacks, Remark 0GL6]): along a
quasi-compact quasi-separated morphism whose direct image has finite cohomological dimension,
`Rg_*E ⊗^L_Λ M̲ ⟶ Rg_*(E ⊗^L_Λ M̲)` is an isomorphism for all `E ∈ D(X_étale, Λ)` and
`M ∈ D(Λ)`. -/
theorem isIso_etaleModuleDerivedProjectionMap [QuasiCompact g] [QuasiSeparated g]
    (hcd : ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ X,
      IsZero (((etaleModuleDirectImage.{u, r} Λ g).rightDerived q).obj F)) :
    IsIso (etaleModuleDerivedProjectionMap Λ g) := by
  have h : ∀ E, IsIso ((etaleModuleDerivedProjectionMap Λ g).app E) := fun E =>
    have : ∀ M, IsIso (((etaleModuleDerivedProjectionMap Λ g).app E).app M) := fun M =>
      isIso_app_of_isIso_app_shifts_constantSheaf Λ g hcd E
        ((etaleModuleDerivedProjectionMap Λ g).app E)
        (isIso_etaleModuleDerivedProjectionMap_app_shift Λ g E) M
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _


end Stacks.EtaleCohomology

end
