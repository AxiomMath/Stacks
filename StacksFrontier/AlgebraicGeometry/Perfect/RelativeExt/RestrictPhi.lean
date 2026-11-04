module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RestrictRelativeExt
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# Restricting `Φ = Lf^*(-) ⊗^L 𝒢` to an open

Let `a : U ⟶ X` and `f : X ⟶ Y` be morphisms of ringed spaces and `𝒢` a complex of
`𝒪_X`-modules. For a complex `K` of `𝒪_Y`-modules, the comparison `a^*(𝒜 ⊗ ℬ) ≅ a^*𝒜 ⊗ a^*ℬ` of
[Stacks, Tag 01CD] and `a^*f^* ≅ (f ∘ a)^*` give an isomorphism of total complexes

`a^* Tot(f^*K ⊗ 𝒢) ≅ Tot((f ∘ a)^*K ⊗ a^*𝒢)`,

natural in `K`. For an open immersion `j` of schemes it descends to the isomorphism of functors
`D(𝒪_S) ⥤ D(𝒪_U)`

`Φ_U ≅ Φ_X ⋙ D(j^*)`, `Φ_X = pullbackTensorDerivedFunctor`, `Φ_U` its analogue for `j^*𝒢`,

and, through `Lj^* ≅ D(j^*)`, to `Φ_U ≅ Φ_X ⋙ Lj^*`.

## Main definitions

* `Stacks.Cohomology.RelativeExt.pullbackTensorComplexRestrictIso`: the isomorphism of total
  complexes.
* `Stacks.Cohomology.RelativeExt.pullbackTensorDerivedRestrictIso`: `Φ_U ≅ Φ_X ⋙ D(j^*)`.
* `Stacks.Cohomology.RelativeExt.pullbackTensorDerivedPullbackIso`: `Φ_U ≅ Φ_X ⋙ Lj^*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance] sheafTensorAdditiveSpace sheafTensorObjAdditiveSpace

section Complex

variable {U X Y : RingedSpace.{u, u}} (a : U ⟶ X) (f : X ⟶ Y)

/-- The term `a^*(f^*𝒫 ⊗ 𝒬) ≅ (f ∘ a)^*𝒫 ⊗ a^*𝒬`. -/
def pullbackTensorBifunctorRestrictIso (P : SheafOfModules.{u} (structureSheafRing Y))
    (Q : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullback a).obj (((pullbackTensorBifunctor f).obj P).obj Q) ≅
      ((pullbackTensorBifunctor (a ≫ f)).obj P).obj ((modulePullback a).obj Q) :=
  (Stacks.RingedSpace.comparisonBifunctorIso a).app ((modulePullback f).obj P, Q) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).mapIso
      ((Stacks.DerivedPullback.Composition.modulePullbackComp a f).app P)).app
        ((modulePullback a).obj Q)

/-- The isomorphism `pullbackTensorBifunctorRestrictIso a f P Q` is natural in `(P, Q)`. -/
private theorem pullbackTensorBifunctorRestrictIso_naturality
    {P P' : SheafOfModules.{u} (structureSheafRing Y)} (w : P ⟶ P')
    {Q Q' : SheafOfModules.{u} (structureSheafRing X)} (v : Q ⟶ Q') :
    (modulePullback a).map (((pullbackTensorBifunctor f).map w).app Q ≫
          ((pullbackTensorBifunctor f).obj P').map v) ≫
        (pullbackTensorBifunctorRestrictIso a f P' Q').hom =
      (pullbackTensorBifunctorRestrictIso a f P Q).hom ≫
        (((pullbackTensorBifunctor (a ≫ f)).map w).app ((modulePullback a).obj Q) ≫
          ((pullbackTensorBifunctor (a ≫ f)).obj P').map ((modulePullback a).map v)) := by
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf
  let c := Stacks.DerivedPullback.Composition.modulePullbackComp a f
  have h0 := (Stacks.RingedSpace.comparisonBifunctorIso a).hom.naturality
    (X := ((modulePullback f).obj P, Q)) (Y := ((modulePullback f).obj P', Q'))
    ((modulePullback f).map w, v)
  have h2 := congrArg (fun t => (T.map t).app ((modulePullback a).obj Q))
    (c.hom.naturality w)
  have h3 := (T.map (c.hom.app P')).naturality ((modulePullback a).map v)
  simp only [Functor.comp_map, Functor.map_comp, NatTrans.comp_app] at h2
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
    Functor.comp_obj] at h0 h3
  have e (P : SheafOfModules.{u} (structureSheafRing Y))
      (Q : SheafOfModules.{u} (structureSheafRing X)) :
      (pullbackTensorBifunctorRestrictIso a f P Q).hom =
        (Stacks.RingedSpace.comparisonBifunctorIso a).hom.app ((modulePullback f).obj P, Q) ≫
          (T.map (c.hom.app P)).app ((modulePullback a).obj Q) := rfl
  rw [e, e]
  erw [reassoc_of% h0]
  exact (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) h3).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h2).trans (Category.assoc _ _ _))))).trans (Category.assoc _ _ _).symm

/-- The isomorphism `pullbackTensorBifunctorRestrictIso a f P Q` is natural in `P`. -/
theorem pullbackTensorBifunctorRestrictIso_naturality_left
    {P P' : SheafOfModules.{u} (structureSheafRing Y)} (w : P ⟶ P')
    (Q : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullback a).map (((pullbackTensorBifunctor f).map w).app Q) ≫
        (pullbackTensorBifunctorRestrictIso a f P' Q).hom =
      (pullbackTensorBifunctorRestrictIso a f P Q).hom ≫
        ((pullbackTensorBifunctor (a ≫ f)).map ((𝟭 _).map w)).app ((modulePullback a).obj Q) := by
  simpa using pullbackTensorBifunctorRestrictIso_naturality a f w (𝟙 Q)

/-- The isomorphism `pullbackTensorBifunctorRestrictIso a f P Q` is natural in `Q`. -/
theorem pullbackTensorBifunctorRestrictIso_naturality_right
    (P : SheafOfModules.{u} (structureSheafRing Y))
    {Q Q' : SheafOfModules.{u} (structureSheafRing X)} (v : Q ⟶ Q') :
    (modulePullback a).map (((pullbackTensorBifunctor f).obj P).map v) ≫
        (pullbackTensorBifunctorRestrictIso a f P Q').hom =
      (pullbackTensorBifunctorRestrictIso a f P Q).hom ≫
        ((pullbackTensorBifunctor (a ≫ f)).obj ((𝟭 _).obj P)).map ((modulePullback a).map v) := by
  simpa using pullbackTensorBifunctorRestrictIso_naturality a f (𝟙 P) v

variable (G : CochainComplex (TModules X) ℤ)

/-- The pullback `a^*` of modules preserves coproducts. -/
theorem modulePullback_preservesColimitsOfShape_discrete {J : Type} :
    PreservesColimitsOfShape (Discrete J) (modulePullback a) :=
  (modulePullbackPushforwardAdjunction a).leftAdjoint_preservesColimits.preservesColimitsOfShape

attribute [local instance] modulePullback_preservesColimitsOfShape_discrete

/-- **`a^* Tot(f^*K ⊗ 𝒢) ≅ Tot((f ∘ a)^*K ⊗ a^*𝒢)`.** -/
def pullbackTensorComplexRestrictIso
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    ((modulePullback a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((pullbackTensorComplexFunctor f G).obj K) ≅
      (pullbackTensorComplexFunctor (a ≫ f) (pullbackComplex a G)).obj K :=
  Functor.mapBifunctorTotalIso (pullbackTensorBifunctor f) (pullbackTensorBifunctor (a ≫ f))
    (𝟭 _) (modulePullback a) (modulePullback a) (pullbackTensorBifunctorRestrictIso a f)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (pullbackTensorBifunctorRestrictIso_naturality_left a f)
    (pullbackTensorBifunctorRestrictIso_naturality_right a f) K G

/-- **`a^* Tot(f^*K ⊗ 𝒢) ≅ Tot((f ∘ a)^*K ⊗ a^*𝒢)`, naturally in the complex `K`.** -/
def pullbackTensorComplexRestrictNatIso :
    pullbackTensorComplexFunctor f G ⋙
        (modulePullback a).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      pullbackTensorComplexFunctor (a ≫ f) (pullbackComplex a G) :=
  NatIso.ofComponents (pullbackTensorComplexRestrictIso a f G) fun {K K'} u => by
    have h := Functor.mapBifunctorTotalIso_hom_naturality (pullbackTensorBifunctor f)
      (pullbackTensorBifunctor (a ≫ f)) (𝟭 _) (modulePullback a) (modulePullback a)
      (pullbackTensorBifunctorRestrictIso a f) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c := ComplexShape.up ℤ) (pullbackTensorBifunctorRestrictIso_naturality_left a f)
      (pullbackTensorBifunctorRestrictIso_naturality_right a f) K K' G G u (𝟙 G)
    rw [CategoryTheory.Functor.map_id] at h
    exact h

end Complex

section Derived

attribute [local instance] HasDerivedCategory.standard isOpenImmersion_toShHom
  modulePullback_preservesFiniteLimits

variable {X U S : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]
  {G : CochainComplex (TModules X.toRingedSpace) ℤ} (hG : IsBoundedFlatOver f.toLRSHom.toShHom G)

/-- `Q ⋙ Φ_U ≅ Q ⋙ (Φ_X ⋙ D(j^*))`. -/
def pullbackTensorDerivedRestrictIsoQ :
    DerivedCategory.Q ⋙ pullbackTensorDerivedFunctor
        (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG) ≅
      DerivedCategory.Q ⋙ (pullbackTensorDerivedFunctor hG ⋙ restrictDerived j) :=
  pullbackTensorDerivedFunctorFactors (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG) ≪≫
    Functor.isoWhiskerRight
      (pullbackTensorComplexRestrictNatIso j.toLRSHom.toShHom f.toLRSHom.toShHom G).symm
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pullbackTensorComplexFunctor f.toLRSHom.toShHom G)
      (Functor.mapDerivedCategoryFactors (modulePullback j.toLRSHom.toShHom)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackTensorDerivedFunctorFactors hG).symm (restrictDerived j) ≪≫
    Functor.associator _ _ _

/-- **`Φ_U ≅ Φ_X ⋙ D(j^*)`**: the functor `Φ` of `j^*𝒢` over `U` is the restriction to `U` of
`Φ`, for an open immersion `j : U ⟶ X`. -/
def pullbackTensorDerivedRestrictIso :
    pullbackTensorDerivedFunctor (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG) ≅
      pullbackTensorDerivedFunctor hG ⋙ restrictDerived j :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
      (ComplexShape.up ℤ)) _).preimageIso (pullbackTensorDerivedRestrictIsoQ f j hG)

/-- On the image `Q K` of a complex `K`, the component of `pullbackTensorDerivedRestrictIso` is
the component at `K` of `pullbackTensorDerivedRestrictIsoQ`. -/
theorem pullbackTensorDerivedRestrictIso_hom_app_Q
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) ℤ) :
    (pullbackTensorDerivedRestrictIso f j hG).hom.app (DerivedCategory.Q.obj K) =
      (pullbackTensorDerivedRestrictIsoQ f j hG).hom.app K :=
  NatTrans.congr_app ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
      (ComplexShape.up ℤ)) _).map_preimage _) K

/-- **`Φ_U ≅ Φ_X ⋙ Lj^*`**, through `Lj^* ≅ D(j^*)` for an open immersion. -/
def pullbackTensorDerivedPullbackIso :
    pullbackTensorDerivedFunctor (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG) ≅
      pullbackTensorDerivedFunctor hG ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j.toLRSHom.toShHom :=
  pullbackTensorDerivedRestrictIso f j hG ≪≫ Functor.isoWhiskerLeft _
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
      j.toLRSHom.toShHom).symm

end Derived

end Stacks.Cohomology.RelativeExt

end
