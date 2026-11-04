module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleOfUnitAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineKoszulGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectFiniteProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTensorPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointPullback

/-!
# On an affine algebraic space, `M ↦ 𝒪_X ⊗_A M` on the model is `M ↦ ε^*(M̃)`

Let `X` be an algebraic space with an isomorphism `g : X ≅ h_T` to the algebraic space represented
by an object `T` of the big fppf site with scheme `Spec A`. The functor `M ↦ ε^*(M̃)` from
`A`-modules to `𝒪_{h_T}`-modules (`AlgebraicGeometry.Space.representedTilde`), restricted along
`g`, is a left adjoint carrying `A` to `𝒪_X`; so it is `𝒪_X ⊗_A -` for the base-ring datum given by
the action of `A` (`AlgebraicGeometry.Space.baseRingTensorModuleIsoOfUnitIso`), and this datum is
a ring isomorphism `A ≅ Γ(X, 𝒪_X)`, the functor being fully faithful. Read on the spaces-étale
model, `𝒪_X ⊗_A -` is the inverse image `T_ψ` along `X ⟶ (pt, A)`
(`AlgebraicGeometry.Space.pullbackToBaseRingIso`).

So there is a ring isomorphism `ψ : A ≅ Γ(X, 𝒪_X)` with `e_X ∘ T_ψ ≅ g^* ∘ (M ↦ ε^*(M̃))`, where
`e_X` is the equivalence of modules on the spaces-étale model with `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.Space.pointRingHomOfModel`: a ring map `A →+* Γ(X, 𝒪_X)` on the small étale
  model read as a ring map to the functions on the spaces-étale site.
* `AlgebraicGeometry.Space.pointTensorModulesEquivIso`: `e_X ∘ T_ψ ≅ 𝒪_X ⊗_A -`.
* `AlgebraicGeometry.Space.representedTildeOfIso`: `g^* ∘ (M ↦ ε^*(M̃))`.

## Main results

* `AlgebraicGeometry.Space.bijective_representedTildeOfIsoBaseRingHom`: the base-ring datum
  `A →+* Γ(X, 𝒪_X)` of `g^* ∘ (M ↦ ε^*(M̃))` is bijective.
* `AlgebraicGeometry.Space.pointTensorIsoRepresentedTildeOfIso`: `e_X ∘ T_ψ ≅ g^* ∘ (M ↦ ε^*(M̃))`
  for the resulting ring isomorphism `ψ`.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section PointRingHom

variable {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]

variable (X) in
/-- The regular functions on `X` as an object of its spaces-étale site are the sections of the
structure sheaf of the model over its terminal object. -/
def spacesEtaleModelTerminalSectionsEquiv :
    (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)) ≃+*
      (spacesEtaleModelStructureSheaf B S hS X).obj.obj (op (spacesEtaleModelTerminal B S hS X)) :=
  ((SpacesEtale.structurePresheaf B S hS X).mapIso
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.app
        (SpacesEtale.idObj B S hS X)).symm.op).commRingCatIsoToRingEquiv.trans
    (Shrink.ringEquiv _).symm

/-- `AlgebraicGeometry.Space.spacesEtaleModelGlobalHom ψ` is `ψ` followed by the ring
isomorphism `AlgebraicGeometry.Space.spacesEtaleModelTerminalSectionsEquiv`. -/
theorem spacesEtaleModelGlobalHom_eq
    (ψ : A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X))) :
    spacesEtaleModelGlobalHom B S hS (R := CommRingCat.of A) ψ =
      CommRingCat.ofHom ((spacesEtaleModelTerminalSectionsEquiv B S hS X).toRingHom.comp ψ) :=
  rfl

/-- A ring map `φ : A →+* Γ(X, 𝒪_X)` on the small étale model, read as a ring map to the regular
functions on `X` as an object of its spaces-étale site. -/
def pointRingHomOfModel (φ : A →+* modelGlobalFunctions B S hS X) :
    A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)) :=
  (spacesEtaleModelTerminalSectionsEquiv B S hS X).symm.toRingHom.comp
    ((spacesEtaleModelGlobalFunctionsEquiv B S hS X).symm.toRingHom.comp φ)

/-- Reading `AlgebraicGeometry.Space.pointRingHomOfModel φ` back on the model gives the base-ring
map `AlgebraicGeometry.Space.spacesEtaleModelBaseRingHom` of `φ`. -/
theorem spacesEtaleModelGlobalHom_pointRingHomOfModel (φ : A →+* modelGlobalFunctions B S hS X) :
    spacesEtaleModelGlobalHom B S hS (R := CommRingCat.of A) (pointRingHomOfModel B S hS φ) =
      spacesEtaleModelBaseRingHom B S hS X φ := by
  rw [spacesEtaleModelGlobalHom_eq]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact (spacesEtaleModelTerminalSectionsEquiv B S hS X).apply_symm_apply _

/-- `AlgebraicGeometry.Space.pointRingHomOfModel φ` is bijective when `φ` is. -/
theorem bijective_pointRingHomOfModel (φ : A →+* modelGlobalFunctions B S hS X)
    (hφ : Function.Bijective φ) : Function.Bijective (pointRingHomOfModel B S hS φ) := by
  rw [pointRingHomOfModel, RingHom.coe_comp, RingHom.coe_comp]
  exact (spacesEtaleModelTerminalSectionsEquiv B S hS X).symm.bijective.comp
    ((spacesEtaleModelGlobalFunctionsEquiv B S hS X).symm.bijective.comp hφ)

/-- **`e_X ∘ T_ψ ≅ 𝒪_X ⊗_A -`** when `ψ` and `φ` are the same ring map, read on the two models. -/
def pointTensorModulesEquivIso {ψ : A →+* (SpacesEtale.structurePresheaf B S hS X).obj
      (op (SpacesEtale.idObj B S hS X))} {φ : A →+* modelGlobalFunctions B S hS X}
    (h : spacesEtaleModelGlobalHom B S hS (R := CommRingCat.of A) ψ =
      spacesEtaleModelBaseRingHom B S hS X φ) :
    spacesEtaleModelPointTensor B S hS ψ ⋙ (spacesEtaleModelModulesEquiv B S hS X).functor ≅
      baseRingTensorModule B S hS X φ :=
  eqToIso (congrArg (fun f : RingedToposSiteHom (spacesEtaleModelRingedTopos B S hS X)
      (pointRingedTopos (CommRingCat.of A)) => (pointModuleCatEquiv (R := A)).inverse ⋙
        (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).inverse ⋙ f.pullbackTopos ⋙
          (spacesEtaleModelModulesEquiv B S hS X).functor)
      (congrArg (toPointRingedTopos (spacesEtaleModelRingedTopos B S hS X)) h)) ≪≫
    pullbackToBaseRingIso B S hS X φ

end PointRingHom

section Represented

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S) {X : AlgebraicSpaces B S hS}
  (g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩)

/-- **`M ↦ g^*(ε^*(M̃))`**: the functor `M ↦ ε^*(M̃)` on `h_T` restricted along `g : X ≅ h_T`. -/
def representedTildeOfIso : ModuleCat.{u} A ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  representedTilde B S hS hA p ⋙ (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor

/-- The functor `M ↦ g^*(ε^*(M̃))` is additive. -/
instance additive_representedTildeOfIso : (representedTildeOfIso B S hS hA p g).Additive :=
  haveI : (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  inferInstanceAs (representedTilde B S hS hA p ⋙
    (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor).Additive

/-- The adjunction of `M ↦ g^*(ε^*(M̃))`: global sections of `ε_*` composed with `g_*`. -/
def representedTildeOfIsoAdjunction :
    representedTildeOfIso B S hS hA p g ⊣
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).inverse ⋙
        representedZariskiDirectImageSchemeModules B S hS (BigFppfOver.mk B S hS hA p) ⋙
          moduleSpecΓFunctor (R := CommRingCat.of A) :=
  ((tilde.adjunction (R := CommRingCat.of A)).comp
    (representedAssociatedModuleZariskiAdjunction B S hS (BigFppfOver.mk B S hS hA p))).comp
    (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).toAdjunction

/-- `g^*(ε^*(Ã)) ≅ 𝒪_X`. -/
def representedTildeOfIsoUnitIso :
    (representedTildeOfIso B S hS hA p g).obj (ModuleCat.of A A) ≅ unitModule B S hS X.2 :=
  (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor.mapIso
    (representedTildeUnitIso B S hS hA p) ≪≫ Iso.refl _

/-- `M ↦ g^*(ε^*(M̃))` is fully faithful. -/
def representedTildeOfIsoFullyFaithful : (representedTildeOfIso B S hS hA p g).FullyFaithful :=
  (representedTildeFullyFaithful B S hS hA p).comp
    (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).fullyFaithfulFunctor

/-- The base-ring datum `A →+* Γ(X, 𝒪_X)` of `M ↦ g^*(ε^*(M̃))`. -/
abbrev representedTildeOfIsoBaseRingHom : A →+* modelGlobalFunctions B S hS X :=
  unitActionBaseRingHom (representedTildeOfIso B S hS hA p g)
    (representedTildeOfIsoUnitIso B S hS hA p g)

/-- The base-ring datum `A →+* Γ(X, 𝒪_X)` of `M ↦ g^*(ε^*(M̃))` is bijective. -/
theorem bijective_representedTildeOfIsoBaseRingHom :
    Function.Bijective (representedTildeOfIsoBaseRingHom B S hS hA p g) := by
  let θ := representedTildeOfIsoUnitIso B S hS hA p g
  let hΦ := representedTildeOfIsoFullyFaithful B S hS hA p g
  let E := smallEtaleModelModulesEquiv B S hS X
  have hsec : ∀ a b : modelGlobalFunctions B S hS X, unitSection a = unitSection b → a = b :=
    fun a b h => Subtype.ext (congrArg Subtype.val h)
  constructor
  · intro a b hab
    have h1 : E.functor.map (Adjunction.moduleCatUnitAction θ a) =
        E.functor.map (Adjunction.moduleCatUnitAction θ b) := by
      rw [map_moduleCatUnitAction, map_moduleCatUnitAction]
      exact congrArg (fun x => (SheafOfModules.unitHomEquiv _).symm (unitSection x)) hab
    have h2 := E.functor.map_injective h1
    rw [Adjunction.moduleCatUnitAction, Adjunction.moduleCatUnitAction] at h2
    have h3 := hΦ.map_injective ((Iso.cancel_iso_hom_right _ _ θ).1
      ((Iso.cancel_iso_inv_left θ _ _).1 h2))
    simpa using congrArg (fun f : ModuleCat.of A A ⟶ ModuleCat.of A A => f.hom (1 : A)) h3
  · intro s
    let v : SheafOfModules.unit (ringSheafOfSite.{u, u, u}
        (smallEtaleModelStructureSheaf B S hS X)) ⟶ SheafOfModules.unit _ :=
      (SheafOfModules.unitHomEquiv _).symm (unitSection s)
    let w : unitModule B S hS X.2 ⟶ unitModule B S hS X.2 := E.fullyFaithfulFunctor.preimage v
    let f : ModuleCat.of A A ⟶ ModuleCat.of A A := hΦ.preimage (θ.hom ≫ w ≫ θ.inv)
    refine ⟨f.hom (1 : A), ?_⟩
    have hf : f.hom (1 : A) • 𝟙 (ModuleCat.of A A) = f := by
      refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
      change f.hom (1 : A) • r = f.hom r
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, smul_eq_mul, mul_one]
    have hμ : Adjunction.moduleCatUnitAction θ (f.hom (1 : A)) = w := by
      rw [Adjunction.moduleCatUnitAction, hf, hΦ.map_preimage]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    refine hsec _ _ ((SheafOfModules.unitHomEquiv _).symm.injective ?_)
    rw [← map_moduleCatUnitAction, hμ]
    exact E.fullyFaithfulFunctor.map_preimage _

/-- The ring isomorphism `ψ : A ≅ Γ(X, 𝒪_X)` of `M ↦ g^*(ε^*(M̃))`, on the spaces-étale site. -/
abbrev representedTildeOfIsoPointRingHom :
    A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)) :=
  pointRingHomOfModel B S hS (representedTildeOfIsoBaseRingHom B S hS hA p g)

/-- **`e_X ∘ T_ψ ≅ g^* ∘ (M ↦ ε^*(M̃))`** for the ring isomorphism `ψ` of
`AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom`. -/
def pointTensorIsoRepresentedTildeOfIso :
    spacesEtaleModelPointTensor B S hS (representedTildeOfIsoPointRingHom B S hS hA p g) ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor ≅
      representedTildeOfIso B S hS hA p g :=
  pointTensorModulesEquivIso B S hS
      (spacesEtaleModelGlobalHom_pointRingHomOfModel B S hS _) ≪≫
    baseRingTensorModuleIsoOfUnitIso (representedTildeOfIso B S hS hA p g)
      (representedTildeOfIsoUnitIso B S hS hA p g) (representedTildeOfIsoAdjunction B S hS hA p g)

section Derived

attribute [local instance high] HasDerivedCategory.standard

/-- **A perfect object on the spaces-étale model of `X ≅ h_{Spec A}` is `𝒪_X ⊗_A C`** for a
bounded complex `C` of finite projective `A`-modules, with `ψ : A ≅ Γ(X, 𝒪_X)` the ring
isomorphism of `AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom`. -/
theorem exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS X).O)))
    (hE : (spacesEtaleModelRingedSite B S hS X).IsPerfect E) :
    ∃ C : CochainComplex (ModuleCat.{u} A) ℤ, {i : ℤ | ¬ IsZero (C.X i)}.Finite ∧
      (∀ i : ℤ, Module.Finite A (C.X i)) ∧ (∀ i : ℤ, Module.Projective A (C.X i)) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) := by
  let eX := spacesEtaleModelModulesEquiv B S hS X
  let Eq := etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g
  have : PreservesFiniteLimits eX.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ eX.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits eX.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      eX.toAdjunction.leftAdjoint_preservesColimits
  have : eX.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits Eq.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ Eq.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits Eq.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      Eq.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteLimits Eq.inverse := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ Eq.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits Eq.inverse :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      Eq.symm.toAdjunction.leftAdjoint_preservesColimits
  have : Eq.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : Eq.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let K := eX.functor.mapDerivedCategory.obj E
  have hK := isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X E hE
  have hK' := isPerfect_etaleModulePullback_standard B S hS g.inv (isEtale_hom_of_iso B S hS
    g.symm) K hK
  obtain ⟨C, hbd, hfin, hproj, ⟨eC⟩⟩ :=
    exists_finiteProjective_representedTilde_iso_of_isPerfect B S hS hA p _ hK'
  let DE := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence Eq.functor Eq.inverse Eq.unitIso
    Eq.counitIso
  let T := spacesEtaleModelPointTensor B S hS (representedTildeOfIsoPointRingHom B S hS hA p g)
  let i₁ : K ≅ Eq.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
      (((representedTilde B S hS hA p).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
    (DE.counitIso.app K).symm ≪≫ Eq.functor.mapDerivedCategory.mapIso eC.symm
  let i₂ : Eq.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
      (((representedTilde B S hS hA p).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) ≅
      eX.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
    Eq.functor.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso
        (((Functor.mapHomologicalComplexCompIso (F := representedTilde B S hS hA p)
          (G := Eq.functor) (H := representedTildeOfIso B S hS hA p g) (Iso.refl _)
            (ComplexShape.up ℤ)).app C) ≪≫
          ((Functor.mapHomologicalComplexCompIso (F := T) (G := eX.functor)
            (H := representedTildeOfIso B S hS hA p g)
              (pointTensorIsoRepresentedTildeOfIso B S hS hA p g)
                (ComplexShape.up ℤ)).app C).symm) ≪≫
      (eX.functor.mapDerivedCategoryFactors.app _).symm
  exact ⟨C, hbd, hfin, hproj,
    ⟨(spacesEtaleModelDerivedEquiv B S hS X).fullyFaithfulFunctor.preimageIso (i₁ ≪≫ i₂)⟩⟩

end Derived

end Represented

end AlgebraicGeometry.Space

end
