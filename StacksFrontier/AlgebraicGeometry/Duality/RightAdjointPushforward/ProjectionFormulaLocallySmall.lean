module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidalUnitors
public import StacksFrontier.AlgebraicGeometry.Duality.InternalHom.LocallySmall

/-!
# The projection formula at the locally small model

[Stacks, Tag 08EU] — for `f : X ⟶ Y` quasi-compact and quasi-separated and `c`, `K` with
quasi-coherent cohomology, `Rf_*c ⊗ᴸ K ⟶ Rf_*(c ⊗ᴸ Lf^*K)` is invertible — is proved at the
standard model of the derived categories as
`Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh`. This file reads it
at the locally small model, the model of `Stacks.Duality.quasiCoherentDerivedCategory`, by
transporting along the comparison of the two models: `Rf_*` and `Lf^*` through
`StacksDraft.DerivedModel.derivedPushforwardModelIso` and `derivedPullbackModelIso`, and `⊗ᴸ`
through `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso`.

## Main definitions

* `Stacks.Duality.ProjectionFormulaLocallySmall.natTrans`: the projection-formula morphism
  `Rf_*c ⊗ᴸ - ⟶ Rf_*(c ⊗ᴸ Lf^*-)` at the locally small model, as a natural transformation.
* `Stacks.Duality.ProjectionFormulaLocallySmall.tensorSwapIso`: the symmetry `A ⊗ᴸ - ≅ - ⊗ᴸ A`.
* `Stacks.Duality.ProjectionFormulaLocallySmall.derivedTensorRightIso`: `- ⊗ᴸ P` is the left
  adjoint `Stacks.Duality.InternalHom.derivedTensorRight P` of `R𝓗om(P, -)`.

## Main results

* `Stacks.Duality.ProjectionFormulaLocallySmall.isIso_natTrans_app`: [Stacks, Tag 08EU] at the
  locally small model.
* `Stacks.Duality.ProjectionFormulaLocallySmall.isIso_derivedRestrict_tensor_pullback_map`: for a
  cartesian square along an open immersion `j`, `c ⊗ᴸ Lf^*u` is invertible on the inverse image of
  the open whenever `u` is invertible on it.

## Implementation notes

`natTrans` is the projection-formula map of the standard model transported along the comparison
of the two models, rather than `Stacks.Duality.projectionFormulaMap` at a comparison `α` of
[Stacks, Tag 079U] at the locally small model. Likewise
`isIso_derivedRestrict_tensor_pullback_map` is proved from the comparison of [Stacks, Tag 079U]
at the standard model along the open immersion; no second pullback-tensor comparison is defined
at the locally small model.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality.ProjectionFormulaLocallySmall

/-! ### Transporting a natural transformation along two equivalences -/

section Transport

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) {Fs Gs : C₁ ⥤ C₂} {Fl Gl : D₁ ⥤ D₂}
  (eF : Fs ⋙ E₂.functor ≅ E₁.functor ⋙ Fl) (eG : Gs ⋙ E₂.functor ≅ E₁.functor ⋙ Gl)

/-- A comparison `F ⋙ E₂ ≅ E₁ ⋙ F'` read as `E₁⁻¹ ⋙ F ⋙ E₂ ≅ F'`. -/
def conjugateIso {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} (e : F ⋙ E₂.functor ≅ E₁.functor ⋙ F') :
    E₁.inverse ⋙ F ⋙ E₂.functor ≅ F' :=
  Functor.isoWhiskerLeft E₁.inverse e ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E₁.counitIso F' ≪≫ F'.leftUnitor

/-- A natural transformation `Fs ⟶ Gs` transported to `Fl ⟶ Gl` along equivalences `E₁`, `E₂`
and comparisons `Fs ⋙ E₂ ≅ E₁ ⋙ Fl`, `Gs ⋙ E₂ ≅ E₁ ⋙ Gl`. -/
def transportNatTrans (π : Fs ⟶ Gs) : Fl ⟶ Gl :=
  (conjugateIso E₁ E₂ eF).inv ≫ Functor.whiskerLeft E₁.inverse (Functor.whiskerRight π E₂.functor) ≫
    (conjugateIso E₁ E₂ eG).hom

/-- The component of `transportNatTrans E₁ E₂ eF eG π` at `K` is invertible if and only if the
component of `π` at `E₁.inverse.obj K` is. -/
theorem isIso_transportNatTrans_app_iff (π : Fs ⟶ Gs) (K : D₁) :
    IsIso ((transportNatTrans E₁ E₂ eF eG π).app K) ↔ IsIso (π.app (E₁.inverse.obj K)) := by
  have e : (transportNatTrans E₁ E₂ eF eG π).app K = ((conjugateIso E₁ E₂ eF).app K).inv ≫
      E₂.functor.map (π.app (E₁.inverse.obj K)) ≫ ((conjugateIso E₁ E₂ eG).app K).hom := rfl
  rw [e, isIso_comp_left_iff, isIso_comp_right_iff]
  exact ⟨fun _ => isIso_of_reflects_iso _ E₂.functor, fun _ => inferInstance⟩

/-- **Invertibility of a map under a functor transports along equivalences.** -/
theorem isIso_map_iff_of_iso {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} (e : F ⋙ E₂.functor ≅ E₁.functor ⋙ F')
    {K K' : D₁} (k : K ⟶ K') :
    IsIso (F'.map k) ↔ IsIso (F.map (E₁.inverse.map k)) := by
  rw [← NatIso.isIso_map_iff (conjugateIso E₁ E₂ e) k]
  exact ⟨fun (_ : IsIso (E₂.functor.map (F.map (E₁.inverse.map k)))) =>
      isIso_of_reflects_iso _ E₂.functor,
    fun _ => Functor.map_isIso E₂.functor (F.map (E₁.inverse.map k))⟩

end Transport


section Standard

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)


/-- `Rf_*` at the standard model. -/
abbrev standardPushforward :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom

/-- `Rf_*c ⊗ᴸ -` at the standard model. -/
abbrev standardSource
    (c : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
    ((standardPushforward f).obj c)


/-- `Lf^* ⋙ (c ⊗ᴸ -) ⋙ Rf_*` at the standard model. -/
abbrev standardTarget
    (c : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj c ⋙
      standardPushforward f


/-- `Lf^* ⋙ (c ⊗ᴸ -) ⋙ Lg^*` at the standard model. -/
abbrev standardPullbackTensorPullback {Z : Scheme.{u}} (g : Z ⟶ X)
    (c : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj c ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom


/-- At the standard model, the derived tensor product of the ringed site of opens is that of the
site of [Stacks, Tag 08J8] (`Stacks.Duality.InternalHom.standardTensor`). -/
def standardTensorIso (Z : Scheme.{u}) :
    Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf ≅
      Stacks.Duality.InternalHom.standardTensor Z :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
    (Stacks.SheafOfModules.ringedSite Z.sheaf)


/-- `- ⊗ᴸ B` at the standard model. -/
abbrev standardTensorRight (Z : Scheme.{u})
    (B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).flip.obj B

/-- The projection-formula morphism `Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)` at the standard model, as a
natural transformation in `K`. -/
def standardNatTrans
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          f.toLRSHom.toShHom).obj E) ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj E ⋙
          Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            f.toLRSHom.toShHom where
  app K := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f.toLRSHom.toShHom E K
  naturality _ _ k :=
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
      f.toLRSHom.toShHom E k

/-- At the standard model, for `f` quasi-compact and quasi-separated and `E`, `K` with
quasi-coherent cohomology, `Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)` is invertible. -/
theorem isIso_standardNatTrans_app [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    IsIso ((standardNatTrans f E).app K) :=
  Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f E K hE hK

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

/-- **Tensoring the derived pullback of a map invertible on an open gives a map invertible on its
inverse image**, at the standard model: for a commutative square `j' ≫ f = f' ≫ j` of ringed
spaces and `v` with `Lj^* v` invertible, `Lj'^*(c ⊗ᴸ Lf^* v)` is invertible. -/
theorem isIso_standard_pullback_tensor_pullback_map {U V X₀ Y₀ : RingedSpace.{u, u}}
    (j' : U ⟶ X₀) (f' : U ⟶ V) (f₀ : X₀ ⟶ Y₀) (j : V ⟶ Y₀) (sq : j' ≫ f₀ = f' ≫ j)
    (c : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X₀.sheaf))
    {J I : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules Y₀.sheaf)} (v : J ⟶ I)
    (hv : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j).map v)) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j').map
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X₀.sheaf).obj c).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f₀).map v))) := by
  let Lj := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j
  let Lj' := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j'
  let Lf := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f₀
  let Lf' := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f'
  have h₁ : IsIso (Lj'.map (Lf.map v)) :=
    (NatIso.isIso_map_iff
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackSquareIso j' f' f₀ j sq) v).1
      (Functor.map_isIso Lf' (Lj.map v))
  let m : ((c, Lf.obj J) : _ × _) ⟶ (c, Lf.obj I) := 𝟙 c ×ₘ Lf.map v
  have h₂ : IsIso ((Stacks.Cohomology.DerivedPullbackTensor.tensorOfPullbacks j').map m) := by
    change IsIso ((Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor U.sheaf)).map
        ((Lj'.prod Lj').map m))
    have e : Lj'.map (𝟙 c) = 𝟙 (Lj'.obj c) := Lj'.map_id c
    have h₀ : IsIso (Lj'.map (𝟙 c)) := by
      rw [e]
      exact IsIso.id _
    have : IsIso ((Lj'.prod Lj').map m) := (isIso_prod_iff _ _).2 ⟨h₀, h₁⟩
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ this
  have h₃ := (NatIso.isIso_map_iff
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso j') m).2 h₂
  change IsIso (Lj'.map ((Functor.uncurry.obj
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X₀.sheaf)).map m)) at h₃
  exact Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X₀.sheaf) c (Lf.map v) ▸ h₃

end Standard


/-! ### The locally small model -/

section LocallySmall

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The comparison of the source `Rf_*c ⊗ᴸ -` of the projection formula at the two models. -/
def sourceModelIso (c : DerivedCategory X.Modules) :
    (standardSource f c) ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u}
          (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u}
          (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)).functor ⋙
        (derivedTensor Y).obj ((derivedPushforward f).obj c) :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Y.sheaf).app
      ((standardPushforward f).obj c)).symm ≪≫
    Functor.isoWhiskerLeft _ ((derivedTensor Y).mapIso
      ((StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).app c))

/-- The comparison of the target `Lf^* ⋙ (c ⊗ᴸ -) ⋙ Rf_*` of the projection formula at the two
models. -/
def targetModelIso (c : DerivedCategory X.Modules) :
    (standardTarget f c) ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u}
          (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u}
          (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)).functor ⋙
        (derivedPullback f ⋙ (derivedTensor X).obj c ⋙ derivedPushforward f) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.derivedPushforwardModelIso
        f.toLRSHom.toShHom) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
        X.sheaf).app c).symm (derivedPushforward f) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom)
      _ ≪≫ Functor.associator _ _ _

/-- **The projection-formula morphism at the locally small model**, natural in `K`:
`Rf_*c ⊗ᴸ K ⟶ Rf_*(c ⊗ᴸ Lf^*K)`, the morphism of [Stacks, Tag 0B53] at the standard model
transported along the comparison of the two models. -/
def natTrans (c : DerivedCategory X.Modules) :
    (derivedTensor Y).obj ((derivedPushforward f).obj c) ⟶
      derivedPullback f ⋙ (derivedTensor X).obj c ⋙ derivedPushforward f :=
  transportNatTrans _ _ (sourceModelIso f c) (targetModelIso f c) (standardNatTrans f c)

/-- **[Stacks, Tag 08EU] at the locally small model**: for `f` quasi-compact and quasi-separated
and `c`, `K` with quasi-coherent cohomology, `Rf_*c ⊗ᴸ K ⟶ Rf_*(c ⊗ᴸ Lf^*K)` is invertible. -/
theorem isIso_natTrans_app [QuasiCompact f] [QuasiSeparated f] (c : DerivedCategory X.Modules)
    (K : DerivedCategory Y.Modules)
    (hc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj c).IsQuasicoherent)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    IsIso ((natTrans f c).app K) :=
  (isIso_transportNatTrans_app_iff _ _ (sourceModelIso f c) (targetModelIso f c)
    (standardNatTrans f c) K).2 <| isIso_standardNatTrans_app f c K
    (fun i => (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      ((homologyFunctorModelIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).app c)
      (hc i))
    (fun i => (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
      ((homologyFunctorModelIso (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).app K)
      (hK i))

/-- The comparison of `Lf^* ⋙ (c ⊗ᴸ -) ⋙ Lg^*` at the two models. -/
def pullbackTensorPullbackModelIso {Z : Scheme.{u}} (g : Z ⟶ X) (c : DerivedCategory X.Modules) :
    standardPullbackTensorPullback f g c ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u}
          (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u}
          (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)).functor ⋙
        (derivedPullback f ⋙ (derivedTensor X).obj c ⋙ derivedPullback g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.derivedPullbackModelIso
        g.toLRSHom.toShHom) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
        X.sheaf).app c).symm (derivedPullback g) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom)
      _ ≪≫ Functor.associator _ _ _

/-- **Tensoring the derived pullback of a map invertible on an open gives a map invertible on its
inverse image**, at the locally small model: for a cartesian square `j' ≫ f = f' ≫ j` with `j`
an open immersion and `u` invertible on `V`, the map `c ⊗ᴸ Lf^*u` is invertible on `U`. -/
theorem isIso_derivedRestrict_tensor_pullback_map {U V : Scheme.{u}} {j' : U ⟶ X} {f' : U ⟶ V}
    {j : V ⟶ Y} (sq : IsPullback j' f' f j) [IsOpenImmersion j] (c : DerivedCategory X.Modules)
    {J I : DerivedCategory Y.Modules} (u : J ⟶ I)
    (hu : IsIso ((OpenImmersion.derivedRestrict j).map u)) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    IsIso ((OpenImmersion.derivedRestrict j').map
      (((derivedTensor X).obj c).map ((derivedPullback f).map u))) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have hs : j'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ j.toLRSHom.toShHom := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : U ⟶ Y => k.toLRSHom.toShHom) sq.w
  rw [NatIso.isIso_map_iff (derivedRestrictIsoDerivedPullback j')]
  have hj : IsIso ((derivedPullback j).map u) :=
    (NatIso.isIso_map_iff (derivedRestrictIsoDerivedPullback j) u).1 hu
  have hj' := (isIso_map_iff_of_iso _ _
    (StacksDraft.DerivedModel.derivedPullbackModelIso j.toLRSHom.toShHom) u).1 hj
  exact (isIso_map_iff_of_iso _ _ (pullbackTensorPullbackModelIso f j' c) u).2
    (isIso_standard_pullback_tensor_pullback_map _ f'.toLRSHom.toShHom _ _ hs c _ hj')

/-- **The symmetry of `⊗ᴸ_{𝒪_Z}`** at the locally small model, as an isomorphism of functors
`A ⊗ᴸ - ≅ - ⊗ᴸ A`: the braiding of the symmetric monoidal structure of [Stacks, Tag 0FPT]. -/
def tensorSwapIso (Z : Scheme.{u}) (A : DerivedCategory Z.Modules) :
    (derivedTensor Z).obj A ≅ (derivedTensor Z).flip.obj A :=
  letI := Scheme.Modules.canonicalDerivedMonoidal Z
  letI : SymmetricCategory (DerivedCategory Z.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Z.sheaf
  (derivedTensorIsoCurriedTensor Z).app A ≪≫ BraidedCategory.tensorLeftIsoTensorRight A ≪≫
    ((flipFunctor _ _ _).mapIso (derivedTensorIsoCurriedTensor Z)).symm.app A

/-- **`- ⊗ᴸ P` at the locally small model is the tensor product of the derived internal Hom
adjunction** `Stacks.Duality.InternalHom.derivedTensorSheafHomAdjunction`, which is transported
from the standard model. -/
def derivedTensorRightIso (Z : Scheme.{u}) (P : DerivedCategory Z.Modules) :
    (derivedTensor Z).flip.obj P ≅ Stacks.Duality.InternalHom.derivedTensorRight P :=
  let e := StacksDraft.DerivedModel.schemeModulesComparison Z
  let i : standardTensorRight Z (e.inverse.obj P) ⋙ e.functor ≅
      e.functor ⋙ (derivedTensor Z).flip.obj P :=
    (((flipFunctor _ _ _).mapIso
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Z.sheaf)).app
        (e.inverse.obj P)).symm
  (conjugateIso e e i).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (((flipFunctor _ _ _).mapIso (standardTensorIso Z)).app (e.inverse.obj P)) _)

end LocallySmall

end Stacks.Duality.ProjectionFormulaLocallySmall

end
