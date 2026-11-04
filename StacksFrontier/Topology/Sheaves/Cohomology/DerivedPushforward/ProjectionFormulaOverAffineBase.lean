module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaDevissage
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDirectSums
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens

/-!
# The projection formula over an affine base

Let `g : X ⟶ Spec A` be a quasi-compact and quasi-separated morphism of schemes and let `E` be an
object of `D_QCoh(𝒪_X)`. Then the projection-formula morphism

`Rg_*E ⊗^𝐋_{𝒪_{Spec A}} K ⟶ Rg_*(E ⊗^𝐋_{𝒪_X} Lg^*K)`

is invertible for every `K` in `D_QCoh(𝒪_{Spec A})`.

## Main results

* `CategoryTheory.Functor.preservesColimitsOfShape_discrete_mapDerivedCategory`: an exact functor
  between Grothendieck abelian categories which commutes with `J`-indexed direct sums induces a
  functor of unbounded derived categories which commutes with them too.

In the namespace `Stacks.Cohomology.ProjectionFormulaOverAffineBase`:

* `preservesColimitsOfShape_discrete_tilde_comp_projectionFormulaTarget`: the functor
  `M ↦ Rg_*(E ⊗^𝐋_{𝒪_X} Lg^*(M^~))` on `D(A)` commutes with direct sums.
* `isIso_projectionFormulaMap_tilde`: the projection-formula morphism is invertible at `M^~` for
  every `M` in `D(A)`.
* `isIso_projectionFormulaMap_of_isQuasicoherent`: the projection-formula morphism is invertible
  at every `K` in `D_QCoh(𝒪_{Spec A})`.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.ProjectionFormulaDevissage
open Stacks.Cohomology.ProjectionFormulaPerfect
open Stacks.Cohomology.ProjectionFormulaShiftedUnit
open Stacks.Cohomology.SupportedComplexes (quasicoherentDerivedProperty)
open Stacks.DerivedTensor.RingedSite

universe w w₁ w₂ v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor

/-- An exact functor between Grothendieck abelian categories which commutes with `J`-indexed
direct sums induces a functor of unbounded derived categories which commutes with them too. -/
theorem preservesColimitsOfShape_discrete_mapDerivedCategory
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [IsGrothendieckAbelian.{w} C₁] [IsGrothendieckAbelian.{w} C₂]
    (J : Type w) [PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete J) F.mapDerivedCategory := by
  have h₁ : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := C₁)) :=
    CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck J
  have h₂ : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := C₂)) :=
    CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck J
  have h₃ : PreservesColimitsOfShape (Discrete J)
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := C₂)) :=
    inferInstance
  have h₄ : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := C₁) ⋙ F.mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
    F.mapDerivedCategory J

end CategoryTheory.Functor

namespace Stacks.Cohomology.ProjectionFormulaOverAffineBase

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (g : X ⟶ Spec A)

/-! ### Quasi-coherence -/

/-- For `M` in `D(A)`, the complex `M^~` has quasi-coherent cohomology sheaves. -/
theorem quasicoherentDerivedProperty_tilde_obj (M : DerivedCategory (ModuleCat.{u} A)) :
    quasicoherentDerivedProperty (Spec A)
      (((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
          DerivedCategory (_root_.SheafOfModules.{u}
            (structureSheafRing (Spec A).toRingedSpace))).obj M) :=
  have := AlgebraicGeometry.tilde.preservesFiniteLimits A
  fun n => AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj A M n

/-- If `E` has quasi-coherent cohomology sheaves, then so does `E ⊗^𝐋_{𝒪_X} Lg^*(M^~)` for every
`M` in `D(A)`. -/
theorem quasicoherentDerivedProperty_derivedTensor_derivedPullback_tilde
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E) (M : DerivedCategory (ModuleCat.{u} A)) :
    quasicoherentDerivedProperty X
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E).obj
        ((derivedPullback g.toLRSHom.toShHom).obj
          (((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
              DerivedCategory (_root_.SheafOfModules.{u}
                (structureSheafRing (Spec A).toRingedSpace))).obj M))) := by
  have hpb : quasicoherentDerivedProperty X
      ((derivedPullback g.toLRSHom.toShHom).obj
        (((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
            DerivedCategory (_root_.SheafOfModules.{u}
              (structureSheafRing (Spec A).toRingedSpace))).obj M)) := fun n =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g _
      (quasicoherentDerivedProperty_tilde_obj M) n
  exact fun n => AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor X E _
    hE hpb n

/-! ### Direct sums -/

/-- The functor `M ↦ E ⊗^𝐋_{𝒪_X} Lg^*(M^~)` corestricted to `D_QCoh(𝒪_X)`, for `E` with
quasi-coherent cohomology. -/
private def tildePullbackTensorQuasicoherent
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E) :
    DerivedCategory (ModuleCat.{u} A) ⥤ (quasicoherentDerivedProperty X).FullSubcategory :=
  (quasicoherentDerivedProperty X).lift
    (((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (_root_.SheafOfModules.{u}
          (structureSheafRing (Spec A).toRingedSpace))) ⋙
      derivedPullback g.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E)
    (quasicoherentDerivedProperty_derivedTensor_derivedPullback_tilde g E hE)

/-- Corestricting `M ↦ E ⊗^𝐋_{𝒪_X} Lg^*(M^~)` and then including is the functor itself. -/
private theorem tildePullbackTensorQuasicoherent_comp_ι
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E) :
    tildePullbackTensorQuasicoherent g E hE ⋙ (quasicoherentDerivedProperty X).ι =
      ((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
          DerivedCategory (_root_.SheafOfModules.{u}
            (structureSheafRing (Spec A).toRingedSpace))) ⋙
        derivedPullback g.toLRSHom.toShHom ⋙
          (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E :=
  rfl

/-- `M ↦ E ⊗^𝐋_{𝒪_X} Lg^*(M^~)`, corestricted to `D_QCoh(𝒪_X)`, commutes with `I`-indexed direct
sums. -/
private theorem preservesColimitsOfShape_discrete_tildePullbackTensorQuasicoherent
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (tildePullbackTensorQuasicoherent g E hE) := by
  have := AlgebraicGeometry.tilde.preservesFiniteLimits A
  have hclosed :=
    Stacks.Cohomology.SupportedComplexes.quasicoherentDerivedProperty_isClosedUnderCoproducts X I
  have hrefl : ReflectsColimitsOfShape (Discrete I)
      (quasicoherentDerivedProperty X).ι := inferInstance
  have htilde : PreservesColimitsOfShape (Discrete I)
      (((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (_root_.SheafOfModules.{u}
          (structureSheafRing (Spec A).toRingedSpace)))) :=
    Functor.preservesColimitsOfShape_discrete_mapDerivedCategory (tilde.functor A) I
  have hcomp : PreservesColimitsOfShape (Discrete I)
      (tildePullbackTensorQuasicoherent g E hE ⋙ (quasicoherentDerivedProperty X).ι) := by
    have hinner : PreservesColimitsOfShape (Discrete I)
        (derivedPullback g.toLRSHom.toShHom ⋙
          (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E) := by
      have hpull : PreservesColimitsOfShape (Discrete I) (derivedPullback g.toLRSHom.toShHom) :=
        (preservesColimitsOfSize_derivedPullback.{u}
          g.toLRSHom.toShHom).preservesColimitsOfShape
      have htensor : PreservesColimitsOfShape (Discrete I)
          ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E) :=
        (preservesColimitsOfSize_derivedTensorProductFunctor_obj.{u}
          (Y := X.toRingedSpace) E).preservesColimitsOfShape
      exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ hpull htensor
    rw [tildePullbackTensorQuasicoherent_comp_ι]
    exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ htilde hinner
  exact @preservesColimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _
    (tildePullbackTensorQuasicoherent g E hE) (quasicoherentDerivedProperty X).ι hcomp hrefl

/-- For a quasi-compact quasi-separated morphism of schemes `g : X ⟶ Spec A` and an `E` in
`D_QCoh(𝒪_X)`, the functor `M ↦ Rg_*(E ⊗^𝐋_{𝒪_X} Lg^*(M^~))` on `D(A)` commutes with `I`-indexed
direct sums. -/
theorem preservesColimitsOfShape_discrete_tilde_comp_projectionFormulaTarget
    [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g]
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
          DerivedCategory (_root_.SheafOfModules.{u}
            (structureSheafRing (Spec A).toRingedSpace))) ⋙
        projectionFormulaTarget g.toLRSHom.toShHom E) := by
  have hqc := preservesColimitsOfShape_discrete_tildePullbackTensorQuasicoherent g E hE I
  have hpush : PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty X).ι ⋙ derivedPushforward g.toLRSHom.toShHom) :=
    Stacks.Cohomology.SupportedComplexes.preservesColimitsOfShape_discrete_ι_comp_derivedPushforward
      g I
  exact comp_preservesColimitsOfShape (tildePullbackTensorQuasicoherent g E hE)
    ((quasicoherentDerivedProperty X).ι ⋙ derivedPushforward g.toLRSHom.toShHom)

/-! ### The projection formula -/

/-- Let `g : X ⟶ Spec A` be a quasi-compact quasi-separated morphism of schemes and `E` an object
of `D_QCoh(𝒪_X)`. Then for every `M` in `D(A)` the projection-formula morphism

`Rg_*E ⊗^𝐋_{𝒪_{Spec A}} M^~ ⟶ Rg_*(E ⊗^𝐋_{𝒪_X} Lg^*(M^~))`

is an isomorphism. -/
theorem isIso_projectionFormulaMap_tilde
    [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g]
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E) (M : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (projectionFormulaMap g.toLRSHom.toShHom E
      (((tilde.functor A).mapDerivedCategory : DerivedCategory (ModuleCat.{u} A) ⥤
          DerivedCategory (_root_.SheafOfModules.{u}
            (structureSheafRing (Spec A).toRingedSpace))).obj M)) := by
  have := AlgebraicGeometry.tilde.preservesFiniteLimits A
  let hcs : Functor.CommShift ((tilde.functor A).mapDerivedCategory) ℤ := inferInstance
  have hct : Functor.IsTriangulated ((tilde.functor A).mapDerivedCategory) := inferInstance
  refine isIso_projectionFormulaMap_of_derivedModuleFunctor (A := (A : Type u))
    g.toLRSHom.toShHom E ((tilde.functor A).mapDerivedCategory) hcs hct
    (fun I => Functor.preservesColimitsOfShape_discrete_mapDerivedCategory (tilde.functor A) I)
    (fun I => preservesColimitsOfShape_discrete_tilde_comp_projectionFormulaTarget g E hE I)
    ?_ M
  exact ((tilde.functor A).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A (Shrink.{u} A)) ≪≫
    (DerivedCategory.singleFunctor (Spec A).Modules 0).mapIso
      ((tilde.functor A).mapIso (Shrink.linearEquiv A A).toModuleIso ≪≫
        AlgebraicGeometry.tildeSelf (R := A))

/-- Let `g : X ⟶ Spec A` be a quasi-compact and quasi-separated morphism of schemes, let `E` be
an object of `D_QCoh(𝒪_X)` and let `K` be an object of `D_QCoh(𝒪_{Spec A})`. Then the
projection-formula morphism

`Rg_*E ⊗^𝐋_{𝒪_{Spec A}} K ⟶ Rg_*(E ⊗^𝐋_{𝒪_X} Lg^*K)`

is an isomorphism. -/
@[stacks 08EU "the affine case, with no hypothesis beyond the tag's own: for a quasi-compact \
quasi-separated morphism of schemes g : X ⟶ Spec A, an E in D_QCoh(𝒪_X) and a K in \
D_QCoh(𝒪_{Spec A}), the Tag 0B53 map Rg_*E ⊗ᴸ K ⟶ Rg_*(E ⊗ᴸ Lg^*K) is invertible. This is the \
source's dévissage carried out — direct sums (Tag 08DZ), distinguished triangles, and the \
reduction to the shifts of the structure sheaf through the equivalence D(A) ≌ D_QCoh(𝒪_{Spec A}) \
of Tag 06Z0 and the remark of Tag 09PB. This is the tag over a base of the form Spec A; the \
source's first step, the reduction of a general base Y to an affine one, is carried out in \
Stacks.Cohomology.ProjectionFormulaGeneralBase, where the tag is registered in full"]
theorem isIso_projectionFormulaMap_of_isQuasicoherent
    [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g]
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E)
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (Spec A).toRingedSpace)))
    (hK : quasicoherentDerivedProperty (Spec A) K) :
    IsIso (projectionFormulaMap g.toLRSHom.toShHom E K) := by
  have := AlgebraicGeometry.tilde.preservesFiniteLimits A
  have hK' : AlgebraicGeometry.StandardModel.derivedQuasicoherent A K := hK
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := AlgebraicGeometry.derivedTilde A) ⟨K, hK'⟩
  refine isIso_projectionFormulaMap_of_iso_right g.toLRSHom.toShHom E
    (((AlgebraicGeometry.derivedTildeCompι A).app M).symm ≪≫
      (AlgebraicGeometry.StandardModel.derivedQuasicoherent A).ι.mapIso e)
    (isIso_projectionFormulaMap_tilde g E hE M)

end Stacks.Cohomology.ProjectionFormulaOverAffineBase

end
