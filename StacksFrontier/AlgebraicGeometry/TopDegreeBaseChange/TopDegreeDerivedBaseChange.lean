module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeAmplitude
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeComparison
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorProjection
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.Global

/-!
# Conclusion (c) of Tag 0EX3 at the level of the derived base change map (draft)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open DerivedCategory RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

/-- **A further cartesian square tacked onto a top-degree base-change situation**, read as a
situation over the original morphism `f`: the composite square
`X'' ⟶ X' ⟶ X` over `Y'' ⟶ Y' ⟶ Y` is cartesian. -/
def extend (S : TopDegreeBaseChangeSituation.{u}) {X'' Y'' : Scheme.{u}} (h' : X'' ⟶ S.X')
    (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (sq : IsPullback h' f'' S.f' h) :
    TopDegreeBaseChangeSituation.{u} where
  X := S.X
  Y := S.Y
  f := S.f
  d := S.d
  isCompact_X := S.isCompact_X
  isQuasiSeparated_X := S.isQuasiSeparated_X
  isCompact_Y := S.isCompact_Y
  isQuasiSeparated_Y := S.isQuasiSeparated_Y
  vanishes_above := S.vanishes_above
  X' := X''
  Y' := Y''
  g' := h' ≫ S.g'
  f' := f''
  g := h ≫ S.g
  isPullback := sq.paste_horiz S.isPullback

end Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

variable (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})

/-- In a top-degree base-change situation the higher direct images along `f'` of quasi-coherent
modules vanish above `d`, in the shape the amplitude lemmas consume. -/
theorem vanishes_above_f' : ∀ i : ℤ, (S.d : ℤ) < i → ∀ F : S.X'.Modules, F.IsQuasicoherent →
    IsZero (((Scheme.Modules.pushforward S.f').rightDerivedPlus i).obj F) := fun i hi F hF =>
  have : F.IsQuasicoherent := hF
  isZero_rightDerivedPlus_pushforward_baseChange S i hi F

/-- `H⁰` of the comparison `Lf^*(M[0]) ⟶ (f^*M)[0]` is invertible. -/
theorem isIso_homology_zero_derivedToOrdinaryPullbackSingle {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (M : SheafOfModules.{u} (structureSheafRing Y)) :
    IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
      (derivedToOrdinaryPullbackSingle f M 0)) := by
  have h := isIso_homologyDerivedPullbackSingleMap f M 0
  rw [homologyDerivedPullbackSingleMap] at h
  exact IsIso.of_isIso_comp_right _ (homologySingleIso ((modulePullback f).obj M) 0).hom

/-- **Conclusion (c) reduces to the derived base change map.** The canonical map `γ` of
[Stacks, Tag 0EX3] is invertible as soon as the degree-`d` cohomology of the derived base change
map at `F'[0]` is: its other two factors are always invertible. -/
theorem isIso_topDirectImageBaseChangeMap_of_isIso_homology_derivedBaseChangeMap
    (F' : S.X'.Modules) [F'.IsQuasicoherent] {X'' Y'' : Scheme.{u}}
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (sq : IsPullback h' f'' S.f' h)
    (hbc : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y''.toRingedSpace))
      (S.d : ℤ)).map
        (derivedBaseChangeMap h'.toLRSHom.toShHom f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom
          h.toLRSHom.toShHom (toShHom_comm_of_isPullback h' f'' h sq)
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing S.X'.toRingedSpace)) 0).obj
            F')))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h (toShHom_comm_of_isPullback h' f'' h sq)) := by
  let S₂ := S.extend h' f'' h sq
  have : QuasiCompact f'' := S₂.quasiCompact_f'
  have : QuasiSeparated f'' := S₂.quasiSeparated_f'
  let E₀ := (singleFunctor (SheafOfModules.{u} (structureSheafRing S.X'.toRingedSpace)) 0).obj F'
  have hE : ((derivedPullback h'.toLRSHom.toShHom).obj E₀).IsLE 0 :=
    isLE_derivedPullback_obj h'.toLRSHom.toShHom _ 0 (isLE_singleFunctor_zero _)
  have hcoh : ∀ i : ℤ, ((homologyFunctor (SheafOfModules.{u}
      (structureSheafRing X''.toRingedSpace)) i).obj
        ((derivedPullback h'.toLRSHom.toShHom).obj E₀)).IsQuasicoherent :=
    Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedPullback_obj h'
      _ (isDQCoh_singleFunctor F' inferInstance)
  have h2 := isIso_homology_derivedPushforward_map_of_isIso_homology_zero f'' S.d
    (vanishes_above_f' S₂) hcoh hE ((modulePullback h'.toLRSHom.toShHom).obj F')
    (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0)
    (isIso_homology_zero_derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F') (S.d : ℤ) le_rfl
  refine (isIso_topDirectImageBaseChangeMap_iff S F' h' f'' h _).2 ?_
  have : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y''.toRingedSpace))
      (S.d : ℤ)).map
        (derivedBaseChangeMap h'.toLRSHom.toShHom f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom
          h.toLRSHom.toShHom (toShHom_comm_of_isPullback h' f'' h sq) E₀ ≫
        (derivedPushforward f''.toLRSHom.toShHom).map
          (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) := by
    rw [Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hbc h2
  exact this

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
