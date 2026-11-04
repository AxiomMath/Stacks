module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedBaseChangeComparison
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.SquarePushforwardModulesIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange

/-!
# The base change map of sheaves of modules of a commutative square of schemes, two ways

For a commutative square `g' ≫ f = f' ≫ g` of schemes, the base change map of sheaves of modules
along the 2-commutative square of étale ringed topoi `etaleRingedToposHomSquareTwoIso`, read
through the identifications `Ψ = etaleRingedForget Λ _` of sheaves of `Λ̲`-modules with sheaves of
`Λ`-modules, is the étale base change map of sheaves of `Λ`-modules, up to the pushforward and
pullback comparisons. This is `Stacks.CategoryTheory.BaseChange.map_comp_localization` for the
"localization" `Ψ`, whose one geometric input is
`Stacks.EtaleCohomology.etaleRingedSquarePullbackIso_comparison`.

## Main results

* `Stacks.EtaleCohomology.etaleRingedSquarePushforwardModulesIso_sections`: the comparison of
  composite direct images of the square is the inverse of the 2-isomorphism on sections.
* `Stacks.EtaleCohomology.etaleRingedSquarePullbackIso_comparison'`: the transport of
  `AlgebraicGeometry.RingedToposHom.TwoIso.squarePullbackIso`.
* `Stacks.EtaleCohomology.etaleModuleBaseChange_etaleRingedForget`: `Ψ` carries the base change
  map of the square of étale ringed topoi to the étale base change map.
* `Stacks.EtaleCohomology.etaleRingedForget_map_baseChange_comp`: the same, followed by `f'_*` of a
  map out of `(g')^* I`.

## Implementation notes

All statements spell the sheaf categories of the ringed topoi as
`SheafOfModules (ringSheaf (RingedSite.ringedTopos (etaleRingedSite Λ X)).O)` and the universe as
`max r (u + 1)`, which are the spellings the morphisms of ringed topoi produce: the kernel compares
large terms built from the other spellings only very slowly.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]
variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- The comparison of composite direct images of sheaves of `Λ̲`-modules around the square is the
inverse of the 2-isomorphism of the square on underlying sheaves of sets. -/
theorem etaleRingedSquarePushforwardModulesIso_sections
    (M : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)).O)).map
        ((RingedToposHom.TwoIso.squarePushforwardModulesIso
      (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')))
      (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)))
      (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y')))
      (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)))
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)).hom.app M) =
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w).e.inv.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ X')).O)).obj M) := by
  apply Sheaf.hom_ext
  ext V x
  rfl

/-- **`Ψ` carries the comparison of pullbacks of the 2-commutative square of étale ringed topoi
to the comparison of composite étale inverse images.** -/
theorem etaleRingedSquarePullbackIso_comparison'
    (K : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)).O)) :
    ((etaleModuleInverseImageCompIso.{u, r} Λ f' g).symm ≪≫
        ((etaleModuleInverseImageCompIso.{u, r} Λ g' f).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w)).symm).hom.app
        ((etaleRingedForget.{u, r} Λ Y).obj K) ≫
      (etaleModuleInverseImage.{u, r} Λ g').map
        ((etaleRingedPullbackComparison.{u, r} Λ f).hom.app K) ≫
      (etaleRingedPullbackComparison.{u, r} Λ g').hom.app
        ((etaleRingedToposHom.{u, r} Λ f).toModulesHom.pullbackModules.obj K) =
    (etaleModuleInverseImage.{u, r} Λ f').map
      ((etaleRingedPullbackComparison.{u, r} Λ g).hom.app K) ≫
      (etaleRingedPullbackComparison.{u, r} Λ f').hom.app
        ((etaleRingedToposHom.{u, r} Λ g).toModulesHom.pullbackModules.obj K) ≫
      (etaleRingedForget.{u, r} Λ X').map ((RingedToposHom.TwoIso.squarePullbackIso
      (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')))
      (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)))
      (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y')))
      (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)))
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)).hom.app K) := by
  refine etaleRingedSquarePullbackIso_comparison.{u, r} Λ f g f' g' w _
    (RingedToposHom.TwoIso.squarePushforwardModulesIso
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)).hom ?_ ?_ K
  · intro K
    exact RingedToposHom.TwoIso.unit_comp_map_squarePullbackIso_hom_app
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w) K
  · exact etaleRingedSquarePushforwardModulesIso_sections.{u, r} Λ f g f' g' w

/-- The instance of `Stacks.CategoryTheory.BaseChange.map_comp_localization` behind
`Stacks.EtaleCohomology.etaleModuleBaseChange_etaleRingedForget`. -/
theorem etaleModuleBaseChange_etaleRingedForget_aux
    (I : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)).O)) :
    (etaleModuleInverseImage.{u, r} Λ g).map
      ((etaleRingedPushforwardComparison.{u, r} Λ f).hom.app I) ≫
      Stacks.CategoryTheory.BaseChange.map (etaleModuleInverseImageAdj.{u, r} Λ f)
        (etaleModuleInverseImageAdj.{u, r} Λ f')
        ((etaleModuleInverseImageCompIso.{u, r} Λ f' g).symm ≪≫
        ((etaleModuleInverseImageCompIso.{u, r} Λ g' f).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w)).symm)
        (Iso.refl _) ((etaleRingedForget.{u, r} Λ X).obj I) ≫
      (etaleModuleDirectImage.{u, r} Λ f').map
        ((etaleRingedPullbackComparison.{u, r} Λ g').hom.app I) =
    (etaleRingedPullbackComparison.{u, r} Λ g).hom.app
        ((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.obj I) ≫
      (etaleRingedForget.{u, r} Λ Y').map (Stacks.CategoryTheory.BaseChange.map
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
        (RingedToposHom.TwoIso.squarePullbackIso
      (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')))
      (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)))
      (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y')))
      (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)))
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) I) ≫
      (etaleRingedPushforwardComparison.{u, r} Λ f').hom.app
        ((etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.obj I) := by
  refine Stacks.CategoryTheory.BaseChange.map_comp_localization
    (QY := etaleRingedForget.{u, r} Λ Y) (QX := etaleRingedForget.{u, r} Λ X)
    (QY' := etaleRingedForget.{u, r} Λ Y') (QX' := etaleRingedForget.{u, r} Λ X')
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
    (etaleModuleInverseImageAdj.{u, r} Λ f) (etaleModuleInverseImageAdj.{u, r} Λ f')
    (etaleRingedPushforwardComparison.{u, r} Λ f).hom
    (etaleRingedPushforwardComparison.{u, r} Λ f').hom
    (etaleRingedPullbackComparison.{u, r} Λ f).hom (etaleRingedPullbackComparison.{u, r} Λ f').hom
    (etaleRingedPullbackComparison.{u, r} Λ g).hom (etaleRingedPullbackComparison.{u, r} Λ g').hom
    (RingedToposHom.TwoIso.squarePullbackIso
      (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')))
      (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)))
      (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y')))
      (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)))
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w))
    ((etaleModuleInverseImageCompIso.{u, r} Λ f' g).symm ≪≫
        ((etaleModuleInverseImageCompIso.{u, r} Λ g' f).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w)).symm)
    ?_ ?_ ?_ I
  · intro K
    exact etaleRingedPullbackComparison_counit.{u, r} Λ f K
  · intro K
    exact etaleRingedPullbackComparison_counit.{u, r} Λ f' K
  · intro K
    have h := etaleRingedSquarePullbackIso_comparison'.{u, r} Λ f g f' g' w K
    convert h using 3



/-- **The base change map of sheaves of modules of the square of étale ringed topoi is the étale
base change map.** For a sheaf `I` of `Λ̲`-modules on `X_étale`, the étale base change map
`g^{-1} f_* ⟶ f'_* (g')^{-1}` at `Ψ I`, between `g^{-1}` of the pushforward comparison along `f`
and `f'_*` of the pullback comparison along `g'`, is the pullback comparison along `g`, followed by
`Ψ` of the base change map of the square of ringed topoi at `I` and by the pushforward comparison
along `f'`. -/
theorem etaleModuleBaseChange_etaleRingedForget
    (I : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)).O)) :
    (etaleModuleInverseImage.{u, r} Λ g).map
      ((etaleRingedPushforwardComparison.{u, r} Λ f).hom.app I) ≫
      (etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm).app ((etaleRingedForget.{u, r} Λ X).obj I) ≫
      (etaleModuleDirectImage.{u, r} Λ f').map
        ((etaleRingedPullbackComparison.{u, r} Λ g').hom.app I) =
    (etaleRingedPullbackComparison.{u, r} Λ g).hom.app
        ((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.obj I) ≫
      (etaleRingedForget.{u, r} Λ Y').map (Stacks.CategoryTheory.BaseChange.map
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
        (RingedToposHom.TwoIso.squarePullbackIso
      (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')))
      (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)))
      (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y')))
      (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)))
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) I) ≫
      (etaleRingedPushforwardComparison.{u, r} Λ f').hom.app
        ((etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.obj I) := by
  have e : etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm =
      Stacks.CategoryTheory.BaseChange.twoSquare (etaleModuleInverseImageAdj.{u, r} Λ f)
        (etaleModuleInverseImageAdj.{u, r} Λ f') (etaleModuleInverseImageCompIso.{u, r} Λ f' g).symm
        ((etaleModuleInverseImageCompIso.{u, r} Λ g' f).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w)) := rfl
  rw [e]
  have h := etaleModuleBaseChange_etaleRingedForget_aux.{u, r} Λ f g f' g' w I
  rw [Stacks.CategoryTheory.BaseChange.map_trans_symm_refl,
    Stacks.CategoryTheory.BaseChange.map] at h
  exact h

/-- The diagram chase behind `etaleRingedForget_map_baseChange_comp`, over variables. -/
private theorem chase_baseChange_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (R : E ⥤ C) (Ψ : D ⥤ C) {b c : C} {e1 e2 e3 : E} {d1 d2 d3 : D}
    (ci : Ψ.obj d1 ⟶ b) (ch : b ⟶ Ψ.obj d1) (hc : ci ≫ ch = 𝟙 _)
    (x : b ⟶ c) (y : c ⟶ R.obj e1) (z1 : e1 ⟶ e2) (z2 : e2 ⟶ e3)
    (W1 : d1 ⟶ d2) (W2 : d2 ⟶ d3) (k1 : Ψ.obj d2 ⟶ R.obj e2) (k2 : Ψ.obj d3 ⟶ R.obj e3)
    (h : x ≫ y ≫ R.map z1 = ch ≫ Ψ.map W1 ≫ k1) (hn : Ψ.map W2 ≫ k2 = k1 ≫ R.map z2) :
    (ci ≫ x) ≫ y ≫ R.map (z1 ≫ z2) = Ψ.map (W1 ≫ W2) ≫ k2 := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, reassoc_of% h, reassoc_of% hc,
    Category.assoc, hn]

/-- **Degreewise, `Ψ` carries the base change map of the square of constant ringed topoi,
followed by `f'_*` of a map `s`, to the étale base change map followed by `f'_*` of `Ψ s`**, up to
the pullback and pushforward comparisons. -/
theorem etaleRingedForget_map_baseChange_comp
    (I : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)).O))
    {T : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')).O)}
    (s : (etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.obj I ⟶ T) :
    ((etaleRingedPullbackComparison.{u, r} Λ g).inv.app
          ((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.obj I) ≫
        (etaleModuleInverseImage.{u, r} Λ g).map
          ((etaleRingedPushforwardComparison.{u, r} Λ f).hom.app I)) ≫
      (etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm).app ((etaleRingedForget.{u, r} Λ X).obj I) ≫
      (etaleModuleDirectImage.{u, r} Λ f').map
        ((etaleRingedPullbackComparison.{u, r} Λ g').hom.app I ≫
          (etaleRingedForget.{u, r} Λ X').map s) =
    (etaleRingedForget.{u, r} Λ Y').map (Stacks.CategoryTheory.BaseChange.map
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
        (RingedToposHom.TwoIso.squarePullbackIso
      (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')))
      (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)))
      (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y')))
      (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)))
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) I ≫
        (etaleRingedToposHom.{u, r} Λ f').pushforwardModules.map s) ≫
      (etaleRingedPushforwardComparison.{u, r} Λ f').hom.app T := by
  have hc := chase_baseChange_comp (etaleModuleDirectImage.{u, r} Λ f')
    (etaleRingedForget.{u, r} Λ Y')
    ((etaleRingedPullbackComparison.{u, r} Λ g).inv.app
      ((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.obj I))
    ((etaleRingedPullbackComparison.{u, r} Λ g).hom.app
      ((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.obj I))
    (Iso.inv_hom_id_app (etaleRingedPullbackComparison.{u, r} Λ g)
      ((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.obj I))
    ((etaleModuleInverseImage.{u, r} Λ g).map
      ((etaleRingedPushforwardComparison.{u, r} Λ f).hom.app I))
    ((etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm).app ((etaleRingedForget.{u, r} Λ X).obj I))
    ((etaleRingedPullbackComparison.{u, r} Λ g').hom.app I) ((etaleRingedForget.{u, r} Λ X').map s)
    (Stacks.CategoryTheory.BaseChange.map
      (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
      (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
      (RingedToposHom.TwoIso.squarePullbackIso
        (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X')))
        (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X)))
        (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y')))
        (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y)))
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) I)
    ((etaleRingedToposHom.{u, r} Λ f').pushforwardModules.map s)
    ((etaleRingedPushforwardComparison.{u, r} Λ f').hom.app
      ((etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.obj I))
    ((etaleRingedPushforwardComparison.{u, r} Λ f').hom.app T)
    (etaleModuleBaseChange_etaleRingedForget.{u, r} Λ f g f' g' w I)
    ((etaleRingedPushforwardComparison.{u, r} Λ f').hom.naturality s)
  exact hc
end Stacks.EtaleCohomology
