module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OrdinaryTopDegreeMate
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardLeray
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomologyEdgeIsomorphism
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionPaste

/-!
# The tail of the transposed top-degree base change map is invertible for an affine base change

`…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit` computes
the transpose, under `h^* ⊣ h_*`, of the canonical map `γ⁺` of conclusion (c) of
[Stacks, Tag 0EX3]: it is the degree-`d` higher direct image along `f'` of the ordinary unit
`F' ⟶ (h')_*(h')^* F'`, followed by a composite of canonical comparisons

> `Θ : R^d f'_*((h')_*(h')^* F') ⟶ h_* R^d f''_* (h')^* F'`.

This file proves that `Θ` is an isomorphism when the bottom morphism `h` of the square, and hence
`h'`, is affine. That is the degeneration of the Leray spectral sequence of the two composites
around the square, and it is the step of the source's proof of (c) that identifies
`H^d(X'', (h')^* F')` with `H^d(X', (h')_*(h')^* F')`.

## Main results

* `…TopDegreeBaseChange.isGE_derivedPushforward_singleFunctor_zero`: `Rg_*(M[0])` lies in
  degrees `≥ 0`.
* `…TopDegreeBaseChange.isIso_derivedPushforwardHomologyComparison_app_derivedPushforward`: the
  cohomology edge morphism `H^q(Rk_* Rg_*(M[0])) ⟶ k_* H^q(Rg_*(M[0]))` is invertible for `k`
  affine, `g` quasi-compact and quasi-separated and `M` quasi-coherent.
* `…TopDegreeBaseChange.isIso_lerayTail`: **`Θ` is an isomorphism for `h` affine.**
* `…TopDegreeBaseChange.lerayTail_naturality`: `Θ` is natural in the module upstairs: it carries
  `R^d f'_*((h')_* φ)` to `h_*(R^d f''_* φ)` for an endomorphism `φ` of `(h')^* F'`.

## Implementation notes

*`Θ` is not given a name.* It is stated verbatim as the tail of
`homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit`, in which the module
`(h')^* F'` is spelled `RingedSpaceModuleAdjunction.modulePullback` in the factors before the
comparison of the iterated derived pushforwards and `AlgebraicGeometry.Scheme.Modules.pullback`
after it. A definition with that body, or any declaration whose type mentions the transpose of
`γ⁺` together with a constant standing for the tail, fails with `(kernel) deterministic timeout`:
the kernel then has to identify the component of the comparison of the iterated derived
pushforwards at the two spellings, which it does by unfolding the comparison. Stating facts about
the tail verbatim and consuming them in lemmas that take the tail as a variable fixed by the
equation of the transpose — unification then matches the two occurrences syntactically — passes
the kernel in seconds.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition
open DerivedCategory

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
  (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
    = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
  (F' : S.X'.Modules)

/-- The derived direct image of a module placed in degree `0` has no cohomology in
negative degrees. -/
theorem isGE_derivedPushforward_singleFunctor_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : X.Modules) :
    ((derivedPushforward g.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj M)).IsGE 0 :=
  (DerivedCategory.isGE_iff _ 0).2 fun i hi =>
    isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus g M i
      (Functor.isZero_rightDerivedPlus_of_neg (modulePushforward g.toLRSHom.toShHom) M i hi)

/-- **The cohomology edge morphism of `Rh_*` is invertible at the derived direct image of a
quasi-coherent module along a quasi-compact quasi-separated morphism, for `h` affine.** -/
theorem isIso_derivedPushforwardHomologyComparison_app_derivedPushforward
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (k : Y ⟶ Z) [IsAffineHom k] [QuasiCompact g]
    [QuasiSeparated g] (M : X.Modules) [M.IsQuasicoherent] (q : ℤ) :
    IsIso ((derivedPushforwardHomologyComparison k.toLRSHom.toShHom q).app
      ((derivedPushforward g.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj M))) := by
  have := isGE_derivedPushforward_singleFunctor_zero g M
  refine isIso_derivedPushforwardHomologyComparison_app_of_isGE k.toLRSHom.toShHom q 0 _
    fun j => ?_
  exact @Stacks.Cohomology.AffineComparison.rightAcyclic_pushforward_of_isAffineHom _ _ k _ _
    (Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward g M j)

include sq in
/-- **The tail `Θ` of the transpose of the top-degree base change map is an isomorphism when the
bottom morphism `h` of the square is affine.** Every factor is: the two crossings of the models of
`Rf_*`, the comparison `(h')_* M ⟶ R(h')_* M` at the quasi-coherent `(h')^* F'` ([Stacks, Tag
0G9N] for the affine `h'`), the comparison of the two iterated derived pushforwards (a conjugate
of an isomorphism), and the cohomology edge morphism of `Rh_*` (the cohomology sheaves of
`Rf''_*((h')^* F')` are quasi-coherent, hence `h_*`-acyclic). -/
theorem isIso_lerayTail [F'.IsQuasicoherent] [IsAffineHom h] [IsAffineHom h']
    [QuasiCompact f''] [QuasiSeparated f''] :
    IsIso ((homologyFunctorDerivedPushforwardIso S.f'
            ((modulePullback h'.toLRSHom.toShHom ⋙
              modulePushforward h'.toLRSHom.toShHom).obj F') (S.d : ℤ)).inv ≫
          (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
            ((derivedPushforward S.f'.toLRSHom.toShHom).map
                ((singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.app
                ((modulePushforward h'.toLRSHom.toShHom).obj
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
              Qh.map ((Functor.mapHomotopyCategorySingleFunctor
                    (modulePushforward h'.toLRSHom.toShHom) 0).inv.app
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                (derivedPushforwardUnit h'.toLRSHom.toShHom).app
                    ((HomotopyCategory.singleFunctor
                      (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
                      ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                  (derivedPushforward h'.toLRSHom.toShHom).map
                    ((singleFunctorIsoCompQh
                        (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.app
                      ((modulePullback h'.toLRSHom.toShHom).obj F'))) ≫
              (Mate.derivedPushforwardComparisonSquare
                  (derivedAdjunction S.f'.toLRSHom.toShHom)
                  (derivedAdjunction f''.toLRSHom.toShHom)
                  (derivedAdjunction h.toLRSHom.toShHom)
                  (derivedAdjunction h'.toLRSHom.toShHom)
                  (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                  (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom)).app
                ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
            ((derivedPushforward f''.toLRSHom.toShHom).obj
              ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom) := by
  have : ((modulePullback h'.toLRSHom.toShHom).obj F').IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback h' F'
  have hC : IsIso ((derivedPushforwardUnit h'.toLRSHom.toShHom).app
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
        ((modulePullback h'.toLRSHom.toShHom).obj F'))) :=
    (AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom h'
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
          ((modulePullback h'.toLRSHom.toShHom).obj F'))
        (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_singleFunctor_obj_X
          0 _ inferInstance))
  have hP : IsIso (derivedPullbackSquare h'.toLRSHom.toShHom f''.toLRSHom.toShHom
      S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq) := by
    dsimp only [derivedPullbackSquare, Mate.derivedPullbackSquare, TwoSquare.mk]
    infer_instance
  have hM : IsIso (Mate.derivedPushforwardComparisonSquare
      (derivedAdjunction S.f'.toLRSHom.toShHom)
      (derivedAdjunction f''.toLRSHom.toShHom)
      (derivedAdjunction h.toLRSHom.toShHom)
      (derivedAdjunction h'.toLRSHom.toShHom)
      (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
        S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
      (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom S.f'.toLRSHom.toShHom)) := by
    rw [derivedPushforwardComparisonSquare_eq_conjugateEquiv h'.toLRSHom.toShHom
      f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq]
    exact conjugateEquiv_iso _ _ _
  have hMapp : IsIso ((Mate.derivedPushforwardComparisonSquare
      (derivedAdjunction S.f'.toLRSHom.toShHom)
      (derivedAdjunction f''.toLRSHom.toShHom)
      (derivedAdjunction h.toLRSHom.toShHom)
      (derivedAdjunction h'.toLRSHom.toShHom)
      (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
        S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
      (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom S.f'.toLRSHom.toShHom)).app
        ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) :=
    NatIso.isIso_app_of_isIso _ _
  have a1 : IsIso ((singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.app
        ((modulePushforward h'.toLRSHom.toShHom).obj
          ((modulePullback h'.toLRSHom.toShHom).obj F'))) := inferInstance
  have a2 : IsIso (Qh.map ((Functor.mapHomotopyCategorySingleFunctor
        (modulePushforward h'.toLRSHom.toShHom) 0).inv.app
      ((modulePullback h'.toLRSHom.toShHom).obj F'))) := inferInstance
  have a4 : IsIso ((derivedPushforward h'.toLRSHom.toShHom).map
      ((singleFunctorIsoCompQh
          (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.app
        ((modulePullback h'.toLRSHom.toShHom).obj F'))) := inferInstance
  have aA := @IsIso.comp_isIso _ _ _ _ _ _ _ a1
    (@IsIso.comp_isIso _ _ _ _ _ _ _ a2 (@IsIso.comp_isIso _ _ _ _ _ _ _ hC a4))
  have e1 := isIso_derivedPushforwardHomologyComparison_app_derivedPushforward f'' h
    ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)
  have e2 : IsIso ((Scheme.Modules.pushforward h).map
      (homologyFunctorDerivedPushforwardIso f''
        ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom) :=
    Functor.map_isIso _ _
  refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' e1 e2))
  exact (Functor.mapIso _
    (Functor.mapIso _ (@asIso _ _ _ _ _ aA) ≪≫ @asIso _ _ _ _ _ hMapp)).isIso_hom

/-- **The tail `Θ` of the transpose of the top-degree base change map is natural in the module
upstairs.** For an endomorphism `φ` of `(h')^* F'`, `R^d f'_*((h')_* φ)` followed by `Θ` is `Θ`
followed by `h_*(R^d f''_* φ)`. Every factor of `Θ` is a component of a natural transformation,
and the squares are pasted. -/
theorem lerayTail_naturality [F'.IsQuasicoherent]
    (φ : (modulePullback h'.toLRSHom.toShHom).obj F' ⟶
      (modulePullback h'.toLRSHom.toShHom).obj F') :
    ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
        ((modulePushforward h'.toLRSHom.toShHom).map φ) ≫
      ((homologyFunctorDerivedPushforwardIso S.f'
            ((modulePullback h'.toLRSHom.toShHom ⋙
              modulePushforward h'.toLRSHom.toShHom).obj F') (S.d : ℤ)).inv ≫
          (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
            ((derivedPushforward S.f'.toLRSHom.toShHom).map
                ((singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.app
                ((modulePushforward h'.toLRSHom.toShHom).obj
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
              Qh.map ((Functor.mapHomotopyCategorySingleFunctor
                    (modulePushforward h'.toLRSHom.toShHom) 0).inv.app
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                (derivedPushforwardUnit h'.toLRSHom.toShHom).app
                    ((HomotopyCategory.singleFunctor
                      (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
                      ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                  (derivedPushforward h'.toLRSHom.toShHom).map
                    ((singleFunctorIsoCompQh
                        (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.app
                      ((modulePullback h'.toLRSHom.toShHom).obj F'))) ≫
              (Mate.derivedPushforwardComparisonSquare
                  (derivedAdjunction S.f'.toLRSHom.toShHom)
                  (derivedAdjunction f''.toLRSHom.toShHom)
                  (derivedAdjunction h.toLRSHom.toShHom)
                  (derivedAdjunction h'.toLRSHom.toShHom)
                  (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                  (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom)).app
                ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
            ((derivedPushforward f''.toLRSHom.toShHom).obj
              ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom) =
    ((homologyFunctorDerivedPushforwardIso S.f'
            ((modulePullback h'.toLRSHom.toShHom ⋙
              modulePushforward h'.toLRSHom.toShHom).obj F') (S.d : ℤ)).inv ≫
          (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
            ((derivedPushforward S.f'.toLRSHom.toShHom).map
                ((singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.app
                ((modulePushforward h'.toLRSHom.toShHom).obj
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
              Qh.map ((Functor.mapHomotopyCategorySingleFunctor
                    (modulePushforward h'.toLRSHom.toShHom) 0).inv.app
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                (derivedPushforwardUnit h'.toLRSHom.toShHom).app
                    ((HomotopyCategory.singleFunctor
                      (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
                      ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                  (derivedPushforward h'.toLRSHom.toShHom).map
                    ((singleFunctorIsoCompQh
                        (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.app
                      ((modulePullback h'.toLRSHom.toShHom).obj F'))) ≫
              (Mate.derivedPushforwardComparisonSquare
                  (derivedAdjunction S.f'.toLRSHom.toShHom)
                  (derivedAdjunction f''.toLRSHom.toShHom)
                  (derivedAdjunction h.toLRSHom.toShHom)
                  (derivedAdjunction h'.toLRSHom.toShHom)
                  (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                  (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom)).app
                ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
            ((derivedPushforward f''.toLRSHom.toShHom).obj
              ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom) ≫
      (Scheme.Modules.pushforward h).map
        (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).map
          (X := (Scheme.Modules.pullback h').obj F') (Y := (Scheme.Modules.pullback h').obj F')
          φ) := by
  have q₁ := homologyFunctorDerivedPushforwardIso_inv_naturality S.f'
    ((modulePushforward h'.toLRSHom.toShHom).map φ) (S.d : ℤ)
  have qa₁ := (singleFunctorIsoCompQh
    (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.naturality
      ((modulePushforward h'.toLRSHom.toShHom).map φ)
  have qa₂ := map_comp_square Qh ((Functor.mapHomotopyCategorySingleFunctor
    (modulePushforward h'.toLRSHom.toShHom) 0).inv.naturality φ)
  have qa₃ := (derivedPushforwardUnit h'.toLRSHom.toShHom).naturality
    ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).map φ)
  have qa₄ := map_comp_square (derivedPushforward h'.toLRSHom.toShHom)
    ((singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.naturality φ)
  have qa := comp_two_squares qa₁ (comp_two_squares qa₂ (comp_two_squares qa₃ qa₄))
  have qb := (Mate.derivedPushforwardComparisonSquare
      (derivedAdjunction S.f'.toLRSHom.toShHom)
      (derivedAdjunction f''.toLRSHom.toShHom)
      (derivedAdjunction h.toLRSHom.toShHom)
      (derivedAdjunction h'.toLRSHom.toShHom)
      (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
        S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
      (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom S.f'.toLRSHom.toShHom)).naturality
    ((singleFunctor X''.Modules 0).map (X := (Scheme.Modules.pullback h').obj F')
      (Y := (Scheme.Modules.pullback h').obj F') φ)
  have q₂ := map_comp_square (homologyFunctor S.Y'.Modules (S.d : ℤ))
    (comp_two_squares (map_comp_square (derivedPushforward S.f'.toLRSHom.toShHom) qa) qb)
  have q₃ := (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).naturality
    ((derivedPushforward f''.toLRSHom.toShHom).map
      ((singleFunctor X''.Modules 0).map (X := (Scheme.Modules.pullback h').obj F')
        (Y := (Scheme.Modules.pullback h').obj F') φ))
  have q₄ := map_comp_square (Scheme.Modules.pushforward h)
    (homologyFunctorDerivedPushforwardIso_hom_naturality f''
      (F := (Scheme.Modules.pullback h').obj F') (G := (Scheme.Modules.pullback h').obj F') φ
      (S.d : ℤ))
  exact comp_two_squares q₁ (comp_two_squares q₂ (comp_two_squares q₃ q₄))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
