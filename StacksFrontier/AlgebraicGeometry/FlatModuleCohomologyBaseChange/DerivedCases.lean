module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.CechResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived comparison of flat base change in the cases already settled

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes and let `G` be a quasi-coherent `𝒪_{S'}`-module flat over `S`.
`AffineMorphism.lean` and `CechResolution.lean` prove the degreewise assertion of
[Stacks, Tag 0GN5] — invertibility of `Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)` — for an affine morphism
and for a quasi-compact separated morphism to an affine base.  Both proofs go through the
criterion of `AcyclicResolution.lean`, which produces invertibility of the *derived* comparison
`RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ` at `F[0]` and only afterwards takes cohomology.  This file records that
intermediate, stronger conclusion in both cases: it is the form in which a Mayer--Vietoris
argument can consume them, because a single morphism of the bounded below derived category is
what a triangle argument compares.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single_of_degreewise`:
  the criterion of `AcyclicResolution.lean` with the derived conclusion.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single_of_rightAcyclic`:
  the derived comparison is invertible at `F[0]` as soon as `F` is right acyclic for `f_*`, the
  underived comparison is invertible at `F` and `Ψ F` is right acyclic for `f'_*`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single_of_isAffineHom`:
  **the derived comparison is invertible at `F[0]` for an affine morphism.**
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single_of_isSeparated`:
  **the derived comparison is invertible at `F[0]` for a quasi-compact separated morphism to an
  affine base.**

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.Tag01XLDerivedIso

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **The criterion of `AcyclicResolution.lean` with the derived conclusion.**  Let `L` be a
bounded below complex of `𝒪_X`-modules whose image in `D⁺(X)` is `F[0]`, with `f_*L` computing
`Rf_*F`, with the underived comparison invertible at every term of `L` and with `Ψ` of every term
of `L` right acyclic for `f'_*`.  Then the derived comparison of [Stacks, Tag 0GN5] is invertible
at `F[0]`. -/
theorem isIso_derivedComparison_app_single_of_degreewise (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (e : DerivedCategory.Plus.Qh.obj L ≅
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnit.app L))
    (hiso : ∀ n : ℤ, IsIso ((underivedComparison H.w G).app (L.obj.as.X n)))
    (hac : ∀ n : ℤ, (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((totalCoefficients g' f' G).obj (L.obj.as.X n))) :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) :=
  isIso_derivedComparison_app_single_of_resolution H.w G hG F L e hL
    ((isIso_comparisonOnHomotopy_app_iff H G hG L).2
      (isIso_complexComparison H.w G L hiso hac))

/-- A property of objects that is invariant under isomorphism and holds for zero objects holds
for every term of the complex `F[0]` as soon as it holds for `F`. -/
private theorem property_single_obj_X {A : Type*} [Category A] [HasZeroObject A]
    [HasZeroMorphisms A] (P : A → Prop) (hiso : ∀ {X Y : A}, (X ≅ Y) → P X → P Y)
    (hz : ∀ {Z : A}, IsZero Z → P Z) (F : A) (hF : P F) (n : ℤ) :
    P (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F).X n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact hiso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm hF
  · exact hz (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn)

/-- **The derived comparison is invertible at `F[0]` when `F` itself computes both sides.**  The
complex is `F` placed in degree zero: its image in `D⁺(X)` is `F[0]`, and the three remaining
conditions of `isIso_derivedComparison_app_single_of_degreewise` are the three hypotheses in
degree zero and automatic in every other degree, the term there being a zero object. -/
theorem isIso_derivedComparison_app_single_of_rightAcyclic (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hFac : (modulePushforward f.toLRSHom.toShHom).rightAcyclic F)
    (hcmp : IsIso ((underivedComparison H.w G).app F))
    (hac : (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((totalCoefficients g' f' G).obj F)) :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  refine isIso_derivedComparison_app_single_of_degreewise H G hG F
    ((HomotopyCategory.Plus.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    ((Functor.singleFunctorPlusIsoCompQh
      (A := SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app F).symm ?_ ?_ ?_
  · refine Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n => ?_
    exact property_single_obj_X _
      (fun e => (modulePushforward f.toLRSHom.toShHom).rightAcyclic.prop_of_iso e)
      (fun hz => haveI := hz.injective; Functor.rightAcyclic_of_injective _ _) F hFac n
  · exact property_single_obj_X (fun X => IsIso ((underivedComparison H.w G).app X))
      (fun e => (NatTrans.isIso_app_iff_of_iso _ e).1)
      (fun hz => isIso_of_isZero (Functor.map_isZero _ hz) (Functor.map_isZero _ hz) _) F hcmp
  · exact property_single_obj_X
      (fun X => (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
        ((totalCoefficients g' f' G).obj X))
      (fun e => (modulePushforward f'.toLRSHom.toShHom).rightAcyclic.prop_of_iso
        ((totalCoefficients g' f' G).mapIso e))
      (fun hz => haveI := ((totalCoefficients g' f' G).map_isZero hz).injective
        Functor.rightAcyclic_of_injective _ _) F hac

/-- **The derived comparison of [Stacks, Tag 0GN5] is invertible at `F[0]` for an affine
morphism.**  This is the derived form of
`isIso_degreewiseComparison_app_of_isAffineHom`: `F` and `Ψ F` are quasi-coherent and `f` and
`f'` are affine, so both are right acyclic for the respective direct image
([Stacks, Tag 01XC]), and the underived comparison is invertible at `F`. -/
theorem isIso_derivedComparison_app_single_of_isAffineHom (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  have hFsm : _root_.SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F :=
    inferInstanceAs F.IsQuasicoherent
  exact isIso_derivedComparison_app_single_of_rightAcyclic H G hG F
    (AlgebraicGeometry.rightAcyclic_pushforward_of_isAffineHom f F)
    (isIso_underivedComparison_app_of_isAffineHom H G F)
    (rightAcyclic_totalCoefficients_of_isAffineHom H G F)

/-- **The derived comparison of [Stacks, Tag 0GN5] is invertible at `F[0]` through the Čech
resolution.**  This is the derived form of
`isIso_degreewiseComparison_app_of_affineOpenCover`: the absolute Čech resolution of a finite
affine open covering of a scheme of affine diagonal, over a base of affine diagonal, computes
both sides. -/
@[ega "III 7.7.2" "special case"]
theorem isIso_derivedComparison_app_single_of_affineOpenCover (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X))]
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S))]
    (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [hF : F.IsQuasicoherent] :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  let Fq : (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := ⟨F, hF⟩
  exact isIso_derivedComparison_app_single_of_degreewise H G hG F
    ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus T).obj Fq))
    ((absoluteCechResolutionIso T).app Fq).symm
    (isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus f T Fq)
    (isIso_underivedComparison_app_absoluteCechComplex H T G inferInstance Fq)
    (rightAcyclic_totalCoefficients_absoluteCechComplex H T G inferInstance Fq)

/-- **The derived comparison of [Stacks, Tag 0GN5] is invertible at `F[0]` for a quasi-compact
separated morphism to an affine base.**  This is the derived form of
`isIso_degreewiseComparison_app_of_isSeparated`. -/
theorem isIso_derivedComparison_app_single_of_isSeparated (H : IsPullback g' f' f g)
    [QuasiCompact f] [IsSeparated f] [IsAffine S]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  have : CompactSpace ↥X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have hsepS : IsSeparated (terminal.from S) := inferInstance
  have hsepX : IsSeparated (terminal.from X) := by
    have h : IsSeparated (f ≫ terminal.from S) := inferInstance
    simpa using h
  have : AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  have : AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S)) := inferInstance
  exact isIso_derivedComparison_app_single_of_affineOpenCover H (finiteAffineOpenCover X) G hG F

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
