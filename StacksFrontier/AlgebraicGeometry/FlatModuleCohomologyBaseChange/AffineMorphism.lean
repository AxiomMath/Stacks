module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AcyclicResolution
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# The comparison of flat base change for an affine morphism

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` affine, let `F` be a quasi-coherent `𝒪_X`-module and
let `G` be a quasi-coherent `𝒪_{S'}`-module flat over `S`. This file proves that the degreewise
comparison of `DegreewiseComparison.lean`,

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`,

is invertible in every degree `i`. No hypothesis on `S`, `S'` or `X` is used.

The complex computing both sides is `F` itself, placed in degree zero: the criterion
`Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_degreewise` asks for
a bounded below complex resolving `F`, whose direct image computes `Rf_*F` and whose terms carry
the underived comparison and have `f'_*`-acyclic image under `Ψ`, and for an affine morphism the
single complex has all four properties:

* its image in `D⁺(X)` is `F[0]` by construction;
* `F` is right acyclic for `f_*` because the higher direct images of a quasi-coherent module
  along an affine morphism vanish ([Stacks, Tag 01XC]);
* the underived comparison is invertible at `F` because both of its factors are — the
  base-change morphism of [Stacks, Tag 02KG] because `f` is affine and `F` quasi-coherent, and
  the projection-formula morphism of [Stacks, Tag 0FZE] because `f'` is affine, being a base
  change of `f`, and both of its arguments are quasi-coherent;
* `Ψ F` is quasi-coherent, being a tensor product of inverse images of quasi-coherent modules
  ([Stacks, Tag 01BG] and [Stacks, Tag 01CE]), so it too is right acyclic for `f'_*`.

The remaining terms of the single complex are zero objects, where every one of the four
conditions is automatic.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_underivedComparison_app_of_isAffineHom`: the
  underived comparison is invertible at a quasi-coherent module when `f` is affine.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.rightAcyclic_totalCoefficients_of_isAffineHom`:
  `Ψ F` is right acyclic for `f'_*` when `f` is affine and `F` and `G` are quasi-coherent.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_isAffineHom`:
  **the comparison of [Stacks, Tag 0GN5] is invertible for an affine morphism**, in every
  degree.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- A morphism between zero objects is invertible. -/
theorem isIso_of_isZero {C : Type*} [Category* C] {A B : C} (hA : IsZero A)
    (hB : IsZero B) (m : A ⟶ B) : IsIso m := by
  rw [hA.eq_of_src m (hA.iso hB).hom]
  infer_instance

/-- Quasi-coherence read at the `Scheme.Modules` spelling of a sheaf of modules. The two
spellings of the structure sheaf of a scheme are definitionally equal, but instance search does
not cross between them. -/
theorem isQuasicoherent_schemeModules {Y : Scheme.{u}}
    (M : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) [h : M.IsQuasicoherent] :
    _root_.SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M := h

/-! ### The two factors of the underived comparison -/

/-- A base change of an affine morphism is affine. -/
private theorem isAffineHom_of_isPullback (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom f] : AlgebraicGeometry.IsAffineHom f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback H ‹_›

/-- **The underived comparison is invertible at a quasi-coherent module when `f` is affine.**
Its two factors are the base-change morphism of [Stacks, Tag 02KG], invertible because `f` is
affine and `F` is quasi-coherent, and the projection-formula morphism of [Stacks, Tag 0FZE],
invertible because `f'` is affine and both its arguments are quasi-coherent. -/
theorem isIso_underivedComparison_app_of_isAffineHom (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsIso ((underivedComparison H.w G).app F) := by
  have := isAffineHom_of_isPullback H
  have hpull : ((modulePullback g'.toLRSHom.toShHom).obj F).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ F
  have hFsm := isQuasicoherent_schemeModules F
  refine isIso_underivedComparison_app H.w G F ?_ ?_
  · exact AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom H F
  · exact Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap f'
      ((modulePullback g'.toLRSHom.toShHom).obj F) G
      (isQuasicoherent_schemeModules _) (isQuasicoherent_schemeModules G)

/-! ### Acyclicity of the two sides -/

/-- The coefficient module upstairs is quasi-coherent: it is a tensor product
([Stacks, Tag 01CE]) of inverse images of quasi-coherent modules ([Stacks, Tag 01BG]). -/
theorem isQuasicoherent_totalCoefficients_obj (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    ((totalCoefficients g' f' G).obj F).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X'.toRingedSpace _ _
    (AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ F)
    (AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ G)

/-- **`Ψ F` is right acyclic for `f'_*` when `f` is affine.** The morphism `f'` is affine, being
a base change of `f`, and `Ψ F` is quasi-coherent, so its higher direct images vanish
([Stacks, Tag 01XC]). -/
theorem rightAcyclic_totalCoefficients_of_isAffineHom (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    (modulePushforward f'.toLRSHom.toShHom).rightAcyclic ((totalCoefficients g' f' G).obj F) := by
  have := isAffineHom_of_isPullback H
  have := isQuasicoherent_totalCoefficients_obj g' f' G F
  have := isQuasicoherent_schemeModules ((totalCoefficients g' f' G).obj F)
  exact AlgebraicGeometry.rightAcyclic_pushforward_of_isAffineHom f'
    ((totalCoefficients g' f' G).obj F)

/-! ### The comparison for an affine morphism -/

/-- **The comparison of [Stacks, Tag 0GN5] is invertible for an affine morphism.** For a
cartesian square with `f` affine, a quasi-coherent `𝒪_X`-module `F` and a quasi-coherent
`𝒪_{S'}`-module `G` flat over `S`, the degreewise comparison

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`

is invertible in every degree `i`. No hypothesis on the schemes of the square is used.

The complex computing both sides is `F` placed in degree zero: its image in `D⁺(X)` is `F[0]`,
`F` is right acyclic for `f_*` ([Stacks, Tag 01XC]), the underived comparison is invertible at
`F` and `Ψ F` is right acyclic for `f'_*`. In every other degree the term is a zero object, and
all four conditions are automatic there. -/
theorem isIso_degreewiseComparison_app_of_isAffineHom (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom f]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) := by
  have hFsm := isQuasicoherent_schemeModules F
  have hFac : (modulePushforward f.toLRSHom.toShHom).rightAcyclic F :=
    AlgebraicGeometry.rightAcyclic_pushforward_of_isAffineHom f F
  have hz : ∀ n : ℤ, n ≠ 0 → IsZero (((HomotopyCategory.Plus.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F).obj.as.X n) :=
    fun n hn => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn
  refine isIso_degreewiseComparison_app_of_degreewise H G hG F
    ((HomotopyCategory.Plus.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    ((Functor.singleFunctorPlusIsoCompQh
      (A := SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app F).symm ?_ ?_ ?_ i
  · refine Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · exact (modulePushforward f.toLRSHom.toShHom).rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm hFac
    · have := (hz n hn).injective
      exact Functor.rightAcyclic_of_injective _ _
  · intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact (CategoryTheory.NatTrans.isIso_app_iff_of_iso (underivedComparison H.w G)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F)).mpr
        (isIso_underivedComparison_app_of_isAffineHom H G F)
    · exact isIso_of_isZero (Functor.map_isZero _ (hz n hn)) (Functor.map_isZero _ (hz n hn)) _
  · intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact (modulePushforward f'.toLRSHom.toShHom).rightAcyclic.prop_of_iso
        ((totalCoefficients g' f' G).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm)
        (rightAcyclic_totalCoefficients_of_isAffineHom H G F)
    · have := (Functor.map_isZero (totalCoefficients g' f' G) (hz n hn)).injective
      exact Functor.rightAcyclic_of_injective _ _

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
