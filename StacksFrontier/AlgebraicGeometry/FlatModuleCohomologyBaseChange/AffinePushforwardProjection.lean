module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AffinePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison at the direct image along an affine morphism

Let

```
Z' --k'--> Z
|i'        |i
X' --g'--> X
|f'        |f
S' --g---> S
```

be two cartesian squares of schemes stacked one above the other, with `i` and `i ≫ f` affine,
let `G` be a quasi-coherent `𝒪_{S'}`-module and let `M` be a quasi-coherent `𝒪_Z`-module. This
file proves that the underived comparison of [Stacks, Tag 0GN5] is invertible at `i_* M`, and
that `Ψ(i_* M)` is right acyclic for `f'_*`.

Neither statement holds at an arbitrary module. What makes `i_* M` special is that both `i` and
`i ≫ f` are affine, so that every morphism in sight can be read through the corresponding
morphism for those two affine morphisms:

* the base-change factor is `isIso_baseChangeNatTrans_app_pushforward`, the compatibility of the
  base-change morphism of [Stacks, Tag 02KG] with stacking the two squares;
* the projection-formula factor is `isIso_projectionFormulaMap_pushforward`, the compatibility of
  the projection-formula morphism of [Stacks, Tag 0FZE] with composition of the morphism,
  `AlgebraicGeometry.projectionFormulaSourceNatTrans_comp_whisker`: the projection formula along
  the composite `i' ≫ f'` factors through the projection formula for `f'` at `i'_*`, so that
  factor is invertible once the two for the affine morphisms `i'` and `i' ≫ f'` are;
* acyclicity is `Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_comp`,
  which is Leray's collapse for the pair `(i'_*, f'_*)`, after `Ψ(i_* M)` has been rewritten as
  a direct image along `i'` by base change and the projection formula for `i'`.

These are exactly the statements the Čech resolution of a quasi-coherent module by a finite
affine open cover consumes: its terms are direct images along the structure morphisms of the
intersections, which are affine as soon as `X` has affine diagonal, and whose composites with
`f` are affine as soon as `S` does.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_projectionFormulaMap_pushforward`: the
  projection-formula morphism of [Stacks, Tag 0FZE] for `f` is invertible at `j_* N` when `j` and
  `j ≫ f` are affine.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_underivedComparison_app_pushforward`: **the
  underived comparison is invertible at `i_* M`.**
* `Stacks.AlgebraicGeometry.ModuleBaseChange.rightAcyclic_totalCoefficients_pushforward`:
  **`Ψ(i_* M)` is right acyclic for `f'_*`.**

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The second of four composable morphisms is invertible when the composite is and the other
three are. -/
private theorem isIso_second_of_four {C : Type*} [Category* C] {V W Y₀ Y T : C} {a : V ⟶ W}
    {b : W ⟶ Y₀} {c : Y₀ ⟶ Y} {d : Y ⟶ T} {r : V ⟶ T} (heq : a ≫ b ≫ c ≫ d = r) (hr : IsIso r)
    (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) : IsIso b := by
  have : IsIso (a ≫ b ≫ c ≫ d) := heq ▸ hr
  rw [show b = inv a ≫ (a ≫ b ≫ c ≫ d) ≫ inv d ≫ inv c by simp]
  infer_instance

/-- The tensor product of two isomorphisms of sheaves of modules on a ringed space is an
isomorphism. The two `IsIso` facts are explicit arguments because instance search does not find
them across the two spellings of a sheaf of modules on a scheme. -/
private theorem isIso_tensorSheafMap_id_left {Z : AlgebraicGeometry.RingedSpace.{u, u}}
    {K L : SheafOfModules.{u} (structureSheafRing Z)} (ψ : K ⟶ L) (hψ : IsIso ψ)
    (N : SheafOfModules.{u} (structureSheafRing Z)) :
    IsIso ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map
        ((𝟙 N, ψ) : (N, K) ⟶ (N, L))) :=
  ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).mapIso
      (X := (N, K)) (Y := (N, L))
      (Iso.prod (Iso.refl N) (@asIso _ _ _ _ ψ hψ))).isIso_hom

/-! ### The projection formula at a direct image along an affine morphism -/

/-- **The projection-formula morphism of [Stacks, Tag 0FZE] at a direct image.**  For `j : Z ⟶ X`
and `f : X ⟶ S` with `j` and `j ≫ f` affine, `N` a quasi-coherent `𝒪_Z`-module and `H` a
quasi-coherent `𝒪_S`-module, the projection-formula morphism

`f_*(j_* N) ⊗_{𝒪_S} H ⟶ f_*(j_* N ⊗_{𝒪_X} f^*H)`

is invertible.  The morphism `f` itself is not assumed affine: by
`AlgebraicGeometry.projectionFormulaSourceNatTrans_comp_whisker` this morphism is, up to
invertible factors, a factor of the projection-formula morphism of the composite `j ≫ f`, the
other factor being the projection-formula morphism of `j`, and both of those are invertible
because `j ≫ f` and `j` are affine. -/
@[sga "3 VIB 11.5" "(a)"]
theorem isIso_projectionFormulaMap_pushforward {Z X S : Scheme.{u}} (j : Z ⟶ X) (f : X ⟶ S)
    [AlgebraicGeometry.IsAffineHom j] [AlgebraicGeometry.IsAffineHom (j ≫ f)] (N : Z.Modules)
    (hN : N.IsQuasicoherent) (H : S.Modules) (hH : H.IsQuasicoherent) :
    IsIso ((AlgebraicGeometry.projectionFormulaSourceNatTrans f H).app
      ((Scheme.Modules.pushforward j).obj N)) := by
  have key : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf).flip.obj H).map
          ((Scheme.Modules.pushforwardComp j f).inv.app N) ≫
        (AlgebraicGeometry.projectionFormulaSourceNatTrans f H).app
          ((Scheme.Modules.pushforward j).obj N) ≫
        (Scheme.Modules.pushforward f).map
          ((AlgebraicGeometry.projectionFormulaSourceNatTrans j
            ((Scheme.Modules.pullback f).obj H)).app N) ≫
        (Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward f).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.map
            ((Scheme.Modules.pullbackComp j f).hom.app H)).app N) =
      (AlgebraicGeometry.projectionFormulaSourceNatTrans (j ≫ f) H).app N ≫
        (Scheme.Modules.pushforwardComp j f).inv.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj
            ((Scheme.Modules.pullback (j ≫ f)).obj H)).obj N) :=
    congr_app (AlgebraicGeometry.projectionFormulaSourceNatTrans_comp_whisker j f H) N
  have hcomp : IsIso ((AlgebraicGeometry.projectionFormulaSourceNatTrans (j ≫ f) H).app N) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap (j ≫ f) N H hN hH
  have hunit : IsIso ((Scheme.Modules.pushforwardComp j f).inv.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj
        ((Scheme.Modules.pullback (j ≫ f)).obj H)).obj N)) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforwardComp j f).app _).inv)
  have hfirst : IsIso ((Scheme.Modules.pushforwardComp j f).inv.app N) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforwardComp j f).app N).inv)
  have ha : IsIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf).flip.obj H).map
        ((Scheme.Modules.pushforwardComp j f).inv.app N)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hfirst
  have hpfj : IsIso ((AlgebraicGeometry.projectionFormulaSourceNatTrans j
      ((Scheme.Modules.pullback f).obj H)).app N) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap j N
      ((Scheme.Modules.pullback f).obj H) hN (Stacks.Modules.isQuasicoherent_pullback f H hH)
  have hc : IsIso ((Scheme.Modules.pushforward f).map
      ((AlgebraicGeometry.projectionFormulaSourceNatTrans j
        ((Scheme.Modules.pullback f).obj H)).app N)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hpfj
  have hpsiTensor : IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Z.sheaf).flip.map
      ((Scheme.Modules.pullbackComp j f).hom.app H)).app N) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj N).mapIso
      ((Scheme.Modules.pullbackComp j f).app H)).isIso_hom
  have hd : IsIso ((Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward f).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.map
        ((Scheme.Modules.pullbackComp j f).hom.app H)).app N)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hpsiTensor
  exact isIso_second_of_four key (IsIso.comp_isIso' hcomp hunit) ha hc hd

/-! ### The comparison and acyclicity at a direct image along an affine morphism -/

section Stacked

variable {S S' X X' Z Z' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  {i : Z ⟶ X} {k' : Z' ⟶ Z} {i' : Z' ⟶ X'}

/-- In two stacked cartesian squares, `i'` and `i' ≫ f'` are affine when `i` and `i ≫ f` are. -/
private theorem isAffineHom_of_stacked (H : IsPullback g' f' f g) (Hi : IsPullback k' i' i g')
    [AlgebraicGeometry.IsAffineHom i] [AlgebraicGeometry.IsAffineHom (i ≫ f)] :
    AlgebraicGeometry.IsAffineHom i' ∧ AlgebraicGeometry.IsAffineHom (i' ≫ f') :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback Hi ‹_›,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (Hi.paste_vert H) ‹_›⟩

/-- **The underived comparison of [Stacks, Tag 0GN5] is invertible at a direct image along an
affine morphism.**  For two cartesian squares stacked one above the other with `i` and `i ≫ f`
affine, `G` a quasi-coherent `𝒪_{S'}`-module and `M` a quasi-coherent `𝒪_Z`-module, the
comparison `Φ(f_*N) ⟶ f'_*(ΨN)` is invertible at `N = i_* M`.

Its two factors are handled separately: the base-change factor by
`isIso_baseChangeNatTrans_app_pushforward`, and the projection-formula factor by
`isIso_projectionFormulaMap_pushforward` for the affine morphism `i'`, after `(g')^*(i_* M)` has
been identified with `i'_*((k')^*M)` by the base-change isomorphism of the upper square — which
is invertible because `i` is affine. -/
theorem isIso_underivedComparison_app_pushforward (H : IsPullback g' f' f g)
    (Hi : IsPullback k' i' i g') [AlgebraicGeometry.IsAffineHom i]
    [AlgebraicGeometry.IsAffineHom (i ≫ f)]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (hG : G.IsQuasicoherent)
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) (hM : M.IsQuasicoherent) :
    IsIso ((underivedComparison H.w G).app
      ((modulePushforward i.toLRSHom.toShHom).obj M)) := by
  obtain ⟨hi', hif'⟩ := isAffineHom_of_stacked H Hi
  have hMk : ((modulePullback k'.toLRSHom.toShHom).obj M).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ M
  have hMsm := isQuasicoherent_schemeModules M
  have hbciso : IsIso ((AffinePushforward.baseChangeNatTrans Hi.w).app M) :=
    AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom Hi M
  exact isIso_underivedComparison_app H.w G _
    (isIso_baseChangeNatTrans_app_pushforward H Hi M)
    ((CategoryTheory.NatTrans.isIso_app_iff_of_iso
      (AlgebraicGeometry.projectionFormulaSourceNatTrans f' G)
      (asIso ((AffinePushforward.baseChangeNatTrans Hi.w).app M))).mpr
      (isIso_projectionFormulaMap_pushforward i' f'
        ((modulePullback k'.toLRSHom.toShHom).obj M) (isQuasicoherent_schemeModules _) G
        (isQuasicoherent_schemeModules G)))

/-- **`Ψ(i_* M)` is right acyclic for `f'_*`.**  By base change along the affine morphism `i` and
the projection formula for the affine morphism `i'`, the module `Ψ(i_* M)` is the direct image
along `i'` of the quasi-coherent module `(k')^*M ⊗ (i')^*(f')^*G`; and `i'` and `i' ≫ f'` are
affine, being base changes of `i` and of `i ≫ f`, so Leray's collapse for the pair `(i'_*, f'_*)`
applies. -/
theorem rightAcyclic_totalCoefficients_pushforward (H : IsPullback g' f' f g)
    (Hi : IsPullback k' i' i g') [AlgebraicGeometry.IsAffineHom i]
    [AlgebraicGeometry.IsAffineHom (i ≫ f)]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (hG : G.IsQuasicoherent)
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) (hM : M.IsQuasicoherent) :
    (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((totalCoefficients g' f' G).obj ((modulePushforward i.toLRSHom.toShHom).obj M)) := by
  obtain ⟨hi', hif'⟩ := isAffineHom_of_stacked H Hi
  have hMk : ((modulePullback k'.toLRSHom.toShHom).obj M).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ M
  have hGf' : ((modulePullback f'.toLRSHom.toShHom).obj G).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ G
  have hGi' : ((modulePullback i'.toLRSHom.toShHom).obj
      ((modulePullback f'.toLRSHom.toShHom).obj G)).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
  let tensorModule : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z'.sheaf) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.sheaf).obj
      ((modulePullback k'.toLRSHom.toShHom).obj M)).obj
        ((modulePullback i'.toLRSHom.toShHom).obj ((modulePullback f'.toLRSHom.toShHom).obj G))
  have hW : tensorModule.IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent Z'.toRingedSpace _ _ hMk hGi'
  have hMsm := isQuasicoherent_schemeModules M
  have hWsm := @isQuasicoherent_schemeModules Z' tensorModule hW
  have hbciso : IsIso ((AffinePushforward.baseChangeNatTrans Hi.w).app M) :=
    AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom Hi M
  have hpf : IsIso (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap i'
      ((modulePullback k'.toLRSHom.toShHom).obj M)
      ((modulePullback f'.toLRSHom.toShHom).obj G)) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap i'
      ((modulePullback k'.toLRSHom.toShHom).obj M)
      ((modulePullback f'.toLRSHom.toShHom).obj G) (@isQuasicoherent_schemeModules Z' _ hMk)
      (@isQuasicoherent_schemeModules X' _ hGf')
  let baseChangeIso :
      (modulePullback g'.toLRSHom.toShHom).obj ((modulePushforward i.toLRSHom.toShHom).obj M) ≅
        (modulePushforward i'.toLRSHom.toShHom).obj ((modulePullback k'.toLRSHom.toShHom).obj M) :=
    @asIso _ _ _ _ ((AffinePushforward.baseChangeNatTrans Hi.w).app M) hbciso
  have e : (totalCoefficients g' f' G).obj ((modulePushforward i.toLRSHom.toShHom).obj M) ≅
      (modulePushforward i'.toLRSHom.toShHom).obj tensorModule :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj
      ((modulePullback f'.toLRSHom.toShHom).obj G)).mapIso
        (X := (modulePullback g'.toLRSHom.toShHom).obj
          ((modulePushforward i.toLRSHom.toShHom).obj M))
        (Y := (modulePushforward i'.toLRSHom.toShHom).obj
          ((modulePullback k'.toLRSHom.toShHom).obj M)) baseChangeIso ≪≫
      @Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIso
        Z' X' i' ((modulePullback k'.toLRSHom.toShHom).obj M)
        ((modulePullback f'.toLRSHom.toShHom).obj G) hpf
  exact (modulePushforward f'.toLRSHom.toShHom).rightAcyclic.prop_of_iso e.symm
    (Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_comp i' f' tensorModule)

end Stacked

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
