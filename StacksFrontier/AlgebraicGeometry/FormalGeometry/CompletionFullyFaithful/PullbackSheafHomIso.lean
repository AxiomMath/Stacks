module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PullbackSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of Tag 0GMX is an isomorphism for a finite locally free source

Let `f : W ⟶ Z` be a morphism of schemes, let `G`, `F` be `𝒪_Z`-modules and suppose `G` is
finite locally free. Then the canonical comparison

`f^* ℋom_{𝒪_Z}(G, F) ⟶ ℋom_{𝒪_W}(f^* G, f^* F)`

of `Stacks.Algebraization.pullbackSheafHomMap` is an isomorphism. This is the clause of
[Stacks, Tag 0GMX] that the finite locally free case of [Stacks, Tag 0GN2] asserts, proved for a
morphism of schemes with no flatness hypothesis: a finite locally free module has finite free
stalks, and base change commutes with taking linear maps out of a finite free module.

## Main results

* `Stacks.Algebraization.bijective_of_hom_baseChange` — the linear algebra: for `V` finite free
  over `R` and `S` an `R`-algebra, a map out of a model of `S ⊗_R (V →ₗ[R] N)` which is
  evaluation on pure tensors is bijective. This is the general-target form of
  `Stacks.Chow.bijective_of_dual_baseChange`, which is the case `N = R`.
* `Stacks.Algebraization.sheafHomStalkEquiv` and
  `Stacks.Algebraization.sheafHomStalkEquiv_germAt` — [Stacks, Tag 01CP] for the internal hom of
  two modules on a scheme, read at the spelling
  `(Stacks.Algebraization.sheafHomFunctor Z G).obj F` that the comparison is stated at. This is
  the general-target form of `Stacks.AlgebraicGeometry.ReflexiveModules.dualStalkEquiv`.
* `Stacks.Algebraization.pullbackSheafHomMap_sheafHomStalkEquiv_germ` — the comparison computed
  on the germs of the canonical images of a local section of `ℋom(G, F)` and a local section of
  `G`. It is `Stacks.Algebraization.pullbackSheafHomMap_unit_eval` read through the stalk
  description of the internal hom.
* `Stacks.Algebraization.isIso_pullbackSheafHomMap` — **the comparison is an isomorphism.**

## Implementation notes

The argument is the one of `Stacks.Chow.pullbackDualMap_isIso`, which is the case `F = 𝒪_Z`, with
the target kept general: invertibility is checked stalkwise with
`Stacks.AlgebraicGeometry.ReflexiveModules.isIso_of_bijective_stalkHom`, the stalk of a pullback
is `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, the stalk of the internal
hom is Tag 01CP, finite freeness of the stalk of `G` is
`Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree`, and the algebra is
`IsBaseChange.linearMapLeftRight`.

The stalk and module structures are spelled as in `Stacks.Chow.pullbackDualMap_isIso`: the local
`let _` instances put the module structure on each stalk at the `Z.presheaf`/`W.presheaf`
spelling, which is the one the pullback stalk formula is stated at, and
`Stacks.Algebraization.sheafHomStalkEquiv` is stated with its source and target written as
`TopCat.Presheaf.stalk _.val.presheaf` rather than as
`Stacks.SheafOfModules.SheafHomStalk.modStalk`, since instance search does not find the module
structure through the latter. `Module.Free` and `Module.Finite` of the stalk of `G` are handed to
the algebra lemma positionally for the same reason.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.ReflexiveModules
open scoped TensorProduct

universe u

namespace Stacks.Algebraization

/-- Linear algebra behind the comparison: for `V` finite free over `R` and `S` an `R`-algebra, a
map from a model of `S ⊗_R (V →ₗ[R] N)` to the module of `S`-linear maps between models of
`S ⊗_R V` and `S ⊗_R N` which is evaluation on pure tensors is bijective, because base change
commutes with taking linear maps out of a finite free module. -/
public theorem bijective_of_hom_baseChange
    {R S V N A B D : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCommGroup N] [Module R N]
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup D] [Module S D]
    (eV : A ≃ₗ[S] S ⊗[R] V) (eN : B ≃ₗ[S] S ⊗[R] N)
    (eD : D ≃ₗ[S] S ⊗[R] (V →ₗ[R] N))
    (k : D →ₗ[S] (A →ₗ[S] B))
    (h : ∀ (l : V →ₗ[R] N) (v : V),
      k (eD.symm (1 ⊗ₜ[R] l)) (eV.symm (1 ⊗ₜ[R] v)) = eN.symm (1 ⊗ₜ[R] l v)) :
    Function.Bijective k := by
  have jV : IsBaseChange S (TensorProduct.mk R S V 1) := TensorProduct.isBaseChange R V S
  have jN : IsBaseChange S (TensorProduct.mk R S N 1) := TensorProduct.isBaseChange R N S
  let e : D ≃ₗ[S] (A →ₗ[S] B) :=
    eD ≪≫ₗ (jV.linearMapLeftRight jN).equiv ≪≫ₗ LinearEquiv.arrowCongr eV.symm eN.symm
  have hgen : ∀ (l : V →ₗ[R] N), k (eD.symm (1 ⊗ₜ[R] l)) = e (eD.symm (1 ⊗ₜ[R] l)) := by
    intro l
    have hc : (k (eD.symm (1 ⊗ₜ[R] l))).comp eV.symm.toLinearMap =
        (e (eD.symm (1 ⊗ₜ[R] l))).comp eV.symm.toLinearMap := by
      refine jV.algHom_ext _ _ fun v => ?_
      refine (h l v).trans ?_
      have he : e (eD.symm (1 ⊗ₜ[R] l)) (eV.symm (1 ⊗ₜ[R] v)) = eN.symm (1 ⊗ₜ[R] l v) := by
        simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm]
        rw [IsBaseChange.equiv_tmul, one_smul]
        exact congrArg eN.symm
          (IsBaseChange.linearMapLeftRightHom_comp_apply jV (TensorProduct.mk R S N 1) l v)
      exact he.symm
    exact (LinearMap.cancel_right eV.symm.surjective).1 hc
  have hk : k = e.toLinearMap := by
    exact (LinearMap.cancel_right eD.symm.surjective).1
      ((TensorProduct.isBaseChange R (V →ₗ[R] N) S).algHom_ext _ _ hgen)
  rw [hk]
  exact e.bijective

variable {Z W : Scheme.{u}}

/-- **[Stacks, Tag 01CP] for the internal hom of two modules on a scheme.** For `G` of finite
presentation the stalk of `ℋom(G, F)` at `x` is the module of `𝒪_{Z,x}`-linear maps
`G_x →ₗ F_x`.

This is `Stacks.SheafOfModules.internalHomSheafStalkEquiv` read at the spelling
`(Stacks.Algebraization.sheafHomFunctor Z G).obj F` of the internal hom and at the spelling
`Z.presheaf.stalk x` of the local ring, which are the ones the comparison of [Stacks, Tag 0GMX]
and the pullback stalk formula of [Stacks, Tag 0098] are stated at. -/
@[ega "0 5.2.6" "special case"]
public def sheafHomStalkEquiv (G F : Z.Modules) [G.IsFinitePresentation] (x : Z) :
    ToType (TopCat.Presheaf.stalk ((sheafHomFunctor Z G).obj F).val.presheaf x) ≃ₗ[
        ToType (Z.presheaf.stalk x)]
      (ToType (TopCat.Presheaf.stalk G.val.presheaf x) →ₗ[ToType (Z.presheaf.stalk x)]
        ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
  Stacks.SheafOfModules.internalHomSheafStalkEquiv Z.sheaf G F x

/-- The germ formula for `Stacks.Algebraization.sheafHomStalkEquiv`. -/
public theorem sheafHomStalkEquiv_germAt (G F : Z.Modules) [G.IsFinitePresentation] (x : Z)
    (U : Z.Opens) (hxU : x ∈ U) (s : ((sheafHomFunctor Z G).obj F).val.obj (op U))
    (m : Γ(G, U)) :
    sheafHomStalkEquiv G F x (germAt ((sheafHomFunctor Z G).obj F) U x hxU s)
        (germAt G U x hxU m) =
      germAt F U x hxU ((s.app (op (Over.mk (𝟙 U)))).hom m) :=
  Stacks.SheafOfModules.internalHomSheafStalkEquiv_germ Z.sheaf G F x U hxU s m

/-- **The comparison of [Stacks, Tag 0GMX], read through the stalk description of an internal
hom of [Stacks, Tag 01CP].** On the germs of the canonical images of a local section of
`ℋom(G, F)` and of a local section of `G` it is the germ of the canonical image of the value. -/
public theorem pullbackSheafHomMap_sheafHomStalkEquiv_germ (f : W ⟶ Z) (G F : Z.Modules)
    [G.IsFinitePresentation]
    (hPfp : ((Scheme.Modules.pullback f).obj G).IsFinitePresentation)
    (x : W) (U : Z.Opens) (hxU : f.base x ∈ U)
    (s : ((sheafHomFunctor Z G).obj F).val.obj (op U)) (m : Γ(G, U)) :
    @sheafHomStalkEquiv W ((Scheme.Modules.pullback f).obj G)
        ((Scheme.Modules.pullback f).obj F) hPfp x
        (stalkHom (pullbackSheafHomMap f G F) x
          (germAt (Rc := W.sheaf)
            ((Scheme.Modules.pullback f).obj ((sheafHomFunctor Z G).obj F)) (f ⁻¹ᵁ U) x hxU
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              ((sheafHomFunctor Z G).obj F)).val.app (op U) s)))
        (germAt (Rc := W.sheaf) ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U) x hxU
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op U) m)) =
      germAt (Rc := W.sheaf) ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ U) x hxU
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U)
          ((s.app (op (Over.mk (𝟙 U)))).hom m)) := by
  have h1 := stalkHom_germAt (pullbackSheafHomMap f G F) x (f ⁻¹ᵁ U) hxU
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((sheafHomFunctor Z G).obj F)).val.app (op U) s)
  have h2 := @sheafHomStalkEquiv_germAt W ((Scheme.Modules.pullback f).obj G)
    ((Scheme.Modules.pullback f).obj F) hPfp x (f ⁻¹ᵁ U) hxU
    (Scheme.Modules.Hom.app (pullbackSheafHomMap f G F) (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((sheafHomFunctor Z G).obj F)).val.app (op U) s))
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op U) m)
  refine Eq.trans (congrArg (fun z => @sheafHomStalkEquiv W _ _ hPfp x z
    (germAt (Rc := W.sheaf) ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U) x hxU
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op U) m))) h1) ?_
  exact h2.trans <| congrArg
    (germAt (Rc := W.sheaf) ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ U) x hxU)
    (pullbackSheafHomMap_unit_eval f G F U s m)

/-- **The comparison of [Stacks, Tag 0GMX] is an isomorphism when its source is finite locally
free**, `f^* ℋom(G, F) ≅ ℋom(f^* G, f^* F)`.

Invertibility is checked on stalks. The stalk of a pullback is the base change of the stalk
([Stacks, Tag 0098]), the stalk of an internal hom with a finitely presented source is the
module of linear maps between the stalks ([Stacks, Tag 01CP]), and the stalk of `G` is a finite
free module over the local ring, for which base change commutes with taking linear maps out of
it. -/
@[ega "0 6.7.6" "special case", sga "3 I 4.6.5" "more general", sga "3 III 0.14" "special case"]
public theorem isIso_pullbackSheafHomMap (f : W ⟶ Z) (G F : Z.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    IsIso (pullbackSheafHomMap f G F) := by
  have : G.IsFinitePresentation :=
    Stacks.Chow.isFinitePresentation_of_isFiniteLocallyFree G hG
  have hPfp : ((Scheme.Modules.pullback f).obj G).IsFinitePresentation :=
    Stacks.Chow.isFinitePresentation_of_isFiniteLocallyFree _
      (Stacks.Chow.isFiniteLocallyFree_pullback f G hG)
  refine isIso_of_bijective_stalkHom (pullbackSheafHomMap f G F) fun x => ?_
  set y := (f.toLRSHom.toShHom).hom.base x
  let HZ := (sheafHomFunctor Z G).obj F
  let GW := (modulePullback f.toLRSHom.toShHom).obj G
  let FW := (modulePullback f.toLRSHom.toShHom).obj F
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Z.presheaf) G.val y
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Z.presheaf) F.val y
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Z.presheaf) HZ.val y
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := W.presheaf) GW.val x
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := W.presheaf) FW.val x
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := W.presheaf) ((modulePullback f.toLRSHom.toShHom).obj HZ).val x
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := W.presheaf) ((sheafHomFunctor W GW).obj FW).val x
  obtain ⟨hfree', hfinite'⟩ : Module.Free (ToType (Z.presheaf.stalk y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y)) ∧
    Module.Finite (ToType (Z.presheaf.stalk y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y)) :=
    Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree G y
  let algInst : Algebra (Z.presheaf.stalk y) (W.presheaf.stalk x) :=
    ((f.toLRSHom.toShHom).hom.stalkMap x).hom.toAlgebra
  obtain ⟨eG, heG⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    f.toLRSHom.toShHom G x
  obtain ⟨eF, heF⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    f.toLRSHom.toShHom F x
  obtain ⟨eH, heH⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    f.toLRSHom.toShHom HZ x
  let e := eH ≪≫ₗ (sheafHomStalkEquiv G F y).baseChange
    (Z.presheaf.stalk y) (W.presheaf.stalk x) _ _
  have hk : Function.Bijective (fun d =>
      (@sheafHomStalkEquiv W GW FW hPfp x) (stalkHom (pullbackSheafHomMap f G F) x d)) := by
    refine @bijective_of_hom_baseChange _ _ _ _ _ _ _ _ _ _ _ _ hfree' hfinite'
      _ _ _ _ _ _ _ _ eG eF e
      { toFun := fun d =>
          (@sheafHomStalkEquiv W GW FW hPfp x) (stalkHom (pullbackSheafHomMap f G F) x d)
        map_add' := fun d d' =>
          (congrArg (@sheafHomStalkEquiv W GW FW hPfp x)
            (map_add (stalkHom (pullbackSheafHomMap f G F) x) d d')).trans
            (map_add (@sheafHomStalkEquiv W GW FW hPfp x) _ _)
        map_smul' := fun r d =>
          (congrArg (@sheafHomStalkEquiv W GW FW hPfp x)
            (LinearMap.map_smul (stalkHom (pullbackSheafHomMap f G F) x) r d)).trans
            (LinearEquiv.map_smul (@sheafHomStalkEquiv W GW FW hPfp x) r _) } ?_
    intro l v
    obtain ⟨U, hxU, s, hs⟩ := exists_germ_eq HZ ((sheafHomStalkEquiv G F y).symm l)
    obtain ⟨V, hVU, hxV, t, ht⟩ := TopCat.Presheaf.exists_le_germ_eq
      (Stacks.SheafOfModules.SheafHomStalk.commVal G).presheaf v hxU
    have hsV : sheafHomStalkEquiv G F y (germAt HZ V y hxV (resLE HZ hVU s)) = l :=
      (congrArg (sheafHomStalkEquiv G F y)
          ((germAt_resLE HZ hVU hxV s).trans hs)).trans
        ((sheafHomStalkEquiv G F y).apply_symm_apply l)
    have hd : e.symm (1 ⊗ₜ[ToType (Z.presheaf.stalk y)] l) =
        germAt (Rc := W.sheaf) ((Scheme.Modules.pullback f).obj HZ) (f ⁻¹ᵁ V) x hxV
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app HZ).val.app (op V)
            (resLE HZ hVU s)) := by
      refine e.injective ((e.apply_symm_apply _).trans ?_)
      refine Eq.symm (((congrArg ((sheafHomStalkEquiv G F y).baseChange
        (Z.presheaf.stalk y) (W.presheaf.stalk x) _ _) (heH V hxV (resLE HZ hVU s))).trans
          (LinearEquiv.baseChange_tmul _ _ _ _ _ _)).trans (congrArg _ hsV))
    have hm : eG.symm (1 ⊗ₜ[ToType (Z.presheaf.stalk y)] v) =
        germAt (Rc := W.sheaf) ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) x hxV
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op V) t) :=
      eG.injective ((eG.apply_symm_apply _).trans ((heG V hxV t).trans (congrArg _ ht)).symm)
    have hlv : sheafHomStalkEquiv G F y (germAt HZ V y hxV (resLE HZ hVU s))
        (germAt G V y hxV t) = l v :=
      (LinearMap.congr_fun hsV _).trans (congrArg l ht)
    have hval := (sheafHomStalkEquiv_germAt G F y V hxV (resLE HZ hVU s) t).symm.trans hlv
    refine Eq.trans (congrArg (fun d =>
      (@sheafHomStalkEquiv W GW FW hPfp x) (stalkHom (pullbackSheafHomMap f G F) x d)
        (eG.symm (1 ⊗ₜ[ToType (Z.presheaf.stalk y)] v))) hd) ?_
    refine Eq.trans (congrArg (fun w =>
      (@sheafHomStalkEquiv W GW FW hPfp x) (stalkHom (pullbackSheafHomMap f G F) x
        (germAt (Rc := W.sheaf) ((Scheme.Modules.pullback f).obj HZ) (f ⁻¹ᵁ V) x hxV
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app HZ).val.app (op V)
            (resLE HZ hVU s)))) w) hm) ?_
    refine (pullbackSheafHomMap_sheafHomStalkEquiv_germ f G F hPfp x V hxV
      (resLE HZ hVU s) t).trans ?_
    exact (eF.eq_symm_apply).2 ((heF V hxV _).trans (congrArg (fun z => 1 ⊗ₜ z) hval))
  exact ((@sheafHomStalkEquiv W GW FW hPfp x).bijective.of_comp_iff'
    (stalkHom (pullbackSheafHomMap f G F) x)).mp hk

end Stacks.Algebraization

end
