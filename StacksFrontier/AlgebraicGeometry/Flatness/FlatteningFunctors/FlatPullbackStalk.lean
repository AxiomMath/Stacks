module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injectivity, surjectivity and vanishing of a module homomorphism after a flat pullback

Let `f : X ⟶ Y` be a flat morphism of schemes and let `φ : M ⟶ N` be a homomorphism of
quasi-coherent `𝒪_Y`-modules.  For `x : X` the stalk of `f^*M` at `x` is the extension of
scalars `𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} M_{f(x)}`, and `𝒪_{Y,f(x)} → 𝒪_{X,x}` is a flat local
homomorphism, hence faithfully flat.  Therefore the stalk of `f^*φ` at `x` is injective,
surjective, or zero exactly when the stalk of `φ` at `f(x)` is.

Combined with the stalkwise criteria for monomorphy and epimorphy
(`AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap` and
`AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap`) this says that pulling a
homomorphism back along a flat morphism preserves monomorphisms, and that it reflects all three
properties along a family of flat morphisms that is jointly surjective on points.

## Main results

* `AlgebraicGeometry.SheafOfModules.eq_zero_iff_stalkMap_apply_eq_zero`: a homomorphism of
  sheaves of modules vanishes exactly when all of its stalk maps do.
* `AlgebraicGeometry.injective_stalkMap_modulePullback_iff`,
  `AlgebraicGeometry.surjective_stalkMap_modulePullback_iff` and
  `AlgebraicGeometry.stalkMap_modulePullback_eq_zero_iff`: the three transfer statements for the
  stalk of a pullback along a flat morphism of schemes.
* `AlgebraicGeometry.Scheme.Modules.mono_pullback_map_of_flat`: the pullback functor along a flat
  morphism of schemes preserves monomorphisms of quasi-coherent modules.

## Implementation notes

The stalk of a homomorphism of sheaves of modules is written
`AlgebraicGeometry.SheafOfModules.stalkMap`, whose scalars are the stalk of the sheaf of rings
taken in `RingCat`.  The extension-of-scalars argument needs the scalars in `CommRingCat`
instead, where the `Algebra` instance lives; that spelling is
`Stacks.ModuleSkyscraper.stalkMapLinear`.  The two have the same underlying function, so the
criteria above are stated with the former and the transfer argument runs with the latter.

The identification of the stalk of a pullback with an extension of scalars is
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, which is stated for
morphisms of ringed spaces; the heart of this file is therefore a statement about ringed spaces,
specialised to schemes afterwards.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ModuleSkyscraper RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {Z : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- A homomorphism of sheaves of modules is zero exactly when every one of its stalk maps is
zero.  This is the vanishing companion of `mono_iff_injective_stalkMap` and
`epi_iff_surjective_stalkMap`. -/
theorem eq_zero_iff_stalkMap_apply_eq_zero {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N) :
    f = 0 ↔ ∀ (x : Z) m, (stalkMap O x f).hom m = 0 := by
  constructor
  · rintro rfl x m
    show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf O.obj).map (0 : M.val ⟶ N.val))).hom m = 0
    simp only [Functor.map_zero]
    rfl
  · intro h
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext s
    refine TopCat.Presheaf.section_ext ((_root_.SheafOfModules.toSheaf O).obj N) U.unop _ _
      fun x hx ↦ ?_
    have hz : (TopCat.Presheaf.germ N.val.presheaf U.unop x hx).hom ((f.val.app U).hom s) = 0 :=
      (stalkMap_germ O x f U.unop hx s).symm.trans (h x _)
    exact hz.trans (map_zero _).symm

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry

/-- Transfer of injectivity, surjectivity and vanishing of a stalk map of sheaves of modules
along the identification of the stalk of a pullback with an extension of scalars, when that
extension of scalars is faithfully flat.  All three statements are proved together because they
share the construction of the identification. -/
private theorem modulePullback_stalkMapLinear_transfer
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G H : _root_.SheafOfModules.{u} (structureSheafRing Y)) (φ : G ⟶ H) (x : X)
    (hff : RingHom.FaithfullyFlat (f.hom.stalkMap x).hom) :
    (Function.Injective (stalkMapLinear (R := X.presheaf)
        (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
        ((modulePullback f).map φ).val x) ↔
      Function.Injective (stalkMapLinear (R := Y.presheaf)
        (M := G.val) (N := H.val) φ.val (f.hom.base x))) ∧
    (Function.Surjective (stalkMapLinear (R := X.presheaf)
        (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
        ((modulePullback f).map φ).val x) ↔
      Function.Surjective (stalkMapLinear (R := Y.presheaf)
        (M := G.val) (N := H.val) φ.val (f.hom.base x))) ∧
    ((∀ n, stalkMapLinear (R := X.presheaf)
        (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
        ((modulePullback f).map φ).val x n = 0) ↔
      ∀ m, stalkMapLinear (R := Y.presheaf)
        (M := G.val) (N := H.val) φ.val (f.hom.base x) m = 0) := by
  let R := Y.presheaf.stalk (f.hom.base x)
  let S := X.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf (f.hom.base x)
  let M' := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) H.val.presheaf (f.hom.base x)
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    ((modulePullback f).obj G).val.presheaf x
  let _ : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val (f.hom.base x)
  let _ : Module R M' :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) H.val (f.hom.base x)
  let _ : Module S N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((modulePullback f).obj G).val x
  let _ : Module S (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((modulePullback f).obj H).val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((modulePullback f).obj H).val x
  let _ : Algebra R S := (f.hom.stalkMap x).hom.toAlgebra
  have hffm : Module.FaithfullyFlat R S := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    simpa [RingHom.algebraMap_toAlgebra] using hff
  obtain ⟨E, hE⟩ := exists_modulePullbackStalkLinearEquiv f G x
  obtain ⟨E', hE'⟩ := exists_modulePullbackStalkLinearEquiv f H x
  set a := stalkMapLinear (R := Y.presheaf) (M := G.val) (N := H.val) φ.val (f.hom.base x)
  set b := stalkMapLinear (R := X.presheaf)
    (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
    ((modulePullback f).map φ).val x
  let qS : TensorProduct R S M →ₗ[S] TensorProduct R S M' := LinearMap.baseChange S a
  let lhs : TensorProduct R S M →ₗ[S] TensorProduct R S M' :=
    E'.toLinearMap.comp (b.comp E.symm.toLinearMap)
  have hgen : ∀ m : M, lhs (1 ⊗ₜ[R] m) = qS (1 ⊗ₜ[R] m) := by
    intro m
    obtain ⟨V, hxV, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) G.val.presheaf m
    let uG := ((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s
    let z := TopCat.Presheaf.germ ((modulePullback f).obj G).val.presheaf
      ((opensMap f).obj V) x hxV uG
    have hunitG : E z = (1 : S) ⊗ₜ[R] m := by
      rw [← hs]
      exact hE V hxV s
    have hz : E.symm ((1 : S) ⊗ₜ[R] m) = z :=
      (congrArg E.symm hunitG.symm).trans (E.symm_apply_apply z)
    have hmap : b z = TopCat.Presheaf.germ ((modulePullback f).obj H).val.presheaf
        ((opensMap f).obj V) x hxV
        ((((modulePullback f).map φ).val.app (op ((opensMap f).obj V))).hom uG) :=
      stalkMapLinear_germ (R := X.presheaf)
        (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
        ((modulePullback f).map φ).val x ((opensMap f).obj V) hxV uG
    have hsec : (((modulePullback f).map φ).val.app (op ((opensMap f).obj V))).hom uG =
        ((modulePullbackPushforwardAdjunction f).unit.app H).val.app (op V)
          ((φ.val.app (op V)).hom s) :=
      congrArg (fun r : G ⟶ (modulePushforward f).obj ((modulePullback f).obj H) ↦
        (r.val.app (op V)).hom s) ((modulePullbackPushforwardAdjunction f).unit_naturality φ)
    have hunitH : E' (TopCat.Presheaf.germ ((modulePullback f).obj H).val.presheaf
        ((opensMap f).obj V) x hxV
        (((modulePullbackPushforwardAdjunction f).unit.app H).val.app (op V)
          ((φ.val.app (op V)).hom s))) =
        (1 : S) ⊗ₜ[R] TopCat.Presheaf.germ H.val.presheaf V (f.hom.base x) hxV
          ((φ.val.app (op V)).hom s) :=
      hE' V hxV ((φ.val.app (op V)).hom s)
    have hφgerm : a m = TopCat.Presheaf.germ H.val.presheaf V (f.hom.base x) hxV
        ((φ.val.app (op V)).hom s) := by
      rw [← hs]
      exact stalkMapLinear_germ (R := Y.presheaf) (M := G.val) (N := H.val) φ.val
        (f.hom.base x) V hxV s
    show E' (b (E.symm (1 ⊗ₜ[R] m))) = qS (1 ⊗ₜ[R] m)
    rw [hz, hmap, hsec, hunitH, ← hφgerm]
    rfl
  have hmaps : ∀ z : TensorProduct R S M, lhs z = qS z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp [hz, hw]
    | tmul s m => rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul, hgen]
  have hcomm : ∀ n : N, E' (b n) = qS (E n) := fun n ↦
    (congrArg (fun y ↦ E' (b y)) (E.symm_apply_apply n).symm).trans (hmaps (E n))
  have hsymm : ∀ z, E' (b (E.symm z)) = qS z := fun z ↦
    (hcomm (E.symm z)).trans (congrArg qS (E.apply_symm_apply z))
  have hfun : ⇑b = ⇑E'.symm ∘ ⇑qS ∘ ⇑E := funext fun n ↦ by
    simp only [Function.comp_apply, ← hcomm n, E'.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun, EquivLike.comp_injective, EquivLike.injective_comp]
    exact Module.FaithfullyFlat.lTensor_injective_iff_injective R S a
  · rw [hfun, EquivLike.comp_surjective, EquivLike.surjective_comp]
    exact Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S a
  · have hzero : (∀ n : N, b n = 0) ↔ ∀ z, qS z = 0 :=
      ⟨fun h z ↦ by rw [← hsymm z, h, map_zero],
        fun h n ↦ E'.map_eq_zero_iff.1 ((hcomm n).trans (h _))⟩
    refine hzero.trans ⟨fun h m ↦ ?_, fun h z ↦ ?_⟩
    · rw [(Module.FaithfullyFlat.zero_iff_lTensor_zero R S a).mpr (LinearMap.ext h)]
      simp
    · have ha0 : a = 0 := LinearMap.ext fun m ↦ h m
      show LinearMap.baseChange S a z = 0
      rw [ha0, LinearMap.baseChange_zero]
      rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]

/-- The stalk of a flat morphism of schemes is a faithfully flat local homomorphism. -/
theorem faithfullyFlat_stalkMap (x : X) : RingHom.FaithfullyFlat (f.stalkMap x).hom := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have _ : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have _ : IsLocalHom
      (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The stalk of the pullback of a homomorphism of modules along a flat morphism of schemes is
injective exactly when the stalk of the homomorphism at the image point is. -/
theorem injective_stalkMap_modulePullback_iff {M N : Y.Modules} (φ : M ⟶ N) (x : X) :
    Function.Injective (SheafOfModules.stalkMap X.ringCatSheaf x
        ((Scheme.Modules.pullback f).map φ)) ↔
      Function.Injective (SheafOfModules.stalkMap Y.ringCatSheaf (f.base x) φ) :=
  (modulePullback_stalkMapLinear_transfer f.toLRSHom.toShHom M N φ x
    (faithfullyFlat_stalkMap f x)).1

/-- The stalk of the pullback of a homomorphism of modules along a flat morphism of schemes is
surjective exactly when the stalk of the homomorphism at the image point is. -/
theorem surjective_stalkMap_modulePullback_iff {M N : Y.Modules} (φ : M ⟶ N) (x : X) :
    Function.Surjective (SheafOfModules.stalkMap X.ringCatSheaf x
        ((Scheme.Modules.pullback f).map φ)) ↔
      Function.Surjective (SheafOfModules.stalkMap Y.ringCatSheaf (f.base x) φ) :=
  (modulePullback_stalkMapLinear_transfer f.toLRSHom.toShHom M N φ x
    (faithfullyFlat_stalkMap f x)).2.1

/-- The stalk of the pullback of a homomorphism of modules along a flat morphism of schemes
vanishes exactly when the stalk of the homomorphism at the image point does. -/
theorem stalkMap_modulePullback_eq_zero_iff {M N : Y.Modules} (φ : M ⟶ N) (x : X) :
    (∀ n, (SheafOfModules.stalkMap X.ringCatSheaf x
        ((Scheme.Modules.pullback f).map φ)).hom n = 0) ↔
      ∀ m, (SheafOfModules.stalkMap Y.ringCatSheaf (f.base x) φ).hom m = 0 :=
  (modulePullback_stalkMapLinear_transfer f.toLRSHom.toShHom M N φ x
    (faithfullyFlat_stalkMap f x)).2.2

namespace Scheme.Modules

/-- Pulling back along a flat morphism of schemes preserves monomorphisms of quasi-coherent
modules: a monomorphism is injective on stalks, and the stalk of the pullback is an extension
of scalars along a faithfully flat homomorphism. -/
@[ega "0 6.7.8" "partial"]
theorem mono_pullback_map_of_flat {M N : Y.Modules} (φ : M ⟶ N) (hφ : Mono φ) :
    Mono ((Scheme.Modules.pullback f).map φ) :=
  (SheafOfModules.mono_iff_injective_stalkMap _).2 fun x ↦
    (injective_stalkMap_modulePullback_iff f φ x).2
      ((SheafOfModules.mono_iff_injective_stalkMap φ).1 hφ (f.base x))

end Scheme.Modules

end AlgebraicGeometry

end
