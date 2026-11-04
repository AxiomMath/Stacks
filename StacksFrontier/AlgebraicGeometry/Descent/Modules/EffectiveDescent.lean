module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Module.BaseExtension
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Pushforward
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.UniversalInjectivity
public import StacksFrontier.RingTheory.UniversallyExact

/-!
# Descent of modules along universally injective ring maps

For a homomorphism of commutative rings, descent of modules, effective descent of modules, and
universal injectivity are equivalent.

## Main results

* `ModuleCat.isDescentMorphismForModules_iff_universallyInjective` characterizes descent
  morphisms for modules by universal injectivity.
* `ModuleCat.isEffectiveDescentMorphismForModules_iff_universallyInjective` gives the same
  characterization for effective descent morphisms.
* `ModuleCat.baseExtensionUnitMap_bijective` and `ModuleCat.baseExtensionUnitEquiv` are the
  exactness of the extended cochain complex of Tag 023K in degrees `−1` and `0`, which is
  Tag 023M in those degrees: the unit `m ↦ 1 ⊗ m` is a bijection of `M` onto the invariants of
  the canonical descent datum on `A ⊗[R] M`.

## Implementation notes

The two equivalences with universal injectivity state the three-way equivalence as two
independent results. The source and target rings share a universe because the ring-map
universal-injectivity predicate uses that universe for both rings; the module universe remains
arbitrary.

A descent morphism is one whose base-extension functor to descent data is fully faithful, and
an effective one is where that functor is an equivalence. Faithfulness already forces the unit
`q ↦ 1 ⊗ q` to be injective, which is universal injectivity. Conversely, universal injectivity
makes the unit of the base-extension adjunction an isomorphism, giving full faithfulness, and
the equalizer of Tag 08X7 identifies the base extension of the invariants of a descent datum
with the datum itself, giving essential surjectivity.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 08XA](https://stacks.math.columbia.edu/tag/08XA)
-/

@[expose] public section

universe u w v

namespace ModuleCat

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

open CategoryTheory TensorProduct
open scoped ChangeOfRings

/-- The linear map `R → Q` sending `r` to `r • q`. -/
private def moduleMapFromScalar {Q : Type u} [AddCommGroup Q] [Module R Q]
    (q : Q) : R →ₗ[R] Q where
  toFun r := r • q
  map_add' r s := add_smul r s q
  map_smul' r s := (smul_smul r s q).symm

/-- The map `r ↦ r • q` between universe-lifted copies of `R` and `Q`. -/
private def moduleMapFromScalarLift {Q : Type u} [AddCommGroup Q] [Module R Q]
    (q : Q) : ULift.{max u w} R →ₗ[R] ULift.{max u w} Q :=
  (ULift.moduleEquiv.{u, u, max u w} (R := R) (M := Q)).symm.toLinearMap.comp
    ((moduleMapFromScalar (R := R) q).comp
      (ULift.moduleEquiv.{u, u, max u w} (R := R) (M := R)).toLinearMap)

/-- If `1 ⊗ q` vanishes then the base extension of `r ↦ r • q` is the zero map of descent data. -/
private theorem baseExtension_map_moduleMapFromScalar_eq_zero
    {Q : Type u} [AddCommGroup Q] [Module R Q] (q : Q)
    (hq : (TensorProduct.mk R A Q (1 : A)) q = 0) :
    (baseExtension.{u, u, w} R A).functor.map
        (ModuleCat.ofHom (moduleMapFromScalarLift (R := R) q)) =
      (baseExtension.{u, u, w} R A).functor.map
        (ModuleCat.ofHom (0 : ULift.{max u w} R →ₗ[R] ULift.{max u w} Q)) := by
  apply DescentData.Hom.ext
  apply ModuleCat.hom_ext
  show LinearMap.baseChange A (moduleMapFromScalarLift (R := R) q) =
    LinearMap.baseChange A (0 : ULift.{max u w} R →ₗ[R] ULift.{max u w} Q)
  have hqLift : TensorProduct.map LinearMap.id
      (ULift.moduleEquiv.{u, u, max u w} (R := R) (M := Q)).symm.toLinearMap
      ((TensorProduct.mk R A Q (1 : A)) q) = 0 := by
    simp [hq]
  refine TensorProduct.AlgebraTensorModule.ext fun a r => ?_
  cases r with
  | up r =>
    simp only [LinearMap.baseChange_tmul, moduleMapFromScalarLift, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ULift.moduleEquiv_apply, ULift.moduleEquiv_symm_apply,
      moduleMapFromScalar, LinearMap.coe_mk, AddHom.coe_mk]
    have hqLift' : (1 : A) ⊗ₜ[R] ULift.up q = 0 := by
      simpa using hqLift
    calc
      a ⊗ₜ[R] ULift.up (r • q) = r • (a ⊗ₜ[R] ULift.up q) := by
        rw [show ULift.up (r • q) = r • ULift.up q by rfl,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = r • (a • ((1 : A) ⊗ₜ[R] ULift.up q)) := by
        congr 1
        simp [TensorProduct.smul_tmul']
      _ = 0 := by simp [hqLift']
      _ = a ⊗ₜ[R] (0 : ULift.{max u w} Q) := by simp

/-- For a descent morphism the unit `q ↦ 1 ⊗ q` is injective on every module in the base ring's
universe. -/
private theorem baseChangeUnit_injective_of_descent
    (hF : IsDescentMorphismForModules.{u, u, w} R A)
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective (TensorProduct.mk R A Q (1 : A)) := by
  rcases hF with ⟨hF⟩
  intro q₁ q₂ hq
  have hq' : (TensorProduct.mk R A Q (1 : A)) (q₁ - q₂) = 0 := by
    rw [map_sub, hq, sub_self]
  let q := q₁ - q₂
  have hmap := baseExtension_map_moduleMapFromScalar_eq_zero (R := R) (A := A) q hq'
  have hg : ModuleCat.ofHom (moduleMapFromScalarLift (R := R) q) =
      ModuleCat.ofHom (0 : ULift.{max u w} R →ₗ[R] ULift.{max u w} Q) :=
    hF.map_injective hmap
  refine sub_eq_zero.mp ?_
  simpa [moduleMapFromScalarLift, moduleMapFromScalar] using
    congrArg (fun f => (f (ULift.up (1 : R))).down) (congrArg ModuleCat.Hom.hom hg)

/-- A descent morphism for modules is universally injective. -/
private theorem descent_implies_ringMapUniversallyInjective
    (hF : IsDescentMorphismForModules.{u, u, w} R A) :
    Algebra.UniversallyInjective R A := by
  intro Q _ _
  have hunit : Function.Injective (TensorProduct.mk R A Q (1 : A)) :=
    baseChangeUnit_injective_of_descent (R := R) (A := A) hF Q
  have hfactor : (TensorProduct.mk R A Q (1 : A)) =
      (LinearMap.rTensor Q (Algebra.linearMap R A)).comp
        (TensorProduct.lid R Q).symm.toLinearMap := by
    ext q
    simp [LinearMap.rTensor_tmul, TensorProduct.lid_symm_apply]
  intro x y hxy
  have hxy' : (TensorProduct.mk R A Q (1 : A))
      ((TensorProduct.lid R Q) x) =
    (TensorProduct.mk R A Q (1 : A)) ((TensorProduct.lid R Q) y) := by
    rw [hfactor]
    simpa using hxy
  exact (TensorProduct.lid R Q).injective (hunit hxy')

/-- A universally injective ring map reflects surjections of modules after tensoring on the
left. -/
private theorem ringMapUniversallyInjective_reflects_surjections
    (h : Algebra.UniversallyInjective R A) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Surjective (LinearMap.lTensor A f)) : Function.Surjective f := by
  let q : Submodule R N := LinearMap.range f
  let p : N →ₗ[R] N ⧸ q := q.mkQ
  have hcomp : LinearMap.lTensor A p ∘ₗ LinearMap.lTensor A f = 0 := by
    rw [← LinearMap.lTensor_comp]
    ext a m
    show a ⊗ₜ[R] p (f m) = 0
    rw [show p (f m) = 0 from (Submodule.Quotient.mk_eq_zero q).mpr ⟨m, rfl⟩, tmul_zero]
  have hkill : ∀ x : TensorProduct R A N, LinearMap.lTensor A p x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := hf x
    simpa using LinearMap.congr_fun hcomp y
  have hunitZero (z : N ⧸ q) :
      (TensorProduct.mk R A (N ⧸ q) (1 : A)) z = 0 := by
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective A (Submodule.mkQ_surjective q)
      ((TensorProduct.mk R A (N ⧸ q) (1 : A)) z)
    rw [← hx]
    exact hkill x
  have hsub : Subsingleton (N ⧸ q) := ⟨fun x y =>
    Algebra.mk_one_injective_of_universallyInjective R A h (N ⧸ q)
      (sub_eq_zero.mp (by rw [← map_sub]; exact hunitZero (x - y)))⟩
  rwa [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]

/-- A universally injective ring map reflects bijections of modules after tensoring on the left. -/
private theorem ringMapUniversallyInjective_reflects_bijective
    (h : Algebra.UniversallyInjective R A) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Bijective (LinearMap.lTensor A f)) : Function.Bijective f := by
  refine ⟨fun x y hxy => Algebra.mk_one_injective_of_universallyInjective R A h M
    (hf.1 (by simp [hxy])), ringMapUniversallyInjective_reflects_surjections
      (R := R) (A := A) h f hf.2⟩

/-- The unit `m ↦ 1 ⊗ m` of the base-extension adjunction, landing in the invariants of the
base-extended descent datum. -/
noncomputable def baseExtensionUnitMap (M : ModuleCat.{max u w} R) :
    M →ₗ[R] invariantSubmodule R A
      ((baseExtension.{u, u, w} R A).functor.obj M) := by
  let D := (baseExtension.{u, u, w} R A).functor.obj M
  let g : M →ₗ[R] restrictModule R A D.module :=
    (restrictionEquiv R A M).symm.toLinearMap.comp
      (TensorProduct.mk R A M (1 : A))
  exact LinearMap.codRestrict (invariantSubmodule R A D) g fun m => by
    have ht := (baseExtension.{u, u, w} R A).transition_tmul
      M (1 : A) (1 : A) m
    change D.transition
      (((baseExtension.{u, u, w} R A).comparison M).inv
        ((1 : A) ⊗ₜ[R, algebraMap R A] m) ⊗ₜ[R] (1 : A)) =
      (1 : A) ⊗ₜ[R] (show restrictModule R A D.module from
        ((baseExtension.{u, u, w} R A).comparison M).inv
          ((1 : A) ⊗ₜ[R, algebraMap R A] m)) at ht
    have hi : ((baseExtension.{u, u, w} R A).comparison M).inv
        ((1 : A) ⊗ₜ[R, algebraMap R A] m) =
      (show D.module from (1 : A) ⊗ₜ[R] m) := by
      change (TensorProduct.congr (algebraRestrictionEquiv R A)
        (LinearEquiv.refl R M)).symm ((1 : A) ⊗ₜ[R] m) = (1 : A) ⊗ₜ[R] m
      rfl
    rw [hi] at ht
    have hg : g m = (show restrictModule R A D.module from
        (1 : A) ⊗ₜ[R] m) := by
      rfl
    change D.transitionRestrictScalars R A
      ((g m) ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] (g m)
    rw [hg]
    simpa [DescentData.transitionRestrictScalars] using ht

/-- An effective descent morphism for modules is a descent morphism. -/
private theorem effectiveDescent_isDescent
    (h : IsEffectiveDescentMorphismForModules.{u, u, w} R A) :
    IsDescentMorphismForModules.{u, u, w} R A := by
  let F := (baseExtension.{u, u, w} R A).functor
  let : F.IsEquivalence := h
  exact ⟨CategoryTheory.Functor.FullyFaithful.ofFullyFaithful F⟩

/-- The comparison of the two equalizer presentations of a descent datum: the split equalizer of
Tag 08WZ and the base-changed equalizer of Tag 08X7 have isomorphic cone points. -/
public noncomputable def descentComparisonLinearIso
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, w} R A) :
    ModuleCat.of A (A ⊗[R] invariantSubmodule R A D) ≅
      ModuleCat.of A (ULift.{u} D.module) := by
  let hWZ := Classical.choice
    (DescentData.isSplitEqualizer_descentComparison R A D)
  let e₁ := hWZ.isEqualizer
  let e₂ := tensorPushforward_isEqualizer R A h D
  exact e₂.conePointUniqueUpToIso e₁

/-- For a universally injective ring map, the base extension of the invariants of a descent datum
is isomorphic to the datum itself. -/
public noncomputable def descentCounitLinearEquiv
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (A ⊗[R] invariantSubmodule R A D) ≃ₗ[A] D.module := by
  let e := descentComparisonLinearIso R A h D
  have he : Function.Bijective e.hom.hom := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  let eLift : (A ⊗[R] invariantSubmodule R A D) ≃ₗ[A]
      ULift.{u} D.module := LinearEquiv.ofBijective e.hom.hom he
  exact eLift.trans (ULift.moduleEquiv.{u, max u w, u} (R := A) (M := D.module))

/-- The extension comparison isomorphism is the identity on elementary tensors. -/
private theorem extensionComparison_inv_tmul
    (M : ModuleCat.{max u w} R) (a : A) (m : M) :
    (extensionComparison R A M).inv
        (a ⊗ₜ[R, algebraMap R A] m) = a ⊗ₜ[R] m := by
  show (TensorProduct.congr (algebraRestrictionEquiv R A)
    (LinearEquiv.refl R M)).symm (a ⊗ₜ[R] m) = a ⊗ₜ[R] m
  rfl

/-- The transition map of the base extension of a module, on elementary tensors. -/
private theorem baseExtension_transition_tmul_tmul
    (M : ModuleCat.{max u w} R) (a b : A) (m : M) :
    let C := (baseExtension.{u, u, w} R A).functor.obj M
    C.transition ((show C.module from (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
      a ⊗ₜ[R] (show restrictModule R A C.module from
        (b ⊗ₜ[R] m : C.module)) := by
  let C := (baseExtension.{u, u, w} R A).functor.obj M
  have h₁ : ((baseExtension.{u, u, w} R A).comparison M).inv
      (a ⊗ₜ[R, algebraMap R A] m) = (a ⊗ₜ[R] m : C.module) :=
    extensionComparison_inv_tmul R A M a m
  have h₂ : ((baseExtension.{u, u, w} R A).comparison M).inv
      (b ⊗ₜ[R, algebraMap R A] m) = (b ⊗ₜ[R] m : C.module) :=
    extensionComparison_inv_tmul R A M b m
  simpa only [h₁, h₂] using (baseExtension.{u, u, w} R A).transition_tmul M a b m

/-- The comparison isomorphism commutes with the two fork maps. -/
private theorem descentComparisonLinearIso_spec
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A)
    (x : A ⊗[R] invariantSubmodule R A D) :
    DescentData.descentComparisonHom R A D
        ((descentComparisonLinearIso R A h D).hom.hom x) =
      tensorPushforwardComparison R A D x := by
  let hWZ := Classical.choice (DescentData.isSplitEqualizer_descentComparison R A D)
  let e₁ := hWZ.isEqualizer
  let e₂ := tensorPushforward_isEqualizer R A h D
  have he : (descentComparisonLinearIso R A h D).hom ≫
      ModuleCat.ofHom (DescentData.descentComparisonHom R A D) =
      ModuleCat.ofHom (tensorPushforwardComparison R A D) :=
    CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp e₂ e₁
      CategoryTheory.Limits.WalkingParallelPair.zero
  have hx := congrArg (fun f : ModuleCat.of A
      (A ⊗[R] invariantSubmodule R A D) ⟶
      ModuleCat.of A (A ⊗[R] restrictModule R A D.module) => f.hom x) he
  simpa using hx

/-- The unit of the base-extension adjunction becomes bijective after tensoring with `A`. -/
private theorem baseExtensionUnitMap_lTensor_bijective
    (h : Algebra.UniversallyInjective R A) (M : ModuleCat.{max u w} R) :
    Function.Bijective
      (LinearMap.lTensor A (baseExtensionUnitMap R A M)) := by
  let D := (baseExtension.{u, u, w} R A).functor.obj M
  let e := descentComparisonLinearIso R A h D
  let lift : (A ⊗[R] M) ≃ₗ[A] ULift.{u} D.module :=
    (ULift.moduleEquiv.{u, max u w, u} (R := A) (M := D.module)).symm
  let n (a : A) (m : M) : D.module := a ⊗ₜ[R] m
  have hpoint (a : A) (m : M) :
      e.hom.hom (LinearMap.lTensor A (baseExtensionUnitMap R A M) (a ⊗ₜ[R] m)) =
        ULift.up (n a m) := by
    apply DescentData.descentComparisonHom_injective R A D
    have hspec := descentComparisonLinearIso_spec R A h D
      (a ⊗ₜ[R] baseExtensionUnitMap R A M m)
    have hleft : tensorPushforwardComparison R A D
        (a ⊗ₜ[R] baseExtensionUnitMap R A M m) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          (show D.module from (1 : A) ⊗ₜ[R] m)) := by
      show a ⊗ₜ[R] (show restrictModule R A D.module from
          (baseExtensionUnitMap R A M m).1) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          (show D.module from (1 : A) ⊗ₜ[R] m))
      congr 1
    have hright : DescentData.descentComparisonHom R A D (ULift.up (n a m)) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          (show D.module from (1 : A) ⊗ₜ[R] m)) := by
      have ht := baseExtension_transition_tmul_tmul R A M a 1 m
      rw [DescentData.descentComparisonHom_apply R A D (n a m)]
      simpa [DescentData.descentComparisonLeft,
        DescentData.transitionRestrictScalars] using ht
    exact hspec.trans hleft |>.trans hright.symm
  have hlift (a : A) (m : M) : lift (a ⊗ₜ[R] m) = ULift.up (n a m) := by
    show (ULift.moduleEquiv.{u, max u w, u} (R := A) (M := D.module)).symm
      (a ⊗ₜ[R] m) = ULift.up (n a m)
    apply (ULift.moduleEquiv.{u, max u w, u} (R := A) (M := D.module)).injective
    rfl
  have hmap : LinearMap.lTensor A (baseExtensionUnitMap R A M) =
      (e.symm.hom.hom).comp lift.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
    simpa [LinearMap.lTensor_tmul, hlift] using congrArg e.symm.hom.hom (hpoint a m)
  rw [hmap]
  exact (ConcreteCategory.bijective_of_isIso e.symm.hom).comp lift.bijective

/-- For a universally injective ring map the unit of the base-extension adjunction is bijective. -/
theorem baseExtensionUnitMap_bijective
    (h : Algebra.UniversallyInjective R A) (M : ModuleCat.{max u w} R) :
    Function.Bijective (baseExtensionUnitMap R A M) :=
  ringMapUniversallyInjective_reflects_bijective
    (R := R) (A := A) h (baseExtensionUnitMap R A M)
    (baseExtensionUnitMap_lTensor_bijective R A h M)

/-- **Stacks Project, Tag 023M in degrees `−1` and `0`.** For a universally injective ring map
the unit `m ↦ 1 ⊗ m` of the base-extension adjunction is an isomorphism of `M` onto the
invariants of the base-extended descent datum.

Exactness of the extended cochain complex `0 → M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯` at `M` is
injectivity of the unit, and exactness at `A ⊗[R] M` says that the kernel of the next
differential — which is `ModuleCat.invariantSubmodule R A` of the canonical descent datum on
`A ⊗[R] M` — is the image of the unit. Together they are bijectivity of the unit onto the
invariants. The source assumes `R → A` faithfully flat; faithful flatness is used only through
universal injectivity (Tag 08WL), which is the hypothesis here. -/
@[stacks 023M "degrees −1 and 0", sga "1 VIII 1.7" "affine case"]
noncomputable def baseExtensionUnitEquiv
    (h : Algebra.UniversallyInjective R A) (M : ModuleCat.{max u w} R) :
    M ≃ₗ[R] invariantSubmodule R A
      ((baseExtension.{u, u, w} R A).functor.obj M) :=
  LinearEquiv.ofBijective (baseExtensionUnitMap R A M)
    (baseExtensionUnitMap_bijective R A h M)

/-- The preimage under base extension of a morphism of descent data, obtained by taking
invariants and conjugating by the unit isomorphism. -/
private noncomputable def baseExtensionMapPreimage
    (h : Algebra.UniversallyInjective R A)
    {M N : ModuleCat.{max u w} R}
    (g : (baseExtension.{u, u, w} R A).functor.obj M ⟶
      (baseExtension.{u, u, w} R A).functor.obj N) : M ⟶ N := by
  let eM := baseExtensionUnitEquiv R A h M
  let eN := baseExtensionUnitEquiv R A h N
  let f : M →ₗ[R] N := eN.symm.toLinearMap.comp
    ((pushforwardMap R A g).comp eM.toLinearMap)
  exact ModuleCat.ofHom f

/-- The base extension of the preimage of a morphism of descent data is that morphism. -/
private theorem baseExtensionMapPreimage_map
    (h : Algebra.UniversallyInjective R A)
    {M N : ModuleCat.{max u w} R}
    (g : (baseExtension.{u, u, w} R A).functor.obj M ⟶
      (baseExtension.{u, u, w} R A).functor.obj N) :
    (baseExtension.{u, u, w} R A).functor.map
      (baseExtensionMapPreimage R A h g) = g := by
  apply DescentData.Hom.ext
  apply ModuleCat.hom_ext
  let eM := baseExtensionUnitEquiv R A h M
  let eN := baseExtensionUnitEquiv R A h N
  let f : M →ₗ[R] N := eN.symm.toLinearMap.comp
    ((pushforwardMap R A g).comp eM.toLinearMap)
  show LinearMap.baseChange A f = g.hom.hom
  let gA : A ⊗[R] M →ₗ[A] A ⊗[R] N := g.hom.hom
  show LinearMap.baseChange A f = gA
  have hunit (m : M) : eN (f m) = pushforwardMap R A g (eM m) := by
    simp [f]
  have hunitVal (m : M) : (1 : A) ⊗ₜ[R] f m =
      gA ((1 : A) ⊗ₜ[R] m) :=
    congrArg (restrictionEquiv R A N) (congrArg Subtype.val (hunit m))
  have hsmul {P : ModuleCat.{max u w} R} (a : A) (n : P) :
      a • ((1 : A) ⊗ₜ[R] n) = a ⊗ₜ[R] n := by
    simp [TensorProduct.smul_tmul']
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  rw [LinearMap.baseChange_tmul, ← hsmul a (f m), hunitVal, ← map_smul gA, hsmul]

/-- Base extension is injective on morphisms when the ring map is universally injective. -/
private theorem baseExtension_map_injective
    (h : Algebra.UniversallyInjective R A)
    {M N : ModuleCat.{max u w} R}
    (f g : M ⟶ N)
    (hfg : (baseExtension.{u, u, w} R A).functor.map f =
      (baseExtension.{u, u, w} R A).functor.map g) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hval := congrArg (fun k :
      (baseExtension.{u, u, w} R A).functor.obj M ⟶
        (baseExtension.{u, u, w} R A).functor.obj N =>
          k.hom ((1 : A) ⊗ₜ[R] m)) hfg
  have hu : baseExtensionUnitMap R A N (f.hom m) =
      baseExtensionUnitMap R A N (g.hom m) := by
    apply Subtype.ext
    have hraw : (1 : A) ⊗ₜ[R] f.hom m = (1 : A) ⊗ₜ[R] g.hom m := by
      change (LinearMap.baseChange A f.hom) ((1 : A) ⊗ₜ[R] m) =
        (LinearMap.baseChange A g.hom) ((1 : A) ⊗ₜ[R] m) at hval
      simpa only [LinearMap.baseChange_tmul] using hval
    exact congrArg (restrictionEquiv R A N).symm hraw
  exact (baseExtensionUnitEquiv R A h N).injective hu

/-- For a universally injective ring map the base-extension functor to descent data is fully
faithful. -/
private noncomputable def baseExtensionFullyFaithful
    (h : Algebra.UniversallyInjective R A) :
    (baseExtension.{u, u, w} R A).functor.FullyFaithful where
  preimage := baseExtensionMapPreimage R A h
  map_preimage := baseExtensionMapPreimage_map R A h
  preimage_map f := by
    apply baseExtension_map_injective R A h
    simp [baseExtensionMapPreimage_map]

/-- The counit isomorphism sends `a ⊗ m` to `a • m`. -/
public theorem descentCounitLinearEquiv_tmul
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A)
    (a : A) (m : invariantSubmodule R A D) :
    descentCounitLinearEquiv R A h D (a ⊗ₜ[R] m) = a • (m.1 : D.module) := by
  have hs := descentComparisonLinearIso_spec R A h D (a ⊗ₜ[R] m)
  have hcmp₁ : DescentData.descentComparisonHom R A D
      (ULift.up (descentCounitLinearEquiv R A h D (a ⊗ₜ[R] m))) =
      a ⊗ₜ[R] (m.1 : restrictModule R A D.module) := by
    simpa [descentCounitLinearEquiv, tensorPushforwardComparison,
      LinearMap.lTensor_tmul] using hs
  have hmul : D.transitionRestrictScalars R A
      (((a • (m.1 : D.module) : D.module) : restrictModule R A D.module) ⊗ₜ[R]
        (1 : A)) = a ⊗ₜ[R] (m.1 : restrictModule R A D.module) := by
    have hcmp := (tensorPushforwardComparison_tmul R A D a m).symm
    change D.transitionRestrictScalars R A
      ((a • (m.1 : restrictModule R A D.module)) ⊗ₜ[R] (1 : A)) =
        a ⊗ₜ[R] (m.1 : restrictModule R A D.module) at hcmp
    convert hcmp using 1
  let n : D.module := a • (m.1 : D.module)
  have hcmp₂ : DescentData.descentComparisonHom R A D (ULift.up n) =
      a ⊗ₜ[R] (m.1 : restrictModule R A D.module) := by
    rw [DescentData.descentComparisonHom_apply R A D n]
    show D.transitionRestrictScalars R A
      (((a • (m.1 : D.module) : D.module) : restrictModule R A D.module)
        ⊗ₜ[R] (1 : A)) = _
    exact hmul
  exact congrArg ULift.down
    (DescentData.descentComparisonHom_injective R A D (hcmp₁.trans hcmp₂.symm))

/-- The counit isomorphism is compatible with the transition maps. -/
private theorem descentCounitDataHom_comm
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (D.transition.toLinearMap.restrictScalars R).comp
        ((restrictHom R A
          (ModuleCat.ofHom (descentCounitLinearEquiv R A h D).toLinearMap)).rTensor A) =
      ((restrictHom R A
          (ModuleCat.ofHom (descentCounitLinearEquiv R A h D).toLinearMap)).lTensor A).comp
        (((baseExtension.{u, u, w} R A).functor.obj
          ((pushforward R A).obj D)).transition.toLinearMap.restrictScalars R) := by
  let M := (pushforward R A).obj D
  let C := (baseExtension.{u, u, w} R A).functor.obj M
  let e := descentCounitLinearEquiv R A h D
  let g : restrictModule R A C.module →ₗ[R]
      restrictModule R A D.module :=
    restrictHom R A (ModuleCat.ofHom e.toLinearMap)
  show (D.transition.toLinearMap.restrictScalars R).comp (g.rTensor A) =
    (g.lTensor A).comp (C.transition.toLinearMap.restrictScalars R)
  apply LinearMap.ext
  intro x
  show D.transitionRestrictScalars R A ((g.rTensor A) x) =
    (g.lTensor A) (C.transitionRestrictScalars R A x)
  induction x using TensorProduct.induction_on with
  | zero => simp [g, restrictHom]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
  | tmul n b =>
    show D.transitionRestrictScalars R A ((g n) ⊗ₜ[R] b) =
      (g.lTensor A) (C.transitionRestrictScalars R A (n ⊗ₜ[R] b))
    induction n using TensorProduct.induction_on with
    | zero =>
      calc
        D.transitionRestrictScalars R A (g 0 ⊗ₜ[R] b) = 0 := by simp
        _ = (g.lTensor A) (C.transitionRestrictScalars R A (0 ⊗ₜ[R] b)) := by simp
    | add n₁ n₂ h₁ h₂ =>
      let n₁' : restrictModule R A C.module := n₁
      let n₂' : restrictModule R A C.module := n₂
      calc
        D.transitionRestrictScalars R A (g (n₁' + n₂') ⊗ₜ[R] b) =
            D.transitionRestrictScalars R A (g n₁ ⊗ₜ[R] b) +
              D.transitionRestrictScalars R A (g n₂ ⊗ₜ[R] b) := by
          rw [map_add, add_tmul, map_add]
        _ = (g.lTensor A) (C.transitionRestrictScalars R A (n₁ ⊗ₜ[R] b)) +
              (g.lTensor A) (C.transitionRestrictScalars R A (n₂ ⊗ₜ[R] b)) := by
          rw [h₁, h₂]
        _ = (g.lTensor A) (C.transitionRestrictScalars R A ((n₁ + n₂) ⊗ₜ[R] b)) := by
          show _ = (g.lTensor A)
            (C.transitionRestrictScalars R A ((n₁' + n₂') ⊗ₜ[R] b))
          have ht : (n₁' + n₂') ⊗ₜ[R] b =
              (n₁' ⊗ₜ[R] b) + (n₂' ⊗ₜ[R] b) := add_tmul n₁' n₂' b
          rw [ht, map_add, map_add]
    | tmul a m =>
      show D.transitionRestrictScalars R A
          (e (a ⊗ₜ[R] m) ⊗ₜ[R] b) =
        (g.lTensor A)
          (C.transitionRestrictScalars R A ((a ⊗ₜ[R] m) ⊗ₜ[R] b))
      rw [descentCounitLinearEquiv_tmul R A h D a m]
      rw [show C.transitionRestrictScalars R A
          ((show C.module from (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A C.module from
          (b ⊗ₜ[R] m : C.module)) from
          baseExtension_transition_tmul_tmul R A ((pushforward R A).obj D) a b m]
      show D.transitionRestrictScalars R A
          ((restrictedScalarAction R A D.module a
            (m.1 : restrictModule R A D.module)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A D.module from e (b ⊗ₜ[R] m))
      rw [descentCounitLinearEquiv_tmul R A h D b m]
      have hb : (show restrictModule R A D.module from
          (b • (m.1 : D.module))) =
          restrictedScalarAction R A D.module b
            (m.1 : restrictModule R A D.module) :=
        (restrictedScalarAction_apply R A D.module b (m.1 : restrictModule R A D.module)).symm
      rw [hb]
      show D.transitionRestrictScalars R A
          ((restrictedScalarAction R A D.module a
            (m.1 : restrictModule R A D.module)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (restrictedScalarAction R A D.module b
          (m.1 : restrictModule R A D.module))
      calc
        D.transitionRestrictScalars R A
            ((restrictedScalarAction R A D.module a
              (m.1 : restrictModule R A D.module)) ⊗ₜ[R] b) =
          D.transitionRestrictScalars R A
            ((a ⊗ₜ[R] b) •
              ((m.1 : restrictModule R A D.module) ⊗ₜ[R] (1 : A))) := by
          congr 1
          simp
        _ = (a ⊗ₜ[R] b) •
            D.transitionRestrictScalars R A
              ((m.1 : restrictModule R A D.module) ⊗ₜ[R] (1 : A)) :=
          map_smul D.transition (a ⊗ₜ[R] b) _
        _ = (a ⊗ₜ[R] b) •
            ((1 : A) ⊗ₜ[R] (m.1 : restrictModule R A D.module)) :=
          congrArg ((a ⊗ₜ[R] b) • ·) m.2
        _ = a ⊗ₜ[R]
            (restrictedScalarAction R A D.module b
              (m.1 : restrictModule R A D.module)) := by
          rw [targetTensor_smul_tmul]
          simp

/-- The counit of the base-extension adjunction as a morphism of descent data. -/
private noncomputable def descentCounitDataHom
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (baseExtension.{u, u, w} R A).functor.obj
        ((pushforward R A).obj D) ⟶ D where
  hom := ModuleCat.ofHom (descentCounitLinearEquiv R A h D).toLinearMap
  comm := descentCounitDataHom_comm R A h D

/-- The inverse of the counit isomorphism is compatible with the transition maps. -/
private theorem descentCounitDataHomInverse_comm
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (((baseExtension.{u, u, w} R A).functor.obj
      ((pushforward R A).obj D)).transition.toLinearMap.restrictScalars R).comp
        ((restrictHom R A
          (ModuleCat.ofHom (descentCounitLinearEquiv R A h D).symm.toLinearMap)).rTensor A) =
      ((restrictHom R A
        (ModuleCat.ofHom (descentCounitLinearEquiv R A h D).symm.toLinearMap)).lTensor A).comp
        (D.transition.toLinearMap.restrictScalars R) := by
  let C := (baseExtension.{u, u, w} R A).functor.obj
    ((pushforward R A).obj D)
  let e := descentCounitLinearEquiv R A h D
  let g : restrictModule R A C.module →ₗ[R]
      restrictModule R A D.module :=
    restrictHom R A (ModuleCat.ofHom e.toLinearMap)
  let gi : restrictModule R A D.module →ₗ[R]
      restrictModule R A C.module :=
    restrictHom R A (ModuleCat.ofHom e.symm.toLinearMap)
  have hgi : g.comp gi = LinearMap.id := by
    ext x
    exact e.apply_symm_apply (show D.module from x)
  have hig : gi.comp g = LinearMap.id := by
    ext x
    exact e.symm_apply_apply (show C.module from x)
  have hcompR : g.rTensor A ∘ₗ gi.rTensor A = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hgi, LinearMap.rTensor_id]
  have hcompL : g.lTensor A ∘ₗ gi.lTensor A = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hgi, LinearMap.lTensor_id]
  have hcancelComp : gi.lTensor A ∘ₗ g.lTensor A = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hig, LinearMap.lTensor_id]
  have hcancel : Function.Injective (g.lTensor A) := by
    intro x y hxy
    have := congrArg (gi.lTensor A) hxy
    change (gi.lTensor A ∘ₗ g.lTensor A) x =
      (gi.lTensor A ∘ₗ g.lTensor A) y at this
    rwa [hcancelComp] at this
  have hforward := descentCounitDataHom_comm R A h D
  change (D.transition.toLinearMap.restrictScalars R).comp (g.rTensor A) =
      (g.lTensor A).comp (C.transition.toLinearMap.restrictScalars R) at hforward
  apply LinearMap.ext
  intro x
  apply hcancel
  calc
    (g.lTensor A) (C.transition.toLinearMap.restrictScalars R (gi.rTensor A x)) =
        D.transition.toLinearMap.restrictScalars R (g.rTensor A (gi.rTensor A x)) :=
      (LinearMap.congr_fun hforward (gi.rTensor A x)).symm
    _ = D.transition.toLinearMap.restrictScalars R x := by
      show D.transition.toLinearMap.restrictScalars R
        ((g.rTensor A ∘ₗ gi.rTensor A) x) = _
      rw [hcompR, LinearMap.id_apply]
    _ = (g.lTensor A) (gi.lTensor A
          (D.transition.toLinearMap.restrictScalars R x)) := by
      show _ = (g.lTensor A ∘ₗ gi.lTensor A)
        (D.transition.toLinearMap.restrictScalars R x)
      rw [hcompL, LinearMap.id_apply]

/-- The inverse of the counit, as a morphism of descent data. -/
private noncomputable def descentCounitDataHomInverse
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    D ⟶ (baseExtension.{u, u, w} R A).functor.obj
        ((pushforward R A).obj D) where
  hom := ModuleCat.ofHom (descentCounitLinearEquiv R A h D).symm.toLinearMap
  comm := descentCounitDataHomInverse_comm R A h D

/-- The base extension of the invariants of a descent datum is isomorphic to the datum, as
descent data. -/
private noncomputable def descentCounitDataIso
    (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (baseExtension.{u, u, w} R A).functor.obj
        ((pushforward R A).obj D) ≅ D where
  hom := descentCounitDataHom R A h D
  inv := descentCounitDataHomInverse R A h D
  hom_inv_id := by
    apply DescentData.Hom.ext
    apply ModuleCat.hom_ext
    change (descentCounitLinearEquiv R A h D).symm.toLinearMap.comp
        (descentCounitLinearEquiv R A h D).toLinearMap = LinearMap.id
    ext x
    simp
  inv_hom_id := by
    apply DescentData.Hom.ext
    apply ModuleCat.hom_ext
    change (descentCounitLinearEquiv R A h D).toLinearMap.comp
        (descentCounitLinearEquiv R A h D).symm.toLinearMap = LinearMap.id
    ext x
    simp

/-- For a universally injective ring map the base-extension functor to descent data is
essentially surjective. -/
private theorem baseExtension_essSurj
    (h : Algebra.UniversallyInjective R A) :
    (baseExtension.{u, u, w} R A).functor.EssSurj where
  mem_essImage D := ⟨(pushforward R A).obj D,
    ⟨descentCounitDataIso R A h D⟩⟩

/-- A ring map is a descent morphism for modules exactly when it is universally injective. -/
@[stacks 08XA "descent morphism"]
public theorem isDescentMorphismForModules_iff_universallyInjective :
    IsDescentMorphismForModules.{u, u, w} R A ↔
      Algebra.UniversallyInjective R A :=
  ⟨descent_implies_ringMapUniversallyInjective R A, fun h => ⟨baseExtensionFullyFaithful R A h⟩⟩

/-- A ring map is an effective descent morphism for modules exactly when it is universally
injective. -/
@[stacks 08XA "effective descent morphism"]
public theorem isEffectiveDescentMorphismForModules_iff_universallyInjective :
    IsEffectiveDescentMorphismForModules.{u, u, w} R A ↔
      Algebra.UniversallyInjective R A := by
  refine ⟨fun h => (isDescentMorphismForModules_iff_universallyInjective R A).mp
    (effectiveDescent_isDescent R A h), fun h => ?_⟩
  let hFF := baseExtensionFullyFaithful R A h
  exact { faithful := hFF.faithful, full := hFF.full, essSurj := baseExtension_essSurj R A h }

end ModuleCat

end
