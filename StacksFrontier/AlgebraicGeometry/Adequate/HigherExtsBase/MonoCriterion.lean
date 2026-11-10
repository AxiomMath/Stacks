module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Monomorphisms between extended module-valued functors

Extension of scalars sends an `A`-module `M` to the module-valued functor `B ↦ B ⊗[A] M` on the
commutative `A`-algebras. This file characterises the maps of modules whose extension is a
monomorphism: they are exactly the universally injective ones.

## Main results

* `AdequateFunctor.mono_moduleExtension_map_of_universallyInjective` — the extension of a
  universally injective map is a monomorphism.
* `AdequateFunctor.universallyInjective_of_mono_moduleExtension_map` — the converse.
* `AdequateFunctor.mono_moduleExtension_map_iff_universallyInjective` — the two together.

## Implementation notes

A monomorphism of presheaves of modules is an objectwise injection, so the forward direction is
injectivity of `B ⊗[A] M → B ⊗[A] N` for an algebra `B`, which is universal injectivity tested at
the algebra carriers.

For the converse one must test at an arbitrary module `Q`, not just at an algebra. A module `Q`
that lives in the universe of the algebra carriers is a direct summand of the trivial square-zero
extension `A ⊕ Q`, an honest `A`-algebra, so testing at that algebra tests at `Q`. A finitely
generated module in the larger value universe shrinks to that universe, and a general module is
the filtered union of its finitely generated submodules, over which tensor products commute.

## References

* [Stacks Project, Tag 058I](https://stacks.math.columbia.edu/tag/058I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace AdequateFunctor

/-- The extension of a universally injective map of `A`-modules is a monomorphism of
module-valued functors: base change to any `A`-algebra stays injective. -/
public lemma mono_moduleExtension_map_of_universallyInjective {A : Type u} [CommRing A]
    {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) (hf : UniversallyInjective f.hom) :
    Mono ((moduleExtensionFunctor.{max u v w, v} A).map f) := by
  apply PresheafOfModules.mono_of_injective
  intro X
  let B := (X.unop.unop : Type (max u v))
  change Function.Injective (LinearMap.baseChange B f.hom)
  let Q : Type (max u v w) := ULift.{max u v w, max u v} B
  let eM : TensorProduct A B M ≃ₗ[A] TensorProduct A Q M :=
    TensorProduct.congr (ULift.moduleEquiv (R := A) (M := B)).symm (LinearEquiv.refl A M)
  let eN : TensorProduct A B N ≃ₗ[A] TensorProduct A Q N :=
    TensorProduct.congr (ULift.moduleEquiv (R := A) (M := B)).symm (LinearEquiv.refl A N)
  have hQ : Function.Injective (LinearMap.lTensor Q f.hom) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj Q f.hom).2 (hf Q)
  have hcomm : (LinearMap.lTensor Q f.hom).comp eM.toLinearMap =
      eN.toLinearMap.comp (LinearMap.lTensor B f.hom) := by
    ext b m
    rfl
  intro x y hxy
  have hxy' : (LinearMap.lTensor B f.hom) x = (LinearMap.lTensor B f.hom) y := by
    simpa only [LinearMap.baseChange_eq_lTensor] using hxy
  refine eM.injective (hQ ?_)
  have hx := LinearMap.congr_fun hcomm x
  have hy := LinearMap.congr_fun hcomm y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx hy
  rw [hx, hy, hxy']

/-- A monomorphism between extended module-valued functors stays injective after tensoring with a
module living in the universe of the algebra carriers: the trivial square-zero extension
`A ⊕ Q` is an `A`-algebra having `Q` as a direct summand. -/
private lemma injective_lTensor_of_mono_moduleExtension_map
    {A : Type u} [CommRing A] {M N : ModuleCat.{max u v w} A}
    (f : M ⟶ N) (hf : Mono ((moduleExtensionFunctor.{max u v w, v} A).map f))
    (Q : Type (max u v)) [AddCommGroup Q] [Module A Q] :
    Function.Injective (LinearMap.lTensor Q f.hom) := by
  let : Module Aᵐᵒᵖ Q := Module.compHom Q (RingEquiv.toOpposite A).symm.toRingHom
  have : IsCentralScalar A Q := ⟨fun _ _ => rfl⟩
  let B := TrivSqZeroExt A Q
  let X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ := Opposite.op (Opposite.op (CommAlgCat.of A B))
  have : Mono ((moduleExtensionFunctor.{max u v w, v} A).map f) := hf
  have hbase : Function.Injective (LinearMap.lTensor B f.hom) := by
    have h := PresheafOfModules.injective_of_mono
      ((moduleExtensionFunctor.{max u v w, v} A).map f) X
    change Function.Injective (LinearMap.baseChange B f.hom) at h
    simpa only [LinearMap.baseChange_eq_lTensor] using h
  let inc : Q →ₗ[A] B := TrivSqZeroExt.inrHom A Q
  let proj : B →ₗ[A] Q := TrivSqZeroExt.sndHom A Q
  let jM := LinearMap.rTensor (M := ModuleCat.of A M) inc
  let jN := LinearMap.rTensor (M := ModuleCat.of A N) inc
  let pM := LinearMap.rTensor (M := ModuleCat.of A M) proj
  have hpj : pM.comp jM = LinearMap.id := by
    rw [← LinearMap.rTensor_comp]
    ext q
    rfl
  have hcomm : (LinearMap.lTensor B f.hom).comp jM = jN.comp (LinearMap.lTensor Q f.hom) := by
    ext q m
    rfl
  have hj : Function.Injective jM := by
    intro x y h
    simpa only [← LinearMap.comp_apply, hpj, LinearMap.id_apply] using congrArg pM h
  intro x y hxy
  exact hj (hbase (by simpa only [← LinearMap.comp_apply, hcomm] using congrArg jN hxy))

/-- The square-zero extension also tests finitely generated modules in the larger value universe:
such a module shrinks to the universe of the algebra carriers. -/
private lemma injective_lTensor_of_mono_moduleExtension_map_of_finite
    {A : Type u} [CommRing A] {M N : ModuleCat.{max u v w} A}
    (f : M ⟶ N) (hf : Mono ((moduleExtensionFunctor.{max u v w, v} A).map f))
    (Q : Type (max u v w)) [AddCommGroup Q] [Module A Q] [Module.Finite A Q] :
    Function.Injective (LinearMap.lTensor Q f.hom) := by
  have : Small.{u} Q := Module.Finite.small A Q
  have : Small.{max u v} Q := small_lift.{max u v w, v, u} Q
  let Qs := Shrink.{max u v} Q
  let eQ : Qs ≃ₗ[A] Q := Shrink.linearEquiv A Q
  let eM : TensorProduct A Qs M ≃ₗ[A] TensorProduct A Q M :=
    TensorProduct.congr eQ (LinearEquiv.refl A M)
  let eN : TensorProduct A Qs N ≃ₗ[A] TensorProduct A Q N :=
    TensorProduct.congr eQ (LinearEquiv.refl A N)
  have hcomm : (LinearMap.lTensor Q f.hom).comp eM.toLinearMap =
      eN.toLinearMap.comp (LinearMap.lTensor Qs f.hom) := by
    ext q m
    rfl
  have hsmall : Function.Injective ((LinearMap.lTensor Q f.hom).comp eM.toLinearMap) := by
    rw [hcomm]
    exact eN.injective.comp (injective_lTensor_of_mono_moduleExtension_map f hf Qs)
  have hlarge : Function.Injective ((LinearMap.lTensor Q f.hom) ∘ eM.toLinearMap) := by
    simpa only [LinearMap.coe_comp] using hsmall
  exact hlarge.of_comp_right eM.surjective

/-- A map of `A`-modules whose extension is a monomorphism of module-valued functors is
universally injective. It suffices to test on finitely generated tensor factors, and each of
those is detected by a trivial square-zero extension. -/
public lemma universallyInjective_of_mono_moduleExtension_map
    {A : Type u} [CommRing A] {M N : ModuleCat.{max u v w} A}
    (f : M ⟶ N) (hf : Mono ((moduleExtensionFunctor.{max u v w, v} A).map f)) :
    UniversallyInjective f.hom := by
  intro Q _ _
  refine (LinearMap.lTensor_inj_iff_rTensor_inj Q f.hom).mp fun x y hxy => ?_
  classical
  obtain ⟨P, hP, x₀, hx₀⟩ := TensorProduct.exists_of_fg (R := A) (M := Q) (N := M) (x - y)
  have h : (LinearMap.lTensor Q f.hom)
      ((LinearMap.rTensor (ModuleCat.of A M) P.subtype) x₀) = 0 := by
    rw [hx₀]
    simp [hxy]
  rw [← sub_eq_zero, ← hx₀]
  let ι := {P : Submodule A Q // P.FG}
  have : IsDirectedOrder ι :=
    ⟨fun P P' => ⟨⟨P.val ⊔ P'.val, P.property.sup P'.property⟩, le_sup_left, le_sup_right⟩⟩
  have : Nonempty ι := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  let : DecidableEq ι := Classical.decEq ι
  let G (P : ι) := TensorProduct A P.val N
  let d (P P' : ι) (h : P ≤ P') :=
    LinearMap.rTensor (ModuleCat.of A N) (Submodule.inclusion h)
  let e := Submodule.FG.rTensor.directLimit A Q (ModuleCat.of A N)
  have : DirectedSystem G (fun P P' h => d P P' h) :=
    Submodule.FG.rTensor.directedSystem A Q (ModuleCat.of A N)
  have hcomp : (LinearMap.rTensor (ModuleCat.of A N) P.subtype).comp
      (LinearMap.lTensor P f.hom) =
      (LinearMap.lTensor Q f.hom).comp
        (LinearMap.rTensor (ModuleCat.of A M) P.subtype) := by
    ext q m
    rfl
  have htarget : (LinearMap.rTensor (ModuleCat.of A N) P.subtype)
      ((LinearMap.lTensor P f.hom) x₀) = 0 := by
    simpa only [LinearMap.comp_apply] using (LinearMap.congr_fun hcomp x₀).trans h
  have hdl : (Module.DirectLimit.of A ι G d ⟨P, hP⟩) ((LinearMap.lTensor P f.hom) x₀) = 0 :=
    e.injective <| by rwa [Submodule.FG.rTensor.directLimit_apply' A Q (ModuleCat.of A N) hP]
  obtain ⟨P', hPP', hstage⟩ := Module.DirectLimit.of.zero_exact hdl
  have : Module.Finite A P'.val := Module.Finite.iff_fg.mpr P'.property
  have hcomm : (LinearMap.lTensor P'.val f.hom).comp
        (LinearMap.rTensor (ModuleCat.of A M) (Submodule.inclusion hPP')) =
      (LinearMap.rTensor (ModuleCat.of A N) (Submodule.inclusion hPP')).comp
        (LinearMap.lTensor P f.hom) := by
    ext q m
    rfl
  have hstage' : (LinearMap.lTensor P'.val f.hom)
      ((LinearMap.rTensor (ModuleCat.of A M) (Submodule.inclusion hPP')) x₀) = 0 := by
    simpa only [LinearMap.comp_apply] using (LinearMap.congr_fun hcomm x₀).trans hstage
  have hinc : (LinearMap.rTensor (ModuleCat.of A M) (Submodule.inclusion hPP')) x₀ = 0 :=
    injective_lTensor_of_mono_moduleExtension_map_of_finite f hf P'.val hstage'
  rw [show P.subtype = P'.val.subtype.comp (Submodule.inclusion hPP') from rfl,
    LinearMap.rTensor_comp, LinearMap.comp_apply, hinc, map_zero]

/-- The extension of a map of `A`-modules to module-valued functors on the commutative
`A`-algebras is a monomorphism exactly when the map is universally injective. -/
public lemma mono_moduleExtension_map_iff_universallyInjective
    {A : Type u} [CommRing A] {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) :
    Mono ((moduleExtensionFunctor.{max u v w, v} A).map f) ↔ UniversallyInjective f.hom :=
  ⟨universallyInjective_of_mono_moduleExtension_map f,
    mono_moduleExtension_map_of_universallyInjective f⟩

end AdequateFunctor

end
