module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealTorsionFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.InvertibleChernSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.LocalEquation
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierRegular.FrameSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents
public import StacksFrontier.RingTheory.Support.Finite

/-!
# Gysin pullback of the cycle of a coherent sheaf

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, let
`L` be an invertible module on `X` with global section `s`, and let `i : D ⟶ X` be the zero
scheme of `s`. For a coherent sheaf `F` on `X` whose support has delta-dimension at most
`k + 1` and on which multiplication by `s` is injective, the Gysin homomorphism `i^*` sends the
cycle `[F]_{k+1}` to the class of the cycle `[i^*F]_k` of the restriction of `F` to `D`.

## Main results

* `Stacks.Chow.schemeDeltaDimension_pullback_support_le_of_mono_section` — the support of `i^*F`
  has delta-dimension at most `k`, so that `[i^*F]_k` is defined.
* `Stacks.Chow.gysinHomomorphismOfInvertible_cycleAssociatedToCoherentSheaf` —
  `i^*[F]_{k+1} = [i^*F]_k` in `CH_k(D)`.

## Implementation notes

The hypothesis that multiplication by `s` is injective on `F` is expressed as monicity of
`1_F ⊗ s : F ⊗ 𝒪_X ⟶ F ⊗ L`, the tensor product of the identity of `F` with the morphism
`𝒪_X ⟶ L` named by `s`. Composing with the canonical isomorphism `F ≅ F ⊗ 𝒪_X` identifies this
morphism with `s : F → F ⊗ L`, and an isomorphism both preserves and reflects monomorphisms, so
the two conditions agree.

The passage from that monicity to the statement that the local equation of `D` acts as a
nonzerodivisor on each stalk of `F` goes through the stalk of the sheaf tensor product. That
machinery is written for a ringed space, which spells the local ring of `X` at `x` and the stalk
of `F` at `x` differently from the way a scheme does; the two spellings agree only after
unfolding definitions that instance search does not unfold. The helpers that use it are
therefore stated for a ringed space and sheaves of modules over its structure sheaf of rings,
so that no scheme-level spelling is ever handed to instance search in place of a ringed-space
one. The scheme appears only in `Stacks.Chow.smulRegular_frameCoordinate_of_mono_section`; the
scalar actions on the stalk in the two spellings are the same Mathlib instance, so no conversion
is needed there.

The companion statement of Stacks 02TB for the fundamental cycle of a closed subscheme, together
with the shared material on relative dimension, the reduced structure on the closure of a point
and local lengths, is in
`StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection`.

## References

* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open TopologicalSpace

open scoped TensorProduct

universe v w
open CategoryTheory.Limits Opposite
private lemma length_tensor_eq_length_quotSMulTop
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    (h : Function.Surjective (algebraMap R S)) (a : R)
    (hker : RingHom.ker (algebraMap R S) = Ideal.span {a}) :
    Module.length S (S ⊗[R] M) = Module.length R (QuotSMulTop a M) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) h
  calc
    Module.length S (S ⊗[R] M) = Module.length R (S ⊗[R] M) :=
      (Module.length_eq_of_surjective h).symm
    _ = Module.length R ((R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] M) :=
      (e.toLinearEquiv.rTensor M).length_eq.symm
    _ = Module.length R ((R ⧸ Ideal.span {a}) ⊗[R] M) := by rw [hker]
    _ = Module.length R (QuotSMulTop a M) :=
      (QuotSMulTop.equivQuotTensor a M).length_eq.symm

private lemma smulRegular_not_mem_minimalSupport
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : IsSMulRegular M x) {q : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) : x ∉ q.asIdeal := by
  intro hxq
  obtain ⟨hprime, m, hm⟩ : q.asIdeal ∈ associatedPrimes R M :=
    Module.mem_associatedPrimes_of_minimal_mem_support hq
  have hm0 : m ≠ 0 := by
    intro h
    refine hprime.ne_top ?_
    rw [hm, h]
    simp
  rw [hm, Ideal.mem_radical_iff] at hxq
  obtain ⟨n, hn⟩ := hxq
  have hpow : x ^ n • m = 0 := by
    simpa using Submodule.mem_colon_singleton.mp hn
  exact hm0 ((hx.pow n) (by simpa using hpow))

private lemma not_smulRegular_of_mem_maximalIdeal_of_finiteLength
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hfg : Module.Finite R M) (hM : IsFiniteLength R M) [Nontrivial M]
    {a : R} (ha : a ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M a) : False := by
  letI := hfg
  have hfin := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  letI : IsNoetherian R M := hfin.1
  letI : IsArtinian R M := hfin.2
  let f : M →ₗ[R] M := LinearMap.lsmul R M a
  have hlen : Module.length R f.range = Module.length R M :=
    (LinearEquiv.ofInjective f hreg).length_eq.symm
  have hrange : f.range = ⊤ := by
    by_contra htop
    have hlt := Submodule.length_lt htop
    rw [hlen] at hlt
    exact (lt_irrefl _ hlt)
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
  have hsub : (⊤ : Submodule R M) ≤ IsLocalRing.maximalIdeal R • ⊤ := by
    intro m hm
    obtain ⟨y, rfl⟩ := hsurj m
    change a • y ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)
    exact Submodule.smul_mem_smul ha (show y ∈ (⊤ : Submodule R M) from trivial)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (IsLocalRing.maximalIdeal R) (⊤ : Submodule R M) Module.Finite.fg_top hsub
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  obtain ⟨m, hm⟩ := (nontrivial_iff_exists_ne (0 : M)).mp ‹Nontrivial M›
  have hmbot : m ∈ (⊥ : Submodule R M) := by rw [← hbot]; trivial
  exact hm (by simpa using hmbot)

private lemma stalk_tensorSheafMap_right
    {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {F G G' : SheafOfModules.{u} (structureSheafRing X)}
    (ψ : G ⟶ G') (idF : F ⟶ F) (x : X.carrier)
    (hid : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X F.val F.val idF.val x = LinearMap.id)
    (z : Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).val x) :
    LinearMap.lTensor (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X F.val x)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X G.val G'.val ψ.val x)
        ((Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x F G) z) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x F G'
        (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).val
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G'))).val
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((idF, ψ) : (_, _) ⟶ (_, _)))).val x z) := by
  have h := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_natural X x F G F G' idF ψ
  have hz := congrArg (fun morphism => morphism z) h
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hz
  rw [hid] at hz
  rw [← LinearMap.lTensor_def] at hz
  exact hz

private lemma lTensor_stalkMap_injective_of_tensorSheafMap_mono
    {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {F G G' : SheafOfModules.{u} (structureSheafRing X)}
    (ψ : G ⟶ G') (x : X.carrier)
    [hmono : Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 F), ψ) : (_, _) ⟶ (_, _))))] :
    Function.Injective
      (LinearMap.lTensor (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X F.val x)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X G.val G'.val ψ.val x)) := by
  let f := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 F), ψ) : (_, _) ⟶ (_, _)))
  let idF : F ⟶ F := 𝟙 F
  have hf : Function.Injective
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G'))).val f.val x) :=
    @Stacks.IdealTorsion.stalkMapL_injective_of_mono X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))) ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G'))) f hmono x
  have hid : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X F.val F.val idF.val x = LinearMap.id := by
    ext z
    simp [idF, Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL, Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap]
    rfl
  let e := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x F G
  let e' := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x F G'
  intro z z' hzz
  have heq : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).val
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G'))).val f.val x (e.symm z) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G'))).val f.val x (e.symm z') := by
    apply e'.injective
    calc
      e' (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G'))).val f.val x (e.symm z)) =
        LinearMap.lTensor (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X F.val x)
          (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X G.val G'.val ψ.val x) (e (e.symm z)) :=
        (stalk_tensorSheafMap_right ψ idF x hid (e.symm z)).symm
      _ = LinearMap.lTensor (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X F.val x)
          (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X G.val G'.val ψ.val x) (e (e.symm z')) := by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact hzz
      _ = e' (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G'))).val f.val x (e.symm z')) :=
        stalk_tensorSheafMap_right ψ idF x hid (e.symm z')
  have hsEq : e.symm z = e.symm z' := hf heq
  exact e.symm.injective hsEq

private lemma smulRegular_of_lTensor_injective
    {A M P N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    [AddCommGroup N] [Module A N]
    (φ : P →ₗ[A] N) (eP : P ≃ₗ[A] A) (eN : N ≃ₗ[A] A) (a : A)
    (he : eN (φ (eP.symm 1)) = a)
    (hinj : Function.Injective (LinearMap.lTensor M φ)) :
    IsSMulRegular M a := by
  change Function.Injective (fun m : M => a • m)
  let eT : TensorProduct A M N →ₗ[A] TensorProduct A M A :=
    TensorProduct.map (LinearMap.id) eN.toLinearMap
  have heT : Function.Bijective eT := by
    apply TensorProduct.map_bijective
    · exact ⟨fun _ _ h => h, fun m => ⟨m, rfl⟩⟩
    · exact eN.bijective
  let ePmap : TensorProduct A M P →ₗ[A] TensorProduct A M A :=
    TensorProduct.map (LinearMap.id) eP.toLinearMap
  have hmul (m : M) :
      eT ((LinearMap.lTensor M φ) (m ⊗ₜ[A] (eP.symm 1))) =
        (a • m) ⊗ₜ[A] (1 : A) := by
    calc
      _ = m ⊗ₜ[A] eN (φ (eP.symm 1)) := by
        simp [eT, TensorProduct.map_tmul, LinearMap.lTensor_tmul]
      _ = m ⊗ₜ[A] a := by rw [he]
      _ = m ⊗ₜ[A] (a • (1 : A)) := by simp
      _ = a • (m ⊗ₜ[A] (1 : A)) := TensorProduct.tmul_smul a m 1
      _ = (a • m) ⊗ₜ[A] (1 : A) := by rw [TensorProduct.smul_tmul']
  intro m n hmn
  change a • m = a • n at hmn
  have hmap : eT ((LinearMap.lTensor M φ) (m ⊗ₜ[A] (eP.symm 1))) =
      eT ((LinearMap.lTensor M φ) (n ⊗ₜ[A] (eP.symm 1))) := by
    rw [hmul m, hmul n]
    exact congrArg (fun v : M => v ⊗ₜ[A] (1 : A)) hmn
  have hten : (LinearMap.lTensor M φ) (m ⊗ₜ[A] (eP.symm 1)) =
      (LinearMap.lTensor M φ) (n ⊗ₜ[A] (eP.symm 1)) := by
    exact heT.1 hmap
  have hmnP : m ⊗ₜ[A] (eP.symm 1) = n ⊗ₜ[A] (eP.symm 1) := hinj hten
  have hmn' : m ⊗ₜ[A] (1 : A) = n ⊗ₜ[A] (1 : A) := by
    have h := congrArg ePmap hmnP
    simpa [ePmap, TensorProduct.map_tmul, eP.apply_symm_apply] using h
  have hmn'' := congrArg (TensorProduct.rid A M) hmn'
  simpa using hmn''

open CategoryTheory.Limits Opposite

/-! ### The frame coordinate of a section as a nonzerodivisor on a stalk

The passage from monicity of `1_F ⊗ s` to the statement that the local equation of the zero
scheme of `s` acts as a nonzerodivisor on each stalk of `F` runs through the stalk of a sheaf
tensor product, and that machinery is written for a ringed space.  A ringed space spells the
local ring at `x` and the stalk of a module at `x` as `TensorStalkRingedSpace.ringStalk` and
`TensorStalkRingedSpace.grpStalk`, and a scheme spells the same two objects as
`X.presheaf.stalk x` and `F.presheaf.stalk x`; the two spellings agree, but only after
unfolding definitions that instance search does not unfold.  Everything in this section is
therefore stated for a ringed space `X` and sheaves of modules over its structure sheaf of
rings, so that no scheme-level spelling is ever handed to instance search in place of a
ringed-space one.  The scheme enters one declaration later, at
`Stacks.Chow.smulRegular_frameCoordinate_of_mono_section`, whose statement is in the scheme
spelling; the scalar action on the stalk is Mathlib's in both spellings. -/

section RingedSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- The structure sheaf of a ringed space, viewed as a module over itself. -/
private abbrev unitModule (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    SheafOfModules.{u} (structureSheafRing X) :=
  SheafOfModules.unit (structureSheafRing X)

/-- The underlying presheaf of abelian groups of a sheaf of modules on a ringed space.  This
is the presheaf whose stalk is `grpStalk`; naming it with `TopCat.Presheaf` as the head of its
type makes the germ, stalk and colimit interface available by dot notation. -/
private abbrev abPresheaf {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    TopCat.Presheaf AddCommGrpCat.{u} X.carrier :=
  F.val.presheaf

/-- Restricting a section twice along `≤` restricts it once. -/
private lemma abPresheaf_map_map {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (F : SheafOfModules.{u} (structureSheafRing X))
    {U V W : TopologicalSpace.Opens X.carrier} (hVU : V ≤ U) (hWV : W ≤ V) (hWU : W ≤ U)
    (m : (abPresheaf F).obj (.op U)) :
    (abPresheaf F).map (homOfLE hWV).op ((abPresheaf F).map (homOfLE hVU).op m) =
      (abPresheaf F).map (homOfLE hWU).op m := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Every element of the stalk of a sheaf of modules on a ringed space is the germ of a
section defined on some neighbourhood of `x` inside a prescribed one.  This repeats
`TopCat.Presheaf.exists_le_germ_eq` with the section typed as an element of the module of
sections and the germ taken by `grpGerm`, which is the shape the lemmas characterising the
stalk module structure are stated at. -/
private lemma exists_le_grpGerm_eq {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (F : SheafOfModules.{u} (structureSheafRing X)) (x : X.carrier)
    {V : TopologicalSpace.Opens X.carrier} (hxV : x ∈ V) (m : grpStalk X F.val x) :
    ∃ (W : TopologicalSpace.Opens X.carrier) (_ : W ≤ V) (hxW : x ∈ W)
      (t : F.val.obj (.op W)), grpGerm X F.val x W hxW t = m := by
  obtain ⟨W, hWV, hxW, t, ht⟩ := (abPresheaf F).exists_le_germ_eq m hxV
  exact ⟨W, hWV, hxW, t, ht⟩

/-- The component at `V ≤ U` of a morphism of modules on the over-site of an open `U`, as a
linear map on modules of sections. -/
private abbrev overApp {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {F G : SheafOfModules.{u} (structureSheafRing X)}
    {U V : TopologicalSpace.Opens X.carrier} (φ : F.over U ⟶ G.over U) (hVU : V ≤ U) :
    F.val.obj (.op V) →ₗ[(O X).obj (.op V)] G.val.obj (.op V) :=
  (φ.val.app (.op (Over.mk (homOfLE hVU)))).hom

private lemma overApp_naturality {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {F G : SheafOfModules.{u} (structureSheafRing X)}
    {U V W : TopologicalSpace.Opens X.carrier} (φ : F.over U ⟶ G.over U) (hVU : V ≤ U)
    (hWV : W ≤ V) (m : F.val.obj (.op V)) :
    overApp φ (hWV.trans hVU) ((abPresheaf F).map (homOfLE hWV).op m) =
      (abPresheaf G).map (homOfLE hWV).op (overApp φ hVU m) := by
  have h := φ.val.naturality (Over.homMk (homOfLE hWV) :
    Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU)).op
  exact congrArg (fun g => g.hom m) h

/-- The map on stalks at `x` induced by a morphism of modules on the over-site of an open
neighbourhood `U` of `x`: a germ at `x` is restricted into `U` and then pushed through the
component of the morphism. -/
private def overStalkMap (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (φ : F.over U ⟶ G.over U)
    (x : X.carrier) (hx : x ∈ U) :
    grpStalk X F.val x ⟶ grpStalk X G.val x :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ abPresheaf F) {
    pt := grpStalk X G.val x
    ι := {
      app := fun V =>
        (abPresheaf F).map (homOfLE (show V.unop.1 ⊓ U ≤ V.unop.1 from inf_le_left)).op ≫
        AddCommGrpCat.ofHom (φ.val.app (.op (Over.mk
          (homOfLE (show V.unop.1 ⊓ U ≤ U from inf_le_right))))).hom.toAddMonoidHom ≫
        (abPresheaf G).germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hx⟩
      naturality := by
        intro V W f
        dsimp
        simp only [Category.comp_id]
        ext m
        have hj : W.unop.1 ⊓ U ≤ V.unop.1 ⊓ U := inf_le_inf f.unop.le le_rfl
        have hm : (abPresheaf F).map
              (homOfLE (show W.unop.1 ⊓ U ≤ W.unop.1 from inf_le_left)).op
              ((abPresheaf F).map
                (homOfLE (show W.unop.1 ≤ V.unop.1 from f.unop.le)).op m) =
            (abPresheaf F).map (homOfLE hj).op
              ((abPresheaf F).map
                (homOfLE (show V.unop.1 ⊓ U ≤ V.unop.1 from inf_le_left)).op m) :=
          (abPresheaf_map_map F (show W.unop.1 ≤ V.unop.1 from f.unop.le) inf_le_left
              (inf_le_left.trans f.unop.le) m).trans
            (abPresheaf_map_map F (show V.unop.1 ⊓ U ≤ V.unop.1 from inf_le_left) hj
              (hj.trans inf_le_left) m).symm
        refine Eq.trans (congrArg (fun t => (abPresheaf G).germ (W.unop.1 ⊓ U) x
          ⟨W.unop.2, hx⟩ (overApp φ
            (hj.trans (show V.unop.1 ⊓ U ≤ U from inf_le_right)) t)) hm) ?_
        refine Eq.trans (congrArg ((abPresheaf G).germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩)
          (overApp_naturality φ (show V.unop.1 ⊓ U ≤ U from inf_le_right) hj
            ((abPresheaf F).map
              (homOfLE (show V.unop.1 ⊓ U ≤ V.unop.1 from inf_le_left)).op m))) ?_
        exact (abPresheaf G).germ_res_apply (homOfLE hj) x _ _ } }

private lemma overStalkMap_germ (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    {U V : TopologicalSpace.Opens X.carrier} (φ : F.over U ⟶ G.over U) (x : X.carrier)
    (hx : x ∈ U) (hxV : x ∈ V) (hVU : V ≤ U) (m : F.val.obj (.op V)) :
    overStalkMap X F G φ x hx (grpGerm X F.val x V hxV m) =
      grpGerm X G.val x V hxV (overApp φ hVU m) := by
  change ((abPresheaf F).germ V x hxV ≫ overStalkMap X F G φ x hx) m = _
  unfold overStalkMap
  change (colimit.ι ((OpenNhds.inclusion x).op ⋙ abPresheaf F) (.op ⟨V, hxV⟩) ≫
    colimit.desc _ _) m = _
  rw [colimit.ι_desc]
  change (abPresheaf G).germ (V ⊓ U) x ⟨hxV, hx⟩
    (overApp φ (inf_le_left.trans hVU)
      ((abPresheaf F).map (homOfLE inf_le_left).op m)) = _
  rw [overApp_naturality φ hVU inf_le_left]
  exact (abPresheaf G).germ_res_apply (homOfLE inf_le_left) x _ _

/-- The map on stalks at `x` induced by a morphism of modules on the over-site of an open
neighbourhood `U` of `x`, as a linear map over the local ring at `x`. -/
private def overStalkLinearMap (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (φ : F.over U ⟶ G.over U)
    (x : X.carrier) (hx : x ∈ U) :
    grpStalk X F.val x →ₗ[ringStalk X x] grpStalk X G.val x where
  toAddHom := (overStalkMap X F G φ x hx).hom.toAddHom
  map_smul' r m := by
    obtain ⟨V, hVU, hxV, r, rfl⟩ := X.presheaf.exists_le_germ_eq r hx
    obtain ⟨W, hWV, hxW, m, rfl⟩ := exists_le_grpGerm_eq F x hxV m
    rw [← X.presheaf.germ_res_apply (homOfLE hWV) x hxW r]
    change overStalkMap X F G φ x hx
        (ringGerm X x W hxW _ • grpGerm X F.val x W hxW m) = _
    rw [← stalkModule_germ_smul]
    change overStalkMap X F G φ x hx (grpGerm X F.val x W hxW (_ • m)) =
        ringGerm X x W hxW (X.presheaf.map (homOfLE hWV).op r) •
          overStalkMap X F G φ x hx (grpGerm X F.val x W hxW m)
    refine Eq.trans (overStalkMap_germ X F G φ x hx hxW (hWV.trans hVU) _) ?_
    refine Eq.trans ?_ (congrArg
      (fun t => ringGerm X x W hxW (X.presheaf.map (homOfLE hWV).op r) • t)
      (overStalkMap_germ X F G φ x hx hxW (hWV.trans hVU) m)).symm
    rw [map_smul]
    exact stalkModule_germ_smul X G.val x W hxW _ _

/-- The isomorphism of stalks at `x` induced by an isomorphism of modules on the over-site of
an open neighbourhood `U` of `x`. -/
private def overStalkLinearEquiv (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (e : F.over U ≅ G.over U)
    (x : X.carrier) (hx : x ∈ U) :
    grpStalk X F.val x ≃ₗ[ringStalk X x] grpStalk X G.val x := by
  refine LinearEquiv.ofLinearMap (overStalkLinearMap X F G e.hom x hx)
    (overStalkLinearMap X G F e.inv x hx) ?_ ?_
  · ext m
    obtain ⟨V, hVU, hxV, m, rfl⟩ := exists_le_grpGerm_eq G x hx m
    change overStalkMap X F G e.hom x hx
      (overStalkMap X G F e.inv x hx (grpGerm X G.val x V hxV m)) =
        grpGerm X G.val x V hxV m
    refine Eq.trans (congrArg (overStalkMap X F G e.hom x hx)
      (overStalkMap_germ X G F e.inv x hx hxV hVU m)) ?_
    refine Eq.trans (overStalkMap_germ X F G e.hom x hx hxV hVU (overApp e.inv hVU m)) ?_
    congr 1
    exact (((_root_.SheafOfModules.evaluation ((structureSheafRing X).over U)
      (.op (Over.mk (homOfLE hVU)))).mapIso e).inv_hom_id_apply m)
  · ext m
    obtain ⟨V, hVU, hxV, m, rfl⟩ := exists_le_grpGerm_eq F x hx m
    change overStalkMap X G F e.inv x hx
      (overStalkMap X F G e.hom x hx (grpGerm X F.val x V hxV m)) =
        grpGerm X F.val x V hxV m
    refine Eq.trans (congrArg (overStalkMap X G F e.inv x hx)
      (overStalkMap_germ X F G e.hom x hx hxV hVU m)) ?_
    refine Eq.trans (overStalkMap_germ X G F e.inv x hx hxV hVU (overApp e.hom hVU m)) ?_
    congr 1
    exact (((_root_.SheafOfModules.evaluation ((structureSheafRing X).over U)
      (.op (Over.mk (homOfLE hVU)))).mapIso e).hom_inv_id_apply m)

/-- A trivialization of `L` over an open neighbourhood `U` of `x` identifies the stalk of `L`
at `x` with the local ring at `x`. -/
private def frameStalkLinearEquiv (X : AlgebraicGeometry.RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier}
    (eU : L.over U ≅ SheafOfModules.unit ((structureSheafRing X).over U))
    (x : X.carrier) (hx : x ∈ U) :
    grpStalk X L.val x ≃ₗ[ringStalk X x] ringStalk X x :=
  (overStalkLinearEquiv X L (unitModule X) eU x hx).trans
    (Stacks.IdealTorsion.unitStalkLinearEquiv X x)

private lemma frameStalkLinearEquiv_germ (X : AlgebraicGeometry.RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheafRing X))
    {U V : TopologicalSpace.Opens X.carrier}
    (eU : L.over U ≅ SheafOfModules.unit ((structureSheafRing X).over U))
    (x : X.carrier) (hx : x ∈ U) (hxV : x ∈ V) (hVU : V ≤ U) (m : L.val.obj (.op V)) :
    frameStalkLinearEquiv X L eU x hx (grpGerm X L.val x V hxV m) =
      X.presheaf.germ V x hxV ((eU.hom.val.app (.op (Over.mk (homOfLE hVU)))).hom m) := by
  change Stacks.IdealTorsion.unitStalkAddEquiv X x
    (overStalkMap X L (unitModule X) eU.hom x hx (grpGerm X L.val x V hxV m)) = _
  refine Eq.trans (congrArg (fun t => Stacks.IdealTorsion.unitStalkAddEquiv X x t)
    (overStalkMap_germ X L (unitModule X) eU.hom x hx hxV hVU m)) ?_
  refine Eq.trans (Stacks.IdealTorsion.unitStalkAddEquiv_germ X x V hxV _) ?_
  rfl

/-- Under the identification of the stalk of `L` at `x` with the local ring given by a
trivialization over `U`, the image of the germ of `s` at `x` is the germ of the frame
coordinate of `s` over `U`. -/
private lemma frameStalkLinearEquiv_section (X : AlgebraicGeometry.RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier}
    (eU : L.over U ≅ SheafOfModules.unit ((structureSheafRing X).over U))
    (s : L.sections) (x : X.carrier) (hx : x ∈ U) :
    frameStalkLinearEquiv X L eU x hx
      (stalkMapL X _ _ (L.unitHomEquiv.symm s).val x
        ((Stacks.IdealTorsion.unitStalkLinearEquiv X x).symm 1)) =
      X.presheaf.germ U x hx
        ((eU.hom.val.app (.op (Over.mk (𝟙 U)))).hom (s.eval (.op U))) := by
  have hunit : (Stacks.IdealTorsion.unitStalkLinearEquiv X x).symm 1 =
      grpGerm X (unitModule X).val x U hx (1 : X.presheaf.obj (.op U)) := by
    apply (Stacks.IdealTorsion.unitStalkLinearEquiv X x).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (Stacks.IdealTorsion.unitStalkAddEquiv_germ X x U hx 1).trans (map_one _) |>.symm
  rw [hunit]
  change frameStalkLinearEquiv X L eU x hx
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map (L.unitHomEquiv.symm s).val))
        (grpGerm X (unitModule X).val x U hx (1 : X.presheaf.obj (.op U)))) = _
  have hstalk : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map (L.unitHomEquiv.symm s).val))
        (grpGerm X (unitModule X).val x U hx (1 : X.presheaf.obj (.op U))) =
      grpGerm X L.val x U hx
        (((L.unitHomEquiv.symm s).val.app (.op U)).hom (1 : X.presheaf.obj (.op U))) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx _ _
  refine Eq.trans (congrArg (fun t => frameStalkLinearEquiv X L eU x hx t) hstalk) ?_
  refine Eq.trans (frameStalkLinearEquiv_germ X L eU x hx hx le_rfl
    (((L.unitHomEquiv.symm s).val.app (.op U)).hom (1 : X.presheaf.obj (.op U)))) ?_
  have hsec : ((L.unitHomEquiv.symm s).val.app (.op U)).hom
      (1 : X.presheaf.obj (.op U)) = s.eval (.op U) :=
    congrArg (fun t : L.sections => t.eval (.op U)) (L.unitHomEquiv.apply_symm_apply s)
  change X.presheaf.germ U x hx
    ((eU.hom.val.app (.op (Over.mk (𝟙 U)))).hom
      (((L.unitHomEquiv.symm s).val.app (.op U)).hom (1 : X.presheaf.obj (.op U)))) = _
  rw [hsec]

/-- Multiplication on the stalk at `x` by the frame coordinate of a global section `s` of an
invertible module is injective on the stalk of `F`, whenever multiplication by `s` is
injective on `F`. -/
private lemma injective_smul_frameCoordinate_of_mono_section
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F L : SheafOfModules.{u} (structureSheafRing X)) (s : L.sections)
    (hs : Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 F), (L.unitHomEquiv.symm s)) : (_, _) ⟶ (_, _)))))
    (U : TopologicalSpace.Opens X.carrier)
    (eU : L.over U ≅ SheafOfModules.unit ((structureSheafRing X).over U))
    (x : X.carrier) (hxU : x ∈ U) :
    Function.Injective
      (fun m : grpStalk X F.val x =>
        (X.presheaf.germ U x hxU
            ((eU.hom.val.app (.op (Over.mk (𝟙 U)))).hom (s.eval (.op U)))) • m) := by
  have hinj := @lTensor_stalkMap_injective_of_tensorSheafMap_mono X F
    (SheafOfModules.unit (structureSheafRing X)) L (L.unitHomEquiv.symm s) x hs
  have hreg := smulRegular_of_lTensor_injective
    (stalkMapL X _ _ (L.unitHomEquiv.symm s).val x)
    (Stacks.IdealTorsion.unitStalkLinearEquiv X x) (frameStalkLinearEquiv X L eU x hxU) _
    (frameStalkLinearEquiv_section X L eU s x hxU) hinj
  exact fun m n h => hreg h

end RingedSpace

/-- The frame coordinate at `x` of a global section `s` of an invertible module is a
nonzerodivisor on the stalk of `F`, whenever multiplication by `s` is injective on `F`. -/
private lemma smulRegular_frameCoordinate_of_mono_section
    (X : Scheme.{u}) (F L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    (hs : Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (((𝟙 F), (L.unitHomEquiv.symm s)) : (_, _) ⟶ (_, _)))))
    (U : X.affineOpens)
    (eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (x : X) (hxU : x ∈ U.1) :
    IsSMulRegular (F.presheaf.stalk x)
      (X.presheaf.germ U.1 x hxU
        (Stacks.Divisors.frameSections X L eU
          (L.presheaf.map (homOfLE le_top).op (s.eval (.op ⊤))))) := by
  have hcoord : (eU.hom.val.app (.op (Over.mk (𝟙 U.1)))).hom (s.eval (.op U.1)) =
      Stacks.Divisors.frameSections X L eU
        (L.presheaf.map (homOfLE le_top).op (s.eval (.op ⊤))) := by
    change _ = (eU.hom.val.app (.op (Over.mk (𝟙 U.1)))).hom
      (L.presheaf.map (homOfLE le_top).op (s.eval (.op ⊤)))
    congr 1
    exact (PresheafOfModules.sections_property s (homOfLE le_top).op).symm
  intro m n h
  rw [← hcoord] at h
  exact injective_smul_frameCoordinate_of_mono_section X.toRingedSpace F L s hs U.1
    eU x hxU h


public lemma supportDim_eq_zero_of_isFiniteLength
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : IsFiniteLength R M) : Module.supportDim R M = 0 := by
  unfold Module.supportDim
  rw [support_of_isFiniteLength hM]
  exact Order.krullDim_eq_zero

private lemma supportDim_eq_one_of_regular_of_finiteLength_quotient
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (a : R) (ha : IsSMulRegular M a) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hQ : IsFiniteLength R (QuotSMulTop a M)) : Module.supportDim R M = 1 := by
  letI : Nontrivial (QuotSMulTop a M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal M ham
  have h := Module.supportDim_quotSMulTop_succ_eq_supportDim ha ham
  rw [supportDim_eq_zero_of_isFiniteLength hQ, zero_add] at h
  exact h.symm

private lemma length_quotSMulTop_eq_sum_of_regular_of_finiteLength_quotient
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (a : R) (ha : IsSMulRegular M a) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hQ : IsFiniteLength R (QuotSMulTop a M)) :
    Module.length R (QuotSMulTop a M) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
        Module.length R (R ⧸ (Ideal.span {a} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) :=
  length_quotSMulTop_eq_sum_of_regular_of_supportDim_eq_one a ha ham
    (supportDim_eq_one_of_regular_of_finiteLength_quotient a ha ham hQ)

private lemma relativeDimension_le_of_mem_support
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (F : X.Modules) [F.IsCoherent]
    (x : X) (hx : x ∈ SheafOfModules.supp F) :
    (relativeDimension C.dimensionFunction p x : EInt) ≤
      schemeDeltaDimension C
        ((reducedSupport F).subschemeι ≫ p) := by
  have hxZ : x ∈ Set.range (reducedSupport F).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]
    exact hx
  obtain ⟨z, rfl⟩ := hxZ
  exact relativeDimension_le_closedSubschemeDimension_at C p (reducedSupport F).subschemeι z

/-- On the support of `F`, the relative dimension is at most `k + 1` when the support has
delta-dimension at most `k + 1`. -/
private lemma relativeDimension_le_succ_of_mem_support
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    {x : X} (hx : x ∈ SheafOfModules.supp F) :
    relativeDimension C.dimensionFunction p x ≤ k + 1 :=
  WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp
    ((relativeDimension_le_of_mem_support C p F x hx).trans hF))

/-- A point where the cycle of a coherent sheaf has nonzero coefficient lies in its support. -/
private lemma mem_supp_of_cycleAssociatedToCoherentSheaf_ne_zero
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    {x : X} (hx : (cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1 x ≠ 0) :
    x ∈ SheafOfModules.supp F := by
  rw [cycleAssociatedToCoherentSheaf_apply] at hx
  split_ifs at hx with h
  · exact h.1
  · exact (hx rfl).elim

private lemma dimension_pullback_support_le_of_avoid
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (i : Y ⟶ X) [IsClosedImmersion i]
    (F : X.Modules) [F.IsCoherent]
    (G : Y.Modules) [G.IsCoherent] (k : ℤ)
    (hG : SheafOfModules.supp G ⊆ i ⁻¹' SheafOfModules.supp F)
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    (havoid : ∀ x ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction p x = k + 1 →
        x ∉ Set.range i) :
    schemeDeltaDimension C
      ((reducedSupport G).subschemeι ≫ i ≫ p) ≤ (k : EInt) := by
  let Z := reducedSupport G
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun W => ?_
  let ξ := W.2.1.genericPoint
  have hξG : Z.subschemeι ξ ∈ SheafOfModules.supp G := by
    rw [← coe_support_reducedSupport G, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨ξ, rfl⟩
  have hξF := hG hξG
  have hle' := relativeDimension_le_succ_of_mem_support C p k F hF hξF
  have hne : relativeDimension C.dimensionFunction p (i (Z.subschemeι ξ)) ≠ k + 1 := by
    intro he
    exact havoid _ hξF he ⟨Z.subschemeι ξ, rfl⟩
  have hlt : relativeDimension C.dimensionFunction p (i (Z.subschemeι ξ)) ≤ k := by omega
  change (relativeDimension C.dimensionFunction
    (Z.subschemeι ≫ i ≫ p) ξ : EInt) ≤ _
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction Z.subschemeι (i ≫ p) ξ,
    relativeDimension_comp_closedImmersion C.dimensionFunction i p (Z.subschemeι ξ)]
  exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hlt)


private lemma not_mem_zeroScheme_support_of_top_dimension
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    (hs : Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (((𝟙 F), (L.unitHomEquiv.symm s)) : (_, _) ⟶ (_, _))))) (x : X)
    (hx : x ∈ SheafOfModules.supp F)
    (hδ : relativeDimension C.dimensionFunction p x = k + 1) :
    x ∉ (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).support := by
  classical
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  intro hxD
  obtain ⟨Z, hZ⟩ := isGenericPoint_component_supp_of_relativeDimension_eq
    C p F (k + 1) x hF hx hδ
  letI : F.IsFiniteType := (inferInstance : F.IsCoherent).isFiniteType
  have hfg : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F x
  letI := hfg
  have hlength := isFiniteLength_stalk_of_isGenericPoint_component_supp F Z x hZ
  letI : Nontrivial (F.presheaf.stalk x) :=
    (nontrivial_iff_exists_ne (0 : F.presheaf.stalk x)).mpr hx
  letI : IsNoetherian (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).1
  obtain ⟨U, eU, _, hxU, _⟩ := exists_affine_frame_subset X L x ⊤ trivial
  exact not_smulRegular_of_mem_maximalIdeal_of_finiteLength hfg hlength
    (frame_coordinate_mem_maximalIdeal X L s U eU x hxU hxD)
    (smulRegular_frameCoordinate_of_mono_section X F L s hs U eU x hxU)

attribute [local instance] Classical.propDecidable

private lemma intersection_cycle_nonzero_mem_pullback_support
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (D : X.IdealSheafData) (F : X.Modules) [F.IsCoherent]
    (y : X) (hy : y ∈ SheafOfModules.supp F) (x : D.subscheme)
    (h : (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
      (((reducedPointClosure y).comap D.subschemeι).subschemeι) k).1 x ≠ 0) :
    x ∈ SheafOfModules.supp ((Scheme.Modules.pullback D.subschemeι).obj F) := by
  letI : F.IsFiniteType := (inferInstance : F.IsCoherent).isFiniteType
  have hx := closedSubscheme_cycle_nonzero_mem_support C (D.subschemeι ≫ p)
    (((reducedPointClosure y).comap D.subschemeι).subschemeι) k x h
  rw [Scheme.IdealSheafData.range_subschemeι] at hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  change D.subschemeι x ∈ ((reducedPointClosure y).support : Set X) at hx
  have hclosed : IsClosed (SheafOfModules.supp F) :=
    SheafOfModules.isClosed_supp F
  have hsub : closure ({y} : Set X) ⊆ SheafOfModules.supp F :=
    closure_minimal (Set.singleton_subset_iff.mpr hy) hclosed
  rw [SheafOfModules.supp_pullback]
  exact hsub (reducedPointClosure_support y ▸ hx)

private lemma gysin_coherent_cycle_representative
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    (hs : Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (((𝟙 F), (L.unitHomEquiv.symm s)) : (_, _) ⟶ (_, _))))) :
    let α := cycleAssociatedToCoherentSheaf C p F (k + 1) hF
    let D := Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))
    ∃ β : CycleGroup C (D.subschemeι ≫ p) k,
      gysinHomomorphismOfInvertible C p k L (s.eval (.op ⊤)) α = QuotientAddGroup.mk β ∧
      ∀ x : D.subscheme, β.1 x = ∑ᶠ y : {y : X // α.1 y ≠ 0}, α.1 y.1 *
        (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
          (((reducedPointClosure y.1).comap D.subschemeι).subschemeι) k).1 x := by
  classical
  dsimp only
  apply gysinHomomorphism_eq_finsum_intersections
  intro x hx hle
  have hsupp := mem_supp_of_cycleAssociatedToCoherentSheaf_ne_zero C p k F hF hx
  have hδ := cycle_dimension_at_support C p (k + 1)
    (cycleAssociatedToCoherentSheaf C p F (k + 1) hF) x hx
  apply not_mem_zeroScheme_support_of_top_dimension C p k L s F hF hs x hsupp hδ
  apply Scheme.IdealSheafData.support_antitone hle
  change x ∈ ((reducedPointClosure x).support : Set X)
  rw [reducedPointClosure_support]
  exact subset_closure (Set.mem_singleton x)

-- The sixteen affine-localization helpers that stood here were a private copy of the public
-- declarations of
-- `StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/AffineLocalization.lean`,
-- which is now imported.  They live in namespace `AlgebraicGeometry`, opened above, so the uses
-- below name them unqualified.  Old line here -> line in that file:
--   `affineStalkModule`                             799 -> 65
--   `affineGerm`                                    805 -> 75
--   `affineGerm_map_units`                          816 -> 86
--   `germ_eq_zero_iff_exists_smul_eq_zero`          837 -> 109
--   `fromSpecSectionsIso`                           891 -> 151
--   `fromSpec_appLE_top`                            898 -> 143
--   `fromSpecSectionsIso_germ_eq_zero_iff`          906 -> 203
--   `fromSpecSectionsIso_smul`                      927 -> 159
--   `fromSpecSectionsIso_germ`                      954 -> 186
--   `germ_eq_zero_iff_exists_smul_eq_zero_affine`   973 -> 214
--   `affineGerm_exists_of_eq`                      1001 -> 239
--   `spec_exists_global_multiple`                  1015 -> 251
--   `fromSpec_stalk_smul_global`                   1075 -> 318
--   `affine_exists_global_multiple`                1134 -> 384
--   `germ_multiple_transport`                      1161 -> 416
--   `affineGerm_isLocalized`                       1171 -> 434

private lemma length_stalk_fromSpecStalk_eq_length_localized
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (z : X)
    (q : PrimeSpectrum (X.presheaf.stalk z)) :
    Module.length (X.presheaf.stalk (X.fromSpecStalk z q))
        (F.presheaf.stalk (X.fromSpecStalk z q)) =
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk z)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hyU : X.fromSpecStalk z q ∈ U := (specializes_fromSpecStalk z q).mem_open U.2 hzU
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  letI : Algebra Γ(X, U) (X.presheaf.stalk (X.fromSpecStalk z q)) :=
    (X.presheaf.germ U (X.fromSpecStalk z q) hyU).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z)
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := hU.isLocalization_stalk ⟨z, hzU⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk z q))
      (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨X.fromSpecStalk z q, hyU⟩
  letI : Module Γ(X, U) (F.presheaf.stalk z) := affineStalkModule F U z hzU
  letI : Module Γ(X, U) (F.presheaf.stalk (X.fromSpecStalk z q)) :=
    affineStalkModule F U (X.fromSpecStalk z q) hyU
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk z) (F.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk (X.fromSpecStalk z q))
      (F.presheaf.stalk (X.fromSpecStalk z q)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI hz' : IsLocalizedModule (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
      (affineGerm F U z hzU) := affineGerm_isLocalized F U hU z hzU
  haveI hy' : IsLocalizedModule
      (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal.primeCompl
      (affineGerm F U (X.fromSpecStalk z q) hyU) :=
    affineGerm_isLocalized F U hU (X.fromSpecStalk z q) hyU
  have hpy : (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal =
      Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk z)) q.asIdeal :=
    primeIdealOf_fromSpecStalk hU z hzU q hyU
  have hT : (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal.primeCompl =
      q.asIdeal.primeCompl.comap (algebraMap Γ(X, U) (X.presheaf.stalk z)) := by
    ext r
    change r ∉ (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal ↔
      algebraMap Γ(X, U) (X.presheaf.stalk z) r ∉ q.asIdeal
    rw [hpy]
    rfl
  exact length_eq_of_localized_at_prime (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
    (affineGerm F U z hzU) q.asIdeal
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (F.presheaf.stalk z))
    (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal.primeCompl hT
    (affineGerm F U (X.fromSpecStalk z q) hyU)

/- A point of the fibre of `Scheme.fromSpecStalk` at `z` lies in the support of `F`
exactly when the corresponding prime lies in the support of the stalk of `F` at `z`. -/
private lemma mem_supp_fromSpecStalk_iff {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (z : X) (q : PrimeSpectrum (X.presheaf.stalk z)) :
    (X.fromSpecStalk z q ∈ SheafOfModules.supp F ↔
      q ∈ Module.support (X.presheaf.stalk z) (F.presheaf.stalk z)) := by
  have hlen := length_stalk_fromSpecStalk_eq_length_localized F z q
  have h1 : Module.length (X.presheaf.stalk (X.fromSpecStalk z q))
      (F.presheaf.stalk (X.fromSpecStalk z q)) = 0 ↔
      Subsingleton (F.presheaf.stalk (X.fromSpecStalk z q)) := Module.length_eq_zero_iff
  have h2 : Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk z)) = 0 ↔
      Subsingleton (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk z)) :=
    Module.length_eq_zero_iff
  have key : Nontrivial (F.presheaf.stalk (X.fromSpecStalk z q)) ↔
      Nontrivial (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk z)) := by
    rw [← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton,
      ← h1, ← h2, hlen]
  exact (nontrivial_iff_exists_ne
    (0 : F.presheaf.stalk (X.fromSpecStalk z q))).symm.trans key

/- A point of the support of `F` strictly specialising to a point of relative
dimension `k` has relative dimension `k + 1`, as the support has dimension at most
`k + 1`. -/
private lemma relativeDimension_eq_succ_of_specializes
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    {y z : X} (hy : y ∈ SheafOfModules.supp F) (hspec : y ⤳ z) (hne : y ≠ z)
    (hz : relativeDimension C.dimensionFunction p z = k) :
    relativeDimension C.dimensionFunction p y = k + 1 := by
  have hlt := relativeDimension_lt_of_specializes C p hspec hne
  rw [hz] at hlt
  have hle' := relativeDimension_le_succ_of_mem_support C p k F hF hy
  omega

/- The coefficient of the cycle of a coherent sheaf at a non-closed point of the
fibre of `Scheme.fromSpecStalk` at `z`: the length of the localization of the stalk
at `z` at the corresponding prime. -/
private lemma cycleAssociatedToCoherentSheaf_fromSpecStalk
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    (z : X) (hz : relativeDimension C.dimensionFunction p z = k)
    (q : PrimeSpectrum (X.presheaf.stalk z))
    (hq :
      q ∈ Module.support (X.presheaf.stalk z) (F.presheaf.stalk z))
    (hqne : q ≠ IsLocalRing.closedPoint (X.presheaf.stalk z)) :
    ((cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1
        (X.fromSpecStalk z q) =
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk z))).toNat : ℤ)) := by
  classical
  letI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hysupp : X.fromSpecStalk z q ∈ SheafOfModules.supp F :=
    (mem_supp_fromSpecStalk_iff F z q).mpr hq
  have hne : X.fromSpecStalk z q ≠ z := by
    intro he
    exact hqne (fromSpecStalk_injective z (he.trans
      (AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint (x := z)).symm))
  have hrel := relativeDimension_eq_succ_of_specializes C p k F hF hysupp
    (specializes_fromSpecStalk z q) hne hz
  have hdelta : deltaDimension C p
      (irreducibleSetEquivPoints.symm (X.fromSpecStalk z q)) = k + 1 := by
    have hg : (irreducibleSetEquivPoints.symm
        (X.fromSpecStalk z q)).isIrreducible.genericPoint = X.fromSpecStalk z q :=
      irreducibleSetEquivPoints.apply_symm_apply _
    simpa only [deltaDimension, hg] using hrel
  rw [cycleAssociatedToCoherentSheaf_apply, if_pos ⟨hysupp, hrel⟩]
  change ((Module.length (X.presheaf.stalk (X.fromSpecStalk z q))
    (F.presheaf.stalk (X.fromSpecStalk z q))).toNat : ℤ) = _
  rw [length_stalk_fromSpecStalk_eq_length_localized F z q]

/- The geometric sum computing the Gysin coefficient at `x`, reindexed over the
minimal primes of the support of the stalk of `F` at the image of `x`. The two
indexings correspond under `Scheme.fromSpecStalk`. -/
private lemma gysin_sum_eq_sum_minimalSupport
    (C : ChowSituation.{u}) {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    (D : X.IdealSheafData) (x : D.subscheme)
    (hδ : relativeDimension C.dimensionFunction (D.subschemeι ≫ p) x = k)
    (a : X.presheaf.stalk (D.subschemeι x))
    (hker : RingHom.ker (D.subschemeι.stalkMap x).hom = Ideal.span {a})
    (haReg :
      IsSMulRegular (F.presheaf.stalk (D.subschemeι x)) a)
    (haMax : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (D.subschemeι x)))
    (havoid : ∀ y : X, y ∈ SheafOfModules.supp F →
      relativeDimension C.dimensionFunction p y = k + 1 →
      y ∉ (D.support : Set X)) :
    ((∑ᶠ y : {y : X //
          (cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1 y ≠ 0},
        (cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1 y.1 *
          (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
            (((reducedPointClosure y.1).comap D.subschemeι).subschemeι) k).1 x) =
      ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
          Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
            (F.presheaf.stalk (D.subschemeι x))) q},
        ((Module.length (X.presheaf.stalk (D.subschemeι x))
            ((X.presheaf.stalk (D.subschemeι x)) ⧸
              (Ideal.span {a} ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              (F.presheaf.stalk (D.subschemeι x)))).toNat : ℤ)) := by
  classical
  letI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  letI : F.IsFiniteType := (inferInstance : F.IsCoherent).isFiniteType
  letI : Module.Finite (X.presheaf.stalk (D.subschemeι x))
      (F.presheaf.stalk (D.subschemeι x)) :=
        _root_.SheafOfModules.finite_stalk X.sheaf F (D.subschemeι x)
  have hzrel : relativeDimension C.dimensionFunction p (D.subschemeι x) = k := by
    rw [← relativeDimension_comp_closedImmersion C.dimensionFunction D.subschemeι p x]
    exact hδ
  have hqne : ∀ q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)),
      Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (F.presheaf.stalk (D.subschemeι x))) q →
      q ≠ IsLocalRing.closedPoint (X.presheaf.stalk (D.subschemeι x)) := by
    intro q hq he
    refine smulRegular_not_mem_minimalSupport haReg hq ?_
    rw [he]
    exact haMax
  have hsupp : ∀ q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)),
      q ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (F.presheaf.stalk (D.subschemeι x)) →
      X.fromSpecStalk (D.subschemeι x) q ∈ SheafOfModules.supp F := fun q hq =>
    (mem_supp_fromSpecStalk_iff F (D.subschemeι x) q).mpr hq
  have hrel : ∀ q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)),
      q ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (F.presheaf.stalk (D.subschemeι x)) →
      q ≠ IsLocalRing.closedPoint (X.presheaf.stalk (D.subschemeι x)) →
      relativeDimension C.dimensionFunction p
        (X.fromSpecStalk (D.subschemeι x) q) = k + 1 := by
    intro q hq hqc
    refine relativeDimension_eq_succ_of_specializes C p k F hF (hsupp q hq)
      (specializes_fromSpecStalk _ q) ?_ hzrel
    intro he
    exact hqc (fromSpecStalk_injective _ (he.trans
      (AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint (x := D.subschemeι x)).symm))
  have hterm : ∀ q ∈ {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
        Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
          (F.presheaf.stalk (D.subschemeι x))) q},
      (cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1
          (X.fromSpecStalk (D.subschemeι x) q) *
        (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
          (((reducedPointClosure (X.fromSpecStalk (D.subschemeι x) q)).comap
            D.subschemeι).subschemeι) k).1 x =
      ((Module.length (X.presheaf.stalk (D.subschemeι x))
          ((X.presheaf.stalk (D.subschemeι x)) ⧸
            (Ideal.span {a} ⊔ q.asIdeal))).toNat : ℤ) *
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl
            (F.presheaf.stalk (D.subschemeι x)))).toNat : ℤ) := by
    intro q hq
    have hgeneric := exists_genericPoint_comap_reducedPointClosure C p k D x
      (X.fromSpecStalk (D.subschemeι x) q) (specializes_fromSpecStalk _ q)
      (havoid _ (hsupp q hq.1) (hrel q hq.1 (hqne q hq))) (hrel q hq.1 (hqne q hq)) hδ
    rw [cycleAssociatedToCoherentSheaf_fromSpecStalk C p k F hF (D.subschemeι x) hzrel q
        hq.1 (hqne q hq),
      intersectionCycleCoeff_eq_length_quotient_sup C p D k x a hker q hgeneric hδ]
    exact mul_comm _ _
  have hinj : Set.InjOn (fun q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) =>
      X.fromSpecStalk (D.subschemeι x) q)
      {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
        Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
          (F.presheaf.stalk (D.subschemeι x))) q} :=
    fun q _ q' _ h => fromSpecStalk_injective _ h
  have hP : ∀ y ∈ Function.support (fun y : X =>
        (cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1 y *
          (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
            (((reducedPointClosure y).comap D.subschemeι).subschemeι) k).1 x),
      ((cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1 y ≠ 0 ↔
        y ∈ (fun q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) =>
            X.fromSpecStalk (D.subschemeι x) q) ''
          {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
            Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
              (F.presheaf.stalk (D.subschemeι x))) q}) := by
    intro y hy
    have hy' : (cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1 y *
        (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
          (((reducedPointClosure y).comap D.subschemeι).subschemeι) k).1 x ≠ 0 := hy
    have hα : (cycleAssociatedToCoherentSheaf C p F (k + 1) hF).1 y ≠ 0 :=
      fun h => hy' (by rw [h, zero_mul])
    have hβ : (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
        (((reducedPointClosure y).comap D.subschemeι).subschemeι) k).1 x ≠ 0 :=
      fun h => hy' (by rw [h, mul_zero])
    refine ⟨fun _ => ?_, fun _ => hα⟩
    have hysupp := mem_supp_of_cycleAssociatedToCoherentSheaf_ne_zero C p k F hF hα
    have hyrel : relativeDimension C.dimensionFunction p y = k + 1 :=
      cycle_dimension_at_support C p (k + 1)
        (cycleAssociatedToCoherentSheaf C p F (k + 1) hF) y hα
    have hxr := closedSubscheme_cycle_nonzero_mem_support C (D.subschemeι ≫ p)
      (((reducedPointClosure y).comap D.subschemeι).subschemeι) k x hβ
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_comap] at hxr
    have hclos : D.subschemeι x ∈ closure ({y} : Set X) := by
      have h : D.subschemeι x ∈ ((reducedPointClosure y).support : Set X) := hxr
      rwa [reducedPointClosure_support] at h
    have hspec : y ⤳ D.subschemeι x := specializes_iff_mem_closure.mpr hclos
    have hyrange : y ∈ Set.range (X.fromSpecStalk (D.subschemeι x)) := by
      rw [Scheme.range_fromSpecStalk]
      exact hspec
    obtain ⟨q, hqy⟩ := hyrange
    refine ⟨q, ?_, hqy⟩
    have hqmem : q ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (F.presheaf.stalk (D.subschemeι x)) :=
      (mem_supp_fromSpecStalk_iff F (D.subschemeι x) q).mp (by rw [hqy]; exact hysupp)
    refine ⟨hqmem, ?_⟩
    intro q' hq' hle'
    by_cases hqq : q' = q
    · exact le_of_eq hqq.symm
    · exfalso
      have hspec' : X.fromSpecStalk (D.subschemeι x) q' ⤳
          X.fromSpecStalk (D.subschemeι x) q :=
        ((PrimeSpectrum.le_iff_specializes q' q).mp hle').map
          (X.fromSpecStalk (D.subschemeι x)).continuous
      have hne' : X.fromSpecStalk (D.subschemeι x) q' ≠
          X.fromSpecStalk (D.subschemeι x) q := fun h =>
        hqq (fromSpecStalk_injective _ h)
      have hlt := relativeDimension_lt_of_specializes C p hspec' hne'
      have hbound := relativeDimension_le_succ_of_mem_support C p k F hF (hsupp q' hq')
      rw [hqy, hyrel] at hlt
      omega
  exact (finsum_subtype_eq_finsum_mem_image _ _ _ _ hinj hP).trans
    (finsum_mem_congr rfl hterm)

/-- The support of a coherent sheaf on which a Cartier section is regular
loses at least one dimension upon restriction to the zero scheme. -/
@[stacks 02TB "part (2): support bound"]
theorem schemeDeltaDimension_pullback_support_le_of_mono_section
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    (hs : Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (((𝟙 F), (L.unitHomEquiv.symm s)) : (_, _) ⟶ (_, _))))) :
    schemeDeltaDimension C
      ((@reducedSupport _
          ((Scheme.Modules.pullback
            (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).obj F)
          (@AlgebraicGeometry.isCoherent_pullback
            (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subscheme X
            (LocallyOfFiniteType.isLocallyNoetherian
              ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p))
            (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι F
            inferInstance)).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) ≤ (k : EInt) := by
  classical
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  letI : F.IsFiniteType := (inferInstance : F.IsCoherent).isFiniteType
  let D := Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))
  let G := (Scheme.Modules.pullback D.subschemeι).obj F
  letI : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ p)
  letI : G.IsCoherent := AlgebraicGeometry.isCoherent_pullback D.subschemeι F
  apply dimension_pullback_support_le_of_avoid C p D.subschemeι F G k
    (le_of_eq (SheafOfModules.supp_pullback D.subschemeι F)) hF
  intro x hx hδ hxD
  apply not_mem_zeroScheme_support_of_top_dimension C p k L s F hF hs x hx hδ
  change x ∈ (D.support : Set X)
  rw [← D.range_subschemeι]
  exact hxD

/-- Gysin pullback of the associated cycle of a coherent sheaf on which the
section is regular is the associated cycle of its restriction. -/
@[stacks 02TB "part (2): Gysin formula"]
theorem gysinHomomorphismOfInvertible_cycleAssociatedToCoherentSheaf
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (F : X.Modules) [F.IsCoherent]
    (hF : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ p) ≤
        ((k + 1 : ℤ) : EInt))
    (hs : Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (((𝟙 F), (L.unitHomEquiv.symm s)) : (_, _) ⟶ (_, _))))) :
    gysinHomomorphismOfInvertible C p k L (s.eval (.op ⊤))
        (cycleAssociatedToCoherentSheaf C p F
          (k + 1) hF) =
      QuotientAddGroup.mk
        (@cycleAssociatedToCoherentSheaf _ C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) inferInstance
          ((Scheme.Modules.pullback
            (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).obj F)
          (@AlgebraicGeometry.isCoherent_pullback
            (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subscheme X
            (LocallyOfFiniteType.isLocallyNoetherian
              ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p))
            (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι F
            inferInstance) k
          (by
            exact schemeDeltaDimension_pullback_support_le_of_mono_section
              C p k L s F hF hs)) := by
  classical
  obtain ⟨β, hβ, hcoeff⟩ := gysin_coherent_cycle_representative C p k L s F hF hs
  rw [hβ]
  apply congrArg QuotientAddGroup.mk
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  rw [hcoeff, cycleAssociatedToCoherentSheaf_apply]
  let D := Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))
  let G := (Scheme.Modules.pullback D.subschemeι).obj F
  by_cases hd : relativeDimension C.dimensionFunction
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) x = k
  · by_cases hxG : x ∈ SheafOfModules.supp G
    · rw [if_pos ⟨hxG, hd⟩]
      letI : IsLocallyNoetherian D.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ p)
      letI : G.IsCoherent := AlgebraicGeometry.isCoherent_pullback D.subschemeι F
      have hbound : schemeDeltaDimension C
          ((reducedSupport G).subschemeι ≫
            D.subschemeι ≫ p) ≤ (k : EInt) := by
        simpa only [D, G] using
          (schemeDeltaDimension_pullback_support_le_of_mono_section
            C p k L s F hF hs)
      have hδ : relativeDimension C.dimensionFunction
          (D.subschemeι ≫ p) x = k := hd
      obtain ⟨Z, hZ⟩ := isGenericPoint_component_supp_of_relativeDimension_eq
        C (D.subschemeι ≫ p) G k x hbound hxG hδ
      have hfinite :
          IsFiniteLength (D.subscheme.presheaf.stalk x) (G.presheaf.stalk x) :=
        isFiniteLength_stalk_of_isGenericPoint_component_supp G Z x hZ
      let z := D.subschemeι x
      letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
      letI : F.IsFiniteType := (inferInstance : F.IsCoherent).isFiniteType
      letI : Module.Finite (X.presheaf.stalk z) (F.presheaf.stalk z) :=
        _root_.SheafOfModules.finite_stalk X.sheaf F z
      obtain ⟨U, eU, _, hzU, _⟩ := exists_affine_frame_subset X L z ⊤ trivial
      let a : X.presheaf.stalk z := (X.presheaf.germ U.1 z hzU).hom
        (Stacks.Divisors.frameSections X L eU
          (L.presheaf.map (homOfLE le_top).op (s.eval (.op ⊤))))
      have hker : RingHom.ker (D.subschemeι.stalkMap x).hom = Ideal.span {a} :=
        ker_zeroScheme_stalkMap_of_frame X L s U eU x hzU
      letI : Algebra (X.presheaf.stalk z) (D.subscheme.presheaf.stalk x) :=
        (D.subschemeι.stalkMap x).hom.toAlgebra
      let e : G.presheaf.stalk x ≃ₗ[D.subscheme.presheaf.stalk x]
          (D.subscheme.presheaf.stalk x) ⊗[X.presheaf.stalk z]
            (F.presheaf.stalk z) :=
        AlgebraicGeometry.Scheme.Modules.pullbackStalkEquiv D.subschemeι F x
      have hlen : Module.length (D.subscheme.presheaf.stalk x) (G.presheaf.stalk x) =
          Module.length (X.presheaf.stalk z) (QuotSMulTop a (F.presheaf.stalk z)) :=
        e.length_eq.trans
          (length_tensor_eq_length_quotSMulTop
            (D.subschemeι.stalkMap_surjective x) a hker)
      have hQ : IsFiniteLength (X.presheaf.stalk z)
          (QuotSMulTop a (F.presheaf.stalk z)) :=
        Module.length_ne_top_iff.mp (by
          rw [← hlen]
          exact Module.length_ne_top_iff.mpr hfinite)
      have hxF : z ∈ SheafOfModules.supp F := by
        rw [SheafOfModules.supp_pullback] at hxG
        exact hxG
      letI : Nontrivial (F.presheaf.stalk z) :=
        (nontrivial_iff_exists_ne (0 : F.presheaf.stalk z)).mpr hxF
      have haReg : IsSMulRegular (F.presheaf.stalk z) a :=
        smulRegular_frameCoordinate_of_mono_section X F L s hs U eU z hzU
      have hzD : z ∈ (D.support : Set X) := by
        rw [← D.range_subschemeι]
        exact ⟨x, rfl⟩
      have haMax : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) :=
        frame_coordinate_mem_maximalIdeal X L s U eU z hzU hzD
      have hlocal := length_quotSMulTop_eq_sum_of_regular_of_finiteLength_quotient
        a haReg haMax hQ
      have hlocalInt :
          ((Module.length (X.presheaf.stalk z)
            (QuotSMulTop a (F.presheaf.stalk z))).toNat : ℤ) =
          ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk z) |
              Minimal (· ∈ Module.support (X.presheaf.stalk z)
                (F.presheaf.stalk z)) q},
            ((Module.length (X.presheaf.stalk z)
              ((X.presheaf.stalk z) ⧸ (Ideal.span {a} ⊔ q.asIdeal)) *
              Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk z))).toNat : ℤ) := by
        rw [hlocal]
        apply intCast_toNat_finsum_mem_of_sum_ne_top _
          (finite_minimalSupport (R := X.presheaf.stalk z)
            (M := F.presheaf.stalk z))
        rw [← hlocal]
        exact Module.length_ne_top_iff.mpr hQ
      have hlocalInt' :
          ((Module.length (X.presheaf.stalk z)
            (QuotSMulTop a (F.presheaf.stalk z))).toNat : ℤ) =
          ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk z) |
              Minimal (· ∈ Module.support (X.presheaf.stalk z)
                (F.presheaf.stalk z)) q},
            ((Module.length (X.presheaf.stalk z)
              ((X.presheaf.stalk z) ⧸ (Ideal.span {a} ⊔ q.asIdeal))).toNat : ℤ) *
              ((Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk z))).toNat : ℤ) := by
        simpa only [ENat.toNat_mul, Nat.cast_mul] using hlocalInt
      change _ = ((Module.length (D.subscheme.presheaf.stalk x)
        (G.presheaf.stalk x)).toNat : ℤ)
      rw [hlen, hlocalInt']
      exact gysin_sum_eq_sum_minimalSupport C p k F hF D x hδ a hker haReg haMax
        (fun y hy hr => not_mem_zeroScheme_support_of_top_dimension
          C p k L s F hF hs y hy hr)
    · rw [if_neg (fun h => hxG h.1)]
      apply finsum_eq_zero_of_forall_eq_zero
      intro y
      have hyF := mem_supp_of_cycleAssociatedToCoherentSheaf_ne_zero C p k F hF y.2
      by_cases hcy :
          (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
            (((reducedPointClosure y.1).comap D.subschemeι).subschemeι) k).1 x = 0
      · rw [hcy, mul_zero]
      · exact (hxG (intersection_cycle_nonzero_mem_pullback_support
          C p k D F y.1 hyF x hcy)).elim
  · rw [if_neg (fun h => hd h.2), ← hcoeff x]
    by_contra hne
    have hδ := cycle_dimension_at_support C
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) k β x hne
    let W : IrreducibleCloseds (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subscheme :=
      irreducibleSetEquivPoints.symm x
    have hg : W.isIrreducible.genericPoint = x :=
      irreducibleSetEquivPoints.apply_symm_apply x
    exact hd (by simpa only [deltaDimension, hg] using hδ)

end Stacks.Chow
