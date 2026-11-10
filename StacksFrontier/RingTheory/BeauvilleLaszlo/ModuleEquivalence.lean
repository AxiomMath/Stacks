module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueingData
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory

@[expose] public section

/-!
# The Beauville--Laszlo equivalence for modules

Let `(R → S, f)` be a Beauville--Laszlo glueing pair. Extension of scalars to `S` and
localization away from `f` send an `R`-module to a glueing datum for the one-element family
`f`, and this assignment identifies the category of *glueable* `R`-modules with the category
of module glueing data. For a module that is not glueable, the canonical map to the compatible
sections of its glueing datum is still surjective and becomes an isomorphism after either of
the two base changes.

## Main definitions

* `glueableModules f` is the object property of `ModuleCat R` cutting out the modules whose
  canonical Beauville--Laszlo module sequence is short exact.
* `canonicalOnGlueableModules f C` is the canonical glueing-data functor of the formal-glueing
  construction `C`, restricted to the glueable modules.

## Main results

* `canonicalOnGlueableModules_isEquivalence` (Stacks 0BP2): the restricted canonical functor is
  an equivalence of categories; compatible sections of any glueing datum are glueable; and the
  canonical unit is bijective after extension of scalars to `S` and after localization away
  from `f`, for every module.
* `canonicalToSections_surjective` (Stacks 0BP9): for an arbitrary `R`-module `M` the canonical
  map to the compatible sections of its glueing datum is surjective, its target is glueable,
  and it is bijective after either base change.

## Implementation notes

The source's category of glueable modules is realized as the full subcategory of `ModuleCat R`
cut out by short exactness of the canonical module sequence (`ObjectProperty.FullSubcategory`).
The single glueing element `f` is fed to the finite-family formal-glueing construction
`FormalGlueing.moduleGlueingConstruction` (Stacks 05EL) as the family indexed by `Fin 1`.

The inverse of the equivalence is the compatible-sections functor. The two base-change
statements recorded alongside the equivalence — bijectivity of `S ⊗ η` and of `η_f` for the
canonical unit `η` — hold for every module, glueable or not, and this is exactly what the proof
of Stacks 0BP9 needs. Isomorphisms of modules are expressed as bijectivity of the
corresponding canonical linear maps, and the generic tensor factor is written in the order
used by the glueing-data construction.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0BP9](https://stacks.math.columbia.edu/tag/0BP9)
-/

namespace BeauvilleLaszlo
section

open CategoryTheory
open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The full-subcategory property of being glueable for `(R → S, f)`: the canonical
Beauville--Laszlo module sequence is short exact. -/
public abbrev glueableModules (f : R) : ObjectProperty (ModuleCat.{w} R) :=
  fun M ↦ (beauvilleLaszloModuleSequence (S := S) M f).ShortExact

/-- The canonical functor from glueable modules to glueing data for a single element. -/
public noncomputable def canonicalOnGlueableModules (f : R)
    (C : FormalGlueing.ModuleGlueingConstruction.{u, v, w} S (fun _ : Fin 1 ↦ f)) :
    letI := C.category
    (glueableModules.{u, v, max u v w} (S := S) f).FullSubcategory ⥤
      FormalGlueing.ModuleGlueingDatum S (fun _ : Fin 1 ↦ f) C.comparison :=
  by
    letI := C.category
    exact (glueableModules.{u, v, max u v w} (S := S) f).ι ⋙ C.canonical

/-- Extension of scalars of an `R`-linear map into an `S`-module, as an `S`-linear map out of
the base change. -/
private noncomputable abbrev extendScalars
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (g : M →ₗ[R] N) : S ⊗[R] M →ₗ[S] N :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton S _ g)

private theorem extendScalars_tmul
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (g : M →ₗ[R] N) (s : S) (m : M) :
    extendScalars g (s ⊗ₜ[R] m) = s • g m := rfl


end

section

open CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

/-- Extension of scalars of an `R`-linear map into an `S`-module, as an `S`-linear map out of
the base change.

This is the form of the construction that the glueing of *algebras* along a Beauville--Laszlo
pair consumes, which needs the comparison maps of the module theorem by name. -/
public noncomputable abbrev extendScalarsMap
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (g : M →ₗ[R] N) : S ⊗[R] M →ₗ[S] N :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton S _ g)

private theorem extendScalarsMap_tmul
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (g : M →ₗ[R] N) (s : S) (m : M) :
    extendScalarsMap g (s ⊗ₜ[R] m) = s • g m := rfl

/-- The glueing-pair hypothesis in the `Ideal.quotientMap` form used by Stacks 0BNK. -/
private theorem quotientMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) (h : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (n : ℕ) (hn : 0 < n) :
    Function.Bijective (Ideal.quotientMap
      (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
      (algebraMap R S) Ideal.le_comap_map) := by
  have he : Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n) =
      (Ideal.span {algebraMap R S f}) ^ n := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  suffices ∀ (J : Ideal S) (hJ : (Ideal.span {f}) ^ n ≤ J.comap (algebraMap R S)),
      J = (Ideal.span {algebraMap R S f}) ^ n →
      Function.Bijective (Ideal.quotientMap J (algebraMap R S) hJ) from
    this _ _ he
  intro J hJ he
  subst J
  exact h n hn

/-- If `f ^ n • x = 0`, then every element of `(f) ^ n` kills `x`. -/
private theorem smul_eq_zero_of_mem_span_pow
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : R} {n : ℕ} {x : M}
    (hx : f ^ n • x = 0) : ∀ r ∈ (Ideal.span {f}) ^ n, r • x = 0 := by
  intro r hr
  rw [Ideal.span_singleton_pow] at hr
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [mul_smul, hx, smul_zero]

/-- A map that is surjective after extension of scalars to `S` and after localization away from
`f` is surjective, for a glueing pair `(R → S, f)`. -/
private theorem surjective_of_tensor_and_localization_surjective
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : R) (h : M →ₗ[R] N)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (ht : Function.Surjective (h.lTensor S))
    (hl : Function.Surjective (LocalizedModule.map (Submonoid.powers f) h)) :
    Function.Surjective h := by
  let Q := N ⧸ h.range
  let : Subsingleton (LocalizedModule (Submonoid.powers f) Q) :=
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ h).mp hl
  have hQ : ∀ q : Q, ∃ n : ℕ, ∀ r ∈ (Ideal.span {f}) ^ n, r • q = 0 := by
    intro q
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) Q)).mp
          (show LocalizedModule.mkLinearMap (Submonoid.powers f) Q q = 0 from
            Subsingleton.elim _ _)
    exact ⟨n, smul_eq_zero_of_mem_span_pow hn⟩
  have hi := ((_root_.tensorProduct_mk_bijective_of_ideal_power_torsion
    R (Ideal.span {f}) Q hQ).1 S (quotientMap_bijective f hquot)).1
  have hc : (h.range.mkQ.lTensor S).comp (h.lTensor S) = 0 := by
    apply TensorProduct.ext'
    intro s m
    change s ⊗ₜ[R] h.range.mkQ (h m) = 0
    rw [show h.range.mkQ (h m) = 0 from
      (Submodule.Quotient.mk_eq_zero h.range).mpr ⟨m, rfl⟩, TensorProduct.tmul_zero]
  intro n
  apply (Submodule.Quotient.mk_eq_zero h.range).mp
  apply hi
  change h.range.mkQ n ⊗ₜ[R] (1 : S) = (0 : Q) ⊗ₜ[R] (1 : S)
  rw [TensorProduct.zero_tmul]
  obtain ⟨x, hx⟩ := ht (1 ⊗ₜ[R] n)
  have hz := DFunLike.congr_fun hc x
  rw [LinearMap.comp_apply, hx, LinearMap.lTensor_tmul, LinearMap.zero_apply] at hz
  simpa only [TensorProduct.comm_tmul, map_zero] using
    congrArg (TensorProduct.comm R S Q) hz

/-- A submodule of a product of an `S`-module and an `R_f`-module is glueable. -/
private theorem submodule_prod_glueable
    {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
    [AddCommGroup B] [Module R B] (f : R)
    [Module (Localization.Away f) B] [IsScalarTower R (Localization.Away f) B]
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (P : Submodule R (A × B)) :
    (beauvilleLaszloModuleSequence (S := S) P f).ShortExact := by
  apply ((beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap.1
    R S P f hquot).2.2.2.2 hglue).mpr
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  let t : Submodule.torsion' R P (Submonoid.powers f) := x - y
  have htensor : (t.1 : P) ⊗ₜ[R] (1 : S) = 0 := by
    have h : (x.1 : P) ⊗ₜ[R] (1 : S) = y.1 ⊗ₜ[R] (1 : S) := congrArg Subtype.val hxy
    change (x.1 - y.1) ⊗ₜ[R] (1 : S) = 0
    rw [TensorProduct.sub_tmul, h, sub_self]
  have hp : t.1.1.1 = 0 := by
    have h := congrArg
      (fun x ↦ extendScalarsMap (S := S) ((LinearMap.fst R A B).comp P.subtype)
        ((TensorProduct.comm R P S) x)) htensor
    simpa only [TensorProduct.comm_tmul, map_zero, extendScalarsMap_tmul, one_smul,
      LinearMap.comp_apply, LinearMap.fst_apply, Submodule.subtype_apply] using h
  have hq : t.1.1.2 = 0 := by
    obtain ⟨r, hr⟩ := t.2
    let : IsLocalizedModule (Submonoid.powers f) (LinearMap.id : B →ₗ[R] B) :=
      isLocalizedModule_id (Submonoid.powers f) B (Localization.Away f)
    apply IsLocalizedModule.smul_injective (LinearMap.id : B →ₗ[R] B) r
    have h := congrArg (fun m : P ↦ m.1.2) hr
    exact h.trans (smul_zero r).symm
  exact Subtype.ext (Prod.ext hp hq)

/-- A submodule of a product of an `S`-module and an `R_f`-module is glueable, stated for the
consumers of the module theorem outside this file. -/
public alias shortExact_submodule_prod := submodule_prod_glueable

section Kernel

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
  [AddCommGroup B] [Module R B]
  (f : R) [Module (Localization.Away f) B] [IsScalarTower R (Localization.Away f) B]
  (α : LocalizedModule.Away (algebraMap R S f) A ≃ₗ[S] S ⊗[R] B)

/-- The difference map `A × B → A_f` of a glueing datum. -/
private noncomputable abbrev difference : (A × B) →ₗ[R]
    LocalizedModule.Away (algebraMap R S f) A :=
  ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) A).restrictScalars R).comp
      (LinearMap.fst R A B) -
    ((α.symm.toLinearMap.restrictScalars R).comp (TensorProduct.mk R S B 1)).comp
      (LinearMap.snd R A B)

/-- The `R`-module glued from a glueing datum: the kernel of the difference map. -/
private noncomputable abbrev kernel := LinearMap.ker (difference f α)

private noncomputable abbrev genericProjection : kernel f α →ₗ[R] A :=
  (LinearMap.fst R A B).comp (LinearMap.ker (difference f α)).subtype

private noncomputable abbrev localProjection : kernel f α →ₗ[R] B :=
  (LinearMap.snd R A B).comp (LinearMap.ker (difference f α)).subtype

omit [Module (Localization.Away f) B] [IsScalarTower R (Localization.Away f) B] in
private theorem kernel_compatibility (m : kernel f α) :
    LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) A m.1.1 =
      α.symm (1 ⊗ₜ[R] m.1.2) :=
  sub_eq_zero.mp m.2

private theorem localProjection_isLocalizedModule :
    IsLocalizedModule (Submonoid.powers f) (localProjection f α) := by
  let g := (LocalizedModule.mkLinearMap
    (Submonoid.powers (algebraMap R S f)) A).restrictScalars R
  let : IsLocalizedModule (Submonoid.powers f) g :=
    IsLocalizedModule.restrictScalars_powers f _
  let : IsLocalizedModule (Submonoid.powers f) (LinearMap.id : B →ₗ[R] B) :=
    isLocalizedModule_id (Submonoid.powers f) B (Localization.Away f)
  refine ⟨IsLocalizedModule.map_units (LinearMap.id : B →ₗ[R] B), ?_, ?_⟩
  · intro b
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f) g
      (α.symm (1 ⊗ₜ[R] b))
    refine ⟨(⟨(a, s • b), ?_⟩, s), rfl⟩
    change g a - α.symm (1 ⊗ₜ[R] ((s : R) • b)) = 0
    rw [sub_eq_zero, ← hs]
    change (s : R) • α.symm (1 ⊗ₜ[R] b) = α.symm (1 ⊗ₜ[R] ((s : R) • b))
    exact (((α.symm.toLinearMap.restrictScalars R).comp
      (TensorProduct.mk R S B 1)).map_smul (s : R) b).symm
  · intro m n h
    have he : g m.1.1 = g n.1.1 := by
      change LocalizedModule.mkLinearMap _ A m.1.1 = LocalizedModule.mkLinearMap _ A n.1.1
      rw [kernel_compatibility, kernel_compatibility]
      exact congrArg (fun b ↦ α.symm (1 ⊗ₜ[R] b)) h
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) he
    exact ⟨s, Subtype.ext (Prod.ext hs (congrArg (s • ·) h))⟩

private theorem genericProjection_injective_on_torsion
    (m : kernel f α) (hm : m ∈ Submodule.torsion' R (kernel f α) (Submonoid.powers f))
    (h : genericProjection f α m = 0) : m = 0 := by
  let := localProjection_isLocalizedModule f α
  obtain ⟨s, hs⟩ := hm
  change (s : R) • m = 0 at hs
  have hb : localProjection f α m = 0 := by
    apply IsLocalizedModule.smul_injective (localProjection f α) s
    change (s : R) • localProjection f α m = (s : R) • 0
    rw [← map_smul, hs, map_zero, smul_zero]
  exact Subtype.ext (Prod.ext h hb)

private theorem genericProjection_baseChange_bijective
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact) :
    Function.Bijective (extendScalarsMap (S := S) (genericProjection f α)) := by
  let K := kernel f α
  let T := Submodule.torsion' R K (Submonoid.powers f)
  let l := (LocalizedModule.mkLinearMap
    (Submonoid.powers (algebraMap R S f)) A).restrictScalars R
  let p := extendScalarsMap (S := S) (genericProjection f α)
  obtain ⟨i, hi, ha, he, hq⟩ :=
    gluingDatum_baseChange_localizationQuotient_shortExact
      R S f (quotientMap_bijective f hquot) hglue A B α
  let a : S ⊗[R] (K ⧸ T) →ₗ[R] LocalizedModule.Away (algebraMap R S f) A :=
    (α.symm.toLinearMap.restrictScalars R).comp (i.lTensor S)
  have ha' : Function.Injective a := by
    intro x y h
    apply (TensorProduct.comm R (K ⧸ T) S).symm.injective
    apply ha
    change a ((TensorProduct.comm R (K ⧸ T) S) _) =
      a ((TensorProduct.comm R (K ⧸ T) S) _)
    simpa only [LinearEquiv.apply_symm_apply] using h
  have hp : l.comp (p.restrictScalars R) = a.comp (T.mkQ.lTensor S) := by
    ext s m
    change l (s • genericProjection f α m) = α.symm (s ⊗ₜ[R] i (T.mkQ m))
    rw [hi]
    change LocalizedModule.mkLinearMap _ A (s • m.1.1) = α.symm (s ⊗ₜ[R] m.1.2)
    rw [map_smul]
    rw [kernel_compatibility f α m]
    rw [show s ⊗ₜ[R] m.1.2 = s • (1 ⊗ₜ[R] m.1.2) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
  have hT : Function.Surjective (fun t : T ↦ (1 : S) ⊗ₜ[R] t) := by
    have ht : ∀ t : T, ∃ n : ℕ, ∀ r ∈ (Ideal.span {f}) ^ n, r • t = 0 := by
      intro t
      obtain ⟨⟨s, n, rfl⟩, hs⟩ := t.2
      exact ⟨n, fun r hr ↦ Subtype.ext (smul_eq_zero_of_mem_span_pow hs r hr)⟩
    have htensor :=
      ((_root_.tensorProduct_mk_bijective_of_ideal_power_torsion
        R (Ideal.span {f}) T ht).1 S (quotientMap_bijective f hquot)).2
    intro z
    obtain ⟨t, ht⟩ := htensor ((TensorProduct.comm R S T) z)
    exact ⟨t, (TensorProduct.comm R S T).injective ht⟩
  constructor
  · apply (injective_iff_map_eq_zero p).2
    intro x hx
    have hqx : (T.mkQ.lTensor S) x = 0 := by
      apply ha'
      have hh := DFunLike.congr_fun hp x
      simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        hx, map_zero] using hh.symm
    have hxrange : x ∈ LinearMap.range (T.subtype.lTensor S) := by
      rw [← lTensor_mkQ S T]
      exact hqx
    obtain ⟨z, rfl⟩ := hxrange
    obtain ⟨t, rfl⟩ := hT z
    have hpz : genericProjection f α t.1 = 0 := by
      simpa only [p, LinearMap.lTensor_tmul, Submodule.subtype_apply,
        extendScalarsMap_tmul, one_smul] using hx
    have ht := genericProjection_injective_on_torsion f α t.1 t.2 hpz
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, ht, TensorProduct.tmul_zero]
  · intro y
    have hl : ((LinearMap.range (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S f)) A)).mkQ) (l y) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := (he (l y)).mp hl
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective S T.mkQ_surjective
      ((TensorProduct.comm R (K ⧸ T) S) z)
    have hxy : l (p x) = l y := by
      change (l.comp (p.restrictScalars R)) x = l y
      rw [hp, LinearMap.comp_apply, hx]
      exact hz
    let m : K := ⟨(y - p x, 0), by
      change l (y - p x) - α.symm (1 ⊗ₜ[R] (0 : B)) = 0
      rw [map_sub, hxy, sub_self, TensorProduct.tmul_zero, map_zero, sub_self]⟩
    refine ⟨x + 1 ⊗ₜ[R] m, ?_⟩
    change p (x + 1 ⊗ₜ[R] m) = y
    rw [map_add, extendScalarsMap_tmul, one_smul]
    change p x + (y - p x) = y
    abel


/-- The difference map `A × B → A_f` of a glueing datum, in the form the consumers of the
module theorem outside this file use. -/
public noncomputable abbrev glueDifference : (A × B) →ₗ[R]
    LocalizedModule.Away (algebraMap R S f) A :=
  ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) A).restrictScalars R).comp
      (LinearMap.fst R A B) -
    ((α.symm.toLinearMap.restrictScalars R).comp (TensorProduct.mk R S B 1)).comp
      (LinearMap.snd R A B)

/-- The `R`-module glued from a glueing datum: the kernel of the difference map. -/
public noncomputable abbrev glueKernel := LinearMap.ker (glueDifference f α)

/-- The projection of the glued module onto the `S`-side module of the datum. -/
public noncomputable abbrev glueGenericProjection : glueKernel f α →ₗ[R] A :=
  (LinearMap.fst R A B).comp (LinearMap.ker (glueDifference f α)).subtype

/-- The projection of the glued module onto the `R_f`-side module of the datum. -/
public noncomputable abbrev glueLocalProjection : glueKernel f α →ₗ[R] B :=
  (LinearMap.snd R A B).comp (LinearMap.ker (glueDifference f α)).subtype

/-- The glued module localizes, away from `f`, to the `R_f`-side module of the datum. -/
public theorem glueLocalProjection_isLocalizedModule :
    IsLocalizedModule (Submonoid.powers f) (glueLocalProjection f α) :=
  localProjection_isLocalizedModule f α

/-- Extension of scalars to `S` carries the projection onto the `S`-side module of the datum to
a bijection. -/
public theorem glueGenericProjection_baseChange_bijective
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact) :
    Function.Bijective
      (extendScalarsMap (S := S) (glueGenericProjection f α)) :=
  genericProjection_baseChange_bijective f α hquot hglue

end Kernel

section Sections

open FormalGlueing Cech

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (f : R)

private local instance restrictFromTarget_isScalarTower (M : ModuleCat.{w} S) :
    IsScalarTower R S (restrictFromTarget (R := R) S M) := IsScalarTower.of_compHom _ _ _

private noncomputable abbrev construction :=
  moduleGlueingConstruction.{u, v, w} S (fun _ : Fin 1 ↦ f)

private noncomputable local instance glueCategory :
    Category (ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (construction.{u, v, w} (S := S) f).comparison) :=
  (construction.{u, v, w} (S := S) f).category

private noncomputable local instance rawGlueCategory :
    Category (ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :=
  moduleGlueingCategory S (fun _ : Fin 1 ↦ f) (localizationComparisons _)

private theorem sections_glueable
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    glueableModules (S := S) f ((construction.{u, v, w} (S := S) f).sections.obj X) := by
  let A := restrictFromTarget (R := R) S X.generic
  let B := ∀ i, restrictFromAway (fun _ : Fin 1 ↦ f) i (X.localPiece i)
  let : IsScalarTower R (Localization.Away f) B :=
    ⟨fun a c b ↦ by ext i; change (a • c) • b i = _; rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact submodule_prod_glueable (S := S) (A := A) (B := B) f hquot hglue
    (compatibleSections S (fun _ : Fin 1 ↦ f) (localizationComparisons _) X)

/-- For a one-element family the only overlap is the diagonal one, on which the glueing
isomorphism of a datum is the identity. -/
private theorem diagonal_overlap
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) (i : Fin 1)
    (b : restrictFromAway (fun _ : Fin 1 ↦ f) i (X.localPiece i)) :
    X.alphaIJ i i (LocalizedModule.mkLinearMap (cechSub (fun _ : Fin 1 ↦ f) {i}) _ b) =
      LocalizedModule.mkLinearMap (cechSub (fun _ : Fin 1 ↦ f) {i}) _ b := by
  let B := restrictFromAway (fun _ : Fin 1 ↦ f) i (X.localPiece i)
  let T := cechSub (fun _ : Fin 1 ↦ f) {i}
  let L := LocalizedModule T B
  let l := LocalizedModule.mkLinearMap T B
  let j := LocalizedModule.mkLinearMap T L
  let E := (localizationComparisons (fun _ : Fin 1 ↦ f)).iterated B {i} {i}
  let F := localizedMap (fun _ : Fin 1 ↦ f) {i} (X.alphaIJ i i).toLinearMap
  let : IsLocalizedModule T (LinearMap.id : L →ₗ[R] L) :=
    isLocalizedModule_id T L (Localization T)
  let e := IsLocalizedModule.linearEquiv T (LinearMap.id : L →ₗ[R] L) j
  have hj (x : L) : e x = j x := IsLocalizedModule.linearEquiv_apply _ _ _ x
  have h := DFunLike.congr_fun (X.cocycle i i i) (E (j (l b)))
  change E (F (E.symm (E (F (E.symm (E (j (l b)))))))) =
    E (F (E.symm (E (j (l b))))) at h
  simp only [LinearEquiv.symm_apply_apply] at h
  have hh := E.injective h
  have hF (x : L) : F (j x) = j ((X.alphaIJ i i) x) :=
    localizedMap_mk (fun _ : Fin 1 ↦ f) {i} (X.alphaIJ i i).toLinearMap x
  rw [hF, hF] at hh
  have hh' := hh
  apply (X.alphaIJ i i).injective
  apply e.injective
  simpa only [hj] using hh'

/-- A map of glueing data which is bijective in each coordinate is an isomorphism. -/
private noncomputable def glueingMapIsoOfBijective
    {X Y : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))}
    (g : ModuleGlueingMap S (fun _ : Fin 1 ↦ f) (localizationComparisons _) X Y)
    (hg : Function.Bijective g.generic.hom)
    (hl : ∀ i, Function.Bijective (g.localPiece i).hom) :
    letI := (construction.{u, v, w} (S := S) f).category
    X ≅ Y := by
  letI := (construction.{u, v, w} (S := S) f).category
  let eg := LinearEquiv.ofBijective g.generic.hom hg
  let el (i : Fin 1) := LinearEquiv.ofBijective (g.localPiece i).hom (hl i)
  let k : ModuleGlueingMap S (fun _ : Fin 1 ↦ f) (localizationComparisons _) Y X :=
    { generic := ModuleCat.ofHom eg.symm.toLinearMap
      localPiece i := ModuleCat.ofHom (el i).symm.toLinearMap
      alpha_compatibility := by
        intro i m
        let : Module R (X.localPiece i) :=
          Module.compHom _ (algebraMap R (Localization.Away f))
        let : Module R (Y.localPiece i) :=
          Module.compHom _ (algebraMap R (Localization.Away f))
        let : IsScalarTower R (Localization.Away f) (X.localPiece i) :=
          IsScalarTower.of_compHom _ _ _
        let : IsScalarTower R (Localization.Away f) (Y.localPiece i) :=
          IsScalarTower.of_compHom _ _ _
        let e := TensorProduct.congr (LinearEquiv.refl R S)
          (restrictAwayLinearEquiv (fun _ : Fin 1 ↦ f) i (el i))
        change X.alpha i (LocalizedModule.mkLinearMap _ _ (eg.symm m)) =
          e.symm (Y.alpha i (LocalizedModule.mkLinearMap _ _ m))
        apply e.eq_symm_apply.mpr
        have h := (g.alpha_compatibility i (eg.symm m)).symm
        rw [show g.generic (eg.symm m) = m from eg.apply_symm_apply m] at h
        convert h using 1 <;> rfl
      alphaIJ_compatibility := by
        intro i j m
        have hij : j = i := Subsingleton.elim _ _
        subst j
        rw [diagonal_overlap, diagonal_overlap, localizedMap_mk]
        rfl }
  refine ⟨g, k, ?_, ?_⟩
  · apply ModuleGlueingMap.ext
    · ext m
      exact eg.symm_apply_apply m
    · funext i
      ext m
      exact (el i).symm_apply_apply m
  · apply ModuleGlueingMap.ext
    · ext m
      exact eg.apply_symm_apply m
    · funext i
      ext m
      exact (el i).apply_symm_apply m

/-- Compatible sections of a one-element glueing datum are the kernel of its difference map. -/
private noncomputable def sectionsKernelEquiv
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    letI : Module R X.generic := Module.compHom _ (algebraMap R S)
    letI : IsScalarTower R S X.generic := IsScalarTower.of_compHom _ _ _
    compatibleSections S (fun _ : Fin 1 ↦ f) (localizationComparisons _) X ≃ₗ[R]
      kernel f (X.alpha 0) := by
  letI : Module R X.generic := Module.compHom _ (algebraMap R S)
  letI : IsScalarTower R S X.generic := IsScalarTower.of_compHom _ _ _
  letI : Module R (X.localPiece 0) :=
    Module.compHom _ (algebraMap R (Localization.Away f))
  refine
    { toFun := fun m ↦ ⟨(m.1.1, m.1.2 0), ?_⟩
      invFun := fun m ↦ ⟨(m.1.1, fun i ↦ ?_), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  · change LocalizedModule.mkLinearMap _ X.generic m.1.1 -
      (X.alpha 0).symm (1 ⊗ₜ[R] m.1.2 0) = 0
    rw [sub_eq_zero]
    exact (X.alpha 0).eq_symm_apply.mpr (m.2.1 0)
  · exact (show i = 0 from Subsingleton.elim _ _) ▸ m.1.2
  · constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ((X.alpha 0).symm_apply_eq.mp (kernel_compatibility f (X.alpha 0) m).symm).symm
    · intro i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i; subst j
      exact diagonal_overlap f X 0 m.1.2
  · intro m
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  · intro m
    rfl

private noncomputable abbrev sectionsGeneric
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    (construction.{u, v, w} (S := S) f).sections.obj X →ₗ[R]
      restrictFromTarget (R := R) S X.generic :=
  (LinearMap.fst R _ _).comp (compatibleSections S _ _ X).subtype

private noncomputable abbrev sectionsLocal
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    (construction.{u, v, w} (S := S) f).sections.obj X →ₗ[R]
      restrictFromAway (fun _ : Fin 1 ↦ f) 0 (X.localPiece 0) :=
  (LinearMap.proj 0).comp ((LinearMap.snd R _ _).comp
    (compatibleSections S _ _ X).subtype)

private theorem sectionsLocal_isLocalizedModule
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    IsLocalizedModule (Submonoid.powers f) (sectionsLocal f X) := by
  let : Module R X.generic := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S X.generic := IsScalarTower.of_compHom _ _ _
  let := localProjection_isLocalizedModule f (X.alpha 0)
  exact IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    (localProjection f (X.alpha 0)) (sectionsKernelEquiv f X)

private theorem sectionsGeneric_baseChange_bijective
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    Function.Bijective (extendScalarsMap (S := S) (sectionsGeneric f X)) := by
  let : Module R X.generic := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S X.generic := IsScalarTower.of_compHom _ _ _
  have he : extendScalarsMap (S := S) (sectionsGeneric f X) =
      (extendScalarsMap (S := S) (genericProjection f (X.alpha 0))).comp
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
          (sectionsKernelEquiv f X)).toLinearMap := by
    ext s
    rfl
  rw [he]
  exact (genericProjection_baseChange_bijective f (X.alpha 0) hquot hglue).comp
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (sectionsKernelEquiv f X)).bijective

private noncomputable def sectionsLocalEquiv
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) (i : Fin 1) :
    ((construction.{u, v, w} (S := S) f).canonical.obj
      ((construction.{u, v, w} (S := S) f).sections.obj X)).localPiece i ≃ₗ[Localization.Away f]
        X.localPiece i := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let K := (construction.{u, v, w} (S := S) f).sections.obj X
  letI := sectionsLocal_isLocalizedModule f X
  letI : IsLocalizedModule (Submonoid.powers f)
      (canonicalLocalMk (fun _ : Fin 1 ↦ f) K 0) :=
    canonicalLocalMk_isLocalized (fun _ : Fin 1 ↦ f) K 0
  exact (IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (canonicalLocalMk (fun _ : Fin 1 ↦ f) K 0) (sectionsLocal f X)).extendScalarsOfIsLocalization
      (Submonoid.powers f) (Localization.Away f)

private theorem sectionsLocalEquiv_mk
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) (i : Fin 1)
    (m : (construction.{u, v, w} (S := S) f).sections.obj X) :
    sectionsLocalEquiv f X i
        (canonicalLocalMk (fun _ : Fin 1 ↦ f) _ i m) = m.1.2 i := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let := sectionsLocal_isLocalizedModule f X
  let := canonicalLocalMk_isLocalized (fun _ : Fin 1 ↦ f)
    ((construction.{u, v, w} (S := S) f).sections.obj X) 0
  exact IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
    (canonicalLocalMk (fun _ : Fin 1 ↦ f) _ 0) (sectionsLocal f X) m

private noncomputable def sectionsCounit
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    ModuleGlueingMap S (fun _ : Fin 1 ↦ f) (localizationComparisons _)
      ((construction.{u, v, w} (S := S) f).canonical.obj
        ((construction.{u, v, w} (S := S) f).sections.obj X)) X := by
  let K := (construction.{u, v, w} (S := S) f).sections.obj X
  letI : Module R X.generic := Module.compHom _ (algebraMap R S)
  letI : IsScalarTower R S X.generic := IsScalarTower.of_compHom _ _ _
  refine
    { generic := ModuleCat.ofHom (extendScalarsMap (S := S) (sectionsGeneric f X))
      localPiece i := ModuleCat.ofHom (sectionsLocalEquiv f X i).toLinearMap
      alpha_compatibility := ?_
      alphaIJ_compatibility := ?_ }
  · intro i t
    let : Module R (X.localPiece i) := Module.compHom _ (algebraMap R (Localization.Away f))
    let : IsScalarTower R (Localization.Away f) (X.localPiece i) := IsScalarTower.of_compHom _ _ _
    let : Module R (((construction.{u, v, w} (S := S) f).canonical.obj K).localPiece i) :=
      Module.compHom _ (algebraMap R (Localization.Away f))
    let q := (restrictAwayLinearEquiv (fun _ : Fin 1 ↦ f) i
      (sectionsLocalEquiv f X i)).toLinearMap
    have he : (X.alpha i).toLinearMap.comp
        ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) X.generic).comp
          (extendScalarsMap (S := S) (sectionsGeneric f X))) =
        (TensorProduct.AlgebraTensorModule.lTensor S S q).comp
          ((canonicalAlpha S (fun _ : Fin 1 ↦ f) K i).toLinearMap.comp
            (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) (S ⊗[R] K))) := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s m
      change X.alpha i (LocalizedModule.mkLinearMap _ _ (s • m.1.1)) =
        (TensorProduct.AlgebraTensorModule.lTensor S S q)
          (canonicalAlpha S (fun _ : Fin 1 ↦ f) K i
            (LocalizedModule.mkLinearMap _ _ (s ⊗ₜ[R] m)))
      rw [canonicalAlpha_mk, map_smul, map_smul, m.2.1 i]
      change s • ((1 : S) ⊗ₜ[R] m.1.2 i) = s ⊗ₜ[R]
        (sectionsLocalEquiv f X i (canonicalLocalMk (fun _ : Fin 1 ↦ f) K i m))
      rw [sectionsLocalEquiv_mk, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact DFunLike.congr_fun he t
  · intro i j m
    have hij : j = i := Subsingleton.elim _ _
    subst j
    rw [diagonal_overlap, diagonal_overlap, localizedMap_mk]
    rfl

private noncomputable def sectionsCounitIso
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))) :
    letI := (construction.{u, v, w} (S := S) f).category
    (construction.{u, v, w} (S := S) f).canonical.obj
      ((construction.{u, v, w} (S := S) f).sections.obj X) ≅ X :=
  glueingMapIsoOfBijective f (sectionsCounit f X)
    (sectionsGeneric_baseChange_bijective f hquot hglue X)
    (fun i ↦ (sectionsLocalEquiv f X i).bijective)

private theorem sectionsCounit_naturality
    {X Y : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f)
      (localizationComparisons (fun _ : Fin 1 ↦ f))}
    (g : ModuleGlueingMap S (fun _ : Fin 1 ↦ f) (localizationComparisons _) X Y) :
    letI := (construction.{u, v, w} (S := S) f).category
    (construction.{u, v, w} (S := S) f).canonical.map
        ((construction.{u, v, w} (S := S) f).sections.map g) ≫
      sectionsCounit f Y = sectionsCounit f X ≫ g := by
  let C := construction.{u, v, w} (S := S) f
  let := C.category
  apply ModuleGlueingMap.ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    change ∀ t : S ⊗[R] C.sections.obj X, _
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change s • g.generic m.1.1 = g.generic (s • m.1.1)
      exact (g.generic.hom.map_smul s m.1.1).symm
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    apply (ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map_injective
    apply ModuleCat.hom_ext
    let := sectionsLocal_isLocalizedModule f Y
    let : IsLocalizedModule (Submonoid.powers f)
        (canonicalLocalMk (fun _ : Fin 1 ↦ f) (C.sections.obj X) 0) :=
      canonicalLocalMk_isLocalized (fun _ : Fin 1 ↦ f) (C.sections.obj X) 0
    apply IsLocalizedModule.ext (Submonoid.powers f)
      (canonicalLocalMk (fun _ : Fin 1 ↦ f) (C.sections.obj X) 0)
      (IsLocalizedModule.map_units (sectionsLocal f Y))
    ext m
    change sectionsLocalEquiv f Y 0
        (canonicalLocalMap (fun _ : Fin 1 ↦ f) (C.sections.map g) 0
          (canonicalLocalMk (fun _ : Fin 1 ↦ f) (C.sections.obj X) 0 m)) =
      g.localPiece 0 (sectionsLocalEquiv f X 0
        (canonicalLocalMk (fun _ : Fin 1 ↦ f) (C.sections.obj X) 0 m))
    rw [canonicalLocalMap_mk, sectionsLocalEquiv_mk, sectionsLocalEquiv_mk]
    rfl

private theorem canonicalSectionsUnit_baseChange_bijective
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (M : ModuleCat.{max u v w} R) :
    Function.Bijective
      (TensorProduct.map (LinearMap.id (R := R) (M := S))
        ((construction.{u, v, w} (S := S) f).canonicalSectionsUnit.app M).hom) := by
  let X := (construction.{u, v, w} (S := S) f).canonical.obj M
  let p := extendScalarsMap (S := S) (sectionsGeneric f X)
  let t := TensorProduct.map (LinearMap.id (R := R) (M := S))
    ((construction.{u, v, w} (S := S) f).canonicalSectionsUnit.app M).hom
  have hp : Function.Bijective p := sectionsGeneric_baseChange_bijective f hquot hglue X
  have he' (x : S ⊗[R] M) : (show S ⊗[R] M from p (t x)) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      exact (congrArg p (map_add t x y)).trans
        ((map_add p _ _).trans (congrArg₂ (· + ·) hx hy))
    | tmul s m =>
      change s • ((1 : S) ⊗ₜ[R] m) = s ⊗ₜ[R] m
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact ⟨fun x y h ↦ by rw [← he' x, ← he' y, h], fun y ↦ ⟨p y, hp.1 (he' (p y))⟩⟩

private theorem canonicalSectionsUnit_localized_bijective
    (M : ModuleCat.{max u v w} R) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers f)
      ((construction.{u, v, w} (S := S) f).canonicalSectionsUnit.app M).hom) := by
  let X := (construction.{u, v, w} (S := S) f).canonical.obj M
  let g := sectionsLocal f X
  let η := ((construction.{u, v, w} (S := S) f).canonicalSectionsUnit.app M).hom
  let := sectionsLocal_isLocalizedModule f X
  have he : g.comp η = canonicalLocalMk (fun _ : Fin 1 ↦ f) M 0 := rfl
  let : IsLocalizedModule (Submonoid.powers f) (g.comp η) := by
    rw [he]
    exact canonicalLocalMk_isLocalized (fun _ : Fin 1 ↦ f) M 0
  apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (g.comp η) g).mp
  have hm : IsLocalizedModule.map (Submonoid.powers f) (g.comp η) g η =
      LinearMap.id := by
    apply IsLocalizedModule.ext (Submonoid.powers f) (g.comp η)
      (IsLocalizedModule.map_units g)
    rw [IsLocalizedModule.map_comp, LinearMap.id_comp]
  rw [hm]
  exact Function.bijective_id

private theorem canonicalSectionsUnit_bijective
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (M : ModuleCat.{max u v w} R) (hM : glueableModules (S := S) f M) :
    Function.Bijective
      ((construction.{u, v, w} (S := S) f).canonicalSectionsUnit.app M).hom := by
  let η := ((construction.{u, v, w} (S := S) f).canonicalSectionsUnit.app M).hom
  constructor
  · apply (injective_iff_map_eq_zero η).mpr
    intro m hm
    have hl : LocalizedModule.mkLinearMap (Submonoid.powers f) M m = 0 :=
      congrArg (fun z ↦ z.1.2 0) hm
    have ht : m ∈ modulePowerTorsion M f :=
      (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mp hl
    have hi := ((beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap.1
      R S M f hquot).2.2.2.2 hglue).mp hM
    have hg : (1 : S) ⊗ₜ[R] m = 0 := congrArg (fun z ↦ z.1.1) hm
    have hz : tensorProductPowerTorsionMap (S := S) M f ⟨m, ht⟩ = 0 := by
      apply Subtype.ext
      change m ⊗ₜ[R] (1 : S) = 0
      simpa only [TensorProduct.comm_tmul, map_zero] using
        congrArg (TensorProduct.comm R S M) hg
    exact congrArg Subtype.val (hi (hz.trans (map_zero _).symm))
  · exact surjective_of_tensor_and_localization_surjective f η hquot
      (canonicalSectionsUnit_baseChange_bijective f hquot hglue M).2
      (canonicalSectionsUnit_localized_bijective f M).2

/-- **Beauville--Laszlo glueing.** For a glueing pair `(R → S, f)`, the canonical functor
from glueable `R`-modules to module glueing data is an equivalence of categories. Compatible
sections of every glueing datum are glueable, and the canonical map from any module to the
sections of its canonical datum induces isomorphisms after extension of scalars to `S` and
localization away from `f`. -/
@[stacks 0BP2]
public theorem canonicalOnGlueableModules_isEquivalence
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact) :
    let C := moduleGlueingConstruction.{u, v, w} S (fun _ : Fin 1 ↦ f)
    letI := C.category
    (canonicalOnGlueableModules f C).IsEquivalence ∧
      (∀ X : ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 ↦ f) C.comparison,
        glueableModules (S := S) f (C.sections.obj X)) ∧
      (∀ M : ModuleCat.{max u v w} R,
        Function.Bijective
            (TensorProduct.map (LinearMap.id (R := R) (M := S))
              (C.canonicalSectionsUnit.app M).hom) ∧
          Function.Bijective
            (LocalizedModule.map (Submonoid.powers f)
              (C.canonicalSectionsUnit.app M).hom)) := by
  refine ⟨?_, sections_glueable f hquot hglue, fun M ↦
    ⟨canonicalSectionsUnit_baseChange_bijective f hquot hglue M,
      canonicalSectionsUnit_localized_bijective f M⟩⟩
  let C := construction.{u, v, w} (S := S) f
  let := C.category
  let P := glueableModules.{u, v, max u v w} (S := S) f
  let G := P.lift C.sections (sections_glueable f hquot hglue)
  let η : 𝟭 P.FullSubcategory ≅ canonicalOnGlueableModules f C ⋙ G :=
    NatIso.ofComponents
      (fun M ↦ P.isoMk ((LinearEquiv.ofBijective (C.canonicalSectionsUnit.app M.obj).hom
        (canonicalSectionsUnit_bijective f hquot hglue M.obj M.property)).toModuleIso))
      (fun g ↦ P.hom_ext (C.canonicalSectionsUnit.naturality g.hom))
  let ε : G ⋙ canonicalOnGlueableModules f C ≅ 𝟭 _ :=
    NatIso.ofComponents (sectionsCounitIso f hquot hglue)
      (fun g ↦ sectionsCounit_naturality f g)
  exact Functor.IsEquivalence.mk' G η ε

end Sections

end

section

open CategoryTheory
open scoped TensorProduct

universe u v w

/-- A five-term comparison of two exact sequences: if the middle map is bijective, the right
map injective and the two squares commute, the left map is surjective. -/
private theorem surjective_of_exact_of_bijective
    {A B D A' B' D' : Type*} [Zero B] [Zero D] [Zero B'] [Zero D']
    (i : A → B) (d : B → D) (i' : A' → B') (d' : B' → D')
    (a : A → A') (b : B → B') (c : D → D')
    (h : Function.Exact i d) (h' : Function.Exact i' d')
    (hi' : Function.Injective i') (hb : Function.Bijective b)
    (hc : Function.Injective c) (hc0 : c 0 = 0)
    (sq₁ : ∀ x, b (i x) = i' (a x)) (sq₂ : ∀ x, c (d x) = d' (b x)) :
    Function.Surjective a := by
  intro x'
  obtain ⟨y, hy⟩ := hb.2 (i' x')
  have hdy : d y = 0 := by
    apply hc
    rw [sq₂, hy, h'.apply_apply_eq_zero, hc0]
  obtain ⟨x, hx⟩ := (h y).mp hdy
  refine ⟨x, hi' ?_⟩
  rw [← sq₁, hx, hy]

private theorem glueable_exact
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (f : R) (N : Type w) [AddCommGroup N] [Module R N]
    (h : glueableModules (S := S) f (ModuleCat.of R N)) :
    Function.Exact (toTensorBaseChanges (S := S) N f)
      (tensorAwayDifference (S := S) N f) := by
  change (beauvilleLaszloModuleSequence (S := S) N f).ShortExact at h
  have hex := h.exact
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  intro x
  constructor
  · intro hx
    have hx' : (beauvilleLaszloModuleSequence (S := S) N f).g ⟨x⟩ = 0 :=
      ULift.down_injective hx
    obtain ⟨y, hy⟩ := (hex ⟨x⟩).mp hx'
    change ULift.up (toTensorBaseChanges (S := S) N f y.down) = ULift.up x at hy
    exact ⟨y.down, congrArg ULift.down hy⟩
  · rintro ⟨y, rfl⟩
    simp [toTensorBaseChanges, tensorAwayDifference,
      baseChangeToAway, localizedBaseChangeToAway]

private theorem glueable_injective
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (f : R) (N : Type w) [AddCommGroup N] [Module R N]
    (h : glueableModules (S := S) f (ModuleCat.of R N)) :
    Function.Injective (toTensorBaseChanges (S := S) N f) := by
  change (beauvilleLaszloModuleSequence (S := S) N f).ShortExact at h
  exact fun x y hxy => ULift.up_injective (h.ab_injective_f (ULift.down_injective hxy))

/-- The `M`-base change of the ring Beauville--Laszlo sequence is exact in the middle, for
every module `M`: only right-exactness of the tensor product is needed. -/
private theorem tensor_beauvilleLaszlo_exact
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (f : R)
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (N : Type w) [AddCommGroup N] [Module R N] :
    Function.Exact (toTensorBaseChanges (S := S) N f)
      (tensorAwayDifference (S := S) N f) := by
  let d : R →ₗ[R] S × Localization.Away f :=
    { toFun := toBaseChangeAndAway f (algebraMap R S)
      map_add' := map_add _
      map_smul' := by intro a b; simp [Algebra.smul_def] }
  let q : (S × Localization.Away f) →ₗ[R]
      Localization.Away (algebraMap R S f) :=
    { toFun := awayDifference f (algebraMap R S)
      map_add' := map_add _
      map_smul' := by
        intro a x
        simp only [awayDifference_apply]
        simp only [Prod.smul_fst, Prod.smul_snd]
        simp only [Algebra.smul_def]
        change algebraMap S (Localization.Away (algebraMap R S f))
              (algebraMap R S a * x.1) -
            Localization.awayMap (algebraMap R S) f
              (algebraMap R (Localization.Away f) a * x.2) = _
        have ha : Localization.awayMap (algebraMap R S) f
              (algebraMap R (Localization.Away f) a) =
            algebraMap R (Localization.Away (algebraMap R S f)) a := by
          rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
          exact (IsScalarTower.algebraMap_apply R S _ a).symm
        have hb : algebraMap S (Localization.Away (algebraMap R S f))
              (algebraMap R S a) =
            algebraMap R (Localization.Away (algebraMap R S f)) a :=
          (IsScalarTower.algebraMap_apply R S _ a).symm
        rw [map_mul, map_mul, ha, hb]
        simp only [RingHom.id_apply]
        ring }
  have hex := hglue.exact
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  have hdq : Function.Exact d q := by
    intro x
    constructor
    · intro hx
      have hx' : (beauvilleLaszloSequence f (algebraMap R S)).g (ULift.up x) = 0 :=
        ULift.down_injective hx
      obtain ⟨y, hy⟩ := (hex (ULift.up x)).mp hx'
      change ULift.up (d y.down) = ULift.up x at hy
      exact ⟨y.down, congrArg ULift.down hy⟩
    · rintro ⟨y, rfl⟩
      simp [d, q, toBaseChangeAndAway, awayDifference,
        Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y, hy⟩ := hglue.ab_surjective_g (ULift.up x)
    change ULift.up (q y.down) = ULift.up x at hy
    exact ⟨y.down, congrArg ULift.down hy⟩
  have ht := lTensor_exact N hdq hq
  let E := TensorProduct.prodRight R R N S (Localization.Away f)
  have hdiff : (LinearMap.lTensor N q).comp E.symm.toLinearMap =
      tensorAwayDifference (S := S) N f := by
    ext m s
    · have hinv : E.symm (m ⊗ₜ[R] s, 0) = m ⊗ₜ[R] (s, 0) := by
        apply E.injective
        simp [E]
      change LinearMap.lTensor N q (E.symm (m ⊗ₜ[R] s, 0)) =
        tensorAwayDifference (S := S) N f (m ⊗ₜ[R] s, 0)
      rw [hinv]
      simp [q, tensorAwayDifference,
        baseChangeToAway, localizedBaseChangeToAway,
        awayDifference]
    · have hinv : E.symm (0, m ⊗ₜ[R] s) = m ⊗ₜ[R] (0, s) := by
        apply E.injective
        simp [E]
      change LinearMap.lTensor N q (E.symm (0, m ⊗ₜ[R] s)) =
        tensorAwayDifference (S := S) N f (0, m ⊗ₜ[R] s)
      rw [hinv]
      simp [q, tensorAwayDifference,
        baseChangeToAway, localizedBaseChangeToAway,
        awayDifference, TensorProduct.tmul_neg]
  intro x
  constructor
  · intro hx
    have hzero : LinearMap.lTensor N q (E.symm x) = 0 := (LinearMap.congr_fun hdiff x).trans hx
    obtain ⟨z, hz⟩ := (ht (E.symm x)).mp hzero
    refine ⟨TensorProduct.rid R N z, ?_⟩
    have hdiag_general : ∀ z : TensorProduct R N R,
        toTensorBaseChanges (S := S) N f
          (TensorProduct.rid R N z) = E (LinearMap.lTensor N d z) := by
      intro z'
      induction z' using TensorProduct.inductionOn with
      | tmul m r =>
          simp only [TensorProduct.rid_tmul, toTensorBaseChanges_apply,
            LinearMap.lTensor_tmul, d]
          change ((r • m) ⊗ₜ[R] 1, (r • m) ⊗ₜ[R] 1) =
            (m ⊗ₜ[R] algebraMap R S r,
              m ⊗ₜ[R] algebraMap R (Localization.Away f) r)
          apply Prod.ext <;> simp only <;>
            rw [TensorProduct.smul_tmul] <;>
            simp [Algebra.smul_def]
      | add a b ha hb => simp only [map_add, ha, hb]
    calc
      _ = E (LinearMap.lTensor N d z) := hdiag_general z
      _ = E (E.symm x) := congrArg E hz
      _ = x := E.apply_symm_apply x
  · rintro ⟨m, rfl⟩
    simp [toTensorBaseChanges, tensorAwayDifference,
      baseChangeToAway, localizedBaseChangeToAway]

/-- Let `(R → S, f)` be a Beauville--Laszlo glueing pair and let `M` be any
`R`-module. The canonical map from `M` to the compatible sections of its canonical
glueing datum is surjective. Its target is glueable, and the map becomes an isomorphism
after extension of scalars to `S` and after localization away from `f`.

The equations on the generic and local coordinates characterize the canonical map. -/
@[stacks 0BP9]
public theorem canonicalToSections_surjective
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (f : R)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (M : Type w) [AddCommGroup M] [Module R M] :
    let C := FormalGlueing.moduleGlueingConstruction.{u, v, w} S (fun _ : Fin 1 ↦ f)
    letI := C.category
    let X := C.canonical.obj (ModuleCat.of R (ULift.{max u v w} M))
    let Mbar := C.sections.obj X
    ∃ g : M →ₗ[R] Mbar,
      (∀ m : M,
        let x := C.sectionsObj X (g m)
        C.canonicalGeneric (ModuleCat.of R (ULift.{max u v w} M)) x.1.1 =
          1 ⊗ₜ[R] ULift.up m ∧
          C.canonicalLocal (ModuleCat.of R (ULift.{max u v w} M)) 0 (x.1.2 0) =
            LocalizedModule.mkLinearMap (Submonoid.powers f) (ULift M) (ULift.up m)) ∧
      glueableModules (S := S) f Mbar ∧
      Function.Bijective
        (TensorProduct.map (LinearMap.id (R := R) (M := S)) g) ∧
      Function.Bijective (LocalizedModule.map (Submonoid.powers f) g) ∧
      Function.Surjective g := by
  dsimp only
  let C := FormalGlueing.moduleGlueingConstruction.{u, v, w} S (fun _ : Fin 1 ↦ f)
  let := C.category
  let N := ModuleCat.of R (ULift.{max u v w} M)
  let X := C.canonical.obj N
  let Mbar := C.sections.obj X
  let e : M ≃ₗ[R] N := ULift.moduleEquiv.symm
  let u : N →ₗ[R] Mbar := (C.canonicalSectionsUnit.app N).hom
  let g : M →ₗ[R] Mbar := u.comp e.toLinearMap
  have hBP2 := canonicalOnGlueableModules_isEquivalence (S := S) f hquot hglue
  have hbar : glueableModules (S := S) f Mbar := hBP2.2.1 X
  have hs : Function.Bijective
      (TensorProduct.map (LinearMap.id (R := R) (M := S)) u) := hBP2.2.2 N |>.1
  have hl : Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) :=
    hBP2.2.2 N |>.2
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact ⟨C.canonicalSectionsUnit_generic N (e m),
      C.canonicalSectionsUnit_local N (e m) 0⟩
  · exact hbar
  · rw [show TensorProduct.map (LinearMap.id (R := R) (M := S)) g =
        (TensorProduct.map (LinearMap.id (R := R) (M := S))
          (C.canonicalSectionsUnit.app N).hom).comp
        (TensorProduct.map (LinearMap.id (R := R) (M := S)) e.toLinearMap) by
          simpa [g] using (TensorProduct.map_comp
            (LinearMap.id (R := R) (M := S)) (C.canonicalSectionsUnit.app N).hom
            (LinearMap.id (R := R) (M := S)) e.toLinearMap)]
    exact hs.comp
      (TensorProduct.map_bijective
        (Function.bijective_id : Function.Bijective (LinearMap.id (R := R) (M := S)))
        e.bijective)
  · have hmap : LocalizedModule.map (Submonoid.powers f) g =
        (LocalizedModule.map (Submonoid.powers f)
          (C.canonicalSectionsUnit.app N).hom).comp
        (LocalizedModule.map (Submonoid.powers f) e.toLinearMap) := by
      ext z
      induction z using LocalizedModule.induction_on with
      | h m s => simp [g, u]
    rw [hmap]
    exact hl.comp
      ⟨LocalizedModule.map_injective _ _ e.injective,
        LocalizedModule.map_surjective _ _ e.surjective⟩
  · suffices Function.Surjective u from this.comp e.surjective
    let sMap := TensorProduct.map u (LinearMap.id (R := R) (M := S))
    have hsMap : Function.Bijective sMap := (LinearMap.lTensor_bij_iff_rTensor_bij S u).mp hs
    let lMap₀ := LocalizedModule.map (Submonoid.powers f) u
    let LT := Localization (Submonoid.powers f)
    let lt : TensorProduct R LT N →ₗ[LT] TensorProduct R LT Mbar :=
      TensorProduct.AlgebraTensorModule.lTensor LT LT u
    let eLN := LocalizedModule.equivTensorProduct (Submonoid.powers f) N
    let eLB := LocalizedModule.equivTensorProduct (Submonoid.powers f) Mbar
    have hlocal : eLB.toLinearMap.comp lMap₀ = lt.comp eLN.toLinearMap := by
      ext z
      induction z using LocalizedModule.induction_on with
      | h m s => simp [eLN, eLB, lMap₀, lt]
    have hlt : Function.Bijective lt := by
      have h : ⇑lt = eLB ∘ lMap₀ ∘ eLN.symm := funext fun x =>
        ((LinearMap.congr_fun hlocal (eLN.symm x)).trans
          (congrArg lt (eLN.apply_symm_apply x))).symm
      rw [h]
      exact eLB.bijective.comp (hl.comp eLN.symm.bijective)
    let lMap := TensorProduct.map u (LinearMap.id (R := R) (M := Localization.Away f))
    have hlMap : Function.Bijective lMap := (LinearMap.lTensor_bij_iff_rTensor_bij LT u).mp hlt
    let b : (TensorProduct R N S × TensorProduct R N (Localization.Away f)) →ₗ[R]
        (TensorProduct R Mbar S × TensorProduct R Mbar (Localization.Away f)) :=
      LinearMap.prodMap sMap lMap
    have hb : Function.Bijective b := hsMap.prodMap hlMap
    let T := Localization.Away (algebraMap R S f)
    let us : TensorProduct R S N →ₗ[S] TensorProduct R S Mbar :=
      TensorProduct.AlgebraTensorModule.lTensor S S u
    have hus : Function.Injective us := fun _ _ hxy ↦ hs.1 hxy
    let base : TensorProduct S T (TensorProduct R S N) →ₗ[T]
        TensorProduct S T (TensorProduct R S Mbar) := us.lTensor T
    have hbase : Function.Injective base :=
      Module.Flat.lTensor_preserves_injective_linearMap us hus
    let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N
    let eB := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T Mbar
    let cu : TensorProduct R T N →ₗ[T] TensorProduct R T Mbar :=
      TensorProduct.AlgebraTensorModule.lTensor T T u
    have hcancel : eB.toLinearMap.comp (base.comp eN.symm.toLinearMap) = cu := by
      ext t
      simp [eN, eB, base, us, cu]
    have hcu : Function.Injective cu := by
      have h : ⇑cu = eB ∘ base ∘ eN.symm := funext fun x => (LinearMap.congr_fun hcancel x).symm
      rw [h]
      exact eB.injective.comp (hbase.comp eN.symm.injective)
    let c := TensorProduct.map u (LinearMap.id (R := R) (M := T))
    have hc : Function.Injective c := (LinearMap.lTensor_inj_iff_rTensor_inj T u).mp hcu
    let iN := toTensorBaseChanges (S := S) N f
    let dN := tensorAwayDifference (S := S) N f
    let iB := toTensorBaseChanges (S := S) Mbar f
    let dB := tensorAwayDifference (S := S) Mbar f
    have hbaseNat : ∀ x : TensorProduct R N S,
        c (baseChangeToAway N f x) =
          baseChangeToAway Mbar f (sMap x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul n s => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    have hlocalNat : ∀ x : TensorProduct R N (Localization.Away f),
        c (localizedBaseChangeToAway N f x) =
          localizedBaseChangeToAway Mbar f (lMap x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul n t => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    apply surjective_of_exact_of_bijective iN dN iB dB u b c
      (tensor_beauvilleLaszlo_exact f hglue N) (glueable_exact f Mbar hbar)
      (glueable_injective f Mbar hbar) hb hc (map_zero c)
    · intro n
      apply Prod.ext
      · simp [b, sMap, iN, iB, toTensorBaseChanges]
      · simp [b, lMap, iN, iB, toTensorBaseChanges]
    · intro x
      rcases x with ⟨x₁, x₂⟩
      simp only [dN, dB, tensorAwayDifference_apply, map_sub,
        b, LinearMap.prodMap_apply, hbaseNat, hlocalNat]

end

end BeauvilleLaszlo

end
