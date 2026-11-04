module

public import StacksCore.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero

/-!
# The localized ideal-power tower

Let `A` be a commutative ring, `S ⊆ A` a multiplicative subset, `I ⊆ A` an ideal and `M` an
`A`-module. Localizing the inverse system `{IⁿM}` term by term produces an inverse system of
modules over `S⁻¹A`, and localizing `M` and extending `I` produces a second one, namely the
ideal-power tower `{(S⁻¹I)ⁿ(S⁻¹M)}` of the localized module. This module identifies the two:
localization is exact and commutes with multiplication of a submodule by an ideal, so
`(IⁿM)_S = (S⁻¹I)ⁿ(M_S)` inside `M_S`, and these identifications are compatible with every
transition map of the two systems.

The comparison is pinned, not merely abstract: each component is characterized by the property
that it commutes with the two inclusions into `M_S`, which is what makes the naturality square
commute and what makes the isomorphism usable for transporting statements about transition maps.

Applying a functor to the comparison transports it to local cohomology. Over a localization
which is Noetherian and local — for instance `Localization 𝔭.primeCompl` at a prime `𝔭` — the
systems `{Hⁱ_𝔪((IⁿM)_S)}` and `{Hⁱ_𝔪((S⁻¹I)ⁿ(M_S))}` are therefore isomorphic, so a transition
map of one vanishes exactly when the corresponding transition map of the other does, and the
images of corresponding transition maps match under the isomorphism. This is the dictionary that
turns the per-prime hypotheses of
`Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_local` and
`Stacks.LocalCohomology.exists_eventually_injective_image_idealPowerTower_of_local` into
statements about the ideal-power tower of a module over a Noetherian local ring, where the local
duality computations live.

## Main definitions

* `Stacks.LocalCohomology.localizedIdealPowerEquiv` — the `S⁻¹A`-linear isomorphism
  `(IⁿM)_S ≃ (S⁻¹I)ⁿ(M_S)` at a single level `n`.
* `Stacks.LocalCohomology.localizedIdealPowerTowerIso` — the isomorphism of inverse systems
  `{IⁿM}_S ≅ {(S⁻¹I)ⁿ(M_S)}`.
* `Stacks.LocalCohomology.localizedIdealPowerTowerLocalCohomologyIso` — the induced isomorphism
  of the two local cohomology systems in a fixed degree.

## Main results

* `Submodule.localized'_pow_smul_top` — `(IⁿM)_S = (S⁻¹I)ⁿ(M_S)` as submodules of `M_S`.
* `Stacks.LocalCohomology.localizedIdealPowerInclusion_mem`,
  `Stacks.LocalCohomology.localizedIdealPowerInclusion_injective` and
  `Stacks.LocalCohomology.localizedIdealPowerInclusion_surjective` — the localization of the
  inclusion `IⁿM ⊆ M` is a bijection of `(IⁿM)_S` onto `(S⁻¹I)ⁿ(M_S)`.
* `Stacks.LocalCohomology.localizedIdealPowerEquiv_coe` — the characterization of the
  comparison by compatibility with the inclusions into `M_S`.
* `Stacks.LocalCohomology.natIso_map_eq_zero_iff` and
  `Stacks.LocalCohomology.natIso_range_map` — an isomorphism of functors preserves vanishing of
  the morphisms in its image and carries ranges to ranges.
* `Stacks.LocalCohomology.localCohomology_localizedIdealPowerTower_map_eq_zero_iff` — a
  transition map of `{Hⁱ_𝔪((IⁿM)_S)}` vanishes exactly when the corresponding transition map of
  `{Hⁱ_𝔪((S⁻¹I)ⁿ(M_S))}` does.
* `Stacks.LocalCohomology.localCohomology_localizedIdealPowerTower_range_map` — the two
  transition images correspond under the comparison.

## Implementation notes

The component isomorphism is the localization of the inclusion `IⁿM ⊆ M`, corestricted to the
submodule of `M_S` where its values lie, rather than an abstract isomorphism obtained from the
uniqueness of localizations. Taking it in this shape makes `localizedIdealPowerEquiv_coe` — the
compatibility with the two inclusions into `M_S` — hold by `rfl`, and that compatibility is what
every later proof uses.

The three inputs are the three properties of that corestriction. Membership and surjectivity
both go through `Submodule.localized'`, the submodule of `M_S` of fractions with numerator in
`IⁿM`: a fraction `x/s` with `x ∈ IⁿM` is a member by definition, and conversely every member is
of that shape, which `IsLocalizedModule.map_mk'` turns into a value of the localized inclusion.
`Submodule.localized'_pow_smul_top` identifies that submodule with `(S⁻¹I)ⁿ(M_S)`. Injectivity
is `IsLocalizedModule.map_injective`, the exactness of localization.

Naturality is then a statement about the two inclusions into `M_S`: the transition maps of both
towers are inclusions of submodules of `M_S`, and the comparison carries an element to the
element of `M_S` with the same value, so both legs of the square send an element to the same
value in `M_S` and `Subtype.ext` closes it. The statements of this section are phrased through
`ModuleCat.localizedModuleMap` rather than `ModuleCat.localizedModuleFunctor.map`, which is the
same morphism: the functor spells the type of its source as `Functor.obj`, and the `Module A`
instance on the submodule is then found only after unfolding, which `rw` and instance search do
not do.

`localCohomologyModuleFunctor` is defined at the maximal ideal of a Noetherian local ring, so the
local cohomology statements carry `[IsNoetherianRing (Localization S)]` and
`[IsLocalRing (Localization S)]`. These are properties of the localization, not restrictions on
the data: both are found by instance search at `S = 𝔭.primeCompl` for a prime `𝔭` of a
Noetherian ring, so the statements below specialize there with no further input. They are what
makes the functor applied to `Localization S` meaningful; the comparison of the towers itself
needs neither.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 00CT](https://stacks.math.columbia.edu/tag/00CT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

/-- Localizing the submodule `Iⁿ • ⊤` of `X` gives the `n`-th power of the extended ideal acting
on the localized module: `(IⁿX)_S = (S⁻¹I)ⁿ(X_S)`.

This is `Submodule.localized'_smul_top` at the ideal `Iⁿ`, together with `Ideal.map_pow` to move
the power across the extension of ideals. -/
theorem Submodule.localized'_pow_smul_top {A : Type u} [CommRing A] (S : Submonoid A)
    (I : Ideal A) (A_S : Type*) [CommRing A_S] [Algebra A A_S] [IsLocalization S A_S]
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module A X] [Module A Y] [Module A_S Y]
    [IsScalarTower A A_S Y] (φ : X →ₗ[A] Y) [IsLocalizedModule S φ] (n : ℕ) :
    (I ^ n • (⊤ : Submodule A X)).localized' A_S S φ =
      I.map (algebraMap A A_S) ^ n • (⊤ : Submodule A_S Y) := by
  rw [Submodule.localized'_smul_top, Ideal.map_pow]

namespace Stacks.LocalCohomology

/-! ### Transporting vanishing and ranges along an isomorphism of functors -/

/-- A morphism in the image of a functor vanishes exactly when the corresponding morphism in the
image of an isomorphic functor does. -/
theorem natIso_map_eq_zero_iff {C : Type*} [Category C] {D : Type*} [Category D]
    [Limits.HasZeroMorphisms D] {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    F.map f = 0 ↔ G.map f = 0 := by
  constructor <;> intro h
  · rw [← NatIso.naturality_1 e f, h]
    simp
  · rw [← NatIso.naturality_2 e f, h]
    simp

/-- An isomorphism of functors into modules carries the range of a morphism in the image of one
onto the range of the corresponding morphism in the image of the other. -/
theorem natIso_range_map {R : Type u} [CommRing R] {C : Type*} [Category C]
    {F G : C ⥤ ModuleCat.{v} R} (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    Submodule.map (e.hom.app Y).hom (LinearMap.range (F.map f).hom) =
      LinearMap.range (G.map f).hom := by
  have hsurj : LinearMap.range (e.inv.app X).hom = ⊤ :=
    LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  rw [← NatIso.naturality_1 e f,
    show ((e.inv.app X ≫ F.map f ≫ e.hom.app Y) : G.obj X ⟶ G.obj Y).hom =
      (e.hom.app Y).hom ∘ₗ ((F.map f).hom ∘ₗ (e.inv.app X).hom) from rfl,
    LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hsurj]

/-- **A containment of kernels of two morphisms out of one object transfers along an isomorphism
of functors.** The two morphisms need not have the same target; only their common source matters.

This is the kernel counterpart of `Stacks.LocalCohomology.natIso_map_eq_zero_iff` and
`Stacks.LocalCohomology.natIso_range_map`, and it is what transports the stable-image assertion of
[Stacks, Tag 0EFX] — a containment `ker(Hⁱ(IᵏM → M)) ⊆ ker(Hⁱ(IᵏM → IᵐM))` — between two
spellings of the same inverse system. -/
theorem natIso_ker_le_ker_iff {R : Type u} [CommRing R] {C : Type*} [Category C]
    {F G : C ⥤ ModuleCat.{v} R} (e : F ≅ G) {X Y Z : C} (f : X ⟶ Y) (f' : X ⟶ Z) :
    (LinearMap.ker (F.map f).hom ≤ LinearMap.ker (F.map f').hom) ↔
      (LinearMap.ker (G.map f).hom ≤ LinearMap.ker (G.map f').hom) := by
  have key : ∀ (W : C) (g : X ⟶ W) (x : F.obj X),
      ((G.map g).hom ((e.hom.app X).hom x) = 0) ↔ ((F.map g).hom x = 0) := by
    intro W g x
    have hnat := ConcreteCategory.congr_hom (e.hom.naturality g) x
    rw [show ((F.map g ≫ e.hom.app W) : F.obj X ⟶ G.obj W).hom x =
        (e.hom.app W).hom ((F.map g).hom x) from rfl,
      show ((e.hom.app X ≫ G.map g) : F.obj X ⟶ G.obj W).hom x =
        (G.map g).hom ((e.hom.app X).hom x) from rfl] at hnat
    rw [← hnat]
    exact map_eq_zero_iff _ ((ModuleCat.mono_iff_injective (e.hom.app W)).1 inferInstance)
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ : ∃ x, (e.hom.app X).hom x = y :=
      ⟨(e.inv.app X).hom y, ConcreteCategory.congr_hom (e.inv_hom_id_app X) y⟩
    rw [LinearMap.mem_ker] at hy ⊢
    exact (key Z f' x).2 (h ((key Y f x).1 hy))
  · intro h x hx
    rw [LinearMap.mem_ker] at hx ⊢
    exact (key Z f' x).1 (h ((key Y f x).2 hx))

/-! ### The comparison at a single level -/

variable {A : Type u} [CommRing A]

/-- The localization of the inclusion `IⁿM ⊆ M` sends the fraction `x/s` to the fraction `x/s`
of `M_S`. -/
private theorem localizedIdealPowerInclusion_mk' (S : Submonoid A) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (n : ℕ) (x : ↥(I ^ n • (⊤ : Submodule A M))) (s : S) :
    (ModuleCat.localizedModuleMap.{max u v} S (idealPowerInclusion.{u, v} I M n)).hom
        (IsLocalizedModule.mk'
          (((idealPowerTower.{u, v} I M).obj (op n)).localizedModuleMkLinearMap S) x s) =
      IsLocalizedModule.mk' (M.localizedModuleMkLinearMap S) x.val s :=
  IsLocalizedModule.map_mk' S
    (((idealPowerTower.{u, v} I M).obj (op n)).localizedModuleMkLinearMap S)
    (M.localizedModuleMkLinearMap S) (I ^ n • (⊤ : Submodule A M)).subtype x s

/-- The localization of the inclusion `IⁿM ⊆ M` lands in `(S⁻¹I)ⁿ(M_S)`.

A fraction with numerator in `IⁿM` lies in the submodule of `M_S` localized from `IⁿM`, which
`Submodule.localized'_pow_smul_top` identifies with `(S⁻¹I)ⁿ(M_S)`. -/
theorem localizedIdealPowerInclusion_mem (S : Submonoid A) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (n : ℕ)
    (y : ((idealPowerTower.{u, v} I M).obj (op n)).localizedModule S) :
    (ModuleCat.localizedModuleMap.{max u v} S
        (idealPowerInclusion.{u, v} I M n)).hom y ∈
      I.map (algebraMap A (Localization S)) ^ n •
        (⊤ : Submodule (Localization S) (M.localizedModule S)) := by
  rw [← Submodule.localized'_pow_smul_top S I (Localization S)
    (M.localizedModuleMkLinearMap S) n]
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S
    (((idealPowerTower.{u, v} I M).obj (op n)).localizedModuleMkLinearMap S) y
  rw [Submodule.mem_localized']
  exact ⟨x.val, x.2, s, (localizedIdealPowerInclusion_mk'.{u, v} S I M n x s).symm⟩

/-- The localization of the inclusion `IⁿM ⊆ M` is injective, because localization is exact. -/
theorem localizedIdealPowerInclusion_injective (S : Submonoid A) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (n : ℕ) :
    Function.Injective (ModuleCat.localizedModuleMap.{max u v} S
      (idealPowerInclusion.{u, v} I M n)).hom :=
  IsLocalizedModule.map_injective S
    (((idealPowerTower.{u, v} I M).obj (op n)).localizedModuleMkLinearMap S)
    (M.localizedModuleMkLinearMap S) (I ^ n • (⊤ : Submodule A M)).subtype
    Subtype.val_injective

/-- Every element of `(S⁻¹I)ⁿ(M_S)` is a value of the localization of the inclusion
`IⁿM ⊆ M`. -/
theorem localizedIdealPowerInclusion_surjective (S : Submonoid A) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (n : ℕ)
    (z : M.localizedModule S)
    (hz : z ∈ I.map (algebraMap A (Localization S)) ^ n •
      (⊤ : Submodule (Localization S) (M.localizedModule S))) :
    ∃ y, (ModuleCat.localizedModuleMap.{max u v} S
      (idealPowerInclusion.{u, v} I M n)).hom y = z := by
  rw [← Submodule.localized'_pow_smul_top S I (Localization S)
    (M.localizedModuleMkLinearMap S) n, Submodule.mem_localized'] at hz
  obtain ⟨m, hm, s, hms⟩ := hz
  exact ⟨_, (localizedIdealPowerInclusion_mk'.{u, v} S I M n ⟨m, hm⟩ s).trans hms⟩

/-- The isomorphism `(IⁿM)_S ≃ (S⁻¹I)ⁿ(M_S)` of modules over `S⁻¹A`.

It is the localization of the inclusion `IⁿM ⊆ M`, corestricted to the submodule
`(S⁻¹I)ⁿ(M_S)` of `M_S` in which its values lie: that map is injective because localization is
exact, and surjective because a fraction whose numerator lies in `IⁿM` is a value of it. -/
def localizedIdealPowerEquiv (S : Submonoid A) (I : Ideal A) (M : ModuleCat.{max u v} A)
    (n : ℕ) :
    ((idealPowerTower.{u, v} I M).obj (op n)).localizedModule S ≃ₗ[Localization S]
      ↥(I.map (algebraMap A (Localization S)) ^ n •
        (⊤ : Submodule (Localization S) (M.localizedModule S))) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _
      (ModuleCat.localizedModuleMap.{max u v} S
        (idealPowerInclusion.{u, v} I M n)).hom
      (localizedIdealPowerInclusion_mem.{u, v} S I M n))
    ⟨fun a b hab =>
      localizedIdealPowerInclusion_injective.{u, v} S I M n (congrArg Subtype.val hab),
      fun z => by
        obtain ⟨y, hy⟩ := localizedIdealPowerInclusion_surjective.{u, v} S I M n z z.2
        exact ⟨y, Subtype.ext hy⟩⟩

/-- **The comparison is pinned by the inclusions into `M_S`.** Following
`localizedIdealPowerEquiv` by the inclusion `(S⁻¹I)ⁿ(M_S) ⊆ M_S` gives the localization of the
inclusion `IⁿM ⊆ M`. -/
theorem localizedIdealPowerEquiv_coe (S : Submonoid A) (I : Ideal A) (M : ModuleCat.{max u v} A)
    (n : ℕ) :
    (I.map (algebraMap A (Localization S)) ^ n •
          (⊤ : Submodule (Localization S) (M.localizedModule S))).subtype ∘ₗ
        (localizedIdealPowerEquiv.{u, v} S I M n).toLinearMap =
      (ModuleCat.localizedModuleMap.{max u v} S
        (idealPowerInclusion.{u, v} I M n)).hom :=
  rfl

/-- The value in `M_S` of the comparison at an element, read off from
`localizedIdealPowerEquiv_coe`. -/
theorem localizedIdealPowerEquiv_coe_apply (S : Submonoid A) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (n : ℕ)
    (x : ((idealPowerTower.{u, v} I M).obj (op n)).localizedModule S) :
    ((localizedIdealPowerEquiv.{u, v} S I M n x : M.localizedModule S)) =
      (ModuleCat.localizedModuleMap.{max u v} S
        (idealPowerInclusion.{u, v} I M n)).hom x :=
  DFunLike.congr_fun (localizedIdealPowerEquiv_coe.{u, v} S I M n) x

/-! ### The comparison of inverse systems -/

/-- **The localized ideal-power tower is the ideal-power tower of the localized module.** The
term-by-term localization of `{IⁿM}` is isomorphic, as an inverse system of modules over `S⁻¹A`,
to the ideal-power tower of `M_S` for the extended ideal `S⁻¹I`.

The components are `localizedIdealPowerEquiv`, and the naturality square commutes because both
of its legs send an element to the same element of `M_S`: the transition maps of both towers are
inclusions of submodules of `M_S`, and the components commute with the inclusions by
`localizedIdealPowerEquiv_coe`. -/
def localizedIdealPowerTowerIso (S : Submonoid A) (I : Ideal A) (M : ModuleCat.{max u v} A) :
    idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v} S ≅
      idealPowerTower.{u, v} (I.map (algebraMap A (Localization S)))
        ((ModuleCat.localizedModuleFunctor.{max u v} S).obj M) :=
  NatIso.ofComponents
    (fun n => (localizedIdealPowerEquiv.{u, v} S I M n.unop).toModuleIso)
    (by
      intro n m f
      have hcomp : (idealPowerTower.{u, v} I M).map f ≫
          idealPowerInclusion.{u, v} I M m.unop = idealPowerInclusion.{u, v} I M n.unop := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        rfl
      have hmap := congrArg (ModuleCat.localizedModuleFunctor.{max u v} S).map hcomp
      rw [Functor.map_comp] at hmap
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      refine Eq.trans (localizedIdealPowerEquiv_coe_apply.{u, v} S I M m.unop _) ?_
      refine Eq.trans ?_ (localizedIdealPowerEquiv_coe_apply.{u, v} S I M n.unop x).symm
      exact congrArg (fun g => ModuleCat.Hom.hom g x) hmap)

/-! ### Transporting the tower along an isomorphism of modules -/

/-- An isomorphism `X ≅ Y` of modules carries the submodule `IⁿX` onto `IⁿY`: multiplying by the
ideal commutes with taking images, and the image of `X` is all of `Y`. -/
theorem map_pow_smul_top_of_iso (I : Ideal A) {X Y : ModuleCat.{max u v} A} (e : X ≅ Y) (n : ℕ) :
    Submodule.map e.hom.hom (I ^ n • (⊤ : Submodule A X)) =
      I ^ n • (⊤ : Submodule A Y) := by
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)]

/-- The isomorphism `IⁿX ≃ IⁿY` of the `n`-th terms of the two ideal-power towers induced by an
isomorphism `X ≅ Y`: the restriction of the isomorphism, which is injective, to a map onto the
image of `IⁿX`, which is `IⁿY`. -/
def idealPowerEquivOfIso (I : Ideal A) {X Y : ModuleCat.{max u v} A} (e : X ≅ Y) (n : ℕ) :
    ↥(I ^ n • (⊤ : Submodule A X)) ≃ₗ[A] ↥(I ^ n • (⊤ : Submodule A Y)) :=
  (Submodule.equivMapOfInjective e.hom.hom
        ((ModuleCat.mono_iff_injective _).1 inferInstance)
        (I ^ n • (⊤ : Submodule A X))).trans
    (LinearEquiv.ofEq _ _ (map_pow_smul_top_of_iso.{u, v} I e n))

/-- **The ideal-power tower is carried along an isomorphism of modules.** An isomorphism
`X ≅ Y` of `A`-modules induces an isomorphism `{IⁿX} ≅ {IⁿY}` of inverse systems.

The components are `idealPowerEquivOfIso`, and the naturality square commutes because both of
its legs send an element of `IⁿX` to the element of `IᵐY` with the same value under the
isomorphism: the transition maps of both towers are inclusions of submodules. -/
def idealPowerTowerIsoOfIso (I : Ideal A) {X Y : ModuleCat.{max u v} A} (e : X ≅ Y) :
    idealPowerTower.{u, v} I X ≅ idealPowerTower.{u, v} I Y :=
  NatIso.ofComponents (fun n => (idealPowerEquivOfIso.{u, v} I e n.unop).toModuleIso)
    (by
      intro n m f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-! ### The induced comparison of local cohomology systems -/

variable (S : Submonoid A) [IsNoetherianRing (Localization S)] [IsLocalRing (Localization S)]

/-- **The two local cohomology systems agree.** In each degree `i`, the system
`{Hⁱ_𝔪((IⁿM)_S)}` obtained by localizing the ideal-power tower of `M` is isomorphic to the
system `{Hⁱ_𝔪((S⁻¹I)ⁿ(M_S))}` of the ideal-power tower of the localized module. -/
def localizedIdealPowerTowerLocalCohomologyIso (I : Ideal A) (M : ModuleCat.{max u v} A)
    (i : ℤ) :
    idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v} S ⋙
        localCohomologyModuleFunctor (Localization S) i ≅
      idealPowerTower.{u, v} (I.map (algebraMap A (Localization S)))
          ((ModuleCat.localizedModuleFunctor.{max u v} S).obj M) ⋙
        localCohomologyModuleFunctor (Localization S) i :=
  Functor.isoWhiskerRight (localizedIdealPowerTowerIso.{u, v} S I M)
    (localCohomologyModuleFunctor (Localization S) i)

/-- A transition map of `{Hⁱ_𝔪((IⁿM)_S)}` vanishes exactly when the corresponding transition map
of `{Hⁱ_𝔪((S⁻¹I)ⁿ(M_S))}` vanishes. -/
theorem localCohomology_localizedIdealPowerTower_map_eq_zero_iff (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ) {m k : ℕ} (h : m ≤ k) :
    (idealPowerTower.{u, v} I M ⋙ ModuleCat.localizedModuleFunctor.{max u v} S ⋙
        localCohomologyModuleFunctor (Localization S) i).map (homOfLE h).op = 0 ↔
      (idealPowerTower.{u, v} (I.map (algebraMap A (Localization S)))
            ((ModuleCat.localizedModuleFunctor.{max u v} S).obj M) ⋙
          localCohomologyModuleFunctor (Localization S) i).map (homOfLE h).op = 0 :=
  natIso_map_eq_zero_iff
    (localizedIdealPowerTowerLocalCohomologyIso.{u, v} S I M i) (homOfLE h).op

/-- The image of a transition map of `{Hⁱ_𝔪((IⁿM)_S)}` is carried onto the image of the
corresponding transition map of `{Hⁱ_𝔪((S⁻¹I)ⁿ(M_S))}` by the comparison. -/
theorem localCohomology_localizedIdealPowerTower_range_map (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ) {m k : ℕ} (h : m ≤ k) :
    Submodule.map
        ((localizedIdealPowerTowerLocalCohomologyIso.{u, v} S I M i).hom.app (op m)).hom
        (LinearMap.range ((idealPowerTower.{u, v} I M ⋙
          ModuleCat.localizedModuleFunctor.{max u v} S ⋙
          localCohomologyModuleFunctor (Localization S) i).map (homOfLE h).op).hom) =
      LinearMap.range ((idealPowerTower.{u, v} (I.map (algebraMap A (Localization S)))
          ((ModuleCat.localizedModuleFunctor.{max u v} S).obj M) ⋙
        localCohomologyModuleFunctor (Localization S) i).map (homOfLE h).op).hom :=
  natIso_range_map
    (localizedIdealPowerTowerLocalCohomologyIso.{u, v} S I M i) (homOfLE h).op

end Stacks.LocalCohomology

end
