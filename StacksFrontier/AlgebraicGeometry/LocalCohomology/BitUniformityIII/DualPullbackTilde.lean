module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackFinFree
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf-level `can` at `M~` over `Spec(A/Iⁿ)`, and its kernel and cokernel

Let `A` be a ring, `I ⊆ A` an ideal and `M` an `(A, n, c)`-module.  The last clause of
[Stacks, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB) says that the kernel and the
cokernel of the canonical map `can : p^*(M^∨) ⟶ (p^*M)^∨` are annihilated by `I^c`, and the
reason it gives is that for `a ∈ I^c` the map `a : M → M` factors through a finite free
`A/Iⁿ`-module, at which `can` is an isomorphism.

This file proves that reason for the sheaf-level map
`Stacks.SheafOfModules.PullbackDual.pullbackDualMap` at the sheaf `M~` on `Spec(A/Iⁿ)`, that is
for `f^*((M~)^∨) ⟶ (f^*(M~))^∨`, with no hypothesis on the endomorphism: the passage from
modules to sheaves on `Spec(A/Iⁿ)` is `M ↦ M~`, `AlgebraicGeometry.tilde.functor`, which is
additive and carries `A/Iⁿ` to the structure sheaf (`AlgebraicGeometry.tildeSelf`), so it
carries the module-level factorization of `a : M → M` to a factorization through
`((A/Iⁿ)^{⊕r})~`, at which `can` is an isomorphism.

The source's `can` has source `p^*(M^∨) = f^*((M^∨)~)` rather than `f^*((M~)^∨)`.  That map,
its functoriality, its invertibility at a finite free module and the annihilation of its kernel
and cokernel are in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackSource`, which
builds on this file and is where Tag 0GAB is registered; it also proves
`(a • 𝟙 M)~ = a • 𝟙 (M~)`, so that the endomorphism `(a • 𝟙 M)~` used below is multiplication
by `a` on `M~`.

The morphism along which the pullback is taken is an arbitrary morphism of ringed sites
`f : X ⟶ Spec(A/Iⁿ)`, which is more general than the source's `p : Y_n → Spec(A/Iⁿ)`.

## What "annihilates" means here

As in `DualPullbackFinFree`, an endomorphism `e : F ⟶ F` induces an endomorphism of
`ker(can_F)` and of `coker(can_F)` through the functoriality of `can` in the module,
`Stacks.SheafOfModules.PullbackDual.pullbackDualMap_naturality`, and "`e` annihilates the
kernel" is the statement that this induced endomorphism is zero.  The endomorphism taken here
is `(a • 𝟙 M)~`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.specRingedSite`: `Spec R` read as a ringed site.
* `Stacks.LocalCohomology.UniformityIII.specTilde`: `M ↦ M~`, with its codomain spelled as the
  sheaves of modules on that ringed site.

## Main results

* `Stacks.SheafOfModules.PullbackDual.isIso_pullbackDualMap_realization_finFree`: for an
  additive functor from `R`-modules to sheaves of modules carrying `R` to the structure sheaf,
  `can` is an isomorphism at the image of a finite free module.
* `Stacks.SheafOfModules.PullbackDual.kernel_map_pullbackDualMap_realization_eq_zero` and
  `Stacks.SheafOfModules.PullbackDual.cokernel_map_pullbackDualMap_realization_eq_zero`: such a
  functor carries a module endomorphism factoring through a finite free module to an
  endomorphism annihilating the kernel and the cokernel of `can`.
* `Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_tilde_finFree_factorization`: for an
  `(A, n, c)`-module `M` and `a ∈ I^c`, the endomorphism `(a : M → M)~` of `M~` factors through
  the sheaf `((A/Iⁿ)^{⊕r})~` on `Spec(A/Iⁿ)`.
* `Stacks.LocalCohomology.UniformityIII.IsANCModule.kernel_map_pullbackDualMap_tilde_eq_zero`
  and
  `Stacks.LocalCohomology.UniformityIII.IsANCModule.cokernel_map_pullbackDualMap_tilde_eq_zero`:
  for an `(A, n, c)`-module `M` and `a ∈ I^c`, `(a • 𝟙 M)~` annihilates the kernel and the
  cokernel of the sheaf-level `can` at `M~`, for every morphism of ringed sites into
  `Spec(A/Iⁿ)`.

## Implementation notes

The two steps are separated because only the second mentions `Spec`: the first is about an
arbitrary additive functor `P : Mod(R) ⥤ Mod(𝒪_Y)` together with an isomorphism
`P(R) ≅ 𝒪_Y`, and it is `M ↦ M~` on `Spec R` that instantiates it.

`Spec R` is read as a ringed site through
`Stacks.SheafOfModules.opensRingedSite`, which presents a ringed space as a ringed site; the
resulting sheaf of rings is `(Spec R).ringCatSheaf` on the nose, so an `𝒪_{Spec R}`-module *is*
a sheaf of modules on `specRingedSite R`, with no comparison.  `specTilde` re-ascribes
`AlgebraicGeometry.tilde.functor` to that spelling of its codomain, which is the same type as
`(Spec R).Modules` but carries a separately declared `Preadditive` instance; that is why
additivity has to be transported, in `specTilde_additive`, exactly as
`Stacks.DerivedQCoh.tildeSheafOfModules_additive` transports it for the `ringCatSheaf`
spelling.

## References

* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.InternalHom Stacks.LocalCohomology.UniformityIII

universe u

namespace Stacks.SheafOfModules.PullbackDual

/-! ### `can` at the image of a finite free module under a realization functor -/

/-- A functor carries a factorization of an endomorphism through a finite free module to one of
its image. -/
private theorem exists_map_finFree_factorization {R : Type u} [CommRing R] {D : Type*}
    [Category D] (P : ModuleCat.{u} R ⥤ D) {M : ModuleCat.{u} R} {e : M ⟶ M}
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    ∃ (r : ℕ) (α : P.obj M ⟶ P.obj (finFreeModule R r))
      (β : P.obj (finFreeModule R r) ⟶ P.obj M), α ≫ β = P.map e := by
  obtain ⟨r, α, β, hαβ⟩ := he
  exact ⟨r, P.map α, P.map β, by rw [← Functor.map_comp, hαβ]⟩

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {R : Type u} [CommRing R]
  (P : ModuleCat.{u} R ⥤
    _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
  [P.Additive]
  (u₀ : P.obj (ModuleCat.of R R) ≅
    _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))

include u₀

/-- The identity of `P(R^{⊕r})` is the sum of the `r` maps through the structure sheaf obtained
from the projections and inclusions of `R^{⊕r}` and the identification `P(R) ≅ 𝒪_Y`. -/
theorem sum_id_realization_finFree (r : ℕ) :
    ∑ i : Fin r, (P.map (finFreeProj R r i) ≫ u₀.hom) ≫ (u₀.inv ≫ P.map (finFreeIncl R r i)) =
      𝟙 (P.obj (finFreeModule R r)) := by
  rw [show (∑ i : Fin r, (P.map (finFreeProj R r i) ≫ u₀.hom) ≫
        (u₀.inv ≫ P.map (finFreeIncl R r i))) =
      ∑ i : Fin r, P.map (finFreeProj R r i ≫ finFreeIncl R r i) from
    Finset.sum_congr rfl fun i _ => by
      rw [Category.assoc, u₀.hom_inv_id_assoc, P.map_comp],
    ← Functor.map_sum, sum_finFreeProj_comp_finFreeIncl]
  exact P.map_id _

/-- **`can` is an isomorphism at the image of a finite free module.**  For an additive functor
`P` from `R`-modules to sheaves of modules which carries `R` to the structure sheaf, `P(R^{⊕r})`
is a sheaf whose identity is a finite sum of maps through `𝒪_Y`, which is
`isIso_pullbackDualMap_of_sum_id`. -/
@[ega "0 5.4.5" "special case"]
theorem isIso_pullbackDualMap_realization_finFree (r : ℕ) :
    IsIso (pullbackDualMap f (P.obj (finFreeModule R r))) :=
  isIso_pullbackDualMap_of_sum_id f _ _ (sum_id_realization_finFree P u₀ r)

/-- **An `R`-module endomorphism which factors through a finite free module is carried by `P`
to an endomorphism annihilating the kernel of `can`.**  This is the kernel half of the last
clause of Tag 0GAB for a realization functor `P`; the hypothesis is one on the *module* `M`,
and for an `(A, n, c)`-module and `a ∈ I^c` it is
`Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_finFree_factorization`. -/
theorem kernel_map_pullbackDualMap_realization_eq_zero {M : ModuleCat.{u} R} (e : M ⟶ M)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    kernel.map (pullbackDualMap f (P.obj M)) (pullbackDualMap f (P.obj M))
        ((ringedSitePullback f).map (dualModuleSheafMap Y (P.map e)))
        (dualModuleSheafMap X ((ringedSitePullback f).map (P.map e)))
        (pullbackDualMap_naturality f (P.map e)) = 0 := by
  obtain ⟨r, α, β, hαβ⟩ := exists_map_finFree_factorization P he
  exact kernel_map_pullbackDualMap_eq_zero_of_factorization f _
    (isIso_pullbackDualMap_realization_finFree f P u₀ r) α β hαβ

/-- **An `R`-module endomorphism which factors through a finite free module is carried by `P`
to an endomorphism annihilating the cokernel of `can`.**  The cokernel half of
`kernel_map_pullbackDualMap_realization_eq_zero`. -/
theorem cokernel_map_pullbackDualMap_realization_eq_zero {M : ModuleCat.{u} R} (e : M ⟶ M)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    cokernel.map (pullbackDualMap f (P.obj M)) (pullbackDualMap f (P.obj M))
        ((ringedSitePullback f).map (dualModuleSheafMap Y (P.map e)))
        (dualModuleSheafMap X ((ringedSitePullback f).map (P.map e)))
        (pullbackDualMap_naturality f (P.map e)) = 0 := by
  obtain ⟨r, α, β, hαβ⟩ := exists_map_finFree_factorization P he
  exact cokernel_map_pullbackDualMap_eq_zero_of_factorization f _
    (isIso_pullbackDualMap_realization_finFree f P u₀ r) α β hαβ

end Stacks.SheafOfModules.PullbackDual

namespace Stacks.LocalCohomology.UniformityIII

open Stacks.SheafOfModules.PullbackDual

/-! ### `Spec R` as a ringed site, and `M ↦ M~` into its sheaves of modules -/

/-- `Spec R` read as a ringed site: the site of the opens of its space with the open-cover
topology, carrying `𝒪_{Spec R}`.  This is `Stacks.SheafOfModules.opensRingedSite` at the
structure sheaf of `Spec R`, and only a change of presentation — the sheaf of rings it
determines is `(Spec R).ringCatSheaf` on the nose. -/
noncomputable abbrev specRingedSite (R : CommRingCat.{u}) : RingedSite.{u, u, u} :=
  Stacks.SheafOfModules.opensRingedSite (Spec R).sheaf

/-- The functor `M ↦ M~` from `R`-modules to sheaves of modules on the ringed site `Spec R`.
This is `AlgebraicGeometry.tilde.functor`, whose codomain `(Spec R).Modules` is the same type;
the ascription is what makes the dual and the pullback of a morphism of ringed sites apply to
its values. -/
noncomputable abbrev specTilde (R : CommRingCat.{u}) :
    ModuleCat.{u} R ⥤
      _root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (specRingedSite R).J))
          (specRingedSite R).O) :=
  tilde.functor R

/-- **`M ↦ M~` is additive**, which is `AlgebraicGeometry.tilde.functor`'s additivity carried
to the ringed-site spelling of its codomain. -/
theorem specTilde_additive (R : CommRingCat.{u}) : (specTilde R).Additive :=
  inferInstanceAs (tilde.functor R).Additive

attribute [local instance] specTilde_additive

/-- `R~` is the structure sheaf of `Spec R`, which is `AlgebraicGeometry.tildeSelf` read at the
ringed-site spelling of the category it lives in. -/
noncomputable def specTildeUnitIso (R : CommRingCat.{u}) :
    (specTilde R).obj (ModuleCat.of R R) ≅
      _root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (specRingedSite R).J))
          (specRingedSite R).O) :=
  tildeSelf

/-! ### The sheaf-level form of the last clause of Tag 0GAB for an `(A, n, c)`-module -/

variable {A : Type u} [CommRing A] {I : Ideal A} {n c : ℕ}
  {M : ModuleCat.{u} (A ⧸ I ^ n)}

/-- **The factorization of Tag 0GAB carried to `Spec(A/Iⁿ)`.**  For an `(A, n, c)`-module `M`
and `a ∈ I^c`, the endomorphism `(a : M → M)~` of the sheaf `M~` factors through the sheaf
`((A/Iⁿ)^{⊕r})~` for some `r`.

This is `IsANCModule.exists_finFree_factorization` with `(-)~` applied to it: the factorization
holds at the level of `A/Iⁿ`-modules, and a functor carries a factorization to a
factorization. -/
theorem IsANCModule.exists_tilde_finFree_factorization (hM : IsANCModule I n c M)
    {a : A ⧸ I ^ n} (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    ∃ (r : ℕ)
      (α : (specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M ⟶
        (specTilde (CommRingCat.of (A ⧸ I ^ n))).obj
          (finFreeModule (A ⧸ I ^ n) r))
      (β : (specTilde (CommRingCat.of (A ⧸ I ^ n))).obj
        (finFreeModule (A ⧸ I ^ n) r) ⟶
          (specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M),
      α ≫ β = (specTilde (CommRingCat.of (A ⧸ I ^ n))).map (a • 𝟙 M) := by
  exact exists_map_finFree_factorization _ (hM.exists_finFree_factorization ha)

/-- **The kernel half of the last clause of Tag 0GAB, for the sheaf-level `can` at `M~`.**  Let
`M` be an `(A, n, c)`-module, let `a ∈ I^c` and let `f : X ⟶ Spec(A/Iⁿ)` be any morphism of
ringed sites.  Then the endomorphism of the kernel of `can : f^*((M~)^∨) ⟶ (f^*(M~))^∨` induced
by `(a • 𝟙 M)~` is zero.  The form with the source's `p^*(M^∨)` is
`IsANCModule.kernel_map_pullbackModuleDualMap_eq_zero`.

There is no hypothesis on the endomorphism.  The source's reason is the proof: by
`IsANCModule.exists_tilde_finFree_factorization` the map `(a : M → M)~` factors through
`((A/Iⁿ)^{⊕r})~`, and `can` is an isomorphism there because `(-)~` is additive and carries
`A/Iⁿ` to `𝒪_{Spec(A/Iⁿ)}`. -/
theorem IsANCModule.kernel_map_pullbackDualMap_tilde_eq_zero
    {X : RingedSite.{u, u, u}}
    (f : RingedSite.Hom X (specRingedSite (CommRingCat.of (A ⧸ I ^ n))))
    (hM : IsANCModule I n c M) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    kernel.map
        (pullbackDualMap f ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M))
        (pullbackDualMap f ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M))
        ((ringedSitePullback f).map (dualModuleSheafMap
          (specRingedSite (CommRingCat.of (A ⧸ I ^ n)))
          ((specTilde (CommRingCat.of (A ⧸ I ^ n))).map (a • 𝟙 M))))
        (dualModuleSheafMap X ((ringedSitePullback f).map
          ((specTilde (CommRingCat.of (A ⧸ I ^ n))).map (a • 𝟙 M))))
        (pullbackDualMap_naturality f
          ((specTilde (CommRingCat.of (A ⧸ I ^ n))).map (a • 𝟙 M))) = 0 := by
  have := specTilde_additive (CommRingCat.of (A ⧸ I ^ n))
  exact kernel_map_pullbackDualMap_realization_eq_zero f _
    (specTildeUnitIso (CommRingCat.of (A ⧸ I ^ n))) (a • 𝟙 M)
    (hM.exists_finFree_factorization ha)

/-- **The cokernel half of the last clause of Tag 0GAB, for the sheaf-level `can` at `M~`.**  The
cokernel companion of `IsANCModule.kernel_map_pullbackDualMap_tilde_eq_zero`. -/
theorem IsANCModule.cokernel_map_pullbackDualMap_tilde_eq_zero
    {X : RingedSite.{u, u, u}}
    (f : RingedSite.Hom X (specRingedSite (CommRingCat.of (A ⧸ I ^ n))))
    (hM : IsANCModule I n c M) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    cokernel.map
        (pullbackDualMap f ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M))
        (pullbackDualMap f ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M))
        ((ringedSitePullback f).map (dualModuleSheafMap
          (specRingedSite (CommRingCat.of (A ⧸ I ^ n)))
          ((specTilde (CommRingCat.of (A ⧸ I ^ n))).map (a • 𝟙 M))))
        (dualModuleSheafMap X ((ringedSitePullback f).map
          ((specTilde (CommRingCat.of (A ⧸ I ^ n))).map (a • 𝟙 M))))
        (pullbackDualMap_naturality f
          ((specTilde (CommRingCat.of (A ⧸ I ^ n))).map (a • 𝟙 M))) = 0 := by
  have := specTilde_additive (CommRingCat.of (A ⧸ I ^ n))
  exact cokernel_map_pullbackDualMap_realization_eq_zero f _
    (specTildeUnitIso (CommRingCat.of (A ⧸ I ^ n))) (a • 𝟙 M)
    (hM.exists_finFree_factorization ha)

end Stacks.LocalCohomology.UniformityIII

end
