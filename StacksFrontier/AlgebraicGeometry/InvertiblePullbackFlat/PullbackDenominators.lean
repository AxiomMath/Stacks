module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorRule
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorsInclusion
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicPullback
public import StacksFrontier.AlgebraicGeometry.Meromorphic.TensorComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The module `𝒩 ⊂ 𝒦_Y` of Stacks Tag 0BD7

Let `φ : X ⟶ Y` be a flat morphism of schemes, `ℒ` a sheaf of `𝒪_X`-modules and `s` a
meromorphic section of `ℒ`. The proof of Stacks Tag 0BD7 introduces the sheaf of
`𝒪_Y`-modules whose sections over an open `V ⊆ Y` are those meromorphic functions
`g ∈ 𝒦_Y(V)` with `φ^*(g) s ∈ ℒ(φ^{-1} V)`, and asserts that for suitable `φ` and `s` it is
invertible with `φ^*𝒩 ≅ ℒ`. This file constructs `𝒩`.

It is the same construction as `AlgebraicGeometry.denominatorIdeal` — the ideal of
denominators of a meromorphic section, Tag 02P0 — with two changes: the source of the
multiplication map is `𝒦_Y` rather than `𝒪_Y`, and the target lives on `X` and is pushed
forward. So `𝒩` is again a categorical fibre product rather than a sectionwise subsheaf, the
two maps of the source are literally its projections, and no sheaf condition has to be
checked separately.

The multiplication map `𝒦_Y ⟶ φ_*𝒦_X(ℒ)`, `g ↦ φ^*(g) s`, is assembled in two steps. Over
the sheaf of rings `𝒦_Y` it is the morphism out of the unit determined by the global section
`s` of `φ_*𝒦_X(ℒ)`, using the ring map `𝒦_Y ⟶ φ_*𝒦_X` of
`Stacks.Meromorphic.Scheme.totalQuotientSheafPullbackOfFlat`; restriction of scalars along
`𝒪_Y ⟶ 𝒦_Y` then turns it into a map of `𝒪_Y`-modules, and
`SheafOfModules.pushforwardRestrictScalars` identifies its target with the pushforward of
`𝒦_X(ℒ)` taken over `𝒪_X`, which is the `𝒪_Y`-module structure every other map in sight
uses. That identification is exactly the commuting square of Tag 02OT: pulling a regular
function back and then regarding it as meromorphic agrees with regarding it as meromorphic
and then pulling back.

## Main definitions

* `PresheafOfModules.pushforwardRestrictScalars` and
  `SheafOfModules.pushforwardRestrictScalars`: for a commuting square of (pre)sheaves of
  rings `θ ≫ b = a ≫ F_*β`, the comparison
  `restrictScalars θ (pushforward b M) ⟶ pushforward a (restrictScalars β M)`. Both sides have
  the same underlying presheaf of abelian groups; the content is that the two scalar actions
  agree.
* `Stacks.Meromorphic.Scheme.ringSheafPullbackOfFlat`: the ring map `𝒦_Y ⟶ φ_*𝒦_X` of a flat
  morphism, read in `RingCat` so that sheaves of modules can be taken over it.
* `Stacks.Meromorphic.pullbackMeromorphicMul`: the map `𝒦_Y ⟶ φ_*𝒦_X(ℒ)`, `g ↦ φ^*(g) s`.
* `Stacks.Meromorphic.pullbackDenominatorModule`: the module `𝒩`, as the fibre product of
  `𝒦_Y` and `φ_*ℒ` over `φ_*𝒦_X(ℒ)`, with its two projections
  `Stacks.Meromorphic.pullbackDenominatorModuleι` (the inclusion `𝒩 ⊂ 𝒦_Y`) and
  `Stacks.Meromorphic.pullbackDenominatorModuleMul` (multiplication by `s`, landing in
  `φ_*ℒ`).
* `Stacks.Meromorphic.pullbackDenominatorModuleToPullback`: the map `φ^*𝒩 ⟶ ℒ`, `g ↦ g s`, of
  the source, obtained from multiplication by `s` through the pullback-pushforward adjunction.
  It lives in `X.Modules`, where the conclusion of the tag is stated.

## Main results

* `Stacks.Meromorphic.Scheme.toTotalQuotientRingSheaf_comp_ringSheafPullbackOfFlat`: the
  commuting square `𝒪_Y ⟶ 𝒦_Y ⟶ φ_*𝒦_X` = `𝒪_Y ⟶ φ_*𝒪_X ⟶ φ_*𝒦_X`, in `RingCat`.
* `Stacks.Meromorphic.pullbackMeromorphicMul_val_app_apply`: the sections of the
  multiplication map are `g ↦ φ^*(g) • s`, with `φ^*` the pullback of meromorphic functions.
* `Stacks.Meromorphic.exists_pullbackDenominatorModuleι_app_eq_iff`: the defining property of
  `𝒩`, that `g ∈ 𝒩(V)` exactly when `φ^*(g) s` is a section of `ℒ` over `φ^{-1} V`.
* `Stacks.Meromorphic.mono_pushforward_map`: pushing forward along a morphism of schemes
  preserves monomorphisms of sheaves of modules.
* `Stacks.Meromorphic.pullbackDenominatorModuleι_mono`: for an invertible `ℒ` the inclusion
  `𝒩 ⟶ 𝒦_Y` is a monomorphism, so `𝒩` really is a submodule of `𝒦_Y`.
* `Stacks.Meromorphic.exists_isInvertible_and_nonempty_pullback_iso`: the conclusion of Tag
  0BD7, granted the two assertions the source proves about `𝒩` — that it is invertible, and
  that `φ^*𝒩 ⟶ ℒ` is an isomorphism. Neither is proved here, so the tag's attribute is not
  attached anywhere in this file.

## Implementation notes

`𝒩` is built over `Stacks.Sheaves.Differentials.ringSheaf Y.sheaf`, which is the spelling
`AlgebraicGeometry.denominatorIdeal` and the whole `Divisors/Meromorphic/` directory use, and
which is the same term as `AlgebraicGeometry.Scheme.ringCatSheaf Y`; pushforward of modules is
therefore `SheafOfModules.pushforward φ.toRingCatSheafHom`, the functor underlying Mathlib's
`AlgebraicGeometry.Scheme.Modules.pushforward φ`.

`SheafOfModules.pushforwardRestrictScalars` is stated for an arbitrary continuous functor of
sites rather than for `Opens.map φ.base`. Over an abstract site the two spellings of the
scalar action are a single rewrite apart, where at the scheme level each application of such
a comparison costs an expensive defeq between `Stacks.Sheaves.Differentials.ringSheaf` and the
  structure sheaf
of rings.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor TopologicalSpace Opposite AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

/-! ### Pushforward against restriction of scalars, for a commuting square of ring sheaves -/

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {S T : Cᵒᵖ ⥤ RingCat.{u}} {R R' : Dᵒᵖ ⥤ RingCat.{u}}
  (θ : S ⟶ T) (β : R ⟶ R') (a : S ⟶ F.op ⋙ R) (b : T ⟶ F.op ⋙ R')
  (sq : θ ≫ b = a ≫ Functor.whiskerLeft F.op β) (M : PresheafOfModules.{u} R')

/-- For a commuting square `θ ≫ b = a ≫ F_*β` of presheaves of rings, the comparison
`restrictScalars θ (pushforward b M) ⟶ pushforward a (restrictScalars β M)`. Both sides have
the same underlying presheaf of abelian groups, namely `V ↦ M(F V)`; the content is that the
two scalar actions of `S` on it agree. -/
noncomputable def pushforwardRestrictScalars :
    (restrictScalars θ).obj ((pushforward.{u} b).obj M) ⟶
      (pushforward.{u} a).obj ((restrictScalars β).obj M) :=
  homMk (𝟙 _) (fun V r m => by
    have h : ((θ ≫ b).app V).hom r = ((a ≫ Functor.whiskerLeft F.op β).app V).hom r := by
      rw [sq]
    change (((θ ≫ b).app V).hom r) • (show M.obj (F.op.obj V) from m) = _
    rw [h]
    rfl)

/-- On sections over `V`, the comparison `pushforwardRestrictScalars` is the identity map. -/
@[simp]
lemma pushforwardRestrictScalars_app_apply (V : Cᵒᵖ)
    (m : ((restrictScalars θ).obj ((pushforward.{u} b).obj M)).obj V) :
    Hom.app (pushforwardRestrictScalars θ β a b sq M) V m = m := rfl

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K]
  {S T : Sheaf J RingCat.{u}} {R R' : Sheaf K RingCat.{u}}
  (θ : S ⟶ T) (β : R ⟶ R')
  (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (b : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R')
  (sq : θ ≫ b = a ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map β)
  (M : SheafOfModules.{u} R')

/-- For a commuting square `θ ≫ b = a ≫ F_*β` of sheaves of rings, the comparison
`restrictScalars θ (pushforward b M) ⟶ pushforward a (restrictScalars β M)`. -/
noncomputable def pushforwardRestrictScalars :
    (restrictScalars θ).obj ((pushforward.{u} b).obj M) ⟶
      (pushforward.{u} a).obj ((restrictScalars β).obj M) :=
  ⟨PresheafOfModules.pushforwardRestrictScalars θ.hom β.hom a.hom b.hom
    (Sheaf.hom_ext_iff.mp sq) M.val⟩

/-- On sections over `V`, the comparison `pushforwardRestrictScalars` is the identity map. -/
@[simp]
lemma pushforwardRestrictScalars_val_app_apply (V : Cᵒᵖ)
    (m : ((restrictScalars θ).obj ((pushforward.{u} b).obj M)).val.obj V) :
    (pushforwardRestrictScalars θ β a b sq M).val.app V m = m := rfl

end SheafOfModules

namespace Stacks.Meromorphic

variable {X Y : Scheme.{u}} (φ : X ⟶ Y)

/-! ### The pullback of meromorphic functions as a morphism of sheaves of rings in `RingCat` -/

/-- The continuous functor of sites along which a module on `X` is pushed forward to `Y`. -/
noncomputable abbrev Scheme.sheafPushforward :=
  (Opens.map φ.base).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- Pushing forward preserves monomorphisms of sheaves of modules along a morphism of schemes,
because the sections of the pushforward over `V` are the sections of the original module over
`φ^{-1} V`. -/
lemma mono_pushforward_map {M N : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)}
    (ν : M ⟶ N) (hν : Mono ν) :
    Mono ((SheafOfModules.pushforward φ.toRingCatSheafHom).map ν) :=
  CategoryTheory.SheafOfModules.mono_of_forall_app_injective _ fun V =>
    CategoryTheory.SheafOfModules.app_injective_of_mono hν ((Opens.map φ.base).op.obj V)

variable [Flat φ]

/-- The morphism of sheaves of rings `𝒦_Y ⟶ φ_*𝒦_X` of a flat morphism of schemes, read in
`RingCat` so that sheaves of modules may be taken over it. This is
`Stacks.Meromorphic.Scheme.totalQuotientSheafPullbackOfFlat` composed with the forgetful
functor, exactly as `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` is for `φ` itself. -/
@[ega "IV 20.1.12" "special case"]
noncomputable def Scheme.ringSheafPullbackOfFlat :
    Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y) Y.totalQuotientSheaf
      ⟶
      (Scheme.sheafPushforward φ).obj
        (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.totalQuotientSheaf) :=
  ⟨Functor.whiskerRight (Scheme.totalQuotientSheafPullbackOfFlat φ).hom _⟩

/-- **Stacks Project, Tag 02OT** in `RingCat`: pulling a regular function back and then
regarding it as meromorphic agrees with regarding it as meromorphic and then pulling back.
This is the square that identifies the two `𝒪_Y`-module structures on `φ_*𝒦_X`. -/
lemma Scheme.toTotalQuotientRingSheaf_comp_ringSheafPullbackOfFlat :
    toTotalQuotientRingSheaf Y ≫ Scheme.ringSheafPullbackOfFlat φ =
      φ.toRingCatSheafHom ≫ (Scheme.sheafPushforward φ).map (toTotalQuotientRingSheaf X) :=
  Sheaf.hom_ext
    (congrArg (fun g => Functor.whiskerRight g (forget₂ CommRingCat.{u} RingCat.{u}))
      (toTotalQuotientSheaf_comp_totalQuotientSheafPullback φ.toLRSHom
        (pullbacksMeromorphicSections_of_flat φ)))

/-! ### Multiplication by a meromorphic section, pulled back -/

variable (L : SheafOfModules.{u}
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
  (s : MeromorphicSection X.sheaf L)

/-- The map `𝒦_Y ⟶ φ_*𝒦_X(ℒ)` of sheaves of `𝒪_Y`-modules sending a meromorphic function `g`
on `V` to `φ^*(g) s` on `φ^{-1} V`. This is the left-hand map of the fibre product defining
the module `𝒩` of Stacks Tag 0BD7. -/
noncomputable def pullbackMeromorphicMul :
    totalQuotientSheafAsModule Y ⟶
      (SheafOfModules.pushforward φ.toRingCatSheafHom).obj
        (meromorphicSectionSheafAsModule X L) :=
  (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf Y)).map
      (((SheafOfModules.pushforward (Scheme.ringSheafPullbackOfFlat φ)).obj
        (meromorphicSectionSheaf X.sheaf L)).unitHomEquiv.symm
          (SheafOfModules.pushforwardSections (Scheme.ringSheafPullbackOfFlat φ) s)) ≫
    SheafOfModules.pushforwardRestrictScalars (toTotalQuotientRingSheaf Y)
      (toTotalQuotientRingSheaf X) φ.toRingCatSheafHom (Scheme.ringSheafPullbackOfFlat φ)
      (Scheme.toTotalQuotientRingSheaf_comp_ringSheafPullbackOfFlat φ)
      (meromorphicSectionSheaf X.sheaf L)

/-- The sections of `Stacks.Meromorphic.pullbackMeromorphicMul` over an open `V`: a meromorphic
function `g` on `V` is sent to `φ^*(g) • s`, the pullback of `g` acting on the restriction of
`s` to `φ^{-1} V`. -/
lemma pullbackMeromorphicMul_val_app_apply (V : (Opens Y)ᵒᵖ)
    (g : (totalQuotientSheafAsModule Y).val.obj V) :
    (pullbackMeromorphicMul φ L s).val.app V g =
      (show (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf).obj.obj ((Opens.map φ.base).op.obj V) from
          ((Scheme.ringSheafPullbackOfFlat φ).hom.app V).hom g) •
        PresheafOfModules.sections.eval s ((Opens.map φ.base).op.obj V) :=
  rfl

/-! ### The module `𝒩 ⊂ 𝒦_Y` -/

/-- **The module `𝒩` of Stacks Tag 0BD7.** For a flat morphism `φ : X ⟶ Y` and a meromorphic
section `s` of a sheaf of `𝒪_X`-modules `ℒ`, this is the sheaf of `𝒪_Y`-modules whose sections
over an open `V ⊆ Y` are the meromorphic functions `g ∈ 𝒦_Y(V)` with
`φ^*(g) s ∈ ℒ(φ^{-1} V)`, realised as the fibre product of `𝒦_Y` and `φ_*ℒ` over
`φ_*𝒦_X(ℒ)`. -/
noncomputable def pullbackDenominatorModule :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
      Y.sheaf) :=
  pullback (pullbackMeromorphicMul φ L s)
    ((SheafOfModules.pushforward φ.toRingCatSheafHom).map
      (toMeromorphicSectionSheafAsModule X L))

/-- The inclusion `𝒩 ⊂ 𝒦_Y`, the first projection of the fibre product. -/
noncomputable def pullbackDenominatorModuleι :
    pullbackDenominatorModule φ L s ⟶ totalQuotientSheafAsModule Y :=
  pullback.fst _ _

/-- Multiplication by `s` on `𝒩`, landing in `φ_*ℒ`; the second projection of the fibre
product. This is the map which Stacks Tag 0BD7 shows to be an isomorphism after pulling
back. -/
noncomputable def pullbackDenominatorModuleMul :
    pullbackDenominatorModule φ L s ⟶
      (SheafOfModules.pushforward φ.toRingCatSheafHom).obj L :=
  pullback.snd _ _

/-- **The defining property of `𝒩`.** A meromorphic function `g` on `V ⊆ Y` lies in `𝒩(V)` —
that is, it is the image of a section of `𝒩` under the inclusion — exactly when `φ^*(g) s` is
a section of `ℒ` over `φ^{-1} V`, that is, lies in the image of the canonical map
`ℒ ⟶ 𝒦_X(ℒ)`. -/
lemma exists_pullbackDenominatorModuleι_app_eq_iff (V : Opens Y)
    (g : (totalQuotientSheafAsModule Y).val.obj (op V)) :
    (∃ n : (pullbackDenominatorModule φ L s).val.obj (op V),
        (pullbackDenominatorModuleι φ L s).val.app (op V) n = g) ↔
      ∃ t : ((SheafOfModules.pushforward φ.toRingCatSheafHom).obj L).val.obj (op V),
        (pullbackMeromorphicMul φ L s).val.app (op V) g =
          ((SheafOfModules.pushforward φ.toRingCatSheafHom).map
            (toMeromorphicSectionSheafAsModule X L)).val.app (op V) t :=
  exists_map_pullback_fst_eq_iff
    (_root_.SheafOfModules.evaluation
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y) Y.sheaf) (op V))
    (pullbackMeromorphicMul φ L s)
    ((SheafOfModules.pushforward φ.toRingCatSheafHom).map
      (toMeromorphicSectionSheafAsModule X L)) g

/-- **`𝒩` really is a submodule of `𝒦_Y`**: the inclusion is a monomorphism. As in Tag 02P0 this
is injectivity of `ℒ ⟶ 𝒦_X(ℒ)`, which holds for an invertible `ℒ`, transported through the
pushforward and the fibre product. -/
lemma pullbackDenominatorModuleι_mono
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) :
    Mono (pullbackDenominatorModuleι φ L s) :=
  have := mono_pushforward_map φ (toMeromorphicSectionSheafAsModule X L)
    (mono_toMeromorphicSectionSheafAsModule X L hL)
  pullback.fst_of_mono

/-! ### The comparison `φ^*𝒩 ⟶ ℒ` -/

/-- **The map `φ^*𝒩 ⟶ ℒ`, `g ↦ g s`, of Stacks Tag 0BD7.** It is multiplication by `s` on `𝒩`,
read through the adjunction between pullback and pushforward of sheaves of modules, so it needs
no further construction: Tag 0BD7 asserts that under its hypotheses this map is an isomorphism.
It lives in `X.Modules`, the category in which the conclusion of the tag is stated. -/
noncomputable def pullbackDenominatorModuleToPullback :
    (Scheme.Modules.pullback φ).obj (pullbackDenominatorModule φ L s) ⟶ L :=
  ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv
      (pullbackDenominatorModule φ L s) L).symm (pullbackDenominatorModuleMul φ L s)

/-- **Stacks Tag 0BD7 reduced to its two remaining assertions.** Granted that `𝒩` is invertible
and that `φ^*𝒩 ⟶ ℒ` is an isomorphism, `ℒ` is pulled back from an invertible module on `Y`.
This is the conclusion of the tag; the tag itself is not proved here, and what remains of it is
exactly the two hypotheses of this lemma. -/
theorem exists_isInvertible_and_nonempty_pullback_iso
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y) Y.sheaf).property
      (pullbackDenominatorModule φ L s))
    (hiso : IsIso (pullbackDenominatorModuleToPullback φ L s)) :
    ∃ (N : Y.Modules) (_ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
        (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
          Y.sheaf).property N),
      Nonempty ((Scheme.Modules.pullback φ).obj N ≅ L) :=
  ⟨pullbackDenominatorModule φ L s, hN, ⟨asIso (pullbackDenominatorModuleToPullback φ L s)⟩⟩

end Stacks.Meromorphic
