module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteModelComparison

/-!
# The two readings of `Mod(C/U, Λ)` over the constant ringed site are the same functor

Let `J` be a Grothendieck topology on a small category `C` and let `Λ` be a commutative ring.
A sheaf of modules over the restriction to an object `U` of the structure sheaf `Λ̲` of the
constant ringed site can be read as a sheaf of `Λ`-modules on the slice site `C/U` in two ways:

* through the constant sheaf of rings **of the slice site**, by restricting the scalars along
  `AlgebraicGeometry.RingedSite.constantRingSheafOverIso` and then applying the equivalence of
  `Stacks.ConstantRingModules.constantModuleSheafEquivalence` on `C/U`. That composite is
  `Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence`.
* through the restriction to `C/U` of the **global** map out of the constant presheaf of rings,
  by `Stacks.ConstantRingModules.toModuleSheaf` at `Stacks.ConstantRingModules.overRingMap`.
  Its compatibility with passage to a slice and with restriction along an arrow of the site is
  `Stacks.ConstantRingModules.toModuleSheafOverIso` and `toModuleSheafOverMapIso`, with derived
  versions `toModuleSheafOverDerivedIso` and `toModuleSheafOverMapDerivedIso`.

The two are the same functor, not merely isomorphic ones:
`Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence_functor_eq`.

## Main results

* `Stacks.ConstantRingModules.restrictScalars_comp_toModuleSheaf`: the `Λ`-reading of sheaves
  of modules depends on the map out of the constant presheaf of rings alone; restricting the
  scalars along `φ : R ⟶ R'` first and reading along `α` is reading along `α ≫ φ`.
* `Stacks.ConstantRingModules.constantRingedSiteRingMap`: the map out of the constant presheaf
  of rings for the constant ringed site; it is locally injective and locally surjective.
* `Stacks.ConstantRingModules.overRingMap_constantRingedSiteRingMap`: its restriction to the
  slice site `C/U` is the sheafification map of `C/U` followed by
  `AlgebraicGeometry.RingedSite.constantRingSheafOverIso`.
* `Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence_functor_eq`: the
  identification of the two readings.
* `Stacks.ConstantRingModules.constantRingedSiteModuleDerivedEquivalence_functor_eq`: the same
  identification on derived categories.

## Implementation notes

**Why an equality and not an isomorphism.** `Stacks.ConstantRingModules.toModuleSheaf` reads a
sheaf of modules over `R` as a sheaf of `Λ`-modules by restricting the scalars along the given
`α : constRing Λ ⟶ R.obj`; it changes neither the sections nor the sheaf condition, and the
`Λ`-action it installs on `M(X)` is `λ • m = α_X(λ) • m`. Restricting the scalars along a
morphism of sheaves of rings first changes the action in exactly the same way, so the composite
reading along `α` is the reading along the composite map, on the nose — that is
`restrictScalars_comp_toModuleSheaf`, proved by `rfl`. The two readings therefore differ only in
their map out of the constant presheaf of rings, and once those two maps are shown equal the
functors are equal by `congrArg`.

**The equality of the two maps** is the sheafification-versus-slicing compatibility of Mathlib,
`CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility`, whose statement is the
whole natural transformation rather than its component at the terminal object of `C/U`
(`Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso`). Composed with the forgetting
of commutativity, `AlgebraicGeometry.RingedSite.constantRingSheafIso`, it is exactly the
definition of `AlgebraicGeometry.RingedSite.constantRingSheafOverIso`, so the proof is that
compatibility, one associativity and `rfl`.

The associativity step is written out in a `calc` rather than reached by `rw`. The codomain of
the compatibility is spelled `(presheafToSheaf J RingCat ⋙ overPullback) (const Λ)` on one side
of the equation and `(Over.forget U).op ⋙ sheafify J (const Λ)` on the other; the two are
definitionally equal but not syntactically so, and a `rw` of `Category.assoc` across them builds
a term that is rejected at the transparency the elaborator re-checks it at. Stating the
intermediate step lets the elaborator unify the two spellings itself.

## References

* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ConstantRingModules

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules.Constant Stacks.Sheaves.RingedPoint

universe r a v u d

section General

variable {C : Type u} [Category.{v} C] (Λ : Type r) [Ring Λ]
  (J : GrothendieckTopology C) {R R' : Sheaf J RingCat.{r}}

/-- **The `Λ`-reading of a sheaf of modules depends only on the map out of the constant presheaf
of rings.** Restricting the scalars along a morphism `φ : R ⟶ R'` of sheaves of rings and then
reading the result as a sheaf of `Λ`-modules along `α : constRing Λ ⟶ R.obj` is reading along
the composite `α ≫ φ`.

This is an equality of functors: neither functor touches the sections or the sheaf condition,
and both install the `Λ`-action `λ • m = φ_X(α_X(λ)) • m`. -/
theorem restrictScalars_comp_toModuleSheaf (φ : R ⟶ R')
    (α : PresheafOfModules.constRing (C := C) Λ ⟶ R.obj) :
    SheafOfModules.restrictScalars.{a} φ ⋙ toModuleSheaf.{a} Λ J α =
      toModuleSheaf.{a} Λ J (α ≫ φ.hom) := rfl

end General

section ConstantRingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
  [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J RingCat.{u}]

/-- **The map out of the constant presheaf of rings for the constant ringed site.** The
sheafification map of `C` followed by the identification of the constant sheaf of rings with the
sheaf of rings underlying the structure sheaf of
`AlgebraicGeometry.RingedSite.constantRingedSite`. -/
def constantRingedSiteRingMap :
    PresheafOfModules.constRing (C := C) Λ ⟶
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O)).obj :=
  constantRingMap Λ J ≫ (constantRingSheafIso_general J Λ).inv.hom

/-- The map `constantRingedSiteRingMap` is locally injective. -/
instance isLocallyInjective_constantRingedSiteRingMap :
    Presheaf.IsLocallyInjective J (constantRingedSiteRingMap J Λ) := by
  rw [show constantRingedSiteRingMap J Λ =
    constantRingMap Λ J ≫ (constantRingSheafIso_general J Λ).inv.hom from rfl]
  infer_instance

/-- The map `constantRingedSiteRingMap` is locally surjective. -/
instance isLocallySurjective_constantRingedSiteRingMap :
    Presheaf.IsLocallySurjective J (constantRingedSiteRingMap J Λ) := by
  rw [show constantRingedSiteRingMap J Λ =
    constantRingMap Λ J ≫ (constantRingSheafIso_general J Λ).inv.hom from rfl]
  infer_instance

variable (U : C) [HasWeakSheafify (J.over U) RingCat.{u}]

/-- **The two readings agree at the level of the maps out of the constant presheaf of rings.**
The restriction to the slice site `C/U` of `constantRingedSiteRingMap` — the global map,
whiskered along `Over.forget U` — is the sheafification map of `C/U` followed by
`AlgebraicGeometry.RingedSite.constantRingSheafOverIso`.

It is Mathlib's compatibility of sheafification with restriction to a slice,
`CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility`, read as the whole
natural transformation. -/
theorem overRingMap_constantRingedSiteRingMap :
    overRingMap Λ J (constantRingedSiteRingMap J Λ) U =
      constantRingMap Λ (J.over U) ≫ (constantRingSheafOverIso_general J Λ U).hom.hom := by
  have h := (Over.forget U).toSheafify_pullbackSheafificationCompatibility RingCat.{u}
    (J.over U) J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  show Functor.whiskerLeft (Over.forget U).op
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))) ≫
      Functor.whiskerLeft (Over.forget U).op (constantRingSheafIso_general J Λ).inv.hom =
    toSheafify (J.over U) ((Over.forget U).op ⋙ (Functor.const Cᵒᵖ).obj (RingCat.of Λ)) ≫
      (constantRingSheafOverIso_general J Λ U).hom.hom
  calc Functor.whiskerLeft (Over.forget U).op
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))) ≫
      Functor.whiskerLeft (Over.forget U).op (constantRingSheafIso_general J Λ).inv.hom
      = (toSheafify (J.over U) ((Over.forget U).op ⋙ (Functor.const Cᵒᵖ).obj (RingCat.of Λ)) ≫
          (((Over.forget U).pushforwardContinuousSheafificationCompatibility RingCat.{u}
            (J.over U) J).hom.app ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).hom) ≫
          Functor.whiskerLeft (Over.forget U).op (constantRingSheafIso_general J Λ).inv.hom := by
        rw [h]
        exact rfl
    _ = toSheafify (J.over U) ((Over.forget U).op ⋙ (Functor.const Cᵒᵖ).obj (RingCat.of Λ)) ≫
          ((((Over.forget U).pushforwardContinuousSheafificationCompatibility RingCat.{u}
            (J.over U) J).hom.app ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).hom ≫
          Functor.whiskerLeft (Over.forget U).op (constantRingSheafIso_general J Λ).inv.hom) :=
        Category.assoc _ _ _
    _ = _ := rfl

variable [(J.over U).WEqualsLocallyBijective RingCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

omit [HasWeakSheafify (J.over U) (ModuleCat Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat Λ)] in
/-- **The two readings of `Mod(C/U, Λ)` over the constant ringed site are the same functor.**
The functor of `Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence`, which reads a
sheaf of `Λ̲|_U`-modules through the constant sheaf of rings of the slice site, *is* the
`Λ`-reading along the restriction to `C/U` of the global map out of the constant presheaf of
rings. -/
theorem constantRingedSiteModuleEquivalence_functor_eq :
    (constantRingedSiteModuleEquivalence J Λ U).functor =
      toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J (constantRingedSiteRingMap J Λ) U) := by
  rw [overRingMap_constantRingedSiteRingMap]
  exact (restrictScalars_comp_toModuleSheaf.{u} Λ (J.over U)
    (constantRingSheafOverIso_general J Λ U).hom (constantRingMap Λ (J.over U))).symm

end ConstantRingedSite

end Stacks.ConstantRingModules

end
