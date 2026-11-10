module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedSectionsIdealPow
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ThickeningDivAlpha
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# The Situation of Tag 0GA6 at the blowup

`Stacks.LocalCohomology.UniformityIII.Situation A I` is the structure the four abstract clause
theorems of [Stacks, Tag 0GA7] in `BitUniformityIII/BoundQAndD.lean` are stated about: a
Noetherian ring `A`, an ideal `I`, two integers `d` and `q₀`, the cohomology modules
`Hⁱ(X, 𝒪_{Yₙ}(q))` and `Hⁱ(X, 𝒪_X(q))` of the blowup as objects of `ModuleCat A`, the canonical
maps out of the subquotients of `A`, the long exact sequences of the two short exact sequences
of the section, and the properties of these that the Stacks Project establishes before Tag 0GA7
is stated.

This file builds that structure **from the blowup geometry**, for `[IsNoetherianRing A]` and any
ideal `I ⊆ A`, so that the four theorems about an abstract `Situation` become statements about the
blowup under no hypothesis beyond Noetherianity. It also defines the integer `q(S)` of
[Stacks, Tag 0GA6] — the least `q₀` such that for `q ≥ q₀` the exceptional divisor `Y` has
`Hⁱ(Y, 𝒪_Y(q)) = 0` for `i ≥ 1` and `H⁰(Y, 𝒪_Y(q)) = Iᑫ/I^{q+1}` — and builds the structure at
`q₀ = q(S)`, which is where Tag 0GA7 is stated.

## The two halves of the bridge

The geometry is available, but about cohomology valued in `AddCommGrpCat`:
`Stacks.LocalCohomology.UniformityIII.blowupH` is the right derived functor of
`secF`, the abelian-group-valued global sections. `Situation` asks for `ModuleCat A`. So:

* **The module structure.** `blowupΓmod` is global sections valued in `ModuleCat A` —
  `AlgebraicGeometry.globalSectionsOver` of the blowup, spelled at the `SheafOfModules`
  view of the category so that its right derived functors are elaborated with the same instances
  as `blowupH`. Its right derived functors are `blowupHmod`, and the only thing needed of the
  `AddCommGrpCat` results is that they transfer: forgetting the `A`-module structure is
  exact, hence commutes with right derived functors
  (`Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`), and
  `blowupΓmod ⋙ forget₂ = secF` **on the nose** (`blowupΓmod_comp_forget`, a `rfl`). That is
  `subsingleton_blowupHmod`, and it is the whole of the transfer: nothing else about the module
  cohomology is imported from the abelian-group version.

* **The long exact sequences.** They are not transferred either: the δ-functor of
  [Stacks, Tag 010Q] is formed for `blowupΓmod` itself (`blowupDeltaMod`), so the connecting maps
  `divδ`/`ambδ` are `A`-linear by construction and the exactness fields are its own
  `exact_map`/`exact_δ₁` at the two short exact sequences,
  `Stacks.LocalCohomology.UniformityIII.shortExact_divα` and
  `Stacks.LocalCohomology.UniformityIII.shortExact_ambientTwistMap`.

In degree `0` the comparison `Functor.toRightDerivedZero` identifies `H⁰` with `Γ`, and is an
isomorphism because `blowupΓmod` is left exact (`blowupΓmod_preservesFiniteLimits`). That is what
carries the statements about sections — the canonical maps
`Stacks.LocalCohomology.UniformityIII.thickeningSections` and
`Stacks.LocalCohomology.UniformityIII.ambientSections` and the two commutative squares of the
Stacks proof — into `H⁰`. Their `A`-linearity is
`Stacks.Blowup.ambientSectionsLinear` together with the functoriality of `blowupΓmod`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupΓmod`: `Γ(X, -) : Mod(𝒪_X) ⥤ ModuleCat A`.
* `Stacks.LocalCohomology.UniformityIII.blowupHmod`: `Hⁱ(X, ℱ)` as an `A`-module.
* `Stacks.LocalCohomology.UniformityIII.blowupDeltaMod`: the `A`-linear δ-functor.
* `Stacks.LocalCohomology.UniformityIII.IsBaseThreshold`: the defining property of `q(S)`.
* `Stacks.LocalCohomology.UniformityIII.qS`: the integer `q(S)`, the least integer with it.
* `Stacks.LocalCohomology.UniformityIII.blowupSituationOf`: a term of `Situation A I` at every
  `q₀` with the defining property of `q(S)`, for `[IsNoetherianRing A]` and any `I`.
* `Stacks.LocalCohomology.UniformityIII.blowupSituation`: **the witness** at `q₀ = q(S)`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupHmod`: the transfer of vanishing from
  `blowupH` to `blowupHmod`.
* `Stacks.LocalCohomology.UniformityIII.thickeningSections_eq_zero_of_mem`: the canonical map
  `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))` kills `I^{q+n}`, for every `n ≥ 1` and with no hypothesis on `q`. This
  is what makes the map out of the subquotient `Iᑫ/I^{q+n}` exist at all; it is the induction of
  the first short exact sequence on the `n = 1` case
  `Stacks.LocalCohomology.UniformityIII.thickeningSections_one_eq_zero_of_mem`.
* `Stacks.LocalCohomology.UniformityIII.isBaseThreshold_qS`,
  `Stacks.LocalCohomology.UniformityIII.qS_le`: `q(S)` has the property and is least with it.
* `Stacks.LocalCohomology.UniformityIII.exists_qS_isLeast_isBaseThresholdUpTo`: `q(S)` is the
  least integer satisfying the source's literal definition, vanishing asked only for
  `1 ≤ i ≤ D`, at a degree bound `D` past which the cohomology of every `𝒪_Y(q)` vanishes.
* `Stacks.LocalCohomology.UniformityIII.blowupSituationOf_Hdiv`,
  `Stacks.LocalCohomology.UniformityIII.blowupSituationOf_Hamb`,
  `Stacks.LocalCohomology.UniformityIII.blowupSituationOf_cdiv_mk`,
  `Stacks.LocalCohomology.UniformityIII.blowupSituationOf_camb`: the witness's cohomology modules
  and canonical maps *are* the blowup's, so that the four theorems of Tag 0GA7 read at
  `blowupSituationOf` are the four clauses of the tag for the blowup.
* `Stacks.LocalCohomology.UniformityIII.blowupHmod_of_qS_le`: **[Stacks, Tag 0GA7]**, all four
  clauses at `q₀ = q(S)`.

## References

* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### `A`-linear global sections and cohomology of the blowup -/

/-- **Global sections of a sheaf of `𝒪_X`-modules on the blowup as an `A`-module**: evaluation at
`⊤` followed by restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`.

This is `AlgebraicGeometry.globalSectionsOver` of `Stacks.Blowup.toSpec`, written out at the
`SheafOfModules` view of the category of modules rather than the `AlgebraicGeometry.Scheme.Modules`
view: the two are definitionally equal but carry separately declared instances, and the right
derived functors below have to be elaborated with the ones `blowupH` uses. -/
abbrev blowupΓmod : _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf ⥤ ModuleCat.{u} A :=
  _root_.SheafOfModules.evaluation (blowupScheme I).ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Stacks.Blowup.toSpec I).appTop).hom)

/-- Addition of sections of a sheaf of modules is computed open by open, so `A`-linear global
sections is additive. -/
instance blowupΓmod_additive : (blowupΓmod I).Additive where map_add := rfl

/-- **`A`-linear global sections with the module structure forgotten is `secF`.** Both sides send
a sheaf of modules to the abelian group of its sections over `⊤`; they are equal, not merely
isomorphic, which is what lets the vanishing statements about `blowupH` be read as
statements about the right derived functors of `blowupΓmod`. -/
theorem blowupΓmod_comp_forget :
    blowupΓmod I ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} =
      secF (blowupScheme I).ringCatSheaf (⊤ : (blowupScheme I).Opens) :=
  rfl

/-- `Γ(X, -)` composed with the forgetful functor is left exact, being `secF`. -/
instance blowupΓmodCompForget_preservesFiniteLimits :
    PreservesFiniteLimits (blowupΓmod I ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) :=
  secFPreservesFiniteLimits I

/-- **`A`-linear global sections on the blowup is left exact.** Forgetting the module structure
reflects finite limits and the composite is `secF`, which is left exact. This is what makes the
degree-`0` fields of the Situation theorems rather than hypotheses. -/
instance blowupΓmod_preservesFiniteLimits : PreservesFiniteLimits (blowupΓmod I) :=
  preservesFiniteLimits_of_reflects_of_preserves (blowupΓmod I)
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})

/-- **The sheaf cohomology `Hⁱ(X, ℱ)` of the blowup as an `A`-module**: the `i`-th right derived
functor of `blowupΓmod`. -/
abbrev blowupHmod (i : ℕ) (F : (blowupScheme I).Modules) : ModuleCat.{u} A :=
  ((blowupΓmod I).rightDerived i).obj F

/-- `Hⁱ(X, -)` of a morphism of sheaves, as a morphism of `A`-modules. -/
abbrev blowupHmodMap (i : ℕ) {F G : (blowupScheme I).Modules} (φ : F ⟶ G) :
    blowupHmod I i F ⟶ blowupHmod I i G :=
  ((blowupΓmod I).rightDerived i).map φ

/-- **The transfer of vanishing from the abelian-group-valued cohomology to the `A`-module-valued
one.** Forgetting the `A`-module structure is exact, hence commutes with right derived functors,
and `blowupΓmod ⋙ forget₂` *is* `secF`; so the underlying abelian group of `Hⁱ(X, ℱ)` in
`ModuleCat A` is `blowupH I i ℱ`, and an `A`-module whose underlying group is trivial is
trivial. -/
theorem subsingleton_blowupHmod (i : ℕ) (F : (blowupScheme I).Modules)
    (h : Subsingleton (blowupH I i F)) : Subsingleton (blowupHmod I i F) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (blowupΓmod I) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) i F
  exact AddCommGrpCat.subsingleton_of_isZero
    ((AddCommGrpCat.isZero_iff_subsingleton.mpr h).of_iso e)

/-- **The `A`-linear cohomological δ-functor of the blowup** ([Stacks, Tag 010Q]): the right
derived δ-functor of `blowupΓmod`. This is what turns the two short exact sequences of sheaves of
the Situation into long exact sequences of `A`-modules, with `A`-linear connecting maps. -/
def blowupDeltaMod :
    CategoryTheory.DeltaFunctor (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf)
      (ModuleCat.{u} A) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (blowupΓmod I)

/-- The δ-functor's functors are the right derived functors of `blowupΓmod`. -/
theorem blowupDeltaMod_functor (i : ℕ) :
    (blowupDeltaMod I).functor i = (blowupΓmod I).rightDerived i :=
  rfl

/-- **The long exact cohomology sequence at the middle term.**

The two maps are explicit arguments rather than the fields of an implicit short complex: with
them implicit, the unification at a use site has to reduce `ShortComplex.mk _ _ _ |>.f`
*underneath* the right derived functor, which exhausts the heartbeat budget. -/
theorem exact_blowupHmodMap {F G H : (blowupScheme I).Modules} (f : F ⟶ G) (g : G ⟶ H)
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact) (i : ℕ) :
    Function.Exact (blowupHmodMap I i f).hom (blowupHmodMap I i g).hom := by
  have h := (blowupDeltaMod I).exact_map hS i
  rwa [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h

/-- **The long exact cohomology sequence at the third term**, the segment adjacent to the
connecting map. -/
theorem exact_blowupHmodMap_δ {F G H : (blowupScheme I).Modules} (f : F ⟶ G) (g : G ⟶ H)
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact) (i : ℕ) :
    Function.Exact (blowupHmodMap I i g).hom ((blowupDeltaMod I).δ hS i).hom := by
  have h := (blowupDeltaMod I).exact_δ₁ hS i
  rwa [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h

/-- **The long exact cohomology sequence begins with an injection.** -/
theorem injective_blowupHmodMap {F G H : (blowupScheme I).Modules} (f : F ⟶ G) (g : G ⟶ H)
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact) :
    Function.Injective (blowupHmodMap I 0 f).hom :=
  (ModuleCat.mono_iff_injective _).1 ((blowupDeltaMod I).mono_map_f hS)

/-! ### Degree zero: the canonical maps out of the powers of `I` -/

/-- The comparison `Γ(X, ℱ) ⟶ H⁰(X, ℱ)`, an isomorphism because `blowupΓmod` is left exact. -/
abbrev blowupΓmodToH0 (F : (blowupScheme I).Modules) :
    (blowupΓmod I).obj F ⟶ blowupHmod I 0 F :=
  (blowupΓmod I).toRightDerivedZero.app F

/-- **`Γ(X, ℱ) ⟶ H⁰(X, ℱ)` is bijective**: it is the inverse of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, which exists because `blowupΓmod` is left
exact. This is what identifies the degree-`0` cohomology of the Situation with the sections the
blowup geometry computes. -/
theorem bijective_blowupΓmodToH0 (F : (blowupScheme I).Modules) :
    Function.Bijective (blowupΓmodToH0 I F) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨(blowupΓmod I).rightDerivedZeroIsoSelf.hom.app F,
      fun x => ConcreteCategory.congr_hom
        ((blowupΓmod I).rightDerivedZeroIsoSelf_inv_hom_id_app F) x,
      fun y => ConcreteCategory.congr_hom
        ((blowupΓmod I).rightDerivedZeroIsoSelf_hom_inv_id_app F) y⟩

/-- `Γ(X, ℱ) ⟶ H⁰(X, ℱ)` is injective. -/
theorem injective_blowupΓmodToH0 (F : (blowupScheme I).Modules) :
    Function.Injective (blowupΓmodToH0 I F) :=
  (bijective_blowupΓmodToH0 I F).1

/-- `Γ(X, ℱ) ⟶ H⁰(X, ℱ)` is surjective. -/
theorem surjective_blowupΓmodToH0 (F : (blowupScheme I).Modules) :
    Function.Surjective (blowupΓmodToH0 I F) :=
  (bijective_blowupΓmodToH0 I F).2

/-- `Γ(X, ℱ) ⟶ H⁰(X, ℱ)` is natural: it intertwines `blowupΓMap` and `blowupHmodMap`. -/
theorem blowupΓmodToH0_naturality {F G : (blowupScheme I).Modules} (φ : F ⟶ G)
    (x : blowupΓ I F) :
    blowupΓmodToH0 I G (blowupΓMap I φ x) = blowupHmodMap I 0 φ (blowupΓmodToH0 I F x) :=
  ConcreteCategory.congr_hom ((blowupΓmod I).toRightDerivedZero.naturality φ) x

/-- The long exact sequence of the first short exact sequence, at the middle term. -/
theorem exact_blowupHmodMap_divα (n i q : ℕ) :
    Function.Exact (blowupHmodMap I i (divα I n q)).hom
      (blowupHmodMap I i (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)).hom :=
  exact_blowupHmodMap I (divα I n q) (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)
    (divα_comp_thickeningTwistRestrict_eq_zero I n q) (shortExact_divα I n q) i

/-- The long exact sequence of the first short exact sequence, at the third term. -/
theorem exact_blowupHmodMap_divα_δ (n i q : ℕ) :
    Function.Exact
      (blowupHmodMap I i (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)).hom
      ((blowupDeltaMod I).δ (shortExact_divα I n q) i).hom :=
  exact_blowupHmodMap_δ I (divα I n q) (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)
    (divα_comp_thickeningTwistRestrict_eq_zero I n q) (shortExact_divα I n q) i

/-- The long exact sequence of the first short exact sequence begins with an injection. -/
theorem injective_blowupHmodMap_divα (n q : ℕ) :
    Function.Injective (blowupHmodMap I 0 (divα I n q)).hom :=
  injective_blowupHmodMap I (divα I n q) (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)
    (divα_comp_thickeningTwistRestrict_eq_zero I n q) (shortExact_divα I n q)

/-- The long exact sequence of the second short exact sequence, at the middle term. -/
theorem exact_blowupHmodMap_ambientTwistMap (i q : ℕ) :
    Function.Exact (blowupHmodMap I i (ambientTwistMap I q)).hom
      (blowupHmodMap I i (thickeningTwistProj I 1 q)).hom :=
  exact_blowupHmodMap I (ambientTwistMap I q) (thickeningTwistProj I 1 q)
    (ambientTwistMap_comp_thickeningTwistProj_eq_zero I q) (shortExact_ambientTwistMap I q) i

/-- The long exact sequence of the second short exact sequence, at the third term. -/
theorem exact_blowupHmodMap_ambientTwistMap_δ (i q : ℕ) :
    Function.Exact (blowupHmodMap I i (thickeningTwistProj I 1 q)).hom
      ((blowupDeltaMod I).δ (shortExact_ambientTwistMap I q) i).hom :=
  exact_blowupHmodMap_δ I (ambientTwistMap I q) (thickeningTwistProj I 1 q)
    (ambientTwistMap_comp_thickeningTwistProj_eq_zero I q) (shortExact_ambientTwistMap I q) i

/-- The long exact sequence of the second short exact sequence begins with an injection. -/
theorem injective_blowupHmodMap_ambientTwistMap (q : ℕ) :
    Function.Injective (blowupHmodMap I 0 (ambientTwistMap I q)).hom :=
  injective_blowupHmodMap I (ambientTwistMap I q) (thickeningTwistProj I 1 q)
    (ambientTwistMap_comp_thickeningTwistProj_eq_zero I q) (shortExact_ambientTwistMap I q)

/-- **The canonical map `Iᑫ → H⁰(X, 𝒪_X(q))` as an `A`-linear map.** Its underlying additive map
is `Stacks.LocalCohomology.UniformityIII.ambientSections` read into `H⁰` along
`blowupΓmodToH0`; the linearity is `Stacks.Blowup.ambientSectionsLinear`. -/
def ambientSectionsMod (q : ℕ) :
    (I ^ q : Ideal A) →ₗ[A] blowupHmod I 0 (blowupTwist I q) :=
  (blowupΓmodToH0 I (blowupTwist I q)).hom ∘ₗ Stacks.Blowup.ambientSectionsLinear I q

/-- `ambientSectionsMod I q x` is the image under `blowupΓmodToH0` of the section
`ambientSections I q x`. -/
theorem ambientSectionsMod_apply (q : ℕ) (x : (I ^ q : Ideal A)) :
    ambientSectionsMod I q x = blowupΓmodToH0 I (blowupTwist I q) (ambientSections I q x) :=
  rfl

/-- **The canonical map `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))` as an `A`-linear map.** -/
def thickeningSectionsMod (n q : ℕ) :
    (I ^ q : Ideal A) →ₗ[A] blowupHmod I 0 (thickeningTwist I n q) :=
  (blowupHmodMap I 0 (thickeningTwistProj I n q)).hom ∘ₗ ambientSectionsMod I q

/-- `thickeningSectionsMod I n q x` is the image under `blowupΓmodToH0` of the section
`thickeningSections I n q x`. -/
theorem thickeningSectionsMod_apply (n q : ℕ) (x : (I ^ q : Ideal A)) :
    thickeningSectionsMod I n q x =
      blowupΓmodToH0 I (thickeningTwist I n q) (thickeningSections I n q x) := by
  change blowupHmodMap I 0 (thickeningTwistProj I n q)
      (blowupΓmodToH0 I (blowupTwist I q) (ambientSections I q x)) = _
  rw [← blowupΓmodToH0_naturality]
  rfl

/-- A class in `Iᑫ` dies in `H⁰(X, 𝒪_{Yₙ}(q))` exactly when its canonical section does. Every
`0` here is the zero of a genuine linear or additive map, which is what keeps the two `Zero`
instances on the sections — the one of `blowupΓ` and the one of `blowupΓmod`'s value — from
having to be matched. -/
theorem thickeningSectionsMod_eq_zero_iff (n q : ℕ) (x : (I ^ q : Ideal A)) :
    thickeningSectionsMod I n q x = 0 ↔ thickeningSections I n q x = 0 := by
  have h : thickeningSectionsMod I n q x = thickeningSectionsMod I n q 0 ↔
      thickeningSections I n q x = thickeningSections I n q 0 := by
    rw [thickeningSectionsMod_apply, thickeningSectionsMod_apply]
    exact (injective_blowupΓmodToH0 I _).eq_iff
  rwa [map_zero, map_zero] at h

/-- **The canonical map `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))` kills `I^{q+n}`**, for every `n ≥ 1` and with no
hypothesis on `q`.

This is what makes the map out of the subquotient `Iᑫ/I^{q+n}` exist. The case `n = 1` is
`Stacks.LocalCohomology.UniformityIII.thickeningSections_one_eq_zero_of_mem`, and the induction
step is the left-hand square of the diagram in the proof of Tag 0GA7(2),
`Stacks.LocalCohomology.UniformityIII.blowupΓMap_divα_thickeningSections`: the class of
`x ∈ I^{q+n+1}` in `H⁰(X, 𝒪_{Y_{n+1}}(q))` is the image under `𝒪_{Yₙ}(q+1) ⟶ 𝒪_{Y_{n+1}}(q)` of
its class in `H⁰(X, 𝒪_{Yₙ}(q+1))`, and `x ∈ I^{(q+1)+n}`. -/
theorem thickeningSections_eq_zero_of_mem {n : ℕ} (hn : 1 ≤ n) :
    ∀ (q : ℕ) (x : (I ^ q : Ideal A)), (x : A) ∈ I ^ (q + n) →
      thickeningSections I n q x = 0 := by
  induction n, hn using Nat.le_induction with
  | base => exact fun q x hx => thickeningSections_one_eq_zero_of_mem I q x hx
  | succ n hn ih =>
    intro q x hx
    have hx1 : (x : A) ∈ I ^ (q + 1) :=
      Ideal.pow_le_pow_right (by omega) hx
    have hz : thickeningSections I n (q + 1) ⟨(x : A), hx1⟩ = 0 :=
      ih (q + 1) ⟨(x : A), hx1⟩ (by rw [show q + 1 + n = q + (n + 1) by omega]; exact hx)
    have key := blowupΓMap_divα_thickeningSections I n q ⟨(x : A), hx1⟩
    rw [hz, map_zero] at key
    have hsub : (⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) hx1⟩ : (I ^ q : Ideal A)) = x :=
      Subtype.ext rfl
    rw [hsub] at key
    exact key.symm

/-- **The canonical map `Iᑫ/I^{q+n+1} → H⁰(X, 𝒪_{Y_{n+1}}(q))` as an `A`-linear map**, the field
`cdiv` of the Situation at `n + 1`: `thickeningSectionsMod` descended along
`thickeningSections_eq_zero_of_mem`. -/
def cdivMod (n q : ℕ) :
    powQuot I q (n + 1) →ₗ[A] blowupHmod I 0 (thickeningTwist I (n + 1) q) :=
  (powSub I q (n + 1)).liftQ (thickeningSectionsMod I (n + 1) q) (by
    intro x hx
    simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hx
    rw [LinearMap.mem_ker, thickeningSectionsMod_eq_zero_iff]
    exact thickeningSections_eq_zero_of_mem I (Nat.le_add_left 1 n) q x hx)

/-- `cdivMod` sends the class of `x ∈ Iᑫ` to `thickeningSectionsMod I (n + 1) q x`. -/
theorem cdivMod_mk' (n q : ℕ) (x : (I ^ q : Ideal A)) :
    cdivMod I n q (Submodule.Quotient.mk x) = thickeningSectionsMod I (n + 1) q x :=
  rfl

/-- `cdivMod` sends the class of `x ∈ Iᑫ` to the image under `blowupΓmodToH0` of the section
`thickeningSections I (n + 1) q x`. -/
theorem cdivMod_mk (n q : ℕ) (x : (I ^ q : Ideal A)) :
    cdivMod I n q (Submodule.Quotient.mk x) =
      blowupΓmodToH0 I (thickeningTwist I (n + 1) q) (thickeningSections I (n + 1) q x) :=
  (cdivMod_mk' I n q x).trans (thickeningSectionsMod_apply I (n + 1) q x)

/-! ### The threshold `q(S)` -/

/-- **`q₀` has the defining property of `q(S)`** ([Stacks, Tag 0GA6]): for every `q ≥ q₀`,
`Hⁱ(Y, 𝒪_Y(q)) = 0` for every `i ≥ 1`, and the canonical map
`Iᑫ/I^{q+1} → H⁰(Y, 𝒪_Y(q))` is an isomorphism of `A`-modules.

`Y = Y₁` is the exceptional divisor, and its twists `𝒪_Y(q)` are the sheaves
`thickeningTwist I 1 q` on the blowup `X`; their cohomology on `X` is the cohomology on `Y`, as the
source itself uses when it says that the case `n = 1` of Tag 0GA7 *is* the definition of `q₀`.

The source asks for the vanishing only for `1 ≤ i ≤ d(S)`, because `Hⁱ(Y, 𝒪_Y(q)) = 0` for
`i > d(S)` anyway ([Stacks, Tags 02V7, 01XK]). Asking it for every `i ≥ 1` is therefore the same
condition; `isBaseThreshold_iff_of_vanishing_gt` says so for every bound `D` above which those
cohomology modules vanish, and `exists_qS_isLeast_isBaseThresholdUpTo` that such a `D` exists
and that `qS` is the least integer satisfying the literal definition at it. -/
def IsBaseThreshold (q₀ : ℕ) : Prop :=
  (∀ i q : ℕ, 1 ≤ i → q₀ ≤ q → Subsingleton (blowupHmod I i (thickeningTwist I 1 q))) ∧
    ∀ q : ℕ, q₀ ≤ q → Function.Bijective (cdivMod I 0 q)

/-- The defining property of `q(S)` passes to every larger integer. -/
theorem IsBaseThreshold.mono {q₀ q₁ : ℕ} (h : IsBaseThreshold I q₀) (hle : q₀ ≤ q₁) :
    IsBaseThreshold I q₁ :=
  ⟨fun i q hi hq => h.1 i q hi (hle.trans hq), fun q hq => h.2 q (hle.trans hq)⟩

/-- **The defining property of `q(S)` with the vanishing asked only up to `D`**, for any `D`
above which `Hⁱ(Y, 𝒪_Y(q))` vanishes for every `q` — for instance `D = d(S)`, the maximal
dimension of the fibres of `p`. This is the literal form of the source's definition, which asks
for `Hⁱ(Y, 𝒪_Y(q)) = 0` only for `1 ≤ i ≤ d`. -/
theorem isBaseThreshold_iff_of_vanishing_gt (D q₀ : ℕ)
    (hD : ∀ i q : ℕ, D < i → Subsingleton (blowupHmod I i (thickeningTwist I 1 q))) :
    IsBaseThreshold I q₀ ↔
      (∀ i q : ℕ, 1 ≤ i → i ≤ D → q₀ ≤ q →
        Subsingleton (blowupHmod I i (thickeningTwist I 1 q))) ∧
        ∀ q : ℕ, q₀ ≤ q → Function.Bijective (cdivMod I 0 q) := by
  refine ⟨fun h => ⟨fun i q hi _ hq => h.1 i q hi hq, h.2⟩,
    fun h => ⟨fun i q hi hq => ?_, h.2⟩⟩
  rcases le_or_gt i D with hiD | hiD
  · exact h.1 i q hi hiD hq
  · exact hD i q hiD

/-- **Some integer has the defining property of `q(S)`**, for `A` Noetherian: the larger of
Serre's two thresholds on `X`, by `exists_baseThreshold`. This is the existence the source draws
from [Stacks, Tags 0AG6, 0AG7] to define `q(S)`. -/
theorem exists_isBaseThreshold [IsNoetherianRing A] : ∃ q₀, IsBaseThreshold I q₀ := by
  obtain ⟨q₀, hvan, hsurj, hker⟩ := exists_baseThreshold I
  refine ⟨q₀, fun i q hi hq => subsingleton_blowupHmod I i _ (hvan i q hi hq), fun q hq => ?_⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [cdivMod_mk', thickeningSectionsMod_eq_zero_iff] at hy
      rw [Submodule.Quotient.mk_eq_zero]
      simpa [powSub] using hker q hq y hy
  · intro y
    obtain ⟨w, hw⟩ := surjective_blowupΓmodToH0 I (thickeningTwist I 1 q) y
    obtain ⟨z, hz⟩ := hsurj q hq w
    exact ⟨Submodule.Quotient.mk z, by rw [cdivMod_mk, hz, hw]⟩

/-- **The integer `q(S)` of [Stacks, Tag 0GA6]**: the smallest `q₀ ≥ 0` such that for all
`q ≥ q₀`, `Hⁱ(Y, 𝒪_Y(q)) = 0` for `i ≥ 1` and `H⁰(Y, 𝒪_Y(q)) = Iᑫ/I^{q+1}`
(`IsBaseThreshold`). It is attained for `A` Noetherian (`isBaseThreshold_qS`) and least
(`qS_le`). -/
def qS : ℕ := sInf {q₀ | IsBaseThreshold I q₀}

/-- `q(S)` has its defining property. -/
theorem isBaseThreshold_qS [IsNoetherianRing A] : IsBaseThreshold I (qS I) :=
  Nat.sInf_mem (exists_isBaseThreshold I)

/-- `q(S)` is the least integer with its defining property. -/
theorem qS_le {q₀ : ℕ} (h : IsBaseThreshold I q₀) : qS I ≤ q₀ :=
  Nat.sInf_le h

/-- An integer has the defining property of `q(S)` exactly when it is at least `q(S)`. -/
theorem isBaseThreshold_iff_qS_le [IsNoetherianRing A] (q₀ : ℕ) :
    IsBaseThreshold I q₀ ↔ qS I ≤ q₀ :=
  ⟨qS_le I, (isBaseThreshold_qS I).mono I⟩

/-- **The cohomology of `𝒪_Y(q)` vanishes above a degree independent of `q`**, for `A`
Noetherian: there is a `D` with `Hⁱ(Y, 𝒪_Y(q)) = 0` for every `i > D` and every `q`. This is the
Čech bound of [Stacks, Tag 071L] for a finite affine open covering of the blowup `X`, on which the
cohomology of `𝒪_Y(q)` is computed (`exists_forall_subsingleton_blowupH`); `D` is that
covering's bound, not the fibre dimension `d(S)` of the source, which bounds the same vanishing
more sharply but which this library does not define. -/
theorem exists_forall_subsingleton_blowupHmod_thickeningTwist_one [IsNoetherianRing A] :
    ∃ D : ℕ, ∀ i q : ℕ, D < i → Subsingleton (blowupHmod I i (thickeningTwist I 1 q)) := by
  obtain ⟨D, hD⟩ := exists_forall_subsingleton_blowupH I
  exact ⟨D, fun i q hi => subsingleton_blowupHmod I i _ (hD _ inferInstance i hi)⟩

/-- **The source's literal definition of the property of `q(S)` at a degree bound `D`**: for every
`q ≥ q₀`, `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ D` and the canonical map
`Iᑫ/I^{q+1} → H⁰(Y, 𝒪_Y(q))` is an isomorphism. [Stacks, Tag 0GA6] takes `D = d(S)`. -/
def IsBaseThresholdUpTo (D q₀ : ℕ) : Prop :=
  (∀ i q : ℕ, 1 ≤ i → i ≤ D → q₀ ≤ q →
      Subsingleton (blowupHmod I i (thickeningTwist I 1 q))) ∧
    ∀ q : ℕ, q₀ ≤ q → Function.Bijective (cdivMod I 0 q)

/-- **`q(S)` is the least integer satisfying the source's literal definition**, at any degree
bound `D` above which the cohomology of every `𝒪_Y(q)` vanishes: `qS I` satisfies
`IsBaseThresholdUpTo I D`, and every `q₀` satisfying it is at least `qS I`. -/
theorem qS_isLeast_isBaseThresholdUpTo [IsNoetherianRing A] {D : ℕ}
    (hD : ∀ i q : ℕ, D < i → Subsingleton (blowupHmod I i (thickeningTwist I 1 q))) :
    IsLeast {q₀ | IsBaseThresholdUpTo I D q₀} (qS I) :=
  ⟨(isBaseThreshold_iff_of_vanishing_gt I D (qS I) hD).1 (isBaseThreshold_qS I),
    fun _ h => qS_le I ((isBaseThreshold_iff_of_vanishing_gt I D _ hD).2 h)⟩

/-- **`q(S)` is the source's `q(S)`**: there is a degree bound `D` above which the cohomology of
every `𝒪_Y(q)` vanishes, and at any such `D`, `qS I` is the least `q₀ ≥ 0` such that for all
`q ≥ q₀` one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ D` and `H⁰(Y, 𝒪_Y(q)) = Iᑫ/I^{q+1}`. -/
theorem exists_qS_isLeast_isBaseThresholdUpTo [IsNoetherianRing A] :
    ∃ D : ℕ, (∀ i q : ℕ, D < i → Subsingleton (blowupHmod I i (thickeningTwist I 1 q))) ∧
      IsLeast {q₀ | IsBaseThresholdUpTo I D q₀} (qS I) := by
  obtain ⟨D, hD⟩ := exists_forall_subsingleton_blowupHmod_thickeningTwist_one I
  exact ⟨D, hD, qS_isLeast_isBaseThresholdUpTo I hD⟩

/-! ### The witness -/

/-- **A witness for `Stacks.LocalCohomology.UniformityIII.Situation`, built from the blowup at a
given threshold**, for a Noetherian ring `A`, any ideal `I ⊆ A` and any `q₀` with the defining
property of `q(S)`: the Situation of [Stacks, Tag 0GA6] holds on the blowup of `Spec A` in `I`
with that `q₀`.

The cohomology modules are the blowup's own, `blowupHmod`; the canonical maps are
`Stacks.LocalCohomology.UniformityIII.thickeningSections` and
`Stacks.LocalCohomology.UniformityIII.ambientSections` read into `H⁰`; the long exact sequences
are those of `blowupDeltaMod` at the two short exact sequences; and the properties are the
blowup geometry — `exists_forall_subsingleton_blowupH` for `d`, the hypothesis `h` for the two
properties of `q₀`, `amb_serre` and `Stacks.Blowup.exists_forall_bijective_ambientSections` for
Serre's two theorems. Only the fields `q₀`, `base_vanishing` and `base_sections` depend on
`q₀`. -/
def blowupSituationOf [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    Situation A I where
  d := (exists_forall_subsingleton_blowupH I).choose
  q₀ := q₀
  Hdiv n i q := blowupHmod I i (thickeningTwist I n q)
  Hamb i q := blowupHmod I i (blowupTwist I q)
  cdiv n q := match n with
    | 0 => 0
    | m + 1 => cdivMod I m q
  camb q := ambientSectionsMod I q
  divα n i q := (blowupHmodMap I i (divα I n q)).hom
  divβ n i q := (blowupHmodMap I i (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)).hom
  divδ n i q := ((blowupDeltaMod I).δ (shortExact_divα I n q) i).hom
  div_exact_mid n i q _ := exact_blowupHmodMap_divα I n i q
  div_exact_right n i q _ := exact_blowupHmodMap_divα_δ I n i q
  div_injective n q _ := injective_blowupHmodMap_divα I n q
  div_sq_left n q hn x := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      change blowupHmodMap I 0 (divα I (m + 1) q) (cdivMod I m (q + 1) _) = cdivMod I (m + 1) q _
      rw [cdivMod_mk, ← blowupΓmodToH0_naturality,
        blowupΓMap_divα_thickeningSections I (m + 1) q z]
      rw [show powShift I q (m + 1) (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk ⟨(z : A), Ideal.pow_le_pow_right (Nat.le_succ q) z.2⟩ from
        powShift_mk I q (m + 1) z, cdivMod_mk]
  div_sq_right n q hn x := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      change blowupHmodMap I 0 (thickeningTwistRestrict I (Nat.le_add_left 1 (m + 1)) q)
          (cdivMod I (m + 1) q _) = cdivMod I 0 q _
      rw [cdivMod_mk, ← blowupΓmodToH0_naturality,
        blowupΓMap_thickeningTwistRestrict_thickeningSections I
          (Nat.le_add_left 1 (m + 1)) q z]
      rw [show powTrunc I q (m + 1) (Submodule.Quotient.mk z) = Submodule.Quotient.mk z from
        powTrunc_mk I q (m + 1) z, cdivMod_mk]
  base_vanishing i q hi _ hq := h.1 i q hi hq
  base_sections q hq := by
    change Function.Bijective (cdivMod I 0 q)
    exact h.2 q hq
  div_vanishing_gt n i q hi := subsingleton_blowupHmod I i (thickeningTwist I n q)
    ((exists_forall_subsingleton_blowupH I).choose_spec (thickeningTwist I n q) inferInstance i hi)
  ambα i q := (blowupHmodMap I i (ambientTwistMap I q)).hom
  ambβ i q := (blowupHmodMap I i (thickeningTwistProj I 1 q)).hom
  ambδ i q := ((blowupDeltaMod I).δ (shortExact_ambientTwistMap I q) i).hom
  amb_exact_mid i q := exact_blowupHmodMap_ambientTwistMap I i q
  amb_exact_right i q := exact_blowupHmodMap_ambientTwistMap_δ I i q
  amb_injective q := injective_blowupHmodMap_ambientTwistMap I q
  amb_sq_left q x := by
    change blowupHmodMap I 0 (ambientTwistMap I q) (ambientSectionsMod I (q + 1) x) = _
    rw [ambientSectionsMod_apply, ← blowupΓmodToH0_naturality,
      blowupΓMap_ambientTwistMap_ambientSections I q x]
    rfl
  amb_sq_right q x := by
    change blowupHmodMap I 0 (thickeningTwistProj I 1 q) (ambientSectionsMod I q x) =
      cdivMod I 0 q _
    rw [ambientSectionsMod_apply, ← blowupΓmodToH0_naturality,
      blowupΓMap_thickeningTwistProj_ambientSections I q x]
    exact (cdivMod_mk I 0 q x).symm
  amb_vanishing_gt i q hi := subsingleton_blowupHmod I i (blowupTwist I q)
    ((exists_forall_subsingleton_blowupH I).choose_spec (blowupTwist I q) inferInstance i hi)
  amb_serre i hi := by
    obtain ⟨N, hN⟩ := amb_serre I i hi
    exact ⟨N, fun q hq => subsingleton_blowupHmod I i (blowupTwist I q) (hN q hq)⟩
  amb_serre_sections := by
    obtain ⟨N, hN⟩ := Stacks.Blowup.exists_forall_bijective_ambientSections I
    refine ⟨N, fun q hq => ?_⟩
    show Function.Bijective (ambientSectionsMod I q)
    have h : (ambientSectionsMod I q : (I ^ q : Ideal A) → blowupHmod I 0 (blowupTwist I q)) =
        (fun z => blowupΓmodToH0 I (blowupTwist I q) z) ∘ (ambientSections I q) := rfl
    rw [h]
    exact Function.Bijective.comp (bijective_blowupΓmodToH0 I (blowupTwist I q)) (hN q hq)

/-- **The witness at `q₀ = q(S)`**: `blowupSituationOf` at the integer `qS I`, for a Noetherian
ring `A` and any ideal `I ⊆ A`. Its field `q₀` is `q(S)` on the nose (`blowupSituation_q₀`). -/
def blowupSituation [IsNoetherianRing A] : Situation A I :=
  blowupSituationOf I (qS I) (isBaseThreshold_qS I)

/-! ### The witness's fields are the blowup's cohomology -/

/-- The witness's threshold is `q(S)`. -/
theorem blowupSituation_q₀ [IsNoetherianRing A] : (blowupSituation I).q₀ = qS I :=
  rfl

/-- The witness's threshold is the one it was built at. -/
theorem blowupSituationOf_q₀ [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    (blowupSituationOf I q₀ h).q₀ = q₀ :=
  rfl

/-- The witness's `Hdiv n i q` is `Hⁱ(X, 𝒪_{Yₙ}(q))`. -/
theorem blowupSituationOf_Hdiv [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀)
    (n i q : ℕ) :
    (blowupSituationOf I q₀ h).Hdiv n i q = blowupHmod I i (thickeningTwist I n q) :=
  rfl

/-- The witness's `Hamb i q` is `Hⁱ(X, 𝒪_X(q))`. -/
theorem blowupSituationOf_Hamb [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀)
    (i q : ℕ) :
    (blowupSituationOf I q₀ h).Hamb i q = blowupHmod I i (blowupTwist I q) :=
  rfl

/-- The witness's `cdiv (n+1) q` is the canonical map of
`Stacks.LocalCohomology.UniformityIII.thickeningSections` read into `H⁰`. -/
theorem blowupSituationOf_cdiv_mk [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀)
    (n q : ℕ) (x : (I ^ q : Ideal A)) :
    (blowupSituationOf I q₀ h).cdiv (n + 1) q (Submodule.Quotient.mk x) =
      blowupΓmodToH0 I (thickeningTwist I (n + 1) q) (thickeningSections I (n + 1) q x) :=
  cdivMod_mk I n q x

/-- The witness's `camb q` is the canonical map of
`Stacks.LocalCohomology.UniformityIII.ambientSections` read into `H⁰`. -/
theorem blowupSituationOf_camb [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀)
    (q : ℕ) (x : (I ^ q : Ideal A)) :
    (blowupSituationOf I q₀ h).camb q x =
      blowupΓmodToH0 I (blowupTwist I q) (ambientSections I q x) :=
  rfl

/-! ### The four clauses of Tag 0GA7 at the blowup

The four theorems of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/BoundQAndD.lean` are stated
about an abstract `Stacks.LocalCohomology.UniformityIII.Situation`. Read at
`blowupSituationOf I q₀ h` they are the four clauses of [Stacks, Tag 0GA7] for the blowup, at
every `q₀` with the defining property of `q(S)`; the four declarations here are those
instantiations, with the fields replaced by the blowup's own cohomology.

The tag is registered once, on `Stacks.LocalCohomology.UniformityIII.blowupHmod_of_qS_le`, which
states all four clauses at `q₀ = q(S)` itself. -/

/-- **Tag 0GA7(1) at the blowup**: `Hⁱ(X, 𝒪_{Yₙ}(q)) = 0` for `n ≥ 1`, `i ≥ 1` and `q ≥ q₀`,
for every `q₀` with the defining property of `q(S)`. -/
theorem subsingleton_blowupHmod_thickeningTwist_of_le [IsNoetherianRing A] {q₀ n i q : ℕ}
    (h : IsBaseThreshold I q₀) (hn : 1 ≤ n) (hi : 1 ≤ i) (hq : q₀ ≤ q) :
    Subsingleton (blowupHmod I i (thickeningTwist I n q)) :=
  (blowupSituationOf I q₀ h).subsingleton_Hdiv hn hi hq

/-- **Tag 0GA7(2) at the blowup**: `Iᑫ/I^{q+n+1} → H⁰(X, 𝒪_{Y_{n+1}}(q))` is bijective for
`q ≥ q₀`, for every `q₀` with the defining property of `q(S)`. -/
theorem bijective_cdivMod_of_le [IsNoetherianRing A] {q₀ n q : ℕ} (h : IsBaseThreshold I q₀)
    (hq : q₀ ≤ q) :
    Function.Bijective (cdivMod I n q) :=
  (blowupSituationOf I q₀ h).bijective_cdiv (Nat.le_add_left 1 n) hq

/-- **Tag 0GA7(3) at the blowup**: `Hⁱ(X, 𝒪_X(q)) = 0` for `i ≥ 1` and `q ≥ q₀`, for every `q₀`
with the defining property of `q(S)`. -/
theorem subsingleton_blowupHmod_blowupTwist_of_le [IsNoetherianRing A] {q₀ i q : ℕ}
    (h : IsBaseThreshold I q₀) (hi : 1 ≤ i) (hq : q₀ ≤ q) :
    Subsingleton (blowupHmod I i (blowupTwist I q)) :=
  (blowupSituationOf I q₀ h).subsingleton_Hamb hi hq

/-- **Tag 0GA7(4) at the blowup**: `Iᑫ → H⁰(X, 𝒪_X(q))` is bijective for `q ≥ q₀`, for every `q₀`
with the defining property of `q(S)`. -/
theorem bijective_ambientSectionsMod_of_le [IsNoetherianRing A] {q₀ q : ℕ}
    (h : IsBaseThreshold I q₀) (hq : q₀ ≤ q) :
    Function.Bijective (ambientSectionsMod I q) :=
  (blowupSituationOf I q₀ h).bijective_camb hq

/-- **All four clauses of [Stacks, Tag 0GA7] at every `q₀` with the defining property of
`q(S)`**, for the `A`-module-valued cohomology of the blowup and `A` Noetherian. By
`isBaseThreshold_iff_qS_le` these are exactly the `q₀ ≥ q(S)`, so this is
`blowupHmod_of_qS_le` read at a larger threshold. -/
theorem blowupHmod_of_isBaseThreshold [IsNoetherianRing A] {q₀ : ℕ} (h : IsBaseThreshold I q₀) :
    (∀ n i q : ℕ, 1 ≤ n → 1 ≤ i → q₀ ≤ q →
        Subsingleton (blowupHmod I i (thickeningTwist I n q))) ∧
      (∀ n q : ℕ, q₀ ≤ q → Function.Bijective (cdivMod I n q)) ∧
      (∀ i q : ℕ, 1 ≤ i → q₀ ≤ q → Subsingleton (blowupHmod I i (blowupTwist I q))) ∧
      (∀ q : ℕ, q₀ ≤ q → Function.Bijective (ambientSectionsMod I q)) :=
  ⟨fun _ _ _ hn hi hq => subsingleton_blowupHmod_thickeningTwist_of_le I h hn hi hq,
    fun _ _ hq => bijective_cdivMod_of_le I h hq,
    fun _ _ hi hq => subsingleton_blowupHmod_blowupTwist_of_le I h hi hq,
    fun _ hq => bijective_ambientSectionsMod_of_le I h hq⟩

/-- **[Stacks, Tag 0GA7]**: with `q₀ = q(S)` (`qS I`, the least integer such that for all
`q ≥ q₀` one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for `i ≥ 1` and `H⁰(Y, 𝒪_Y(q)) = Iᑫ/I^{q+1}`), for a
Noetherian ring `A` and any ideal `I`, on the blowup `X` of `Spec A` in `I`:

1. for `n ≥ 1`, `q ≥ q₀` and `i > 0`, `Hⁱ(X, 𝒪_{Yₙ}(q)) = 0`;
2. for `n ≥ 1` and `q ≥ q₀`, the canonical map `Iᑫ/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))` is an
   isomorphism — stated as the bijectivity of `cdivMod I m q`, whose source is `Iᑫ/I^{q+m+1}`
   and whose target is `H⁰(X, 𝒪_{Y_{m+1}}(q))`, for every `m`, i.e. at `n = m + 1`;
3. for `q ≥ q₀` and `i > 0`, `Hⁱ(X, 𝒪_X(q)) = 0`;
4. for `q ≥ q₀`, the canonical map `Iᑫ → H⁰(X, 𝒪_X(q))` is an isomorphism.

The cohomology is `A`-module-valued, the source's identifications being isomorphisms of
`A`-modules. The integer `d = d(S)` the tag names enters only through the definition of `q(S)`,
where it bounds the degrees in which vanishing is asked; see `IsBaseThreshold`,
`isBaseThreshold_iff_of_vanishing_gt` and `exists_qS_isLeast_isBaseThresholdUpTo`. -/
@[stacks 0GA7]
theorem blowupHmod_of_qS_le [IsNoetherianRing A] :
    (∀ n i q : ℕ, 1 ≤ n → 1 ≤ i → qS I ≤ q →
        Subsingleton (blowupHmod I i (thickeningTwist I n q))) ∧
      (∀ n q : ℕ, qS I ≤ q → Function.Bijective (cdivMod I n q)) ∧
      (∀ i q : ℕ, 1 ≤ i → qS I ≤ q → Subsingleton (blowupHmod I i (blowupTwist I q))) ∧
      (∀ q : ℕ, qS I ≤ q → Function.Bijective (ambientSectionsMod I q)) :=
  blowupHmod_of_isBaseThreshold I (isBaseThreshold_qS I)

/-- **Some threshold past which all four clauses of [Stacks, Tag 0GA7] hold.** This existential
is weaker than the tag: it forgets which threshold works, and the tag's content is that `q(S)`,
a threshold read off the exceptional divisor `Y` alone, works for every thickening `Yₙ` and for
`X` itself. That statement is `blowupHmod_of_qS_le`, from which this follows at `q₀ = q(S)`. -/
theorem exists_threshold_forall_blowupHmod [IsNoetherianRing A] :
    ∃ q₀ : ℕ,
      (∀ n i q : ℕ, 1 ≤ n → 1 ≤ i → q₀ ≤ q →
        Subsingleton (blowupHmod I i (thickeningTwist I n q))) ∧
      (∀ n q : ℕ, q₀ ≤ q → Function.Bijective (cdivMod I n q)) ∧
      (∀ i q : ℕ, 1 ≤ i → q₀ ≤ q → Subsingleton (blowupHmod I i (blowupTwist I q))) ∧
      (∀ q : ℕ, q₀ ≤ q → Function.Bijective (ambientSectionsMod I q)) :=
  ⟨qS I, blowupHmod_of_qS_le I⟩

end Stacks.LocalCohomology.UniformityIII

end
