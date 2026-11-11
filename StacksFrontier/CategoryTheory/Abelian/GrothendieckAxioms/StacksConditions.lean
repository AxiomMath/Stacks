module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Subobject.Lattice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generators in the sense of the Stacks project

Grothendieck singled out abelian categories with special properties by the conditions AB3, AB4,
AB5 and their duals AB3\*, AB4\*, AB5\*, and called an abelian category with AB5 and a generator a
*Grothendieck abelian category*.

The exactness conditions are in Mathlib, and this file uses them:

* the existence of direct sums is `CategoryTheory.Limits.HasCoproducts`, and the existence of
  products is `CategoryTheory.Limits.HasProducts`;
* exactness of direct sums is `CategoryTheory.AB4OfSize`, and exactness of products is
  `CategoryTheory.AB4StarOfSize`;
* exactness of filtered colimits is `CategoryTheory.AB5OfSize`, and exactness of cofiltered limits
  is `CategoryTheory.AB5StarOfSize`;
* Grothendieck abelian categories are `CategoryTheory.IsGrothendieckAbelian`.

Mathlib's exactness classes take the existence of the (co)limits as an instance argument, while the
Stacks project's AB4, AB5, AB4\*, AB5\* include AB3 or AB3\*. This file states the six conditions
as propositions about `C` in the Stacks project's form, `Stacks.Injectives.AB3` to
`Stacks.Injectives.AB5Star`, and relates each to Mathlib's class.

Mathlib has no notion of a **generator** in the Stacks project's sense: an object `U` such that
for every `N ⊂ M` with `N ≠ M` some morphism `U ⟶ M` fails to factor through `N`. Mathlib instead
uses separators, `CategoryTheory.IsSeparator U`: morphisms out of `U` distinguish parallel pairs.
This file defines the generator condition, identifies it with `CategoryTheory.IsSeparator`, defines
a Grothendieck abelian category as one with AB5 and a generator, and shows that this is Mathlib's
`CategoryTheory.IsGrothendieckAbelian`.

## Universe conventions

The shapes of the filtered colimits of AB5 are taken in a universe `w`, the size parameter of
Mathlib's `CategoryTheory.AB5OfSize.{w, w}` and `CategoryTheory.IsGrothendieckAbelian.{w}`. The
Stacks project's categories are locally small, and accordingly the characterization
`Stacks.Injectives.isGrothendieckAbelian_iff_ab5_and_exists_isGenerator` is stated for `w` the hom
universe `v` of `C`: Mathlib's class carries the extra requirement `LocallySmall.{w} C`, which is
vacuous exactly when `w = v`, and which has no counterpart in the Stacks definition.

## Main definitions

* `Stacks.Injectives.AB3`, `Stacks.Injectives.AB4`, `Stacks.Injectives.AB5`: the conditions AB3,
  AB4, AB5.
* `Stacks.Injectives.AB3Star`, `Stacks.Injectives.AB4Star`, `Stacks.Injectives.AB5Star`: the dual
  conditions AB3\*, AB4\*, AB5\*.
* `Stacks.Injectives.IsGenerator`: the Stacks definition of a generator.
* `Stacks.Injectives.IsGrothendieckAbelianCategory`: AB5 and a generator.

## Main results

* `Stacks.Injectives.ab3_iff_hasColimitsOfSize`, `Stacks.Injectives.ab4_iff_ab4OfSize`,
  `Stacks.Injectives.ab5_iff` and their duals: the conditions in Mathlib's terms.
* `Stacks.Injectives.isGrothendieckAbelianCategory_iff`: the Stacks notion of a Grothendieck
  abelian category is Mathlib's `CategoryTheory.IsGrothendieckAbelian.{v}`.
* `Stacks.Injectives.isGenerator_iff_subobject`: the generator condition phrased with subobjects.
* `Stacks.Injectives.isGenerator_iff_isSeparator`: a generator is the same thing as a separator.
* `Stacks.Injectives.isGrothendieckAbelian_iff_ab5_and_exists_isGenerator`: an abelian category is
  a Grothendieck abelian category, in Mathlib's sense, if and only if it has AB5 and a generator.
* `Stacks.Injectives.hasProducts_of_isGrothendieckAbelian`: a Grothendieck abelian category has
  AB3\*, that is, it has products.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079B)
* [Stacks: a Grothendieck abelian category has AB3\*](https://stacks.math.columbia.edu/tag/07D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Generators -/

/-- An object `U` of `C` is a *generator* if for every `N ⊂ M` with `N ≠ M` there is a morphism
`U ⟶ M` which does not factor through `N`. A subobject `N ⊂ M` is given by a monomorphism
`i : N ⟶ M`, and `N ≠ M` says that `i` is not an isomorphism.

Mathlib has no name for this condition; it uses `CategoryTheory.IsSeparator` instead, with which
this agrees by `Stacks.Injectives.isGenerator_iff_isSeparator`. -/
@[stacks 079B "generator"]
def IsGenerator (U : C) : Prop :=
  ∀ ⦃N M : C⦄ (i : N ⟶ M), Mono i → ¬IsIso i → ∃ u : U ⟶ M, ∀ v : U ⟶ N, v ≫ i ≠ u

omit [Abelian C] in
/-- The definition of a generator, phrased with subobjects: `U` is a generator if and only if for
every object `M` and every subobject `N` of `M` other than `M` itself there is a morphism `U ⟶ M`
which does not factor through `N`. -/
@[stacks 079B "generator as a subobject condition"]
theorem isGenerator_iff_subobject (U : C) :
    IsGenerator U ↔ ∀ (M : C) (N : Subobject M), N ≠ ⊤ →
      ∃ u : U ⟶ M, ∀ v : U ⟶ (N : C), v ≫ N.arrow ≠ u := by
  constructor
  · intro hU M N hN
    exact hU N.arrow inferInstance fun h => hN ((Subobject.isIso_arrow_iff_eq_top N).1 h)
  · intro hU N M i hi hiso
    obtain ⟨u, hu⟩ := hU M (Subobject.mk i) fun h => hiso <| by
      have : IsIso (Subobject.mk i).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
      rw [← Subobject.underlyingIso_arrow i]
      infer_instance
    refine ⟨u, fun v hv => hu (v ≫ (Subobject.underlyingIso i).inv) ?_⟩
    rw [Category.assoc, Subobject.underlyingIso_arrow, hv]

/-- A generator in the sense of the Stacks project is the same thing as a separator in the sense of
Mathlib: morphisms out of `U` see every proper subobject if and only if they distinguish parallel
morphisms.

From left to right: if `f : X ⟶ Y` is killed by every morphism `U ⟶ X` then every such morphism
factors through `ker f`, which therefore cannot be a proper subobject of `X`, so `f = 0`. From
right to left: if `i : N ⟶ M` is a monomorphism through which every morphism `U ⟶ M` factors, then
every morphism `U ⟶ M` is killed by `coker i ≠ 0`, so `i` is an epimorphism and hence, `C` being
balanced, an isomorphism. -/
@[stacks 079B "generator is separator"]
theorem isGenerator_iff_isSeparator (U : C) : IsGenerator U ↔ IsSeparator U := by
  constructor
  · intro hU
    rw [Preadditive.isSeparator_iff]
    intro X Y f hf
    by_contra hne
    have hniso : ¬IsIso (kernel.ι f) := fun _ =>
      hne <| (cancel_epi (kernel.ι f)).1 (by simp [kernel.condition f])
    obtain ⟨u, hu⟩ := hU (kernel.ι f) inferInstance hniso
    exact hu (kernel.lift f u (hf u)) (by simp)
  · intro hU N M i hi hiso
    rw [Preadditive.isSeparator_iff] at hU
    by_contra! hcon
    have hπ : cokernel.π i = 0 := hU _ fun u => by
      obtain ⟨v, rfl⟩ := hcon u
      simp
    have : Epi i := Abelian.epi_of_cokernel_π_eq_zero i hπ
    exact hiso (isIso_of_mono_of_epi i)

/-! ### Grothendieck abelian categories -/

variable (C)

/-- An abelian category is a *Grothendieck abelian category* if it has AB5 and a generator. Both
sides are expressed with Mathlib's vocabulary: AB5 at size `v` is
`CategoryTheory.AB5OfSize.{v, v}`, and `CategoryTheory.IsGrothendieckAbelian.{v}` is Mathlib's
class.

The equivalence is stated at `w = v`, for `v` the hom universe of `C`, because Mathlib's class
carries the further requirement `LocallySmall.{w} C`, which has no counterpart in the Stacks
definition and is vacuous exactly for that choice of `w`. The hypothesis that filtered colimits of
size `v` exist is part of AB5 as the Stacks project states it, AB5 being AB3 together with
exactness of filtered colimits; in Mathlib it is the instance argument of
`CategoryTheory.AB5OfSize`, so it has to be assumed on both sides at once. -/
@[stacks 079B "Grothendieck abelian category"]
theorem isGrothendieckAbelian_iff_ab5_and_exists_isGenerator
    [HasFilteredColimitsOfSize.{v, v} C] :
    CategoryTheory.IsGrothendieckAbelian.{v} C ↔
      (CategoryTheory.AB5OfSize.{v, v} C ∧ ∃ U : C, IsGenerator U) := by
  constructor
  · intro h
    obtain ⟨U, hU⟩ := HasSeparator.hasSeparator (C := C)
    exact ⟨inferInstance, U, (isGenerator_iff_isSeparator U).2 hU⟩
  · rintro ⟨h5, U, hU⟩
    exact
      { locallySmall := inferInstance
        hasFilteredColimitsOfSize := inferInstance
        ab5OfSize := h5
        hasSeparator := ⟨U, (isGenerator_iff_isSeparator U).1 hU⟩ }

/-! ### The conditions AB3, AB4, AB5 and their duals

The direct sums, products, filtered colimits and cofiltered limits below are indexed by
categories of size `w`. In each condition the existence part (AB3, respectively AB3\*) is bundled
in, as in the Stacks project, so that each condition is a plain proposition about `C`; the
exactness parts are Mathlib's `CategoryTheory.AB4OfSize`, `CategoryTheory.AB5OfSize`,
`CategoryTheory.AB4StarOfSize` and `CategoryTheory.AB5StarOfSize`, in which "exact" means that the
colimit (respectively limit) functor preserves finite limits (respectively finite colimits); the
colimit functor is always right exact, and the limit functor always left exact, so this is
exactness of the functor. -/

/-- **AB3**: `C` has direct sums, i.e. coproducts indexed by every type in `Type w`. -/
@[stacks 079B "AB3"]
def AB3 : Prop := HasCoproducts.{w} C

/-- **AB4**: `C` has AB3 and direct sums are exact. -/
@[stacks 079B "AB4"]
def AB4 : Prop := ∃ _ : HasCoproducts.{w} C, CategoryTheory.AB4OfSize.{w} C

/-- **AB5**: `C` has AB3 and filtered colimits are exact. Filtered colimits exist as soon as AB3
holds, `C` having coequalizers
(`CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts`, [Stacks, Tag 002P]);
exactness is `CategoryTheory.AB5OfSize`. -/
@[stacks 079B "AB5"]
def AB5 : Prop :=
  ∃ _ : HasCoproducts.{w} C,
    haveI : HasColimitsOfSize.{w, w} C := has_colimits_of_hasCoequalizers_and_coproducts
    CategoryTheory.AB5OfSize.{w, w} C

/-- **AB3\***: `C` has products, indexed by every type in `Type w`. -/
@[stacks 079B "AB3*"]
def AB3Star : Prop := HasProducts.{w} C

/-- **AB4\***: `C` has AB3\* and products are exact. -/
@[stacks 079B "AB4*"]
def AB4Star : Prop := ∃ _ : HasProducts.{w} C, CategoryTheory.AB4StarOfSize.{w} C

/-- **AB5\***: `C` has AB3\* and cofiltered limits are exact. Cofiltered limits exist as soon as
AB3\* holds, `C` having equalizers
(`CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products`, [Stacks, Tag 002N]);
exactness is `CategoryTheory.AB5StarOfSize`. -/
@[stacks 079B "AB5*"]
def AB5Star : Prop :=
  ∃ _ : HasProducts.{w} C,
    haveI : HasLimitsOfSize.{w, w} C := has_limits_of_hasEqualizers_and_products
    CategoryTheory.AB5StarOfSize.{w, w} C

/-- AB3 is the existence of all colimits of size `w` ([Stacks, Tag 002P]). -/
@[stacks 079B "AB3 gives all colimits"]
theorem ab3_iff_hasColimitsOfSize : AB3.{w} C ↔ HasColimitsOfSize.{w, w} C :=
  ⟨fun h => haveI : HasCoproducts.{w} C := h
    has_colimits_of_hasCoequalizers_and_coproducts,
    fun h _J => haveI := h; inferInstance⟩

/-- AB3\* is the existence of all limits of size `w` ([Stacks, Tag 002N]). -/
@[stacks 079B "AB3* gives all limits"]
theorem ab3Star_iff_hasLimitsOfSize : AB3Star.{w} C ↔ HasLimitsOfSize.{w, w} C :=
  ⟨fun h => haveI : HasProducts.{w} C := h
    has_limits_of_hasEqualizers_and_products,
    fun h _J => haveI := h; inferInstance⟩

omit [Abelian C] in
/-- On a category with direct sums, AB4 is Mathlib's `CategoryTheory.AB4OfSize`. -/
@[stacks 079B "AB4 in Mathlib's terms"]
theorem ab4_iff_ab4OfSize [HasCoproducts.{w} C] : AB4.{w} C ↔ CategoryTheory.AB4OfSize.{w} C :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨inferInstance, h⟩⟩

/-- AB5 is AB3 together with Mathlib's `CategoryTheory.AB5OfSize`. -/
@[stacks 079B "AB5 in Mathlib's terms"]
theorem ab5_iff [HasFilteredColimitsOfSize.{w, w} C] :
    AB5.{w} C ↔ HasCoproducts.{w} C ∧ CategoryTheory.AB5OfSize.{w, w} C :=
  ⟨fun ⟨h3, h5⟩ => ⟨h3, h5⟩, fun ⟨h3, h5⟩ => ⟨h3, h5⟩⟩

omit [Abelian C] in
/-- On a category with products, AB4\* is Mathlib's `CategoryTheory.AB4StarOfSize`. -/
@[stacks 079B "AB4* in Mathlib's terms"]
theorem ab4Star_iff_ab4StarOfSize [HasProducts.{w} C] :
    AB4Star.{w} C ↔ CategoryTheory.AB4StarOfSize.{w} C :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨inferInstance, h⟩⟩

/-- AB5\* is AB3\* together with Mathlib's `CategoryTheory.AB5StarOfSize`. -/
@[stacks 079B "AB5* in Mathlib's terms"]
theorem ab5Star_iff [HasCofilteredLimitsOfSize.{w, w} C] :
    AB5Star.{w} C ↔ HasProducts.{w} C ∧ CategoryTheory.AB5StarOfSize.{w, w} C :=
  ⟨fun ⟨h3, h5⟩ => ⟨h3, h5⟩, fun ⟨h3, h5⟩ => ⟨h3, h5⟩⟩

/-- AB5 implies AB4: Mathlib's `CategoryTheory.AB4.of_AB5`. -/
theorem AB5.ab4 (h : AB5.{w} C) : AB4.{w} C := by
  obtain ⟨_, h5⟩ := h
  have : HasColimitsOfSize.{w, w} C := has_colimits_of_hasCoequalizers_and_coproducts
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  exact ⟨inferInstance, CategoryTheory.AB4.of_AB5 C⟩

/-! ### Grothendieck abelian categories in the sense of the Stacks project -/

/-- **Grothendieck abelian category**: `C` has AB5 and a generator. The direct sums and filtered
colimits of AB5 are indexed by sets in the hom universe `v` of `C`, the size at which the
Stacks project's (locally small) categories live. -/
@[stacks 079B "Grothendieck abelian category, Stacks definition"]
def IsGrothendieckAbelianCategory : Prop := AB5.{v} C ∧ ∃ U : C, IsGenerator U

/-- A category is a Grothendieck abelian category in the sense of the Stacks project, that is it
has AB5 and a generator, if and only if it is one in the sense of Mathlib,
`CategoryTheory.IsGrothendieckAbelian.{v}` (locally small, exact filtered colimits of size `v`,
a separator), with no further hypothesis. -/
@[stacks 079B "Grothendieck abelian category, agreement with Mathlib"]
theorem isGrothendieckAbelianCategory_iff :
    IsGrothendieckAbelianCategory C ↔ CategoryTheory.IsGrothendieckAbelian.{v} C := by
  constructor
  · rintro ⟨⟨_, h5⟩, hU⟩
    have : HasColimitsOfSize.{v, v} C := has_colimits_of_hasCoequalizers_and_coproducts
    exact (isGrothendieckAbelian_iff_ab5_and_exists_isGenerator C).2 ⟨h5, hU⟩
  · intro h
    have h' := (isGrothendieckAbelian_iff_ab5_and_exists_isGenerator C).1 h
    exact ⟨⟨inferInstance, h'.1⟩, h'.2⟩

/-- A Grothendieck abelian category has AB3\*, that is, it has products. Mathlib's name for AB3\*
is `CategoryTheory.Limits.HasProducts`, so there is nothing left to define here.

The Stacks project deduces this from its criterion for representability of a functor on a
Grothendieck abelian category: for a family `M_i` of objects the functor `F = ∏ h_{M_i}` commutes
with colimits, so it is representable, and the representing object is the product of the family.
Here we instead invoke `CategoryTheory.IsGrothendieckAbelian.hasLimits`, which gives all limits of
size `w` at once. -/
@[stacks 07D8, sga "4 V 0.1.1"]
theorem hasProducts_of_isGrothendieckAbelian [CategoryTheory.IsGrothendieckAbelian.{w} C] :
    HasProducts.{w} C := fun _ => inferInstance

end Stacks.Injectives

end
