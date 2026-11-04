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

**Almost all of this is already in Mathlib, and this file does not restate it.** Mathlib provides:

* AB3, the existence of direct sums, as `CategoryTheory.Limits.HasCoproducts`, and AB3\*, the
  existence of products, as `CategoryTheory.Limits.HasProducts`;
* AB4, exactness of direct sums, as `CategoryTheory.AB4OfSize` and its unbundled form
  `CategoryTheory.AB4`, and AB4\* as `CategoryTheory.AB4StarOfSize`;
* AB5, exactness of filtered colimits, as `CategoryTheory.AB5OfSize` and its unbundled form
  `CategoryTheory.AB5`, and AB5\* as `CategoryTheory.AB5StarOfSize`;
* Grothendieck abelian categories as `CategoryTheory.IsGrothendieckAbelian`.

Several of those declarations — `CategoryTheory.AB4`, `CategoryTheory.AB4StarOfSize`,
`CategoryTheory.AB5`, `CategoryTheory.AB5StarOfSize` and
`CategoryTheory.IsGrothendieckAbelian` — already carry the tag
[079B](https://stacks.math.columbia.edu/tag/079B) in Mathlib itself.

What is *not* in Mathlib is the Stacks project's notion of a **generator**: an object `U` such that
for every `N ⊂ M` with `N ≠ M` some morphism `U ⟶ M` fails to factor through `N`. Mathlib instead
uses separators, `CategoryTheory.IsSeparator U`: morphisms out of `U` distinguish parallel pairs.
This file supplies the missing vocabulary — the generator condition, its identification with
`CategoryTheory.IsSeparator`, and the characterization of Grothendieck abelian categories it
yields — and nothing else.

## Universe conventions

The shapes of the filtered colimits of AB5 are taken in a universe `w`, the size parameter of
Mathlib's `CategoryTheory.AB5OfSize.{w, w}` and `CategoryTheory.IsGrothendieckAbelian.{w}`. The
Stacks project's categories are locally small, and accordingly the characterization
`Stacks.Injectives.isGrothendieckAbelian_iff_ab5_and_exists_isGenerator` is stated for `w` the hom
universe `v` of `C`: Mathlib's class carries the extra requirement `LocallySmall.{w} C`, which is
vacuous exactly when `w = v`, and which has no counterpart in the Stacks definition.

## Main definitions

* `Stacks.Injectives.IsGenerator`: the Stacks definition of a generator.

## Main results

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
