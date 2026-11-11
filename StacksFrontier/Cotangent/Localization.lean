module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Cotangent.DerivedPushoutBaseChange
public import StacksFrontier.Cotangent.EtaleVanishing
public import StacksFrontier.Cotangent.Triangle.VanishingVertex
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# Localization and the cotangent complex

Let `A → B` be a ring map and let `S ⊆ A` and `T ⊆ B` be multiplicative subsets such that `S`
maps into `T`. **[Stacks, Tag 08SF]** asserts that then

`L_{T⁻¹B/S⁻¹A} = L_{B/A} ⊗^𝐋_B T⁻¹B`

in `D(T⁻¹B)`.

The two localizations are presented as an `S`-localization `A'` of `A` and a `T`-localization
`B'` of `B`, and the ring map `S⁻¹A → T⁻¹B` as an `A'`-algebra structure on `B'` compatible with
the `A`-algebra structures. That datum is not an extra assumption: it exists because `S` maps
into `T`, and it is unique, both of which `CommAlgCat.algebraMap_localization_eq_map` records by
identifying the structure map with `IsLocalization.map`.

## Main results

* `CommAlgCat.algebraMap_localization_eq_map`: the structure map `S⁻¹A → T⁻¹B` is the canonical
  one induced by `A → B`.
* `CommAlgCat.bijective_algebraMap_tensorProduct_localization`: a localization is an epimorphism
  of rings, in the form `T⁻¹B → T⁻¹B ⊗_B T⁻¹B` is bijective.
* `CommAlgCat.isZero_cotangentComplexDerived_localization`: `L_{T⁻¹B/B} = 0` in `D(T⁻¹B)`, which
  is item (3) of [Stacks, Tag 08R2].
* `CommAlgCat.nonempty_cotangentComplexDerived_iso_localizationBase`:
  `L_{T⁻¹B/A} = L_{T⁻¹B/S⁻¹A}` in `D(T⁻¹B)`, the conclusion [Stacks, Tag 08QZ] draws from the
  flatness of `A → S⁻¹A`.
* `CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization`: the isomorphism of
  [Stacks, Tag 08SF] from a given distinguished fundamental triangle of `A → B → T⁻¹B`. The
  lemma itself, with the triangle of Proposition 08QX supplied, is
  `CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization_unconditional` of
  `StacksFrontier.Cotangent.LocalizationUnconditional`.

## The proof

The source's two steps are taken, in the second of which [Stacks, Tag 08QQ] replaces
[Stacks, Tag 08QZ]:

* `L_{T⁻¹B/A} = L_{B/A} ⊗^𝐋_B T⁻¹B` by [Stacks, Tag 08R3] for the tower `A → B → T⁻¹B`, whose
  hypothesis `L_{T⁻¹B/B} = 0` holds because `B → T⁻¹B` is a flat epimorphism: a localization is
  flat, and the multiplication `T⁻¹B ⊗_B T⁻¹B → T⁻¹B` is bijective, so its right inverse
  `b ↦ b ⊗ 1` is bijective too, which is the epimorphism condition of item (2) of
  [Stacks, Tag 08R2];
* `L_{T⁻¹B/A} = L_{T⁻¹B/S⁻¹A}` by [Stacks, Tag 08QQ] applied to the square `A → S⁻¹A`,
  `T⁻¹B → T⁻¹B` with the identity on top. Its hypotheses hold without restriction on `A → B`:
  `S⁻¹A` is flat over `A`, which gives the Tor independence of `S⁻¹A` and `T⁻¹B` over `A`, and
  the unit `S⁻¹A ⊗_A T⁻¹B → T⁻¹B` is bijective because `S` maps into `T`, so that every element
  of `S` is already invertible in `T⁻¹B` and the square is a pushout. The base change of
  [Stacks, Tag 08QQ] is then taken along the identity of `T⁻¹B`, where it is the identity
  functor of `D(T⁻¹B)`.

## Implementation notes

**What is proved outright.** Both halves are proved here with no carried hypothesis:
`CommAlgCat.isZero_cotangentComplexDerived_localization`, the vanishing of `L_{T⁻¹B/B}`, and
`CommAlgCat.nonempty_cotangentComplexDerived_iso_localizationBase`, the identification
`L_{T⁻¹B/A} = L_{T⁻¹B/S⁻¹A}`. The latter is the conclusion of [Stacks, Tag 08QZ] in the case at
hand, obtained from [Stacks, Tag 08QQ] rather than from Tag 08QZ itself: the library's Tag 08QZ,
`CommAlgCat.midCotangentComplexHomologyIso`, is an isomorphism on each homology module and not an
isomorphism in the derived category, which is what the conclusion in `D(T⁻¹B)` requires.

**The fundamental triangle.** The distinguished triangle of Proposition 08QX for the tower
`A → B → T⁻¹B` is the hypothesis `hT` of the main theorem of this file, passed unchanged to
[Stacks, Tag 08R3], `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero`.
Proposition 08QX is proved in the library, as
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, which is downstream of this file;
`StacksFrontier.Cotangent.LocalizationUnconditional` supplies it. The other form of Tag 08R3 in
this library, `CommAlgCat.nonempty_derivedBaseChange_iso_cotangentComplexDerived_of_isZero_obj₃`,
carries no triangle but assumes `B ⟶ T⁻¹B` injective, which fails as soon as `T` contains a
zerodivisor, so it is of no use here.

**One universe.** [Stacks, Tag 08QQ] is formalized with its two base rings and its two algebras
in a single universe, so all four rings are taken in `Type u`.

## References

* [Stacks Project, Tag 08SF](https://stacks.math.columbia.edu/tag/08SF)
* [Stacks Project, Tag 08R3](https://stacks.math.columbia.edu/tag/08R3), the vanishing third
  vertex.
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the displayed triangle.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), that it is
  distinguished.
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ), base change along a
  derived pushout square.
* [Stacks Project, Tag 08QZ](https://stacks.math.columbia.edu/tag/08QZ), the source's second
  step.
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), items (2) and (3).
* [Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660), Tor independence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

section Localization

/-- **A localization is an epimorphism.** For a localization `B → T⁻¹B` the map
`b ↦ b ⊗ 1 : T⁻¹B → T⁻¹B ⊗_B T⁻¹B` is bijective: it is a right inverse of the multiplication
map, which is bijective for a localization. -/
theorem bijective_algebraMap_tensorProduct_localization (B : Type u) [CommRing B]
    (T : Submonoid B) (B' : Type u) [CommRing B'] [Algebra B B'] [IsLocalization T B'] :
    Function.Bijective (algebraMap B' (B' ⊗[B] B')) := by
  have hmul : Function.Bijective (LinearMap.mul' B B') :=
    IsLocalization.bijective_linearMap_mul' T B'
  have key : ∀ x : B', LinearMap.mul' B B' (algebraMap B' (B' ⊗[B] B') x) = x := by
    intro x
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp
  refine ⟨fun x y hxy => ?_, fun z => ⟨LinearMap.mul' B B' z, hmul.injective ?_⟩⟩
  · have h := congrArg (LinearMap.mul' B B') hxy
    rwa [key, key] at h
  · rw [key]

/-- **The cotangent complex of a localization vanishes.** `L_{T⁻¹B/B} = 0` in `D(T⁻¹B)`: a
localization is flat and an epimorphism, so item (2) of [Stacks, Tag 08R2] applies. This is item
(3) of that lemma. -/
theorem isZero_cotangentComplexDerived_localization (B : Type u) [CommRing B]
    (T : Submonoid B) (B' : Type u) [CommRing B'] [Algebra B B'] [IsLocalization T B'] :
    IsZero (cotangentComplexDerived.{u, u} B (CommAlgCat.of B B')) :=
  have : Module.Flat B B' := IsLocalization.flat B' T
  isZero_cotangentComplexDerived_of_flat_of_bijective B B'
    (bijective_algebraMap_tensorProduct_localization B T B')

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (S : Submonoid A) (T : Submonoid B)
  (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalization S A']
  (B' : Type u) [CommRing B'] [Algebra B B'] [IsLocalization T B']
  [Algebra A B'] [IsScalarTower A B B'] [Algebra A' B'] [IsScalarTower A A' B']

/-- **The structure map `S⁻¹A → T⁻¹B` is the canonical one.** If `S` maps into `T` then
`A → B` induces a map `S⁻¹A → T⁻¹B`, namely `IsLocalization.map`, and any `S⁻¹A`-algebra
structure on `T⁻¹B` compatible with the `A`-algebra structures is that one: two ring maps out of
a localization of `A` agreeing on `A` are equal. -/
theorem algebraMap_localization_eq_map (hST : ∀ s ∈ S, algebraMap A B s ∈ T) :
    algebraMap A' B' =
      IsLocalization.map (M := S) B' (algebraMap A B) (fun s hs => hST s hs) := by
  refine IsLocalization.ringHom_ext S ?_
  have h := IsLocalization.map_comp (M := S) (S := A') (Q := B')
    (g := algebraMap A B) (fun s hs => hST s hs)
  rw [h, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- **Localizing the base ring does not change the cotangent complex.**
`L_{T⁻¹B/A} = L_{T⁻¹B/S⁻¹A}` in `D(T⁻¹B)`, for `S` mapping into `T`.

This is the conclusion of [Stacks, Tag 08QZ] for the tower `A → S⁻¹A → T⁻¹B`, proved here from
[Stacks, Tag 08QQ] applied to the square `A → S⁻¹A`, `T⁻¹B → T⁻¹B` with the identity on top.
Tag 08QQ's two hypotheses hold: `S⁻¹A` is flat over `A`, hence Tor independent from `T⁻¹B` over
`A`; and `S⁻¹A ⊗_A T⁻¹B → T⁻¹B` is bijective because every element of `S` becomes invertible in
`T⁻¹B`, which makes the square a pushout. Its derived base change is taken along the identity of
`T⁻¹B` and is therefore the identity functor of `D(T⁻¹B)`. -/
theorem nonempty_cotangentComplexDerived_iso_localizationBase
    (hST : ∀ s ∈ S, algebraMap A B s ∈ T) :
    Nonempty (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B') ≅
      cotangentComplexDerived.{u, u} A' (CommAlgCat.of A' B')) := by
  have hunit : Algebra.algebraMapSubmonoid B' S ≤ IsUnit.submonoid B' := by
    rintro x ⟨s, hs, rfl⟩
    rw [IsScalarTower.algebraMap_apply A B B' s]
    exact IsLocalization.map_units B' (⟨algebraMap A B s, hST s hs⟩ : T)
  have : IsLocalization (Algebra.algebraMapSubmonoid B' S) B' :=
    IsLocalization.of_le_isUnit hunit
  have : Algebra.IsPushout A B' A' B' := Algebra.isPushout_of_isLocalization S A' B' B'
  have : Module.Flat A A' := IsLocalization.flat A' S
  exact ⟨(totalDerivedExtensionScalarsId B').app _ ≪≫
    derivedCotangentComplexBaseChangeIso (A' := A') (B := CommAlgCat.of A B')
      (B' := CommAlgCat.of A' B') (AlgHom.id A B') (torIndependent_of_flat A A' B')
      (bijective_baseChangeUnit_of_isPushout _ fun _ => rfl)⟩

/-- **Localization and the cotangent complex, from a given fundamental triangle.** Let `A → B`
be a ring map and let `S ⊆ A` and `T ⊆ B` be multiplicative subsets such that `S` maps into `T`.
For any distinguished triangle on the vertices of the display 92.7.0.1 of the tower
`A → B → T⁻¹B`,

`L_{T⁻¹B/S⁻¹A} = L_{B/A} ⊗^𝐋_B T⁻¹B`

in `D(T⁻¹B)`.

This file is upstream of Proposition 08QX, which supplies such a triangle,
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`; [Stacks, Tag 08SF] itself is
`CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization_unconditional` of
`StacksFrontier.Cotangent.LocalizationUnconditional`, which applies this theorem to that triangle.
The two remaining steps are proved here: `L_{T⁻¹B/B} = 0`, which is the vanishing third vertex
Tag 08R3 asks for, and `L_{T⁻¹B/A} = L_{T⁻¹B/S⁻¹A}`. -/
theorem nonempty_cotangentComplexDerivedBaseChange_iso_localization
    (hST : ∀ s ∈ S, algebraMap A B s ∈ T)
    {α : fundamentalVertex₁.{u, u} A B B' ⟶ fundamentalVertex₂.{u, u} A B'}
    {β : fundamentalVertex₂.{u, u} A B' ⟶ fundamentalVertex₃.{u, u} B B'}
    {γ : fundamentalVertex₃.{u, u} B B' ⟶ (fundamentalVertex₁.{u, u} A B B')⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} B'))) :
    Nonempty (cotangentComplexDerivedBaseChange.{u, u} A (CommAlgCat.of A B) B' ≅
      cotangentComplexDerived.{u, u} A' (CommAlgCat.of A' B')) := by
  obtain ⟨e₁⟩ := nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero.{u, u} A B B' hT
    (isZero_cotangentComplexDerived_localization B T B')
  obtain ⟨e₂⟩ := nonempty_cotangentComplexDerived_iso_localizationBase A B S T A' B' hST
  exact ⟨e₁ ≪≫ e₂⟩

end Localization

end CommAlgCat

end
