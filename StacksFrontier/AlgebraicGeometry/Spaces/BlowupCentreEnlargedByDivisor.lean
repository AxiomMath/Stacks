module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum

/-!
# Enlarging the centre of a blowup by an effective Cartier divisor

Let `S` be a scheme, let `𝔅` be an algebraic space over `S`, let `Z ⊆ 𝔅` be a closed subspace
and let `D ⊆ 𝔅` be an effective Cartier divisor.  Let `Z' = Z + D` be the closed subspace cut
out by the product `𝓘_Z 𝓘_D` of the two defining ideals, Stacks 083U.  Stacks 0867 part (1)
says that the blowup of `𝔅` in `Z'` is the blowup of `𝔅` in `Z`.

## Main results

* `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces` is Stacks 0867, part (1), from the
  two inputs `h0809` and `h083V` described below: a morphism which is the blowup of `𝔅` in `Z`
  is also the blowup of `𝔅` in `Z + D`.
* `AlgebraicGeometry.Space.exists_iso_blowup_sumClosedSubspaces` is the source's phrasing of
  the same statement: every blowup of `𝔅` in `Z + D` is isomorphic over `𝔅` to the blowup of
  `𝔅` in `Z`.
* `CategoryTheory.ObjectProperty.isTerminal_of_le`: a terminal object of a full subcategory
  which lies in a smaller full subcategory is terminal there too.

## How the statement is said here

The blowup is named by the universal property of Stacks 085U,
`AlgebraicGeometry.Space.IsBlowupAlong Z b`, which says that `b : B' ⟶ 𝔅` is a terminal object
of the category `𝒞_Z` of algebraic spaces over `𝔅` on which the inverse image of `Z` is an
effective Cartier divisor.  Asserting `IsBlowupAlong (Z + D) b` therefore says that `b` is the
blowup of `𝔅` in `Z + D`, which is the source's "the blowup of `𝔅` in `Z'` is isomorphic to
`B' ⟶ 𝔅`"; that reading is `AlgebraicGeometry.Space.exists_iso_blowup_sumClosedSubspaces`.

Read through the universal property the content of part (1) is that the two categories
`𝒞_{Z+D}` and `𝒞_Z` have the same terminal objects.  Since `𝒞_{Z+D} ⊆ 𝒞_Z` and `b` lies in
the smaller one, terminality in the larger one gives terminality in the smaller, which is
`CategoryTheory.ObjectProperty.isTerminal_of_le`.

## The two inputs

The statements here take two facts about effective Cartier divisors as hypotheses, so that this
file needs few imports.  Neither mentions the blowup's universal property.

* `h0809` is that the inverse image of `D` along `b` is an effective Cartier divisor on `B'`,
  Stacks 085X, the algebraic-space analogue of the scheme-level Stacks 0809; it is
  `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined_of_isEffectiveCartierDivisor`.
* `h083V` is that the inverse image of `Z + D` along a morphism is an effective Cartier divisor
  exactly when those of `Z` and of `D` are; it is
  `AlgebraicGeometry.Space.isPullbackDefined_sumClosedSubspaces_iff`.

With both discharged, Stacks 0867 — part (1), and part (2) on strict transforms — is
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_and_strictTransformSheaf_eq` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupCentreEnlargedByDivisorConstructed.lean`.

## References

* [Stacks Project, Tag 0867](https://stacks.math.columbia.edu/tag/0867)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083V](https://stacks.math.columbia.edu/tag/083V)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe v u

/-- **A terminal object of a full subcategory is terminal in every smaller full subcategory it
belongs to.**  Morphisms of a full subcategory are morphisms of the ambient category, so the
unique morphism into the object exists and is unique in the smaller subcategory as well. -/
def isTerminal_of_le {C : Type u} [Category.{v} C] {P Q : ObjectProperty C}
    (hQP : ∀ Y : C, Q Y → P Y) {X : C} (hPX : P X) (hQX : Q X)
    (h : IsTerminal (⟨X, hPX⟩ : P.FullSubcategory)) :
    IsTerminal (⟨X, hQX⟩ : Q.FullSubcategory) :=
  IsTerminal.ofUniqueHom
    (fun Y => homMk (h.from ⟨Y.obj, hQP Y.obj Y.property⟩).hom)
    fun Y m => by
      have key : m.hom = (h.from ⟨Y.obj, hQP Y.obj Y.property⟩).hom :=
        congrArg InducedCategory.Hom.hom (h.hom_ext
          (homMk (X := (⟨Y.obj, hQP Y.obj Y.property⟩ : P.FullSubcategory)) m.hom)
          (h.from ⟨Y.obj, hQP Y.obj Y.property⟩))
      exact hom_ext Q key

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0867, part (1).** Let `Z ⊆ 𝔅` and `D ⊆ 𝔅` be closed subspaces of an algebraic
space over `S` with `D` an effective Cartier divisor, and let `Z + D` be the closed subspace cut
out by the product of their defining ideals.  A morphism `b : B' ⟶ 𝔅` which is the blowup of
`𝔅` in `Z` is also the blowup of `𝔅` in `Z + D`.

This form takes as hypotheses that the inverse image of `D` along `b` is an effective Cartier
divisor (Stacks 085X, the algebraic-space counterpart of Stacks 0809), and that the inverse
image of `Z + D` along a morphism is an effective Cartier divisor exactly when those of `Z` and
of `D` are (Stacks 083V for algebraic spaces, and its converse).  Both are proved in the
library, and the statement without them is
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor`; the
form with hypotheses is kept because it needs fewer imports. -/
theorem isBlowupAlong_sumClosedSubspaces {𝔅 B' : AlgebraicSpaces B S hS}
    (Z D : ClosedSubspaces B S hS 𝔅.1)
    (_hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b)
    (h0809 : IsPullbackDefined B S hS b D)
    (h083V : ∀ {Y : AlgebraicSpaces B S hS} (g : Y ⟶ 𝔅),
      IsPullbackDefined B S hS g (sumClosedSubspaces B S hS 𝔅 Z D) ↔
        IsPullbackDefined B S hS g Z ∧ IsPullbackDefined B S hS g D) :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS 𝔅 Z D) b := by
  obtain ⟨hcart, ⟨ht⟩⟩ := hb
  exact ⟨(h083V b).2 ⟨hcart, h0809⟩,
    ⟨ObjectProperty.isTerminal_of_le (fun Y hY => ((h083V Y.hom).1 hY).1) hcart _ ht⟩⟩

/-- **Stacks 0867, part (1), in the source's phrasing.**  Every blowup of `𝔅` in `Z + D` is
isomorphic over `𝔅` to a blowup `b : B' ⟶ 𝔅` of `𝔅` in `Z`.

Blowups in a fixed centre are isomorphic over the base,
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`, so this follows from
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces`. -/
theorem exists_iso_blowup_sumClosedSubspaces {𝔅 B' : AlgebraicSpaces B S hS}
    (Z D : ClosedSubspaces B S hS 𝔅.1)
    (hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b)
    (h0809 : IsPullbackDefined B S hS b D)
    (h083V : ∀ {Y : AlgebraicSpaces B S hS} (g : Y ⟶ 𝔅),
      IsPullbackDefined B S hS g (sumClosedSubspaces B S hS 𝔅 Z D) ↔
        IsPullbackDefined B S hS g Z ∧ IsPullbackDefined B S hS g D) :
    ∀ (B'' : AlgebraicSpaces B S hS) (b'' : B'' ⟶ 𝔅),
      IsBlowupAlong B S hS (sumClosedSubspaces B S hS 𝔅 Z D) b'' →
        ∃ e : B' ≅ B'', e.hom ≫ b'' = b :=
  fun _ _ hb'' =>
    (isBlowupAlong_sumClosedSubspaces B S hS Z D hD hb h0809 h083V).exists_iso hb''

end AlgebraicGeometry.Space

end
