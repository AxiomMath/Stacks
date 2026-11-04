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

* `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces` is **Stacks 0867, part (1)**: a
  morphism which is the blowup of `𝔅` in `Z` is also the blowup of `𝔅` in `Z + D`.
* `AlgebraicGeometry.Space.exists_iso_blowup_sumClosedSubspaces` is the source's phrasing of
  the same statement: every blowup of `𝔅` in `Z + D` is isomorphic over `𝔅` to the blowup of
  `𝔅` in `Z`.
* `CategoryTheory.ObjectProperty.isTerminal_of_le`: a terminal object of a full subcategory
  which lies in a smaller full subcategory is terminal there too.

## How the statement is said here

The library has no construction of the blowup of an algebraic space; what it has is the
universal property of Stacks 085U, `AlgebraicGeometry.Space.IsBlowupAlong Z b`, which says
that `b : B' ⟶ 𝔅` is a terminal object of the category `𝒞_Z` of algebraic spaces over `𝔅` on
which the inverse image of `Z` is an effective Cartier divisor.  Asserting
`IsBlowupAlong (Z + D) b` therefore says both that the blowup of `𝔅` in `Z + D` exists and
that it is `b`, which is the source's "the blowup of `𝔅` in `Z'` is isomorphic to `B' ⟶ 𝔅`";
that reading is `AlgebraicGeometry.Space.exists_iso_blowup_sumClosedSubspaces`.

Read through the universal property the content of part (1) is that the two categories
`𝒞_{Z+D}` and `𝒞_Z` have the same terminal objects.  Since `𝒞_{Z+D} ⊆ 𝒞_Z` and `b` lies in
the smaller one, terminality in the larger one gives terminality in the smaller, which is
`CategoryTheory.ObjectProperty.isTerminal_of_le`.

## What is granted

Two inputs about effective Cartier divisors are carried as hypotheses, because the library does
not have them for algebraic spaces.  Both are strictly weaker than the conclusion: neither
mentions the blowup's universal property.

* `h0809` is that the inverse image of `D` along `b` is an effective Cartier divisor on `B'`,
  the algebraic-space analogue of the scheme-level Stacks 0809 used at this point of the
  source's proof (`AlgebraicGeometry.isPullbackDefined_blowUpToBase` in
  `StacksFrontier/AlgebraicGeometry/Blowup/Transform/RegularPullback.lean`).
* `h083V` is that the inverse image of `Z + D` along a morphism is an effective Cartier divisor
  exactly when those of `Z` and of `D` are — one direction is the algebraic-space analogue of
  Stacks 083V, the other the observation that a factor of an invertible ideal product is
  invertible.  Both directions compare the defining ideal of `Z + D`, which
  `AlgebraicGeometry.Space.sumClosedSubspaces` describes on the étale scheme charts, with
  invertibility on the small étale site of the source, and that comparison is Stacks 083C,
  recorded as missing in
  `StacksFrontier/AlgebraicGeometry/Spaces/EffectiveCartierEtaleCharts.lean`: it rests on the
  identification of modules on the small étale site of a scheme with modules on the scheme
  (Stacks 03DX(2) and 03LX) and on the descent clause of Stacks 0B8M.

The source's hypothesis that `D` is an effective Cartier divisor is carried but not used again:
it is the hypothesis under which the two granted inputs hold.

## What is not proved

Part (2) of Stacks 0867 — that the strict transform of a quasi-coherent module with no nonzero
sections supported on `|f^{-1}D|` is the same for the centre `Z` and for the centre `Z + D` —
is not proved.  Over the blowup the two strict transforms are quotients of the same pullback by
the sections supported on `|pr^{-1}(b^{-1}Z)|` and on `|pr^{-1}(b^{-1}(Z + D))|`
(`AlgebraicGeometry.Space.strictTransformSheaf`), so the statement is the equality of those two
submodules of supported sections.  It needs the point set of `Z + D` to be the union of those
of `Z` and `D`, which again compares the chartwise product ideal with data on the small étale
site, and the algebraic-space analogue of
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`.

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

Granted as hypotheses: that the inverse image of `D` along `b` is an effective Cartier divisor
(Stacks 0809 for algebraic spaces), and that the inverse image of `Z + D` along a morphism is an
effective Cartier divisor exactly when those of `Z` and of `D` are (Stacks 083V for algebraic
spaces, and its converse).  See the module documentation. -/
@[stacks 0867 "part (1): granted, as the hypotheses h0809 and h083V, that the inverse image \
of D along the blowup is an effective Cartier divisor and that the inverse image of Z + D \
along a morphism is one exactly when those of Z and of D are"]
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
