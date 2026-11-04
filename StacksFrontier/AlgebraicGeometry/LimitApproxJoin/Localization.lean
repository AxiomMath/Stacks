module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The localization hypothesis of the one-affine-open step, from the qcqs lemma

Let `j : V ⟶ Y` be an open immersion of schemes with `V` quasi-compact and `Y` quasi-compact and
quasi-separated, and let `g : Γ(Y, ⊤)` be a global section whose standard open lies inside the
image of `j`.  Then the induced map on localizations `Γ(Y, ⊤)_g ⟶ Γ(V, ⊤)_{g|_V}` is bijective.

This is the hypothesis `hloc` of Tag 01Z9 as
`AlgebraicGeometry.isOpenImmersion_spec_fibreProduct_of_app_eq` states it, in the geometric
situation of step (ii) of the one-affine-open step of Tag 07RN: `Y` is the affine open being
added, `V` is its overlap with the part of the scheme already approximated, `j` is the inclusion
of that overlap, and the `g` are the finitely many elements of `Γ(Y, ⊤)` whose standard opens
were chosen inside the overlap and covering it.

## Main results

* `AlgebraicGeometry.isLocalization_away_of_eq_basicOpen`: the qcqs lemma, Tag 01P7, for an open
  merely *equal* to a basic open rather than spelled as one.  Mathlib has this for an affine
  scheme (`AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen`) and the qcqs lemma
  itself only in the spelled form; the proof is the same substitution.
* `AlgebraicGeometry.bijective_awayMap_appTop_of_basicOpen_le_opensRange`: the localization
  hypothesis of Tag 01Z9.

## Implementation notes

Tag 01P7 is applied twice, once on `Y` and once on `V`:

- on `Y` at `⊤`, giving that `Γ(Y, Y.basicOpen g)` is the localization of `Γ(Y, ⊤)` at `g`;
- on `V` at `⊤`, giving that `Γ(V, j⁻¹(Y.basicOpen g))` — which is the basic open of `V` cut
  out by the restriction of `g`, by `AlgebraicGeometry.Scheme.preimage_basicOpen_top` — is the
  localization of `Γ(V, ⊤)` at that restriction.

The two are the *same ring*, because the standard open lies inside the image of `j` and so
`j.app (Y.basicOpen g)` is an isomorphism (`AlgebraicGeometry.Scheme.Hom.isIso_app`).  That is
the whole geometric content; the rest is the elementwise reading of bijectivity supplied by
Mathlib's `Localization.awayMap_injective_iff` and `Localization.awayMap_surjective_iff`,
transported across the isomorphism through the naturality square of `j`.

The elementwise criteria are used rather than an isomorphism of localizations.  The hypothesis
of Tag 01Z9 is about `Localization.awayMap` of a bare ring map, so any comparison of
localizations would have to be made between two `Localization.Away` constructions whose algebra
structures over `Γ(Y, ⊤)` differ by a composite.  With the criteria, the only facts needed are
`IsLocalization.Away.surj` and `IsLocalization.Away.exists_of_eq` for the two instances above,
and the instances never have to be identified with each other.

The algebra structure on `Γ(V, j⁻¹(Y.basicOpen g))` over `Γ(V, ⊤)` is *not* found by instance
search: the open is a preimage, not syntactically a basic open, so Mathlib's
`AlgebraicGeometry.Scheme.algebra_section_section_basicOpen` does not apply.  It is introduced as
a local definition inside the proof, and the qcqs lemma is applied in the
`isLocalization_away_of_eq_basicOpen` form whose statement names that same structure.  Writing
the open as `V.basicOpen (j.appTop g)` instead would get the instance for free but would then
need the isomorphism `j.app (Y.basicOpen g)` transported along an equality of opens.

`AlgebraicGeometry.Scheme.Hom.appTop` is the component of `AlgebraicGeometry.Scheme.Hom.app` at
`⊤`, and the identification rests on `j⁻¹(⊤) = ⊤` holding definitionally.  The naturality square
of `j` therefore closes by `congrArg` on the morphism, with no rewriting; a `simpa` normalizes the
square to `True` and loses the equation that is wanted.

The two schemes and all the rings live in one universe.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The qcqs lemma for an open equal to a basic open.**  Tag 01P7 in the form that applies to
an open presented as something other than a basic open, with the algebra structure given by the
restriction along a chosen morphism to `⊤`. -/
lemma isLocalization_away_of_eq_basicOpen {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (r : Γ(X, ⊤)) {V : X.Opens} (i : V ⟶ ⊤) (e : V = X.basicOpen r) :
    @IsLocalization.Away _ _ r Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra := by
  subst e
  exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r

/-- **The localization hypothesis of Tag 01Z9, from the qcqs lemma applied twice.**  Let
`j : V ⟶ Y` be an open immersion with `V` quasi-compact and `Y` quasi-compact and
quasi-separated, and let `g : Γ(Y, ⊤)` have its standard open inside the image of `j`.  Then
`Γ(Y, ⊤)_g ⟶ Γ(V, ⊤)_{g|_V}` is bijective.

Tag 01P7 identifies both sides with the sections over `Y.basicOpen g`, which is an open of `Y`
inside the image of `j` and so has the same sections on either side. -/
lemma bijective_awayMap_appTop_of_basicOpen_le_opensRange {V Y : Scheme.{u}} (j : V ⟶ Y)
    [IsOpenImmersion j] [CompactSpace V] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : Γ(Y, ⊤)) (hg : Y.basicOpen g ≤ j.opensRange) :
    Function.Bijective (Localization.awayMap j.appTop.hom g) := by
  have hqsV : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated j
  have hiso : IsIso (j.app (Y.basicOpen g)) := j.isIso_app _ hg
  have instY : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ g
  let algV : Algebra Γ(V, ⊤) Γ(V, j ⁻¹ᵁ Y.basicOpen g) :=
    (V.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ Y.basicOpen g ≤ ⊤)).op).hom.toAlgebra
  have instV : IsLocalization.Away (j.appTop g) Γ(V, j ⁻¹ᵁ Y.basicOpen g) :=
    isLocalization_away_of_eq_basicOpen (X := V) (j.appTop g)
      (homOfLE (le_top : j ⁻¹ᵁ Y.basicOpen g ≤ ⊤)) (Scheme.preimage_basicOpen_top j g)
  have hsq : ∀ c : Γ(Y, ⊤),
      (j.app (Y.basicOpen g)) (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen g) c) =
        algebraMap Γ(V, ⊤) Γ(V, j ⁻¹ᵁ Y.basicOpen g) (j.appTop c) := fun c ↦
    congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(V, j ⁻¹ᵁ Y.basicOpen g) ↦ k.hom c)
      (j.naturality (homOfLE (le_top : Y.basicOpen g ≤ ⊤)).op)
  have hbij := (ConcreteCategory.isIso_iff_bijective (j.app (Y.basicOpen g))).mp hiso
  constructor
  · rw [Localization.awayMap_injective_iff]
    intro a ha
    have h0 : algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen g) a =
        algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen g) 0 := by
      refine hbij.1 ?_
      rw [hsq a, hsq 0, ha]
      simp
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq g h0
    exact ⟨n, by simpa using hn⟩
  · rw [Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨a₂, ha₂⟩ := hbij.2 (algebraMap Γ(V, ⊤) Γ(V, j ⁻¹ᵁ Y.basicOpen g) a)
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj (S := Γ(Y, Y.basicOpen g)) g a₂
    have h1 := congrArg (j.app (Y.basicOpen g)) hb
    rw [map_mul, ha₂, map_pow, hsq, hsq] at h1
    have key : algebraMap Γ(V, ⊤) Γ(V, j ⁻¹ᵁ Y.basicOpen g) (j.appTop g ^ m * a) =
        algebraMap Γ(V, ⊤) Γ(V, j ⁻¹ᵁ Y.basicOpen g) (j.appTop b) := by
      rw [map_mul, map_pow, mul_comm, h1]
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (j.appTop g) key
    refine ⟨g ^ n * b, n + m, ?_⟩
    rw [map_mul, map_pow, ← hn, pow_add]
    ring

end AlgebraicGeometry
