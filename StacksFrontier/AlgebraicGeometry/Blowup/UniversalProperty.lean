module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense

/-!
# The universal property of blowing up

Let `S` be a scheme and `Z ⊆ S` the closed subscheme cut out by a quasi-coherent ideal sheaf
`I`. Let `C` be the full subcategory of `Sch/S` consisting of those `Y ⟶ S` whose inverse
image of `Z` is an effective Cartier divisor on `Y`. Stacks tag 0806 says that the blowup
`b : S' ⟶ S` of `Z` in `S` is a final object of `C`.

The blowup itself is the relative `Proj` of the Rees algebra `⨁_{n ≥ 0} Iⁿ` (tag 01OG), which
is not yet available: the affine charts are
`StacksFrontier/AlgebraicGeometry/Blowup/Basic.lean` and the gluing datum is
`StacksFrontier/AlgebraicGeometry/Blowup/RelativeProjGluing.lean`, but no global blowup morphism
has been assembled from them. What this file supplies is the rest of tag 0806: the reduction
of finality in `C` to the geometric inputs of the Stacks proof, for an *arbitrary* morphism
`b : S' ⟶ S` in place of the blowup.

The Stacks proof of 0806 has two halves. Existence of a morphism `Y ⟶ S'` over `S` comes from
the universal property of relative `Proj` (Constructions, Section 01NS): for `f : Y ⟶ S` in
`C` with `D = f^{-1}(Z)`, the surjection `f^* I → I_D` onto an invertible module extends to a
graded map `⨁ f^* Iⁿ → ⨁ I_Dⁿ`, and that is the datum classifying a morphism into the
relative `Proj`. Uniqueness is separate and purely about `S`-schemes: the two candidate
morphisms agree over `S \ Z`, because `b` is an isomorphism there (tag 02OS part 1); the
inverse image of `S \ Z` in `Y` is the complement of the effective Cartier divisor `D`, hence
scheme-theoretically dense (tag 07ZU); and `b` is separated (tag 01O2), so two morphisms over
`S` agreeing on a scheme-theoretically dense open are equal (tag 01RH,
`AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense`).

The uniqueness half is proved here in full. Consequently
`Stacks.Blowup.exists_nonempty_isTerminal` closes tag 0806 for a morphism `b : S' ⟶ S` given
five inputs about it, all of which the blowup has still to supply: separatedness (tag 01O2),
membership in `C` (tag 02OS part 2), being an isomorphism over the complement of the center
(tag 02OS part 1), scheme-theoretic density of the complement of an effective Cartier divisor
(tag 07ZU), and the existence of the classifying morphism (Constructions, Section 01NS).

## Main definitions

* `Stacks.Blowup.IsCartierOver`: the property of an object of `Sch/S` that the inverse image
  of `I` is an effective Cartier divisor.
* `Stacks.Blowup.CartierOver`: the category `C` of tag 0806, the corresponding full
  subcategory of `Sch/S`.

## Main results

* `Stacks.Blowup.eq_of_eq_restrict`: two morphisms to a separated `S`-scheme that agree on a
  scheme-theoretically dense open of their common source are equal. Tag 01RH, restated for
  bare scheme morphisms rather than morphisms of `CategoryTheory.Over S`.
* `Stacks.Blowup.eq_of_isIso_morphismRestrict`: a morphism `b` which restricts to an
  isomorphism over an open `V` of its target is a monomorphism on morphisms whose composite
  with `b` lands in `V`.
* `Stacks.Blowup.eq_of_comp_eq`: the uniqueness assertion of tag 0806. A morphism to `S'` over
  `S` is determined by its composite with `b`, when `b` is separated, restricts to an
  isomorphism over `V`, and the inverse image of `V` in the source is scheme-theoretically
  dense.
* `Stacks.Blowup.nonempty_isTerminal_of_forall_exists`: a morphism `b : S' ⟶ S` which is
  separated, lies in `C`, restricts to an isomorphism over an open `V` of `S`, and admits a
  morphism from every object of `C`, is a final object of `C`, provided the inverse image of
  `V` in each object of `C` is scheme-theoretically dense.
* `Stacks.Blowup.exists_nonempty_isTerminal`: the same statement with `V` specialized to the
  complement of the support of `I`, so that the two topological hypotheses are exactly tags
  02OS part 1 and 07ZU, and in the conjunctive form of tag 0806.

## Implementation notes

Finality is asserted as `Nonempty (CategoryTheory.Limits.IsTerminal _)`: `IsTerminal` is data,
and the statement of tag 0806 is a proposition.

The hypothesis that `b` is an isomorphism over `V` is `IsIso (b ∣_ V)`, Mathlib's
`AlgebraicGeometry.morphismRestrict`. It is used only through
`Stacks.Blowup.eq_of_isIso_morphismRestrict`, whose proof factors the two morphisms through
the open subscheme `b ⁻¹ᵁ V` with `AlgebraicGeometry.IsOpenImmersion.lift` and then cancels
the monomorphisms `(b ∣_ V)` and `V.ι`. Only monomorphy of `b ∣_ V` is used, so the
hypothesis could be weakened; it is stated as an isomorphism because that is what tag 02OS
part 1 provides.

The density hypothesis is phrased on the open `Y.hom ⁻¹ᵁ V` rather than on the complement of
the divisor `I.comap Y.hom`, because that is the form in which the uniqueness argument needs
it. `Stacks.Blowup.preimage_compl_support` identifies the two, which is what lets
`Stacks.Blowup.exists_nonempty_isTerminal` take tag 07ZU as its hypothesis verbatim.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 01RH](https://stacks.math.columbia.edu/tag/01RH)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

variable {S : Scheme.{u}}

/-- An object `Y ⟶ S` of `Sch/S` has effective Cartier inverse image of the closed subscheme
cut out by `I`. This is the defining condition of the category `C` of Stacks tag 0806. -/
abbrev IsCartierOver (I : S.IdealSheafData) : ObjectProperty (Over S) :=
  fun Y => Stacks.Divisors.IsEffectiveCartierDivisor (I.comap Y.hom)

/-- The category `C` of Stacks tag 0806: the full subcategory of `Sch/S` consisting of those
`Y ⟶ S` for which the inverse image of the closed subscheme cut out by `I` is an effective
Cartier divisor on `Y`. -/
abbrev CartierOver (I : S.IdealSheafData) := (IsCartierOver I).FullSubcategory

/-- **Stacks Project, Tag 01RH** for bare scheme morphisms. Two morphisms `T ⟶ S'` with the
same composite to `S` along a separated `b : S' ⟶ S` are equal as soon as they agree on a
scheme-theoretically dense open subscheme of `T`. -/
theorem eq_of_eq_restrict {S' T : Scheme.{u}} (b : S' ⟶ S) [IsSeparated b] {f : T ⟶ S}
    (g₁ g₂ : T ⟶ S') (h₁ : g₁ ≫ b = f) (h₂ : g₂ ≫ b = f)
    (U : T.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (h : U.ι ≫ g₁ = U.ι ≫ g₂) : g₁ = g₂ := by
  have : IsSeparated (Over.mk b).hom := ‹IsSeparated b›
  exact congrArg CommaMorphism.left (AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense
    (X := Over.mk f) (Y := Over.mk b) (Over.homMk g₁ h₁) (Over.homMk g₂ h₂) U hU h)

/-- A morphism `b` restricting to an isomorphism over an open `V` of its target cancels on the
left of morphisms whose composite with `b` factors through `V`. -/
theorem eq_of_isIso_morphismRestrict {S' W : Scheme.{u}} {b : S' ⟶ S} {V : S.Opens}
    [IsIso (b ∣_ V)] (h₁ h₂ : W ⟶ S') (hb : h₁ ≫ b = h₂ ≫ b)
    (hr : Set.range (h₁ ≫ b).base ⊆ (V : Set S)) : h₁ = h₂ := by
  have key : ∀ g : W ⟶ S', Set.range (g ≫ b).base ⊆ (V : Set S) →
      ∃ l : W ⟶ (b ⁻¹ᵁ V).toScheme, l ≫ (b ⁻¹ᵁ V).ι = g := fun g hg =>
    ⟨IsOpenImmersion.lift _ g (by
      rw [Scheme.Opens.range_ι]
      rintro x ⟨w, rfl⟩
      exact hg ⟨w, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨l₁, e₁⟩ := key h₁ hr
  obtain ⟨l₂, e₂⟩ := key h₂ (by rwa [← hb])
  have step : l₁ ≫ (b ∣_ V) = l₂ ≫ (b ∣_ V) := by
    apply (cancel_mono V.ι).1
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, ← Category.assoc,
      e₁, e₂, hb]
  rw [← e₁, ← e₂, (cancel_mono (b ∣_ V)).1 step]

/-- The inverse image of an open `V` maps into `V`. -/
theorem range_preimage_ι_comp {T : Scheme.{u}} (f : T ⟶ S) (V : S.Opens) :
    Set.range ((f ⁻¹ᵁ V).ι ≫ f).base ⊆ (V : Set S) := by
  rintro x ⟨w, rfl⟩
  exact w.2

/-- The inverse image of the complement of the closed subscheme cut out by `I` is the
complement of the closed subscheme cut out by the inverse image of `I`. -/
theorem preimage_compl_support {T : Scheme.{u}} (I : S.IdealSheafData) (f : T ⟶ S) :
    f ⁻¹ᵁ I.support.compl = (I.comap f).support.compl := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The uniqueness assertion of **Stacks Project, Tag 0806**: a morphism to `S'` over `S` is
determined by its composite with `b`, provided `b` is separated, `b` restricts to an
isomorphism over an open `V` of `S`, and the inverse image of `V` in the source is
scheme-theoretically dense.

For the blowup of `S` in `I` the hypotheses hold with `V` the complement of the center: `b` is
separated by tag 01O2, it is an isomorphism over `V` by tag 02OS part 1, and the inverse image
of `V` is the complement of an effective Cartier divisor, hence scheme-theoretically dense by
tag 07ZU. -/
theorem eq_of_comp_eq {S' T : Scheme.{u}} (b : S' ⟶ S) [IsSeparated b] {V : S.Opens}
    [IsIso (b ∣_ V)] {f : T ⟶ S}
    (hdense : Scheme.Opens.IsSchemeTheoreticallyDense (f ⁻¹ᵁ V))
    (g₁ g₂ : T ⟶ S') (h₁ : g₁ ≫ b = f) (h₂ : g₂ ≫ b = f) : g₁ = g₂ := by
  refine eq_of_eq_restrict b _ _ h₁ h₂ _ hdense ?_
  refine eq_of_isIso_morphismRestrict (b := b) (V := V) _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, h₁, h₂]
  · rw [Category.assoc, h₁]
    exact range_preimage_ι_comp f V

/-- **Stacks Project, Tag 0806** reduced to its geometric inputs: the uniqueness half is
proved, the existence half is a hypothesis.

A morphism `b : S' ⟶ S` is a final object of the category `C` of schemes over `S` on which the
inverse image of `I` is an effective Cartier divisor, as soon as

* `b` is separated (tag 01O2 for the blowup);
* `b` is an object of `C`, i.e. the exceptional divisor is an effective Cartier divisor
  (tag 02OS part 2 for the blowup);
* `b` restricts to an isomorphism over an open `V` of `S` (tag 02OS part 1 for the blowup,
  with `V` the complement of the center);
* the inverse image of `V` in every object of `C` is scheme-theoretically dense (tag 07ZU for
  the blowup, with `V` as above);
* every object of `C` admits a morphism to `S'` over `S` (the universal property of relative
  `Proj`, Constructions Section 01NS, for the blowup). -/
theorem nonempty_isTerminal_of_forall_exists {S' : Scheme.{u}} (I : S.IdealSheafData)
    (b : S' ⟶ S) [IsSeparated b] (hb : IsCartierOver I (Over.mk b))
    (V : S.Opens) [IsIso (b ∣_ V)]
    (hdense : ∀ Y : Over S, IsCartierOver I Y →
      Scheme.Opens.IsSchemeTheoreticallyDense (Y.hom ⁻¹ᵁ V))
    (hex : ∀ Y : Over S, IsCartierOver I Y → ∃ g : Y.left ⟶ S', g ≫ b = Y.hom) :
    Nonempty (IsTerminal (⟨Over.mk b, hb⟩ : CartierOver I)) := by
  refine ⟨IsTerminal.ofUniqueHom (fun Y => ObjectProperty.homMk
      (Over.homMk (hex Y.obj Y.property).choose (hex Y.obj Y.property).choose_spec))
    (fun Y m => ?_)⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact eq_of_comp_eq b (hdense Y.obj Y.property) _ _ (Over.w m.hom)
    (hex Y.obj Y.property).choose_spec

/-- **Stacks Project, Tag 0806**, in its own conjunctive form, with the three statements the
blowup has still to supply as hypotheses: the universal property of relative `Proj`, and tags
02OS part 1 and 07ZU.

The open `V` of `Stacks.Blowup.nonempty_isTerminal_of_forall_exists` is specialized to the
complement of the center, so `hiso` is literally tag 02OS part 1 and `hcartierDense` is
literally the density half of tag 07ZU. -/
theorem exists_nonempty_isTerminal {S' : Scheme.{u}} (I : S.IdealSheafData)
    (b : S' ⟶ S) [IsSeparated b] (hb : IsCartierOver I (Over.mk b))
    (hiso : IsIso (b ∣_ I.support.compl))
    (hcartierDense : ∀ (T : Scheme.{u}) (J : T.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor J →
        Scheme.Opens.IsSchemeTheoreticallyDense J.support.compl)
    (hex : ∀ Y : Over S, IsCartierOver I Y → ∃ g : Y.left ⟶ S', g ≫ b = Y.hom) :
    ∃ h : IsCartierOver I (Over.mk b),
      Nonempty (IsTerminal (⟨Over.mk b, h⟩ : CartierOver I)) := by
  refine ⟨hb, nonempty_isTerminal_of_forall_exists I b hb I.support.compl (fun Y hY => ?_) hex⟩
  rw [preimage_compl_support]
  exact hcartierDense _ _ hY

end Stacks.Blowup

end
