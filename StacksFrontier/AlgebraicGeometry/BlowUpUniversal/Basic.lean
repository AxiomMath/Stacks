module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense

/-!
# The universal property of blowing up, reduced to the inputs it needs

Tag 0806 says that for a closed subscheme `Z ⊆ X` the blowup `b : X' → X` of `Z` in `X` is a
*final* object of the full subcategory of `Sch/X` whose objects are the morphisms `Y → X` for
which the inverse image of `Z` is an effective Cartier divisor on `Y`.

This file states that subcategory and proves the reduction of the finality statement to the
inputs the Stacks proof uses, every one of which is a separate result:

* `b` itself is an object of the subcategory, and `b` is an isomorphism over the complement of
  `Z` — the second and first assertions of Tag 02OS;
* a morphism `Y → X'` over `X` exists for every object `Y` of the subcategory — the content of
  Constructions, Tag 01NS, applied to the triple `(1, f, ψ)` built from the surjection
  `f^*ℐ → ℐ_D` onto an invertible module;
* the complement of an effective Cartier divisor is scheme-theoretically dense — Tag 07ZU;
* `b` is separated — Tag 01O2.

The fifth input of the Stacks proof, Tag 01RH (two morphisms into a separated scheme over `S`
agreeing on a scheme-theoretically dense open are equal), is already available as
`AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense`, so it is *used* here rather than assumed.

## Main definitions

* `Stacks.AlgebraicGeometry.BlowUpUniversal.supportCompl` is the open complement of the support
  of an ideal sheaf: for the centre it is `X \ Z`, and for the inverse image it is `Y \ D`.
* `Stacks.AlgebraicGeometry.BlowUpUniversal.IsCartierOver` is the property of an object of
  `Over X` that the inverse image of the centre is an effective Cartier divisor.
* `Stacks.AlgebraicGeometry.BlowUpUniversal.CartierOver` is the corresponding full subcategory,
  the category `𝒞` of Tag 0806.

## Main results

* `Stacks.AlgebraicGeometry.BlowUpUniversal.ι_comp_eq_of_mono`: two morphisms to the blowup
  lying over the same morphism to the base agree on the inverse image of the complement of the
  centre, as soon as the blowup morphism restricted over that complement is a monomorphism.
  This is the step the Stacks proof records as "the restriction `Y \ D → X' \ b⁻¹(Z) = X \ Z`
  is unique", and it is proved here outright.
* `Stacks.AlgebraicGeometry.BlowUpUniversal.over_hom_unique`: the uniqueness half of Tag 0806
  outright, from Tags 02OS (1), 01O2 and 07ZU — an object of `Over X` with effective Cartier
  inverse image of the centre admits *at most one* morphism to the blowup over the base.
* `Stacks.AlgebraicGeometry.BlowUpUniversal.nonempty_isTerminal_blowUp_of`: Tag 0806's
  conclusion, from the inputs above together with the existence of one lift. The tag is
  deliberately **not** attached: the statement carries hypotheses that Tag 0806 does not, so it
  is a reduction and not the lemma.

## Implementation notes

The agreement step is proved without any point-set surgery on the blowup. Both morphisms
restricted to `Y \ D` have topological image inside `b⁻¹(X \ Z)`, because composing either with
`b` gives `f`; so both factor through that open subscheme by the universal property of an open
immersion, `AlgebraicGeometry.IsOpenImmersion.lift`. Composing the two factorizations with the
restricted morphism `b ∣_ (X \ Z)` and with the inclusion of `X \ Z` gives the same morphism,
namely the restriction of `f`; cancelling the inclusion, which is a monomorphism, and then the
restricted morphism leaves the two factorizations equal.

The hypothesis on `b ∣_ (X \ Z)` is stated as `Mono` rather than `IsIso` in
`ι_comp_eq_of_mono`, since that is all the argument consumes; the reduction theorem takes the
literal `IsIso` of Tag 02OS (1) and weakens it on the spot.

Finality is built with `CategoryTheory.Limits.IsTerminal.ofUniqueHom`. A morphism in a full
subcategory is a morphism of the ambient category, so both halves — the chosen lift and its
uniqueness — are statements in `Over X`, and `AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense`
applies to them directly without transporting anything across the inclusion functor.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.BlowUpUniversal

/-- The open complement of the support of an ideal sheaf: the open subscheme on which the
closed subscheme it cuts out is empty. For the centre of a blowup this is `X \ Z`, and for the
inverse image of the centre along `f : Y ⟶ X` it is `Y \ f⁻¹(Z)`. -/
public abbrev supportCompl {X : Scheme.{u}} (I : X.IdealSheafData) : X.Opens :=
  I.support.compl

/-- An object `Y ⟶ X` of `Over X` has effective Cartier inverse image of the centre `I`. This
is the defining property of the full subcategory `𝒞` of Tag 0806. -/
public abbrev IsCartierOver {X : Scheme.{u}} (I : X.IdealSheafData) :
    ObjectProperty (Over X) :=
  fun Y => Stacks.Divisors.IsEffectiveCartierDivisor (I.comap Y.hom)

/-- The full subcategory of `Sch/X` consisting of the `Y ⟶ X` for which the inverse image of
the centre is an effective Cartier divisor: the category `𝒞` of Tag 0806. -/
public abbrev CartierOver {X : Scheme.{u}} (I : X.IdealSheafData) :=
  (IsCartierOver I).FullSubcategory

/-- Taking the complement of the support commutes with inverse image: the part of `Y` away
from `f⁻¹(Z)` is the inverse image of the part of `X` away from `Z`. -/
public theorem preimage_supportCompl {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    f ⁻¹ᵁ supportCompl I = supportCompl (I.comap f) := by
  ext y
  simp [Scheme.IdealSheafData.support_comap]

/-- Two morphisms to the blowup lying over one morphism to the base agree over the complement
of the centre, provided the blowup morphism restricted over that complement is a monomorphism
(which Tag 02OS (1) provides, as it is even an isomorphism there).

This is the step that the proof of Tag 0806 records as "the restriction
`Y \ D ⟶ X' \ b⁻¹(Z) = X \ Z` is unique". -/
public theorem ι_comp_eq_of_mono {X : Scheme.{u}} (I : X.IdealSheafData)
    (hmono : Mono (blowUpToBase I ∣_ supportCompl I))
    {Y : Scheme.{u}} {f : Y ⟶ X} (g₁ g₂ : Y ⟶ blowUp I)
    (h₁ : g₁ ≫ blowUpToBase I = f) (h₂ : g₂ ≫ blowUpToBase I = f) :
    (f ⁻¹ᵁ supportCompl I).ι ≫ g₁ = (f ⁻¹ᵁ supportCompl I).ι ≫ g₂ := by
  -- Each restriction factors through the open subscheme over the complement of the centre, and
  -- the factorization has composite `V.ι ≫ f` into the complement of the centre.
  have key : ∀ g : Y ⟶ blowUp I, g ≫ blowUpToBase I = f →
      ∃ l : (f ⁻¹ᵁ supportCompl I).toScheme ⟶ (blowUpToBase I ⁻¹ᵁ supportCompl I).toScheme,
        l ≫ (blowUpToBase I ⁻¹ᵁ supportCompl I).ι = (f ⁻¹ᵁ supportCompl I).ι ≫ g ∧
        l ≫ (blowUpToBase I ∣_ supportCompl I) ≫ (supportCompl I).ι =
          (f ⁻¹ᵁ supportCompl I).ι ≫ f := by
    intro g hg
    have hrange : Set.range ((f ⁻¹ᵁ supportCompl I).ι ≫ g) ⊆
        Set.range (blowUpToBase I ⁻¹ᵁ supportCompl I).ι := by
      rw [Scheme.Opens.range_ι, Set.range_subset_iff]
      intro v
      have hv : ((f ⁻¹ᵁ supportCompl I).ι v) ∈ (f ⁻¹ᵁ supportCompl I : Y.Opens) := by
        rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
        exact ⟨v, rfl⟩
      have hcomp : blowUpToBase I (((f ⁻¹ᵁ supportCompl I).ι ≫ g) v) =
          f ((f ⁻¹ᵁ supportCompl I).ι v) := by
        rw [← Scheme.Hom.comp_apply, Category.assoc, hg, Scheme.Hom.comp_apply]
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, hcomp]
      exact hv
    have hl := IsOpenImmersion.lift_fac (blowUpToBase I ⁻¹ᵁ supportCompl I).ι
      ((f ⁻¹ᵁ supportCompl I).ι ≫ g) hrange
    refine ⟨_, hl, ?_⟩
    rw [morphismRestrict_ι, ← Category.assoc, hl, Category.assoc, hg]
  obtain ⟨l₁, e₁, k₁⟩ := key g₁ h₁
  obtain ⟨l₂, e₂, k₂⟩ := key g₂ h₂
  rw [← e₁, ← e₂]
  have : l₁ ≫ (blowUpToBase I ∣_ supportCompl I) = l₂ ≫ (blowUpToBase I ∣_ supportCompl I) := by
    rw [← cancel_mono (supportCompl I).ι, Category.assoc, Category.assoc, k₁, k₂]
  rw [cancel_mono (blowUpToBase I ∣_ supportCompl I)] at this
  rw [this]

/-- The uniqueness half of Tag 0806, stated in `Over X`: an object of `Over X` whose inverse
image of the centre is an effective Cartier divisor admits at most one morphism to the blowup
over the base.

This is Tag 01RH applied to the open complement of that divisor: the two morphisms agree there
by `ι_comp_eq_of_mono`, the open is scheme-theoretically dense by Tag 07ZU, and the blowup
morphism is separated by Tag 01O2. -/
public theorem over_hom_unique {X : Scheme.{u}} (I : X.IdealSheafData)
    (hmono : Mono (blowUpToBase I ∣_ supportCompl I))
    (hsep : IsSeparated (blowUpToBase I))
    (hdense : ∀ {W : Scheme.{u}} (D : W.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor D →
      Scheme.Opens.IsSchemeTheoreticallyDense (supportCompl D))
    {Y : Over X} (hY : IsCartierOver I Y)
    (g₁ g₂ : Y ⟶ Over.mk (blowUpToBase I)) : g₁ = g₂ := by
  have hsep' : IsSeparated (Over.mk (blowUpToBase I)).hom := hsep
  refine AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense g₁ g₂
    (Y.hom ⁻¹ᵁ supportCompl I) ?_ ?_
  · rw [preimage_supportCompl]
    exact hdense _ hY
  · exact ι_comp_eq_of_mono I hmono g₁.left g₂.left (Over.w g₁) (Over.w g₂)

/-- **The reduction of Stacks Project, Tag 0806.** The blowup of `X` in `I` is a final object
of the full subcategory of `Sch/X` whose objects have effective Cartier inverse image of the
centre, given the four results the Stacks proof invokes:

* `hcartier`: the blowup is itself an object of the subcategory — Tag 02OS (2), that the
  exceptional divisor `b⁻¹(Z)` is an effective Cartier divisor on `X'`;
* `hiso`: the blowup morphism is an isomorphism over the complement of the centre — Tag
  02OS (1);
* `hsep`: the blowup morphism is separated — Tag 01O2, separatedness of the structure morphism
  of a relative `Proj`;
* `hdense`: the complement of an effective Cartier divisor is scheme-theoretically dense —
  Tag 07ZU, stated here for an arbitrary scheme and divisor, as that is what Tag 07ZU says;
* `hlift`: every object of the subcategory admits at least one morphism to the blowup over the
  base — the existence half, which Constructions, Tag 01NS, supplies from the triple
  `(1, f, ψ)` determined by the surjection `f^*ℐ → ℐ_D` onto an invertible module.

Tag 0806's fifth input, Tag 01RH, is not a hypothesis: it is proved in this repository as
`AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense` and is used below.

The tag of 0806 is deliberately left off this declaration, because the statement carries
hypotheses that Tag 0806 does not. Discharging the hypotheses turns it into the tag. -/
public theorem nonempty_isTerminal_blowUp_of {X : Scheme.{u}} (I : X.IdealSheafData)
    (hcartier : IsCartierOver I (Over.mk (blowUpToBase I)))
    (hiso : IsIso (blowUpToBase I ∣_ supportCompl I))
    (hsep : IsSeparated (blowUpToBase I))
    (hdense : ∀ {W : Scheme.{u}} (D : W.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor D →
      Scheme.Opens.IsSchemeTheoreticallyDense (supportCompl D))
    (hlift : ∀ Y : Over X, IsCartierOver I Y →
      Nonempty (Y ⟶ Over.mk (blowUpToBase I))) :
    ∃ h : IsCartierOver I (Over.mk (blowUpToBase I)),
      Nonempty (IsTerminal (⟨Over.mk (blowUpToBase I), h⟩ : CartierOver I)) := by
  have hmono : Mono (blowUpToBase I ∣_ supportCompl I) := by
    have := hiso
    infer_instance
  refine ⟨hcartier, ⟨IsTerminal.ofUniqueHom
    (fun Y => ObjectProperty.homMk (hlift Y.obj Y.property).some) ?_⟩⟩
  intro Y m
  exact ObjectProperty.hom_ext (P := IsCartierOver I)
    (over_hom_unique I hmono hsep hdense Y.property m.hom _)

end Stacks.AlgebraicGeometry.BlowUpUniversal

end
