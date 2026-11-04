module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase
public import StacksFrontier.AlgebraicGeometry.RestrictIso

/-!
# Relative ampleness along a nested open restriction of the base

Let `f : X ⟶ S` be a morphism of schemes, `ℒ` an invertible `𝒪_X`-module and `W ≤ U` two opens of
`S`. The proof of [Stacks, Tag 0D2N] shrinks the base twice: first to an open `U ∋ y` over which
the sections defining the morphism to projective space exist, and then — inside `U` — to an open
over which they generate everywhere. Its conclusion therefore arrives as relative ampleness of the
**twice-restricted** morphism

`(f ∣_ U) ∣_ (U.ι ⁻¹ᵁ W) : (f ∣_ U)⁻¹(U.ι⁻¹W) ⟶ (U.ι⁻¹W)`

for the twice-restricted module, whereas the statement of the tag speaks about the once-restricted
morphism `f ∣_ W : f⁻¹W ⟶ W` over an open of `S` itself. This file is that transport, and nothing
else; it is one step of the proof of [Stacks, Tag 0D2N], which is registered as
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`
(`AmpleFibreNeighbourhood/RelativelyAmpleNeighbourhood.lean`).

## Main results

* `Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_morphismRestrict_of_le`: for `W ≤ U`, relative
  ampleness of `ℒ|_{(f ∣_ U)⁻¹(U.ι⁻¹W)}` for `(f ∣_ U) ∣_ (U.ι ⁻¹ᵁ W)` gives relative ampleness of
  `ℒ|_{f⁻¹W}` for `f ∣_ W`.
* `Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_morphismRestrict_image`: the same statement in
  the shape the shrinking step produces it, where the second open is given as an open `W'` of the
  scheme `U.toScheme` and the conclusion is about `f ∣_ (U.ι ''ᵁ W')`.

## The route

Everything is read off the two clauses of [Stacks, Tag 01VJ] that this repository already proves.

* Relative ampleness of `f ∣_ W` is produced by the pointwise affine criterion
  `Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple` — clause (3) implies
  clause (1) — so only *absolute* ampleness over the preimage of one affine open of `W.toScheme`
  around each of its points has to be supplied.
* Both the production and the consumption of such an ampleness statement go through one lemma,
  `Stacks.RelativeAmpleRestrictBase.isAmple_preimage_morphismRestrict_iff`: for an open `A` of an
  open `V ⊆ S`, ampleness of the restriction of `ℒ|_{f⁻¹V}` to `(f ∣_ V)⁻¹A` is ampleness of the
  restriction of `ℒ` to `f⁻¹(V.ι ''ᵁ A)`, the two open subschemes of `X` having the same underlying
  open. It is applied three times here: once for `f` and `W` to reach the goal, and then for
  `f ∣_ U` and for `f` to carry the hypothesis down to `X`, the module on `(f⁻¹U).toScheme` being
  `ℒ|_{f⁻¹U}` in the second of those.
* The opens are matched by `Stacks.RestrictIso.ι_image_ι_preimage_of_le`, which is the identity
  `U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W` for `W ≤ U`, and the affineness of the preimages by
  `AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion`; the affine opens of `S` around a
  given point and inside `W` exist because they form a basis
  (`AlgebraicGeometry.Scheme.isBasis_affineOpens`).

**Quasi-compactness is not assumed.** It is the first conjunct of
`Stacks.RelativeAmple.IsRelativelyAmple`, so the hypothesis already carries quasi-compactness of
the twice-restricted morphism, and `Stacks.RestrictIso.morphismRestrictRestrictLE` — the arrow
isomorphism `f ∣_ U ∣_ (U.ι ⁻¹ᵁ W) ≅ f ∣_ W` of `AlgebraicGeometry.morphismRestrictRestrict` and
`AlgebraicGeometry.morphismRestrictEq` — transports it to `f ∣_ W`, quasi-compactness of a
morphism respecting isomorphisms because it is stable under base change
(`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`). No properness, no
Noetherian hypothesis and no affineness of `U` or `W` is used.

The invertibility of the restricted modules, needed to state both results, is the instance
`Stacks.InvertiblePullback.isInvertibleModule_restrict`, so none of it has to be named.

## No `@[stacks]` attribute is attached

Neither result is a numbered statement of the Stacks project. Both are transports of
`Stacks.RelativeAmple.IsRelativelyAmple` between two spellings of one restriction of `f`, and the
mathematics they consume carries its own tags elsewhere: clause (2) of [Stacks, Tag 01VJ] at
`StacksFrontier/AlgebraicGeometry/RelativeAmple/RestrictBase.lean` and clause (3) at
`StacksFrontier/AlgebraicGeometry/RelativeAmple/LocalOnBase.lean`. In particular no `@[stacks 0D2N]`
attribute is attached: this is one step of the proof of that tag, not its conclusion.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.RelativeAmpleRestrictBase (isAmple_preimage_morphismRestrict_iff)
open Stacks.RestrictIso (ι_image_ι_preimage_of_le morphismRestrictRestrictLE)

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-- Ampleness of the restriction of `ℒ|_{f⁻¹V}` to `(f ∣_ V)⁻¹(V.ι⁻¹A)` is ampleness of `ℒ|_{f⁻¹A}`
for `A ≤ V`. -/
private theorem isAmple_preimage_morphismRestrict_iff_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] {V A : S.Opens} (hAV : A ≤ V) :
    IsAmple ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ A)).toScheme
        (pullbackModule ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ A)).ι (pullbackModule (f ⁻¹ᵁ V).ι L)) ↔
      IsAmple (f ⁻¹ᵁ A).toScheme (pullbackModule (f ⁻¹ᵁ A).ι L) := by
  have := isAmple_preimage_morphismRestrict_iff f L (V.ι ⁻¹ᵁ A)
  rwa [ι_image_ι_preimage_of_le hAV] at this

/-- **Relative ampleness of a twice-restricted morphism is relative ampleness over the smaller
open of the base itself.** Let `f : X ⟶ S`, let `ℒ` be an invertible `𝒪_X`-module and let
`W ≤ U` be opens of `S`. If the restriction of `ℒ` to `(f ∣_ U)⁻¹(U.ι⁻¹W)` is ample relative to
`(f ∣_ U) ∣_ (U.ι ⁻¹ᵁ W)`, then the restriction of `ℒ` to `f⁻¹W` is ample relative to `f ∣_ W`.

Quasi-compactness of `f ∣_ W` is read off the hypothesis, which contains quasi-compactness of the
twice-restricted morphism, along the arrow isomorphism
`Stacks.RestrictIso.morphismRestrictRestrictLE`; quasi-compactness respects isomorphisms by
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`.

The ampleness is then checked pointwise on the base by
`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple`, clause (3) implies
clause (1) of [Stacks, Tag 01VJ]. For an affine open `W₁ ⊆ W` of `S` the open `U.ι⁻¹W₁` of
`U.toScheme`, and then its preimage in `(U.ι⁻¹W).toScheme`, are affine by
`AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion`, so the hypothesis applies to the
second of them; two applications of
`Stacks.RelativeAmpleRestrictBase.isAmple_preimage_morphismRestrict_iff` — one for `f ∣_ U` and the
restriction of `ℒ` to `f⁻¹U`, one for `f` and `ℒ` — turn the resulting ampleness into ampleness of
`ℒ|_{f⁻¹W₁}`, the opens being matched by `Stacks.RestrictIso.ι_image_ι_preimage_of_le`. A third
application of the same lemma, for `f` and the open `W.ι⁻¹W₁` of `W.toScheme`, is what the
pointwise criterion consumes, and the affine opens of `S` inside `W` around a point of `W` exist
because the affine opens form a basis (`AlgebraicGeometry.Scheme.isBasis_affineOpens`). -/
theorem isRelativelyAmple_morphismRestrict_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] {U W : S.Opens} (hWU : W ≤ U)
    (h : Stacks.RelativeAmple.IsRelativelyAmple ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ W))
      (pullbackModule ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι (pullbackModule (f ⁻¹ᵁ U).ι L))) :
    Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ W) (pullbackModule (f ⁻¹ᵁ W).ι L) := by
  have : MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hqc : QuasiCompact (f ∣_ W) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @QuasiCompact)
      (morphismRestrictRestrictLE f hWU)).mp h.1
  have key : ∀ W₁ : S.Opens, IsAffineOpen W₁ → W₁ ≤ W →
      IsAmple (f ⁻¹ᵁ W₁).toScheme (pullbackModule (f ⁻¹ᵁ W₁).ι L) := by
    intro W₁ hW₁ hW₁W
    have hle : U.ι ⁻¹ᵁ W₁ ≤ U.ι ⁻¹ᵁ W := fun z hz => hW₁W hz
    have hAU := hW₁W.trans hWU
    have h1 := hW₁.preimage_of_isOpenImmersion U.ι (by simpa using hAU)
    have h2 := h1.preimage_of_isOpenImmersion (U.ι ⁻¹ᵁ W).ι (by simpa using hle)
    exact (isAmple_preimage_morphismRestrict_iff_of_le f L hAU).mp
      ((isAmple_preimage_morphismRestrict_iff_of_le (f ∣_ U) (pullbackModule (f ⁻¹ᵁ U).ι L)
        hle).mp (h.2 _ h2))
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple _ _ hqc
    fun x => ?_
  have hxmem : (W.ι x : S) ∈ (W : Set S) := by
    have hr : (W.ι x : S) ∈ ((W.ι.opensRange : S.Opens) : Set S) := ⟨x, rfl⟩
    rwa [Scheme.Opens.opensRange_ι] at hr
  obtain ⟨-, ⟨W₁, hW₁, rfl⟩, hxW₁, hW₁W⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxmem W.isOpen
  have hW₁W' : W₁ ≤ W := hW₁W
  exact ⟨W.ι ⁻¹ᵁ W₁, hW₁.preimage_of_isOpenImmersion W.ι (by simpa using hW₁W'), hxW₁,
    (isAmple_preimage_morphismRestrict_iff_of_le f L hW₁W').mpr (key W₁ hW₁ hW₁W')⟩

/-- **The same transport, with the smaller open given inside `U`.** Let `f : X ⟶ S`, let `ℒ` be an
invertible `𝒪_X`-module, let `U` be an open of `S` and let `W'` be an open of the scheme
`U.toScheme`. If the restriction of `ℒ` to `(f ∣_ U)⁻¹W'` is ample relative to `(f ∣_ U) ∣_ W'`,
then the restriction of `ℒ` to `f⁻¹(U.ι ''ᵁ W')` is ample relative to `f ∣_ (U.ι ''ᵁ W')`.

This is the shape in which the shrinking step of [Stacks, Tag 0D2N] produces its open: the second
shrinking happens inside `U.toScheme`, so what it names is an open of that scheme and not an open
of `S` below `U`. The image `U.ι ''ᵁ W'` lies in `U` by `AlgebraicGeometry.Scheme.Opens.ι_image_le`
and satisfies `U.ι ⁻¹ᵁ (U.ι ''ᵁ W') = W'` because `U.ι` is an open immersion
(`AlgebraicGeometry.Scheme.Hom.preimage_image_eq`), so
`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_morphismRestrict_of_le` applies to it. -/
theorem isRelativelyAmple_morphismRestrict_image {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] {U : S.Opens} (W' : U.toScheme.Opens)
    (h : Stacks.RelativeAmple.IsRelativelyAmple ((f ∣_ U) ∣_ W')
      (pullbackModule ((f ∣_ U) ⁻¹ᵁ W').ι (pullbackModule (f ⁻¹ᵁ U).ι L))) :
    Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ (U.ι ''ᵁ W'))
      (pullbackModule (f ⁻¹ᵁ (U.ι ''ᵁ W')).ι L) := by
  refine isRelativelyAmple_morphismRestrict_of_le f L (U.ι_image_le W') ?_
  rw [U.ι.preimage_image_eq W']
  exact h

end Stacks.AmpleFibreNeighbourhood

end
