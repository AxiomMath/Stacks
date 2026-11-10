module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperClosedFibre

/-!
# Two unconditional cases of Tag 0GS2 that use no algebraization

Let `(A, I)` be a henselian pair, write `q : Spec (A ⧸ I) ⟶ Spec A` for the quotient map and let
`f : X ⟶ Spec A` be proper with closed fibre `X ×_{Spec A} Spec (A ⧸ I)`.  Tag 0GS2 asserts that
base change along the first projection of that closed fibre is an equivalence on finite étale
covers; the essential-surjectivity half of it is reduced to Grothendieck existence in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence` and is proved for
the *finite* morphisms in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase`.  This file adds the
two statements about that situation that need no algebraization at all.

The first is the family of morphisms that factor through the closed subscheme.  If `f = h ≫ q`
then the closed fibre *is* `X`: `q` is a closed immersion, hence a monomorphism, so the first
projection of the pullback of `h ≫ q` along `q` is an isomorphism and the conclusion of Tag 0GS2
follows from `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isIso`.  Neither properness
nor henselianness is used.  The point of recording it is that `h` is an arbitrary morphism to
`Spec (A ⧸ I)`: when `h` is proper so is `h ≫ q`, so this exhibits the conclusion of Tag 0GS2 for
proper morphisms that need not be finite and for ideals that need not be `⊥` — the two families for
which the conclusion was already available.  It is a degenerate case by construction, not progress
on the mathematics of the tag.

The second is the last step of the Stacks proof of Tag 0GS2, which *is* part of that mathematics.
After algebraization one has a morphism `U ⟶ X` with `U` proper over `Spec A`, known to be étale
only in a neighbourhood of the closed fibre of `U`, and concludes that it is étale everywhere
because every point of `U` specializes into that closed fibre.  Since an open subscheme containing
the closed fibre has `V.ι` an isomorphism
(`AlgebraicGeometry.isIso_opens_ι_of_forall_exists_specializes`), this holds for every morphism
property that respects isomorphisms, with no local-at-source hypothesis.

## Main results

* `AlgebraicGeometry.isClosedImmersion_specMap_quotientMk` and
  `AlgebraicGeometry.mono_specMap_quotientMk` — the quotient map `Spec (A ⧸ I) ⟶ Spec A` is a
  closed immersion, hence a monomorphism.
* `AlgebraicGeometry.isIso_pullback_fst_of_factorsThrough_quotient` — the closed fibre of a
  morphism that factors through `Spec (A ⧸ I)` is the scheme itself.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_factorsThrough_quotient` — the
  conclusion of Tag 0GS2 for such a morphism.
* `AlgebraicGeometry.of_restrict_opens_of_forall_exists_specializes` and
  `AlgebraicGeometry.etale_of_etale_restrict_of_isProper_of_henselianPair` — a morphism out of a
  scheme proper over a henselian pair is étale as soon as its restriction to an open neighbourhood
  of the closed fibre is.

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] (I : Ideal A)

/-! ### Morphisms that factor through the closed subscheme -/

/-- The quotient map `Spec (A ⧸ I) ⟶ Spec A` is a closed immersion, because
`Ideal.Quotient.mk I` is surjective. -/
theorem isClosedImmersion_specMap_quotientMk :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The quotient map `Spec (A ⧸ I) ⟶ Spec A` is a monomorphism. -/
theorem mono_specMap_quotientMk :
    Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  have := isClosedImmersion_specMap_quotientMk A I
  inferInstance

/-- **The closed fibre of a morphism factoring through `Spec (A ⧸ I)` is the scheme itself.** The
first projection of the pullback of `h ≫ q` along `q` is an isomorphism, since `q` is a
monomorphism. -/
theorem isIso_pullback_fst_of_factorsThrough_quotient {X : Scheme.{u}}
    (h : X ⟶ Spec (.of (A ⧸ I))) :
    IsIso (pullback.fst (h ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :=
  have := mono_specMap_quotientMk A I
  inferInstance

/-- **The conclusion of Tag 0GS2 for a morphism that factors through the closed subscheme.** If
`f = h ≫ q` for some `h : X ⟶ Spec (A ⧸ I)`, then base change along the first projection of the
closed fibre of `f` is an equivalence on finite étale covers.

The closed fibre of such an `f` is `X` itself, so this uses neither properness of `f` nor
henselianness of the pair; when `h` is proper, `f` is proper and need not be finite. -/
theorem isEquivalence_finiteEtaleBaseChange_of_factorsThrough_quotient {X : Scheme.{u}}
    (h : X ⟶ Spec (.of (A ⧸ I))) :
    (finiteEtaleBaseChange
      (pullback.fst (h ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence :=
  have := isIso_pullback_fst_of_factorsThrough_quotient A I h
  isEquivalence_finiteEtaleBaseChange_of_isIso _

/-! ### Étale in a neighbourhood of the closed fibre -/

/-- **A property respecting isomorphisms descends from an open neighbourhood of the image of `g`.**
If every point of `X` specializes into the image of `g : X₀ ⟶ X` and `V` is an open subscheme
containing that image, then `V.ι` is an isomorphism, so `P (V.ι ≫ f)` and `P f` say the same
thing. -/
theorem of_restrict_opens_of_forall_exists_specializes {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {X X₀ Y : Scheme.{u}} (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') (V : X.Opens)
    (hV : Set.range g.base ⊆ Set.range V.ι.base) (f : X ⟶ Y) (hf : P (V.ι ≫ f)) : P f := by
  have : IsIso V.ι := isIso_opens_ι_of_forall_exists_specializes g hsp V hV
  rwa [P.cancel_left_of_respectsIso V.ι f] at hf

/-- **A morphism out of a scheme proper over a henselian pair is étale as soon as it is étale in a
neighbourhood of the closed fibre.** This is the step with which the Stacks proof of Tag 0GS2 ends:
the algebraized morphism is étale at the points of the closed fibre, hence on an open set
containing it, and every point of a scheme proper over a henselian pair specializes into the closed
fibre. -/
theorem etale_of_etale_restrict_of_isProper_of_henselianPair (hI : HenselianPair A I)
    {U : Scheme.{u}} (p : U ⟶ Spec (.of A)) [IsProper p] (V : U.Opens)
    (hV : Set.range
        (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base
      ⊆ Set.range V.ι.base)
    {X : Scheme.{u}} (f : U ⟶ X) (hf : Etale (V.ι ≫ f)) : Etale f :=
  let _ : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
      (Q := RingHom.Etale)).toRespects
  of_restrict_opens_of_forall_exists_specializes (P := @Etale) _
    (exists_specializes_mem_range_pullback_fst_of_isProper A hI.le_jacobson p) V hV f hf

end AlgebraicGeometry

end
