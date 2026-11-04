module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAffineRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginAwayFromZero
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginEquivalenceRelation

/-!
# The Galois twist of the affine line with zero doubled is an algebraic space

The quotient sheaf
`AlgebraicGeometry.TwistedDoubledOrigin.quadraticGaloisTwistedDoubledOrigin` is the standard
example of an algebraic space which is not a scheme. That it is an algebraic space at all was,
in this development, conditional on effective fppf descent along the covering sieves — Stacks
0265, which rests on Stacks 0247 — and so was undischarged.

It is unconditional. The relation is an *affine* morphism into the self-product of the chart,
by `AlgebraicGeometry.TwistedDoubledOrigin.isAffineHom_twistedRelation_left`, the puncture being
the principal open `D(x)`, and for an affine relation Stacks 0265 needs effective descent only
at the affine monomorphisms locally of finite type, where
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType`
proves it outright.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.coverSiteObject`: the chart as an object of the big
  fppf site of the base.
* `AlgebraicGeometry.TwistedDoubledOrigin.isAlgebraicSpace_quadraticGaloisTwistedDoubledOrigin`:
  **Stacks 03FN's algebraic-space clause** — `X = U/R` is an algebraic space over the affine
  line, with **no hypothesis** beyond the site conventions.
* `AlgebraicGeometry.TwistedDoubledOrigin.surjective_toQuotientSheaf_twistedRelation` and
  `AlgebraicGeometry.TwistedDoubledOrigin.etale_toQuotientSheaf_twistedRelation`: the quotient
  map from the chart is surjective and étale.
* `AlgebraicGeometry.TwistedDoubledOrigin.isQuasiCompactSpace_quadraticGaloisTwistedDoubledOrigin`:
  the quotient is quasi-compact as an algebraic space, the chart being affine. This is Stacks
  03E3 for this example, and the first half of Stacks 03KI's quasi-compactness clause; the
  second half, Stacks 073B part (1), additionally needs the affine line to be quasi-separated as
  an algebraic space, which this development does not yet have.

## Implementation notes

*The tag.* The sentence "it is easy to see that `R` is an étale equivalence relation on `U`
over `S` and hence `X = U/R` is an algebraic space by Theorem 02WW" is a clause of Stacks 03FN
in its own right — it is what the parts (1)–(7) of the example are then asserted *about* — so
`isAlgebraicSpace_quadraticGaloisTwistedDoubledOrigin` carries the tag, under the clause key
`X = U/R is an algebraic space`. Stacks 02WW is the general criterion and keeps its own tag
elsewhere; what is registered here is the criterion *applied to this example*, which is what
03FN asserts. The remaining declarations of this file are not 03FN clauses and stay untagged.

*What this does not give.* The quotient is not representable —
`AlgebraicGeometry.TwistedDoubledOrigin.quadraticGaloisTwistedDoubledOrigin_not_representable`,
Stacks 03FN's `not_scheme` clause — so no shortcut through representability exists, and that is
consistent: the chart is relatively representable with étale surjective, not with an
isomorphism.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
  [IsGalois k K]

/-- The chart is an object of the big fppf site of the base: it is of finite type and
quasi-compact over the base, so its size is below the site's cutoff. -/
theorem contains_cover (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    B.Contains (cover K) :=
  have _hfp : LocallyOfFinitePresentation (coverMap k K) := (coverMap_fppf k K).2.1
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (coverMap k K) hS

/-- The chart of the twisted doubled origin, as an object of the big fppf site of the base. -/
noncomputable def coverSiteObject (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    BigFppfOver B (base k) hS :=
  Over.mk (⟨(coverOverBase k K).hom⟩ : B.obj (contains_cover k K B hS) ⟶ B.obj hS)

/-- The underlying scheme of `AlgebraicGeometry.TwistedDoubledOrigin.coverSiteObject` is the
chart, hence affine. -/
instance isAffine_coverSiteObject (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    IsAffine ((BigFppfOver.toScheme B (base k) hS).obj (coverSiteObject k K B hS)) :=
  inferInstanceAs (IsAffine (cover K))

/-- **Stacks 03FN.** The Galois twist of the affine line with zero doubled **is an algebraic
space**: `R` is an étale equivalence relation on `U` over `S`, and so the quotient `X = U/R` is
an algebraic space. No descent hypothesis is needed.

The relation is an affine morphism into the self-product of the chart, so
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isAffineHom` applies: Stacks 0265 is
unconditional for an affine étale equivalence relation. -/
@[stacks 03FN "X = U/R is an algebraic space"]
theorem isAlgebraicSpace_quadraticGaloisTwistedDoubledOrigin
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    IsAlgebraicSpace B (base k) hS
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj :=
  @Space.isAlgebraicSpace_quotientSheaf_of_isAffineHom B (base k) hS
    (coverSiteObject k K B hS) _ _ (twistedRelation k K σ)
    (twistedRelation_isEtaleEquivalenceRelation k K hdegree σ hσ) _
    (isAffineHom_twistedRelation_left k K hdegree σ hσ)

/-- **The quotient map of the twisted doubled origin is surjective**, with no descent
hypothesis. -/
theorem surjective_toQuotientSheaf_twistedRelation
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (base k) hS)))
      (yonedaEquiv.symm
        ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
          (Over.post B.inclusion) (twistedRelation k K σ)).app
          (Opposite.op (coverSiteObject k K B hS))
          (𝟙 ((Over.post B.inclusion).obj (coverSiteObject k K B hS))))) :=
  @Space.surjective_toQuotientSheaf_of_isAffineHom B (base k) hS
    (coverSiteObject k K B hS) _ _ (twistedRelation k K σ)
    (twistedRelation_isEtaleEquivalenceRelation k K hdegree σ hσ) _
    (isAffineHom_twistedRelation_left k K hdegree σ hσ)

/-- **The quotient map of the twisted doubled origin is étale**, with no descent
hypothesis. -/
theorem etale_toQuotientSheaf_twistedRelation
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (base k) hS)))
      (yonedaEquiv.symm
        ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
          (Over.post B.inclusion) (twistedRelation k K σ)).app
          (Opposite.op (coverSiteObject k K B hS))
          (𝟙 ((Over.post B.inclusion).obj (coverSiteObject k K B hS))))) :=
  @Space.etale_toQuotientSheaf_of_isAffineHom B (base k) hS
    (coverSiteObject k K B hS) _ _ (twistedRelation k K σ)
    (twistedRelation_isEtaleEquivalenceRelation k K hdegree σ hσ) _
    (isAffineHom_twistedRelation_left k K hdegree σ hσ)

/-- **The Galois twist of the affine line with zero doubled is quasi-compact as an algebraic
space.** Its chart is the affine line over `K`, which is affine hence compact, and the quotient
map is surjective and étale.

This is Stacks 03E3 for this example. It is the source half of Stacks 03KI's quasi-compactness
clause: Stacks 073B part (1),
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace`, turns it into
quasi-compactness of the structure morphism once the target is known to be quasi-separated as an
algebraic space. -/
theorem isQuasiCompactSpace_quadraticGaloisTwistedDoubledOrigin
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    Space.IsQuasiCompactSpace B (base k) hS
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj := by
  have _hmul := Space.isMultiplicative_presheaf_etale B (base k) hS
  refine ⟨coverSiteObject k K B hS, _, Scheme.compactSpace_of_isAffine _,
    surjective_toQuotientSheaf_twistedRelation k K hdegree σ hσ B hS, fun V φ hφ ↦ ?_⟩
  exact MorphismProperty.comp_mem _ φ _ hφ
    (etale_toQuotientSheaf_twistedRelation k K hdegree σ hσ B hS)

end AlgebraicGeometry.TwistedDoubledOrigin

end
