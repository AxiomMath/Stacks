module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart of a quotient sheaf costs nothing once its diagonal is representable

Stacks 0265 was reduced in `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic` to
*two* instances of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`, at two
properties neither of which implies the other: the monomorphisms locally of finite type for the
diagonal, and the property of Stacks 02W8 together with surjectivity and étaleness for the
chart. This file removes the second one.

Doing so removes the affineness of `U` as well, so the results below are the content of
Stacks 02WW and not only of Stacks 0265: **no theorem in this file asks anything of the
underlying scheme of `U`.** See the implementation note *Why `U` need not be affine*.

## Main results

* `AlgebraicGeometry.Space.presheaf_quotientChart_of_relativelyRepresentable_diag`: the chart of
  the quotient sheaf of an étale equivalence relation on an arbitrary object of the site is
  representable with `P`, for every property `P` which is stable under base change, Zariski
  local on the target, satisfies fppf descent and holds for the target map of the relation —
  **with no effective descent hypothesis at all**, only representability of the diagonal of the
  quotient sheaf.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_diagDescent`,
  `AlgebraicGeometry.Space.surjective_toQuotientSheaf_of_diagDescent` and
  `AlgebraicGeometry.Space.etale_toQuotientSheaf_of_diagDescent`: the three conclusions of
  Stacks 0265, for an arbitrary `U`, from effective descent along the covering sieves at the
  monomorphisms locally of finite type **alone**.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase`,
  `AlgebraicGeometry.Space.surjective_toQuotientSheaf_of_affineBase` and
  `AlgebraicGeometry.Space.etale_toQuotientSheaf_of_affineBase`: the same three conclusions from
  the *affine-base body* of that predicate at the monomorphisms locally of finite type, with no
  cardinal hypothesis and no hypothesis on the site. For an arbitrary `U` these are the
  algebraicity and chart halves of Stacks 02WW; the presentation they assemble into is
  `AlgebraicGeometry.Space.quotientPresentation_of_affineBase` of
  `StacksFrontier.AlgebraicGeometry.Spaces.EtaleEquivalenceRelationQuotient`.

**Read `_of_affineBase` carefully: the "affine base" is the base object of the *descent
predicate*, not `U`.** It is the object `a` over which the covering sieve of the hypothesis `H`
lives, which `H` restricts to the affine case; `U` itself is unrestricted throughout. A reader
who takes the suffix to be a hypothesis on `U` will conclude that these statements are the
affine case of Stacks 0265, which they are not.

## Implementation notes

*Why the chart needs no descent hypothesis.* The hypothesis
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` does two things at once: it makes
the descended fibre product `X ×[Y] yoneda.obj a` *representable*, and it transports the
property `P` to the descended morphism. The second half is free — it is
`AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`, which assumes the
representability and asks for nothing else. For the chart of a quotient sheaf the first half is
free as well, because the fibre product in question is
`yoneda.obj U ×[U/R] yoneda.obj a`, a base change of the chart along a point of the quotient,
and `CategoryTheory.Functor.relativelyRepresentable.of_diag` makes *every* morphism from a
representable presheaf to a presheaf with representable diagonal relatively representable. The
diagonal of the quotient sheaf is exactly what
`AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf` provides.

So the chart's descent hypothesis was never load-bearing: both of its instances in
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` are consequences of the diagonal's.

*Why `U` need not be affine.* Affineness of `U` entered Stacks 0265 at exactly one point, and
it is a point this route does not pass through. The property at which the chart's instance was
taken is the one of Stacks 02W8 together with surjectivity and étaleness, and of its five
conjuncts only *separatedness* of the target map of the relation needs `U` affine — that is
`Stacks.Groupoids.isSeparated_target_of_isAffine`, and for a general `U` the morphism
`U ×_S U ⟶ U` is not separated. But
`AlgebraicGeometry.Space.presheaf_quotientChart_of_relativelyRepresentable_diag` does not ask
for separatedness: it asks for a property stable under base change, Zariski local on the target
and fppf descending, and `AlgebraicGeometry.Surjective ⊓ AlgebraicGeometry.Etale` is such a
property, by `MorphismProperty.IsStableUnderBaseChange.inf`,
`MorphismProperty.IsLocalAtTarget.inf` and `MorphismProperty.DescendsAlong.inf`. Taking `P`
there rather than the larger property of Stacks 02W8 discharges the hypothesis from
`Stacks.Groupoids.surjective_target` and étaleness of the relation, neither of which looks at
`U`. The remaining inputs were already general:
`AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf` never used affineness, and
`AlgebraicGeometry.Space.exists_isPullback_quotientChart` records the base change of the chart
along a lifted point as the relation pulled back along that lift, with the Cartesian square and
the surjectivity, étaleness, local quasi-finiteness and local finite type of its projection all
properties of the target map alone.

The consequence is that the general case of Stacks 02WW costs exactly what the affine case of
Stacks 0265 costs, under literally the same descent hypothesis. In particular the reduction the
source performs — replacing `U` by a disjoint union of affine opens, using invariance of the
quotient under restriction along a surjective étale morphism (Stacks 02VH) and openness of the
quotient of a restriction (Stacks 02WU), then glueing by Stacks 02WR and Stacks 02WQ — is not
needed in this library, and none of those tags is invoked here.

*What this buys.* The diagonal's instance is taken at
`MorphismProperty.monomorphisms Scheme.{u} ⊓ AlgebraicGeometry.LocallyOfFiniteType`, a property
*below the monomorphisms*, and for such a property
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms`
reduces the predicate to its affine-base body with **no cardinal hypothesis**: the glueing step
is paid for by `AlgebraicGeometry.Scheme.size_le_of_mono`. The chart's instance, taken at a
property containing the surjective étale morphisms, admits no such payment — the coproduct of
`κ` copies of `Spec A` over `Spec A` is surjective, étale, separated, locally quasi-finite and
locally of finite type for every `κ`, so no size bound exists and the affine-base reduction
there would need regularity of the site's cutoff, which the site does not supply: a cardinal
which is both a strong prelimit and regular is inaccessible, while
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` and
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof` are all the site guarantees. Routing the
chart through the diagonal therefore removes the one cardinal obligation of Stacks 0265 rather
than merely renaming it.

Nothing here carries a tag. The results are the conclusions of Stacks 0265 and, for an
arbitrary `U`, of Stacks 02WW, but both rest on the undischarged hypothesis `H`.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : BigFppfOver B S hS)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {R : Over S}
  (j : PreRelation R ((Over.post B.inclusion).obj U))
  [IsEtaleEquivalenceRelation j]

/-! ### The chart from the diagonal -/

/-- **The chart of a quotient sheaf is representable with `P`, with no effective descent
hypothesis.** Let `j` be an étale equivalence relation on an object `U` of the big fppf site of
`S`, and let `P` be a property of morphisms of schemes which is stable under base change,
Zariski local on the target, satisfies fppf descent and holds for the target map of `j`. If the
diagonal of the quotient sheaf is relatively representable, then the chart
`yoneda.obj U ⟶ U/R` is relatively representable with `P`.

This is `AlgebraicGeometry.Space.presheaf_quotientChart` with its hypothesis
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` replaced by representability of
the diagonal. The covering sieve is the same one — the sieve of arrows along which the given
point of the quotient lifts to `U`, which is covering because the chart is locally surjective,
and over whose arrows the base change of the chart is described by
`AlgebraicGeometry.Space.exists_isPullback_quotientChart`. What changes is how it is consumed:
the representability of `yoneda.obj U ×[U/R] yoneda.obj a` comes from
`CategoryTheory.Functor.relativelyRepresentable.of_diag` instead of from the descent
hypothesis, and the property `P` is then recovered on the descended morphism by the
unconditional `AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`. -/
@[sga "3 IV 4.6.5" "Converse direction", sga "3 VIB 9.2" "(vii)"]
theorem presheaf_quotientChart_of_relativelyRepresentable_diag
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hdiag : yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj))
    (hP : P j.target.left) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) := by
  have hri : MorphismProperty.RespectsIso (P.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
    isLocallySurjective_quotientChart _ _ _ _
  have hchart : yoneda.relativelyRepresentable
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
    hdiag.of_diag _
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 ?_
  intro a h
  refine presheaf_of_coveringSieve_of_descendsAlong h
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ h) hchart)
    (T := Presheaf.imageSieve
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
      (yonedaEquiv h)) (Presheaf.imageSieve_mem _ _ _) ?_
  intro b q hq
  obtain ⟨xx, hxx⟩ := hq
  have hfac : yoneda.map q ≫ h =
      yoneda.map xx ≫
        quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j :=
    yonedaEquiv.injective <| by
      rw [← yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      exact hxx.symm
  obtain ⟨d, p₁, p₂, sq, ⟨t, sqs⟩, -, -, -, -⟩ :=
    exists_isPullback_quotientChart B S hS U j b xx
  have sq' : IsPullback (yoneda.map p₁) (yoneda.map p₂)
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
      (yoneda.map q ≫ h) := by rw [hfac]; exact sq
  exact presheaf_pullback_snd_of_isPullback sq' (MorphismProperty.of_isPullback sqs hP)

/-! ### The three conclusions of Stacks 0265, for an arbitrary `U`, from the representable
diagonal -/

/-- Being surjective and étale is stable under base change. -/
private theorem isStableUnderBaseChange_surjective_inf_etale :
    MorphismProperty.IsStableUnderBaseChange
      (@Surjective.{u} ⊓ @Etale : MorphismProperty Scheme.{u}) := .inf

/-- Being surjective and étale is Zariski local on the target. -/
private theorem isZariskiLocalAtTarget_surjective_inf_etale :
    IsZariskiLocalAtTarget (@Surjective.{u} ⊓ @Etale : MorphismProperty Scheme.{u}) :=
  have _he : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- Being surjective and étale satisfies fppf descent. -/
private theorem descendsAlong_fppf_surjective_inf_etale :
    MorphismProperty.DescendsAlong
      (@Surjective.{u} ⊓ @Etale : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _h1 := Space.surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  have _h2 := Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  MorphismProperty.DescendsAlong.inf

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The target map of an étale equivalence relation is surjective and étale: it is étale by
definition and the reflexivity morphism of the relation is a section of it. No hypothesis on
`U` is used. -/
private theorem surjective_inf_etale_target :
    (@Surjective.{u} ⊓ @Etale : MorphismProperty Scheme.{u}) j.target.left :=
  ⟨surjective_target j, inferInstance⟩

/-- The chart of the quotient sheaf is representable with surjective étale morphisms, from the
representable diagonal. -/
private theorem presheaf_surjective_inf_etale_quotientChart
    (hdiag : yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} ⊓ @Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
  have _hbc := isStableUnderBaseChange_surjective_inf_etale.{u}
  have _h1 := isZariskiLocalAtTarget_surjective_inf_etale.{u}
  have _h2 := descendsAlong_fppf_surjective_inf_etale.{u}
  presheaf_quotientChart_of_relativelyRepresentable_diag B S hS U j _ hdiag
    (surjective_inf_etale_target B S hS U j)

/-- **Stacks 0265, surjectivity of the quotient map, from the representable diagonal alone.**
This is `AlgebraicGeometry.Space.presheaf_surjective_quotientChart` with its effective descent
hypothesis replaced by representability of the diagonal of the quotient sheaf — and with no
hypothesis on `U`, which is what Stacks 02WW needs. -/
theorem presheaf_surjective_quotientChart_of_relativelyRepresentable_diag
    (hdiag : yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
      fun _ _ _ hf => hf.1) _
    (presheaf_surjective_inf_etale_quotientChart B S hS U j hdiag)

/-- **Stacks 0265, étaleness of the quotient map, from the representable diagonal alone.** This
is `AlgebraicGeometry.Space.presheaf_etale_quotientChart` with its effective descent hypothesis
replaced by representability of the diagonal of the quotient sheaf — and with no hypothesis on
`U`, which is what Stacks 02WW needs. -/
theorem presheaf_etale_quotientChart_of_relativelyRepresentable_diag
    (hdiag : yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
      fun _ _ _ hf => hf.2) _
    (presheaf_surjective_inf_etale_quotientChart B S hS U j hdiag)

/-- **Stacks 0265 and the algebraicity half of Stacks 02WW, from the representable diagonal
alone.** The quotient sheaf of an étale equivalence relation on an object of the big fppf site
of `S` is an algebraic space over `S` as soon as its diagonal is relatively representable. The
underlying scheme of the object is arbitrary, which is the generality of Stacks 02WW.

The two hypotheses of `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` have collapsed to
one: the chart's instance is a consequence of the diagonal's, by
`AlgebraicGeometry.Space.presheaf_quotientChart_of_relativelyRepresentable_diag`. -/
theorem isAlgebraicSpace_quotientSheaf_of_relativelyRepresentable_diag
    (hdiag : yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)) :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf_of_chart B S hS U j hdiag
    (presheaf_surjective_quotientChart_of_relativelyRepresentable_diag B S hS U j hdiag)
    (presheaf_etale_quotientChart_of_relativelyRepresentable_diag B S hS U j hdiag)

/-- **Stacks 0265, surjectivity of the quotient map in the shape the source states it, from the
representable diagonal alone.** This is
`AlgebraicGeometry.Space.surjective_toQuotientSheaf` with its effective descent hypothesis
replaced by representability of the diagonal of the quotient sheaf. -/
theorem surjective_toQuotientSheaf_of_relativelyRepresentable_diag
    (hdiag : yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) := by
  rw [yonedaEquiv_symm_app_toQuotientSheaf]
  exact presheaf_surjective_quotientChart_of_relativelyRepresentable_diag B S hS U j hdiag

/-- **Stacks 0265, étaleness of the quotient map in the shape the source states it, from the
representable diagonal alone.** This is `AlgebraicGeometry.Space.etale_toQuotientSheaf` with its
effective descent hypothesis replaced by representability of the diagonal of the quotient
sheaf. -/
theorem etale_toQuotientSheaf_of_relativelyRepresentable_diag
    (hdiag : yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) := by
  rw [yonedaEquiv_symm_app_toQuotientSheaf]
  exact presheaf_etale_quotientChart_of_relativelyRepresentable_diag B S hS U j hdiag

/-! ### The three conclusions of Stacks 0265, for an arbitrary `U`, from one descent hypothesis

The hypothesis is the one the *diagonal* needs, at the monomorphisms locally of finite type. The
chart's hypothesis, at the property of Stacks 02W8 together with surjectivity and étaleness, has
disappeared: it is a consequence of the diagonal's. With it went the affineness of `U`, so these
are the conclusions of Stacks 02WW and not only of Stacks 0265.
-/

section DiagDescent

variable (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
  (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType))

include hdesc in
/-- **Stacks 0265, the algebraic-space property, conditional on effective descent along the
covering sieves at the monomorphisms locally of finite type and on nothing else.**

This is `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_coveringSieveDescent` with
its hypothesis moved down from the property of Stacks 02W8 to the property the base changes of
the diagonal actually carry. The move matters: the smaller property lies below the
monomorphisms, where
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms`
reduces the predicate to its affine-base body with no cardinal hypothesis, while at the chart's
property no such reduction exists. It does **not** carry `@[stacks 0265]`: the descent hypothesis
is undischarged. -/
theorem isAlgebraicSpace_quotientSheaf_of_diagDescent :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf_of_relativelyRepresentable_diag B S hS U j
    (relativelyRepresentable_diag_quotientSheaf B S hS U j hdesc)

include hdesc in
/-- **Stacks 0265, surjectivity of the quotient map, conditional on effective descent along the
covering sieves at the monomorphisms locally of finite type and on nothing else.** It does
**not** carry `@[stacks 0265]`: the descent hypothesis is undischarged. -/
theorem surjective_toQuotientSheaf_of_diagDescent :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  surjective_toQuotientSheaf_of_relativelyRepresentable_diag B S hS U j
    (relativelyRepresentable_diag_quotientSheaf B S hS U j hdesc)

include hdesc in
/-- **Stacks 0265, étaleness of the quotient map, conditional on effective descent along the
covering sieves at the monomorphisms locally of finite type and on nothing else.** It does
**not** carry `@[stacks 0265]`: the descent hypothesis is undischarged. -/
theorem etale_toQuotientSheaf_of_diagDescent :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  etale_toQuotientSheaf_of_relativelyRepresentable_diag B S hS U j
    (relativelyRepresentable_diag_quotientSheaf B S hS U j hdesc)

end DiagDescent

/-! ### The three conclusions of Stacks 0265, and of Stacks 02WW, from the affine-base body,
with no cardinal hypothesis

`H` below is the body of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` at the
monomorphisms locally of finite type with the single extra assumption that the base object is
affine; no other quantifier is restricted and no other hypothesis is added. Nothing is asked of
the site's cutoff.

The object restricted to the affine case by `H` is the base object `a` of the covering sieve,
**not** `U`: the three theorems below hold for an object `U` of the site whose underlying
scheme is arbitrary, which is the generality of Stacks 02WW rather than of Stacks 0265. The
suffix `_of_affineBase` names the hypothesis, not a hypothesis on `U`.
-/

section AffineBase

variable (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
  Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
  Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
  ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
    IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
    T ∈ BigFppfOver.topology B S hS a →
    (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
      ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
        (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map q ≫ h))) →
    ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h))

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
include H in
/-- The affine-base body at the monomorphisms locally of finite type gives the full predicate at
that property, by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms`:
a monomorphism locally of finite type is a monomorphism, so the size hypothesis of the
affine-base reduction is discharged by `AlgebraicGeometry.Scheme.size_le_of_mono` and nothing is
asked of the site's cutoff. -/
theorem isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType_of_affineBase :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  have _h1 := monomorphisms_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms
    (fun _ _ _ hg => hg.1) H

include H in
/-- **Stacks 0265, and the algebraicity half of Stacks 02WW, conditional on the affine-base
body of effective descent along the covering sieves at the monomorphisms locally of finite
type — and on nothing else.** No cardinal hypothesis and no hypothesis on the site's cutoff is
used, and the underlying scheme of `U` is arbitrary; the "affine base" of the name is the base
object of the descent predicate `H`, not `U`.

It does **not** carry `@[stacks 0265]` or `@[stacks 02WW]`: the hypothesis `H` is
undischarged. -/
theorem isAlgebraicSpace_quotientSheaf_of_affineBase :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType_of_affineBase
      B S hS H)

include H in
/-- **Stacks 0265, surjectivity of the quotient map, conditional on the affine-base body of
effective descent along the covering sieves at the monomorphisms locally of finite type — and on
nothing else.** The underlying scheme of `U` is arbitrary, so together with étaleness this is
also the chart half of Stacks 02WW. It does **not** carry `@[stacks 0265]` or
`@[stacks 02WW]`: the hypothesis `H` is undischarged. -/
theorem surjective_toQuotientSheaf_of_affineBase :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  surjective_toQuotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType_of_affineBase
      B S hS H)

include H in
/-- **Stacks 0265, étaleness of the quotient map, conditional on the affine-base body of
effective descent along the covering sieves at the monomorphisms locally of finite type — and on
nothing else.** The underlying scheme of `U` is arbitrary, so together with surjectivity this is
also the chart half of Stacks 02WW. It does **not** carry `@[stacks 0265]` or
`@[stacks 02WW]`: the hypothesis `H` is undischarged. -/
theorem etale_toQuotientSheaf_of_affineBase :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  etale_toQuotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType_of_affineBase
      B S hS H)

end AffineBase

end AlgebraicGeometry.Space

end
