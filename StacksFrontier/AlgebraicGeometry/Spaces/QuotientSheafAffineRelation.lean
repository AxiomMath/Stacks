module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal

/-!
# Stacks 0265 for an affine étale equivalence relation, with no descent hypothesis

Stacks 0265 — that the quotient sheaf of an étale equivalence relation on an affine object of
the big fppf site of `S` is an algebraic space with surjective étale quotient map — was reduced
in `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal` to a *single*
hypothesis: effective descent along the covering sieves of the site at the monomorphisms locally
of finite type, which is what representability of the diagonal of the quotient sheaf needs.

That hypothesis is not available at the monomorphisms locally of finite type. It *is* available
one step further down, at the affine monomorphisms locally of finite type, where
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType`
proves it outright. This file shows that the smaller property is enough whenever the relation
itself is an affine morphism into the self-product of the chart, and so discharges Stacks 0265
for such relations unconditionally.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf_of_isAffineHom`: the
  diagonal of the quotient sheaf of an étale equivalence relation whose relation is an affine
  morphism is relatively representable, with **no descent hypothesis**.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isAffineHom`,
  `AlgebraicGeometry.Space.surjective_toQuotientSheaf_of_isAffineHom`,
  `AlgebraicGeometry.Space.etale_toQuotientSheaf_of_isAffineHom`: the three conclusions of
  Stacks 0265 for an affine étale equivalence relation on an affine object, with **no
  hypothesis**.

## Implementation notes

*Why the affine conjunct is available here.* The base change of the diagonal of the quotient
sheaf along a pair of points of the quotient lifted to the chart is a base change of the
relation `j` itself — this is
`AlgebraicGeometry.Space.exists_isPullback_diag_quotientSheaf`, whose last clause transports to
that base change every property of `j` stable under base change. The four properties the clause
before it reports are what `j` carries for *every* étale equivalence relation; affineness is
not one of them, and is therefore carried as a hypothesis.

*No tag.* These statements do not carry `@[stacks 0265]`: the source asserts the conclusions for
an arbitrary étale equivalence relation, and affineness of the relation is a genuine extra
hypothesis, not a reformulation. The general statement still rests on Stacks 0247.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
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

/-- **The diagonal of the quotient sheaf of an affine étale equivalence relation is
representable, with no descent hypothesis.**

This is `AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf` with its hypothesis
discharged. That theorem takes effective descent along the covering sieves at the monomorphisms
locally of finite type, which is the property the base changes of the diagonal carry for a
general étale equivalence relation and at which the predicate is not available. When `j` is
affine those base changes are affine too, by the last clause of
`AlgebraicGeometry.Space.exists_isPullback_diag_quotientSheaf`, so the predicate is needed only
at `AlgebraicGeometry.affineMonoLocallyOfFiniteType`, where
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType`
proves it. No affineness of `U` is used. -/
theorem relativelyRepresentable_diag_quotientSheaf_of_isAffineHom
    (haff : _root_.AlgebraicGeometry.IsAffineHom j.left) :
    yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).obj) := by
  have _hbc₁ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := .inf
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (_root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u}) := .inf
  have hri : MorphismProperty.RespectsIso
      ((_root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u}).inverseImage
        (BigFppfOver.toScheme B S hS)) := MorphismProperty.RespectsIso.inverseImage _ _
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
    isLocallySurjective_quotientChart _ _ _ _
  suffices key : ((_root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u}).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf
      (diag (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).obj) from key.rep
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 fun a h => ?_
  refine isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType B S hS _
    (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).property
    (isSheaf_prod (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j)
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j)) h
    (Presheaf.imageSieve
        (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yonedaEquiv (h ≫ prod.fst)) ⊓
      Presheaf.imageSieve
        (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yonedaEquiv (h ≫ prod.snd)))
    ((BigFppfOver.topology B S hS).intersection_covering
      (Presheaf.imageSieve_mem _ _ _) (Presheaf.imageSieve_mem _ _ _)) ?_
  rintro b q ⟨⟨xx, hxx⟩, ⟨yy, hyy⟩⟩
  have hfac : yoneda.map q ≫ h =
      prod.lift
        (yoneda.map xx ≫
          quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yoneda.map yy ≫
          quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) := by
    refine prod.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd] <;>
      refine yonedaEquiv.injective ?_ <;>
      rw [yonedaEquiv_comp (yoneda.map _)
          (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j),
        yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality]
    exacts [hxx.symm, hyy.symm]
  obtain ⟨d, p, sq, hm, -, -, hloft, hstable⟩ :=
    exists_isPullback_diag_quotientSheaf B S hS U j b xx yy
  rw [← hfac] at sq
  exact presheaf_pullback_snd_of_isPullback sq
    ⟨⟨hm, hloft⟩, hstable (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      _root_.AlgebraicGeometry.isAffineHom_isStableUnderBaseChange haff⟩

/-- **Stacks 0265, the algebraic-space property, for an affine étale equivalence relation, with
no hypothesis.** The quotient sheaf of an étale equivalence relation on an object of the big fppf
site of `S` is an algebraic space over `S` whenever the relation is an affine morphism into the
self-product of the chart; no affineness of the object is used.

It does **not** carry `@[stacks 0265]`: affineness of the relation is an extra hypothesis, and
the general statement still rests on Stacks 0247. -/
theorem isAlgebraicSpace_quotientSheaf_of_isAffineHom
    (haff : _root_.AlgebraicGeometry.IsAffineHom j.left) :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf_of_relativelyRepresentable_diag B S hS U j
    (relativelyRepresentable_diag_quotientSheaf_of_isAffineHom B S hS U j haff)

/-- **Stacks 0265, surjectivity of the quotient map, for an affine étale equivalence relation,
with no hypothesis.** It does **not** carry `@[stacks 0265]`: affineness of the relation is an
extra hypothesis. -/
theorem surjective_toQuotientSheaf_of_isAffineHom
    (haff : _root_.AlgebraicGeometry.IsAffineHom j.left) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  surjective_toQuotientSheaf_of_relativelyRepresentable_diag B S hS U j
    (relativelyRepresentable_diag_quotientSheaf_of_isAffineHom B S hS U j haff)

/-- **Stacks 0265, étaleness of the quotient map, for an affine étale equivalence relation, with
no hypothesis.** It does **not** carry `@[stacks 0265]`: affineness of the relation is an extra
hypothesis. -/
theorem etale_toQuotientSheaf_of_isAffineHom
    (haff : _root_.AlgebraicGeometry.IsAffineHom j.left) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  etale_toQuotientSheaf_of_relativelyRepresentable_diag B S hS U j
    (relativelyRepresentable_diag_quotientSheaf_of_isAffineHom B S hS U j haff)

end AlgebraicGeometry.Space

end
