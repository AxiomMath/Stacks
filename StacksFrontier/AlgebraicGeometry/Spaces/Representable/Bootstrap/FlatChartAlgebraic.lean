module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatChartQuotient

/-!
# Condition (3) of Stacks 04S6 is condition (1) applied to the kernel pair of the chart

Let `S` be a scheme contained in a big fppf site.  Condition (3) of [Stacks, Tag 04S6] says that
a sheaf `Y` on the big fppf site of `S` which receives a morphism `f : X ⟶ Y` from an algebraic
space over `S` that is representable by algebraic spaces, surjective, flat and locally of finite
presentation is itself an algebraic space over `S`.  This module proves it from condition (1) of
the same tag — the algebraicity of the fppf quotient sheaf of an equivalence relation of
algebraic spaces whose source and target are flat and locally of finite presentation.

This is the first two paragraphs of the source's proof, in the direction the source takes them:
with `R = X ×_Y X` the kernel pair of `f`, the two projections `t, s : R ⟶ X` are flat and
locally of finite presentation, `j = (t, s)` is an equivalence relation, `Y` is the quotient
sheaf `X/R`, and condition (1) applies to `j`.

## Main results

* `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf`:
  `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` implies
  `AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`.

## Implementation notes

The identification `Y = X/R` is
`AlgebraicGeometry.Space.isIso_quotientSheafDesc_kernelPairRelation`, which takes the three
relative properties of the chart and produces an isomorphism of fppf sheaves out of the quotient
sheaf; the surjectivity of sheaves it consumes is [Stacks, Tag 04S1].  Nothing else about the
topology is used, and in particular no étale-local surjectivity: a flat chart has only
fppf-local sections, which is why this reduction cannot be read off
`AlgebraicGeometry.Space.coreCriterion`, whose chart is smooth.

Flatness and local finite presentation of the first projection of the kernel pair are
`AlgebraicGeometry.Space.hasProperty_pullback_fst_of_isAlgebraicSpace` at the two packaged
properties — the base change of `f` along `f` itself, read at the algebraic-space-valued point
`X` of `Y` rather than at a scheme-valued one, which is where locality of the two properties on
the base enters.  The second projection is the first one composed with the interchange
isomorphism of the fibre product, so it has every property invariant under isomorphism; that
step is `AlgebraicGeometry.Space.prop_pullback_snd_of_pullback_fst`, stated for an arbitrary such
property rather than twice for flatness and local finite presentation.

The hypothesis is not weakened to the conclusion of the library's Stacks 04S6, which is
conditions (5) and (6) of the source: those assume the diagonal of the sheaf being concluded
about to be representable, and are themselves conditional on condition (3).  Condition (1),
carried as `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`, is the clause this reduction
needs and the clause whose proof in the source is the Bootstrap chapter's slicing and
quasi-splitting argument.

## References

* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The second projection of the kernel pair of `f` has every property of morphisms of algebraic
spaces invariant under isomorphism that the first projection has: the two differ by the
interchange isomorphism of the fibre product. -/
theorem prop_pullback_snd_of_pullback_fst
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hR : IsAlgebraicSpace B S hS (pullback f f))
    (h : P (ObjectProperty.homMk (pullback.fst f f) :
      (⟨pullback f f, hR⟩ : AlgebraicSpaces B S hS) ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS))) :
    P (ObjectProperty.homMk (pullback.snd f f) :
      (⟨pullback f f, hR⟩ : AlgebraicSpaces B S hS) ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS)) := by
  let Po : AlgebraicSpaces B S hS := ⟨pullback f f, hR⟩
  let Xo : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let e : Po ≅ Po :=
    ObjectProperty.isoMk (fun G => IsAlgebraicSpace B S hS G) (pullbackSymmetry f f)
  have key := (MorphismProperty.cancel_left_of_respectsIso (P := P) e.hom
    (ObjectProperty.homMk (pullback.fst f f) : Po ⟶ Xo)).mpr h
  rwa [show e.hom ≫ (ObjectProperty.homMk (pullback.fst f f) : Po ⟶ Xo) =
      ObjectProperty.homMk (pullback.snd f f) from
    ObjectProperty.hom_ext _ (pullbackSymmetry_hom_comp_fst f f)] at key

/-- **Condition (3) of Stacks 04S6 from condition (1).** Granted the algebraicity of the fppf
quotient sheaf of an equivalence relation of algebraic spaces over `S` whose source and target
are flat and locally of finite presentation, a sheaf on the big fppf site of `S` which receives a
morphism from an algebraic space over `S` that is representable by algebraic spaces, surjective,
flat and locally of finite presentation is an algebraic space over `S`.

With `R = X ×_Y X` the kernel pair of the chart `f`, the projections `t = pr₁` and `s = pr₂` are
base changes of `f` along `f`, hence flat and locally of finite presentation; `(t, s)` is an
equivalence relation; and `Y` is the quotient sheaf `X/R` because `f` is a surjection of fppf
sheaves.  Condition (1) makes `X/R` an algebraic space, and `Y` inherits it along that
isomorphism. -/
theorem isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf
    (h04S6 : Bootstrap04S6QuotientSheaf B S hS) :
    IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS := by
  intro X Y f hY hX hf hSurj hFlat hLfp
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  -- The kernel pair of the chart is an algebraic space over `S`.
  have hR : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS f f hf hX
  -- Both projections of the kernel pair inherit any such property of the chart.
  have key (P : MorphismProperty (AlgebraicSpaces B S hS))
      [P.IsLocalAtTarget (Topology.fpqc.precoverage.{u, u} B S hS)]
      [P.IsStableUnderBaseChange] (hP : HasProperty B S hS P f hf) :
      P (ObjectProperty.homMk (pullback.fst f f) :
        (⟨pullback f f, hR⟩ : AlgebraicSpaces B S hS) ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS)) ∧
      P (ObjectProperty.homMk (pullback.snd f f) :
        (⟨pullback f f, hR⟩ : AlgebraicSpaces B S hS) ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS)) := by
    have : P.IsLocalAtTarget (Topology.fppf.precoverage.{u, u} B S hS) :=
      MorphismProperty.IsLocalAtTarget.of_le
        (L := Topology.fpqc.precoverage.{u, u} B S hS)
        (fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
    have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hfst := hasProperty_pullback_fst_of_isAlgebraicSpace.{u, u} B S hS P hX f f hf hP
    exact ⟨hfst, prop_pullback_snd_of_pullback_fst B S hS P hX f hR hfst⟩
  obtain ⟨hfstFlat, hsndFlat⟩ := key (flatProperty B S hS) hFlat
  obtain ⟨hfstLfp, hsndLfp⟩ := key (locallyOfFinitePresentationProperty B S hS) hLfp
  -- Condition (1) applies to the kernel-pair relation.
  have hQ : IsAlgebraicSpace B S hS (quotientSheaf (kernelPairRelation f)).obj := by
    refine h04S6 (kernelPairRelation f) hR hX (isEquivalenceRelation_kernelPairRelation f)
      ?_ ?_ ?_ ?_
    · rw [kernelPairRelation_target_left]; exact hfstFlat
    · rw [kernelPairRelation_target_left]; exact hfstLfp
    · rw [kernelPairRelation_source_left]; exact hsndFlat
    · rw [kernelPairRelation_source_left]; exact hsndLfp
  -- The chart presents `Y` as the quotient sheaf of its kernel pair.
  have hiso : IsIso (quotientSheafDesc (kernelPairRelation f) ⟨Y, hY⟩ f
      (isPullback_kernelPairRelation f).w) :=
    isIso_quotientSheafDesc_kernelPairRelation hY hX f hf hSurj hFlat hLfp
  exact hQ.of_iso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
    (asIso (quotientSheafDesc (kernelPairRelation f) ⟨Y, hY⟩ f
      (isPullback_kernelPairRelation f).w)))

end AlgebraicGeometry.Space

end
