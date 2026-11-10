module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismPropertyTopology.FppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginNotSeparated

/-!
# The separation properties of the twisted doubled origin

The fifth assertion of the example is that `X = U/R` is not separated but is locally
separated and quasi-separated.  All three halves are proved here.

Each is a property of the diagonal of `X` over the base, and each is equivalent to the
corresponding property of the relation `j : R ⟶ U ×_S U`: the relation is the base change of
the diagonal along the square of the chart, which is a surjective étale chart of `X ×_S X`.
The relation is an open immersion
(`AlgebraicGeometry.TwistedDoubledOrigin.isOpenImmersion_twistedRelation_left`), hence an
immersion, which gives local separatedness; and it is an affine morphism
(`AlgebraicGeometry.TwistedDoubledOrigin.isAffineHom_twistedRelation_left`), hence
quasi-compact, which gives quasi-separatedness.  Conversely the relation is a represented
base change of the diagonal, so it would be a closed immersion were `X` separated; it is
not, because the puncture is not closed in the chart.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.relationSiteObject`,
  `AlgebraicGeometry.TwistedDoubledOrigin.relationFirstSite` and
  `AlgebraicGeometry.TwistedDoubledOrigin.relationSecondSite` present the relation and its two
  projections inside the big fppf site over the base.

## Main results

* `AlgebraicGeometry.Space.presheaf_diag_quotientSheaf`: a property of scheme morphisms which
  is stable under base change and fppf local on the target passes from the relation of an
  étale equivalence relation to the diagonal of its quotient sheaf, when that quotient is an
  algebraic space, and
  `AlgebraicGeometry.Space.prop_relation_left_of_presheaf_diag` is the converse, which needs
  no locality hypothesis.
* `TwistedDoubledOrigin.isLocallySeparatedOver_quadraticGaloisTwistedDoubledOrigin` and
  `TwistedDoubledOrigin.isQuasiSeparatedOver_quadraticGaloisTwistedDoubledOrigin`:
  **Stacks 03FN, part (5)** — the quotient is locally separated and quasi-separated over the
  base, and
  `AlgebraicGeometry.TwistedDoubledOrigin.not_isSeparatedOver_quadraticGaloisTwistedDoubledOrigin`
  — it is not separated over the base.

## Implementation notes

`AlgebraicGeometry.Space.presheaf_diag_quotientSheaf` is the quotient-sheaf form of
`AlgebraicGeometry.Space.presheaf_diag_of_kernelPair`: the kernel pair of the chart is the
relation by Stacks 02WV, and the morphism `R ⟶ U ⨯ U` of the site it produces has the same
underlying morphism of schemes as `j : R ⟶ U ×_S U`, because `Over.post` of the inclusion of
the site preserves binary products.  It is the analogue for an arbitrary étale equivalence
relation of `AlgebraicGeometry.Space.presheaf_diag_actionQuotient`, which does the same for a
finite group action.

The relation of the twisted doubled origin is `U ⨿ (U ∖ {0})`, whose structure morphism to
the base is locally of finite type (it is so on each summand) and quasi-compact (the source is
affine), so the relation is an object of the site; its two projections are then morphisms of
the site, and the pre-relation they present is the one the quotient is formed from.

Non-separatedness is read off the same cartesian square: the relation is literally a
represented base change of the diagonal, so no descent is involved in that direction, and
what has to be excluded is that `j : R ⟶ U ×_S U` be a closed immersion.  Under the splitting
`U ×_S U ≅ U ⨿ U` the relation is `U ⨿ (U ∖ {0}) ⟶ U ⨿ U`, whose base change along the second
coprojection is the inclusion of the puncture — a dense proper open of the irreducible chart,
so not closed.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The diagonal of a quotient sheaf inherits the properties of its relation.** Let
`s, t : R ⟶ U` be an étale equivalence relation in the big fppf site of `S` whose quotient
sheaf is an algebraic space.  A property of morphisms of schemes which is stable under base
change and fppf local on the target holds for every represented base change of the diagonal of
the quotient as soon as it holds for `j : R ⟶ U ×_S U`.

This is `AlgebraicGeometry.Space.presheaf_diag_of_kernelPair` applied to the kernel pair of
the quotient map, which is the relation by Stacks 02WV. -/
theorem presheaf_diag_quotientSheaf {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hQ : IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hj : P ((relation B S hS s t).left)) :
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (diag (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj) := by
  set Fsite := BigFppfOver.toScheme B S hS with hFsite
  have hrep : yoneda.relativelyRepresentable (quotientMap B S hS s t) :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t hQ
  have hq_surj := quotientMap_surjective B S hS s t hrep
  have hq_etale := quotientMap_etale B S hS s t hrep
  have hker : IsPullback (yoneda.map t) (yoneda.map s)
      (quotientMap B S hS s t) (quotientMap B S hS s t) := quotientMap_isPullback B S hS s t
  have : HasTerminal (BigFppfOver B S hS) := inferInstance
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  have : PreservesLimitsOfShape (Discrete.{0} PEmpty) B.inclusion := inferInstance
  have : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  set post : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion with hpostdef
  have : PreservesFiniteLimits post := PreservesFiniteLimits.overPost
  set rsite : R ⟶ U ⨯ U := prod.lift t s with hrsite
  set postProd : post.obj (U ⨯ U) ≅ post.obj U ⨯ post.obj U :=
    asIso (prodComparison post U U) with hpostProd
  have hpost : post.map rsite ≫ postProd.hom = relation B S hS s t := by
    apply prod.hom_ext
    · change (post.map rsite ≫ prodComparison post U U) ≫ prod.fst = _
      simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp, hrsite,
        prod.lift_fst]
      exact (prod.lift_fst _ _).symm
    · change (post.map rsite ≫ prodComparison post U U) ≫ prod.snd = _
      simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp, hrsite,
        prod.lift_snd]
      exact (prod.lift_snd _ _).symm
  set targetIso : Fsite.obj (U ⨯ U) ≅ ((post.obj U) ⨯ (post.obj U)).left :=
    (Over.forget S).mapIso postProd with htargetIso
  have htarget : Fsite.map rsite ≫ targetIso.hom = (relation B S hS s t).left := by
    change (Over.forget S).map (post.map rsite) ≫ (Over.forget S).map postProd.hom = _
    rw [← Functor.map_comp, hpost]
    rfl
  have hrsiteP : P (Fsite.map rsite) := by
    have hcomp : P (Fsite.map rsite ≫ targetIso.hom) := by rw [htarget]; exact hj
    exact (MorphismProperty.cancel_right_of_respectsIso P _ targetIso.hom).mp hcomp
  exact presheaf_diag_of_kernelPair B S hS P hQ.diagonal_representable hker hq_surj hq_etale
    hrsiteP

/-- **The relation inherits the properties of the diagonal of its quotient sheaf.** The
converse direction of `AlgebraicGeometry.Space.presheaf_diag_quotientSheaf`, which needs no
locality hypothesis: the relation `j : R ⟶ U ×_S U` *is* a represented base change of the
diagonal of the quotient, along the chart of `X ×_S X` attached to the chart of `X`. -/
theorem prop_relation_left_of_presheaf_diag {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (h : (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (diag (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj)) :
    P ((relation B S hS s t).left) := by
  set Fsite := BigFppfOver.toScheme B S hS with hFsite
  set q := quotientMap B S hS s t with hqdef
  have hker : IsPullback (yoneda.map t) (yoneda.map s) q q := quotientMap_isPullback B S hS s t
  have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  have : PreservesLimitsOfShape (Discrete.{0} PEmpty) B.inclusion := inferInstance
  have : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  set post : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion with hpostdef
  have : PreservesFiniteLimits post := PreservesFiniteLimits.overPost
  set rsite : R ⟶ U ⨯ U := prod.lift t s with hrsite
  set postProd : post.obj (U ⨯ U) ≅ post.obj U ⨯ post.obj U :=
    asIso (prodComparison post U U) with hpostProd
  have hpost : post.map rsite ≫ postProd.hom = relation B S hS s t := by
    apply prod.hom_ext
    · change (post.map rsite ≫ prodComparison post U U) ≫ prod.fst = _
      simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp, hrsite,
        prod.lift_fst]
      exact (prod.lift_fst _ _).symm
    · change (post.map rsite ≫ prodComparison post U U) ≫ prod.snd = _
      simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp, hrsite,
        prod.lift_snd]
      exact (prod.lift_snd _ _).symm
  set targetIso : Fsite.obj (U ⨯ U) ≅ ((post.obj U) ⨯ (post.obj U)).left :=
    (Over.forget S).mapIso postProd with htargetIso
  have htarget : Fsite.map rsite ≫ targetIso.hom = (relation B S hS s t).left := by
    change (Over.forget S).map (post.map rsite) ≫ (Over.forget S).map postProd.hom = _
    rw [← Functor.map_comp, hpost]
    rfl
  have hmono : Mono (prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U)) (yoneda.map prod.snd)) :=
    inferInstanceAs (Mono (prodComparison yoneda U U))
  have hjSq : IsPullback (yoneda.map t ≫ q) (yoneda.map rsite)
      (diag (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj)
      (prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U) ≫ q) (yoneda.map prod.snd ≫ q)) :=
    isPullback_diag_of_isPullback q hker hmono
      (by rw [← Functor.map_comp, hrsite, prod.lift_fst])
      (by rw [← Functor.map_comp, hrsite, prod.lift_snd])
  have hrsiteP : P (Fsite.map rsite) := h.property _ (yoneda.map t ≫ q) rsite hjSq
  rw [← htarget]
  exact MorphismProperty.RespectsIso.postcomp P _ _ hrsiteP

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
  [IsGalois k K]

/-- The relation `R = U ⨿ (U ∖ {0})` is locally of finite type over the base: it is so on
each of the two summands. -/
theorem locallyOfFiniteType_relationOverBase_hom :
    LocallyOfFiniteType (relationOverBase k K).hom := by
  have hfp : LocallyOfFinitePresentation (coverMap k K) := (coverMap_fppf k K).2.1
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  change LocallyOfFiniteType
    (coprod.desc (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K))
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (coprodOpenCover.{u, u} (cover K) (puncturedCover K).toScheme)]
  rintro (⟨⟩ | ⟨⟩)
  · change LocallyOfFiniteType
      (coprod.inl ≫ coprod.desc (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K))
    rw [coprod.inl_desc]
    infer_instance
  · change LocallyOfFiniteType
      (coprod.inr ≫ coprod.desc (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K))
    rw [coprod.inr_desc]
    infer_instance

/-- The relation of the twisted doubled origin is an object of the big fppf site of the
base: it is of finite type over the base, being affine and locally of finite type. -/
theorem contains_relationScheme (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    B.Contains (relationScheme K) := by
  have _hft := locallyOfFiniteType_relationOverBase_hom k K
  have _haff : IsAffineHom (relationOverBase k K).hom :=
    have : IsAffine (relationOverBase k K).left := inferInstanceAs (IsAffine (relationScheme K))
    isAffineHom_of_isAffine _
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (relationOverBase k K).hom hS

/-- The relation of the twisted doubled origin, as an object of the big fppf site of the
base. -/
def relationSiteObject (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    BigFppfOver B (base k) hS :=
  Over.mk (⟨(relationOverBase k K).hom⟩ :
    B.obj (contains_relationScheme k K B hS) ⟶ B.obj hS)

/-- The first projection of the relation, as a morphism of the big fppf site. -/
def relationFirstSite (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    relationSiteObject k K B hS ⟶ coverSiteObject k K B hS :=
  Over.homMk (⟨(relationFirst k K).left⟩ :
    (relationSiteObject k K B hS).left ⟶ (coverSiteObject k K B hS).left)
    (ObjectProperty.hom_ext _ (relationFirst k K).w)

/-- The second projection of the relation, twisted by the Galois automorphism, as a morphism
of the big fppf site. -/
def relationSecondSite (σ : K ≃ₐ[k] K) (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    relationSiteObject k K B hS ⟶ coverSiteObject k K B hS :=
  Over.homMk (⟨(relationSecond k K σ).left⟩ :
    (relationSiteObject k K B hS).left ⟶ (coverSiteObject k K B hS).left)
    (ObjectProperty.hom_ext _ (relationSecond k K σ).w)

/-- The pre-relation presented by the two projections of the relation in the site is the
relation of the twisted doubled origin. -/
theorem relation_relationSecondSite_relationFirstSite (σ : K ≃ₐ[k] K) (B : BigFppfSite.{u})
    (hS : B.Contains (base k)) :
    Space.relation B (base k) hS (relationSecondSite k K σ B hS)
        (relationFirstSite k K B hS) =
      twistedRelation k K σ := rfl

/-- **Stacks 03FN, part (5).** The Galois twist of the affine line with zero doubled is
locally separated over the base: its diagonal is an immersion.

The relation `j : R ⟶ U ×_S U` is an open immersion, hence an immersion, and the diagonal of
the quotient is covered by it. -/
@[stacks 03FN "part (5): X is locally separated over S"]
theorem isLocallySeparatedOver_quadraticGaloisTwistedDoubledOrigin
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    Space.IsLocallySeparatedOver B (base k) hS
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj := by
  have hrel : IsEtaleEquivalenceRelation
      (Space.relation B (base k) hS (relationSecondSite k K σ B hS)
        (relationFirstSite k K B hS)) :=
    twistedRelation_isEtaleEquivalenceRelation k K hdegree σ hσ
  have hQ : IsAlgebraicSpace B (base k) hS
      (quotientSheaf (BigFppfOver.topology B (base k) hS) (Over.post B.inclusion)
        (Space.relation B (base k) hS (relationSecondSite k K σ B hS)
          (relationFirstSite k K B hS))).obj :=
    isAlgebraicSpace_quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS
  have hj : _root_.AlgebraicGeometry.IsImmersion ((twistedRelation k K σ).left) :=
    have := isOpenImmersion_twistedRelation_left k K hdegree σ hσ
    inferInstance
  exact Space.presheaf_diag_quotientSheaf B (base k) hS _ _ hQ
    (@_root_.AlgebraicGeometry.IsImmersion.{u}) hj

/-- **Stacks 03FN, part (5).** The Galois twist of the affine line with zero doubled is
quasi-separated over the base: its diagonal is quasi-compact.

The relation `j : R ⟶ U ×_S U` is an affine morphism, hence quasi-compact, and the diagonal of
the quotient is covered by it. -/
@[stacks 03FN "part (5): X is quasi-separated over S"]
theorem isQuasiSeparatedOver_quadraticGaloisTwistedDoubledOrigin
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    Space.IsQuasiSeparatedOver B (base k) hS
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj := by
  have hrel : IsEtaleEquivalenceRelation
      (Space.relation B (base k) hS (relationSecondSite k K σ B hS)
        (relationFirstSite k K B hS)) :=
    twistedRelation_isEtaleEquivalenceRelation k K hdegree σ hσ
  have hQ : IsAlgebraicSpace B (base k) hS
      (quotientSheaf (BigFppfOver.topology B (base k) hS) (Over.post B.inclusion)
        (Space.relation B (base k) hS (relationSecondSite k K σ B hS)
          (relationFirstSite k K B hS))).obj :=
    isAlgebraicSpace_quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS
  have hj : QuasiCompact ((twistedRelation k K σ).left) :=
    have := isAffineHom_twistedRelation_left k K hdegree σ hσ
    inferInstance
  exact Space.presheaf_diag_quotientSheaf B (base k) hS _ _ hQ
    (@QuasiCompact.{u}) hj

/-- The relation of the twisted doubled origin is not closed in the self-product of the chart
over the base: under the splitting `U ×_S U ≅ U ⨿ U` it is `U ⨿ (U ∖ {0}) ⟶ U ⨿ U`, whose
base change along the second coprojection is the inclusion of the puncture, and the puncture
is a dense proper open of the irreducible chart. -/
theorem not_isClosedImmersion_twistedRelation_left
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    ¬ _root_.AlgebraicGeometry.IsClosedImmersion ((twistedRelation k K σ).left) := by
  intro h
  have hiso : _root_.AlgebraicGeometry.IsClosedImmersion
      ((twistedRelation k K σ).left ≫ (coverSelfProductIso k K hdegree σ hσ).hom) :=
    MorphismProperty.RespectsIso.postcomp
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _ _ h
  rw [twistedRelation_left_comp_coverSelfProductIso k K hdegree σ hσ] at hiso
  exact not_isClosedImmersion_puncturedCover_ι K
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion)
      (isPullback_inr_inr_coprodMap (𝟙 (cover K)) (puncturedCover K).ι).flip hiso)

/-- **Stacks 03FN, part (5).** The Galois twist of the affine line with zero doubled is *not*
separated over the base: its diagonal is not a closed immersion.

The relation is a represented base change of the diagonal, so a closed-immersion diagonal
would make the relation a closed immersion of schemes, which
`AlgebraicGeometry.TwistedDoubledOrigin.not_isClosedImmersion_twistedRelation_left`
excludes. -/
@[stacks 03FN "part (5): X is not separated over S"]
theorem not_isSeparatedOver_quadraticGaloisTwistedDoubledOrigin
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    ¬ Space.IsSeparatedOver B (base k) hS
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj := by
  intro h
  have hrel : IsEtaleEquivalenceRelation
      (Space.relation B (base k) hS (relationSecondSite k K σ B hS)
        (relationFirstSite k K B hS)) :=
    twistedRelation_isEtaleEquivalenceRelation k K hdegree σ hσ
  have h' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (base k) hS)))
      (diag (quotientSheaf (BigFppfOver.topology B (base k) hS) (Over.post B.inclusion)
        (Space.relation B (base k) hS (relationSecondSite k K σ B hS)
          (relationFirstSite k K B hS))).obj) := h
  exact not_isClosedImmersion_twistedRelation_left k K hdegree σ hσ
    (Space.prop_relation_left_of_presheaf_diag B (base k) hS
      (relationSecondSite k K σ B hS) (relationFirstSite k K B hS)
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) h')

end AlgebraicGeometry.TwistedDoubledOrigin

end
