module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartFibreComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChowProjProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSiteLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementDistinct

/-!
# The valuative lifting condition for the cover of Stacks 089J

`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion` reduces properness of the
morphism `X' ⟶ X` of Stacks 089J to seven hypotheses. Six are discharged elsewhere in this
directory; the seventh is the valuative lifting condition itself — the substance of the claim
inside the proof of Stacks 089J — and this file proves it.

The argument of the source, link by link. Let `R` be a valuation ring with fraction field `K`
and let a valuative square for `ψ : X' ⟶ X` be given whose generic point factors through the
scheme-theoretically dense open `V ⊆ X'`.

1. The bottom edge `Spec R ⟶ X` lifts through the surjective flat chart `c : W ⟶ X` after
   enlarging `R` to a dominating valuation ring `R'` with fraction field `K'`; this is Stacks
   089F in the form `exists_dominatingExtension_lift_of_isFlat_of_isSurjective`.
2. The generic point of the enlarged square, read through `V`, is `d` *pairwise distinct*
   morphisms `Spec K' ⟶ W` over one `K'`-point of `X`: distinctness is
   `SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne`.
3. The restriction to `Spec K'` of the lift produced in step 1 is a further morphism
   `Spec K' ⟶ W` over that same point, so it is *one of the `d`*, provided `d` is at least the
   universal fibre-degree bound of Stacks 03JL; this is
   `exists_eq_of_hasUniversallyBoundedFibers`.
4. Say it is the `k`-th. Then the `k`-th projection `gₖ` of the scheme-theoretic image carries
   the square, and `gₖ` is proper, so the square has a scheme-level lift
   `Spec R' ⟶ Z` by `exists_valuativeLift_of_isProper` and `isProper_chowProj`.
5. That lift has range inside `X' = ⋃ᵢ gᵢ⁻¹(W)` and is therefore a morphism of site objects
   `Spec R' ⟶ X'`, by `exists_hom_chowCoverObj_of_comp_chowProj_eq`.
6. Its upper triangle holds because the inclusion of `X'` into the scheme-theoretic image is a
   monomorphism; its lower triangle is the uniqueness half of Stacks 03IX for the separated
   structure morphism of `X`, which is Stacks 03KU.

## Main definitions

* `AlgebraicGeometry.Space.denseToImage` and `AlgebraicGeometry.Space.chowCoverObjι`: the
  morphism `V ⟶ Z` onto the scheme-theoretic image, and the inclusion `X' ⟶ Z`, retyped so
  that their types mention `AlgebraicGeometry.Space.chowImageObj` itself.
* `AlgebraicGeometry.Space.chowCoverIncl`: the `i`-th open immersion `gᵢ⁻¹(W) ⟶ X'`, retyped.
* `AlgebraicGeometry.Space.chowDenseIncl`: **the inclusion `V ⟶ X'` of the dense open into the
  cover**, obtained by factoring `V ⟶ Z` through the `i`-th member of the covering of `X'`; it
  does not depend on `i`.

## Main results

* `AlgebraicGeometry.Space.eq_of_comp_eq_of_isSeparated`: two morphisms from the spectrum of a
  valuation ring to an algebraic space separated over the base which agree on the spectrum of
  the fraction field are equal. This is Stacks 03KU, applied.
* `AlgebraicGeometry.Space.exists_hom_chowCoverObj_of_valuativeLift`: steps 4 and 5 — a
  matching of the enlarged lift with the `k`-th projection yields a morphism of site objects
  `Spec R' ⟶ X'` lifting the generic point through `V`.
* `AlgebraicGeometry.Space.exists_dominatingExtension_lift_of_lift_generic`: steps 1, 2, 3 and
  6, with the output of step 5 taken as a hypothesis; the conclusion is the valuative lifting
  condition for one square.
* `AlgebraicGeometry.Space.exists_degreeBound_match`: the fibre-degree bound of Stacks 03JL, in
  the shape step 3 consumes — there is a `d` for which the matching holds.
* `AlgebraicGeometry.Space.yoneda_map_chowDenseIncl_comp`: the inclusion of the dense open
  followed by the glued morphism is a projection of the complement of the diagonals followed by
  the chart.
* `AlgebraicGeometry.Space.exists_dominatingExtension_lift_chowCover`: **the valuative lifting
  condition for the morphism `X' ⟶ X` of Stacks 089J**, which is the hypothesis `hexists` of
  `AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`.

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute:
Stacks 089F is carried by
`AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat`, Stacks 03JL by
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`, Stacks 03IX by
`AlgebraicGeometry.Space.ValuativeCriterion`, Stacks 03KU by
`AlgebraicGeometry.Space.valuativeCriterion_uniqueness_of_isSeparated`, Stacks 01KF by
Mathlib's `AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion` and Stacks 01WC by
`AlgebraicGeometry.isProper_of_isProjectiveMorphism`.

What is **not** proved is properness of `X' ⟶ X`, which also needs the six formal hypotheses of
the refined valuative criterion; see
`StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverProper`. Surjectivity of the cover, which
holds only over the open where the fibre degree is minimal, and the induction on that degree,
are not addressed anywhere in this file.

Three side conditions are hypotheses rather than consequences: that the compactification is
proper over the base (in Stacks 089J it is projective), that the chart is flat and surjective
(in Stacks 089J it is surjective étale), and that the algebraic space is separated over the
base (which Stacks 089J assumes). The glued morphism `ψ` and the family `ρ` are also
hypotheses, supplied by `AlgebraicGeometry.Space.exists_chowCoverHom`.

## References

* [Stacks Project, Tag 01KF](https://stacks.math.columbia.edu/tag/01KF)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03KU](https://stacks.math.columbia.edu/tag/03KU)
* [Stacks Project, Tag 089F](https://stacks.math.columbia.edu/tag/089F)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The left column of a valuative square

The morphism `Spec K ⟶ Spec R` of site objects attached to a valuation ring and its fraction
field already exists as `AlgebraicGeometry.Space.ValuativeSquare.fracHom` inside
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/ValuativeCriteria.lean`, but it is `private`
there, so it is re-derived here — as a `private` reducible abbreviation, for raw valuation-ring
data rather than for a square, which is the form the statements below need. -/

/-- The morphism of site objects `Spec K ⟶ Spec R` attached to a valuation ring in the chosen
big site and its fraction field. A file-local copy of the `private`
`AlgebraicGeometry.Space.ValuativeSquare.fracHom`, taking the ring data rather than a
square. -/
private abbrev specArrow {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S) :
    siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
      siteObject B S hS hR base :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    B.obj hK ⟶ B.obj hR)

/-- The commuting square of a valuative square, read through
`AlgebraicGeometry.Space.specArrow`. -/
private theorem square_comm' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (q : ValuativeSquare f) :
    q.generic ≫ f =
      yoneda.map (specArrow B S hS q.ring_mem q.field_mem q.base) ≫ q.special :=
  q.comm

/-- A morphism of site objects `Spec K ⟶ Spec R` whose underlying scheme morphism is
`Spec.map (algebraMap R K)` is `AlgebraicGeometry.Space.specArrow`. -/
private theorem eq_specArrow_of_map_toScheme_eq {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S)
    (σ : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
      siteObject B S hS hR base)
    (hσ : (BigFppfOver.toScheme B S hS).map σ =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    σ = specArrow B S hS hR hK base :=
  BigFppfOver.map_toScheme_injective B S hS (hσ.trans rfl)

/-- **Two morphisms from the spectrum of a valuation ring to an algebraic space separated over
the base which agree on the spectrum of the fraction field are equal.**

The morphism `σ` of site objects is the left column of a valuative square: it is pinned down by
the hypothesis `hσ`, the functor to schemes being faithful.

This is the uniqueness half of the valuative criterion of Stacks 03IX, which a separated
morphism satisfies by Stacks 03KU: the two morphisms are two lifts of one valuative square for
the structure morphism of the space, whose bottom edge is forced because the target of the
structure morphism is terminal.

It is what makes the lower triangle of the lift constructed below commute. -/
theorem eq_of_comp_eq_of_isSeparated (X : AlgebraicSpaces B S hS)
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X.obj))
    (R K : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S)
    (σ : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
      siteObject B S hS hR base)
    (hσ : (BigFppfOver.toScheme B S hS).map σ =
      Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (a b : yoneda.obj (siteObject B S hS hR base) ⟶ X.obj)
    (h : yoneda.map σ ≫ a = yoneda.map σ ≫ b) : a = b := by
  obtain rfl := eq_specArrow_of_map_toScheme_eq B S hS hR hK base σ hσ
  exact congrArg ValuativeSquare.Lift.map
    ((valuativeCriterion_uniqueness_of_isSeparated
        ((isTerminal_yoneda_obj_base B S hS).from X.obj) hXsep
      { R := R, K := K, ring_mem := hR, field_mem := hK, base := base
        generic := yoneda.map (specArrow B S hS hR hK base) ≫ a
        special := (isTerminal_yoneda_obj_base B S hS).from _
        comm := (isTerminal_yoneda_obj_base B S hS).hom_ext _ _ }).allEq
      { map := a, generic_comm := rfl
        special_comm := (isTerminal_yoneda_obj_base B S hS).hom_ext _ _ }
      { map := b, generic_comm := h.symm
        special_comm := (isTerminal_yoneda_obj_base B S hS).hom_ext _ _ })

variable (X : AlgebraicSpaces B S hS) (Wch : BigFppfOver B S hS)
    (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)

/-! ### The dense open inside the cover

`AlgebraicGeometry.Space.chowImageObj` is defined as
`AlgebraicGeometry.Space.schemeImageObj` of `AlgebraicGeometry.Space.chowToOverProd`, and
`AlgebraicGeometry.Space.chowCoverObj` as `AlgebraicGeometry.Space.unionPreimageObj` of it.
Both are ordinary definitions, so a term whose type mentions one spelling is not type-correct
at the transparency `rw` and `simp` work at when the goal mentions the other. The two
definitions below are the same morphisms, retyped so that every statement in this file is on
one side of that line. -/

/-- The morphism `V ⟶ Z` onto the scheme-theoretic image of Stacks 089J, retyped so that its
target is `AlgebraicGeometry.Space.chowImageObj`. -/
def denseToImage : V ⟶ chowImageObj B S hS X Wch c hc hsep Yo j n V e :=
  toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)

/-- **The composite of `V ⟶ Z` with the `i`-th projection is the `i`-th projection of the
complement of the diagonals followed by the open immersion of the chart**, for
`AlgebraicGeometry.Space.denseToImage`. -/
theorem denseToImage_comp_chowProj (i : Fin (n + 1)) :
    (BigFppfOver.toScheme B S hS).map (denseToImage B S hS X Wch c hc hsep Yo j n V e) ≫
        chowProj B S hS X Wch c hc hsep Yo j n V e i =
      (BigFppfOver.toScheme B S hS).map
          (SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i) ≫
        (BigFppfOver.toScheme B S hS).map j :=
  toSchemeImageObj_comp_chowProj B S hS X Wch c hc hsep Yo j n V e i

variable (hj : _root_.AlgebraicGeometry.IsOpenImmersion
  ((BigFppfOver.toScheme B S hS).map j))

/-- The inclusion `X' ⟶ Z` of the cover of Stacks 089J into the scheme-theoretic image,
retyped so that its source is `AlgebraicGeometry.Space.chowCoverObj` and its target
`AlgebraicGeometry.Space.chowImageObj`. -/
def chowCoverObjι :
    chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj ⟶
      chowImageObj B S hS X Wch c hc hsep Yo j n V e :=
  unionPreimageObjι B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
    (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj)

/-- Under `BigFppfOver.toScheme`, the inclusion `AlgebraicGeometry.Space.chowCoverObjι` is the
inclusion of the open union of the preimages `gᵢ⁻¹(W)` of the chart into the
scheme-theoretic image. -/
theorem chowCoverObjι_toScheme :
    (BigFppfOver.toScheme B S hS).map (chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj) =
      (unionPreimageOpens B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj)).ι :=
  unionPreimageObjι_toScheme B S hS _ _ _

/-- **The inclusion of the cover into the scheme-theoretic image is a monomorphism**, being the
inclusion of an open of the site. -/
theorem mono_chowCoverObjι :
    Mono (chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj) :=
  mono_openSubHom B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e) _

/-- The `i`-th open immersion `gᵢ⁻¹(W) ⟶ X'` of the covering of the cover of Stacks 089J,
retyped so that its target is `AlgebraicGeometry.Space.chowCoverObj`. -/
def chowCoverIncl (i : Fin (n + 1)) :
    preimageObj B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e)
        (chartOpensRange B S hS j hj) i ⟶
      chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj :=
  unionPreimageIncl B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
    (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj) i

/-- **The inclusion `V ⟶ X'` of the scheme-theoretically dense open into the cover of Stacks
089J.** It is the factorisation `AlgebraicGeometry.Space.chowDenseLift` of `V ⟶ Z` through the
`i`-th member `gᵢ⁻¹(W)` of the covering of `X'`, followed by the inclusion of that member; it
does not depend on `i` by `AlgebraicGeometry.Space.chowDenseIncl_eq`. -/
def chowDenseIncl (i : Fin (n + 1)) :
    V ⟶ chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj :=
  chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫
    chowCoverIncl B S hS X Wch c hc hsep Yo j n V e hj i

/-- The presheaf morphism underlying `AlgebraicGeometry.Space.chowDenseIncl` is the Yoneda
image of the factorisation through the `i`-th member of the covering, followed by that of the
inclusion of the member. -/
theorem yoneda_map_chowDenseIncl (i : Fin (n + 1)) :
    yoneda.map (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i) =
      yoneda.map (chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i) ≫
        yoneda.map (chowCoverIncl B S hS X Wch c hc hsep Yo j n V e hj i) :=
  yoneda.map_comp _ _

/-- **The inclusion of the dense open into the cover, followed by the inclusion of the cover
into the scheme-theoretic image, is the morphism `V ⟶ Z`.** -/
theorem chowDenseIncl_comp_chowCoverObjι (i : Fin (n + 1)) :
    chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i ≫
        chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj =
      denseToImage B S hS X Wch c hc hsep Yo j n V e := by
  show (chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫
      unionPreimageIncl B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e)
        (chartOpensRange B S hS j hj) i) ≫
      unionPreimageObjι B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj) =
    toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)
  rw [Category.assoc, unionPreimageIncl_comp_unionPreimageObjι]
  exact chowDenseLift_comp_preimageObjι B S hS X Wch c hc hsep Yo j n V e hj i

/-- **The inclusion of the dense open into the cover does not depend on the member of the
covering it is read through**, the inclusion of the cover into the scheme-theoretic image being
a monomorphism. -/
theorem chowDenseIncl_eq (i i' : Fin (n + 1)) :
    chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i =
      chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i' :=
  have := mono_chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj
  (cancel_mono (chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj)).1 (by
    rw [chowDenseIncl_comp_chowCoverObjι, chowDenseIncl_comp_chowCoverObjι])

/-! ### The scheme-level valuative lift, promoted to the site -/

/-- **Steps 4 and 5 of the valuative-criterion argument of Stacks 089J.** Suppose the
restriction `Spec K' ⟶ W` of a lift `ll : Spec R' ⟶ W` of the bottom edge through the chart
agrees with the `k`-th projection of the complement of the diagonals read through
`gg : Spec K' ⟶ V`. Then the generic point `Spec K' ⟶ V ⟶ X'` extends to `Spec R' ⟶ X'`.

The `k`-th projection `gₖ : Z ⟶ Y` of the scheme-theoretic image is proper by
`AlgebraicGeometry.Space.isProper_chowProj`, so the square formed by `gg` composed with
`V ⟶ Z` and by `ll` composed with `W ⟶ Y` has a scheme-level lift `z : Spec R' ⟶ Z` by
`AlgebraicGeometry.exists_valuativeLift_of_isProper`. Its composite with `gₖ` factors through
the chart, so its range lies in `gₖ⁻¹(W) ⊆ X'` and it is a morphism of site objects into `X'`
by `AlgebraicGeometry.Space.exists_hom_chowCoverObj_of_comp_chowProj_eq`. That it lifts the
generic point is read off by cancelling the monomorphism `X' ⟶ Z`. -/
theorem exists_hom_chowCoverObj_of_valuativeLift
    (hYo : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Yo.hom))
    (vV : V ⟶ chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj)
    (hvV : vV ≫ chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj =
      denseToImage B S hS X Wch c hc hsep Yo j n V e)
    (R' K' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (hR : B.Contains (Spec (.of R')))
    (hK : B.Contains (Spec (.of K'))) (base : Spec (.of R') ⟶ S)
    (σ : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ base) ⟶
      siteObject B S hS hR base)
    (hσ : (BigFppfOver.toScheme B S hS).map σ =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')))
    (gg : siteObject B S hS hK
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ base) ⟶ V)
    (ll : siteObject B S hS hR base ⟶ Wch) (k : Fin (n + 1))
    (hk : σ ≫ ll =
      gg ≫ SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e k) :
    ∃ ws : siteObject B S hS hR base ⟶
        chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj,
      σ ≫ ws = gg ≫ vV := by
  obtain rfl := eq_specArrow_of_map_toScheme_eq B S hS hR hK base σ hσ
  have hproper := isProper_chowProj B S hS X Wch c hc hsep Yo j n V e k hYo
  have hjw : (BigFppfOver.toScheme B S hS).map j ≫ B.inclusion.map Yo.hom =
      B.inclusion.map Wch.hom := by
    rw [show (BigFppfOver.toScheme B S hS).map j = B.inclusion.map j.left from rfl,
      ← Functor.map_comp, Over.w]
  have hcomm : ((BigFppfOver.toScheme B S hS).map gg ≫
        (BigFppfOver.toScheme B S hS).map
          (denseToImage B S hS X Wch c hc hsep Yo j n V e)) ≫
        chowProj B S hS X Wch c hc hsep Yo j n V e k =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        ((BigFppfOver.toScheme B S hS).map ll ≫ (BigFppfOver.toScheme B S hS).map j) := by
    rw [Category.assoc, denseToImage_comp_chowProj, ← Category.assoc, ← Functor.map_comp, ← hk,
      Functor.map_comp, Category.assoc]
    rfl
  obtain ⟨z, hz1, hz2⟩ := exists_valuativeLift_of_isProper
    (chowProj B S hS X Wch c hc hsep Yo j n V e k) R' K'
    ((BigFppfOver.toScheme B S hS).map gg ≫
      (BigFppfOver.toScheme B S hS).map (denseToImage B S hS X Wch c hc hsep Yo j n V e))
    ((BigFppfOver.toScheme B S hS).map ll ≫ (BigFppfOver.toScheme B S hS).map j) hcomm
  have hzstruct : z ≫ B.inclusion.map (chowImageObj B S hS X Wch c hc hsep Yo j n V e).hom =
      B.inclusion.map (siteObject B S hS hR base).hom := by
    rw [← chowProj_comp_hom B S hS X Wch c hc hsep Yo j n V e k, ← Category.assoc, hz2,
      Category.assoc, hjw,
      show (BigFppfOver.toScheme B S hS).map ll = B.inclusion.map ll.left from rfl,
      ← Functor.map_comp, Over.w]
  obtain ⟨ws, hws⟩ := exists_hom_chowCoverObj_of_comp_chowProj_eq B S hS X Wch c hc hsep Yo j n
    V e hj (siteObject B S hS hR base) z hzstruct k ((BigFppfOver.toScheme B S hS).map ll) hz2
  refine ⟨ws, ?_⟩
  have := mono_chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj
  have hws' : (BigFppfOver.toScheme B S hS).map
      (ws ≫ chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj) = z :=
    ((BigFppfOver.toScheme B S hS).map_comp ws _).trans
      ((congrArg (fun t ↦ (BigFppfOver.toScheme B S hS).map ws ≫ t)
        (chowCoverObjι_toScheme B S hS X Wch c hc hsep Yo j n V e hj)).trans hws)
  refine (cancel_mono (chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj)).1 ?_
  rw [Category.assoc, Category.assoc, hvV]
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  calc (BigFppfOver.toScheme B S hS).map (specArrow B S hS hR hK base ≫
          ws ≫ chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj)
      = (BigFppfOver.toScheme B S hS).map (specArrow B S hS hR hK base) ≫
          (BigFppfOver.toScheme B S hS).map
            (ws ≫ chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj) :=
        (BigFppfOver.toScheme B S hS).map_comp _ _
    _ = Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ z := by rw [hws']; rfl
    _ = (BigFppfOver.toScheme B S hS).map gg ≫
          (BigFppfOver.toScheme B S hS).map
            (denseToImage B S hS X Wch c hc hsep Yo j n V e) := hz1
    _ = (BigFppfOver.toScheme B S hS).map
          (gg ≫ denseToImage B S hS X Wch c hc hsep Yo j n V e) :=
        ((BigFppfOver.toScheme B S hS).map_comp _ _).symm

/-! ### The valuative lifting condition -/

/-- **Steps 1, 2, 3 and 6 of the valuative-criterion argument of Stacks 089J**, with the output
of steps 4 and 5 taken as the hypothesis `hlift`.

The data is a morphism `ψ : X' ⟶ X` of presheaves out of an object of the site, an object `V`
with a morphism `vV : V ⟶ X'`, and `n + 1` morphisms `pr k : V ⟶ Wch` to a chart
`c : Wch ⟶ X`, pairwise distinct on points (`hprne`) and lying over one morphism to `X`
(`hpr`), with `vV` followed by `ψ` the `i₀`-th of them followed by the chart (`hψ`).

The conclusion is the valuative lifting condition of the refined valuative criterion for one
valuative square `q` of `ψ` whose generic point factors through `vV`: after a dominating
extension of the valuation ring the square has a lift.

Step 1 is Stacks 089F in the form
`AlgebraicGeometry.Space.exists_dominatingExtension_lift_of_isFlat_of_isSurjective`, which
needs the chart to be flat and surjective. Step 3 is the hypothesis `hmatch`, which says the
`n + 1` morphisms exhaust the morphisms to the chart over a field-valued point of `X`; it is
available as soon as `n + 1` is at least the fibre-degree bound of Stacks 03JL, by
`AlgebraicGeometry.Space.exists_degreeBound_match`. Step 6 is
`AlgebraicGeometry.Space.eq_of_comp_eq_of_isSeparated`, which needs `X` separated over the
base.

Nothing about properness or about liftability of `ψ` is assumed: `hlift` produces a morphism of
site objects out of the spectrum of the enlarged valuation ring and says only that it restricts
to the generic point on the spectrum of the fraction field. That its composite with `ψ` is the
bottom edge of the square — the lower triangle, which is what a lift of the square asserts — is
*proved* here, from separatedness of `X` over the base. -/
theorem exists_dominatingExtension_lift_of_lift_generic (X : AlgebraicSpaces B S hS)
    (Wch : BigFppfOver B S hS) (c : yoneda.obj Wch ⟶ X.obj)
    (hcf : IsFlat B S hS c) (hcs : IsSurjective B S hS c)
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X.obj))
    (V X' : BigFppfOver B S hS) (vV : V ⟶ X') (ψ : yoneda.obj X' ⟶ X.obj)
    (n : ℕ) (pr : Fin (n + 1) → (V ⟶ Wch)) (i₀ : Fin (n + 1))
    (hψ : yoneda.map vV ≫ ψ = yoneda.map (pr i₀) ≫ c)
    (hpr : ∀ k k', yoneda.map (pr k) ≫ c = yoneda.map (pr k') ≫ c)
    (hprne : ∀ (T : BigFppfOver B S hS) (gf : T ⟶ V) (_ : points B S hS (yoneda.obj T))
      (a b : Fin (n + 1)), a ≠ b → gf ≫ pr a ≠ gf ≫ pr b)
    (hmatch : ∀ (K' : Type u) (_ : Field K') (T' : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec (CommRingCat.of K'))
      (ξ : yoneda.obj T' ⟶ X.obj) (w : Fin (n + 1) → (T' ⟶ Wch)),
      (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w →
        ∀ v : T' ⟶ Wch, yoneda.map v ≫ c = ξ → ∃ k, v = w k)
    (hlift : ∀ (R' K' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R'] [Field K']
      [Algebra R' K'] [IsFractionRing R' K'] (hR : B.Contains (Spec (.of R')))
      (hK : B.Contains (Spec (.of K'))) (base : Spec (.of R') ⟶ S)
      (σ : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ base) ⟶
        siteObject B S hS hR base),
      (BigFppfOver.toScheme B S hS).map σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' K')) →
      ∀ (gg : siteObject B S hS hK
          (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ base) ⟶ V)
        (ll : siteObject B S hS hR base ⟶ Wch) (k : Fin (n + 1)),
        σ ≫ ll = gg ≫ pr k →
          ∃ ws : siteObject B S hS hR base ⟶ X', σ ≫ ws = gg ≫ vV)
    (q : ValuativeSquare ψ)
    (g : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ yoneda.obj V)
    (hg : g ≫ yoneda.map vV = q.generic) :
    ∃ dx : q.DominatingExtension, Nonempty dx.square.Lift := by
  obtain ⟨dx, l, hl⟩ := exists_dominatingExtension_lift_of_isFlat_of_isSurjective B S hS X.2 q
    Wch c hcf hcs
  refine ⟨dx, ?_⟩
  obtain ⟨gg, hggy⟩ : ∃ gg : siteObject B S hS dx.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap dx.square.R dx.square.K)) ≫
        dx.square.base) ⟶ V,
      yoneda.map gg = yoneda.map dx.genericOver ≫ g :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  obtain ⟨ll, hlly⟩ : ∃ ll : siteObject B S hS dx.square.ring_mem dx.square.base ⟶ Wch,
      yoneda.map ll = l := ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hgen : yoneda.map gg ≫ yoneda.map vV = dx.square.generic := by
    rw [hggy, Category.assoc, hg, dx.generic_comm]
  have hwξ : ∀ k, yoneda.map (gg ≫ pr k) ≫ c = yoneda.map (gg ≫ pr i₀) ≫ c := by
    intro k
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hpr k i₀]
  have hwinj : Function.Injective (fun k ↦ gg ≫ pr k) := by
    intro a b hab
    by_contra hne
    exact hprne _ gg (fieldSpecPoint B S hS dx.square.field_mem _) a b hne hab
  have hv : yoneda.map (specArrow B S hS dx.square.ring_mem dx.square.field_mem
        dx.square.base ≫ ll) ≫ c = yoneda.map (gg ≫ pr i₀) ≫ c := by
    rw [Functor.map_comp, Category.assoc, hlly, hl, ← square_comm' B S hS dx.square, ← hgen,
      Category.assoc, hψ, Functor.map_comp, Category.assoc]
  obtain ⟨k, hk⟩ := hmatch dx.square.K inferInstance _ (Iso.refl _)
    (yoneda.map (gg ≫ pr i₀) ≫ c) (fun k ↦ gg ≫ pr k) hwξ hwinj
    (specArrow B S hS dx.square.ring_mem dx.square.field_mem dx.square.base ≫ ll) hv
  obtain ⟨ws, hws⟩ := hlift dx.square.R dx.square.K dx.square.ring_mem dx.square.field_mem
    dx.square.base (specArrow B S hS dx.square.ring_mem dx.square.field_mem dx.square.base)
    rfl gg ll k hk
  have hgenlift : yoneda.map (specArrow B S hS dx.square.ring_mem dx.square.field_mem
      dx.square.base) ≫ yoneda.map ws = dx.square.generic := by
    rw [← Functor.map_comp, hws, Functor.map_comp, hgen]
  refine ⟨{ map := yoneda.map ws, generic_comm := hgenlift, special_comm := ?_ }⟩
  refine eq_of_comp_eq_of_isSeparated B S hS X hXsep dx.square.R dx.square.K
    dx.square.ring_mem dx.square.field_mem dx.square.base
    (specArrow B S hS dx.square.ring_mem dx.square.field_mem dx.square.base) rfl _ _ ?_
  rw [← Category.assoc, hgenlift, square_comm' B S hS dx.square]

/-- **The fibre-degree bound of Stacks 03JL, in the shape the matching step of Stacks 089J
consumes.** A chart with universally bounded fibres has a `d` — here written `n + 1` — such that
`d` pairwise distinct morphisms from the spectrum of a field to the chart lying over one
morphism to the algebraic space are *all* of them.

This is `AlgebraicGeometry.Space.exists_eq_of_hasUniversallyBoundedFibers` instantiated at
`m = n + 1` with `n` the bound it produces; it is the choice of `d` with which the proof of
Stacks 089J forms the complement of the diagonals. -/
theorem exists_degreeBound_match {Xp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Wch : BigFppfOver B S hS) (c : yoneda.obj Wch ⟶ Xp)
    (hbound : HasUniversallyBoundedFibers B S hS Wch c) :
    ∃ n : ℕ, ∀ (K' : Type u) (_ : Field K') (T' : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec (CommRingCat.of K'))
      (ξ : yoneda.obj T' ⟶ Xp) (w : Fin (n + 1) → (T' ⟶ Wch)),
      (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w →
        ∀ v : T' ⟶ Wch, yoneda.map v ≫ c = ξ → ∃ k, v = w k := by
  obtain ⟨nb, hnb⟩ := exists_eq_of_hasUniversallyBoundedFibers B S hS Wch c hbound
  exact ⟨nb, fun K' hK' T' eT' ξ w hw hwinj v hv ↦
    hnb K' hK' T' eT' ξ (nb + 1) (Nat.le_succ nb) w hw hwinj v hv⟩

/-- **The inclusion of the dense open into the cover, followed by the glued morphism
`ψ : X' ⟶ X`, is the `i`-th projection of the complement of the diagonals followed by the
chart.**

The data `ρ`, `ψ` with the two properties `hρ` and `hψ` is what
`AlgebraicGeometry.Space.exists_chowCoverHom` produces. -/
theorem yoneda_map_chowDenseIncl_comp (X : AlgebraicSpaces B S hS)
    (Wch : BigFppfOver B S hS) (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ)
    (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (ρ : ∀ i : Fin (n + 1), preimageObj B S hS
      (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
      (chowProj B S hS X Wch c hc hsep Yo j n V e)
      (chartOpensRange B S hS j hj) i ⟶ Wch)
    (hρ : ∀ i, chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫ ρ i =
      SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i)
    (ψ : yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj) ⟶ X.obj)
    (hψ : ∀ i, yoneda.map (chowCoverIncl B S hS X Wch c hc hsep Yo j n V e hj i) ≫ ψ =
      yoneda.map (ρ i) ≫ c)
    (i : Fin (n + 1)) :
    yoneda.map (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i) ≫ ψ =
      yoneda.map (SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i)
        ≫ c := by
  rw [yoneda_map_chowDenseIncl, Category.assoc, hψ i, ← Category.assoc,
    ← Functor.map_comp, hρ i]

/-- **The valuative lifting condition for the morphism `X' ⟶ X` of Stacks 089J.** This is the
hypothesis `hexists` of `AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion` for the
glued morphism `ψ` of `AlgebraicGeometry.Space.exists_chowCoverHom`, with the dense open
`V ⊆ X'` being `AlgebraicGeometry.Space.chowDenseIncl`.

The data `ρ` and `ψ` with their two properties is exactly what
`AlgebraicGeometry.Space.exists_chowCoverHom` produces: `ρ i` is the morphism from the `i`-th
member `gᵢ⁻¹(W)` of the covering of `X'` to the chart, restricting on `V` to the `i`-th
projection of the complement of the diagonals, and `ψ` is the morphism glued out of the
`ρ i ≫ c`.

The three remaining inputs are: `hmatch`, the fibre-degree bound of Stacks 03JL at `n + 1`,
which `AlgebraicGeometry.Space.exists_degreeBound_match` supplies for a suitable `n`; properness
of the compactification over the base, which in Stacks 089J holds because the compactification
is projective; and separatedness of `X` over the base, which Stacks 089J assumes.

This is the single claim inside the proof of Stacks 089J whose verification the source calls
the substance of the argument, and it is proved here in full. -/
theorem exists_dominatingExtension_lift_chowCover (X : AlgebraicSpaces B S hS)
    (Wch : BigFppfOver B S hS) (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (hcs : IsSurjective B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hYo : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Yo.hom))
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X.obj))
    (hmatch : ∀ (K' : Type u) (_ : Field K') (T' : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec (CommRingCat.of K'))
      (ξ : yoneda.obj T' ⟶ X.obj) (w : Fin (n + 1) → (T' ⟶ Wch)),
      (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w →
        ∀ v : T' ⟶ Wch, yoneda.map v ≫ c = ξ → ∃ k, v = w k)
    (ρ : ∀ i : Fin (n + 1), preimageObj B S hS
      (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
      (chowProj B S hS X Wch c hc hsep Yo j n V e)
      (chartOpensRange B S hS j hj) i ⟶ Wch)
    (hρ : ∀ i, chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫ ρ i =
      SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i)
    (ψ : yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj) ⟶ X.obj)
    (hψ : ∀ i, yoneda.map (chowCoverIncl B S hS X Wch c hc hsep Yo j n V e hj i) ≫ ψ =
      yoneda.map (ρ i) ≫ c)
    (i₀ : Fin (n + 1))
    (q : ValuativeSquare ψ)
    (g : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ yoneda.obj V)
    (hg : g ≫ yoneda.map (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i₀) =
      q.generic) :
    ∃ dx : q.DominatingExtension, Nonempty dx.square.Lift := by
  have hdense := yoneda_map_chowDenseIncl_comp B S hS X Wch c hc hsep Yo j n V e hj ρ hρ ψ hψ
  refine exists_dominatingExtension_lift_of_lift_generic B S hS X Wch c
    (isFlat_of_isEtale B S hS hc) hcs hXsep V
    (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj)
    (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i₀) ψ n
    (SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e) i₀
    (hdense i₀)
    (fun k k' ↦ SpacesEtale.yoneda_map_diagonalComplementProj_comp_chart_eq B S hS X Wch c hc
      hsep (n + 1) V e k k')
    (fun T gf t a b hab heq ↦ ?_) hmatch (fun R' K' _ _ _ _ _ _ hR hK base σ hσ gg ll k hk ↦ ?_)
    q g hg
  · exact SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne B S hS X Wch c hc hsep (n + 1)
      V e (yoneda.map gf) t hab
      (by rw [← Functor.map_comp, ← Functor.map_comp, heq])
  · refine exists_hom_chowCoverObj_of_valuativeLift B S hS X Wch c hc hsep Yo j n V e hj hYo
      (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i₀) ?_ R' K' hR hK base σ hσ gg ll
      k hk
    exact chowDenseIncl_comp_chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj i₀

end AlgebraicGeometry.Space

end
