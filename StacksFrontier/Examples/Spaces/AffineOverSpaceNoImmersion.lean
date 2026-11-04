module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalHomeomorphismEtaleFailure

/-!
# An affine scheme over an algebraic space need not immerse into affine space

A morphism `Y ⟶ X` of schemes which is locally of finite type with `Y` affine admits an
immersion of `Y` into affine `n`-space over `X` (Stacks 04II).  For a morphism of *algebraic
spaces* this fails, and already over a quasi-separated target: take `Y = 𝔸¹_k` and
`X = 𝔸¹_k/R` the quotient of Stacks 02Z1, where `R = Δ ⨿ Γ` is the diagonal together with
the graph of negation on the punctured line.  A map `Y ⟶ 𝔸^n_X` over `X` is given by regular
functions `f₁, …, fₙ` on `Y`, and its base change along the chart `𝔸^{n+1}_k ⟶ 𝔸^n_X` is

  `{(f₁(t), …, fₙ(t), t)} ⨿ {(f₁(t), …, fₙ(t), -t) : t ≠ 0} ⟶ 𝔸^{n+1}_k`,

which is not an immersion: the generic point of the second summand specializes to the origin
of the first summand downstairs, but not upstairs, where the two summands are disjoint.

## Main definitions

* `AlgebraicGeometry.Space.affineSpaceOver` is relative affine `n`-space
  over a presheaf on the big fppf site of `S`, the product of the presheaf with the
  restricted functor of points of affine `n`-space over `S`.

## Main results

* `Stacks.Examples.exists_finiteType_affine_not_immersion_into_affineSpace`: Stacks 088W,
  the counterexample.
* `Stacks.Examples.AffineOverAlgebraicSpace.isFiniteType_quotientSpaceMap` and
  `Stacks.Examples.AffineOverAlgebraicSpace.not_isImmersion_affineSpaceOver_quotientSpaceMap`
  are the two assertions of Stacks 088W for the concrete witness.

## Implementation notes

The nonexistence assertion ranges over all morphisms `Y ⟶ 𝔸^n_X` over `X`, not just over
those given by a choice of coordinates: `affineSpaceOver` is a product of presheaves, and a
morphism into it over `X` is a morphism into its second factor, which is the restricted
functor of points of `𝔸^n_S`.  Because the second factor is the restriction of a
representable functor along the fully faithful `CategoryTheory.Over.post` of the site's
inclusion, it is itself represented by an object `W` of the site — this is
`AlgebraicGeometry.Space.pointsYonedaIso` — so the second component of such a morphism is
`CategoryTheory.yoneda.map a` for a unique `a : Y ⟶ W`, and the morphism itself is
`CategoryTheory.Limits.prod.lift` of the chart and of `yoneda.map a`.  That is the shape the
base-change argument needs.

Base-changing along the chart is `AlgebraicGeometry.Space.quotientMap_isPullback`, the
identification of the kernel pair of the chart with the relation (Stacks 02WV); the
elementary `isPullback_prod_lift` turns that square into the square exhibiting
`prod.lift s (t ≫ a) : R ⟶ Y ⨯ W` as a base change of `prod.lift q (yoneda.map a)`.  Since
immersions of algebraic spaces are tested after representable base change and `yoneda`
preserves binary products, what comes out is an immersion of *schemes* `R ⟶ 𝔸^{n+1}_k`,
i.e. the displayed morphism, and an immersion of schemes is in particular an embedding on
the underlying spaces.

The two points are the generic point `η` of `𝔸¹_k`, which lies in the punctured line and
specializes to every point, and the image `z` of the zero section.  Negation fixes `z`, so
the two composites `R ⟶ Y ⨯ W` agree on the two relevant points after projecting, giving
the downstairs specialization; upstairs it is refuted by
`not_specializes_coprod_inr_inl`.

The statement carries no hypothesis beyond those of the source.  Stacks 0265 is applied to
the quotient through
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient_of_isAffineHom`,
which needs no effective-descent input because the relation `R ⟶ 𝔸¹_k ×_k 𝔸¹_k` of this
example is an affine morphism, both its source and its target being affine schemes; the
descent that Stacks 0265 consumes is then effective descent at the affine monomorphisms
locally of finite type, which this library proves outright in
`StacksFrontier/AlgebraicGeometry/Descent/AffineHomCoveringSieveDescent.lean`.
Quasi-separatedness is obtained the same way, from the surjectivity and étaleness of the
chart in their unconditional forms.

## References

* [Stacks Project, Tag 088W](https://stacks.math.columbia.edu/tag/088W)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AffineLineInvolution Stacks.Groupoids

universe u v

namespace Stacks.Examples.AffineOverAlgebraicSpace

/-! ### Two elementary lemmas -/

/-- In a coproduct of schemes no point of the right summand specializes to a point of the
left summand: the right summand is closed, and the closure of a point of it meets the left
summand not at all. -/
theorem not_specializes_coprod_inr_inl {X Y : Scheme.{u}} (x : Y) (y : X) :
    ¬ ((Limits.coprod.inr : Y ⟶ X ⨿ Y) x) ⤳ ((Limits.coprod.inl : X ⟶ X ⨿ Y) y) := by
  intro h
  have h' : (Sum.inr x : X ⊕ Y) ⤳ Sum.inl y := by
    refine (AlgebraicGeometry.coprodMk X Y).isInducing.specializes_iff.mp ?_
    rwa [AlgebraicGeometry.coprodMk_inl, AlgebraicGeometry.coprodMk_inr]
  obtain ⟨x', hx'⟩ := h'.mem_closed isClosed_range_inr ⟨x, rfl⟩
  cases hx'

/-- The square exhibiting `prod.lift s (t ≫ a)` as a base change of `prod.lift f a` along
`prod.map g (𝟙 M)`, for a fibre square `IsPullback t s f g` and a morphism `a` out of the
target of `t`.

This is the square along which an immersion into a relative affine space is pulled back to
the relation scheme. -/
theorem isPullback_prod_lift {C : Type u} [Category.{v} C]
    [HasBinaryProducts C] {R A A' X M : C}
    {t : R ⟶ A} {s : R ⟶ A'} {f : A ⟶ X} {g : A' ⟶ X}
    (h : IsPullback t s f g) (a : A ⟶ M) :
    IsPullback (prod.lift s (t ≫ a)) t (prod.map g (𝟙 M)) (prod.lift f a) := by
  apply IsPullback.of_right (h₁₂ := prod.fst) (h₂₂ := prod.fst)
  · simpa only [prod.lift_fst] using h.flip
  · apply prod.hom_ext <;> simp [h.w]
  · exact IsPullback.of_prod_fst_with_id g M

/-! ### The two points of the affine line -/

variable (k : Type u) [Field k]

/-- No point of the graph summand of the relation scheme `R = Δ ⨿ Γ` specializes to a point
of its diagonal summand.  The coproduct is taken in the slice over `Spec k`, where it is
computed on underlying schemes by
`AlgebraicGeometry.overCoprodIso`; the assertion is therefore
`not_specializes_coprod_inr_inl` transported along that comparison isomorphism. -/
theorem not_specializes_relationScheme
    (x : (puncturedAffineLine k).left) (y : (affineLine k).left) :
    ¬ (((Over.forget (Spec (.of k))).map
          (coprod.inr : puncturedAffineLine k ⟶ relationScheme k)) x) ⤳
      (((Over.forget (Spec (.of k))).map
          (coprod.inl : affineLine k ⟶ relationScheme k)) y) := by
  intro h
  set e := overCoprodIso (affineLine k) (puncturedAffineLine k) with he
  have hR : (coprod.inr : (puncturedAffineLine k).left ⟶
        (affineLine k).left ⨿ (puncturedAffineLine k).left) ≫ e.hom =
      (Over.forget (Spec (.of k))).map
        (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) := by
    rw [he, overCoprodIso_hom]
    exact Limits.coprodComparison_inr (Over.forget (Spec (.of k)))
      (A := affineLine k) (B := puncturedAffineLine k)
  have hL : (coprod.inl : (affineLine k).left ⟶
        (affineLine k).left ⨿ (puncturedAffineLine k).left) ≫ e.hom =
      (Over.forget (Spec (.of k))).map
        (coprod.inl : affineLine k ⟶ relationScheme k) := by
    rw [he, overCoprodIso_hom]
    exact Limits.coprodComparison_inl (Over.forget (Spec (.of k)))
      (A := affineLine k) (B := puncturedAffineLine k)
  refine not_specializes_coprod_inr_inl (X := (affineLine k).left)
    (Y := (puncturedAffineLine k).left) x y ?_
  refine e.hom.isEmbedding.isInducing.specializes_iff.mp ?_
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hR, hL]
  exact h

/-- The zero section of the affine line over `Spec k`. -/
noncomputable abbrev originSection : Spec (.of k) ⟶ (affineLine k).left :=
  AffineSpace.homOfVector (𝟙 (Spec (.of k))) (fun _ : PUnit.{u + 1} => 0)

/-- **Negation fixes the zero section.**  Both sides are maps into affine space over
`Spec k`, so they agree as soon as they agree over the base and on the coordinate, where
negating zero gives zero. -/
theorem originSection_comp_affineLineNeg :
    originSection k ≫ (affineLineNeg k).left = originSection k := by
  refine AffineSpace.hom_ext ?_ ?_
  · simp [AffineSpace.homOfVector_over]
  · intro i
    rw [Scheme.Hom.comp_appTop]
    have hneg : ((affineLineNeg k).left).appTop (AffineSpace.coord (Spec (.of k)) i) =
        -AffineSpace.coord (Spec (.of k)) i := by
      rw [affineLineNeg_left, AffineSpace.homOfVector_appTop_coord]
    show (originSection k).appTop
      (((affineLineNeg k).left).appTop (AffineSpace.coord (Spec (.of k)) i)) =
      (originSection k).appTop (AffineSpace.coord (Spec (.of k)) i)
    rw [hneg, map_neg, AffineSpace.homOfVector_appTop_coord]
    simp

/-- **The generic point of the affine line.**  Affine space over `Spec k` on a singleton
index set is the spectrum of a polynomial ring in one variable over `k`, which is
irreducible, so it has a generic point; and the generic point lies in the punctured line,
since it specializes to the point where the coordinate is `1`. -/
theorem exists_genericPoint_affineLine :
    ∃ η : (affineLine k).left,
      η ∈ (puncturedAffineLineOpen k : Set (affineLine k).left) ∧
      ∀ x : (affineLine k).left, η ⤳ x := by
  set e := AffineSpace.SpecIso PUnit.{u + 1} (.of k) with he
  set η := (Scheme.homeoOfIso e).symm
    (genericPoint (Spec (.of (MvPolynomial PUnit.{u + 1} k)))) with hη
  have hspec (x : (affineLine k).left) : η ⤳ x := by
    have hs := (genericPoint_specializes (e.hom.base x)).map e.inv.continuous
    have hcomp : e.inv.base (e.hom.base x) = x := by
      show (e.hom ≫ e.inv).base x = x
      simp
    simpa [hη, Scheme.homeoOfIso_symm, Scheme.coe_homeoOfIso_symm, hcomp] using hs
  refine ⟨η, ?_, hspec⟩
  set one : Spec (.of k) ⟶ (affineLine k).left :=
    AffineSpace.homOfVector (𝟙 (Spec (.of k))) (fun _ : PUnit.{u + 1} => 1) with hone
  have hmem : one.base (genericPoint (Spec (.of k))) ∈
      (affineLine k).left.basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) := by
    rw [← Scheme.Hom.mem_preimage, Scheme.Hom.preimage_basicOpen_top]
    rw [hone, AffineSpace.homOfVector_appTop_coord, Scheme.basicOpen_one]
    trivial
  exact (hspec (one.base (genericPoint (Spec (.of k))))).mem_open
    (puncturedAffineLineOpen k).isOpen hmem

/-! ### Relative affine space over an algebraic space -/

variable (B : BigFppfSite.{u})

/-- Affine `n`-space over `Spec k` is an object of a big fppf site containing `Spec k`,
being the spectrum of a polynomial ring in finitely many variables over `k`. -/
theorem contains_affineSpace (hS : B.Contains (Spec (.of k))) (n : ℕ) :
    B.Contains (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))) := by
  have hSpec : (Spec (.of (MvPolynomial (ULift.{u} (Fin n)) k))).size < B.cutoff :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      k (MvPolynomial (ULift.{u} (Fin n)) k) hS
  show (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))).size < B.cutoff
  rw [Scheme.size_congr (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k))]
  exact hSpec

section RelativeAffineSpace

variable (S : Scheme.{u}) (hS : B.Contains S)

end RelativeAffineSpace

/-! ### The chart data of the example -/

section Construction

variable (hS : B.Contains (Spec (.of k)))

include hS in
/-- The affine line is an object of a big fppf site containing `Spec k`. -/
theorem contains_affineLine : B.Contains (affineLine k).left :=
  (affineLineChart k B hS).left.2



/-- The relation scheme `Δ ⨿ Γ` of Stacks 02Z1, as an object of the big fppf site over
`Spec k`. -/
noncomputable def relationChart : BigFppfOver B (Spec (.of k)) hS :=
  BigFppfOver.mk B (Spec (.of k)) hS (contains_relationScheme k B hS) (relationScheme k).hom

/-- The underlying `Spec k`-scheme of `relationChart` is the relation scheme. -/
theorem relationChart_post :
    (Over.post B.inclusion).obj (relationChart k B hS) = relationScheme k := rfl

/-- The punctured affine line, as an object of the big fppf site over `Spec k`: it is an
open subscheme of the affine line, which is an object of the site. -/
noncomputable def puncturedChart : BigFppfOver B (Spec (.of k)) hS :=
  BigFppfOver.mk B (Spec (.of k)) hS
    (AlgebraicGeometry.AffineLineInvolution.contains_puncturedAffineLine k B hS)
    (puncturedAffineLine k).hom

/-- The underlying `Spec k`-scheme of `puncturedChart` is the punctured affine line. -/
theorem puncturedChart_post :
    (Over.post B.inclusion).obj (puncturedChart k B hS) = puncturedAffineLine k := rfl

/-- The base `Spec k`, as an object of the big fppf site over itself. -/
noncomputable def baseChart : BigFppfOver B (Spec (.of k)) hS :=
  BigFppfOver.mk B (Spec (.of k)) hS hS (𝟙 (Spec (.of k)))

/-- The underlying `Spec k`-scheme of `baseChart` is `Spec k` over itself by the identity. -/
theorem baseChart_post :
    (Over.post B.inclusion).obj (baseChart k B hS) = Over.mk (𝟙 (Spec (.of k))) := rfl

/-! #### The structural morphisms, lifted to the site

The functor `CategoryTheory.Over.post B.inclusion` presenting the big fppf category over
`Spec k` as a site of `Spec k`-schemes is fully faithful, so each morphism of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution` between the objects above comes
from a unique morphism of the site; `CategoryTheory.Functor.preimage` is that morphism. -/

/-- The target map `R ⟶ U` of the involution relation, as a morphism of the site. -/
noncomputable def chartTarget : relationChart k B hS ⟶ affineLineChart k B hS :=
  (Over.post B.inclusion).preimage (involutionRelation k).target

/-- The source map `R ⟶ U` of the involution relation, as a morphism of the site. -/
noncomputable def chartSource : relationChart k B hS ⟶ affineLineChart k B hS :=
  (Over.post B.inclusion).preimage (involutionRelation k).source

/-- The inclusion of the diagonal summand `Δ = 𝔸¹_k` into the relation scheme, as a
morphism of the site. -/
noncomputable def chartDelta : affineLineChart k B hS ⟶ relationChart k B hS :=
  (Over.post B.inclusion).preimage (coprod.inl : affineLine k ⟶ relationScheme k)

/-- The inclusion of the graph summand `Γ = 𝔸¹_k ∖ 0` into the relation scheme, as a
morphism of the site. -/
noncomputable def chartGamma : puncturedChart k B hS ⟶ relationChart k B hS :=
  (Over.post B.inclusion).preimage (coprod.inr : puncturedAffineLine k ⟶ relationScheme k)

/-- The inclusion of the punctured line into the affine line, as a morphism of the site. -/
noncomputable def chartPunctured : puncturedChart k B hS ⟶ affineLineChart k B hS :=
  (Over.post B.inclusion).preimage (puncturedAffineLineInclusion k)

/-- Negation on the affine line, as a morphism of the site. -/
noncomputable def chartNeg : affineLineChart k B hS ⟶ affineLineChart k B hS :=
  (Over.post B.inclusion).preimage (affineLineNeg k)

/-- The zero section of the affine line, as a morphism of the site. -/
noncomputable def chartOrigin : baseChart k B hS ⟶ affineLineChart k B hS :=
  (Over.post B.inclusion).preimage
    (Over.homMk (originSection k) (AffineSpace.homOfVector_over _ _))

/-- The image of `chartTarget` in `Spec k`-schemes is the target map of the relation. -/
@[simp]
theorem post_chartTarget : (Over.post B.inclusion).map (chartTarget k B hS) =
    (involutionRelation k).target := (Over.post B.inclusion).map_preimage _

/-- The image of `chartSource` in `Spec k`-schemes is the source map of the relation. -/
@[simp]
theorem post_chartSource : (Over.post B.inclusion).map (chartSource k B hS) =
    (involutionRelation k).source := (Over.post B.inclusion).map_preimage _

/-- The image of `chartDelta` in `Spec k`-schemes is the inclusion of the diagonal summand. -/
@[simp]
theorem post_chartDelta : (Over.post B.inclusion).map (chartDelta k B hS) =
    (coprod.inl : affineLine k ⟶ relationScheme k) :=
  (Over.post B.inclusion).map_preimage _

/-- The image of `chartGamma` in `Spec k`-schemes is the inclusion of the graph summand. -/
@[simp]
theorem post_chartGamma : (Over.post B.inclusion).map (chartGamma k B hS) =
    (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) :=
  (Over.post B.inclusion).map_preimage _

/-- The image of `chartPunctured` in `Spec k`-schemes is the inclusion of the punctured
line into the affine line. -/
@[simp]
theorem post_chartPunctured : (Over.post B.inclusion).map (chartPunctured k B hS) =
    puncturedAffineLineInclusion k := (Over.post B.inclusion).map_preimage _

/-- The image of `chartNeg` in `Spec k`-schemes is negation on the affine line. -/
@[simp]
theorem post_chartNeg : (Over.post B.inclusion).map (chartNeg k B hS) =
    affineLineNeg k := (Over.post B.inclusion).map_preimage _

/-- The image of `chartOrigin` in `Spec k`-schemes is the zero section of the affine line. -/
@[simp]
theorem post_chartOrigin : (Over.post B.inclusion).map (chartOrigin k B hS) =
    Over.homMk (originSection k) (AffineSpace.homOfVector_over _ _) :=
  (Over.post B.inclusion).map_preimage _

/-- The underlying scheme morphism of the inclusion of the punctured line. -/
theorem toScheme_map_chartPunctured :
    (BigFppfOver.toScheme B (Spec (.of k)) hS).map (chartPunctured k B hS) =
      (puncturedAffineLineOpen k).ι := by
  show ((Over.post B.inclusion).map (chartPunctured k B hS)).left = _
  rw [post_chartPunctured]
  rfl

/-- The underlying scheme morphism of the zero section. -/
theorem toScheme_map_chartOrigin :
    (BigFppfOver.toScheme B (Spec (.of k)) hS).map (chartOrigin k B hS) =
      originSection k :=
  congrArg Over.Hom.left (post_chartOrigin k B hS)

/-- The underlying scheme morphism of the inclusion of the diagonal summand. -/
theorem toScheme_map_chartDelta :
    (BigFppfOver.toScheme B (Spec (.of k)) hS).map (chartDelta k B hS) =
      (Over.forget (Spec (.of k))).map (coprod.inl : affineLine k ⟶ relationScheme k) :=
  congrArg Over.Hom.left (post_chartDelta k B hS)

/-- The underlying scheme morphism of the inclusion of the graph summand. -/
theorem toScheme_map_chartGamma :
    (BigFppfOver.toScheme B (Spec (.of k)) hS).map (chartGamma k B hS) =
      (Over.forget (Spec (.of k))).map
        (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) :=
  congrArg Over.Hom.left (post_chartGamma k B hS)

/-! #### The relations between the structural morphisms -/

/-- Both projections of the relation restrict to the identity on the diagonal summand. -/
theorem chartDelta_comp_chartTarget :
    chartDelta k B hS ≫ chartTarget k B hS = 𝟙 _ := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, post_chartDelta, post_chartTarget, CategoryTheory.Functor.map_id,
    involutionRelation_target]
  exact coprod.inl_desc _ _

/-- The source projection of the relation restricts to the identity on the diagonal
summand. -/
theorem chartDelta_comp_chartSource :
    chartDelta k B hS ≫ chartSource k B hS = 𝟙 _ := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, post_chartDelta, post_chartSource, CategoryTheory.Functor.map_id,
    involutionRelation_source]
  exact coprod.inl_desc _ _

/-- On the graph summand the target projection is the inclusion of the punctured line. -/
theorem chartGamma_comp_chartTarget :
    chartGamma k B hS ≫ chartTarget k B hS = chartPunctured k B hS := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, post_chartGamma, post_chartTarget, post_chartPunctured,
    involutionRelation_target]
  exact coprod.inr_desc _ _

/-- On the graph summand the source projection is the inclusion of the punctured line
followed by negation. -/
theorem chartGamma_comp_chartSource :
    chartGamma k B hS ≫ chartSource k B hS =
      chartPunctured k B hS ≫ chartNeg k B hS := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, Functor.map_comp, post_chartGamma, post_chartSource,
    post_chartPunctured, post_chartNeg, involutionRelation_source]
  exact coprod.inr_desc _ _

/-- Negation fixes the zero section. -/
theorem chartOrigin_comp_chartNeg :
    chartOrigin k B hS ≫ chartNeg k B hS = chartOrigin k B hS := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, post_chartOrigin, post_chartNeg]
  exact Over.OverMorphism.ext (originSection_comp_affineLineNeg k)

/-- The pre-relation determined by the two charted projections is the involution relation of
Stacks 02Z1. -/
theorem relation_eq_involutionRelation :
    Space.relation B (Spec (.of k)) hS (chartSource k B hS) (chartTarget k B hS) =
      involutionRelation k := by
  refine Limits.prod.hom_ext ?_ ?_
  · exact (prod.lift_fst _ _).trans (post_chartTarget k B hS)
  · exact (prod.lift_snd _ _).trans (post_chartSource k B hS)

/-! ### The geometric heart of the example -/

/-- **Stacks 088W, the geometric step.**  Let `r : R ⟶ P` be a morphism of the site out of
the relation scheme which restricts to `d` on the diagonal summand and factors as `g` after
the inclusion of the punctured line on the graph summand, and suppose `g` and `d` agree on
the zero section.  Then `r` is not an immersion of schemes.

The generic point `η` of the affine line specializes to the image `z` of the zero section,
hence `g η ⤳ g z`.  Those two points are the images under `r` of `η` in the graph summand and
of `z` in the diagonal summand, so an immersion `r` — being an embedding — would force a
specialization inside `R = Δ ⨿ Γ` from a point of the second summand to a point of the
first, which `not_specializes_coprod_inr_inl` forbids. -/
theorem not_isImmersion_of_relation_factorizations
    {P : BigFppfOver B (Spec (.of k)) hS} (r : relationChart k B hS ⟶ P)
    {g d : affineLineChart k B hS ⟶ P}
    (hdelta : chartDelta k B hS ≫ r = d)
    (hgamma : chartGamma k B hS ≫ r = chartPunctured k B hS ≫ g)
    (horigin : chartOrigin k B hS ≫ g = chartOrigin k B hS ≫ d) :
    ¬ AlgebraicGeometry.IsImmersion
        ((BigFppfOver.toScheme B (Spec (.of k)) hS).map r) := by
  intro him
  set T := BigFppfOver.toScheme B (Spec (.of k)) hS with hT
  have hTp : T.map (chartPunctured k B hS) = (puncturedAffineLineOpen k).ι :=
    toScheme_map_chartPunctured k B hS
  obtain ⟨η, hηmem, hηspec⟩ := exists_genericPoint_affineLine k
  set p : T.obj (baseChart k B hS) := genericPoint (Spec (.of k)) with hp
  set z : T.obj (affineLineChart k B hS) := (T.map (chartOrigin k B hS)) p with hz
  set ηV : T.obj (puncturedChart k B hS) := ⟨η, hηmem⟩ with hηV
  have hmap {X Y Z : BigFppfOver B (Spec (.of k)) hS} (u : X ⟶ Y) (v : Y ⟶ Z) (x : T.obj X) :
      T.map v (T.map u x) = T.map (u ≫ v) x := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
  -- The image of `η` in the graph summand, pushed through `r`, is computed by `g`.
  have hGamma : (T.map r) ((T.map (chartGamma k B hS)) ηV) = (T.map g) η := by
    rw [hmap (chartGamma k B hS) r, hgamma, ← hmap, hTp]
    rfl
  -- The image of `z` in the diagonal summand, pushed through `r`, is computed by `g` too:
  -- there it is computed by `d`, and `g` and `d` agree on the zero section.
  have hDelta : (T.map r) ((T.map (chartDelta k B hS)) z) = (T.map g) z := by
    rw [hz, hmap (chartDelta k B hS) r, hmap (chartOrigin k B hS), hdelta, ← horigin,
      ← hmap]
  -- Downstairs the specialization holds, because `η` specializes to `z`.
  have hTargetSpec : (T.map r) ((T.map (chartGamma k B hS)) ηV) ⤳
      (T.map r) ((T.map (chartDelta k B hS)) z) := by
    rw [hGamma, hDelta]
    exact (hηspec z).map (T.map g).continuous
  -- An immersion is an embedding, so the specialization lifts to the relation scheme.
  have hDomainSpec : (T.map (chartGamma k B hS)) ηV ⤳ (T.map (chartDelta k B hS)) z :=
    (T.map r).isEmbedding.isInducing.specializes_iff.mp hTargetSpec
  -- Upstairs it is refuted: the relation scheme is a coproduct.
  refine not_specializes_relationScheme k ηV z ?_
  rw [← toScheme_map_chartGamma k B hS, ← toScheme_map_chartDelta k B hS]
  exact hDomainSpec

/-! ### The quotient and its chart -/

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] [NeZero (2 : k)]

include hS in
omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The two charted projections form an étale equivalence relation, being the involution
relation of Stacks 02Z1. -/
theorem isEtaleEquivalenceRelation_relation :
    IsEtaleEquivalenceRelation
      (Space.relation B (Spec (.of k)) hS (chartSource k B hS) (chartTarget k B hS)) := by
  rw [relation_eq_involutionRelation]
  exact isEtaleEquivalenceRelation k

attribute [local instance] isEtaleEquivalenceRelation_relation

/-- The quotient `X = 𝔸¹_k/R` of Stacks 02Z1, presented as the quotient sheaf of the
pre-relation determined by the two charted projections. -/
noncomputable abbrev quotientSpace : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u :=
  (quotientSheaf (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
    (Space.relation B (Spec (.of k)) hS (chartSource k B hS) (chartTarget k B hS))).obj

/-- The chart `𝔸¹_k ⟶ X` of the quotient. -/
noncomputable abbrev quotientSpaceMap :
    yoneda.obj (affineLineChart k B hS) ⟶ quotientSpace k B hS :=
  Space.quotientMap B (Spec (.of k)) hS (chartSource k B hS) (chartTarget k B hS)

include hS in
omit [NeZero (2 : k)] in
/-- The quotient sheaf `quotientSpace` is the involution quotient of the affine line. -/
theorem quotientSpace_eq : quotientSpace k B hS = (involutionQuotient k B hS).obj := by
  show (quotientSheaf (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
    (Space.relation B (Spec (.of k)) hS (chartSource k B hS) (chartTarget k B hS))).obj = _
  rw [relation_eq_involutionRelation]
  rfl

include hS in
omit [NeZero (2 : k)] in
/-- The quotient is an algebraic space over `Spec k`, by Stacks 02Z1.

The relation of this example is an affine morphism, so Stacks 0265 applies to it with no
descent hypothesis: this is
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient_of_isAffineHom`. -/
theorem isAlgebraicSpace_quotientSpace (hchar : (2 : k) ≠ 0) :
    IsAlgebraicSpace B (Spec (.of k)) hS (quotientSpace k B hS) := by
  rw [quotientSpace_eq]
  exact isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hS hchar

include hS in
omit [NeZero (2 : k)] in
/-- The quotient is quasi-separated, by Stacks 02Z1.

This is the proof of
`AlgebraicGeometry.AffineLineInvolution.isAbsolutelyQuasiSeparated_involutionQuotient` with
its three inputs — algebraicity of the quotient and surjectivity and étaleness of the chart —
taken in the unconditional forms available because the relation is an affine morphism. -/
theorem isAbsolutelyQuasiSeparated_quotientSpace (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsAbsolutelyQuasiSeparated B (Spec (.of k)) hS hZ (quotientSpace k B hS) := by
  rw [quotientSpace_eq]
  have : NeZero (2 : k) := ⟨hchar⟩
  have _hrel : IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  obtain ⟨d, p₁, p₂, hpb, hqc⟩ :=
    exists_isPullback_quotientChart_involutionRelation k B hS
  exact Space.isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection
    B (Spec (.of k)) hS hZ (isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hS hchar)
    (presheafSurjective_quotientChart k B hS hchar)
    (presheafEtale_quotientChart k B hS hchar)
    (quasiSeparated_affineLineChart k B hS) hpb hqc

/-! ### Descending an immersion to the relation scheme -/

include hS in
/-- **Stacks 088W, the descent step.**  If `prod.lift q (yoneda.map a)` is an immersion of
algebraic spaces, where `q` is the chart of the quotient, then the induced morphism
`prod.lift s (t ≫ a) : R ⟶ 𝔸¹_k ⨯ W` of the site is an immersion of schemes.

The relation is the kernel pair of the chart (Stacks 02WV), so `isPullback_prod_lift` makes
`prod.lift s (t ≫ a)` a base change of `prod.lift q (yoneda.map a)` after `yoneda`; the
property of being an immersion after representable base change is stable under base change,
and `yoneda` preserves binary products, so what is obtained is representability of
`yoneda.map (prod.lift s (t ≫ a))` with that property, which is the assertion.

Algebraicity of the quotient sheaf is not needed:
`AlgebraicGeometry.Space.quotientMap_isPullback` assumes nothing about the quotient, the
kernel-pair identity resting only on the left exactness of sheafification. -/
theorem isImmersion_relation_prod_lift
    [HasBinaryProducts (BigFppfOver B (Spec (.of k)) hS)]
    {W : BigFppfOver B (Spec (.of k)) hS} (a : affineLineChart k B hS ⟶ W)
    (him : Space.IsImmersion B (Spec (.of k)) hS
      (prod.lift (quotientSpaceMap k B hS) (yoneda.map a))) :
    AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hS).map
      (prod.lift (chartSource k B hS) (chartTarget k B hS ≫ a))) := by
  set Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsImmersion.{u})
    (BigFppfOver.toScheme B (Spec (.of k)) hS) with hQdef
  have _ : MorphismProperty.IsStableUnderBaseChange Q.presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  have hpb := Space.quotientMap_isPullback B (Spec (.of k)) hS
    (chartSource k B hS) (chartTarget k B hS)
  have hYoneda : Q.presheaf (prod.lift (yoneda.map (chartSource k B hS))
      (yoneda.map (chartTarget k B hS) ≫ yoneda.map a)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_prod_lift hpb (yoneda.map a)).flip him
  set r : relationChart k B hS ⟶ Limits.prod (affineLineChart k B hS) W :=
    prod.lift (chartSource k B hS) (chartTarget k B hS ≫ a) with hr
  have hYonedaMap : Q.presheaf (yoneda.map r) := by
    set e := PreservesLimitPair.iso (yoneda (C := BigFppfOver B (Spec (.of k)) hS))
      (affineLineChart k B hS) W with he
    have hcomm : yoneda.map r ≫ e.hom =
        prod.lift (yoneda.map (chartSource k B hS))
          (yoneda.map (chartTarget k B hS) ≫ yoneda.map a) := by
      refine Limits.prod.hom_ext ?_ ?_ <;>
        simp [hr, he, ← CategoryTheory.Functor.map_comp]
    rw [← MorphismProperty.cancel_right_of_respectsIso Q.presheaf _ e.hom, hcomm]
    exact hYoneda
  exact MorphismProperty.of_relative_map (P := Q) (F := yoneda) hYonedaMap

include hS in
/-- **Stacks 088W, the two steps combined.**  No morphism `a : 𝔸¹_k ⟶ W` of the site makes
`prod.lift q (yoneda.map a)` an immersion of algebraic spaces, where `q` is the chart of the
quotient `X = 𝔸¹_k/R`.

Such an immersion would base-change to an immersion of schemes `prod.lift s (t ≫ a)` out of
the relation scheme, by `isImmersion_relation_prod_lift`; the three identities below say that
this morphism restricts to `prod.lift (𝟙 𝔸¹) a` on the diagonal summand, factors through
`prod.lift (-1) a` on the graph summand, and that those two agree on the zero section, which
is what `not_isImmersion_of_relation_factorizations` refutes.

As for the descent step, algebraicity of the quotient sheaf is not assumed. -/
theorem not_isImmersion_prod_lift
    [HasBinaryProducts (BigFppfOver B (Spec (.of k)) hS)]
    {W : BigFppfOver B (Spec (.of k)) hS} (a : affineLineChart k B hS ⟶ W) :
    ¬ Space.IsImmersion B (Spec (.of k)) hS
      (prod.lift (quotientSpaceMap k B hS) (yoneda.map a)) := by
  intro him
  refine not_isImmersion_of_relation_factorizations k B hS
    (prod.lift (chartSource k B hS) (chartTarget k B hS ≫ a))
    (g := prod.lift (chartNeg k B hS) a) (d := prod.lift (𝟙 _) a) ?_ ?_ ?_
    (isImmersion_relation_prod_lift k B hS a him)
  · refine Limits.prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.lift_fst, prod.lift_fst, chartDelta_comp_chartSource]
    · rw [Category.assoc, prod.lift_snd, prod.lift_snd, ← Category.assoc,
        chartDelta_comp_chartTarget, Category.id_comp]
  · refine Limits.prod.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, prod.lift_fst, prod.lift_fst,
        chartGamma_comp_chartSource]
    · rw [Category.assoc, Category.assoc, prod.lift_snd, prod.lift_snd, ← Category.assoc,
        chartGamma_comp_chartTarget]
  · refine Limits.prod.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, prod.lift_fst, prod.lift_fst,
        chartOrigin_comp_chartNeg, Category.comp_id]
    · rw [Category.assoc, Category.assoc, prod.lift_snd, prod.lift_snd]

/-! ### The chart, over the quotient -/

include hS in
omit [NeZero (2 : k)] in
/-- The chart `𝔸¹_k ⟶ X` of the quotient is of finite type.

It is étale, because it is the quotient map of an étale equivalence relation, hence locally
of finite type; and it is quasi-compact because its source is quasi-compact and the quotient
is quasi-separated. -/
theorem isFiniteType_quotientSpaceMap (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsFiniteType B (Spec (.of k)) hS (quotientSpaceMap k B hS) := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have hXalg := isAlgebraicSpace_quotientSpace k B hS hchar
  have hXqs := isAbsolutelyQuasiSeparated_quotientSpace k B hS hchar hZ
  refine ⟨?_, ?_⟩
  · exact Space.isLocallyOfFiniteType_of_isEtale B (Spec (.of k)) hS hXalg
      (Space.isEtale_of_presheaf_etale B (Spec (.of k)) hS
        (Space.quotientMap_etale B (Spec (.of k)) hS _ _
          (Space.relativelyRepresentable_quotientMap_of_isAlgebraicSpace B (Spec (.of k)) hS
            (chartSource k B hS) (chartTarget k B hS) hXalg)))
  · exact Space.isQuasiCompact_of_isQuasiCompactSpace B (Spec (.of k)) hS hZ hXalg hXqs
      (Space.isQuasiCompactSpace_yoneda_obj B (Spec (.of k)) hS
        (Scheme.compactSpace_of_isAffine _)) _

include hS in
/-- **Stacks 088W, the nonexistence of the immersion, for the chart itself.**  No morphism
`j : 𝔸¹_k ⟶ 𝔸ⁿ_X` over the quotient `X = 𝔸¹_k/R` is an immersion of algebraic spaces.

Affine `n`-space over `Spec k` is an object `W` of the site and represents the second factor
of `𝔸ⁿ_X = X ⨯ 𝔸ⁿ_k`, so a morphism `j` over `X` is `prod.lift` of the chart with a morphism
`a : 𝔸¹_k ⟶ W` of the site, up to an isomorphism of arrows; `not_isImmersion_prod_lift`
refutes that. -/
theorem not_isImmersion_affineSpaceOver_quotientSpaceMap (n : ℕ)
    (j : yoneda.obj (affineLineChart k B hS) ⟶
      Space.affineSpaceOver B (Spec (.of k)) hS (quotientSpace k B hS) n)
    (hj : j ≫ prod.fst = quotientSpaceMap k B hS) :
    ¬ Space.IsImmersion B (Spec (.of k)) hS j := by
  have : HasBinaryProducts (BigFppfOver B (Spec (.of k)) hS) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  intro him
  have _ : MorphismProperty.RespectsIso (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsImmersion.{u})
        (BigFppfOver.toScheme B (Spec (.of k)) hS))) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
  -- Affine `n`-space over `Spec k`, as an object of the site, represents the second factor.
  set W : BigFppfOver B (Spec (.of k)) hS :=
    BigFppfOver.mk B (Spec (.of k)) hS (contains_affineSpace k B hS n)
      (AffineSpace.over (ULift.{u} (Fin n)) (Spec (.of k))).hom with hW
  have eW : points (Over.post B.inclusion)
      (Over.mk (AffineSpace.over (ULift.{u} (Fin n)) (Spec (.of k))).hom) ≅
      yoneda.obj W := Space.pointsYonedaIso (Over.post B.inclusion) W
  -- Hence `j` is `prod.lift` of the chart with a morphism of the site.
  set a : affineLineChart k B hS ⟶ W := yoneda.preimage ((j ≫ prod.snd) ≫ eW.hom) with ha
  have hamap : yoneda.map a = (j ≫ prod.snd) ≫ eW.hom := yoneda.map_preimage _
  have hcomm : j ≫ (prod.mapIso (Iso.refl (quotientSpace k B hS)) eW).hom =
      prod.lift (quotientSpaceMap k B hS) (yoneda.map a) := by
    refine Limits.prod.hom_ext ?_ ?_
    · show (j ≫ prod.map (𝟙 _) eW.hom) ≫ prod.fst = _
      rw [Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst]
      exact hj
    · show (j ≫ prod.map (𝟙 _) eW.hom) ≫ prod.snd = _
      rw [Category.assoc, prod.map_snd, prod.lift_snd]
      exact hamap.symm
  have him' := (MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.presheaf _) j
    (prod.mapIso (Iso.refl (quotientSpace k B hS)) eW).hom).mpr him
  rw [hcomm] at him'
  -- Base-change the immersion to the relation scheme, and refute it there.
  exact not_isImmersion_prod_lift k B hS a him'

end Construction

end Stacks.Examples.AffineOverAlgebraicSpace

namespace Stacks.Examples

open AffineOverAlgebraicSpace

/-- **Stacks 088W.**  There is a finite-type morphism `Y ⟶ X` of algebraic spaces with `Y`
an affine scheme and `X` quasi-separated which admits no immersion of `Y`, over `X`, into
relative affine `n`-space over `X` for any `n`.

Take for `X` the quotient `𝔸¹_k/R` of Stacks 02Z1 over a field in which two is invertible,
for `Y` its chart `𝔸¹_k`, and for the morphism the chart itself: it is étale, hence locally
of finite type, and quasi-compact because its source is quasi-compact and `X` is
quasi-separated — that is
`AffineOverAlgebraicSpace.isFiniteType_quotientSpaceMap`.  The nonexistence of an immersion
is `AffineOverAlgebraicSpace.not_isImmersion_affineSpaceOver_quotientSpaceMap`.

Algebraicity and quasi-separatedness of the target come from Stacks 02Z1 in the form in
which the relation of this example is an affine morphism, so Stacks 0265 applies to it with
no effective-descent input:
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient_of_isAffineHom`
rests on the relation being affine, which is Mathlib's `IsAffineHom` instance for a morphism
between affine schemes, and the descent that Stacks 0265 then consumes is effective descent at
the affine monomorphisms locally of finite type, proved outright in
`StacksFrontier/AlgebraicGeometry/Descent/AffineHomCoveringSieveDescent.lean`. -/
@[stacks 088W "the counterexample"]
theorem exists_finiteType_affine_not_immersion_into_affineSpace
    (k : Type u) [Field k] (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    ∃ (Y : BigFppfOver B (Spec (.of k)) hS)
      (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
      (f : yoneda.obj Y ⟶ X),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj Y) ∧
      IsAlgebraicSpace B (Spec (.of k)) hS (yoneda.obj Y) ∧
      IsAlgebraicSpace B (Spec (.of k)) hS X ∧
      Space.IsFiniteType B (Spec (.of k)) hS f ∧
      Space.IsAbsolutelyQuasiSeparated B (Spec (.of k)) hS hZ X ∧
      ∀ (n : ℕ) (j : yoneda.obj Y ⟶ Space.affineSpaceOver B (Spec (.of k)) hS X n),
        j ≫ prod.fst = f → ¬ Space.IsImmersion B (Spec (.of k)) hS j := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have := isEtaleEquivalenceRelation_relation k B hS
  exact ⟨affineLineChart k B hS, quotientSpace k B hS, quotientSpaceMap k B hS,
    inferInstance, isAlgebraicSpace_yoneda B (Spec (.of k)) hS _,
    isAlgebraicSpace_quotientSpace k B hS hchar,
    isFiniteType_quotientSpaceMap k B hS hchar hZ,
    isAbsolutelyQuasiSeparated_quotientSpace k B hS hchar hZ,
    not_isImmersion_affineSpaceOver_quotientSpaceMap k B hS⟩

end Stacks.Examples

end
