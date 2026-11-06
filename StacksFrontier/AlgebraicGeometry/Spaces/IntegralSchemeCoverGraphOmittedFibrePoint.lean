module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresStrictDrop
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverDenseDegreeCarry
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGraphComplementScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGraphOmittedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# The fibre-degree drop of the inductive step of Stacks 09YB

This file closes the gap between the three proved halves of the fibre-degree drop of
[Stacks, Tag 09YB] and the drop itself. The three halves are

* the **splitting** `U ×_X Y = U ⨿ W`, as a pair of complementary open-and-closed subspaces
  (`AlgebraicGeometry.Space.exists_graphComplement_decomposition`), with `W` representable
  (`AlgebraicGeometry.Space.isRepresentable_graphComplement`);
* the **omitted point**, in point sets: over a point of `Y` in the image of `j` the graph of `j`
  supplies a point of `U ×_X Y` outside `W`
  (`AlgebraicGeometry.Space.exists_notMem_range_pointsMap_ι_of_mem_range_pointsMap`); and
* the **carry** of a degree bound from a topologically dense set of points of the base to all of
  them (`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange`).

What was missing between them was a translation and a strengthening, and both are supplied here.

**The translation.** The drop
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits`) asks for its
omitted point as a point of the *underlying scheme* of the canonical fibre of the projection over
a field-valued point, outside the image of the base change of `W`'s inclusion; the splitting
speaks of `AlgebraicGeometry.Space.points` of subfunctors. The passage is
`AlgebraicGeometry.Space.exists_notMem_range_toScheme_map_pullback_snd_of_notMem_range`: a point
of the source lying over the given field-valued point and outside the image of the open subobject
is lifted into the canonical fibre by Tag 03H4
(`AlgebraicGeometry.Space.exists_points_of_isPullback`) and read as a point of the representing
scheme by Tag 03BX (`AlgebraicGeometry.Space.pointsEquivScheme`); a preimage of it under the base
change of the inclusion would, by the pullback relation, exhibit the original point inside the
open subobject.

**The strengthening.** The drop used to assume its omitted point over *every* field-valued point
of the base. That is false here — the graph of `j` is a section only over `j(U)` — and it is why
the drop is now stated at one point. See the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresStrictDrop`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_notMem_range_toScheme_map_pullback_snd_of_notMem_range`: the
  translation of an omitted point from `AlgebraicGeometry.Space.points` of the source to a point
  of the scheme underlying the canonical fibre.
* `AlgebraicGeometry.Space.exists_graphComplement_isEtale_isFiniteLocallyFreeOfRank_lt`: **the
  fibre-degree drop of the inductive step of [Stacks, Tag 09YB].** For an étale chart
  `p = j ≫ π : h_U ⟶ X` factored through a quasi-compact open immersion `j` with topologically
  dense image and an integral `π`, the complementary summand `W` of the splitting
  `h_U ×_X Y = h_U ⨿ W` is an object of the site, étale over `Y`, factoring through `h_U` over
  `X`, meeting with `j(U)` every point of `Y`, and with **every** field-valued fibre of degree
  strictly below any bound for the field-valued fibres of `p`.

* `AlgebraicGeometry.Space.exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt`: the same
  summand presented as a **surjective étale chart of the open subspace `V ⊆ Y` it covers**, with
  every field-valued fibre of degree strictly below `d`. This is the shape the recursion of the
  tag needs, the recursion being on a bound for the fibre degrees of a chart.

## Implementation notes

**Why the summand has to be repackaged as a morphism of the site.** The splitting produces `W`
as a subfunctor of the fibre product, and the drop is stated for a morphism `σ : V ⟶ W` of the
big fppf category, since its scheme-level content
(`AlgebraicGeometry.finite_open_rank_lt_of_field`) is about an open immersion of schemes. Both
the fibre product and the summand are representable here — the first projection of the fibre
product is a base change of the integral `π`, and the summand is a closed subspace of it — so
`CategoryTheory.Functor.reprX` and `CategoryTheory.Functor.reprW` name site objects for them and
`CategoryTheory.Functor.preimage` turns the inclusion into a morphism of the site. Its underlying
morphism of schemes is an open immersion because the inclusion of an open subspace is one and the
two isomorphisms are, and because open immersion is read off a morphism of the site by evaluating
the `CategoryTheory.MorphismProperty.presheaf` at the identity base change.

**Where each hypothesis is used.** Separatedness of the chart gives separatedness of the
summand over `Y`, which the carry needs for Tag 07S8; surjectivity of the chart gives
surjectivity of the projection, which is what makes `j(U)` together with the image of `W` cover
`Y`; topological density of `j(U)` is what the carry carries along. The non-strict degree bound
`hd` is used twice: once as the hypothesis of the drop at each point of `j(U)`, and once —
through `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_isOpenImmersion` — to supply the
universal bound that the carry asks for, which cannot come from the drop since the carry is what
propagates the drop.

## What is and is not proved

Nothing here carries a Stacks attribute, and no part of [Stacks, Tag 09YB] is registered. What is
proved is the fibre-degree drop of the inductive step of that tag. The induction it feeds is
performed in `StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverInduction`, which consumes
`AlgebraicGeometry.Space.exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt` below: it
covers the open subspace `V ⊆ Y` by recursion at the strictly smaller bound, glues the result
with the reduced induced structure on `Y ∖ V`, and descends from `Y` to `X`. Clause (1) of the
tag is discharged there.

The integrality of the factorization `φ : h_W ⟶ h_U` through the chart, conjoined to both
statements below, is what that recursion needs and the only thing added here beyond the drop
itself: with `φ` integral the new chart's source is quasi-compact over the old one and the new
chart is separated, which is what replaces affineness across the recursion.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_IntegralSchemeCoverGraphOmittedFibrePoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_IntegralSchemeCoverGraphOmittedFibrePoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_IntegralSchemeCoverGraphOmittedFibrePoint B S hS).has_limit _

/-! ### An omitted point of the canonical fibre, from an omitted point of the source -/

/-- **The omitted point of the drop, translated from point sets to the canonical fibre.** Let
`Ψ : h_P ⟶ Y` be relatively representable, let `σ : W ⟶ P` be a morphism of the site, and let `ξ`
be a morphism into `Y` from the presheaf represented by an object `T`. Suppose some point `a` of
`h_P` is carried by `Ψ` to the image under `ξ` of a point of `h_T`, and does **not** lie in the
image of `h_W`. Then the scheme underlying the canonical fibre of `Ψ` over `ξ` has a point
outside the image of the base change of `σ` to that fibre.

This is the shape in which
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits` asks
for its omitted point. The lift of `a` into the fibre is Tag 03H4, the passage to the scheme is
Tag 03BX, and the exclusion is the pullback relation: a preimage of the lifted point under the
base change of `σ` would, pushed along the first projection, exhibit `a` in the image of
`h_W`. -/
theorem exists_notMem_range_toScheme_map_pullback_snd_of_notMem_range
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {P W : BigFppfOver B S hS}
    {Ψ : yoneda.obj P ⟶ Y} (hΨ : yoneda.relativelyRepresentable Ψ) (σ : W ⟶ P)
    {T : BigFppfOver B S hS} (ξ : yoneda.obj T ⟶ Y)
    (a : points B S hS (yoneda.obj P)) (t : points B S hS (yoneda.obj T))
    (hat : pointsMap B S hS (yoneda.obj P) Ψ a = pointsMap B S hS (yoneda.obj T) ξ t)
    (ha : a ∉ Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map σ))) :
    ∃ x : (BigFppfOver.toScheme B S hS).obj (hΨ.pullback ξ),
      x ∉ Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd σ (hΨ.fst' ξ))).base := by
  classical
  obtain ⟨z, hz1, -⟩ := exists_points_of_isPullback B S hS (hΨ.isPullback' ξ) a t hat
  refine ⟨pointsEquivScheme B S hS (hΨ.pullback ξ) z, ?_⟩
  rintro ⟨b, hb⟩
  set z' := (pointsEquivScheme B S hS (pullback σ (hΨ.fst' ξ))).symm b with hz'
  have hzz : pointsMap B S hS (yoneda.obj (pullback σ (hΨ.fst' ξ)))
      (yoneda.map (pullback.snd σ (hΨ.fst' ξ))) z' = z := by
    refine (pointsEquivScheme B S hS (hΨ.pullback ξ)).injective ?_
    rwa [pointsEquivScheme_pointsMap_yoneda, hz', Equiv.apply_symm_apply]
  refine ha ⟨pointsMap B S hS (yoneda.obj (pullback σ (hΨ.fst' ξ)))
    (yoneda.map (pullback.fst σ (hΨ.fst' ξ))) z', ?_⟩
  rw [← pointsMap_comp_apply, ← Functor.map_comp, pullback.condition,
    Functor.map_comp, pointsMap_comp_apply, hzz, hz1]

/-- **The omitted point of the drop, for a subfunctor presented by isomorphisms.** Let
`C ⊆ Z` be a subfunctor, presented by isomorphisms `h_P ≅ Z` and `h_W ≅ C` and a morphism
`σ : W ⟶ P` of the site inducing the inclusion, and let `s : Z ⟶ Y`. A point `w` of `Z` outside
`C` lying over a point of `h_T` along `ξ` gives a point of the scheme underlying the canonical
fibre of `h_P ⟶ Y` over `ξ` outside the image of the base change of `σ`. -/
private theorem exists_notMem_range_toScheme_map_pullback_snd_of_iso
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {P W : BigFppfOver B S hS} (s : Z ⟶ Y)
    (C : Subfunctor Z) (eP : yoneda.obj P ≅ Z) (eW : yoneda.obj W ≅ C.toFunctor) (σ : W ⟶ P)
    (hσ : yoneda.map σ = eW.hom ≫ C.ι ≫ eP.inv) (hΨ : yoneda.relativelyRepresentable (eP.hom ≫ s))
    {T : BigFppfOver B S hS} (ξ : yoneda.obj T ⟶ Y) (w : points B S hS Z)
    (t : points B S hS (yoneda.obj T))
    (hwy : pointsMap B S hS Z s w = pointsMap B S hS (yoneda.obj T) ξ t)
    (hwC : w ∉ Set.range (pointsMap B S hS C.toFunctor C.ι)) :
    ∃ x : (BigFppfOver.toScheme B S hS).obj (hΨ.pullback ξ),
      x ∉ Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd σ (hΨ.fst' ξ))).base := by
  refine exists_notMem_range_toScheme_map_pullback_snd_of_notMem_range B S hS hΨ σ ξ
    (pointsMap B S hS Z eP.inv w) t ?_ ?_
  · rw [← pointsMap_comp_apply, ← Category.assoc, eP.inv_hom_id, Category.id_comp, hwy]
  · rintro ⟨v, hv⟩
    rw [hσ] at hv
    refine hwC ⟨pointsMap B S hS (yoneda.obj W) eW.hom v, ?_⟩
    refine (pointsEquivOfIso B S hS eP.symm).injective ?_
    rw [pointsEquivOfIso_apply, pointsEquivOfIso_apply, Iso.symm_hom, ← pointsMap_comp_apply]
    exact (pointsMap_comp_apply B S hS eW.hom (C.ι ≫ eP.inv) v).symm.trans hv

/-- **The non-strict bound on the fibres of the projection of `h_U ×_X Y`.** If every
field-valued fibre of `j ≫ π : h_U ⟶ X` has degree at most `d`, then so has every field-valued
fibre of the second projection `h_U ×_X Y ⟶ Y`, presented through an isomorphism
`h_P ≅ h_U ×_X Y`. -/
private theorem exists_isPullback_isFiniteLocallyFreeOfRank_le_of_iso_pullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U P : BigFppfOver B S hS}
    (j : yoneda.obj U ⟶ Y) (π : Y ⟶ X) (d : ℕ)
    (hd : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ζ : yoneda.obj T ⟶ X) (Q : BigFppfOver B S hS) (q : Q ⟶ T)
      (c : yoneda.obj Q ⟶ yoneda.obj U),
      IsPullback c (yoneda.map q) (j ≫ π) ζ →
        ∃ r : ℕ, r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r)
    (eP : yoneda.obj P ≅ pullback (j ≫ π) π)
    (hΨ : yoneda.relativelyRepresentable (eP.hom ≫ pullback.snd (j ≫ π) π)) :
    ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
      (ξ : yoneda.obj T ⟶ Y),
      ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (c : yoneda.obj Q ⟶ yoneda.obj P) (r : ℕ),
        r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
          IsPullback c (yoneda.map q) (eP.hom ≫ pullback.snd (j ≫ π) π) ξ := by
  intro k hk T eT ξ
  have ht : IsPullback (eP.hom ≫ pullback.fst (j ≫ π) π) (eP.hom ≫ pullback.snd (j ≫ π) π)
      (j ≫ π) π :=
    (IsPullback.of_hasPullback (j ≫ π) π).isoVertex eP
  obtain ⟨r, hrd, hrank⟩ := hd k hk T eT (ξ ≫ π) (hΨ.pullback ξ) (hΨ.snd ξ)
    (yoneda.map (hΨ.fst' ξ) ≫ eP.hom ≫ pullback.fst (j ≫ π) π)
    (IsPullback.paste_horiz (hΨ.isPullback' ξ) ht)
  exact ⟨_, _, _, r, hrd, hrank, hΨ.isPullback' ξ⟩

/-! ### The drop on the complementary summand of the graph -/

/-- **The fibre-degree drop of the inductive step of [Stacks, Tag 09YB].**

Let `X` be an algebraic space over `S`, let `U` be an object of the big fppf site and let
`p = j ≫ π : h_U ⟶ X` be a surjective separated étale chart of `X` factored through an open
immersion `j : h_U ⟶ Y` with topologically dense image and an integral morphism `π : Y ⟶ X`, as
Stacks 0ABS factors it. Let `d` bound the degrees of the field-valued fibres of `p`.

Then the complementary summand `W` of the splitting `h_U ×_X Y = h_U ⨿ W` of
`AlgebraicGeometry.Space.exists_graphComplement_decomposition` is an object of the site, it is
étale over `Y`, its structure morphism to `X` factors through the chart, its image together with
`j(U)` is all of `Y`, and **every** field-valued fibre of `W ⟶ Y` is finite locally free of
degree strictly below `d`.

The strict bound is the source's: over a point of `j(U)` the graph of `j` is a section of the
projection, so it occupies a point of the fibre there which `W` misses — "the `U` summand
accounts for one of the `d`" — and the bound is carried from the dense `j(U)` to the whole of `Y`
by closedness of the degree stratum of Stacks 07S8. Note that no additivity of the degree across
the splitting is used, and the splitting is used only in its lattice form: what the argument
takes from it is the complementarity of the two point sets. -/
theorem exists_graphComplement_isEtale_isFiniteLocallyFreeOfRank_lt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (U : BigFppfOver B S hS)
    (j : yoneda.obj U ⟶ Y) (π : Y ⟶ X)
    (hj : IsOpenImmersion B S hS j) (hπ : IsIntegralHom B S hS π)
    (hp : IsEtale B S hS (j ≫ π)) (hpsep : IsSeparated B S hS (j ≫ π))
    (hpsurj : IsSurjective B S hS (j ≫ π))
    (hdense : DenseRange (pointsMap B S hS (yoneda.obj U) j))
    (d : ℕ)
    (hd : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ζ : yoneda.obj T ⟶ X) (Q : BigFppfOver B S hS) (q : Q ⟶ T)
      (c : yoneda.obj Q ⟶ yoneda.obj U),
      IsPullback c (yoneda.map q) (j ≫ π) ζ →
        ∃ r : ℕ, r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) :
    ∃ (Wc : BigFppfOver B S hS) (g : yoneda.obj Wc ⟶ Y) (φ : yoneda.obj Wc ⟶ yoneda.obj U),
      IsEtale B S hS g ∧
      IsIntegralHom B S hS φ ∧
      g ≫ π = φ ≫ (j ≫ π) ∧
      Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
          Set.range (pointsMap B S hS (yoneda.obj Wc) g) = Set.univ ∧
      ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
        (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
        (ξ : yoneda.obj T ⟶ Y) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
        (i : yoneda.obj Vf ⟶ yoneda.obj Wc),
        IsPullback i (yoneda.map q) g ξ →
          ∃ r : ℕ, r < d ∧
            IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r := by
  classical
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hjEt : IsEtale B S hS j := isEtale_of_isOpenImmersion B S hS hj
  have hπsep : IsSeparated B S hS π := isSeparated_of_isIntegralHom B S hS π hY hX hπ
  -- the splitting of the fibre product into the graph and its complement
  obtain ⟨C, hCo, hCc, -, -, -, -, hCpt⟩ :=
    exists_graphComplement_decomposition B S hS hU hY hX j π hjEt hp hπsep
  -- both the fibre product and the complementary summand are schemes
  have hPrep : (pullback (j ≫ π) π).IsRepresentable :=
    isRepresentable_pullback_of_isIntegralHom B S hS j π hU hY hX hπ
      (inferInstanceAs (Functor.IsRepresentable (yoneda.obj U)))
  have hCrep : C.toFunctor.IsRepresentable :=
    isRepresentable_graphComplement B S hS j π hU hY hX hπ
      (inferInstanceAs (Functor.IsRepresentable (yoneda.obj U))) C hCc
  set eP : yoneda.obj (pullback (j ≫ π) π).reprX ≅ pullback (j ≫ π) π :=
    (pullback (j ≫ π) π).reprW
  set eW : yoneda.obj C.toFunctor.reprX ≅ C.toFunctor := C.toFunctor.reprW
  set σ : C.toFunctor.reprX ⟶ (pullback (j ≫ π) π).reprX :=
    yoneda.preimage (eW.hom ≫ C.ι ≫ eP.inv)
  have hmapσ : yoneda.map σ = eW.hom ≫ C.ι ≫ eP.inv := yoneda.map_preimage _
  set Ψ : yoneda.obj (pullback (j ≫ π) π).reprX ⟶ Y :=
    eP.hom ≫ pullback.snd (j ≫ π) π with hΨdef
  -- the inclusion of the summand is an open immersion of schemes
  have hσsp : IsOpenImmersion B S hS (yoneda.map σ) := by
    rw [hmapσ]
    exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS eW.hom)
      (isOpenImmersion_comp B S hS _ _ hCo.2 (isOpenImmersion_of_isIso B S hS eP.inv))
  have hσsch : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ) :=
    hσsp.2 (𝟙 _) (𝟙 _) σ
      (IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩)
  -- the projection of the fibre product is étale, hence relatively representable
  have hΨet : IsEtale B S hS Ψ := isEtale_comp B S hS (isEtale_of_isIso B S hS eP.hom)
    (isEtale_pullback_snd B S hS hY hX hU (j ≫ π) π hp)
  have hΨrr : yoneda.relativelyRepresentable Ψ :=
    ((isEtale_iff_presheaf_of_yoneda B S hS Ψ).1 hΨet).rep
  -- the non-strict bound on the fibres of the projection, at every field-valued point of `Y`
  have hbndΨ := exists_isPullback_isFiniteLocallyFreeOfRank_le_of_iso_pullback B S hS j π d hd
    eP hΨrr
  have hgEt : IsEtale B S hS (yoneda.map σ ≫ Ψ) :=
    isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hσsp) hΨet
  have hgeq : yoneda.map σ ≫ Ψ = eW.hom ≫ C.ι ≫ pullback.snd (j ≫ π) π := by
    rw [hmapσ, hΨdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- the summand's structure morphism to `Y`, and its properties
  refine ⟨C.toFunctor.reprX, yoneda.map σ ≫ Ψ,
    eW.hom ≫ C.ι ≫ pullback.fst (j ≫ π) π, hgEt, ?_, ?_, ?_, ?_⟩
  -- the factorization through the chart is integral: an isomorphism, followed by the
  -- inclusion of a closed subspace, followed by a base change of the integral `π`
  · exact isIntegralHom_comp B S hS
      (isIntegralHom_of_isClosedImmersion B S hS _ (isClosedImmersion_of_isIso B S hS eW.hom))
      (isIntegralHom_comp B S hS (isIntegralHom_of_isClosedImmersion B S hS _ hCc.2)
        (isIntegralHom_of_isPullback B S hS (IsPullback.of_hasPullback (j ≫ π) π).flip hπ))
  · rw [hgeq]
    simp only [Category.assoc]
    rw [pullback.condition]
  · have hrng : Set.range (pointsMap B S hS (yoneda.obj C.toFunctor.reprX)
          (eW.hom ≫ C.ι ≫ pullback.snd (j ≫ π) π)) =
        Set.range (pointsMap B S hS C.toFunctor (C.ι ≫ pullback.snd (j ≫ π) π)) := by
      rw [pointsMap_comp]
      exact (pointsEquivOfIso B S hS eW).surjective.range_comp _
    rw [hgeq, hrng]
    exact union_range_pointsMap_graph_range_pointsMap_comp_eq_univ B S hS j π
      (isSurjective_pullback_snd B S hS hU hX hY (j ≫ π) π hpsurj) C hCpt
  -- the strict bound, point by point over `j(U)` and then everywhere by the carry
  · have hgsep : IsSeparated B S hS (yoneda.map σ ≫ Ψ) := by
      rw [hgeq]
      exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS eW.hom)
        (isSeparated_comp B S hS _ _
          (isSeparated_of_mono C.ι (mono_of_isOpenImmersion B S hS C.ι hCo.2))
          (isSeparated_pullbackSnd B S hS π hpsep))
    refine exists_isFiniteLocallyFreeOfRank_lt_of_denseRange B S hS C.toFunctor.reprX
      (yoneda.map σ ≫ Ψ) hY hgEt hgsep
      (hasUniversallyBoundedFibers_of_isOpenImmersion B S hS Ψ hΨrr σ hσsch d hbndΨ)
      d j hdense ?_
    intro kk hkk TT eTT ξ Vf q i hsq hrange
    -- the omitted point, from the graph over a point of `j(U)`
    obtain ⟨t₀⟩ := nonempty_points_yoneda_of_isoSpec_toScheme B S hS TT eTT
    obtain ⟨w, hwy, hwC⟩ := exists_notMem_range_pointsMap_ι_of_mem_range_pointsMap B S hS j π
      C hCpt (hrange ⟨t₀, rfl⟩)
    exact isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits B S hS Ψ hΨrr σ hσsch d
      eTT ξ (hbndΨ kk hkk TT eTT ξ)
      (exists_notMem_range_toScheme_map_pullback_snd_of_iso B S hS _ C eP eW σ hmapσ hΨrr ξ w t₀
        hwy hwC) q i hsq


/-! ### The summand as a chart of the open subspace of `Y` it covers -/

/-- **The input of the recursion of [Stacks, Tag 09YB].** The complementary summand `W` of the
splitting is a *surjective* étale chart of the open subspace `V ⊆ Y` cut out by its image, and
every field-valued fibre of that chart has degree strictly below `d`; what `V` misses of `Y` is
contained in `j(U)`.

This is `AlgebraicGeometry.Space.exists_graphComplement_isEtale_isFiniteLocallyFreeOfRank_lt`
with its étale morphism factored through its image by Stacks 06NF
(`AlgebraicGeometry.Space.factorThroughEtaleImage` and the two assertions about it), which is
what turns the drop into a chart of a *smaller* space to recurse on: the degrees transfer because
`V.ι` is a monomorphism, so a cartesian square over the factored morphism is cartesian over the
original one (`CategoryTheory.isPullback_comp_mono`).

The factorization `φ` through the chart is integral, which is what makes the recursion's chart
quasi-compact and separated without any affineness. The recursion itself — covering `V` at the
smaller bound, glueing the result with the reduced induced structure on `Y ∖ V`, and descending
along the integral `π` — is
`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_chart_fibre_le`. -/
theorem exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (U : BigFppfOver B S hS)
    (j : yoneda.obj U ⟶ Y) (π : Y ⟶ X)
    (hj : IsOpenImmersion B S hS j) (hπ : IsIntegralHom B S hS π)
    (hp : IsEtale B S hS (j ≫ π)) (hpsep : IsSeparated B S hS (j ≫ π))
    (hpsurj : IsSurjective B S hS (j ≫ π))
    (hdense : DenseRange (pointsMap B S hS (yoneda.obj U) j))
    (d : ℕ)
    (hd : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ζ : yoneda.obj T ⟶ X) (Q : BigFppfOver B S hS) (q : Q ⟶ T)
      (c : yoneda.obj Q ⟶ yoneda.obj U),
      IsPullback c (yoneda.map q) (j ≫ π) ζ →
        ∃ r : ℕ, r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) :
    ∃ (Wc : BigFppfOver B S hS) (V : Subfunctor Y) (g' : yoneda.obj Wc ⟶ V.toFunctor)
      (φ : yoneda.obj Wc ⟶ yoneda.obj U),
      IsOpenSubspace B S hS V ∧
      IsEtale B S hS g' ∧ IsSurjective B S hS g' ∧
      IsIntegralHom B S hS φ ∧
      (g' ≫ V.ι) ≫ π = φ ≫ (j ≫ π) ∧
      Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
          Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.univ ∧
      ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
        (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
        (ξ : yoneda.obj T ⟶ V.toFunctor) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
        (i : yoneda.obj Vf ⟶ yoneda.obj Wc),
        IsPullback i (yoneda.map q) g' ξ →
          ∃ r : ℕ, r < d ∧
            IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r := by
  classical
  obtain ⟨Wc, g, φ, hgEt, hφint, hfac, hcov, hdrop⟩ :=
    exists_graphComplement_isEtale_isFiniteLocallyFreeOfRank_lt B S hS hX hY U j π hj hπ hp
      hpsep hpsurj hdense d hd
  set V : Subfunctor Y :=
    openSubspaceOfPoints B S hS Y (Set.range (pointsMap B S hS (yoneda.obj Wc) g))
  have hVopen : IsOpenSubspace B S hS V :=
    isOpenSubspace_openSubspaceOfPoints_range_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS Wc) hY hgEt
  have hVrange : Set.range (pointsMap B S hS V.toFunctor V.ι) =
      Set.range (pointsMap B S hS (yoneda.obj Wc) g) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  set g' : yoneda.obj Wc ⟶ V.toFunctor :=
    factorThroughEtaleImage B S hS hY Wc g V hVopen hVrange
  have hg'fac : g' ≫ V.ι = g :=
    factorThroughEtaleImage_comp B S hS hY Wc g V hVopen hVrange
  have _ : Mono V.ι := mono_of_isOpenImmersion B S hS V.ι hVopen.2
  refine ⟨Wc, V, g', φ, hVopen, ?_, ?_, hφint, ?_, ?_, ?_⟩
  · exact isEtale_of_presheaf_etale B S hS
      (etale_factor_through_etaleImage B S hS Wc g (presheaf_etale_of_isEtale B S hS hgEt)
        V hVopen g' hg'fac)
  · exact isSurjective_of_presheafSurjective B S hS g'
      (surjective_factor_through_etaleImage B S hS Wc g V hVopen hVrange g' hg'fac)
  · rwa [hg'fac]
  · rwa [hVrange]
  · intro kk hkk TT eTT ξ Vf q i hsq
    refine hdrop kk hkk TT eTT (ξ ≫ V.ι) Vf q i ?_
    have := isPullback_comp_mono hsq V.ι
    rwa [hg'fac] at this

end AlgebraicGeometry.Space

end
