module

public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv.IdealDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv.ChartConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv.Invertibility

/-!
# The étale-chart characterization of effective Cartier divisors on an algebraic space

Stacks 083C lists four conditions on a closed subspace `D` of an algebraic space `X` over a
scheme `S` and asserts that they are equivalent:

1. `D` is an effective Cartier divisor on `X`, that is, its defining ideal sheaf `𝓘_D` is an
   invertible `𝒪_X`-module on the small étale site of `X`;
2. there is a scheme `U` and a surjective étale morphism `U ⟶ X` with `D ×_X U` an effective
   Cartier divisor on `U`;
3. for *every* scheme `U` and every étale morphism `U ⟶ X`, the inverse image `D ×_X U` is an
   effective Cartier divisor on `U`;
4. every point of `|D|` admits an étale pointed morphism `(U, u) ⟶ (X, x)` with `U = Spec A`
   affine and `D ×_X U = Spec (A / (f))` for a nonzerodivisor `f ∈ A`.

The four conditions are already stated in the library: (1) is
`AlgebraicGeometry.Space.IsEffectiveCartierDivisor` (Stacks 083B) and (2), (3), (4) are
`AlgebraicGeometry.Space.HasEffectiveCartierEtaleCover`,
`AlgebraicGeometry.Space.HasEffectiveCartierEtalePullbacks` and
`AlgebraicGeometry.Space.HasAffinePrincipalEtaleNeighborhoods` of
`StacksFrontier/AlgebraicGeometry/Spaces/EffectiveCartierEtaleCharts.lean`.  This file proves the
implications between the four conditions and their equivalence, from the three files it
re-exports: `IdealDescent` (the scheme-level descent), `ChartConditions` (the chart lemmas, the
points of the small étale site, and the rank-one bridge from (1)) and `Invertibility` (the
trivialization of the defining ideal sheaf on charts).

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_tfae`: **Stacks 083C**, the equivalence of
  the four conditions.
* `AlgebraicGeometry.Space.hasEffectiveCartierEtaleCover_iff_etalePullbacks` and
  `AlgebraicGeometry.Space.hasEffectiveCartierEtalePullbacks_iff_hasAffinePrincipal`:
  **conditions (2), (3) and (4) of Stacks 083C are equivalent.**
* `AlgebraicGeometry.Space.hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier`,
  `AlgebraicGeometry.Space.hasEffectiveCartierEtaleCover_of_isEffectiveCartier` and
  `AlgebraicGeometry.Space.hasAffinePrincipalEtaleNeighborhoods_of_isEffectiveCartier`:
  **condition (1) implies conditions (2), (3) and (4).**
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtalePullbacks`,
  `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover` and
  `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods`:
  **each of conditions (2), (3) and (4) implies condition (1).**
* `Stacks.Divisors.isEffectiveCartierDivisor_of_flat_universallyOpen_pointwise`: the
  scheme-level input that makes (4) ⟹ (3) work, and which is of independent interest:
  **effective Cartier-ness of an ideal sheaf of a scheme descends along flat universally open
  morphisms, checked one point of the target at a time.**  Only the pullback direction of this,
  `Stacks.Divisors.isPullbackDefined_of_flat` of Stacks 02OO, was available before.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_definingIdealSheaf`: Stacks 0B8Q
  applied to the defining ideal sheaf on the small étale site, which is the bridge from
  condition (1) to the chart conditions.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_definingIdealSheaf_of_etalePullbacks`:
  the converse bridge, **condition (3) implies the rank clause of condition (1)**: if the
  inverse image of `D` is an effective Cartier divisor on every étale scheme chart then `𝓘_D` is
  finite locally free of rank one on the small étale site.
* `AlgebraicGeometry.Space.exists_index_schemePoint_of_sieve_mem`: a covering sieve of the
  small étale site is jointly surjective on the points of the underlying schemes.
* `AlgebraicGeometry.Space.exists_fieldValuedPoint_of_isPullback`: a matching pair of points of
  two charts comes from a point of their fibre product.

## Implementation notes

**The universe of the sections, and how the chart conditions reach condition (1).** Conditions
(2), (3), (4) produce a family of étale charts covering `X` on each of which `𝓘_D` is isomorphic
to the structure sheaf, that is, they make `𝓘_D` finite locally free of rank one on the small
étale site.  The passage from there to invertibility is Stacks 0B8M, and the forms of it that
construct the inverse as the dual sheaf `SheafHom_{𝒪}(L, 𝒪)` of Stacks 03EM are stated only for
a sheaf of modules whose sections live in the universe `max u v` of a site `C : Type u` with
`Category.{v} C`.  The small étale site of an algebraic space over `Scheme.{u}` is
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects form a `Type (u + 1)` while the
sections of `𝒪_X` are in `Type u`, so the dual sheaf of `𝓘_D` is one universe too large.  What
applies instead is
`AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall`,
which trades that universe relation for essential smallness of the site — a hypothesis the
small étale site satisfies at the universe of its schemes.

**What the 0B8Q converse buys.** The other half of Stacks 0B8Q — an invertible module on a
locally ringed site is finite locally free of rank one — is
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'`, which *is*
stated at a free section universe (it needs no dual sheaf).  Its two sheafification hypotheses
hold for the small étale site at `AddCommGrpCat.{u}`, and local ringedness is Stacks 04KH,
`AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`.  That is what makes (1) ⟹ (3)
available.

**Reading the chart conditions as conditions on one ideal sheaf.** Throughout, the inverse
image `D ×_X U` on a chart `g : h_U ⟶ X` is the canonical base change `D.2.2.rep.snd g`
supplied by relative representability, and the chart condition is effective Cartier-ness of
the single ideal sheaf `(D ×_X U ⟶ U).ker`; that reduction is
`AlgebraicGeometry.Space.isSchemeEffectiveCartierPullback_iff`, and on an affine chart that
kernel is the ideal sheaf of `AlgebraicGeometry.Space.definingIdealAt` by
`AlgebraicGeometry.Space.ker_rep_snd_eq_ofIdealTop_definingIdealAt`.  No presentation data is
manipulated here beyond those two bridges.

**Why (2) ⟹ (4) needs no descent.** The surjective chart `U` of condition (2) already carries
an effective Cartier ideal sheaf, and a point of `|D|` lifts to a point of `D ×_X U` because
`U ⟶ X` is surjective on points.  Shrinking `U` to an affine open around the image of that
point and applying the affine-local form of Stacks 01WS,
`Stacks.CartierAffineLocal.exists_affineOpen_isRegular`, produces the pointed affine chart of
condition (4) directly.  Descent enters only in (4) ⟹ (3), where an arbitrary étale chart has
to be compared with the charts supplied by (4); the comparison is made on a common refinement,
which is flat and universally open over the arbitrary chart, and that is what
`Stacks.Divisors.isEffectiveCartierDivisor_of_flat_universallyOpen_pointwise` descends along.

**The descent argument on schemes.** Let `q : W ⟶ Y` be flat and universally open and let
`I.comap q` be effective Cartier near a point `w` of `W` above `y ∈ Y`.  Shrinking twice — to
an affine open `A'` of `W` on which `I.comap q` is generated by a nonzerodivisor, and then to a
basic open `Y.basicOpen g` of an affine open of `Y` whose points are all images of points of
`A'` — makes `Γ(A' ∩ q⁻¹(Y.basicOpen g))` a faithfully flat `Γ(Y, Y.basicOpen g)`-algebra, by
`Module.FaithfullyFlat.of_comap_surjective`.  Over a faithfully flat extension the ideal
`I.ideal` becomes free of rank one, hence is finite flat of rank one to begin with
(`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`,
`Module.Flat.of_flat_tensorProduct`), hence free after one further localization
(`Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant`).  A free ideal of rank one is
generated by a nonzerodivisor, and the converse half of Stacks 01WS,
`Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_isRegular`, closes the
argument.  Universal openness is used only to make the image of `A'` open in `Y`, so that the
basic open `Y.basicOpen g` can be chosen inside it.

**Points.** Points of an algebraic space are the equivalence classes of field-valued points of
Stacks 03BU, and the translation between a point of a chart and a point of the underlying
scheme is `AlgebraicGeometry.Space.pointsToScheme`, a bijection by
`AlgebraicGeometry.Space.pointsEquivScheme`.  One fact about points is proved here
because the library does not have it: a point of a fibre product of presheaves is the image of
a field-valued point of the fibre product
(`AlgebraicGeometry.Space.exists_fieldValuedPoint_of_isPullback`).  That a covering sieve of
the small étale site may be tested on scheme points
(`AlgebraicGeometry.Space.exists_index_schemePoint_of_sieve_mem`) is then
`AlgebraicGeometry.Space.exists_geo_lift_at_chart_point` read through the point of the site of
Stacks 04K0; it is the converse of
`AlgebraicGeometry.Space.smallEtale_sieve_of_pointwise_covering`.

## References

* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (2) implies condition (4) -/

/-- **Stacks 083C, (2) ⟹ (4).** If the inverse image of `D` is an effective Cartier divisor on
one surjective étale scheme chart, then every point of `|D|` has an affine étale neighbourhood
on which `D` is cut out by a nonzerodivisor.

The point of `|D|` lifts to a field-valued point of `D ×_X U` on the surjective chart, whose
image in `U` lies in the support of the chart ideal sheaf.  By the affine-local form of
Stacks 01WS that ideal sheaf is generated by a nonzerodivisor on an affine open `V` of `U`
around that image; `V` is again an étale chart of `X`, the inverse image of `D` on it is the
base change of `D ×_X U`, and its ideal sheaf is therefore the principal ideal sheaf of the
restricted generator. -/
@[stacks 083C "part (2) implies part (4)"]
theorem hasAffinePrincipalEtaleNeighborhoods_of_hasEffectiveCartierEtaleCover
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (h : HasEffectiveCartierEtaleCover B S hS X D) :
    HasAffinePrincipalEtaleNeighborhoods B S hS X D := by
  obtain ⟨U, g, hg, hsurj, hcart⟩ := h
  set T := BigFppfOver.toScheme B S hS
  set j := D.2.2.rep.snd g
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion (T.map j) := D.2.2.property_snd g
  have hrange : D.1.preimage g = Subfunctor.range (yoneda.map j) :=
    preimage_eq_range_rep_snd B S hS X D U g
  have hI : Stacks.Divisors.IsEffectiveCartierDivisor (T.map j).ker :=
    (isSchemeEffectiveCartierPullback_iff B S hS X D U g).1 hcart
  intro x
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_rep_pullback_of_isSurjective B S hS X D U g hsurj x
  set t := T.map (p.value ≫ j) with ht
  have hwsupp : t (IsLocalRing.closedPoint p.carrier) ∈ ((T.map j).ker).supportSet := by
    show _ ∈ (((T.map j).ker).support : Set (T.obj U))
    rw [← Scheme.IdealSheafData.range_subschemeι]
    refine ⟨(Stacks.Divisors.closedImmersionKerIso (T.map j)).hom
      ((T.map p.value) (IsLocalRing.closedPoint p.carrier)), ?_⟩
    show ((Stacks.Divisors.closedImmersionKerIso (T.map j)).hom ≫
      ((T.map j).ker).subschemeι) _ = _
    rw [← Stacks.Divisors.closedImmersion_eq_kerIso_comp]
    rw [ht, Functor.map_comp]
    rfl
  obtain ⟨V, hwV, f, hf, hgen⟩ := Stacks.CartierAffineLocal.exists_affineOpen_isRegular
    ((T.map j).ker) hI (t (IsLocalRing.closedPoint p.carrier))
  have hVB : B.Contains V.1.toScheme :=
    (Scheme.size_coe_opens_le (T.obj U) V.1).trans_lt U.left.property
  set U' : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (V.1.ι ≫ U.hom.hom) : B.obj hVB ⟶ B.obj hS) with hU'
  set k : U' ⟶ U := Over.homMk (ObjectProperty.homMk V.1.ι) with hk
  have hkm : T.map k = V.1.ι := rfl
  have hketale : Etale (T.map k) := by
    rw [hkm]
    infer_instance
  have hg' : IsEtale B S hS (yoneda.map k ≫ g) := isEtale_yoneda_map_comp B S hS g k hketale hg
  have htr : Set.range t ⊆ Set.range V.1.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨t z, ?_⟩, rfl⟩
    have hz : z = IsLocalRing.closedPoint p.carrier :=
      Subsingleton.elim (α := PrimeSpectrum p.carrier) _ _
    rw [hz]
    exact hwV
  set t' := IsOpenImmersion.lift V.1.ι t htr
  have ht' : t' ≫ V.1.ι = t := IsOpenImmersion.lift_fac V.1.ι t htr
  set q : p.siteObject ⟶ U' := Over.homMk (ObjectProperty.homMk t') (by
    apply ObjectProperty.hom_ext
    show t' ≫ (V.1.ι ≫ U.hom.hom) = p.toBase
    rw [← Category.assoc, ht']
    exact congrArg (fun z => z.hom) (p.value ≫ j).w)
  have hq : q ≫ k = p.value ≫ j := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact ht'
  set p' : FieldValuedPoint B S hS (yoneda.obj U') :=
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := q }
  have hpb := T.map_isPullback (IsPullback.of_hasPullback k j)
  have hci' : _root_.AlgebraicGeometry.IsClosedImmersion (T.map (pullback.fst k j)) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have hprincipal : (T.map (pullback.fst k j)).ker =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {V.1.topIso.inv.hom f}) := by
    rw [Stacks.Divisors.ker_eq_comap_of_isPullback hpb, hkm]
    exact Stacks.Divisors.comap_ι_eq_ofIdealTop_of_ideal_eq_span _ V.1 V.2 f hgen
  obtain ⟨e', he'⟩ : ∃ e' : T.obj (pullback k j) ≅
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {V.1.topIso.inv.hom f})).subscheme,
      T.map (pullback.fst k j) = e'.hom ≫
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.span {V.1.topIso.inv.hom f})).subschemeι := by
    rw [← hprincipal]
    exact ⟨Stacks.Divisors.closedImmersionKerIso _,
      Stacks.Divisors.closedImmersion_eq_kerIso_comp _⟩
  refine ⟨U', yoneda.map k ≫ g, p'.class B S hS _, V.2, hg', ?_,
    V.1.topIso.inv.hom f, pullback k j, pullback.fst k j, e',
    Stacks.Divisors.isRegular_ringEquiv
      V.1.topIso.symm.commRingCatIsoToRingEquiv hf, he', ?_⟩
  · rw [← hp]
    show (FieldValuedPoint.map B S hS _ (yoneda.map k ≫ g) p').class B S hS _ =
      (FieldValuedPoint.map B S hS _ (yoneda.map j ≫ g) p).class B S hS _
    apply congrArg (FieldValuedPoint.class B S hS X.1)
    show (⟨p.carrier, p.contained, p.toBase, g.app _ (q ≫ k)⟩ :
      FieldValuedPoint B S hS X.1) =
        ⟨p.carrier, p.contained, p.toBase, g.app _ (p.value ≫ j)⟩
    rw [hq]
  · show (D.1.preimage g).preimage (yoneda.map k) = _
    rw [hrange]
    exact (Subfunctor.range_snd_eq_preimage_range_of_isPullback
      (yoneda.map_isPullback (IsPullback.of_hasPullback k j).flip)).symm

/-! ### The equivalence of conditions (2), (3) and (4) -/

/-- Affine étale charts around every point on which the defining ideal is generated by a
nonzerodivisor give effective Cartier inverse images on every étale scheme chart. -/
private theorem hasEffectiveCartierEtalePullbacks_of_affine_charts_isRegular_span
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (h : ∀ x : points B S hS X.1,
      ∃ (V : SmallEtale B S hS X.1) (v : points B S hS (yoneda.obj V.1.left)),
        IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) ∧
        pointsMap B S hS (yoneda.obj V.1.left) V.1.hom v = x ∧
        ∃ f : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤),
          IsRegular f ∧ definingIdealAt B S hS X D (op V) = Ideal.span {f}) :
    HasEffectiveCartierEtalePullbacks B S hS X D := by
  refine hasEffectiveCartierEtalePullbacks_of_pointwise_charts B S hS X D fun x => ?_
  obtain ⟨V, v, haff, hv, f, hf, hgen⟩ := h x
  exact ⟨V.1.left, V.1.hom, v, isEtale_of_presheaf_etale B S hS V.2, hv,
    isSchemeEffectiveCartierPullback_of_isRegular_span B S hS X D V haff f hf hgen⟩

/-- **Stacks 083C, (4) ⟹ (3).** If every point of `|D|` has an affine étale neighbourhood on
which `D` is cut out by a nonzerodivisor, then the inverse image of `D` is an effective Cartier
divisor on every étale scheme chart. -/
@[stacks 083C "part (4) implies part (3)"]
theorem hasEffectiveCartierEtalePullbacks_of_hasAffinePrincipal (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1)
    (h : HasAffinePrincipalEtaleNeighborhoods B S hS X D) :
    HasEffectiveCartierEtalePullbacks B S hS X D := by
  exact hasEffectiveCartierEtalePullbacks_of_affine_charts_isRegular_span B S hS X D
    (exists_affine_chart_isRegular_span_of_hasAffinePrincipal B S hS X D h)

/-- **Stacks 083C, (3) ⟺ (4).** The inverse image of a closed subspace is an effective Cartier
divisor on every étale scheme chart if and only if every point of `|D|` has an affine étale
neighbourhood on which the subspace is cut out by a nonzerodivisor. -/
@[stacks 083C "parts (3) and (4)"]
theorem hasEffectiveCartierEtalePullbacks_iff_hasAffinePrincipal (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) :
    HasEffectiveCartierEtalePullbacks B S hS X D ↔
      HasAffinePrincipalEtaleNeighborhoods B S hS X D :=
  ⟨fun h => hasAffinePrincipalEtaleNeighborhoods_of_hasEffectiveCartierEtaleCover B S hS X D
      (hasEffectiveCartierEtaleCover_of_hasEffectiveCartierEtalePullbacks B S hS X D h),
    hasEffectiveCartierEtalePullbacks_of_hasAffinePrincipal B S hS X D⟩

/-- **Stacks 083C, (2) ⟺ (3).** The inverse image of a closed subspace is an effective Cartier
divisor on one surjective étale scheme chart if and only if it is so on every étale scheme
chart.

The nontrivial direction passes through condition (4): a surjective chart gives affine charts
cut out by nonzerodivisors at every point of `|D|`, and those descend to an arbitrary chart. -/
@[stacks 083C "parts (2) and (3)"]
theorem hasEffectiveCartierEtaleCover_iff_etalePullbacks (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) :
    HasEffectiveCartierEtaleCover B S hS X D ↔
      HasEffectiveCartierEtalePullbacks B S hS X D :=
  ⟨fun h => hasEffectiveCartierEtalePullbacks_of_hasAffinePrincipal B S hS X D
      (hasAffinePrincipalEtaleNeighborhoods_of_hasEffectiveCartierEtaleCover B S hS X D h),
    hasEffectiveCartierEtaleCover_of_hasEffectiveCartierEtalePullbacks B S hS X D⟩

/-! ### Condition (1) implies the chart conditions -/

universe v₀ w₀

/-- **Stacks 083C, (1) ⟹ (3).** If a closed subspace is an effective Cartier divisor, then its
inverse image is an effective Cartier divisor on every étale scheme chart. -/
@[stacks 083C "part (1) implies part (3)"]
theorem hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (h : IsEffectiveCartierDivisor B S hS X D) :
    HasEffectiveCartierEtalePullbacks B S hS X D := by
  exact hasEffectiveCartierEtalePullbacks_of_affine_charts_isRegular_span B S hS X D
    (exists_affine_chart_isRegular_span_of_isFiniteLocallyFree B S hS X D
      (isFiniteLocallyFreeOfRank_one_definingIdealSheaf B S hS X D h))

/-- **Stacks 083C, (1) ⟹ (2).** If a closed subspace is an effective Cartier divisor, then its
inverse image is an effective Cartier divisor on some surjective étale scheme chart. -/
@[stacks 083C "part (1) implies part (2)"]
theorem hasEffectiveCartierEtaleCover_of_isEffectiveCartier (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (h : IsEffectiveCartierDivisor B S hS X D) :
    HasEffectiveCartierEtaleCover B S hS X D :=
  hasEffectiveCartierEtaleCover_of_hasEffectiveCartierEtalePullbacks B S hS X D
    (hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X D h)

/-- **Stacks 083C, (1) ⟹ (4).** If a closed subspace is an effective Cartier divisor, then
every point of `|D|` has an affine étale neighbourhood on which the subspace is cut out by a
nonzerodivisor. -/
@[stacks 083C "part (1) implies part (4)"]
theorem hasAffinePrincipalEtaleNeighborhoods_of_isEffectiveCartier (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (h : IsEffectiveCartierDivisor B S hS X D) :
    HasAffinePrincipalEtaleNeighborhoods B S hS X D :=
  hasAffinePrincipalEtaleNeighborhoods_of_hasEffectiveCartierEtaleCover B S hS X D
    (hasEffectiveCartierEtaleCover_of_isEffectiveCartier B S hS X D h)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Conditions (2), (3) and (4) imply condition (1) -/

/-- **Stacks 083C, condition (3) implies rank one.** If the inverse image of a closed subspace
`D` is an effective Cartier divisor on every étale scheme chart, then the defining ideal sheaf
of `D` is finite locally free of rank one on the small étale site of `X`.

Over an arbitrary chart the affine opens on which the chart ideal sheaf is generated by a
nonzerodivisor are again charts and they cover it; over such a chart the defining ideal is
generated by the pullback of that nonzerodivisor at *every* chart above it, so multiplication by
it is an isomorphism from the structure sheaf onto `𝓘_D`, which is a one-legged colimit cofan of
the structure sheaf. -/
@[stacks 083C "part (3) implies the rank clause of part (1)"]
theorem isFiniteLocallyFreeOfRank_one_definingIdealSheaf_of_etalePullbacks
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (h : HasEffectiveCartierEtalePullbacks B S hS X D) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      (definingIdealSheaf B S hS X D).toSheafOfModules 1 := by
  intro U
  refine ⟨_, _, _,
    sieve_ofArrows_nonempty_unitIso_definingIdealSheaf_mem B S hS X D h U, ?_⟩
  rintro ⟨V, m, ⟨e⟩⟩
  refine ⟨fun _ => e.hom, ⟨Limits.Cofan.IsColimit.mk _ (fun t => e.inv ≫ t.inj 0) ?_ ?_⟩⟩
  · intro t j
    obtain rfl : j = 0 := Subsingleton.elim j 0
    exact Iso.hom_inv_id_assoc e (t.inj 0)
  · intro t n hn
    have h0 : e.hom ≫ n = t.inj 0 := hn 0
    exact (Iso.inv_hom_id_assoc e n).symm.trans (congrArg (fun q => e.inv ≫ q) h0)

/-- **Stacks 083C, (3) ⟹ (1).** If the inverse image of a closed subspace is an effective
Cartier divisor on every étale scheme chart, then the subspace is an effective Cartier divisor.

The defining ideal sheaf is then finite locally free of rank one on the small étale site, and
the small étale site is essentially small at the universe of the sections of its structure
sheaf, so Stacks 0B8M applies to it. -/
@[stacks 083C "part (3) implies part (1)"]
theorem isEffectiveCartierDivisor_of_hasEffectiveCartierEtalePullbacks
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (h : HasEffectiveCartierEtalePullbacks B S hS X D) :
    IsEffectiveCartierDivisor B S hS X D := by
  have hsmall : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS X.1))
  have h₁ : HasWeakSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
  have h₂ : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall
      (smallEtaleRingedSite B S hS X.1 X.2) _
      (isFiniteLocallyFreeOfRank_one_definingIdealSheaf_of_etalePullbacks B S hS X D h))

/-- **Stacks 083C, (2) ⟹ (1).** If the inverse image of a closed subspace is an effective
Cartier divisor on one surjective étale scheme chart, then the subspace is an effective Cartier
divisor. -/
@[stacks 083C "part (2) implies part (1)"]
theorem isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (h : HasEffectiveCartierEtaleCover B S hS X D) :
    IsEffectiveCartierDivisor B S hS X D :=
  isEffectiveCartierDivisor_of_hasEffectiveCartierEtalePullbacks B S hS X D
    ((hasEffectiveCartierEtaleCover_iff_etalePullbacks B S hS X D).1 h)

/-- **Stacks 083C, (4) ⟹ (1).** If every point of `|D|` has an affine étale neighbourhood of
`X` on which `D` is cut out by a nonzerodivisor, then `D` is an effective Cartier divisor. -/
@[stacks 083C "part (4) implies part (1)"]
theorem isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (h : HasAffinePrincipalEtaleNeighborhoods B S hS X D) :
    IsEffectiveCartierDivisor B S hS X D :=
  isEffectiveCartierDivisor_of_hasEffectiveCartierEtalePullbacks B S hS X D
    ((hasEffectiveCartierEtalePullbacks_iff_hasAffinePrincipal B S hS X D).2 h)

/-- **Stacks 083C.** For a closed subspace `D` of an algebraic space `X` over a scheme `S` the
following are equivalent: `D` is an effective Cartier divisor on `X`; the inverse image of `D`
is an effective Cartier divisor on some surjective étale scheme chart of `X`; it is so on every
étale scheme chart of `X`; and every point of `|D|` has an affine étale neighbourhood of `X` on
which `D` is cut out by a nonzerodivisor. -/
@[stacks 083C "the equivalence of parts (1), (2), (3) and (4)"]
theorem isEffectiveCartierDivisor_tfae (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) :
    List.TFAE
      [IsEffectiveCartierDivisor B S hS X D,
        HasEffectiveCartierEtaleCover B S hS X D,
        HasEffectiveCartierEtalePullbacks B S hS X D,
        HasAffinePrincipalEtaleNeighborhoods B S hS X D] := by
  tfae_have 1 → 2 := hasEffectiveCartierEtaleCover_of_isEffectiveCartier B S hS X D
  tfae_have 2 → 3 := (hasEffectiveCartierEtaleCover_iff_etalePullbacks B S hS X D).1
  tfae_have 3 → 4 := (hasEffectiveCartierEtalePullbacks_iff_hasAffinePrincipal B S hS X D).1
  tfae_have 4 → 1 := isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods B S hS X D
  tfae_finish

end AlgebraicGeometry.Space

end
