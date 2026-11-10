module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingRationalFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeDivisorPoleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsMeromorphicChartFraction

/-!
# An invertible rational function is a unit on a nonempty open, and Stacks 0ENN

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let
`f ∈ R(X)^*`. **Stacks 0ENN** says that the prime divisors `Z` of `X` with generic point `ξ`
such that `f ∉ 𝒪_{X, ξ}`, and the prime divisors `Z` with `ord_Z(f) ≠ 0`, form two locally
finite collections in `|X|`. The source's proof starts: *there exists a nonempty open subspace
`U ⊆ X` such that `f` corresponds to a section of `Γ(U, 𝒪_X^*)`*. This file proves that
sentence from `f ∈ R(X)^*` alone, in the form the order of vanishing needs, and then proves
Stacks 0ENN with exactly the source's hypotheses.

## Main results

* `AlgebraicGeometry.Space.RationalMap.exists_rep_isUnit_affineLineCoordinate`: an invertible
  rational function has a representative on a dense open subspace whose coordinate is a unit at
  every point of that subspace — a section of `Γ(U, 𝒪_X^*)`. The proof represents `f` and
  `f⁻¹` on one dense open subspace and shrinks to a dense open subspace on which the product of
  the two representatives agrees with the constant `1`.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_affine_factors_through_openSubspace`:
  a point of an open subspace of a decent algebraic space has an affine elementary étale
  neighbourhood mapping into that open subspace.
* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_toRationalMap_of_factors`: on an
  affine étale chart factoring through the domain of a representative, the pullback of the
  rational function to `Q(Γ(U, 𝒪_U))` is the image of the coordinate of the representative.
* `AlgebraicGeometry.Space.PrimeDivisor.isUnit_rationalFunctionsToGenericTotalFractionRing`:
  the image of `f` in `Q(𝒪^h_{X, ξ})` under the canonical embedding of Stacks 0ENK is a unit,
  at every prime divisor.
* `Space.exists_isOpen_isUnit_rationalFunctionsToGenericTotalFractionRing_eq_algebraMap`:
  there is a nonempty open `U ⊆ |X|` such that at the generic point `ξ` of every prime divisor
  meeting `U` the image of `f` in `Q(𝒪^h_{X, ξ})` is the image of a unit of `𝒪^h_{X, ξ}`.
* `AlgebraicGeometry.Space.ordRationalFunction_mem_weilDivisor`: the family `Z ↦ ord_Z(f)` is a
  Weil divisor, that is its support is locally finite.
* `Space.locallyFinite_primeDivisor_not_isDefinedAt_and_ordRationalFunction_ne_zero`:
  **Stacks 0ENN**, both collections.

## Implementation notes

The order of vanishing is `AlgebraicGeometry.Space.ordRationalFunction` of Stacks 0ENL, which
is computed through the canonical embedding
`AlgebraicGeometry.Space.genericFractionEmbedding` of Stacks 0ENK; nothing about it is a
parameter. The condition `f ∉ 𝒪_{X, ξ}` is read, as in
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_isDefinedAt`, as `f` not being defined
at `ξ` in the sense of Stacks 0EMQ; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.PrimeDivisorPoleLocus`.

To see that the image of `f` at `ξ ∈ U` comes from a unit of `𝒪^h_{X, ξ}`, the embedding is
computed on an affine elementary étale neighbourhood of `ξ` mapping into the domain of the
unit representative, which is allowed by
`AlgebraicGeometry.Space.PrimeDivisor.neighborhoodTotalFractionRingToGeneric_pullback_eq`;
there the image of `f` is the image of a unit of the global sections of the chart.

## References

* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0EMQ](https://stacks.math.columbia.edu/tag/0EMQ)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- **An invertible rational function is a unit section on a dense open subspace.** A unit `f`
of the ring of rational functions has a representative on a dense open subspace whose
coordinate is a unit at every point of that subspace, that is a section of `Γ(U, 𝒪_X^*)` for a
dense open `U`. This is the first sentence of the source's proof of Stacks 0ENN. -/
theorem RationalMap.exists_rep_isUnit_affineLineCoordinate
    (f : (rationalFunctions B S hS hX)ˣ) :
    ∃ g : PartialMap B S hS hX (affineLineFunctor B S hS),
      g.toRationalMap B S hS = (f : rationalFunctions B S hS hX) ∧
      ∀ T x, IsUnit (affineLineCoordinate B S hS T (g.hom.app T x)) := by
  obtain ⟨p, hp⟩ := RationalMap.exists_rep B S hS (f : rationalFunctions B S hS hX)
  obtain ⟨q, hq⟩ := RationalMap.exists_rep B S hS
    ((f⁻¹ : (rationalFunctions B S hS hX)ˣ) : rationalFunctions B S hS hX)
  obtain ⟨V, hV, hVp, hVq⟩ :=
    exists_isDenseOpenSubspace_le B S hS hX p.dense_open_domain q.dense_open_domain
  have hres : ∀ (r : PartialMap B S hS hX (affineLineFunctor B S hS))
      (a : rationalFunctions B S hS hX), r.toRationalMap B S hS = a →
      ∀ {W} (hW : IsDenseOpenSubspace B S hS hX W) (h : W ≤ r.domain),
        PartialMap.toRationalMap B S hS
          (⟨W, hW, Subfunctor.homOfLe h ≫ r.hom⟩ : PartialMap B S hS hX _) = a :=
    fun r a hr _ hW h => (toRationalMap_restrict B S hS hX r hW h).trans hr
  obtain ⟨n, hn, hnR⟩ := exists_mul_rep B S hS hX V hV
    (Subfunctor.homOfLe hVp ≫ p.hom) (Subfunctor.homOfLe hVq ≫ q.hom)
  obtain ⟨-, o, -, ho, -, hoR⟩ := exists_zero_one_rep B S hS hX V hV
  have hno : PartialMap.toRationalMap B S hS
      (⟨V, hV, n⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) =
      PartialMap.toRationalMap B S hS
        (⟨V, hV, o⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) := by
    rw [hnR, hoR, hres p _ hp hV hVp, hres q _ hq hV hVq, Units.mul_inv]
  obtain ⟨W, hW, hWn, hWo, heq⟩ := (PartialMap.toRationalMap_eq_iff B S hS).1 hno
  refine ⟨⟨W, hW, Subfunctor.homOfLe hWn ≫ Subfunctor.homOfLe hVp ≫ p.hom⟩, ?_, ?_⟩
  · exact hres ⟨V, hV, Subfunctor.homOfLe hVp ≫ p.hom⟩ _ (hres p _ hp hV hVp) hW hWn
  · intro T x
    have key := hn T ((Subfunctor.homOfLe hWn).app T x)
    have h1 : n.app T ((Subfunctor.homOfLe hWn).app T x) =
        o.app T ((Subfunctor.homOfLe hWo).app T x) :=
      congrArg (fun φ => φ.app T x) heq
    rw [h1, ho] at key
    exact IsUnit.of_mul_eq_one _ key.symm

/-- A point of an open subspace `V` of a decent algebraic space has an affine elementary étale
neighbourhood whose structure morphism factors through `V`: restrict an affine neighbourhood,
which exists by Stacks 0BBP, to an affine open around the marked point inside the preimage of
the point set of `V`. -/
theorem ElementaryEtaleNeighborhood.exists_affine_factors_through_openSubspace
    (hdec : IsDecentSpace B S hS X) (x : points B S hS X) (V : Subfunctor X)
    (hV : IsOpenSubspace B S hS V) (hx : x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    ∃ (E : ElementaryEtaleNeighborhood B S hS X hX x) (j : yoneda.obj E.scheme ⟶ V.toFunctor),
      IsAffine E.scheme.left.1 ∧ j ≫ V.ι = E.toSpace := by
  obtain ⟨U₀, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec x
  set R : Set (points B S hS X) := Set.range (pointsMap B S hS V.toFunctor V.ι)
  have hRopen : IsOpen R := isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2
  set e := schemePointsHomeomorph B S hS U₀.scheme
  set O : Set U₀.scheme.left.1 :=
    e.symm ⁻¹' (pointsMap B S hS (yoneda.obj U₀.scheme) U₀.toSpace ⁻¹' R) with hOdef
  have hOopen : IsOpen O :=
    (hRopen.preimage (continuous_pointsMap B S hS U₀.toSpace)).preimage e.symm.continuous
  have hpt : e.symm U₀.point =
      presheafPoint B S hS U₀.scheme U₀.point U₀.residueField_contained := by
    rw [Homeomorph.symm_apply_eq, schemePointsHomeomorph_apply,
      pointsToScheme_presheafPoint]
  have hptO : U₀.point ∈ O := by
    change pointsMap B S hS _ U₀.toSpace (e.symm U₀.point) ∈ R
    rwa [hpt, U₀.map_point]
  obtain ⟨-, ⟨W, hW, rfl⟩, hpW, hWO⟩ :=
    U₀.scheme.left.1.isBasis_affineOpens.exists_subset_of_mem_open hptO hOopen
  let E := openRestrictionNeighborhood B S hS X hX x U₀ W hpW
  have hrange : Set.range (pointsMap B S hS (yoneda.obj E.scheme) E.toSpace) ⊆ R := by
    rintro _ ⟨y, rfl⟩
    change pointsMap B S hS _
      (yoneda.map (openRestrictionMap B S hS X hX x U₀ W) ≫ U₀.toSpace) y ∈ R
    rw [pointsMap_comp_apply]
    set z := pointsMap B S hS _ (yoneda.map (openRestrictionMap B S hS X hX x U₀ W)) y
    have hz : e z ∈ O := by
      rw [schemePointsHomeomorph_apply, pointsToScheme_pointsMap]
      exact hWO (pointsToScheme B S hS _ y).2
    rwa [hOdef, Set.mem_preimage, Homeomorph.symm_apply_apply] at hz
  obtain ⟨j, hj⟩ := (factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS E.scheme) V hV E.toSpace).2 hrange
  exact ⟨E, j, hW, hj⟩

/-- On an affine étale chart whose structure morphism factors through the domain of a
representative `g`, the pullback of the rational function of `g` to `Q(Γ(U, 𝒪_U))` is the image
of the coordinate of `g` on the chart. -/
theorem rationalFunctionsToTotalFractionRing_toRationalMap_of_factors
    (W : BigFppfOver B S hS) [IsAffine W.left.1] [IsReduced W.left.1]
    [IsLocallyNoetherian W.left.1] (c : yoneda.obj W ⟶ X) (hc : IsEtale B S hS c)
    (g : PartialMap B S hS hX (affineLineFunctor B S hS))
    (j : yoneda.obj W ⟶ g.domain.toFunctor) (hj : j ≫ g.domain.ι = c) :
    rationalFunctionsToTotalFractionRing B S hS hX W c hc (g.toRationalMap B S hS) =
      algebraMap Γ(W.left.1, ⊤) (FractionRing Γ(W.left.1, ⊤))
        (affineLineCoordinate B S hS (Opposite.op W) (yonedaEquiv (j ≫ g.hom))) := by
  rw [rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hX W c hc
      (factorsThroughDenseOpens_totalFractionObject B S hS hX W c hc),
    evalSiteRingHom_eq B S hS hX _ g (yoneda.map (totalFractionObjectMap B S hS W) ≫ j)
      (by rw [Category.assoc, hj]),
    Category.assoc, ← yonedaEquiv_naturality, affineLineCoordinate_map]
  exact ΓSpecIso_hom_fromSpecTotalFractionRing_appTop W.left.1 _

variable (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))

/-- The image of an invertible rational function under the canonical embedding
`R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK is a unit, at every prime divisor. -/
theorem PrimeDivisor.isUnit_rationalFunctionsToGenericTotalFractionRing
    (Z : PrimeDivisor B S hS X) (f : (rationalFunctions B S hS hX)ˣ) :
    IsUnit (Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN
      (f : rationalFunctions B S hS hX)) :=
  f.isUnit.map _

/-- If a representative `g` has unit coordinate on its domain and the generic point `ξ` of a
prime divisor lies in that domain, then the image of the rational function of `g` in
`Q(𝒪^h_{X, ξ})` is the image of a unit of `𝒪^h_{X, ξ}`. -/
theorem PrimeDivisor.exists_isUnit_rationalFunctionsToGenericTotalFractionRing_eq_algebraMap
    (Z : PrimeDivisor B S hS X) (g : PartialMap B S hS hX (affineLineFunctor B S hS))
    (hg : ∀ T x, IsUnit (affineLineCoordinate B S hS T (g.hom.app T x)))
    (hZ : Z.genericPoint B S hS X ∈ Set.range (pointsMap B S hS g.domain.toFunctor g.domain.ι)) :
    ∃ r : ↥(Z.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
      Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN
          (g.toRationalMap B S hS) =
        algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec) r := by
  obtain ⟨E, j, hEaff, hj⟩ :=
    ElementaryEtaleNeighborhood.exists_affine_factors_through_openSubspace B S hS hX hdec
      (Z.genericPoint B S hS X) g.domain g.dense_open_domain.1 hZ
  have := hEaff
  have := Z.isReduced_chart B S hS hX hInt E
  have := Z.isLocallyNoetherian_chart B S hS hX hN E
  have : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  refine ⟨Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec E
      (affineLineCoordinate B S hS (Opposite.op E.scheme) (yonedaEquiv (j ≫ g.hom))),
    ?_, ?_⟩
  · rw [yonedaEquiv_comp]
    exact (hg (Opposite.op E.scheme) (yonedaEquiv j)).map
      (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec E)
  · rw [← Z.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX hdec hInt hN E,
      rationalFunctionsToTotalFractionRing_toRationalMap_of_factors B S hS hX E.scheme E.toSpace
        E.etale_toSpace g j hj,
      PrimeDivisor.neighborhoodTotalFractionRingToGeneric, IsLocalization.map_eq]

/-- **An invertible rational function is a unit near the generic points of the prime divisors
meeting a nonempty open.** For `f ∈ R(X)^*` on a locally Noetherian integral algebraic space
there is a nonempty open `U ⊆ |X|` such that, at the generic point `ξ` of every prime divisor
with `ξ ∈ U`, the image of `f` under the canonical embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks
0ENK is the image of a unit of `𝒪^h_{X, ξ}`. This is the source's "`f` corresponds to a section
of `Γ(U, 𝒪_X^*)`", read at those generic points. -/
theorem exists_isOpen_isUnit_rationalFunctionsToGenericTotalFractionRing_eq_algebraMap
    (f : (rationalFunctions B S hS hX)ˣ) :
    ∃ U : Set (points B S hS X), IsOpen U ∧ U.Nonempty ∧
      ∀ Z : PrimeDivisor B S hS X, Z.genericPoint B S hS X ∈ U →
        ∃ r : ↥(Z.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
          Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN
              (f : rationalFunctions B S hS hX) =
            algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec) r := by
  have := IsIntegralSpace.irreducibleSpace B S hS X hInt
  obtain ⟨g, hgf, hg⟩ := RationalMap.exists_rep_isUnit_affineLineCoordinate B S hS hX f
  refine ⟨Set.range (pointsMap B S hS g.domain.toFunctor g.domain.ι),
    isOpen_range_pointsMap_of_isOpenImmersion B S hS g.domain.ι g.dense_open_domain.1.2,
    g.dense_open_domain.2.nonempty, fun Z hZ => ?_⟩
  rw [← hgf]
  exact Z.exists_isUnit_rationalFunctionsToGenericTotalFractionRing_eq_algebraMap B S hS hX hdec
    hInt hN g hg hZ

/-- The order of vanishing `ord_Z(f)` of Stacks 0ENL is zero when the image of `f` in
`Q(𝒪^h_{X, ξ})` is the image of a unit of `𝒪^h_{X, ξ}`. -/
theorem ordRationalFunction_eq_zero_of_eq_algebraMap (f : (rationalFunctions B S hS hX)ˣ)
    (Z : PrimeDivisor B S hS X)
    {r : ↥(Z.genericHenselianLocalRing B S hS hX hInt.isDecentSpace)} (hr : IsUnit r)
    (hfr : Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hInt.isDecentSpace hInt hN
        (f : rationalFunctions B S hS hX) =
      algebraMap _ (Z.genericTotalFractionRing B S hS hX hInt.isDecentSpace) r) :
    ordRationalFunction B S hS hX hInt hN f Z = 0 := by
  have := (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).nontrivial Z
  have := (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).isNoetherianRing Z
  have := (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).krullDimLE Z
  exact Ring.ordTotalFracInt_eq_zero_of_eq_algebraMap _ (f.isUnit.map _) hr hfr

/-- The order-of-vanishing family `Z ↦ ord_Z(f)` of an invertible rational function on a
locally Noetherian integral algebraic space is a Weil divisor: the prime divisors with
`ord_Z(f) ≠ 0` are locally finite. Their generic points avoid the nonempty open of
`Space.exists_isOpen_isUnit_rationalFunctionsToGenericTotalFractionRing_eq_algebraMap`,
and Stacks 0EE5 applies through
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`. -/
theorem ordRationalFunction_mem_weilDivisor (f : (rationalFunctions B S hS hX)ˣ) :
    ordRationalFunction B S hS hX hInt hN f ∈ WeilDivisor B S hS X := by
  classical
  have hirr := IsIntegralSpace.irreducibleSpace B S hS X hInt
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_isUnit_rationalFunctionsToGenericTotalFractionRing_eq_algebraMap B S hS hX
      hInt.isDecentSpace hInt hN f
  have h := locallyFinite_primeDivisor_of_genericPoint_notMem B S hS hX hN hirr
    (fun Z : PrimeDivisor B S hS X ↦ ordRationalFunction B S hS hX hInt hN f Z ≠ 0) U hUopen hUne
    (fun Z hZ hmem ↦ by
      obtain ⟨r, hr, hfr⟩ := hU Z hmem
      exact hZ (ordRationalFunction_eq_zero_of_eq_algebraMap B S hS hX hInt hN f Z hr hfr))
  refine h.subset fun Z p hp => ?_
  rw [Set.mem_ite_empty_right]
  rwa [Set.mem_ite_empty_left] at hp

/-- **Stacks 0ENN.** Let `X` be a locally Noetherian integral algebraic space over `S` and let
`f ∈ R(X)^*`. Then the prime divisors `Z` of `X` whose generic point `ξ` has `f ∉ 𝒪_{X, ξ}` —
`f` not defined at `ξ` in the sense of Stacks 0EMQ — and the prime divisors `Z` with
`ord_Z(f) ≠ 0`, for the order of vanishing of Stacks 0ENL, are both locally finite collections
in `|X|`.

As in the source, both follow from Stacks 0EE5 once the generic points of the prime divisors in
question avoid a nonempty open. For the first collection that open is the domain of a
representative of `f`, which is
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_isDefinedAt`; for the second it is the
open on which `f` is a unit section, which is
`AlgebraicGeometry.Space.ordRationalFunction_mem_weilDivisor`. -/
@[stacks 0ENN "both collections, with the source's hypotheses only: the prime divisors at whose \
  generic point f is not defined (f ∉ 𝒪_{X,ξ}) and those with ord_Z(f) ≠ 0 are locally finite"]
theorem locallyFinite_primeDivisor_not_isDefinedAt_and_ordRationalFunction_ne_zero
    (f : (rationalFunctions B S hS hX)ˣ) :
    LocallyFinite (fun Z : {Z : PrimeDivisor B S hS X //
        ¬ RationalMap.IsDefinedAt B S hS (f : rationalFunctions B S hS hX)
          (Z.genericPoint B S hS X)} ↦ Z.1.support B S hS X) ∧
    LocallyFinite (fun Z : {Z : PrimeDivisor B S hS X //
        ordRationalFunction B S hS hX hInt hN f Z ≠ 0} ↦ Z.1.support B S hS X) := by
  classical
  refine ⟨locallyFinite_primeDivisor_not_isDefinedAt B S hS hX hN
    (IsIntegralSpace.irreducibleSpace B S hS X hInt) _, ?_⟩
  have h : LocallyFinite fun Z : PrimeDivisor B S hS X =>
      if ordRationalFunction B S hS hX hInt hN f Z = 0 then ∅ else Z.support B S hS X :=
    ordRationalFunction_mem_weilDivisor B S hS hX hInt hN f
  refine (h.comp_injective Subtype.val_injective).subset fun Z ↦ ?_
  simp only [Function.comp_apply]
  rw [ite_eq_right Z.2]

end AlgebraicGeometry.Space

end
