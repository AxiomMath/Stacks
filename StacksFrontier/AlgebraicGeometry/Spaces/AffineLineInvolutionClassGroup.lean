module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ClassGroupOfUniversalHomeomorphismToLine
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericTrivialization

/-!
# The class group of the affine line with nonzero points identified with their negatives

Over a field `k` of characteristic different from two, let `X = 𝔸¹_k/\{t ∼ -t ∣ t ≠ 0\}` be the
algebraic space of Stacks 02Z1. This file proves **Stacks 0ENT**: `X` is a smooth, Noetherian,
integral algebraic space over `k`, the squaring map `X → 𝔸¹_k` is a universal homeomorphism and
an isomorphism over `𝔸¹_k ∖ {0}`, the prime divisors of `X` are its closed points, the divisor of
the coordinate `t` is `2 [x]` for the point `x` over the origin, and `Cl(X) = ℤ/2ℤ`.

The class group computation is the general
`AlgebraicGeometry.Space.weilDivisorClassGroupEquivZModTwo`; what is specific to `X` is
integrality and the order of vanishing of `t` along `x`, which is read on the chart `𝔸¹_k → X`
at the origin, an elementary étale neighbourhood of `x` since the residue field there is `k`: on
it `t` pulls back to the square of the coordinate.

## Main results

* `isIntegralSpace_involutionQuotient`: `X` is integral.
* `originDivisor` and `ordRationalFunction_coordinatePullbackUnit_originDivisor`: the prime
  divisor over the origin, along which `t` vanishes to order two.
* `involutionQuotient_classGroup`: **Stacks 0ENT**.
* `not_mono_involutionRelation_of_two_eq_zero`: the characteristic hypothesis is needed for the
  construction.

All names are in the namespace `AlgebraicGeometry.AffineLineInvolution`.

## References

* [Stacks Project, Tag 0ENT](https://stacks.math.columbia.edu/tag/0ENT)
* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AffineLineInvolution

attribute [local instance] Space.pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-! ### The characteristic hypothesis -/

/-- In characteristic two negation of the coordinate is the identity of the affine line. -/
theorem affineLineNeg_eq_id_of_two_eq_zero (h2 : (2 : k) = 0) : affineLineNeg k = 𝟙 _ := by
  ext1
  refine AffineSpace.hom_ext ?_ ?_
  · simp
  · intro i
    cases i
    rw [affineLineNeg_left, AffineSpace.homOfVector_appTop_coord, Over.id_left,
      Scheme.Hom.id_appTop]
    have h2' : (2 : Γ((affineLine k).left, ⊤)) = 0 := by
      have h := map_ofNat ((Scheme.ΓSpecIso (.of k)).inv ≫ (affineLine k).hom.appTop).hom 2
      rw [h2, map_zero] at h
      exact h.symm
    have hc : -coordinate k = coordinate k :=
      neg_eq_of_add_eq_zero_left (by rw [← two_mul, h2', zero_mul])
    exact hc.trans rfl

/-- **The characteristic hypothesis of Stacks 02Z1 is needed.** In characteristic two the graph
of negation on the punctured line is the diagonal, so the morphism `Δ ⨿ Γ ⟶ 𝔸¹_k ×_k 𝔸¹_k` of
the example identifies the two copies of the punctured line and is not a monomorphism: it is not
a relation, and `𝔸¹_k/\{t ∼ -t ∣ t ≠ 0\}` is not the quotient by an equivalence relation. -/
theorem not_mono_involutionRelation_of_two_eq_zero (h2 : (2 : k) = 0) :
    ¬ Mono (involutionRelation k) := by
  intro hm
  have heq : (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) ≫ involutionRelation k =
      (puncturedAffineLineInclusion k ≫ coprod.inl) ≫ involutionRelation k := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, Category.assoc, involutionRelation, prod.lift_fst,
        coprod.inr_desc, coprod.inl_desc, Category.comp_id]
    · rw [Category.assoc, Category.assoc, Category.assoc, involutionRelation, prod.lift_snd,
        coprod.inr_desc, coprod.inl_desc, Category.comp_id,
        affineLineNeg_eq_id_of_two_eq_zero k h2, Category.comp_id]
  have h := (cancel_mono _).1 heq
  have hcmp : IsIso (coprodComparison (Over.forget (Spec (.of k))) (affineLine k)
      (puncturedAffineLine k)) :=
    (PreservesColimitPair.iso (Over.forget (Spec (.of k))) _ _).isIso_hom
  have hl : (coprod.inl : (affineLine k).left ⟶
        (affineLine k).left ⨿ (puncturedAffineLine k).left) ≫
      coprodComparison (Over.forget (Spec (.of k))) (affineLine k) (puncturedAffineLine k) =
      (coprod.inl : affineLine k ⟶ relationScheme k).left :=
    inl_coprodComparison (Over.forget (Spec (.of k))) _ _
  have hr : (coprod.inr : (puncturedAffineLine k).left ⟶
        (affineLine k).left ⨿ (puncturedAffineLine k).left) ≫
      coprodComparison (Over.forget (Spec (.of k))) (affineLine k) (puncturedAffineLine k) =
      (coprod.inr : puncturedAffineLine k ⟶ relationScheme k).left :=
    inr_coprodComparison (Over.forget (Spec (.of k))) _ _
  have h' := congrArg (fun f => f.left) h
  simp only [Over.comp_left, puncturedAffineLineInclusion_left] at h'
  rw [← hl, ← hr, ← Category.assoc] at h'
  have h'' := (cancel_mono _).1 h'
  obtain ⟨p⟩ := (inferInstance : Nonempty (puncturedAffineLine k).left)
  exact inl_ne_inr _ _ _ p (congrArg (fun f => f p) h'').symm

/-! ### Integrality -/

/-- The chart of the involution quotient is étale. -/
theorem isEtale_quotientChart (hchar : (2 : k) ≠ 0) :
    Space.IsEtale B (Spec (.of k)) hk (quotientChart k B hk) :=
  (Space.isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hk _).2
    (presheafEtale_quotientChart k B hk hchar)

/-- The involution quotient is reduced, its chart being the reduced affine line. -/
theorem hasEtaleLocalProperty_isReduced (hchar : (2 : k) ≠ 0) :
    Space.HasEtaleLocalProperty B (Spec (.of k)) hk (involutionQuotient k B hk).obj
      (fun Y : Scheme.{u} => IsReduced Y) :=
  ⟨affineLineChart k B hk, quotientChart k B hk, presheafSurjective_quotientChart k B hk hchar,
    presheafEtale_quotientChart k B hk hchar,
    inferInstanceAs (IsReduced (AffineSpace PUnit.{u + 1} (Spec (.of k))))⟩

/-- The involution quotient is locally Noetherian, its chart being the affine line. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian (hchar : (2 : k) ≠ 0) :
    Space.HasEtaleLocalProperty B (Spec (.of k)) hk (involutionQuotient k B hk).obj
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y) :=
  ⟨affineLineChart k B hk, quotientChart k B hk, presheafSurjective_quotientChart k B hk hchar,
    presheafEtale_quotientChart k B hk hchar, isLocallyNoetherian_affineLine k⟩

/-- The space of points of the involution quotient is irreducible, being the image of the
irreducible affine line under the surjective chart. -/
theorem irreducibleSpace_points (hchar : (2 : k) ≠ 0) :
    IrreducibleSpace (Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj) := by
  have hsurj : Function.Surjective (Space.pointsMap B (Spec (.of k)) hk _ (quotientChart k B hk)) :=
    (Space.presheafSurjective_iff_isSurjective_yoneda B (Spec (.of k)) hk _
      (isAlgebraicSpace_involutionQuotient k hchar B hk) _ _).1
      (presheafSurjective_quotientChart k B hk hchar)
  have : IrreducibleSpace
      (Space.points B (Spec (.of k)) hk (yoneda.obj (affineLineChart k B hk))) :=
    (Space.schemePointsHomeomorph B (Spec (.of k)) hk
      (affineLineChart k B hk)).irreducibleSpace_iff.2 (irreducibleSpace_affineLine k)
  exact hsurj.irreducibleSpace (Space.continuous_pointsMap B (Spec (.of k)) hk _)

/-- **Stacks 0ENT, integrality.** Away from characteristic two, the involution quotient is an
integral algebraic space: it is reduced, decent, being Noetherian, and its space of points is
irreducible. -/
theorem isIntegralSpace_involutionQuotient (hchar : (2 : k) ≠ 0) (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsIntegralSpace B (Spec (.of k)) hk (involutionQuotient k B hk).obj :=
  ⟨hasEtaleLocalProperty_isReduced k B hk hchar,
    Space.isDecentSpace_of_isNoetherian B (Spec (.of k)) hk hZ
      (isAlgebraicSpace_involutionQuotient k hchar B hk)
      (isNoetherian_involutionQuotient k hchar B hk hZ),
    irreducibleSpace_points k B hk hchar⟩

/-! ### The prime divisor over the origin -/

/-- The point of the involution quotient lying over the origin: the image of the origin of the
chart. -/
def originQuotientPoint : Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj :=
  Space.pointsMap B (Spec (.of k)) hk _ (quotientChart k B hk)
    (Space.presheafPoint B (Spec (.of k)) hk (affineLineChart k B hk) (origin k)
      (B.residueField_spec_contains (affineLineChart k B hk).left.property (origin k)))

/-- The point over the origin is the generic point of a prime divisor: the origin of the chart has
coheight one. -/
theorem exists_primeDivisor_genericPoint_eq_originQuotientPoint (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    ∃ Z : Space.PrimeDivisor B (Spec (.of k)) hk (involutionQuotient k B hk).obj,
      Z.genericPoint B (Spec (.of k)) hk _ = originQuotientPoint k B hk := by
  have h := Space.chartPoint_pointsToScheme B (Spec (.of k)) hk (affineLineChart k B hk)
    (quotientChart k B hk) (Space.presheafPoint B (Spec (.of k)) hk (affineLineChart k B hk)
      (origin k) (B.residueField_spec_contains (affineLineChart k B hk).left.property (origin k)))
  refine Space.exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one B (Spec (.of k))
    hk (isAlgebraicSpace_involutionQuotient k hchar B hk)
    (isIntegralSpace_involutionQuotient k B hk hchar hZ).isDecentSpace (affineLineChart k B hk)
    (quotientChart k B hk) (presheafEtale_quotientChart k B hk hchar) _ _ h ?_
  exact (Space.pointsToScheme_presheafPoint B (Spec (.of k)) hk (affineLineChart k B hk) (origin k)
    _).symm ▸ coheight_origin k

/-- The prime divisor `x` of the involution quotient lying over the origin. -/
def originDivisor (hchar : (2 : k) ≠ 0) (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.PrimeDivisor B (Spec (.of k)) hk (involutionQuotient k B hk).obj :=
  (exists_primeDivisor_genericPoint_eq_originQuotientPoint k B hk hchar hZ).choose

/-- The generic point of the prime divisor `originDivisor` is the point over the origin. -/
theorem genericPoint_originDivisor (hchar : (2 : k) ≠ 0) (hZ : B.Contains (⊤_ Scheme.{u})) :
    (originDivisor k B hk hchar hZ).genericPoint B (Spec (.of k)) hk _ =
      originQuotientPoint k B hk :=
  (exists_primeDivisor_genericPoint_eq_originQuotientPoint k B hk hchar hZ).choose_spec

/-- The chart followed by the squaring map is squaring the coordinate. -/
theorem yonedaEquiv_quotientChart_comp_squaringMap :
    yonedaEquiv (quotientChart k B hk ≫ squaringMap k B hk) = affineLineSquare k := by
  have h : (affineLinePointsIso k B hk).inv ≫ (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
        (yoneda.map (affineLineSquare k)) =
      yoneda.map ((Over.post (X := B.obj hk) B.inclusion).preimage (X := affineLineChart k B hk)
        (Y := affineLineChart k B hk) (affineLineSquare k)) ≫ (affineLinePointsIso k B hk).inv :=
    Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
      (V := affineLineChart k B hk) (W := affineLineChart k B hk) (affineLineSquare k)
  rw [quotientChart, Category.assoc, toQuotientSheaf_comp_squaringMap, h, yonedaEquiv_comp,
    yonedaEquiv_yoneda_map]
  exact (Over.post (X := B.obj hk) B.inclusion).map_preimage (X := affineLineChart k B hk)
    (Y := affineLineChart k B hk) (affineLineSquare k)

/-- The pullback of the coordinate along squaring is the square of the coordinate. -/
theorem affineLineSquare_appTop_coordinate :
    (affineLineSquare k).left.appTop (coordinate k) = coordinate k ^ 2 := by
  rw [affineLineSquare_left]
  exact AffineSpace.homOfVector_appTop_coord _ _ _

/-- The square of the coordinate has order of vanishing two at the origin of the affine line. -/
theorem ord_germ_origin_coordinate_sq :
    Ring.ord ((affineLine k).left.presheaf.stalk (origin k))
      ((affineLine k).left.presheaf.germ ⊤ (origin k) trivial (coordinate k ^ 2)) = 2 := by
  have hne : (affineLine k).left.presheaf.germ ⊤ (origin k) trivial (coordinate k) ≠ 0 :=
    fun h => coordinate_ne_zero k (germ_injective_of_isIntegral _ (U := ⊤) (origin k) trivial
      (h.trans (map_zero _).symm))
  rw [map_pow, Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hne),
    ord_germ_eq_one_of_primeIdealOf_eq_span (Y := (affineLine k).left) (q := origin k)
      (primeIdealOf_origin k)]
  rfl

/-- **Stacks 0ENT, the divisor of `t`.** The pullback of the coordinate of the affine line to the
involution quotient vanishes to order two along the prime divisor over the origin: on the chart it
is the square of the coordinate, and the chart is an elementary étale neighbourhood of the origin,
whose residue field is `k`. -/
theorem ordRationalFunction_coordinatePullbackUnit_originDivisor (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.ordRationalFunction B (Spec (.of k)) hk (isAlgebraicSpace_involutionQuotient k hchar B hk)
        (isIntegralSpace_involutionQuotient k B hk hchar hZ)
        (hasEtaleLocalProperty_isLocallyNoetherian k B hk hchar)
        (Space.coordinatePullbackUnit (squaringMap k B hk)
          (isAlgebraicSpace_involutionQuotient k hchar B hk)
          (isIntegralSpace_involutionQuotient k B hk hchar hZ)
          (isIso_squaringMap_pullback_puncturedAffineLine k hchar B hk))
        (originDivisor k B hk hchar hZ) = 2 := by
  have : IsAffine (affineLineChart k B hk).left.1 := isAffine_affineLine k
  have : IsReduced (affineLineChart k B hk).left.1 :=
    inferInstanceAs (IsReduced (AffineSpace PUnit.{u + 1} (Spec (.of k))))
  have : IsLocallyNoetherian (affineLineChart k B hk).left.1 := isLocallyNoetherian_affineLine k
  have hmono : Mono ((affineLineChart k B hk).left.1.fromSpecResidueField (origin k) ≫
      (affineLineChart k B hk).hom.1) :=
    Space.mono_fromSpecResidueField_comp_of_section (affineLine k).hom (constSection k 0)
      (AffineSpace.homOfVector_over _ _)
  let U := Space.elementaryEtaleNeighborhoodOfMonoStructure B (Spec (.of k)) hk
    (affineLineChart k B hk) (isAlgebraicSpace_involutionQuotient k hchar B hk)
    (quotientChart k B hk) (isEtale_quotientChart k B hk hchar) (origin k) hmono _
    (genericPoint_originDivisor k B hk hchar hZ).symm
  have : IsAffine U.scheme.left.1 := isAffine_affineLine k
  have : IsReduced U.scheme.left.1 :=
    inferInstanceAs (IsReduced (AffineSpace PUnit.{u + 1} (Spec (.of k))))
  have : IsLocallyNoetherian U.scheme.left.1 := isLocallyNoetherian_affineLine k
  have ha : Space.rationalFunctionsToTotalFractionRing B (Spec (.of k)) hk
      (isAlgebraicSpace_involutionQuotient k hchar B hk) U.scheme U.toSpace U.etale_toSpace
      ((Space.coordinatePullbackUnit (squaringMap k B hk)
          (isAlgebraicSpace_involutionQuotient k hchar B hk)
          (isIntegralSpace_involutionQuotient k B hk hchar hZ)
          (isIso_squaringMap_pullback_puncturedAffineLine k hchar B hk) :
        Space.rationalFunctions B (Spec (.of k)) hk
          (isAlgebraicSpace_involutionQuotient k hchar B hk))) =
      algebraMap Γ(U.scheme.left.1, ⊤) (FractionRing Γ(U.scheme.left.1, ⊤))
        ((affineLineSquare k).left.appTop (coordinate k)) := by
    have h1 := Space.rationalFunctionsToTotalFractionRing_linePullbackFunction (squaringMap k B hk)
      (isAlgebraicSpace_involutionQuotient k hchar B hk) (affineLineChart k B hk)
      (quotientChart k B hk) (isEtale_quotientChart k B hk hchar) (coordinate k)
    rwa [yonedaEquiv_quotientChart_comp_squaringMap] at h1
  rw [(originDivisor k B hk hchar hZ).ordRationalFunction_eq_ord_germ B (Spec (.of k)) hk _ _ _ U _
    _ ha, affineLineSquare_appTop_coordinate]
  exact (congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_germ_origin_coordinate_sq k)).trans rfl

/-! ### Stacks 0ENT -/

/-- **Stacks 0ENT.** Let `k` be a field of characteristic different from two and let
`X = 𝔸¹_k/\{t ∼ -t ∣ t ≠ 0\}` be the algebraic space of Stacks 02Z1, the quotient of the affine
line by the punctured graph of negation. Then:

1. `X` is an algebraic space, smooth over `k`;
2. the morphism `X → 𝔸¹_k = Spec k[t]` descended from squaring the coordinate is a universal
   homeomorphism which is an isomorphism over `𝔸¹_k ∖ {0}`;
3. `X` is Noetherian and integral, and `|X|` has dimension one;
4. the prime divisors of `X` are the closed points of `X`, a prime divisor corresponding to its
   generic point;
5. the prime divisor `x` of `X` over the origin is a closed point, and the unique point of `X`
   over `0 ∈ 𝔸¹_k`;
6. the classes in `Cl(X)` of the prime divisors other than `x` are zero;
7. the divisor of `t` on `X` is `2 [x]`;
8. `Cl(X) ≅ ℤ/2ℤ`, by an isomorphism sending `[x]` to `1`.

Here `Cl(X)` is the Weil divisor class group of Stacks 0ENR, and `t` is the coordinate of the
affine line, pulled back to a rational function on `X`.

The characteristic hypothesis is that of Stacks 02Z1, where `X` is constructed, which Stacks 05Z6
and Stacks 0ENT continue: in characteristic two the graph of negation is the diagonal, so the
relation `Δ ⨿ Γ ⟶ 𝔸¹_k ×_k 𝔸¹_k` is not a monomorphism and the construction does not produce an
equivalence relation at all. The hypothesis `hZ` that the big fppf site contains the final scheme
is the one under which `AlgebraicGeometry.Space.IsNoetherian` is formulated. -/
@[stacks 0ENT]
theorem involutionQuotient_classGroup (hchar : (2 : k) ≠ 0) (hZ : B.Contains (⊤_ Scheme.{u})) :
    IsAlgebraicSpace B (Spec (.of k)) hk (involutionQuotient k B hk).obj ∧
      Space.IsSmooth B (Spec (.of k)) hk (terminal.from (involutionQuotient k B hk).obj) ∧
      Space.UniversalHomeomorphism B (Spec (.of k)) hk (squaringMap k B hk) ∧
      IsIso (pullback.snd (squaringMap k B hk) (Space.puncturedLineInclusion k B hk)) ∧
      Space.IsNoetherian B (Spec (.of k)) hk hZ (involutionQuotient k B hk).obj ∧
      Space.IsIntegralSpace B (Spec (.of k)) hk (involutionQuotient k B hk).obj ∧
      topologicalKrullDim (Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj) = 1 ∧
      (∃ e : Space.PrimeDivisor B (Spec (.of k)) hk (involutionQuotient k B hk).obj ≃
          {ξ : Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj //
            IsClosed ({ξ} : Set _)},
        ∀ Z, (e Z : Space.points B (Spec (.of k)) hk _) = Z.genericPoint B (Spec (.of k)) hk _) ∧
      IsClosed ({(originDivisor k B hk hchar hZ).genericPoint B (Spec (.of k)) hk _} :
        Set (Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj)) ∧
      (∀ ξ : Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj,
        Space.pointsHomeomorphAffineLine (squaringMap k B hk)
            (universalHomeomorphism_squaringMap k B hk hchar) ξ = origin k ↔
          ξ = (originDivisor k B hk hchar hZ).genericPoint B (Spec (.of k)) hk _) ∧
      (∀ Z : Space.PrimeDivisor B (Spec (.of k)) hk (involutionQuotient k B hk).obj,
        Z ≠ originDivisor k B hk hchar hZ →
          (Space.primeDivisorClass Z : Space.weilDivisorClassGroup B (Spec (.of k)) hk
            (isAlgebraicSpace_involutionQuotient k hchar B hk)
            (isIntegralSpace_involutionQuotient k B hk hchar hZ)
            (hasEtaleLocalProperty_isLocallyNoetherian k B hk hchar)) = 0) ∧
      Space.divRationalFunction B (Spec (.of k)) hk
          (isAlgebraicSpace_involutionQuotient k hchar B hk)
          (isIntegralSpace_involutionQuotient k B hk hchar hZ)
          (hasEtaleLocalProperty_isLocallyNoetherian k B hk hchar)
          (Space.coordinatePullbackUnit (squaringMap k B hk)
            (isAlgebraicSpace_involutionQuotient k hchar B hk)
            (isIntegralSpace_involutionQuotient k B hk hchar hZ)
            (isIso_squaringMap_pullback_puncturedAffineLine k hchar B hk)) =
        2 • Space.primeDivisorClass (originDivisor k B hk hchar hZ) ∧
      ∃ e : Space.weilDivisorClassGroup B (Spec (.of k)) hk
          (isAlgebraicSpace_involutionQuotient k hchar B hk)
          (isIntegralSpace_involutionQuotient k B hk hchar hZ)
          (hasEtaleLocalProperty_isLocallyNoetherian k B hk hchar) ≃+ ZMod 2,
        e (Space.primeDivisorClass (originDivisor k B hk hchar hZ)) = 1 := by
  have hX := isAlgebraicSpace_involutionQuotient k hchar B hk
  have hInt := isIntegralSpace_involutionQuotient k B hk hchar hZ
  have hN := hasEtaleLocalProperty_isLocallyNoetherian k B hk hchar
  have hπ := universalHomeomorphism_squaringMap k B hk hchar
  have hiso := isIso_squaringMap_pullback_puncturedAffineLine k hchar B hk
  have hord := ordRationalFunction_coordinatePullbackUnit_originDivisor k B hk hchar hZ
  have hinj := (Space.isHomeomorph_pointsMap_of_universalHomeomorphism _ hπ).injective
  exact ⟨hX, isSmooth_involutionQuotient k hchar B hk, hπ, hiso,
    isNoetherian_involutionQuotient k hchar B hk hZ, hInt,
    Space.topologicalKrullDim_points _ hπ,
    ⟨Space.primeDivisorEquivClosedPointsOfUniversalHomeomorphism _ hπ hX hInt.isDecentSpace,
      fun _ => rfl⟩,
    (Space.exists_primeDivisor_genericPoint_eq_iff_isClosed _ hπ hX hInt.isDecentSpace _).1
      ⟨_, rfl⟩,
    Space.pointsHomeomorphAffineLine_eq_origin_iff _ hπ hX hInt hN hiso _ hord,
    fun _ hZ' =>
      Space.weilDivisorClassGroup_primeDivisorClass_eq_zero _ hX hInt hN hπ hiso _ hord hZ',
    Space.divRationalFunction_coordinatePullbackUnit _ hX hInt hN hiso hinj _ hord,
    ⟨Space.weilDivisorClassGroupEquivZModTwo _ hX hInt hN hπ hiso _ hord,
      Space.weilDivisorClassGroupEquivZModTwo_primeDivisorClass _ hX hInt hN hπ hiso _ hord⟩⟩

end AlgebraicGeometry.AffineLineInvolution

end
