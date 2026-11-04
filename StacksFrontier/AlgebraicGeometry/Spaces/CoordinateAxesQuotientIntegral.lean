module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.CoordinateAxesQuotientUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# The coordinate-axes quotient is integral and Noetherian

Let `k` be a field, `U = Spec (k[x, y]/(xy))`, `R = Δ(U) ⨿ Δ'(U ∖ {0_U})` and `X = U/R`.
**Stacks 0ENU** deduces from the universal homeomorphism `X ⟶ 𝔸¹_k` that `X` is integral and
Noetherian. This file proves both.

## Main results

* `AlgebraicGeometry.CoordinateAxesQuotient.isReduced_nodalRing`: `k[x, y]/(xy)` is reduced.
* `AlgebraicGeometry.CoordinateAxesQuotient.puncturedCoordinateAxes_eq_basicOpen`: the punctured
  axes are the basic open `D(x + y)`, so the relation scheme is affine.
* `AlgebraicGeometry.CoordinateAxesQuotient.isAbsolutelyQuasiSeparated_quotientSpace`: `X` is
  quasi-separated.
* `AlgebraicGeometry.CoordinateAxesQuotient.isNoetherian_quotientSpace`: `X` is Noetherian.
* `AlgebraicGeometry.CoordinateAxesQuotient.irreducibleSpace_points_quotientSpace`: `|X|` is
  irreducible, being homeomorphic to `|𝔸¹_k|` through the universal homeomorphism.
* `AlgebraicGeometry.CoordinateAxesQuotient.isIntegralSpace_quotientSpace` and
  `AlgebraicGeometry.CoordinateAxesQuotient.isIntegralSpace_and_isNoetherian_quotientSpace`:
  **Stacks 0ENU**, `X` is integral and Noetherian.

## Implementation notes

Reducedness and local Noetherianity are read off the chart `U`. Quasi-separatedness is Stacks
07S4 for the chart `U ⟶ X`: its kernel pair is a base change of the first projection
`R ⟶ U`, which is a morphism of affine schemes once the punctured axes are recognized as
`D(x + y)`. Decency follows from Noetherianity. Quasi-separatedness of `X` is absolute
quasi-separatedness, which needs the terminal scheme in the site (`hZ`), and so does the
Noetherian property; irreducibility of `|X|` needs neither.

## References

* [Stacks Project, Tag 0ENU](https://stacks.math.columbia.edu/tag/0ENU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedChangeOfRings Stacks.Groupoids

universe u

namespace AlgebraicGeometry.CoordinateAxesQuotient

open AffineLineInvolution

attribute [local instance] Space.pointTopology

/-! ### The coordinate ring and the relation scheme -/

section Rings

variable (k : Type u) [Field k]

/-- The two variables of `k[x, y]` are relatively prime. -/
theorem isRelPrime_X_false_X_true :
    IsRelPrime (MvPolynomial.X false : MvPolynomial Bool k) (MvPolynomial.X true) := by
  intro d hd0 hd1
  obtain ⟨e, he⟩ := hd0
  rcases (MvPolynomial.X_prime (i := false) (R := k)).irreducible.isUnit_or_isUnit he with
    hu | hu
  · exact hu
  · exfalso
    have hassoc : Associated d (MvPolynomial.X false : MvPolynomial Bool k) :=
      ⟨hu.unit, by rw [he]; simp⟩
    have : (MvPolynomial.X false : MvPolynomial Bool k) ∣ MvPolynomial.X true :=
      hassoc.symm.dvd.trans hd1
    exact absurd (MvPolynomial.X_dvd_X.mp this) (by decide)

/-- `k[x, y]/(xy)` is reduced: `xy` is a product of two relatively prime primes. -/
theorem isReduced_nodalRing : _root_.IsReduced (NodalRing k) := by
  have hrad : IsRadical ((MvPolynomial.X false : MvPolynomial Bool k) * MvPolynomial.X true) := by
    intro n y hy
    refine (isRelPrime_X_false_X_true k).mul_dvd ?_ ?_
    · exact (MvPolynomial.X_prime (i := false) (R := k)).dvd_of_dvd_pow
        ((dvd_mul_right _ _).trans hy)
    · exact (MvPolynomial.X_prime (i := true) (R := k)).dvd_of_dvd_pow
        ((dvd_mul_left _ _).trans hy)
  exact (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_iff_span_singleton.mp hrad)

end Rings

variable (S : Setup.{u})

/-- The coordinate ring `k[x, y]/(xy)` of the coordinate axes is reduced. -/
instance : _root_.IsReduced (NodalRing S.k) := isReduced_nodalRing S.k

/-- The punctured coordinate axes `D(x) ∪ D(y)` are the basic open `D(x + y)`: on `D(x)` the
function `y` vanishes, so `x + y = x` there, and symmetrically. -/
theorem puncturedCoordinateAxes_eq_basicOpen :
    puncturedCoordinateAxes S = (coordinateAxes S).basicOpen (xSection S + ySection S) := by
  have key : ∀ f, f * (xSection S + ySection S) = f ^ 2 →
      (coordinateAxes S).basicOpen f ≤ (coordinateAxes S).basicOpen (xSection S + ySection S) := by
    intro f hf
    have h' := (coordinateAxes S).basicOpen_mul f (xSection S + ySection S)
    rw [hf, Scheme.basicOpen_pow _ _ two_pos] at h'
    rw [h']
    exact inf_le_right
  refine le_antisymm (sup_le (key _ ?_) (key _ ?_)) ((coordinateAxes S).basicOpen_add_le _ _)
  · rw [mul_add, xSection_mul_ySection, add_zero, pow_two]
  · rw [mul_add, mul_comm, xSection_mul_ySection, zero_add, pow_two]

/-- The punctured coordinate axes are an affine open. -/
theorem isAffineOpen_puncturedCoordinateAxes : IsAffineOpen (puncturedCoordinateAxes S) := by
  rw [puncturedCoordinateAxes_eq_basicOpen]
  exact (isAffineOpen_top _).basicOpen _

/-- The punctured coordinate axes form an affine scheme. -/
instance : IsAffine (puncturedCoordinateAxes S).toScheme :=
  isAffineOpen_puncturedCoordinateAxes S

/-- The first projection `R ⟶ U` of the relation is quasi-compact: it is a morphism of affine
schemes. -/
theorem quasiCompact_relationTarget : QuasiCompact (relationPreRelation S).target.left := by
  rw [relationPreRelation_target, relationLeftOver_left]
  have : IsAffine (relationScheme S) := inferInstance
  have : IsAffineHom (relationLeft S) := inferInstance
  infer_instance

/-! ### The quotient -/

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of S.k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u)]

/-- The chart `U ⟶ X`. -/
noncomputable abbrev chart :
    yoneda.obj (axesChart S B hS) ⟶ (quotientSpace S B hS).obj :=
  quotientChart (BigFppfOver.topology B (Spec (.of S.k)) hS) (Over.post B.inclusion)
    (axesChart S B hS) (relationPreRelation S)

/-- The pre-relation `R ⇉ U` of the coordinate axes is an étale equivalence relation. -/
private instance isEtaleEquivalenceRelation_axesChart :
    IsEtaleEquivalenceRelation (R := relationOver S)
      (U := (Over.post B.inclusion).obj (axesChart S B hS)) (relationPreRelation S) :=
  isEtaleEquivalenceRelation S

/-- The diagonal of `X` is representable, with no descent hypothesis. -/
theorem relativelyRepresentable_diag_quotientSpace :
    yoneda.relativelyRepresentable (diag (quotientSpace S B hS).obj) :=
  Space.relativelyRepresentable_diag_quotientSheaf B (Spec (.of S.k)) hS
    (axesChart S B hS) (relationPreRelation S)
    (Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B (Spec (.of S.k)) hS)

/-- The chart `U ⟶ X` is surjective. -/
theorem presheafSurjective_chart :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of S.k)) hS)).presheaf (chart S B hS) :=
  Space.presheaf_surjective_quotientChart_of_relativelyRepresentable_diag B (Spec (.of S.k)) hS
    (axesChart S B hS) (relationPreRelation S) (relativelyRepresentable_diag_quotientSpace S B hS)

/-- The chart `U ⟶ X` is étale. -/
theorem presheafEtale_chart :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of S.k)) hS)).presheaf (chart S B hS) :=
  Space.presheaf_etale_quotientChart_of_relativelyRepresentable_diag B (Spec (.of S.k)) hS
    (axesChart S B hS) (relationPreRelation S) (relativelyRepresentable_diag_quotientSpace S B hS)

/-- The coordinate axes are a Noetherian scheme. -/
instance isLocallyNoetherian_axesChart :
    IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).obj (axesChart S B hS)) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of (NodalRing S.k))))

/-- The coordinate axes are a reduced scheme. -/
instance isReduced_axesChart :
    IsReduced ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).obj (axesChart S B hS)) :=
  haveI : _root_.IsReduced (CommRingCat.of (NodalRing S.k)) := isReduced_nodalRing S.k
  inferInstanceAs (IsReduced (Spec (.of (NodalRing S.k))))

/-- A property of schemes holding for the chart `U` holds étale locally on `X`. -/
private theorem hasEtaleLocalProperty_quotientSpace_of_axesChart
    (P : Scheme.{u} → Prop)
    (h : P ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).obj (axesChart S B hS))) :
    Space.HasEtaleLocalProperty B (Spec (.of S.k)) hS (quotientSpace S B hS).obj P :=
  ⟨axesChart S B hS, chart S B hS, presheafSurjective_chart S B hS, presheafEtale_chart S B hS, h⟩

/-- `X` is reduced: its chart `U` is. -/
theorem hasEtaleLocalProperty_isReduced :
    Space.HasEtaleLocalProperty B (Spec (.of S.k)) hS (quotientSpace S B hS).obj
      (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_quotientSpace_of_axesChart S B hS _ inferInstance

/-- `X` is locally Noetherian: its chart `U` is. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian :
    Space.HasEtaleLocalProperty B (Spec (.of S.k)) hS (quotientSpace S B hS).obj
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y) :=
  hasEtaleLocalProperty_quotientSpace_of_axesChart S B hS _ inferInstance

omit [HasSheafify (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u)] in
/-- The coordinate axes, as an object of the big fppf site, are quasi-separated over `Spec ℤ`:
they form an affine scheme. -/
theorem quasiSeparated_axesChart :
    QuasiSeparated (B.inclusion.map (axesChart S B hS).hom ≫ terminal.from (Spec (.of S.k))) := by
  have h := (quasiSeparatedSpace_iff_quasiSeparated
    ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).obj (axesChart S B hS))).mp inferInstance
  rwa [terminal.hom_ext
    (terminal.from ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).obj (axesChart S B hS)))
    (B.inclusion.map (axesChart S B hS).hom ≫ terminal.from (Spec (.of S.k)))] at h

/-- `X` is quasi-separated: the chart `U ⟶ X` is a surjective étale atlas by an affine scheme
and its kernel pair is a base change of the quasi-compact first projection `R ⟶ U`, so
Stacks 07S4 applies. -/
theorem isAbsolutelyQuasiSeparated_quotientSpace (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsAbsolutelyQuasiSeparated B (Spec (.of S.k)) hS hZ (quotientSpace S B hS).obj := by
  obtain ⟨d, p₁, p₂, hpb, ⟨w, hw⟩, -⟩ :=
    Space.exists_isPullback_quotientChart B (Spec (.of S.k)) hS (axesChart S B hS)
      (relationPreRelation S) (axesChart S B hS) (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hpb
  exact Space.isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection
    B (Spec (.of S.k)) hS hZ (isAlgebraicSpace_quotientSpace S B hS)
    (presheafSurjective_chart S B hS) (presheafEtale_chart S B hS)
    (quasiSeparated_axesChart S B hS) hpb
    (MorphismProperty.of_isPullback (P := @QuasiCompact.{u}) hw (quasiCompact_relationTarget S))

/-- `X` is Noetherian: it is quasi-compact, quasi-separated and locally Noetherian. -/
theorem isNoetherian_quotientSpace (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsNoetherian B (Spec (.of S.k)) hS hZ (quotientSpace S B hS).obj :=
  ⟨⟨axesChart S B hS, chart S B hS, inferInstanceAs (CompactSpace (Spec _)),
      presheafSurjective_chart S B hS,
      (Space.isEtale_iff_presheaf_of_yoneda B (Spec (.of S.k)) hS _).2
        (presheafEtale_chart S B hS)⟩,
    isAbsolutelyQuasiSeparated_quotientSpace S B hS hZ,
    hasEtaleLocalProperty_isLocallyNoetherian S B hS⟩

/-- `|X|` is irreducible: the universal homeomorphism `X ⟶ 𝔸¹_k` identifies it with `|𝔸¹_k|`,
which is irreducible. -/
theorem irreducibleSpace_points_quotientSpace :
    IrreducibleSpace (Space.points B (Spec (.of S.k)) hS (quotientSpace S B hS).obj) := by
  let F := Over.post (X := B.obj hS) B.inclusion
  let A := Stacks.Groupoids.points F (affineLine S.k)
  have hA := Space.isAlgebraicSpace_points_affineLine B S.k hS
  have h := universalHomeomorphism_sumMap B S hS A hA (𝟙 A)
  let e₁ := h.homeomorph
  let e₂ := Space.pointsHomeomorphOfIso B (Spec (.of S.k)) hS
    (asIso (pullback.snd (𝟙 A) (sumMap S B hS)))
  let e₃ := (Space.pointsHomeomorphOfIso B (Spec (.of S.k)) hS
    (Space.pointsYonedaIso F (affineLineChart S.k B hS))).trans
      (Space.schemePointsHomeomorph B (Spec (.of S.k)) hS (affineLineChart S.k B hS))
  let e := e₃.symm.trans (e₁.symm.trans e₂)
  have : IrreducibleSpace
      ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).obj (affineLineChart S.k B hS)) :=
    inferInstanceAs (IrreducibleSpace (AffineSpace PUnit.{u + 1} (Spec (.of S.k))))
  rw [irreducibleSpace_def]
  have hi := (irreducibleSpace_def _).mp this
  have himg := hi.image e e.continuous.continuousOn
  rw [Set.top_eq_univ, Set.image_univ_of_surjective e.surjective] at himg
  rwa [Set.top_eq_univ]

/-- `X` is integral: reduced, decent and with irreducible space of points. -/
theorem isIntegralSpace_quotientSpace (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsIntegralSpace B (Spec (.of S.k)) hS (quotientSpace S B hS).obj :=
  ⟨hasEtaleLocalProperty_isReduced S B hS,
    Space.isDecentSpace_of_isNoetherian B (Spec (.of S.k)) hS hZ
      (isAlgebraicSpace_quotientSpace S B hS) (isNoetherian_quotientSpace S B hS hZ),
    irreducibleSpace_points_quotientSpace S B hS⟩

/-- **Stacks 0ENU.** The quotient `X = U/R` of the coordinate axes is integral and
Noetherian. -/
theorem isIntegralSpace_and_isNoetherian_quotientSpace (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsIntegralSpace B (Spec (.of S.k)) hS (quotientSpace S B hS).obj ∧
      Space.IsNoetherian B (Spec (.of S.k)) hS hZ (quotientSpace S B hS).obj :=
  ⟨isIntegralSpace_quotientSpace S B hS hZ, isNoetherian_quotientSpace S B hS hZ⟩

end AlgebraicGeometry.CoordinateAxesQuotient

end
