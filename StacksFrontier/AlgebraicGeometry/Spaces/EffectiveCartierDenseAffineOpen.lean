module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.ReducedAffineComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# The complement of a dense affine open in a regular Noetherian separated algebraic space

Let `X` be a regular Noetherian separated algebraic space over a scheme `S` and let `U ⊆ X` be a
dense affine open subspace.  Then the reduced induced closed subspace `D` of `X` on the closed
set `|X| ∖ |U|` is an effective Cartier divisor, so that `U = X ∖ D`.  This is Stacks 0DML.

## Main results

* `AlgebraicGeometry.Space.exists_hasEffectiveCartierEtaleCover_reducedClosedSubspace_compl`:
  the reduced induced closed subspace on the complement of a dense affine open subspace has
  point set that complement and is an effective Cartier divisor read on étale scheme charts,
  that is, it satisfies condition (2) of Stacks 083C.
* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_compl_denseAffineOpen`:
  **Stacks 0DML**, with its two scheme-level and chart-level inputs taken as hypotheses.
* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_compl_denseAffineOpen'`:
  **Stacks 0DML** with both of those inputs discharged.
* `AlgebraicGeometry.Space.exists_denseAffineOpen_isEffectiveCartierDivisor_compl`: on a
  regular Noetherian separated algebraic space there *is* a dense affine open subspace, and
  its complement is an effective Cartier divisor.

## The argument

The argument is the one of the source.  The divisor is the reduced induced closed subspace of
Stacks 03IQ and 047X on the closed set `|X| ∖ |U|`, and the point is that forming it commutes
with étale localization: on an étale scheme chart `V` of `X` it is cut out by the vanishing
ideal of the part of `V` lying over `|X| ∖ |U|`
(`AlgebraicGeometry.Space.atlasVanishingIdeal`), which is exactly what the proof of Stacks 03IQ
constructs.  Being Noetherian, `X` has a *single affine* surjective étale chart `V` by
Stacks 03H6; being regular and locally Noetherian étale-locally, `V` is a regular Noetherian
scheme by Stacks 03E8; and the base change `U ×_X V` is affine, because `X` is separated and
both `U` and `V` are affine — this is the affine-intersection criterion of Stacks 0AHS.  Since
an étale chart is open on points, the open `U ×_X V ⊆ V` is moreover dense.  So the hypotheses
of Stacks 0BCW are met on `V`, the stalks of a regular scheme being factorial, and the
vanishing ideal of the complement of `U ×_X V` in `V` is an effective Cartier divisor.  Reading
that back through Stacks 083C gives the conclusion.

## The two inputs, and where they come from

`AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_compl_denseAffineOpen` takes two
inputs as explicit hypotheses, and
`AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_compl_denseAffineOpen'` supplies both.

* `hBCW` is **Stacks 0BCW** in the form its own proof gives: on a Noetherian separated scheme
  with factorial local rings along the complement of a dense affine open, the *reduced induced*
  closed subscheme on that complement — the vanishing ideal of the complement — is an effective
  Cartier divisor.  What
  `StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/AffineComplement.lean` lands for
  that tag, `AlgebraicGeometry.exists_effectiveCartierDivisor_compl_affineOpen`, is the
  existential form of the statement: *some* ideal sheaf with that support is an effective
  Cartier divisor.  The existential form is not enough here, because only the reduced induced
  structure is invariant under the relation of an étale chart and hence descends to the space;
  the source itself cites "Lemma 0BCW and its proof" at this point.  The reduced induced form
  is `AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_compl_denseAffineOpen`: the
  vanishing ideal of the complement is the radical of the existential divisor, and the radical
  of an effective Cartier divisor is again one over factorial local rings.

* `h083C` is the implication (2) ⟹ (1) of **Stacks 083C**: a closed subspace whose inverse
  image on a surjective étale scheme chart is an effective Cartier divisor is an effective
  Cartier divisor in the sense of Stacks 083B.  This is
  `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover`.
  The chart-level conclusion, condition (2) of Stacks 083C, is proved outright in
  `AlgebraicGeometry.Space.exists_hasEffectiveCartierEtaleCover_reducedClosedSubspace_compl`,
  which needs only the first input.

## Implementation notes

"Separated" is the absolute notion `AlgebraicGeometry.Space.IsAbsolutelySeparated` of
Stacks 03BS, part (1), which is what the affine-intersection criterion of Stacks 0AHS speaks
about and what the source means by a separated algebraic space; it is why the containment `hZ`
of the terminal scheme in the site is required, as it is already for
`AlgebraicGeometry.Space.IsNoetherian` of Stacks 03EA.  Regularity is the étale-local scheme
property `AlgebraicGeometry.IsRegular` of Stacks 02IS through
`AlgebraicGeometry.Space.HasEtaleLocalProperty`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ResolutionOfSingularities.lean`.

The dense affine open subspace is given as a morphism `u : h_W ⟶ X` which is an open immersion,
with `W` an object of the site whose underlying scheme is affine, and whose set of points is
dense.  Its image subfunctor is then an open subspace in the sense of Stacks 02YU, part (2),
which is affine in the sense of `AlgebraicGeometry.Space.IsAffineSpace`; presenting it by `u`
rather than by a subfunctor together with an isomorphism to a representable presheaf is what
lets the affine-intersection criterion and the base-change-to-a-chart machinery be applied
directly to it.

`AlgebraicGeometry.Space.range_toScheme_map_eq_atlasPointSet` is
`AlgebraicGeometry.Space.range_map_eq_atlasPointSet` for an arbitrary morphism from a
representable presheaf in place of the inclusion of a subfunctor; the proof is the same.

## References

* [Stacks Project, Tag 0DML](https://stacks.math.columbia.edu/tag/0DML)
* [Stacks Project, Tag 0BCW](https://stacks.math.columbia.edu/tag/0BCW)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 0AHS](https://stacks.math.columbia.edu/tag/0AHS)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### The part of a chart lying over the image of a morphism -/

/-- **The part of a chart lying over the point set of a morphism from a representable presheaf
is the range of the base change of that morphism to the chart.**  This is
`AlgebraicGeometry.Space.range_map_eq_atlasPointSet` with the inclusion of a subfunctor
replaced by an arbitrary morphism `a : h_W ⟶ X`. -/
theorem range_toScheme_map_eq_atlasPointSet
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uc W V : BigFppfOver B S hS}
    {φ : yoneda.obj Uc ⟶ X} {a : yoneda.obj W ⟶ X} {i : V ⟶ Uc}
    {k : yoneda.obj V ⟶ yoneda.obj W} (hk : IsPullback k (yoneda.map i) a φ) :
    Set.range ((BigFppfOver.toScheme B S hS).map i).base =
      atlasPointSet B S hS φ (Set.range (pointsMap B S hS (yoneda.obj W) a)) := by
  ext x
  rw [mem_atlasPointSet_iff]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨pointsMap B S hS (yoneda.obj V) k ((pointsEquivScheme B S hS V).symm v), ?_⟩
    rw [pointsEquivScheme_symm_map, ← Function.comp_apply
        (f := pointsMap B S hS (yoneda.obj Uc) φ), ← pointsMap_comp, ← hk.w, pointsMap_comp]
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS hk z
      ((pointsEquivScheme B S hS Uc).symm x) hz
    refine ⟨(pointsEquivScheme B S hS V) w, ?_⟩
    refine (pointsEquivScheme B S hS Uc).symm.injective ?_
    rw [pointsEquivScheme_symm_map, Equiv.symm_apply_apply]
    exact hw

/-- The part of a chart lying over the complement of a set of points is the complement of the
part lying over that set. -/
theorem atlasPointSet_compl {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uc : BigFppfOver B S hS}
    (φ : yoneda.obj Uc ⟶ X) (T : Set (points B S hS X)) :
    atlasPointSet B S hS φ Tᶜ = (atlasPointSet B S hS φ T)ᶜ :=
  rfl

/-! ### The divisor on an étale scheme chart -/

/-- The range of a morphism of schemes is unchanged by precomposition with an isomorphism. -/
private theorem range_base_iso_comp {A A' Y : Scheme.{u}} (ε : A ≅ A') (h : A' ⟶ Y) :
    Set.range (ε.hom ≫ h).base = Set.range h.base := by
  simp [Set.range_comp]

/-- **A reduced closed subscheme of a chart whose range is the part of the chart lying over a
closed set of points is cut out by the vanishing ideal of that part.**  A reduced closed
subscheme is determined by its support, which is
`AlgebraicGeometry.Space.eq_atlasReducedSubscheme`; two monomorphisms defining the same
subobject then factor through each other, so they have the same kernel, and the kernel of the
inclusion of the subscheme cut out by an ideal sheaf is that ideal sheaf. -/
private theorem ker_eq_atlasVanishingIdeal_of_isReduced
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uc : BigFppfOver B S hS}
    (φ : yoneda.obj Uc ⟶ X) (T : Set (points B S hS X)) (hT : _root_.IsClosed T)
    {Y : Scheme.{u}} (f₀ : Y ⟶ (BigFppfOver.toScheme B S hS).obj Uc)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion f₀) (hred : IsReduced Y)
    (hrange : Set.range f₀.base = atlasPointSet B S hS φ T) :
    f₀.ker = atlasVanishingIdeal B S hS φ T hT := by
  have _ := hci
  have _ := hred
  have hmono : Mono f₀ := inferInstance
  have hciZ : _root_.AlgebraicGeometry.IsClosedImmersion (Subobject.mk f₀).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk f₀]
    infer_instance
  have hredZ : IsReduced (Subobject.underlying.obj (Subobject.mk f₀)) :=
    ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z)
      (Subobject.underlyingIso f₀).symm hred
  have hrangeZ : Set.range (Subobject.mk f₀).arrow.base = atlasPointSet B S hS φ T := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk f₀, range_base_iso_comp]
    exact hrange
  have hmk : Subobject.mk f₀ =
      Subobject.mk (atlasVanishingIdeal B S hS φ T hT).subschemeι :=
    eq_atlasReducedSubscheme B S hS (Subobject.mk f₀) hciZ hredZ T hT hrangeZ
  have h1 := Subobject.ofMkLEMk_comp (f := f₀)
    (g := (atlasVanishingIdeal B S hS φ T hT).subschemeι) hmk.le
  have h2 := Subobject.ofMkLEMk_comp (f := (atlasVanishingIdeal B S hS φ T hT).subschemeι)
    (g := f₀) hmk.ge
  rw [← Scheme.IdealSheafData.ker_subschemeι (atlasVanishingIdeal B S hS φ T hT)]
  refine le_antisymm ?_ ?_
  · conv_rhs => rw [← h2]
    exact Scheme.Hom.le_ker_comp _ _
  · conv_rhs => rw [← h1]
    exact Scheme.Hom.le_ker_comp _ _

/-- **The reduced closed subspace on a closed set of points is cut out on an étale scheme chart
by the vanishing ideal of the part of the chart lying over that set.**  The base change of the
subspace to the chart is a closed subscheme, it is reduced because the chart of the subspace it
induces is étale over the étale-locally reduced subspace, and its support is the part of the
chart lying over the closed set; a reduced closed subscheme with that support is the reduced
induced one. -/
theorem ker_rep_snd_reducedClosedSubspace_eq_atlasVanishingIdeal
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (hT : _root_.IsClosed T)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ X.1)
    (hgE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hDc : IsClosedSubspace B S hS (reducedClosedSubspace B S hS X.1 X.2 T hT)) :
    ((BigFppfOver.toScheme B S hS).map (hDc.2.rep.snd g)).ker =
      atlasVanishingIdeal B S hS g T hT := by
  have hstabe := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hfstE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (hDc.2.rep.fst g) :=
    MorphismProperty.of_isPullback (hDc.2.rep.isPullback g).flip hgE
  refine ker_eq_atlasVanishingIdeal_of_isReduced B S hS g T hT _ (hDc.2.property_snd g)
    (isReduced_of_hasEtaleLocalProperty_isReduced B S hS
      (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X.1 X.2 T hT) hfstE) ?_
  rw [range_map_eq_atlasPointSet B S hS (reducedClosedSubspace B S hS X.1 X.2 T hT)
      (hDc.2.rep.isPullback g),
    range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 T hT]

/-! ### Stacks 0DML -/

/-- **The reduced induced closed subspace on the complement of a dense affine open subspace of
a regular Noetherian separated algebraic space is an effective Cartier divisor on every — and
hence on one surjective — étale scheme chart.**  This is Stacks 0DML with its conclusion read
in the form of condition (2) of Stacks 083C.

The hypothesis `hBCW` is Stacks 0BCW in the form its own proof gives: the vanishing ideal of
the complement of a dense affine open of a Noetherian separated scheme with factorial local
rings along that complement is an effective Cartier divisor. -/
theorem exists_hasEffectiveCartierEtaleCover_reducedClosedSubspace_compl
    (X : AlgebraicSpaces B S hS)
    (hsep : IsAbsolutelySeparated B S hS hZ X.1)
    (hnoeth : IsNoetherian B S hS hZ X.1)
    (hreg : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsRegular T))
    (W : BigFppfOver B S hS) (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (u : yoneda.obj W ⟶ X.1) (hu : IsOpenImmersion B S hS u)
    (hudense : Dense (Set.range (pointsMap B S hS (yoneda.obj W) u)))
    (hBCW : ∀ Y : Scheme.{u}, _root_.AlgebraicGeometry.IsNoetherian Y → Scheme.IsSeparated Y →
      ∀ O : Y.Opens, IsAffineOpen O → Dense (O : Set Y) →
        (∀ y : Y, y ∉ O → UniqueFactorizationMonoid (Y.presheaf.stalk y)) →
          Stacks.Divisors.IsEffectiveCartierDivisor
            (Scheme.IdealSheafData.vanishingIdeal ⟨(O : Set Y)ᶜ, O.2.isClosed_compl⟩)) :
    ∃ D : ClosedSubspaces B S hS X.1,
      Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) =
          (Set.range (pointsMap B S hS (yoneda.obj W) u))ᶜ ∧
        HasEtaleLocalProperty B S hS D.1.toFunctor (fun Y : Scheme.{u} => IsReduced Y) ∧
          HasEffectiveCartierEtaleCover B S hS X D := by
  classical
  have hRopen : _root_.IsOpen (Set.range (pointsMap B S hS (yoneda.obj W) u)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS u hu
  set R := Set.range (pointsMap B S hS (yoneda.obj W) u) with hRdef
  have hT : _root_.IsClosed Rᶜ := hRopen.isClosed_compl
  refine ⟨⟨reducedClosedSubspace B S hS X.1 X.2 Rᶜ hT,
      isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 Rᶜ hT⟩,
    range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 Rᶜ hT,
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X.1 X.2 Rᶜ hT, ?_⟩
  -- an affine surjective étale chart, which exists because `X` is quasi-compact
  obtain ⟨V, g, hVaff, hgsurj, hgEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).mp hnoeth.1
  have hgE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g := presheaf_etale_of_isEtale B S hS hgEtale
  refine ⟨V, g, hgEtale, isSurjective_of_presheafSurjective B S hS g hgsurj, ?_⟩
  rw [isSchemeEffectiveCartierPullback_iff,
    ker_rep_snd_reducedClosedSubspace_eq_atlasVanishingIdeal B S hS X Rᶜ hT V g hgE
      (isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 Rᶜ hT)]
  -- the chart is a regular Noetherian affine, hence separated, scheme
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  have _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS X.1
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y) X.2).mp hnoeth.2.2 V g hgE
  have hVreg : _root_.AlgebraicGeometry.IsRegular ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS X.1
      (fun Y : Scheme.{u} => _root_.AlgebraicGeometry.IsRegular Y) X.2).mp hreg V g hgE
  have hVnoeth : _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B S hS).obj V) := by constructor
  have hVsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj V) := inferInstance
  -- the base change of the dense affine open to the chart is a dense affine open
  have hint := (isAbsolutelySeparated_iff_hasAffineIntersections B S hS hZ X.1 X.2).mp hsep
  have hsq : IsPullback (yoneda.map (yoneda.preimage (hu.rep.fst g)))
      (yoneda.map (hu.rep.snd g)) u g := by
    rw [yoneda.map_preimage]
    exact hu.rep.isPullback g
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (hu.rep.pullback g)) :=
    (hint W V (hu.rep.pullback g) u g (yoneda.preimage (hu.rep.fst g)) (hu.rep.snd g)
      hWaff hVaff hsq).1
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hu.rep.snd g)) := hu.property_snd g
  obtain ⟨O, hOaff, hOpt⟩ : ∃ O : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      IsAffineOpen O ∧
        (O : Set ((BigFppfOver.toScheme B S hS).obj V)) = atlasPointSet B S hS g R :=
    ⟨Scheme.Hom.opensRange ((BigFppfOver.toScheme B S hS).map (hu.rep.snd g)),
      isAffineOpen_opensRange _, range_toScheme_map_eq_atlasPointSet B S hS hsq⟩
  have hOdense : Dense (O : Set ((BigFppfOver.toScheme B S hS).obj V)) := by
    rw [hOpt]
    exact (hudense.preimage (isOpenMap_pointsMap_of_etale B S hS X.2 V g hgE)).preimage
      (schemePointsHomeomorph B S hS V).symm.isOpenMap
  -- the local rings of a regular scheme are factorial
  have hVstalk : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj V,
        IsRegularLocalRing (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk y) :=
    ((isRegular_tfae ((BigFppfOver.toScheme B S hS).obj V)).out 1 2
      (by simp) (by simp)).mp hVreg
  have hUFD : ∀ y : (BigFppfOver.toScheme B S hS).obj V, y ∉ O →
      UniqueFactorizationMonoid
        (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk y) := by
    intro y _
    have _ : IsRegularLocalRing
        (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk y) := hVstalk.2 y
    exact IsRegularLocalRing.uniqueFactorizationMonoid _
  -- Stacks 0BCW on the chart
  have hOcompl : (O : Set ((BigFppfOver.toScheme B S hS).obj V))ᶜ =
      atlasPointSet B S hS g Rᶜ := by
    rw [atlasPointSet_compl, hOpt]
  have hVanish : Scheme.IdealSheafData.vanishingIdeal
        (⟨(O : Set ((BigFppfOver.toScheme B S hS).obj V))ᶜ, O.2.isClosed_compl⟩ :
          Closeds ((BigFppfOver.toScheme B S hS).obj V)) =
      atlasVanishingIdeal B S hS g Rᶜ hT :=
    congrArg Scheme.IdealSheafData.vanishingIdeal (Closeds.ext hOcompl)
  rw [← hVanish]
  exact hBCW ((BigFppfOver.toScheme B S hS).obj V) hVnoeth hVsep O hOaff hOdense hUFD

/-- **Stacks Project, Tag 0DML.** Let `S` be a scheme and let `X` be a regular Noetherian
separated algebraic space over `S`.  Let `U ⊆ X` be a dense affine open subspace, presented by
an open immersion `u : h_W ⟶ X` whose source has affine underlying scheme and whose set of
points is dense.  Then there is an effective Cartier divisor `D ⊆ X` with `U = X ∖ D`: namely
the reduced induced closed subspace on the closed set `|X| ∖ |U|`.

The hypothesis `hBCW` is Stacks 0BCW in the form its own proof gives, for the reduced induced
closed subscheme on the complement of a dense affine open of a scheme, and `h083C` is the
implication (2) ⟹ (1) of Stacks 083C; both are inputs this library does not have, and the
conclusion of the chart-level statement
`AlgebraicGeometry.Space.exists_hasEffectiveCartierEtaleCover_reducedClosedSubspace_compl`
needs only the first of them. -/
@[stacks 0DML]
theorem exists_isEffectiveCartierDivisor_compl_denseAffineOpen
    (X : AlgebraicSpaces B S hS)
    (hsep : IsAbsolutelySeparated B S hS hZ X.1)
    (hnoeth : IsNoetherian B S hS hZ X.1)
    (hreg : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsRegular T))
    (W : BigFppfOver B S hS) (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (u : yoneda.obj W ⟶ X.1) (hu : IsOpenImmersion B S hS u)
    (hudense : Dense (Set.range (pointsMap B S hS (yoneda.obj W) u)))
    (hBCW : ∀ Y : Scheme.{u}, _root_.AlgebraicGeometry.IsNoetherian Y → Scheme.IsSeparated Y →
      ∀ O : Y.Opens, IsAffineOpen O → Dense (O : Set Y) →
        (∀ y : Y, y ∉ O → UniqueFactorizationMonoid (Y.presheaf.stalk y)) →
          Stacks.Divisors.IsEffectiveCartierDivisor
            (Scheme.IdealSheafData.vanishingIdeal ⟨(O : Set Y)ᶜ, O.2.isClosed_compl⟩))
    (h083C : ∀ D : ClosedSubspaces B S hS X.1,
      HasEffectiveCartierEtaleCover B S hS X D → IsEffectiveCartierDivisor B S hS X D) :
    ∃ D : ClosedSubspaces B S hS X.1,
      IsEffectiveCartierDivisor B S hS X D ∧
        Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) =
          (Set.range (pointsMap B S hS (yoneda.obj W) u))ᶜ := by
  obtain ⟨D, hDpt, -, hDcover⟩ :=
    exists_hasEffectiveCartierEtaleCover_reducedClosedSubspace_compl B S hS hZ X hsep hnoeth
      hreg W hWaff u hu hudense hBCW
  exact ⟨D, h083C D hDcover, hDpt⟩

/-- **Stacks Project, Tag 0DML.** Let `S` be a scheme and let `X` be a regular Noetherian
separated algebraic space over `S`.  Let `U ⊆ X` be a dense affine open subspace, presented by
an open immersion `u : h_W ⟶ X` whose source has affine underlying scheme and whose set of
points is dense.  Then there is an effective Cartier divisor `D ⊆ X` with `U = X ∖ D`.

This is `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_compl_denseAffineOpen` with
both of its inputs supplied: the reduced induced form of Stacks 0BCW on a scheme by
`AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_compl_denseAffineOpen`, and the
implication (2) ⟹ (1) of Stacks 083C by
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover`. -/
@[stacks 0DML]
theorem exists_isEffectiveCartierDivisor_compl_denseAffineOpen'
    (X : AlgebraicSpaces B S hS)
    (hsep : IsAbsolutelySeparated B S hS hZ X.1)
    (hnoeth : IsNoetherian B S hS hZ X.1)
    (hreg : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsRegular T))
    (W : BigFppfOver B S hS) (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (u : yoneda.obj W ⟶ X.1) (hu : IsOpenImmersion B S hS u)
    (hudense : Dense (Set.range (pointsMap B S hS (yoneda.obj W) u))) :
    ∃ D : ClosedSubspaces B S hS X.1,
      IsEffectiveCartierDivisor B S hS X D ∧
        Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) =
          (Set.range (pointsMap B S hS (yoneda.obj W) u))ᶜ := by
  refine exists_isEffectiveCartierDivisor_compl_denseAffineOpen B S hS hZ X hsep hnoeth hreg
    W hWaff u hu hudense (fun Y hN hSep O hO hd hufd => ?_)
    (fun D hD => isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS X D hD)
  have := hN
  have := hSep
  exact AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_compl_denseAffineOpen
    Y O hO hd hufd

/-- **On a regular Noetherian separated algebraic space some dense affine open subspace has an
effective Cartier divisor as its complement.**  A Noetherian algebraic space has a dense affine
open subspace, and Stacks 0DML makes the complement of such a subspace an effective Cartier
divisor.  This is the opening move of Stacks 0DMM, where the dense affine open is additionally
chosen so as to trivialize a given invertible module. -/
theorem exists_denseAffineOpen_isEffectiveCartierDivisor_compl
    (X : AlgebraicSpaces B S hS)
    (hsep : IsAbsolutelySeparated B S hS hZ X.1)
    (hnoeth : IsNoetherian B S hS hZ X.1)
    (hreg : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsRegular T)) :
    ∃ (W : BigFppfOver B S hS) (u : yoneda.obj W ⟶ X.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      IsOpenImmersion B S hS u ∧
      Dense (Set.range (pointsMap B S hS (yoneda.obj W) u)) ∧
      ∃ D : ClosedSubspaces B S hS X.1,
        IsEffectiveCartierDivisor B S hS X D ∧
          Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) =
            (Set.range (pointsMap B S hS (yoneda.obj W) u))ᶜ := by
  obtain ⟨W, u, hWaff, hu, hudense⟩ :=
    exists_dense_affine_openImmersion_self B S hS hZ X.1 X.2 hnoeth
  exact ⟨W, u, hWaff, hu, hudense,
    exists_isEffectiveCartierDivisor_compl_denseAffineOpen' B S hS hZ X hsep hnoeth hreg
      W hWaff u hu hudense⟩

end AlgebraicGeometry.Space

end
