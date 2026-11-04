module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Algebraization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.FlatnessKernelPowers
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.FlatLocusOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UpperSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyContraction
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison

/-!
# Formal objects of the stack of curves are effective

Every formal object of the stack `Curves` of families of curves over `Spec(ℤ)` is effective
(Stacks 0D58): a Noetherian complete local ring `(R, 𝔪)` with families of curves
`X_n ⟶ Spec (R / 𝔪 ^ (n + 1))` and cartesian transitions comes from a family of curves over
`Spec R`.

The proof is the source's.

* The levels are schemes: the closed level is a family of curves over a field, a scheme by
  Stacks 0ADD (`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`), and the higher
  levels are thickenings of it, schemes by Stacks 05ZR
  (`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_hom`).
* Their tower algebraizes by Stacks 0E7R, in its scheme form
  (`Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`), to a
  projective `Y ⟶ Spec R` with `Y ×_{Spec R} Spec (R / 𝔪 ^ (n + 1)) ≅ X_n`.
* `Y ⟶ Spec R` is flat by Stacks 0D4G at the points over the closed point, and everywhere because
  the non-flat locus is closed (Stacks 0255) with closed image.
* `Y ⟶ Spec R` has fibres of dimension at most one: the locus where the fibre dimension is at most
  one is open by the semicontinuity of Stacks 0D4I (the half of Stacks 0D4J that is used) and
  contains the closed point, whose fibre lies in the closed level.
* So `Y ⟶ Spec R` is a family of curves, and the identifications with the levels realize the
  formal object (`Deformation.Artin.FormalObject.isEffective_of_realization`).

## Main results

* `AlgebraicGeometry.C1590Private.isEffective_curvesFormalObject`: Stacks 0D58, for the model
  `AlgebraicGeometry.curvesFiberedCategory` of the stack of curves.
* `AlgebraicGeometry.C1590Private.flat_of_flat_pullback_adicThickeningι`: flatness over a
  Noetherian local ring from flatness over its adic thickenings.
* `AlgebraicGeometry.C1590Private.fiberDimension_le_of_closedPoint`: over a local base, the
  fibre-dimension bound at the closed point bounds every fibre.
* `AlgebraicGeometry.C1590Private.CurvesFormal.curveFamilyOfFiberDimensionLE`: a flat proper
  morphism of finite presentation of the site with fibres of dimension at most one is a family of
  curves.

## Implementation notes

The relative-dimension condition of a family of curves is the every-étale-chart condition of
Stacks 04NC; for a morphism of the site it is read off the fibres of the underlying morphism of
schemes through the identity chart, so no bound on the dimension of the total space is needed.

The statement here is not the full statement of Stacks 0D58, so no `@[stacks]` attribute is
attached here.

## References

* [Stacks Project, Tag 0D58](https://stacks.math.columbia.edu/tag/0D58)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0D4G](https://stacks.math.columbia.edu/tag/0D4G)
* [Stacks Project, Tag 0D4I](https://stacks.math.columbia.edu/tag/0D4I)
* [Stacks Project, Tag 0D4J](https://stacks.math.columbia.edu/tag/0D4J)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation.Artin

namespace AlgebraicGeometry.C1590Private

universe u

/-! ### Morphism properties and `eqToHom` -/

section EqToHom

variable {C : Type*} [Category C] (P : MorphismProperty C)

/-- A morphism property holds for `f ≫ eqToHom h` exactly when it holds for `f`. -/
theorem morphismProperty_comp_eqToHom_iff {X Y Y' : C} (f : X ⟶ Y) (h : Y = Y') :
    P (f ≫ eqToHom h) ↔ P f := by
  subst h; simp

/-- A morphism property holds for `eqToHom h ≫ f` exactly when it holds for `f`. -/
theorem morphismProperty_eqToHom_comp_iff {X X' Y : C} (h : X' = X) (f : X ⟶ Y) :
    P (eqToHom h ≫ f) ↔ P f := by
  subst h; simp

end EqToHom

/-! ### Morphisms to the spectrum of a Noetherian local ring -/

section LocalBase

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Every point of the spectrum of a local ring specializes to the closed point. -/
private theorem specializes_closedPoint (x : PrimeSpectrum R) : x ⤳ closedPoint R :=
  (PrimeSpectrum.le_iff_specializes x (closedPoint R)).mp (le_maximalIdeal x.isPrime.ne_top)

/-- An open subset of the spectrum of a local ring containing the closed point is everything:
every point specializes to the closed point. -/
theorem eq_univ_of_isOpen_of_closedPoint_mem {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    (h : closedPoint R ∈ U) : U = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    (specializes_closedPoint x).mem_open hU h

/-- The closed point of the spectrum of a local ring lies in the image of the closed point of
the first adic thickening. -/
theorem closedPoint_mem_range_adicThickeningι_zero :
    closedPoint R ∈ Set.range (adicThickeningι R (maximalIdeal R) 0) := by
  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  have : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.mpr hne
  obtain ⟨s⟩ : Nonempty (PrimeSpectrum (R ⧸ maximalIdeal R ^ (0 + 1))) := inferInstance
  refine ⟨s, ?_⟩
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) s.asIdeal = maximalIdeal R
  refine le_antisymm (le_maximalIdeal (Ideal.comap_ne_top _ s.isPrime.ne_top)) fun x hx => ?_
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (by rwa [zero_add, pow_one])]
  exact s.asIdeal.zero_mem

variable [IsNoetherianRing R] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R))

/-- **Flatness over a Noetherian local ring from flatness over its adic thickenings.** A
universally closed morphism locally of finite type `g : Y ⟶ Spec R` whose base change to every
`Spec (R / 𝔪 ^ (n + 1))` is flat is flat. At the points over the closed point this is
Stacks 0D4G; the non-flat locus is closed (Stacks 0255), so its image is closed and, if nonempty,
contains the closed point. -/
theorem flat_of_flat_pullback_adicThickeningι [UniversallyClosed g] [LocallyOfFiniteType g]
    (hflat : ∀ n, Flat (pullback.snd g (adicThickeningι R (maximalIdeal R) n))) : Flat g := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hcl : ∀ y : Y, g y = closedPoint R → IsFlatAt g.toLRSHom.toShHom y := fun y hy =>
    flat_stalkMap_of_flat_pullbacks_spec_quotient_pow (maximalIdeal R) g hflat y
      (by rw [hy]; exact le_rfl)
  rw [Flat.iff_flat_stalkMap]
  by_contra hne
  simp only [not_forall] at hne
  obtain ⟨y, hy⟩ := hne
  have hC : IsClosed {y : Y | ¬ IsFlatAt g.toLRSHom.toShHom y} :=
    (isOpen_setOf_isFlatAt_of_isLocallyNoetherian g).isClosed_compl
  have himg : IsClosed (g.base '' {y : Y | ¬ IsFlatAt g.toLRSHom.toShHom y}) :=
    g.isClosedMap _ hC
  obtain ⟨y', hy'C, hy'⟩ := (specializes_closedPoint (g y)).mem_closed himg ⟨y, hy, rfl⟩
  exact hy'C (hcl y' hy')

/-- An element of `WithBot ℕ∞` below `d + 1` is at most `d`. -/
theorem le_natCast_of_lt_natCast_add_one (x : WithBot ℕ∞) (d : ℕ)
    (h : x < ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ (d : WithBot ℕ∞) := by
  cases x with
  | bot => exact bot_le
  | coe x =>
    cases x with
    | top => exact absurd h (not_lt_of_ge (by exact_mod_cast le_top))
    | coe m =>
      have h' : m < d + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.mp h'

omit [IsNoetherianRing R] in
/-- **The fibre dimension over a local ring is bounded by that of the closed fibre.**
For a universally closed morphism locally of finite type `g : Y ⟶ Spec R`, the locus where the
fibre has dimension at most `d` is open (Stacks 0D4I), so it is everything once it contains the
closed point. -/
theorem fiberDimension_le_of_closedPoint [UniversallyClosed g] [LocallyOfFiniteType g] (d : ℕ)
    (h : g.fiberDimension (closedPoint R) ≤ (d : WithBot ℕ∞)) (s : Spec (.of R)) :
    g.fiberDimension s ≤ (d : WithBot ℕ∞) := by
  have hopen := (upperSemicontinuous_iff_isOpen_preimage.mp
    (upperSemicontinuous_fiberDimension g)) ((d + 1 : ℕ) : WithBot ℕ∞)
  have hcp : closedPoint R ∈ g.fiberDimension ⁻¹' Set.Iio ((d + 1 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self d)
  have hs : s ∈ g.fiberDimension ⁻¹' Set.Iio ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [eq_univ_of_isOpen_of_closedPoint_mem hopen hcp]; trivial
  exact le_natCast_of_lt_natCast_add_one _ d hs

end LocalBase

namespace CurvesFormal

/-! ### The tower of schemes of a formal object of the stack of curves -/

section Tower

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (ξ : FormalObject B integerBase hZ (curvesProjectionOver B hZ))

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The base of the `n`-th level of a formal object of `Curves` is the `n`-th thickening of its
complete local base. -/
theorem level_base (n : ℕ) :
    (ξ.level n).base = truncationOver B integerBase hZ ξ.base ξ.contains n :=
  ξ.level_eq n

/-- The morphism of bases of a transition of a formal object of `Curves` is the inclusion of the
thickenings. -/
theorem transition_baseMap (n : ℕ) :
    (ξ.transition n).baseMap = eqToHom (level_base ξ n) ≫
      truncationOverSucc B integerBase hZ ξ.base ξ.contains n ≫
        eqToHom (level_base ξ (n + 1)).symm :=
  let := ξ.transition_lift n
  IsHomLift.fac' (curvesProjectionOver B hZ) _ (ξ.transition n)

/-- The `(0 + 1)`-st power of the maximal ideal of a local ring is maximal. -/
theorem isMaximal_maximalIdeal_pow_zero_add_one (R : Type u) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R ^ (0 + 1)).IsMaximal := by
  rw [zero_add, pow_one]; exact maximalIdeal.isMaximal R

/-- **The levels of a formal object of `Curves` are schemes.** The closed level is a family of
curves over a field, whose total space is a scheme by Stacks 0ADD; and a family of curves over a
thickening of the base of a family whose total space is a scheme has a scheme as its total space
(Stacks 05ZR). -/
theorem isRepresentable_level_total (n : ℕ) : (ξ.level n).total.obj.IsRepresentable := by
  induction n with
  | zero =>
    have := isMaximal_maximalIdeal_pow_zero_add_one ξ.base.R
    let : Field (ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1)) := Ideal.Quotient.field _
    exact (ξ.level 0).isRepresentable_total_of_base_eq
      (K := ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1)) (congrArg (𝒯).obj (level_base ξ 0))
  | succ n ih =>
    refine CurveFamily.isRepresentable_total_of_hom (ξ.transition n) ?_ ih
    have h : (𝒯).map (truncationOverSucc B integerBase hZ ξ.base ξ.contains n) =
        adicThickeningSucc ξ.base.R (maximalIdeal ξ.base.R) n := rfl
    rw [transition_baseMap, Functor.map_comp, Functor.map_comp, h, eqToHom_map, eqToHom_map]
    exact ⟨(morphismProperty_eqToHom_comp_iff @IsClosedImmersion _ _).mpr
      ((morphismProperty_comp_eqToHom_iff @IsClosedImmersion _ _).mpr
        (isClosedImmersion_adicThickeningSucc _ _ n)),
      ((morphismProperty_eqToHom_comp_iff @Surjective _ _).mpr
        ((morphismProperty_comp_eqToHom_iff @Surjective _ _).mpr
          (surjective_adicThickeningSucc _ _ n))).surj⟩

/-- The scheme under the base of the `n`-th level is the `n`-th thickening. -/
theorem levelBaseEq (n : ℕ) :
    (𝒯).obj (ξ.level n).base = adicThickening ξ.base.R (maximalIdeal ξ.base.R) n :=
  congrArg (𝒯).obj (level_base ξ n)

/-- The object of the site representing the total space of the `n`-th level. -/
def levelSite (n : ℕ) : BigFppfOver B integerBase hZ :=
  haveI := isRepresentable_level_total ξ n
  (ξ.level n).total.obj.reprX

/-- The identification of the presheaf represented by `levelSite ξ n` with the total space of
the `n`-th level. -/
def levelIso (n : ℕ) : yoneda.obj (levelSite ξ n) ≅ (ξ.level n).total.obj :=
  haveI := isRepresentable_level_total ξ n
  (ξ.level n).total.obj.reprW

/-- The identification of the algebraic space of `levelSite ξ n` with the total space of the
`n`-th level. -/
def levelTotalIso (n : ℕ) : schemeSpace (levelSite ξ n) ≅ (ξ.level n).total :=
  ObjectProperty.isoMk _ (levelIso ξ n)

/-- The morphism of presheaves underlying `levelTotalIso ξ n`. -/
@[simp]
theorem levelTotalIso_hom_hom (n : ℕ) : (levelTotalIso ξ n).hom.hom = (levelIso ξ n).hom := rfl

/-- The morphism of presheaves underlying the inverse of `levelTotalIso ξ n`. -/
@[simp]
theorem levelTotalIso_inv_hom (n : ℕ) : (levelTotalIso ξ n).inv.hom = (levelIso ξ n).inv := rfl

/-- The structure morphism of the `n`-th level, as a morphism of the site. -/
def levelHom (n : ℕ) : levelSite ξ n ⟶ (ξ.level n).base :=
  yoneda.preimage ((levelIso ξ n).hom ≫ (ξ.level n).toBase.hom)

/-- The represented morphism of `levelHom ξ n` is the structure morphism of the level. -/
theorem yoneda_map_levelHom (n : ℕ) :
    yoneda.map (levelHom ξ n) = (levelIso ξ n).hom ≫ (ξ.level n).toBase.hom :=
  yoneda.map_preimage _

/-- The total space of the `n`-th level is the base change of the level along the identity, with
`levelSite ξ n` as its scheme. -/
theorem isPullback_levelHom (n : ℕ) :
    IsPullback (levelTotalIso ξ n).hom (schemeSpaceMap (levelHom ξ n)) (ξ.level n).toBase
      (schemeSpaceMap (𝟙 (ξ.level n).base)) := by
  have : IsIso (schemeSpaceMap (𝟙 (ξ.level n).base)) :=
    inferInstanceAs (IsIso ((schemeSpaceFunctor B integerBase hZ).map (𝟙 _)))
  refine IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ ?_⟩
  show (levelIso ξ n).hom ≫ (ξ.level n).toBase.hom = yoneda.map (levelHom ξ n) ≫ yoneda.map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, yoneda_map_levelHom]
  exact (Category.comp_id _).symm

/-- The scheme of the `n`-th level is proper over the base of the level. -/
theorem isProper_levelHom (n : ℕ) : IsProper ((𝒯).map (levelHom ξ n)) :=
  (ξ.level n).isProper_toScheme_map_of_isPullback_schemeSpaceMap (isPullback_levelHom ξ n)

/-- The scheme of the `n`-th level is flat over the base of the level. -/
theorem flat_levelHom (n : ℕ) : Flat ((𝒯).map (levelHom ξ n)) :=
  (ξ.level n).flat_toScheme_map_of_isPullback (isPullback_levelHom ξ n)

/-- The fibres of the scheme of the `n`-th level over its base have dimension at most one: the
relative-dimension condition of the level, read in the identity chart (Stacks 04NC). -/
theorem topologicalKrullDim_fiber_levelHom_le (n : ℕ) (s : (𝒯).obj (ξ.level n).base) :
    topologicalKrullDim (((𝒯).map (levelHom ξ n)).fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
  (ξ.level n).topologicalKrullDim_fiber_toScheme_map_le_of_isPullback (isPullback_levelHom ξ n)
    (by rw [CategoryTheory.Functor.map_id]; infer_instance) s

/-- The scheme of the `n`-th level. -/
abbrev towerScheme (n : ℕ) : Scheme.{u} := (𝒯).obj (levelSite ξ n)

/-- The structure morphism of the `n`-th level to the `n`-th thickening. -/
def towerHom (n : ℕ) :
    towerScheme ξ n ⟶ adicThickening ξ.base.R (maximalIdeal ξ.base.R) n :=
  (𝒯).map (levelHom ξ n ≫ eqToHom (level_base ξ n))

/-- The transition of the levels, as a morphism of the site. -/
def towerTransitionSite (n : ℕ) : levelSite ξ n ⟶ levelSite ξ (n + 1) :=
  yoneda.preimage ((levelIso ξ n).hom ≫ (ξ.transition n).totalMap.hom ≫ (levelIso ξ (n + 1)).inv)

/-- The represented morphism of `towerTransitionSite ξ n` is the transition of total spaces. -/
theorem yoneda_map_towerTransitionSite (n : ℕ) :
    yoneda.map (towerTransitionSite ξ n) =
      (levelIso ξ n).hom ≫ (ξ.transition n).totalMap.hom ≫ (levelIso ξ (n + 1)).inv :=
  yoneda.map_preimage _

/-- The inverse of `levelTotalIso ξ n` followed by the represented structure morphism of the level
is the structure morphism of the level. -/
private theorem levelTotalIso_inv_comp_schemeSpaceMap_levelHom (n : ℕ) :
    (levelTotalIso ξ n).inv ≫ schemeSpaceMap (levelHom ξ n) = (ξ.level n).toBase :=
  ObjectProperty.hom_ext _ (by
    change (levelIso ξ n).inv ≫ yoneda.map (levelHom ξ n) = (ξ.level n).toBase.hom
    rw [yoneda_map_levelHom]
    exact Iso.inv_hom_id_assoc _ _)

/-- The inverse of `levelTotalIso ξ n` followed by the represented transition of the tower is the
transition of total spaces followed by the inverse of `levelTotalIso ξ (n + 1)`. -/
private theorem levelTotalIso_inv_comp_schemeSpaceMap_towerTransitionSite (n : ℕ) :
    (levelTotalIso ξ n).inv ≫ schemeSpaceMap (towerTransitionSite ξ n) =
      (ξ.transition n).totalMap ≫ (levelTotalIso ξ (n + 1)).inv :=
  ObjectProperty.hom_ext _ (by
    change (levelIso ξ n).inv ≫ yoneda.map (towerTransitionSite ξ n) =
      (ξ.transition n).totalMap.hom ≫ (levelIso ξ (n + 1)).inv
    rw [yoneda_map_towerTransitionSite]
    exact Iso.inv_hom_id_assoc _ _)

/-- The transition of the levels. -/
abbrev towerTransition (n : ℕ) : towerScheme ξ n ⟶ towerScheme ξ (n + 1) :=
  (𝒯).map (towerTransitionSite ξ n)

/-- The `n`-th level is proper over the `n`-th thickening. -/
theorem isProper_towerHom (n : ℕ) : IsProper (towerHom ξ n) := by
  rw [towerHom, Functor.map_comp, eqToHom_map]
  exact (morphismProperty_comp_eqToHom_iff @IsProper _ _).mpr (isProper_levelHom ξ n)

/-- The `n`-th level is flat over the `n`-th thickening. -/
theorem flat_towerHom (n : ℕ) : Flat (towerHom ξ n) := by
  rw [towerHom, Functor.map_comp, eqToHom_map]
  exact (morphismProperty_comp_eqToHom_iff @Flat _ _).mpr (flat_levelHom ξ n)

/-- The squares of the tower of a formal object of `Curves` are cartesian. -/
theorem isPullback_tower (n : ℕ) :
    IsPullback (towerTransition ξ n) (towerHom ξ n) (towerHom ξ (n + 1))
      (adicThickeningSucc ξ.base.R (maximalIdeal ξ.base.R) n) := by
  have h1 : IsPullback (schemeSpaceMap (towerTransitionSite ξ n))
      (schemeSpaceMap (levelHom ξ n)) (schemeSpaceMap (levelHom ξ (n + 1)))
      (schemeSpaceMap (ξ.transition n).baseMap) :=
    (ξ.transition n).cartesian.of_iso (levelTotalIso ξ n).symm (levelTotalIso ξ (n + 1)).symm
      (Iso.refl _) (Iso.refl _)
      (levelTotalIso_inv_comp_schemeSpaceMap_towerTransitionSite ξ n).symm
      ((Category.comp_id _).trans (levelTotalIso_inv_comp_schemeSpaceMap_levelHom ξ n).symm)
      ((Category.comp_id _).trans (levelTotalIso_inv_comp_schemeSpaceMap_levelHom ξ (n + 1)).symm)
      (by simp)
  have h2 : IsPullback (towerTransitionSite ξ n) (levelHom ξ n ≫ eqToHom (level_base ξ n))
      (levelHom ξ (n + 1) ≫ eqToHom (level_base ξ (n + 1)))
      (truncationOverSucc B integerBase hZ ξ.base ξ.contains n) := by
    refine (isPullback_of_isPullback_schemeSpaceMap h1).of_iso (Iso.refl _) (Iso.refl _)
      (eqToIso (level_base ξ n)) (eqToIso (level_base ξ (n + 1))) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    · rw [Iso.refl_hom, Category.id_comp, eqToIso.hom]
    · rw [Iso.refl_hom, Category.id_comp, eqToIso.hom]
    · rw [transition_baseMap, eqToIso.hom, eqToIso.hom, Category.assoc, Category.assoc,
        eqToHom_trans, eqToHom_refl, Category.comp_id]
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  exact h2.map 𝒯

/-- The closed level of a formal object of `Curves` has dimension at most one: it is the fibre of
a family of curves over a field. -/
theorem topologicalKrullDim_towerScheme_zero_le :
    topologicalKrullDim (towerScheme ξ 0) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have := isMaximal_maximalIdeal_pow_zero_add_one ξ.base.R
  let : Field (ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1)) := Ideal.Quotient.field _
  have hK : (𝒯).obj (ξ.level 0).base = Spec (.of (ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1))) :=
    congrArg (𝒯).obj (level_base ξ 0)
  have : Subsingleton ((𝒯).obj (ξ.level 0).base) := by rw [hK]; infer_instance
  set f := (𝒯).map (levelHom ξ 0)
  rcases isEmpty_or_nonempty (towerScheme ξ 0) with h | ⟨⟨x⟩⟩
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).mpr h]; exact bot_le
  · have hpre : f ⁻¹' {f x} = Set.univ := Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
    let e : towerScheme ξ 0 ≃ₜ f.fiber (f x) :=
      (Homeomorph.Set.univ _).symm.trans ((Homeomorph.setCongr hpre.symm).trans
        (f.fiberHomeo (f x)).symm)
    rw [IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph]
    exact topologicalKrullDim_fiber_levelHom_le ξ 0 (f x)

end Tower

/-! ### Families of curves from morphisms of schemes with bounded fibres -/

section Family

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **A flat proper morphism of finite presentation with fibres of dimension at most one is a
family of curves** (Stacks 0D4Z). The relative-dimension condition is read off the fibres of
the morphism of schemes through the identity chart (Stacks 04NC), so no bound on the dimension of
the source is needed. -/
def curveFamilyOfFiberDimensionLE {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((𝒯).map g)) (hproper : IsProper ((𝒯).map g))
    (hlfp : LocallyOfFinitePresentation ((𝒯).map g))
    (hfib : ∀ s, topologicalKrullDim (((𝒯).map g).fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    CurveFamily B hZ where
  base := U
  total := schemeSpace T
  toBase := schemeSpaceMap g
  flat := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    Flat.isEtaleLocalOnSourceAndTarget g).2 hflat
  proper := by
    have := hproper
    refine ⟨(Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance,
      ⟨?_, Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance⟩, ?_⟩
    · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget g).2 inferInstance
    · have hrep : yoneda.relativelyRepresentable (yoneda.map g) :=
        Functor.relativelyRepresentable.map _ _
      exact (Space.presheaf_universallyClosed_iff B integerBase hZ
          (isAlgebraicSpace_yoneda B integerBase hZ T)
          (isAlgebraicSpace_yoneda B integerBase hZ U) hrep).1
        (Space.presheaf_yoneda_map_of_inverseImage B integerBase hZ
          (P := @UniversallyClosed.{u}) inferInstance g inferInstance)
  finitePresentation := by
    have := hproper
    exact ⟨(Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget g).2 hlfp,
      Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance,
      (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance⟩
  relativeDimensionLE x := by
    set y := Space.pointsToScheme B integerBase hZ T x
    have hnat : ∀ d : WithBot ℕ∞, 0 ≤ d → d ≤ (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) →
        ∃ e : ℕ, e ≤ 1 ∧ d = ((e : ℕ∞) : WithBot ℕ∞) := by
      intro d h0 hn
      cases d with
      | bot => exact absurd h0 (by simp)
      | coe c =>
        cases c with
        | top => exact absurd (WithBot.coe_le_coe.mp hn) (not_le.mpr (ENat.natCast_lt_top (1 : ℕ)))
        | coe m => exact ⟨m, by exact_mod_cast hn, rfl⟩
    obtain ⟨e, he, hee⟩ := hnat _
      (topologicalKrullDimAt_nonneg (((𝒯).map g).asFiber y))
      ((topologicalKrullDimAt_le_topologicalKrullDim _).trans (hfib _))
    exact ⟨e, he, (Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B integerBase hZ
      (@HasFiberDimensionAt.{u} (e : ℕ∞)) (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞))
      g x).2 ((hasFiberDimensionAt_ofSchemeHom_iff _ _ _).2 hee)⟩

end Family

/-! ### The algebraization of a formal object of the stack of curves -/

section Algebraization

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (ξ : FormalObject B integerBase hZ (curvesProjectionOver B hZ))

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **Stacks 0E7R for the tower of a formal object of `Curves`.** The tower of schemes of the
levels algebraizes to a projective morphism `Y ⟶ Spec R` identifying each level with the base
change of `Y` to the corresponding thickening. -/
theorem exists_algebraization :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of ξ.base.R)), IsProjectiveMorphism fY ∧
      ∃ k : ∀ n, towerScheme ξ n ⟶ Y, (∀ n, towerTransition ξ n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (towerHom ξ n) fY
          (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n) := by
  have := ξ.base.noetherian
  have := ξ.base.complete
  exact Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one _ _
    (towerHom ξ) (towerTransition ξ) (isPullback_tower ξ) (isProper_towerHom ξ 0)
    (by exact_mod_cast topologicalKrullDim_towerScheme_zero_le ξ)

variable {ξ} {Y : Scheme.{u}} {fY : Y ⟶ Spec (.of ξ.base.R)} {k : ∀ n, towerScheme ξ n ⟶ Y}
  (hpb : ∀ n, IsPullback (k n) (towerHom ξ n) fY
    (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n))
include hpb

/-- The algebraization is flat (Stacks 0D4G), its base changes to the thickenings being the
levels. -/
theorem flat_algebraization [IsProper fY] : Flat fY := by
  have := ξ.base.noetherian
  refine flat_of_flat_pullback_adicThickeningι fY fun n => ?_
  have e : pullback.snd fY (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n) =
      (hpb n).isoPullback.inv ≫ towerHom ξ n := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  rw [e]
  have := flat_towerHom ξ n
  infer_instance

/-- The fibre of the algebraization over the closed point has dimension at most one: it is
contained in the image of the closed level. -/
theorem topologicalKrullDim_fiber_closedPoint_le :
    topologicalKrullDim (fY.fiber (closedPoint ξ.base.R)) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have hι : IsClosedImmersion (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hk : IsClosedImmersion (k 0) := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (hpb 0).flip hι
  have hsub : fY ⁻¹' {closedPoint ξ.base.R} ⊆ Set.range (k 0) := by
    intro y hy
    have hy' : y ∈ Set.range
        (pullback.fst fY (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0)) := by
      rw [Scheme.Pullback.range_fst]
      rw [Set.mem_preimage, Set.mem_singleton_iff.mp hy]
      exact closedPoint_mem_range_adicThickeningι_zero
    obtain ⟨z, rfl⟩ := hy'
    refine ⟨(hpb 0).isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  calc topologicalKrullDim (fY.fiber (closedPoint ξ.base.R))
      = topologicalKrullDim (fY ⁻¹' {closedPoint ξ.base.R}) :=
        IsHomeomorph.topologicalKrullDim_eq _ (fY.fiberHomeo _).isHomeomorph
    _ ≤ topologicalKrullDim (Set.range (k 0)) :=
        (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    _ = topologicalKrullDim (towerScheme ξ 0) :=
        (IsHomeomorph.topologicalKrullDim_eq _
          ((k 0).isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph).symm
    _ ≤ ((1 : ℕ) : WithBot ℕ∞) := topologicalKrullDim_towerScheme_zero_le ξ

end Algebraization

/-! ### Effectivity -/

section Effective

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (ξ : FormalObject B integerBase hZ (curvesProjectionOver B hZ))

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **Every formal object of `Curves` is effective**, for the projection
`AlgebraicGeometry.curvesProjectionOver`: the algebraization of its tower (Stacks 0E7R) is flat
(Stacks 0D4G) with fibres of dimension at most one (Stacks 0D4I), hence a family of curves over
the complete local base, and its identifications with the levels realize the formal object. -/
theorem isEffective_curvesProjectionOver (hp : (curvesProjectionOver B hZ).IsFiberedInGroupoids) :
    FormalObject.IsEffective B integerBase hZ (curvesProjectionOver B hZ) hp ξ := by
  have := ξ.base.noetherian
  have hA : B.Contains (Spec (.of ξ.base.R)) := ξ.contains_spec_base
  obtain ⟨Y, fY, hproj, k, hk, hpb⟩ := exists_algebraization ξ
  have : IsProper fY := isProper_of_isProjectiveMorphism fY hproj
  have hflat : Flat fY := flat_algebraization hpb
  have hlfp : LocallyOfFinitePresentation fY :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hfib : ∀ s, topologicalKrullDim (fY.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    fiberDimension_le_of_closedPoint fY 1 (topologicalKrullDim_fiber_closedPoint_le hpb)
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fY hA
  let T : BigFppfOver B integerBase hZ := CurveFamily.ofScheme Y hY
  let g : T ⟶ baseOver B integerBase hZ ξ.base hA := CurveFamily.homOfScheme fY
  let X : CurveFamily B hZ := curveFamilyOfFiberDimensionLE B hZ g hflat
    (inferInstance : IsProper fY) hlfp hfib
  let K : ∀ n, levelSite ξ n ⟶ T := fun n => CurveFamily.homOfScheme (k n)
  have hK : ∀ n, towerTransitionSite ξ n ≫ K (n + 1) = K n := fun n =>
    (𝒯).map_injective (by rw [Functor.map_comp]; exact hk n)
  let r : ∀ n, ξ.level n ⟶ X := fun n =>
    { baseMap := eqToHom (level_base ξ n) ≫
        restrictionToBase B integerBase hZ ξ.base hA ξ.contains n
      totalMap := (levelTotalIso ξ n).inv ≫ schemeSpaceMap (K n)
      cartesian := by
        have h1 : IsPullback (K n) (levelHom ξ n ≫ eqToHom (level_base ξ n)) g
            (restrictionToBase B integerBase hZ ξ.base hA ξ.contains n) :=
          CurveFamily.isPullback_of_isPullback_toScheme_map
            ((𝒯).map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact (hpb n).w))
            (hpb n)
        refine (CurveFamily.isPullback_schemeSpaceMap_of_isPullback h1).of_iso
          (levelTotalIso ξ n) (Iso.refl _)
          ((schemeSpaceFunctor B integerBase hZ).mapIso (eqToIso (level_base ξ n).symm))
          (Iso.refl _) ?_ ?_ ?_ ?_
        · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm
        · have e : schemeSpaceMap (levelHom ξ n ≫ eqToHom (level_base ξ n)) ≫
              ((schemeSpaceFunctor B integerBase hZ).mapIso
                (eqToIso (level_base ξ n).symm)).hom = schemeSpaceMap (levelHom ξ n) := by
            show (schemeSpaceFunctor B integerBase hZ).map _ ≫
              (schemeSpaceFunctor B integerBase hZ).map _ =
                (schemeSpaceFunctor B integerBase hZ).map _
            rw [← Functor.map_comp, Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
              Category.comp_id]
          exact e.trans (ObjectProperty.hom_ext _ (yoneda_map_levelHom ξ n))
        · exact (Category.comp_id _).trans (Category.id_comp _).symm
        · have e : (schemeSpaceFunctor B integerBase hZ).map (eqToHom (level_base ξ n).symm) ≫
              (schemeSpaceFunctor B integerBase hZ).map (eqToHom (level_base ξ n) ≫
                restrictionToBase B integerBase hZ ξ.base hA ξ.contains n) =
              (schemeSpaceFunctor B integerBase hZ).map
                (restrictionToBase B integerBase hZ ξ.base hA ξ.contains n) := by
            rw [← Functor.map_comp, ← Category.assoc, eqToHom_trans, eqToHom_refl,
              Category.id_comp]
          exact (Category.comp_id _).trans e.symm }
  refine FormalObject.isEffective_of_realization (hA := hA) (x := X) (hx := rfl) hp
    { r := r
      comp_transition := fun n => ?_
      map_eq := fun n => ?_ }
  · apply CurveFamily.Hom.ext
    · show (ξ.transition n).baseMap ≫ eqToHom (level_base ξ (n + 1)) ≫
          restrictionToBase B integerBase hZ ξ.base hA ξ.contains (n + 1) =
        eqToHom (level_base ξ n) ≫ restrictionToBase B integerBase hZ ξ.base hA ξ.contains n
      rw [transition_baseMap, Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, restrictionToBase_succ]
    · show (ξ.transition n).totalMap ≫ (levelTotalIso ξ (n + 1)).inv ≫
          schemeSpaceMap (K (n + 1)) = (levelTotalIso ξ n).inv ≫ schemeSpaceMap (K n)
      rw [← hK n, schemeSpaceMap_comp, ← Category.assoc (levelTotalIso ξ n).inv,
        levelTotalIso_inv_comp_schemeSpaceMap_towerTransitionSite, Category.assoc]
  · show eqToHom (level_base ξ n) ≫ restrictionToBase B integerBase hZ ξ.base hA ξ.contains n =
      eqToHom (ξ.level_eq n) ≫ restrictionToBase B integerBase hZ ξ.base hA ξ.contains n ≫
        eqToHom rfl
    rw [eqToHom_refl, Category.comp_id]
    rfl

end Effective

end CurvesFormal

/-- **Every formal object of the stack of curves is effective** (Stacks 0D58). Let `ξ` be a
formal object of `Curves` over `Spec ℤ`: a Noetherian complete local ring `R` with families of
curves `X_n` over `Spec (R / 𝔪 ^ (n + 1))` and cartesian transitions between them. Then `ξ` is
effective (Stacks 07X7): it comes from a family of curves over `Spec R`.

The proof is the source's: by Stacks 0E7R the tower algebraizes to a projective `X ⟶ Spec R`
restricting to the `X_n`; it is flat by Stacks 0D4G and of relative dimension at most one by the
semicontinuity of the fibre dimension (Stacks 0D4I, the part of Stacks 0D4J that is needed). The
levels of `ξ` are schemes (Stacks 0ADD for the closed level, Stacks 05ZR along the thickenings),
which is what the scheme form of Stacks 0E7R consumes. -/
theorem isEffective_curvesFormalObject (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (ξ : FormalObject B integerBase hZ (curvesFiberedCategory B hZ).val.p) :
    FormalObject.IsEffective B integerBase hZ (curvesFiberedCategory B hZ).val.p
      (curvesFiberedCategory B hZ).property ξ :=
  CurvesFormal.isEffective_curvesProjectionOver ξ (curvesFiberedCategory B hZ).property

end AlgebraicGeometry.C1590Private

end
