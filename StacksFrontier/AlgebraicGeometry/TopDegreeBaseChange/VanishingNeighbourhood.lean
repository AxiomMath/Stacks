module

public import StacksFrontier.AlgebraicGeometry.ProperFibreDimensionNeighbourhood.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FirstDirectImageBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FirstDirectImageFiniteType

/-!
# The vanishing of `R¹ f_* 𝒪_X` near a fibre with `H¹ = 0`

[Stacks, Tag 0E7G]: let `f : X ⟶ Y` be proper and let `y ∈ Y` be a point with `dim(X_y) ≤ 1`
and `H¹(X_y, 𝒪_{X_y}) = 0`. Then there is an open neighbourhood `V` of `y` with
`R¹ f_* 𝒪_X|_V = 0`, and the same holds after base change by any `Y' ⟶ V`.

The source's proof quotes two clauses, finite type of `R¹ f_* 𝒪_X` ([Stacks, Tag 0EX4]) and
its formation commuting with base change ([Stacks, Tag 0EX3]). Both are proved: the first is
`firstDirectImageFiniteTypeOfFibreDimensionOne`, and of the second only the vanishing form is
used, `isZero_pullback_firstDirectImage_iff_of_isPullback`. As in the source, the first step is
to shrink `Y` to an open `W ∋ y` over which all fibres have dimension at most one
([Stacks, Tag 02FZ], `exists_affineOpen_fiberDimension_le`).

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_pullback_firstDirectImage_iff_of_factor`: the vanishing form of the base change of
  `R¹ f_* 𝒪_X` along a morphism factoring through an open over which the fibres have
  dimension at most one.
* `exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber`:
  **[Stacks, Tag 0E7G]**, with the base change taken along any cartesian square over `V`.
* `exists_isOpen_firstDirectImage_vanishes_universally`: **[Stacks, Tag 0E7G]**, with the base
  change the chosen pullback along a morphism into `V`.

## References

* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

variable {X Y : Scheme.{u}}

/-- **The base change of `R¹ f_* 𝒪_X`, read on vanishing, along a morphism that factors through
an open of the base over which all fibres have dimension at most one.** For `g₀ : Y' ⟶ W`, the
pullback of `R¹ f_* 𝒪_X` along `g₀ ≫ W.ι` vanishes exactly when `R¹ f'_* 𝒪_{X'} = 0` for the
base change `f'` of `f` along `g₀ ≫ W.ι`.

The pullback is that of `R¹ (f ∣_ W)_* 𝒪` along `g₀`, and the base change of `f` along
`g₀ ≫ W.ι` is the base change of `f ∣_ W` along `g₀` (pasting with the cartesian square of
`AlgebraicGeometry.isPullback_morphismRestrict`), so this is
`isZero_pullback_firstDirectImage_iff_of_isPullback` for `f ∣_ W`, whose hypothesis is
[Stacks, Tag 0E7D] over the affine opens of `W`. -/
theorem isZero_pullback_firstDirectImage_iff_of_factor_of_isPullback (f : X ⟶ Y) [IsProper f]
    (W : Y.Opens) (hdimW : ∀ y ∈ W, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (g₀ : Y' ⟶ W.toScheme) (hg : g₀ ≫ W.ι = g) :
    IsZero ((Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f)) ↔
      IsZero (firstDirectImageStructureSheaf f') := by
  subst hg
  have hdim' := topologicalKrullDim_fiber_morphismRestrict_le f W 1 hdimW
  have hright := (isPullback_morphismRestrict f W).flip
  have hrange : Set.range g' ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (g' z) ∈ W
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact (g₀ (f' z)).2
  let l := IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g' hrange
  have hl : l ≫ (f ⁻¹ᵁ W).ι = g' := IsOpenImmersion.lift_fac _ _ _
  have hp : l ≫ (f ∣_ W) = f' ≫ g₀ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hl,
      sq.w, Category.assoc]
  have hsq : IsPullback l f' (f ∣_ W) g₀ :=
    IsPullback.of_right (by rwa [hl]) hp hright
  have key := isZero_pullback_firstDirectImage_iff_of_isPullback hsq fun U hU G hG => by
    have _ : IsAffine U.toScheme := hU
    have _ : G.IsQuasicoherent := hG
    exact isZero_cohomology_of_affine_base (d := 1) ((f ∣_ W) ∣_ U)
      (topologicalKrullDim_fiber_morphismRestrict_le (f ∣_ W) U 1 fun t _ => hdim' t) G 2
      (by norm_num)
  let P := firstDirectImageStructureSheaf f
  let e : (Scheme.Modules.pullback (g₀ ≫ W.ι)).obj P ≅
      (Scheme.Modules.pullback g₀).obj (firstDirectImageStructureSheaf (f ∣_ W)) :=
    ((Scheme.Modules.pullbackComp g₀ W.ι).app P).symm ≪≫
      (Scheme.Modules.pullback g₀).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app P).symm ≪≫
      (Scheme.Modules.pullback g₀).mapIso (firstDirectImageRestrictIso f W).symm
  exact e.isZero_iff.trans key

/-- The same, for the chosen base change `pullback.snd f g`. -/
theorem isZero_pullback_firstDirectImage_iff_of_factor (f : X ⟶ Y) [IsProper f] (W : Y.Opens)
    (hdimW : ∀ y ∈ W, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) (g₀ : Y' ⟶ W.toScheme) (hg : g₀ ≫ W.ι = g) :
    IsZero ((Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f)) ↔
      IsZero (firstDirectImageStructureSheaf (pullback.snd f g)) :=
  isZero_pullback_firstDirectImage_iff_of_factor_of_isPullback f W hdimW
    (IsPullback.of_hasPullback f g) g₀ hg

/-- If `P` restricts to zero on an open `V`, its pullback along any `g = l ≫ V.ι` vanishes. -/
private theorem isZero_pullback_of_isZero_restrict {Y' : Scheme.{u}} (P : Y.Modules)
    (V : Y.Opens) (h : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj P))
    (l : Y' ⟶ V.toScheme) {g : Y' ⟶ Y} (hl : l ≫ V.ι = g) :
    IsZero ((Scheme.Modules.pullback g).obj P) :=
  IsZero.of_iso (Functor.map_isZero (Scheme.Modules.pullback l)
      (IsZero.of_iso h ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app P).symm))
    (((Scheme.Modules.pullbackCongr hl).app P).symm ≪≫
      ((Scheme.Modules.pullbackComp l V.ι).app P).symm)

/-- **`R¹ f_* 𝒪_X` vanishes universally near the image of a base change along which it
vanishes.** Let `f : X ⟶ Y` be proper, let `W ⊆ Y` be an open over which all fibres of `f` have
dimension at most one, and let `g : Y' ⟶ Y` factor through `W` with `R¹ f'_* 𝒪_{X'} = 0` for the
base change `f'` of `f` along `g`. Then there is an open `V ⊆ W` containing the image of `g` such
that `R¹ f_* 𝒪_X|_V = 0` and `R¹ f''_* 𝒪_{X''} = 0` for the base change `f''` along every
`Y'' ⟶ V`.

Over `W` the module `R¹ f_* 𝒪_X` is of finite type ([Stacks, Tag 0EX4],
`firstDirectImageFiniteTypeOfFibreDimensionOne`), and its pullback along `g` vanishes
(`isZero_pullback_firstDirectImage_iff_of_factor`), so the image of `g` misses its closed support
([Stacks, Tag 056J]); `V` is the complement of the support in `W`. -/
theorem exists_isOpen_firstDirectImage_vanishes_of_factor (f : X ⟶ Y) [IsProper f]
    (W : Y.Opens) (hdimW : ∀ y ∈ W, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (g₀ : Y' ⟶ W.toScheme) (hg : g₀ ≫ W.ι = g)
    (hR : IsZero (firstDirectImageStructureSheaf f')) :
    ∃ V : Y.Opens, V ≤ W ∧ Set.range g ⊆ V ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      ∀ (Y'' : Scheme.{u}) (g' : Y'' ⟶ V.toScheme),
        IsZero (firstDirectImageStructureSheaf (pullback.snd f (g' ≫ V.ι))) := by
  let P := firstDirectImageStructureSheaf f
  let M' := (Scheme.Modules.restrictFunctor W.ι).obj P
  have hftW : (firstDirectImageStructureSheaf (f ∣_ W)).IsFiniteType :=
    firstDirectImageFiniteTypeOfFibreDimensionOne (f ∣_ W) inferInstance
      (topologicalKrullDim_fiber_morphismRestrict_le f W 1 hdimW)
  have hft : M'.IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (firstDirectImageRestrictIso f W)
  have hpull : IsZero ((Scheme.Modules.pullback g).obj P) :=
    (isZero_pullback_firstDirectImage_iff_of_factor_of_isPullback f W hdimW sq g₀ hg).mpr hR
  have hpull' : IsZero ((Scheme.Modules.pullback g₀).obj M') :=
    IsZero.of_iso hpull <| (Scheme.Modules.pullback g₀).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app P) ≪≫
      (Scheme.Modules.pullbackComp g₀ W.ι).app P ≪≫
      (Scheme.Modules.pullbackCongr hg).app P
  let V' : W.toScheme.Opens := ⟨(SheafOfModules.supp M')ᶜ,
    (SheafOfModules.isClosed_supp M').isOpen_compl⟩
  let V : Y.Opens := W.ι ''ᵁ V'
  have hVW : V ≤ W := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hstalk : ∀ v : Y, v ∈ V → IsZero (P.presheaf.stalk v) := by
    rintro _ ⟨w, hw, rfl⟩
    exact IsZero.of_iso ((notMem_supp_iff_isZero_stalk M' w).mp hw)
      ((Scheme.Modules.restrictStalkNatIso W.ι w).app P).symm
  have hres : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj P) :=
    isZero_of_forall_isZero_stalk _ fun v =>
      IsZero.of_iso (hstalk _ v.2) ((Scheme.Modules.restrictStalkNatIso V.ι v).app P)
  refine ⟨V, hVW, ?_, hres, fun Y'' g' => ?_⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨g₀ z, notMem_supp_of_isZero_pullback M' hft g₀ z hpull', ?_⟩
    rw [← hg, Scheme.Hom.comp_apply]
    rfl
  · refine (isZero_pullback_firstDirectImage_iff_of_factor f W hdimW (g' ≫ V.ι)
      (g' ≫ Y.homOfLE hVW) ?_).mp (isZero_pullback_of_isZero_restrict P V hres g' rfl)
    rw [Category.assoc, Y.homOfLE_ι]

/-- **[Stacks, Tag 0E7G].** Let `f : X ⟶ Y` be proper and let `y ∈ Y` be a point with
`dim(X_y) ≤ 1` and `H¹(X_y, 𝒪_{X_y}) = 0`. Then there is an open neighbourhood `V` of `y` such
that `R¹ f_* 𝒪_X|_V = 0`, and the same holds after base change by any `Y' ⟶ V`: for every
cartesian square `X' ⟶ X`, `f' : X' ⟶ Y'`, `g : Y' ⟶ Y` over `f` with `g(Y') ⊆ V`,
`R¹ f'_* 𝒪_{X'} = 0`.

The source's proof: shrink to an open `W ∋ y` over which all fibres have dimension at most one
([Stacks, Tag 02FZ]); there `R¹ f_* 𝒪_X` is of finite type ([Stacks, Tag 0EX4],
`firstDirectImageFiniteTypeOfFibreDimensionOne`) and its pullback to `Spec κ(y)` is `R¹` of the
fibre, which vanishes; so `y` is outside the closed support ([Stacks, Tag 056J]), and `V` is the
complement of the support in `W` (`exists_isOpen_firstDirectImage_vanishes_of_factor`). For a
base change along `g` into `V`, the pullback of `R¹ f_* 𝒪_X` along `g` factors through its
restriction to `V`, which is zero, and over `W` this pullback is `R¹ f'_* 𝒪_{X'}`
(`isZero_pullback_firstDirectImage_iff_of_factor_of_isPullback`, the vanishing form of
[Stacks, Tag 0EX3]). -/
@[stacks 0E7G]
theorem exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hH : IsZero (firstCohomologyStructureSheaf (f.fiber y))) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      ∀ ⦃X' Y' : Scheme.{u}⦄ {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y},
        IsPullback g' f' f g → Set.range g ⊆ V → IsZero (firstDirectImageStructureSheaf f') := by
  obtain ⟨W, hyW, -, -, -, -, -, hdimW⟩ :=
    ProperFibreDimension.exists_affineOpen_fiberDimension_le f y 1 hdim
  have hrange : Set.range (Y.fromSpecResidueField y) ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.fromSpecResidueField_apply]
    exact hyW
  have _ : IsProper (f.fiberToSpecResidueField y) := isProper_fiberToSpecResidueField f y
  have hfib : IsZero (firstDirectImageStructureSheaf
      (pullback.snd f (Y.fromSpecResidueField y))) :=
    isZero_rightDerivedPlus_pushforward_of_isZero_cohomology (f.fiberToSpecResidueField y) 1
      (SheafOfModules.unit (f.fiber y).ringCatSheaf) hH
  obtain ⟨V, hVW, hrV, hres, -⟩ := exists_isOpen_firstDirectImage_vanishes_of_factor f W hdimW
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))
    (IsOpenImmersion.lift W.ι (Y.fromSpecResidueField y) hrange)
    (IsOpenImmersion.lift_fac _ _ _) hfib
  refine ⟨V, hrV ⟨(default : Spec (Y.residueField y)), Scheme.fromSpecResidueField_apply y _⟩,
    hres, fun X' Y' g' f' g sq hg => ?_⟩
  let P := firstDirectImageStructureSheaf f
  let l := IsOpenImmersion.lift V.ι g (by rwa [Scheme.Opens.range_ι])
  have hl : l ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  refine (isZero_pullback_firstDirectImage_iff_of_factor_of_isPullback f W hdimW sq
    (l ≫ Y.homOfLE hVW) ?_).mp (isZero_pullback_of_isZero_restrict P V hres l hl)
  rw [Category.assoc, Y.homOfLE_ι, hl]

/-- **[Stacks, Tag 0E7G].** Let `f : X ⟶ Y` be proper and let `y ∈ Y` be a point with
`dim(X_y) ≤ 1` and `H¹(X_y, 𝒪_{X_y}) = 0`. Then there is an open neighbourhood `V` of `y` such
that `R¹ f_* 𝒪_X|_V = 0`, and `R¹ f'_* 𝒪_{X'} = 0` for the base change `f'` of `f` along every
`Y' ⟶ V`.

The source's proof: shrink to an open `W ∋ y` over which all fibres have dimension at most one
([Stacks, Tag 02FZ]); there `R¹ f_* 𝒪_X` is of finite type ([Stacks, Tag 0EX4]) and its pullback
to `Spec κ(y)` is `R¹` of the fibre, which vanishes; so `y` is outside the closed support
([Stacks, Tag 056J]). This is
`exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber`
read on the cartesian square of the chosen pullback along `g ≫ V.ι`. -/
@[stacks 0E7G]
theorem exists_isOpen_firstDirectImage_vanishes_universally (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hH : IsZero (firstCohomologyStructureSheaf (f.fiber y))) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme),
        IsZero (firstDirectImageStructureSheaf (pullback.snd f (g ≫ V.ι))) := by
  obtain ⟨V, hyV, hres, huniv⟩ :=
    exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber
      f y hdim hH
  refine ⟨V, hyV, hres, fun Y' g => huniv (IsPullback.of_hasPullback f (g ≫ V.ι)) ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact (g z).2

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
