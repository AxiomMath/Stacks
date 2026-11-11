module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology

/-!
# The first direct image of the structure sheaf and the first cohomology of a fibre

Let `f : X ⟶ Y` be proper and let `y ∈ Y` be a point whose fibre has dimension at most one.
[Stacks, Tag 0E7F] deduces `H¹(X_y, 𝒪_{X_y}) = 0` from the vanishing of `R¹ f_* 𝒪_X`, or more
generally from the vanishing of `R¹ f'_* 𝒪_{X'}` for a base change `g : Y' ⟶ Y` whose image
contains `y`; [Stacks, Tag 0E7G] goes back, producing from `H¹(X_y, 𝒪_{X_y}) = 0` an open
neighbourhood of `y` over which `R¹ f_* 𝒪_X` vanishes universally. Both proofs quote the same two
clauses about `R¹ f_* 𝒪_X`: that it is quasi-coherent **of finite type** ([Stacks, Tag 0EX4]) and
that **its formation commutes with arbitrary base change** ([Stacks, Tag 0E7D], through
[Stacks, Tag 0EX3] (b)).

Both clauses are proved in this development for fibre dimension one: the finite-type clause is
`firstDirectImageFiniteTypeOfFibreDimensionOne` (`FirstDirectImageFiniteType.lean`), and the
base-change clause, in the vanishing form the two arguments use, is
`isZero_pullback_firstDirectImage_iff_of_isPullback` (`FirstDirectImageBaseChangeVanishing.lean`).
Those files import this one, so the argument below takes the two clauses as arguments `hft` and
`hbc`; [Stacks, Tag 0E7G] itself, with no further argument, is
`exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber` and
`exists_isOpen_firstDirectImage_vanishes_universally` in `VanishingNeighbourhood.lean`.
The connecting device is the support of a module of finite type: it is closed
(`SheafOfModules.isClosed_supp`) and its formation commutes with pullback
(`SheafOfModules.supp_pullback`), which is exactly what replaces the source's passage through the
finite module `M` over an affine base, Nakayama's lemma and the localisation `M_f = 0`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `exists_isOpen_isZero_restrict_firstDirectImage_of_isZero_cohomologyOne_fiber`: the argument
  of [Stacks, Tag 0E7G] from the finite-type clause `hft` and the base-change isomorphisms `hbc`.

[Stacks, Tag 0E7F] itself is
`isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage` and its `_baseChange`
form in `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/FibreFirstCohomology.lean`, without
the hypotheses `hft` and `hbc`.

Along the way, three facts about supports that the two arguments share:
`notMem_supp_iff_isZero_stalk`, `notMem_supp_of_isZero_pullback`,
`isZero_pullback_fromSpecResidueField_of_notMem_supp`, and the neighbourhood statement
`exists_isOpen_isZero_restrict_of_isZero_stalk`.

Also `isZero_firstDirectImage_structureSheaf_restrict`: the vanishing of `R¹ f_* 𝒪_X` passes to
the restriction of `f` over an open of the base.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.fiber` is *defined* as `pullback f (Y.fromSpecResidueField y)` and
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` as the second projection of that pullback,
so instantiating `hbc` at `g := Y.fromSpecResidueField y` already speaks about the fibre; the
normalised forms are named in explicit `have`s so that no step depends on unfolding a `def`.

Properness of `f.fiberToSpecResidueField y` is not found by instance search, because that `def`
is not unfolded by it. It is obtained from `CategoryTheory.MorphismProperty.of_isPullback`
applied to `CategoryTheory.IsPullback.of_hasPullback`, after which quasi-separatedness follows by
instance search; quasi-compactness is already an instance.

`SheafOfModules.IsFiniteType` is passed as an explicit argument rather than an instance binder:
at the `AlgebraicGeometry.Scheme.Modules` spelling instance search does not match Mathlib's
instances, the same wall `TopDegreeBaseChange/FinitePresentationSuffices.lean` documents.

The fibre dimension bound is carried because the tags state it, but it is not used: the two
arguments use it only to make the two quoted clauses available, and here those clauses are
arguments.

## References

* [Stacks Project, Tag 0E7F](https://stacks.math.columbia.edu/tag/0E7F)
* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {X Y : Scheme.{u}}

/-- `R¹ f_* 𝒪_X`, the first higher direct image of the structure sheaf. -/
abbrev firstDirectImageStructureSheaf (f : X ⟶ Y) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerivedPlus 1).obj (SheafOfModules.unit X.ringCatSheaf)

/-- `H¹(Z, 𝒪_Z)`, the first cohomology of the structure sheaf of a scheme, as a module over
`Γ(Z, ⊤)`. -/
abbrev firstCohomologyStructureSheaf (Z : Scheme.{u}) : ModuleCat.{u} Γ(Z, ⊤) :=
  ((moduleGlobalSections Z).rightDerivedPlus 1).obj (SheafOfModules.unit Z.ringCatSheaf)

/-- **The base-change clause quoted by [Stacks, Tags 0E7F] and [0E7G]**: the formation of
`R¹ f_* 𝒪_X` commutes with an arbitrary base change `g : Y' ⟶ Y`, so that the pullback of
`R¹ f_* 𝒪_X` along `g` is the first higher direct image of the structure sheaf of `X ×_Y Y'`.

This is [Stacks, Tag 0EX3] (b) for the structure sheaf in degree one, which [Stacks, Tag 0E7D]
makes available once the fibres of `f` are bounded by one. Its vanishing form, which is what the
proofs of [Stacks, Tags 0E7F] and [0E7G] use, is proved at fibre dimension one as
`isZero_pullback_firstDirectImage_iff_of_isPullback` in `FirstDirectImageBaseChangeVanishing.lean`;
the statements below take the isomorphisms themselves as an argument. -/
abbrev FirstDirectImageCommutesBaseChange (f : X ⟶ Y) : Type (u + 1) :=
  ∀ ⦃Y' : Scheme.{u}⦄ (g : Y' ⟶ Y),
    (Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f) ≅
      firstDirectImageStructureSheaf (pullback.snd f g)

/-- The morphism from a fibre to the spectrum of the residue field of the image point is proper:
the fibre square is cartesian and properness is stable under base change. -/
theorem isProper_fiberToSpecResidueField (f : X ⟶ Y) [IsProper f] (y : Y) :
    IsProper (f.fiberToSpecResidueField y) :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹_›

/-- A point misses the support of a sheaf of modules exactly when the stalk there is a zero
object. -/
theorem notMem_supp_iff_isZero_stalk {Z : Scheme.{u}} (M : Z.Modules) (z : Z) :
    z ∉ SheafOfModules.supp M ↔ IsZero (M.presheaf.stalk z) := by
  refine ⟨fun h => AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩, fun h hz => ?_⟩
  · have ha : ∀ a : M.presheaf.stalk z, a = 0 := fun a => by
      by_contra hA
      exact h ⟨a, hA⟩
    rw [ha a, ha b]
  · have _ : Subsingleton (M.presheaf.stalk z) := AddCommGrpCat.isZero_iff_subsingleton.mp h
    obtain ⟨a, ha⟩ := hz
    exact ha (Subsingleton.elim (α := M.presheaf.stalk z) a 0)

/-- **A module of finite type whose pullback along `g` vanishes misses the support at every point
of the image of `g`.** The support of the pullback is the inverse image of the support
([Stacks, Tag 056J], `SheafOfModules.supp_pullback`), and a zero object has empty support.

This is the step the source performs with Nakayama's lemma: over an affine base the support
condition at `g z'` says that the finite module `M` has vanishing localisation there. -/
theorem notMem_supp_of_isZero_pullback {Z Z' : Scheme.{u}} (M : Z.Modules)
    (hM : M.IsFiniteType) (g : Z' ⟶ Z) (z' : Z')
    (h : IsZero ((Scheme.Modules.pullback g).obj M)) :
    g z' ∉ SheafOfModules.supp M := by
  have _ : M.IsFiniteType := hM
  have hz' : z' ∉ SheafOfModules.supp ((Scheme.Modules.pullback g).obj M) :=
    (notMem_supp_iff_isZero_stalk _ z').mpr
      (isZero_stalk_of_isZero_module ((Scheme.Modules.pullback g).obj M) z' h)
  rw [SheafOfModules.supp_pullback g M] at hz'
  exact hz'

/-- **A module of finite type which misses the support at `z` has vanishing pullback to
`Spec κ(z)`.** Every point of `Spec κ(z)` maps to `z`, so by [Stacks, Tag 056J] the pullback has
empty support, hence vanishing stalks, hence is a zero object. -/
theorem isZero_pullback_fromSpecResidueField_of_notMem_supp {Z : Scheme.{u}} (M : Z.Modules)
    (hM : M.IsFiniteType) (z : Z) (h : z ∉ SheafOfModules.supp M) :
    IsZero ((Scheme.Modules.pullback (Z.fromSpecResidueField z)).obj M) := by
  have _ : M.IsFiniteType := hM
  refine isZero_of_forall_isZero_stalk _ fun w => ?_
  refine (notMem_supp_iff_isZero_stalk _ w).mp ?_
  rw [SheafOfModules.supp_pullback (Z.fromSpecResidueField z) M, Set.mem_preimage,
    Scheme.fromSpecResidueField_apply]
  exact h

/-- Under base-change compatibility, the pullback of `R¹ f_* 𝒪_X` along `g` vanishes exactly when
`R¹ f'_* 𝒪_{X'}` vanishes for the base change `f'` of `f` along `g`. -/
private theorem isZero_pullback_firstDirectImage_iff {f : X ⟶ Y}
    (hbc : FirstDirectImageCommutesBaseChange f) {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsZero ((Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f)) ↔
      IsZero (firstDirectImageStructureSheaf (pullback.snd f g)) :=
  ⟨fun h => IsZero.of_iso h (hbc g).symm, fun h => IsZero.of_iso h (hbc g)⟩

/-- **The fibre form of the base-change clause.** If the pullback of `R¹ f_* 𝒪_X` to
`Spec κ(y)` vanishes, then `H¹(X_y, 𝒪_{X_y}) = 0`.

The base `Spec κ(y)` is affine and `X_y ⟶ Spec κ(y)` is proper, so `hbc` identifies the pullback
with `R¹ (f_y)_* 𝒪_{X_y}` and a vanishing higher direct image over an affine base is vanishing
cohomology (`isZero_cohomology_of_isZero_rightDerivedPlus_pushforward`, [Stacks, Tag 01XK]). -/
theorem isZero_cohomologyOne_fiber_of_isZero_pullback (f : X ⟶ Y) [IsProper f] (y : Y)
    (hbc : FirstDirectImageCommutesBaseChange f)
    (h : IsZero ((Scheme.Modules.pullback (Y.fromSpecResidueField y)).obj
      (firstDirectImageStructureSheaf f))) :
    IsZero (firstCohomologyStructureSheaf (f.fiber y)) := by
  have _ : IsProper (f.fiberToSpecResidueField y) := isProper_fiberToSpecResidueField f y
  have hfib : IsZero (firstDirectImageStructureSheaf (f.fiberToSpecResidueField y)) :=
    (isZero_pullback_firstDirectImage_iff hbc _).mp h
  exact isZero_cohomology_of_isZero_rightDerivedPlus_pushforward
    (f.fiberToSpecResidueField y) 1 (SheafOfModules.unit (f.fiber y).ringCatSheaf) hfib

/-- **A module of finite type with a vanishing stalk vanishes on a neighbourhood.** The support
of a sheaf of modules of finite type is closed (`SheafOfModules.isClosed_supp`), so its
complement is an open neighbourhood of any point whose stalk vanishes, and the restriction of the
module to that open has all its stalks zero.

This is the geometric form of the source's final step, where a finite module with vanishing
localisation at `𝔭` is killed by some `a ∉ 𝔭` and hence vanishes on `D(a)`. -/
theorem exists_isOpen_isZero_restrict_of_isZero_stalk {Z : Scheme.{u}} (M : Z.Modules)
    (hM : M.IsFiniteType) (z : Z) (h : IsZero (M.presheaf.stalk z)) :
    ∃ V : Z.Opens, z ∈ V ∧ IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M) := by
  have _ : M.IsFiniteType := hM
  refine ⟨⟨(SheafOfModules.supp M)ᶜ, (SheafOfModules.isClosed_supp M).isOpen_compl⟩,
    (notMem_supp_iff_isZero_stalk M z).mpr h, ?_⟩
  refine isZero_of_forall_isZero_stalk _ fun w => ?_
  exact IsZero.of_iso ((notMem_supp_iff_isZero_stalk M _).mp w.2)
    ((Scheme.Modules.restrictStalkNatIso _ w).app M)

/-- **The argument of [Stacks, Tag 0E7G] from the finite-type and base-change clauses.** Let
`f : X ⟶ Y` be proper, let `R¹ f_* 𝒪_X` be of finite type (`hft`) with formation commuting with
base change (`hbc`), and let `y ∈ Y` be a point with `H¹(X_y, 𝒪_{X_y}) = 0`. Then there is an
open `V ∋ y` with `R¹ f_* 𝒪_X|_V = 0`, and `R¹ f'_* 𝒪_{X'} = 0` for the base change along every
`g : Y' ⟶ V`. The tag itself, where both clauses are proved from the fibre dimension bound, is
`exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber` and
`exists_isOpen_firstDirectImage_vanishes_universally`.

The hypothesis on the fibre makes `R¹ (f_y)_* 𝒪_{X_y}` vanish over the affine base `Spec κ(y)`,
hence by `hbc` the pullback of `R¹ f_* 𝒪_X` along `Spec κ(y) ⟶ Y`; so `y` misses the support of
`R¹ f_* 𝒪_X` by [Stacks, Tag 056J]. The support is closed because of the finite-type clause
`hft`, which gives the neighbourhood `V`. Universality after base change is `hbc` again, applied
to `g ≫ V.ι` and read through the compatibility of pullback with composition. -/
theorem exists_isOpen_isZero_restrict_firstDirectImage_of_isZero_cohomologyOne_fiber
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (_hdim : topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (hbc : FirstDirectImageCommutesBaseChange f)
    (hH : IsZero (firstCohomologyStructureSheaf (f.fiber y))) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme),
        IsZero (firstDirectImageStructureSheaf (pullback.snd f (g ≫ V.ι))) := by
  have _ : IsProper (f.fiberToSpecResidueField y) := isProper_fiberToSpecResidueField f y
  have hfib : IsZero (firstDirectImageStructureSheaf (f.fiberToSpecResidueField y)) :=
    isZero_rightDerivedPlus_pushforward_of_isZero_cohomology (f.fiberToSpecResidueField y) 1
      (SheafOfModules.unit (f.fiber y).ringCatSheaf) hH
  have hsupp : y ∉ SheafOfModules.supp (firstDirectImageStructureSheaf f) := by
    have := notMem_supp_of_isZero_pullback (firstDirectImageStructureSheaf f) hft
      (Y.fromSpecResidueField y) (default : Spec (Y.residueField y))
      ((isZero_pullback_firstDirectImage_iff hbc _).mpr hfib)
    rwa [Scheme.fromSpecResidueField_apply] at this
  obtain ⟨V, hyV, hV⟩ :=
    exists_isOpen_isZero_restrict_of_isZero_stalk (firstDirectImageStructureSheaf f) hft y
      ((notMem_supp_iff_isZero_stalk _ y).mp hsupp)
  refine ⟨V, hyV, hV, fun Y' g => ?_⟩
  have h1 : IsZero ((Scheme.Modules.pullback V.ι).obj (firstDirectImageStructureSheaf f)) :=
    IsZero.of_iso hV
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        (firstDirectImageStructureSheaf f)).symm
  exact (isZero_pullback_firstDirectImage_iff hbc _).mp <| IsZero.of_iso (Functor.map_isZero _ h1)
    ((Scheme.Modules.pullbackComp g V.ι).app (firstDirectImageStructureSheaf f)).symm

/-- **The vanishing of `R¹ f_* 𝒪_X` restricted over an open of the base.** If `R¹ f_* 𝒪_X = 0`
then `R¹ (f ∣_ V)_* 𝒪_{f⁻¹V} = 0` for every open `V ⊆ Y`.

Restriction to `V` is additive, so it kills `R¹ f_* 𝒪_X`; the restriction comparison of
[Stacks, Tag 01E5] identifies the result with `R¹ (f ∣_ V)_*` of the restriction of `𝒪_X`, which
is `𝒪_{f⁻¹V}` by `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`. -/
theorem isZero_firstDirectImage_structureSheaf_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (h : IsZero (firstDirectImageStructureSheaf f)) :
    IsZero (firstDirectImageStructureSheaf (f ∣_ V)) := by
  have h1 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (firstDirectImageStructureSheaf f)) := Functor.map_isZero _ h
  have h2 : IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus ((1 : ℕ) : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (SheafOfModules.unit X.ringCatSheaf))) :=
    IsZero.of_iso h1
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f V 1
        (SheafOfModules.unit X.ringCatSheaf))
  exact IsZero.of_iso h2
    (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus 1).mapIso
      (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ V).ι)).symm

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
