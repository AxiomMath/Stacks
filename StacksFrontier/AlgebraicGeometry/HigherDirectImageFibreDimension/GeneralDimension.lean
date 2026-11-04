module

public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionAffine
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimension
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 02V7: the higher direct images of a proper morphism die above the fibre dimension

[Stacks, Tag 02V7] fixes a proper morphism `f : X ⟶ Y` onto a locally Noetherian scheme and a
point `y ∈ Y` whose fibre has dimension `d`, and asserts that `(Rᵖ f_* ℱ)_y = 0` for every
coherent `ℱ` on `X` and every `p > d`. **The tag is proved here, for an arbitrary `d`.**

The argument is the source's. It has two halves. The first is the reduction to an affine base,
already available in `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/`: the locus of points of
`X` where the fibre has local dimension at most `d` is open and `f` is closed, so `y` has an
affine open neighbourhood `V` over which *every* fibre has dimension at most `d`
(`AlgebraicGeometry.exists_isAffineOpen_forall_topologicalKrullDim_fiber_le`); the stalk at `y`
only sees `f ∣_ V` (`…SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict`),
and over an affine base the higher direct image vanishes as soon as the absolute cohomology does
([Stacks, Tags 01XJ and 01XK], in
`…TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`).

The second half is the substance and is in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageFibreDimension/GeneralDimensionAffine.lean`:
over an affine Noetherian base `Spec A` with all fibres of dimension at most `d`, the cohomology
`Hᵖ(X, ℱ)` of a coherent module vanishes for `p > d`. That is where the theorem on formal
functions and Grothendieck vanishing enter; see that file's module documentation.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.FibreDimension`.

* `isZero_stalk_rightDerivedPlus_of_fiber_dimension_le`: **[Stacks, Tag 02V7]**.
* `isZero_rightDerived_moduleGlobalSections_of_affine_base`: the affine-base case over an
  arbitrary affine locally Noetherian scheme rather than over `Spec A` for a ring `A`.
* `topologicalKrullDim_fiber_comp_iso_le`: the transport of a fibre-dimension bound along an
  isomorphism of the target, which is what lets the previous statement be read off the one over
  `Spec Γ(Y₀, ⊤)`.

## Implementation notes

Fibre dimension is `topologicalKrullDim (f.fiber y)` and is bounded above rather than fixed, as
everywhere else in this development: the source's `dim(X_y) = d` is read as `dim(X_y) ≤ d`, which
is the direction its conclusion uses and is the weaker hypothesis.

The degree is an integer, which is how `CategoryTheory.Functor.rightDerivedPlus` is indexed, and
`d` is a natural number; the source's `p > d` is `(d : ℤ) < p`, which forces `p ≥ 0` and lets the
degree be converted to a natural number inside the proof.

`CategoryTheory.HasDerivedCategory.standard` is given a raised priority. Without it a different
`HasDerivedCategory` instance in the import closure is selected and the `rightDerivedPlus` in the
statement acquires a derived-category universe different from the one the rest of
`TopDegreeBaseChange/` uses, so the statements no longer compose.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.FibreDimension

attribute [local instance 2000] HasDerivedCategory.standard

/-- **A fibre-dimension bound transports along an isomorphism of the target.** If every fibre of
`h : X₀ ⟶ Y₀` has dimension at most `d` and `e : Y₀ ≅ Y₁`, then every fibre of `h ≫ e.hom` does
too: the fibre of `h ≫ e.hom` over `s` is the fibre of `h` over `e.inv s`, because the square
with sides the identity of `X₀` and `e.inv` commutes on points and `e.inv` is injective
(`AlgebraicGeometry.fiberHomeoOfSquare`). -/
theorem topologicalKrullDim_fiber_comp_iso_le {X₀ Y₀ Y₁ : Scheme.{u}} (h : X₀ ⟶ Y₀)
    (e : Y₀ ≅ Y₁) {d : ℕ}
    (hfib : ∀ s : Y₀, topologicalKrullDim (h.fiber s) ≤ (d : WithBot ℕ∞)) (s : Y₁) :
    topologicalKrullDim ((h ≫ e.hom).fiber s) ≤ (d : WithBot ℕ∞) := by
  have hih : ∀ z : Y₀, e.inv.base (e.hom.base z) = z :=
    fun z => (Scheme.homeoOfIso e).symm_apply_apply z
  have hinj : Function.Injective e.inv.base := (Scheme.homeoOfIso e.symm).injective
  have hcomm : ∀ x : X₀, h.base ((Homeomorph.refl (X₀ : Type u)) x) =
      e.inv.base ((h ≫ e.hom).base x) := fun x => by
    simpa using (hih (h.base x)).symm
  refine le_trans (le_of_eq ?_) (hfib (e.inv.base s))
  exact IsHomeomorph.topologicalKrullDim_eq _
    (_root_.AlgebraicGeometry.fiberHomeoOfSquare h (h ≫ e.hom)
      (Homeomorph.refl (X₀ : Type u)) e.inv hinj hcomm s).isHomeomorph

/-- **[Stacks, Tag 02V7] over an affine locally Noetherian base, in its cohomological form.**
For `g : X₀ ⟶ Y₀` proper with `Y₀` affine and locally Noetherian and every fibre of dimension at
most `d`, the cohomology `Hᵖ(X₀, ℱ)` of a coherent module vanishes for `p > d`.

This is the statement over `Spec A`,
`isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le`,
read through `AlgebraicGeometry.Scheme.isoSpec`: the ring of global functions of an affine
locally Noetherian scheme is Noetherian, and composing `g` with the isomorphism
`Y₀ ≅ Spec Γ(Y₀, ⊤)` changes neither properness nor the fibres. -/
theorem isZero_rightDerived_moduleGlobalSections_of_affine_base {X₀ Y₀ : Scheme.{u}}
    (g : X₀ ⟶ Y₀) [IsProper g] [IsAffine Y₀] [IsLocallyNoetherian Y₀] {d : ℕ}
    (hfib : ∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞))
    (F : X₀.Modules) [F.IsCoherent] {p : ℕ} (hp : d < p) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X₀).rightDerived p).obj F) := by
  have : IsNoetherianRing ↥Γ(Y₀, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y₀⟩
  have e : Y₀ ≅ Spec (.of ↥Γ(Y₀, ⊤)) := Y₀.isoSpec
  have : IsProper (g ≫ e.hom) := by
    have : IsIso e.hom := inferInstance
    infer_instance
  exact isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le (g ≫ e.hom)
    (topologicalKrullDim_fiber_comp_iso_le g e hfib) F hp

/-- **[Stacks, Tag 02V7].** Let `f : X ⟶ Y` be a morphism of schemes and let `y ∈ Y`. Assume
`Y` locally Noetherian, `f` proper and `dim(X_y) = d`. Then for every coherent sheaf `ℱ` on `X`
we have `(Rᵖ f_* ℱ)_y = 0` for all `p > d`.

The fibre dimension is taken as the upper bound `dim(X_y) ≤ d`, which is what the proof uses.
A neighbourhood `V` of `y` over which every fibre is bounded by `d` is produced by
`AlgebraicGeometry.exists_isAffineOpen_forall_topologicalKrullDim_fiber_le`; the stalk at `y` of
the higher direct image along `f` is the one along `f ∣_ V`; over the affine base `V` the higher
direct image vanishes as soon as the cohomology of `f ⁻¹ V` does; and that vanishing is
`isZero_rightDerived_moduleGlobalSections_of_affine_base`. -/
@[stacks 02V7, ega "III 4.2.2" "partial", sga "6 X 4.4" "Stalk form of (4.4.5)"]
theorem isZero_stalk_rightDerivedPlus_of_fiber_dimension_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] (p : ℤ) (hp : (d : ℤ) < p) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).presheaf.stalk y) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hyV, hVaff, hVdim⟩ :=
    _root_.AlgebraicGeometry.exists_isAffineOpen_forall_topologicalKrullDim_fiber_le f
      f.isClosedMap y d hdim
  let : IsAffine V.toScheme := hVaff
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg ((Int.natCast_nonneg d).trans hp.le)).symm⟩
  have hn : d < n := by exact_mod_cast hp
  set F' := (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F with hF'
  have : F'.IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion (f ⁻¹ᵁ V).ι F
  have : F'.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F'
  refine SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict f V y hyV F
    (Int.natCast_nonneg n)
    (TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
      (f ∣_ V) (n : ℤ) F' ?_)
  rw [Stacks.Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup,
    ← Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      (R := (f ⁻¹ᵁ V).toScheme.ringCatSheaf) (U := ⊤) n F']
  exact isZero_rightDerived_moduleGlobalSections_of_affine_base (f ∣_ V)
    (fun s => _root_.AlgebraicGeometry.topologicalKrullDim_fiber_morphismRestrict_le f V d
      (fun z hz => hVdim z hz) s) F' hn

end Stacks.AlgebraicGeometry.FibreDimension

end
