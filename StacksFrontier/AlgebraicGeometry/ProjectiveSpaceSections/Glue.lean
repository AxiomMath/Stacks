module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.UnitRescale
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Basic
public import StacksFrontier.AlgebraicGeometry.RationalFunctions.Basic

/-!
# Glueing the charts of the morphism to projective space defined by generating sections

Let `L` be an invertible module on a scheme `X` and let `s₀, …, sₙ` be global sections of `L`
whose nonvanishing loci cover `X`. On each chart `X_{sᵢ}` the section `sᵢ` trivializes `L`, so the
ratios `sₖ / sᵢ` are *functions*, and Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections`
turns them into a morphism `X_{sᵢ} ⟶ ℙⁿ`: this is
`Stacks.ProjectiveSpaceSections.chartMorphism`. This file glues those charts into a single
morphism `X ⟶ ℙⁿ`, which is the morphism `φ_{(L, s)}` of the discussion following
[Stacks, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF).

The cocycle computation is the whole content, and it is three steps.

1. On an open `V` contained in both `X_{sᵢ}` and `X_{sⱼ}` the two chart data differ by the single
   unit `sⱼ / sᵢ` *on the variables*: `sₖ / sᵢ = (sₖ / sⱼ) · (sⱼ / sᵢ)` is
   `Stacks.SheafOfModules.divBySection_trans`, and `sⱼ / sᵢ` is a unit by
   `Stacks.SheafOfModules.isUnit_divBySection`.
2. `MvPolynomial.IsHomogeneous.eval₂Hom_const_mul` upgrades that from the variables to every
   homogeneous element: a homogeneous polynomial of degree `d` picks up exactly `d` factors of the
   unit. This is where the degree-one generation of `ℤ[T₀, …, Tₙ]` is used.
3. `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` then identifies the two morphisms, and
   `AlgebraicGeometry.Proj.comp_fromOfGlobalSections` identifies each restricted chart with the
   construction for the restricted ring homomorphism. `AlgebraicGeometry.Scheme.Cover`'s
   `glueMorphisms` glues, the pullback of the two inclusions being the intersection by
   `AlgebraicGeometry.isPullback_opens_inf`.

## Main definitions

* `Stacks.ProjectiveSpaceSections.ratioOn` and `Stacks.ProjectiveSpaceSections.homOn`: the ratio
  `sₖ / sᵢ` and the ring homomorphism `ℤ[T] → Γ(V, 𝒪)` on an arbitrary open `V ≤ X_{sᵢ}`. These
  generalize `chartRatio` and `chartHom`, which are the case `V = X_{sᵢ}`.
* `Stacks.ProjectiveSpaceSections.transitionUnit`: the unit `sⱼ / sᵢ` on an overlap.
* `Stacks.ProjectiveSpaceSections.morphismAtUniverse`: **the morphism `φ_{(L, s)} : X ⟶ ℙⁿ`.**
* `Stacks.ProjectiveSpaceSections.morphismOver`: its lift to `ℙⁿ_S` along a morphism `X ⟶ S`.

## Main results

* `Stacks.ProjectiveSpaceSections.homOn_eq_transitionUnit_pow_mul`: the degreewise rescaling
  identity on an overlap, the hypothesis of
  `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit`.
* `Stacks.ProjectiveSpaceSections.homOfLE_comp_chartMorphism_eq`: **the charts agree on the
  overlaps.**
* `Stacks.ProjectiveSpaceSections.nonvanishingChart_ι_morphismAtUniverse`: on the chart `X_{sᵢ}`
  the glued morphism is `chartMorphism`.

## Implementation notes

The hypothesis of `morphismAtUniverse` is `⨆ i, nonvanishingChart L (sᵢ) = ⊤`, which is literally
`TopologicalSpace.IsOpenCover` of the charts; for a family coming from a
`SheafOfModules.GeneratingSections` indexed by `Fin (n + 1)` it is
`Stacks.ProjectiveSpaceSections.iSup_nonvanishingOpen_eq_top`.

The compatibility of `Scheme.Opens.topIso` with restriction to a smaller open is
`AlgebraicGeometry.homOfLE_appTop_topIso_inv`, which is already proved in
`StacksFrontier/AlgebraicGeometry/RationalFunctions/Basic.lean`; it is reused rather than reproved,
which is why this module imports that one. Its proof contains the reusable trick for this material:
the square of four restriction maps is **not** type-correct at `implicit` transparency in the
specialized form, so `rw [← Functor.map_comp]` fails on its motive, but it is type-correct when the
four opens are left as variables, which is what that file's `presheaf_map_square` does before
specializing.

The two steps of this file that still meet the wall — `appTop_homOfLE_chartRatio`, where the
restriction map of `L` is spelled at `X.toSheafedSpace` on one side and `X.toRingedSpace` on the
other, and `homOfLE_comp_chartMorphism_eq`, where the target is spelled `projectiveSpaceAtUniverse`
on one side and `Proj 𝒜` on the other — are written in term mode for the same reason. No
transparency option is needed in either case.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.ProjectiveSpaceSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

/-- The unique ring homomorphism out of `ULift ℤ` is natural: postcomposing it with any ring
homomorphism gives the unique ring homomorphism to the target. -/
theorem baseHom_comp {R S : Type u} [CommRing R] [CommRing S] (h : R →+* S) :
    h.comp (baseHom R) = baseHom S := by
  ext x
  simp [baseHom]

section RatioOn

variable {n : ℕ} (s : Fin (n + 1) → L.sections) (i k : Fin (n + 1))

/-- The ratio `sₖ / sᵢ`, as a function on an arbitrary open `V` contained in the chart `X_{sᵢ}`.
`Stacks.ProjectiveSpaceSections.chartRatio` is the case `V = X_{sᵢ}`. -/
noncomputable def ratioOn {V : X.Opens} (hV : V ≤ nonvanishingChart L (s i)) :
    Γ(V.toScheme, ⊤) :=
  V.topIso.inv.hom
    (SheafOfModules.divBySection (X := X.toRingedSpace) L (s i) hV ((s k).eval (op V)))

/-- On the whole chart, `ratioOn` is `chartRatio`. -/
theorem ratioOn_le_rfl : ratioOn L s i k le_rfl = chartRatio L s i k := rfl

/-- The ring homomorphism `ℤ[T₀, …, Tₙ] → Γ(V, 𝒪)` sending `Tₖ` to `sₖ / sᵢ`, on an arbitrary
open `V` contained in the chart `X_{sᵢ}`. `Stacks.ProjectiveSpaceSections.chartHom` is the case
`V = X_{sᵢ}`. -/
noncomputable def homOn {V : X.Opens} (hV : V ≤ nonvanishingChart L (s i)) :
    MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) →+* Γ(V.toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (baseHom _) (fun m => ratioOn L s i m hV)

/-- **The ratio restricts to the ratio.** Proved in term mode: the restriction map of the
structure presheaf is spelled at `X.toSheafedSpace` on one side of
`Stacks.SheafOfModules.secRestr_sections_eval` and at `X.toRingedSpace` on the other, which are
equal but not type-correct at `implicit` transparency, so `rw` fails on its motive. -/
theorem appTop_homOfLE_chartRatio {V : X.Opens} (hV : V ≤ nonvanishingChart L (s i)) :
    (X.homOfLE hV).appTop.hom (chartRatio L s i k) = ratioOn L s i k hV :=
  (homOfLE_appTop_topIso_inv hV _).trans
    (congrArg V.topIso.inv.hom
      ((SheafOfModules.map_divBySection L (s i) hV le_rfl _).trans
        (congrArg (SheafOfModules.divBySection (X := X.toRingedSpace) L (s i) hV)
          (SheafOfModules.secRestr_sections_eval L (s k) hV))))

/-- **The chart ring homomorphism restricts to `homOn`.** This is the datum
`AlgebraicGeometry.Proj.comp_fromOfGlobalSections` produces when the chart morphism is restricted
to a smaller open. -/
theorem appTop_homOfLE_comp_chartHom {V : X.Opens} (hV : V ≤ nonvanishingChart L (s i)) :
    (X.homOfLE hV).appTop.hom.comp (chartHom L s i) = homOn L s i hV := by
  rw [chartHom, MvPolynomial.comp_eval₂Hom, baseHom_comp, homOn]
  exact congrArg (MvPolynomial.eval₂Hom (baseHom _))
    (funext fun m => appTop_homOfLE_chartRatio L s i m hV)

end RatioOn

section Overlap

variable {n : ℕ} (s : Fin (n + 1) → L.sections) (i j : Fin (n + 1)) {V : X.Opens}

/-- On an open where both `sᵢ` and `sⱼ` are nonvanishing, the ratio `sⱼ / sᵢ` is a unit. -/
theorem isUnit_ratioOn (hVi : V ≤ nonvanishingChart L (s i))
    (hVj : V ≤ nonvanishingChart L (s j)) : IsUnit (ratioOn L s i j hVi) :=
  (SheafOfModules.isUnit_divBySection (X := X.toRingedSpace) L (s i) (s j) hVi hVj).map
    V.topIso.inv.hom

/-- **The transition unit of the two charts `i` and `j`**: the ratio `sⱼ / sᵢ`, a unit on any open
where both sections are nonvanishing. -/
noncomputable def transitionUnit (hVi : V ≤ nonvanishingChart L (s i))
    (hVj : V ≤ nonvanishingChart L (s j)) : Γ(V.toScheme, ⊤)ˣ :=
  (isUnit_ratioOn L s i j hVi hVj).unit

/-- The underlying element of `transitionUnit` is the ratio `sⱼ / sᵢ`. -/
@[simp] theorem transitionUnit_val (hVi : V ≤ nonvanishingChart L (s i))
    (hVj : V ≤ nonvanishingChart L (s j)) :
    (transitionUnit L s i j hVi hVj : Γ(V.toScheme, ⊤)) = ratioOn L s i j hVi :=
  rfl

/-- **The cocycle identity on the variables**: `sₖ / sᵢ = (sⱼ / sᵢ) · (sₖ / sⱼ)`. -/
theorem ratioOn_eq_transitionUnit_mul (hVi : V ≤ nonvanishingChart L (s i))
    (hVj : V ≤ nonvanishingChart L (s j)) (k : Fin (n + 1)) :
    ratioOn L s i k hVi
      = (transitionUnit L s i j hVi hVj : Γ(V.toScheme, ⊤)) * ratioOn L s j k hVj := by
  rw [transitionUnit_val, ratioOn, ratioOn, ratioOn,
    SheafOfModules.divBySection_trans L (s i) (s j) hVi hVj, map_mul, mul_comm]

/-- **The cocycle identity on every homogeneous element.** The two chart data on an overlap differ
by the `d`-th power of the transition unit on `ℤ[T₀, …, Tₙ]`'s degree-`d` piece. -/
theorem homOn_eq_transitionUnit_pow_mul (hVi : V ≤ nonvanishingChart L (s i))
    (hVj : V ≤ nonvanishingChart L (s j)) (d : ℕ)
    (a : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) d) :
    homOn L s i hVi a
      = (transitionUnit L s i j hVi hVj : Γ(V.toScheme, ⊤)) ^ d * homOn L s j hVj a := by
  rw [homOn, homOn,
    funext fun m => ratioOn_eq_transitionUnit_mul L s i j hVi hVj m]
  exact ((MvPolynomial.mem_homogeneousSubmodule d a).1 ha).eval₂Hom_const_mul _ _ _

/-- **The charts of `φ_{(L, s)}` agree on their overlaps.** On an open where both `sᵢ` and `sⱼ`
are nonvanishing the two chart morphisms restrict to the same morphism to `ℙⁿ`: by
`AlgebraicGeometry.Proj.comp_fromOfGlobalSections` each restriction is the construction for the
restricted ring homomorphism, and those two differ degreewise by the transition unit, so
`AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` identifies them. -/
theorem homOfLE_comp_chartMorphism_eq (hVi : V ≤ nonvanishingChart L (s i))
    (hVj : V ≤ nonvanishingChart L (s j)) :
    X.homOfLE hVi ≫ chartMorphism L s i = X.homOfLE hVj ≫ chartMorphism L s j := by
  have hff' : ∀ (d : ℕ), ∀ a ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) d,
      ((X.homOfLE hVi).appTop.hom.comp (chartHom L s i)) a
        = (transitionUnit L s i j hVi hVj : Γ(V.toScheme, ⊤)) ^ d
          * ((X.homOfLE hVj).appTop.hom.comp (chartHom L s j)) a := by
    intro d a ha
    rw [appTop_homOfLE_comp_chartHom L s i hVi, appTop_homOfLE_comp_chartHom L s j hVj]
    exact homOn_eq_transitionUnit_pow_mul L s i j hVi hVj d a ha
  exact (Proj.comp_fromOfGlobalSections _ (X.homOfLE hVi) (chartHom L s i)
      (map_irrelevant_chartHom_eq_top L s i)
      (Proj.map_irrelevant_comp_appTop_eq_top _ _ _ (map_irrelevant_chartHom_eq_top L s i))).trans
    (((Proj.fromOfGlobalSections_congr_unit _ _ _ (transitionUnit L s i j hVi hVj)
        hff' _ _).symm).trans
      (Proj.comp_fromOfGlobalSections _ (X.homOfLE hVj) (chartHom L s j)
        (map_irrelevant_chartHom_eq_top L s j)
        (Proj.map_irrelevant_comp_appTop_eq_top _ _ _
          (map_irrelevant_chartHom_eq_top L s j))).symm)

end Overlap

section Glue

variable {n : ℕ} (s : Fin (n + 1) → L.sections)
  (hs : (⨆ i, nonvanishingChart L (s i)) = ⊤)

/-- The cover of `X` by the nonvanishing loci of the `sᵢ`, as a `Scheme.OpenCover`. -/
noncomputable def chartCover : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun i => nonvanishingChart L (s i)) hs

/-- **The charts agree on the overlaps, in the pullback form
`AlgebraicGeometry.Scheme.Cover.glueMorphisms` asks for.** The pullback of the two inclusions is
the intersection of the two charts, by `AlgebraicGeometry.isPullback_opens_inf`. -/
theorem pullback_fst_comp_chartMorphism (i j : Fin (n + 1)) :
    pullback.fst (nonvanishingChart L (s i)).ι (nonvanishingChart L (s j)).ι
        ≫ chartMorphism L s i
      = pullback.snd (nonvanishingChart L (s i)).ι (nonvanishingChart L (s j)).ι
        ≫ chartMorphism L s j := by
  rw [← cancel_epi (isPullback_opens_inf (nonvanishingChart L (s i))
      (nonvanishingChart L (s j))).isoPullback.hom, ← Category.assoc, ← Category.assoc,
    IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
  exact homOfLE_comp_chartMorphism_eq L s i j inf_le_left inf_le_right

/-- **The morphism to projective space defined by a family of generating sections of an invertible
module.** This is the morphism `φ_{(L, s)} : X ⟶ ℙⁿ` of the discussion following
[Stacks, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF): on the chart `X_{sᵢ}`, where `sᵢ`
trivializes `L`, it is the morphism defined by the functions `s₀/sᵢ, …, sₙ/sᵢ`. -/
noncomputable def morphismAtUniverse : X ⟶ projectiveSpaceAtUniverse.{u} n :=
  (chartCover L s hs).glueMorphisms (fun i => chartMorphism L s i)
    fun i j => pullback_fst_comp_chartMorphism L s i j

/-- **On the chart `X_{sᵢ}` the glued morphism is `chartMorphism`.** -/
@[simp] theorem nonvanishingChart_ι_morphismAtUniverse (i : Fin (n + 1)) :
    (nonvanishingChart L (s i)).ι ≫ morphismAtUniverse L s hs = chartMorphism L s i :=
  (chartCover L s hs).ι_glueMorphisms _ _ i

/-- **The morphism to relative projective space defined by a family of generating sections.** The
lift of `morphismAtUniverse` along a structure morphism `f : X ⟶ S`, by the universal property of
the pullback defining `projectiveSpaceOver`. -/
noncomputable def morphismOver {S : Scheme.{u}} (f : X ⟶ S) : X ⟶ projectiveSpaceOver n S :=
  projectiveSpaceOver.liftAtUniverse n f (morphismAtUniverse L s hs)

/-- Composing `morphismOver` with the projection to `S` gives the structure morphism `f`. -/
@[simp] theorem morphismOver_fst {S : Scheme.{u}} (f : X ⟶ S) :
    morphismOver L s hs f ≫ pullback.fst _ _ = f :=
  projectiveSpaceOver.liftAtUniverse_fst _ _ _

/-- Composing `morphismOver` with the projection to `projectiveSpaceAtUniverse` gives
`morphismAtUniverse`. -/
@[simp] theorem morphismOver_toIntegralAtUniverse {S : Scheme.{u}} (f : X ⟶ S) :
    morphismOver L s hs f ≫ projectiveSpaceOver.toIntegralAtUniverse n S
      = morphismAtUniverse L s hs :=
  projectiveSpaceOver.liftAtUniverse_toIntegralAtUniverse _ _ _

end Glue

end Stacks.ProjectiveSpaceSections

end
