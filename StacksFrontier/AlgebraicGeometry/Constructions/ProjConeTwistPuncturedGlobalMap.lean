module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedLocalRestriction

/-!
# The degreewise inclusion `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` and let `U ⊆ L` be the punctured cone.
Over a standard open `D₊(f)` of a positive-degree homogeneous element,
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp` is the inclusion of
`Γ(D₊(f), 𝒪_P(m))` in `Γ(D₊(f), (π|_U)_* 𝒪_U)` as a map of modules over `Γ(P, D₊(f))`. This file
**glues those local maps into a morphism of sheaves of `𝒪_P`-modules**

  `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U`,

for **every** integer `m`, which is the degreewise half of the presentation
`(π|_U)_* 𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` of [Stacks, Tag 0EKG]. It is the punctured analogue of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeTwistGlobalMap.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistStandardOpenHomData`: the local maps
  as a `Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom`: **the morphism
  `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U` of sheaves of `𝒪_P`-modules**, for every integer `m`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.awayToSection_degreeZeroRingMap_sigmaMulPsi`: the
  identification `B_{(σ f · ψ f)} = Γ(L, D₊(σ f · ψ f))` of [Stacks, Tag 01M6] intertwines the
  degree-zero restriction map of `B` with the restriction map of `𝒪_L`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedChartRestrict_restrict`: **restriction to the
  chart of `U` commutes with restriction between two standard opens.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp_restrict`: **the punctured
  degreewise inclusion is compatible with restriction between two standard opens**, which is the
  hypothesis the gluing principle asks for.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp_degree_indep`: the local map
  depends only on the standard open, not on the degree in which the element cutting it out is
  homogeneous.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_app`: the glued morphism restricts on
  each standard open of the basis to the local map.

## Implementation notes

Both charts of `U` appearing in the restriction compatibility are cut out by
`AlgebraicGeometry.Scheme.Hom.appLE` of the open immersion of `U`, so the two composites to be
compared are handled by the naturality of `appLE` in its two variables,
`AlgebraicGeometry.Scheme.Hom.map_appLE` and `AlgebraicGeometry.Scheme.Hom.appLE_map`: both
reduce to `appLE` between the *same* pair of opens, and the inequality of opens such an `appLE`
carries is a proposition, so the two agree. That is
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedChartRestrict_restrict`, and it replaces the
`Subsingleton.elim`-on-opens bookkeeping of the nonnegative case, where the comparison took place
inside a single presheaf.

For the same reason the degree-independence of the local map is the degree-independence of
`Stacks.Truncation.puncturedGradingEquivSectionsTwist` alone: the chart restriction
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedChartRestrict` mentions the degree only in a
proof argument.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}

/-! ### The restriction compatibility of the punctured degreewise inclusion -/

/-- The identification `B_{(σ f · ψ f)} = Γ(L, D₊(σ f · ψ f))` of [Stacks, Tag 01M6] intertwines
the degree-zero restriction map of `B` with the restriction map of `𝒪_L`. This is
`ProjectiveSpectrum.basicOpenIsoAway_restrict` read on elements, at the element `σ f · ψ f`
cutting out the chart of the punctured cone. -/
theorem awayToSection_degreeZeroRingMap_sigmaMulPsi {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) :
    (AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 g)).hom
        (ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (sigmaMulPsi 𝒜 f) (sigmaMulPsi 𝒜 g)
          ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩ ⟨e, he, sigmaMulPsi_mem_grading 𝒜 e hg⟩
          (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg) z) =
      ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
          (homOfLE (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg)).op).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom z) := by
  have h := ProjectiveSpectrum.basicOpenIsoAway_restrict (grading 𝒜) (sigmaMulPsi 𝒜 f)
    (sigmaMulPsi 𝒜 g) d e (sigmaMulPsi_mem_grading 𝒜 d hf) hd
    (sigmaMulPsi_mem_grading 𝒜 e hg) he
    (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg)
  rw [AlgebraicGeometry.Proj.basicOpenIsoAway_hom,
    AlgebraicGeometry.Proj.basicOpenIsoAway_hom] at h
  exact congrArg (fun φ : CommRingCat.of
    (HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) ⟶
      Γ(AlgebraicGeometry.Proj (grading 𝒜),
        AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 g)) =>
    CommRingCat.Hom.hom φ z) h

/-- **Restriction to the chart of `U` commutes with restriction between two standard opens.**
Both composites are `AlgebraicGeometry.Scheme.Hom.appLE` of the open immersion of `U` between
the same pair of opens — `D₊(σ f · ψ f)` of `L` and the chart of `U` over `D₊(g)` — and the
inequality of opens that an `appLE` carries is a proposition. -/
theorem puncturedChartRestrict_restrict {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e)
    (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
          (homOfLE (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg)).op ≫
        puncturedChartRestrict 𝒜 e hg he =
      puncturedChartRestrict 𝒜 d hf hd ≫ (openUInL 𝒜).toScheme.presheaf.map
        ((Opens.map ((openUInL 𝒜).ι ≫ pi 𝒜).base).map (homOfLE hfg)).op := by
  have h1 := Scheme.Hom.map_appLE (openUInL 𝒜).ι
    (U := AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 g))
    (V := ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g)
    (puncturedPi_preimage_basicOpen 𝒜 e hg he).le
    (homOfLE (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg)).op
  have h2 := Scheme.Hom.appLE_map (openUInL 𝒜).ι
    (U := AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
    (V := ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (puncturedPi_preimage_basicOpen 𝒜 d hf hd).le
    ((Opens.map ((openUInL 𝒜).ι ≫ pi 𝒜).base).map (homOfLE hfg)).op
  exact h1.trans h2.symm

/-- **The local punctured degreewise inclusion commutes with restriction to a smaller standard
open.** This is the compatibility the gluing principle of [Stacks, Tag 009U] asks for. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to (pi|_U)_* O_U over standard opens is \
compatible with restriction between two standard opens, for every integer m"]
theorem puncturedConeTwistApp_restrict (m : ℤ) {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (puncturedConeTwistApp 𝒜 m e hg he).hom
        (((twistingSheaf 𝒜 m).val.map (homOfLE hfg).op).hom s) =
      ((Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map
          (homOfLE hfg).op).hom ((puncturedConeTwistApp 𝒜 m d hf hd).hom s) := by
  have key := ConcreteCategory.congr_hom (puncturedChartRestrict_restrict 𝒜 hf hd hg he hfg)
    ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom
      (puncturedConeTwistAwayHom 𝒜 m d hf hd s))
  simp only at key
  have hL : (puncturedConeTwistApp 𝒜 m e hg he).hom
        (((twistingSheaf 𝒜 m).val.map (homOfLE hfg).op).hom s) =
      (puncturedChartRestrict 𝒜 e hg he).hom
        (((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
            (homOfLE (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg)).op).hom
          ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom
            (puncturedConeTwistAwayHom 𝒜 m d hf hd s))) := by
    refine (puncturedConeTwistApp_apply 𝒜 m e hg he _).trans ?_
    refine Eq.trans (congrArg (fun w => (puncturedChartRestrict 𝒜 e hg he).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 g)).hom w))
      (puncturedConeTwistAwayHom_degreeZeroRingMap 𝒜 m hf hd hg he hfg s)) ?_
    exact congrArg (puncturedChartRestrict 𝒜 e hg he).hom
      (awayToSection_degreeZeroRingMap_sigmaMulPsi 𝒜 hf hd hg he hfg _)
  have hR : ((Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map
          (homOfLE hfg).op).hom ((puncturedConeTwistApp 𝒜 m d hf hd).hom s) =
      ((openUInL 𝒜).toScheme.presheaf.map
          ((Opens.map ((openUInL 𝒜).ι ≫ pi 𝒜).base).map (homOfLE hfg)).op).hom
        ((puncturedChartRestrict 𝒜 d hf hd).hom
          ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom
            (puncturedConeTwistAwayHom 𝒜 m d hf hd s))) :=
    congrArg ((Stacks.Morphisms.pushforwardStructureSheaf
        ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map (homOfLE hfg).op).hom
      (puncturedConeTwistApp_apply 𝒜 m d hf hd s)
  exact hL.trans (key.trans hR.symm)

/-- **The local punctured degreewise inclusion depends only on the standard open**, not on the
degree in which the element cutting it out is homogeneous. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to (pi|_U)_* O_U over one standard open depends \
only on that open, not on the degree of the element cutting it out, for every integer m"]
theorem puncturedConeTwistApp_degree_indep (m : ℤ) {d d' : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hf' : f ∈ 𝒜 d') (hd' : 0 < d') :
    puncturedConeTwistApp 𝒜 m d hf hd = puncturedConeTwistApp 𝒜 m d' hf' hd' := by
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  rw [puncturedConeTwistApp_apply, puncturedConeTwistApp_apply]
  exact congrArg (fun z => (puncturedChartRestrict 𝒜 d hf hd).hom
      ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom z))
    (puncturedGradingEquivSectionsTwist_symm_degree_indep 𝒜 hf hd hf' hd' m s)

/-! ### Gluing the local maps -/

section Glue

open Stacks.AlgebraicGeometry.ProjTwistComparison

/-- The local punctured degreewise inclusion attached to a positive-degree homogeneous element,
with a degree for it chosen. The choice is immaterial, by
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp_degree_indep`. -/
def puncturedConeTwistStandardOpenApp (m : ℤ) (p : PositiveElem 𝒜) :
    (twistingSheaf 𝒜 m).val.obj (op (positiveBasicOpen 𝒜 p)) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.obj
        (op (positiveBasicOpen 𝒜 p)) :=
  puncturedConeTwistApp 𝒜 m (Classical.choose p.2) (Classical.choose_spec p.2).2
    (Classical.choose_spec p.2).1

/-- **The local data of the punctured degreewise inclusion**, in the form the gluing principle
consumes: the maps on the sections over the positive-degree standard opens, together with their
compatibility with restriction. -/
def puncturedConeTwistStandardOpenHomData (m : ℤ) :
    StandardOpenHomData 𝒜 (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 m)
      (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)) where
  app := puncturedConeTwistStandardOpenApp 𝒜 m
  app_restrict p q h s :=
    puncturedConeTwistApp_restrict 𝒜 m (Classical.choose_spec p.2).2
      (Classical.choose_spec p.2).1 (Classical.choose_spec q.2).2
      (Classical.choose_spec q.2).1 h s

/-- **The degreewise inclusion `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U`**, for every integer `m`: the morphism of
sheaves of `𝒪_P`-modules glued from the local maps over the standard opens of positive-degree
homogeneous elements. This is the degreewise half of the presentation
`(π|_U)_* 𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` of [Stacks, Tag 0EKG]. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to (pi|_U)_* O_U as a morphism of sheaves of \
O_P-modules, for the punctured cone of the truncation algebra and every integer m"]
def puncturedTwistHom (m : ℤ) :
    ProjectiveSpectrum.Proj.twistingSheaf 𝒜 m ⟶
      Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜) :=
  homOfStandardOpenHomData 𝒜 (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 m)
    (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜))
    (puncturedConeTwistStandardOpenHomData 𝒜 m)

/-- **The glued punctured morphism restricts on a standard open to the local degreewise
inclusion.** -/
@[stacks 0EKG "the global punctured degreewise inclusion restricts on each standard open to the \
local one, for every integer m"]
theorem puncturedTwistHom_app (m : ℤ) (p : PositiveElem 𝒜) :
    (puncturedTwistHom 𝒜 m).val.app (op (positiveBasicOpen 𝒜 p)) =
      puncturedConeTwistStandardOpenApp 𝒜 m p :=
  homOfStandardOpenHomData_app 𝒜 (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 m)
    (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜))
    (puncturedConeTwistStandardOpenHomData 𝒜 m) p

end Glue

end Stacks.AlgebraicGeometry.ProjConeTwist

end
