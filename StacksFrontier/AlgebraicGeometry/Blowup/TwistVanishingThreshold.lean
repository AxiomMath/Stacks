module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjAmple.DegreeOneCover
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechVanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Serre vanishing for the twists on an affine blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `X = Proj(⨁_{n ≥ 0} Iⁿ)` the blowup of
`Spec A` in `I`. This file produces the vanishing half of the threshold `q(A, I)` of
[Stacks, Tag 0G9Z]:

`∃ q₀, ∀ q ≥ q₀, ∀ i > 0, Hⁱ(X, 𝒪_X(q)) = 0`.

The Rees algebra is generated in degree one over its degree-zero part
(`Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top`), so the standard opens of its
degree-one elements cover `X` and `𝒪_X(1)` is an **ample** invertible sheaf; `X` is **proper**
over the affine Noetherian `Spec A` (`Stacks.Blowup.instIsProperToSpec`). That is exactly the
situation of [Stacks, Tag 02O1] over an affine base, which is proved with no hypothesis as
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase`, and it hands out
a single bound serving every positive cohomological degree at once. Finally `𝒪_X(1)^{⊗ q}` is
`𝒪_X(q)` by `Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf`.

## Main results

* `Stacks.Blowup.isAmple_twistingSheaf_reesGrading_one`: **`𝒪_X(1)` is ample on the affine
  blowup.**
* `Stacks.Blowup.exists_forall_isZero_rightDerivedPlus_twistingSheaf_reesGrading`:
  **the vanishing half of the threshold `q(A, I)`**, in the `rightDerivedPlus` spelling in which
  `StacksFrontier/AlgebraicGeometry/Blowup/TwistedPullbackTerms.lean` and
  `StacksFrontier/AlgebraicGeometry/Blowup/TwistedPullbackSections.lean` consume it.

## Implementation notes

The cohomology of a scheme appears here in two spellings: `Hgroup`, valued in
abelian groups and `ℕ`-indexed, which [Stacks, Tag 02O1]'s affine-base form is stated in, and the
right derived functor of `Stacks.Cohomology.sectionsFunctor`, valued in `Γ(X, ⊤)`-modules and
`ℤ`-indexed through `rightDerivedPlus`, which the twisted-pullback files use. They are matched by
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup` and
`Stacks.DerivedIndexing.rightDerivedIso`.

**No `@[stacks]` attribute is attached.** The statements here are the paragraph of
[Stacks, Tag 0G9Z] that fixes `q(A, I)`, not a numbered lemma of the source; the tags whose
content they instantiate — [Stacks, Tag 02O1] and [Stacks, Tag 01PS] — are carried by the
declarations used.

## References

* [Stacks Project, Tag 0G9Z](https://stacks.math.columbia.edu/tag/0G9Z)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- Every point of the affine blowup lies in the standard open of a degree-one element of the
Rees algebra: those standard opens cover, by
`Stacks.Blowup.iSup_basicOpen_reesGrading_one_eq_top`. -/
theorem exists_mem_basicOpen_reesGrading_one (x : ProjectiveSpectrum.top (reesGrading I)) :
    ∃ g : reesAlgebra I, g ∈ reesGrading I 1 ∧
      x ∈ ProjectiveSpectrum.basicOpen (reesGrading I) g := by
  have htop : (⨆ f : reesGrading I 1,
      ProjectiveSpectrum.basicOpen (reesGrading I) (f : reesAlgebra I)) = ⊤ :=
    iSup_basicOpen_reesGrading_one_eq_top I
  have hx : x ∈ (⨆ f : reesGrading I 1,
      ProjectiveSpectrum.basicOpen (reesGrading I) (f : reesAlgebra I)) := by
    rw [htop]
    trivial
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨(f : reesAlgebra I), f.2, hf⟩

/-- `𝒪_X(1)` is invertible on the affine blowup, at the spelling the ampleness predicates are
stated in. The Rees algebra is generated in degree one, which is what
`AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf` asks
for; it is applied by name because instance search does not cross the two spellings of the
structure sheaf. -/
@[ega "II 8.6.4" "special case"]
instance algebraicGeometry_isInvertible_twistingSheaf_reesGrading (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (blowUpSpec I).toRingedSpace.presheaf
      (structureSheafRing (blowUpSpec I).toRingedSpace).property
      (twistingSheaf (reesGrading I) n) :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf
    (reesGrading I) (adjoin_reesGradingZero_reesGrading_one_eq_top I) n

/-- `𝒪_X(1)` is invertible on the affine blowup, at the spelling the ampleness theory uses. -/
instance isInvertibleModule_twistingSheaf_reesGrading (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (blowUpSpec I) (twistingSheaf (reesGrading I) n) :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf
    (reesGrading I) (adjoin_reesGradingZero_reesGrading_one_eq_top I) n

/-- The same at the `Proj (reesGrading I)` spelling of the blowup: `Stacks.Blowup.blowUpSpec` is
a definition, and instance search does not unfold it. -/
instance isInvertibleModule_twistingSheaf_reesGrading' (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj (reesGrading I))
      (twistingSheaf (reesGrading I) n) :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf
    (reesGrading I) (adjoin_reesGradingZero_reesGrading_one_eq_top I) n

/-- **`𝒪_X(1)` is an ample invertible sheaf on the affine blowup `X = Proj(⨁_{n ≥ 0} Iⁿ)`.**

`X` is quasi-compact over the Noetherian base and every point lies in the standard open of a
degree-one element of the Rees algebra, which is the hypothesis of
`Stacks.ProjDegreeOneCover.isAmple_twistingModule_one`; the two ampleness predicates of
[Stacks, Tag 01PS] are identified by `Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple`. -/
theorem isAmple_twistingSheaf_reesGrading_one [IsNoetherianRing A] :
    Stacks.Ample.IsAmple (blowUpSpec I) (twistingSheaf (reesGrading I) 1) :=
  Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple _ _
    (Stacks.ProjDegreeOneCover.isAmple_twistingModule_one (reesGrading I)
      (inferInstanceAs (CompactSpace (blowUpSpec I)))
      (exists_mem_basicOpen_reesGrading_one I))

/-- **Serre vanishing for the twists on the affine blowup, in the `Hgroup` spelling.** One bound
`q₀` serves every positive cohomological degree: `Hⁱ(X, 𝒪_X(q)) = 0` for `i > 0` and `q ≥ q₀`. -/
theorem exists_forall_isZero_Hgroup_twistingSheaf_reesGrading [IsNoetherianRing A] :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ p : ℕ, 0 < p →
      IsZero (Hgroup (blowUpSpec I).ringCatSheaf ⊤ p
        (twistingSheaf (reesGrading I) (q : ℤ))) := by
  have hnoeth : IsLocallyNoetherian (Spec (CommRingCat.of A)) :=
    AlgebraicGeometry.isLocallyNoetherian_Spec.mpr inferInstance
  obtain ⟨q₀, hq₀⟩ :=
    Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase
      (blowUpSpec I) (Spec (CommRingCat.of A)) (toSpec I) inferInstance hnoeth inferInstance
      (twistingSheaf (reesGrading I) 1) (isAmple_twistingSheaf_reesGrading_one I)
  refine ⟨q₀, fun q hq p hp => ?_⟩
  refine (hq₀ q hq p hp).of_iso ?_
  exact (Hfunctor (blowUpSpec I).ringCatSheaf ⊤ p).mapIso
    (Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf
      (reesGrading I) (adjoin_reesGradingZero_reesGrading_one_eq_top I) (q : ℤ)).symm

/-- **The vanishing half of the threshold `q(A, I)` of [Stacks, Tag 0G9Z].**

For `A` Noetherian and `I ⊆ A` an ideal there is a `q₀` such that for every `q ≥ q₀` the
positive-degree cohomology of `𝒪_X(q)` on the blowup `X` of `Spec A` in `I` vanishes. This is
the spelling consumed by `Stacks.Blowup.derivedGlobalSectionsTwistedPullbackIso` and the theorems
built on it. -/
theorem exists_forall_isZero_rightDerivedPlus_twistingSheaf_reesGrading [IsNoetherianRing A] :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ j : ℤ, 0 < j →
      IsZero (((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightDerivedPlus j).obj
        (twistingSheaf (reesGrading I) (q : ℤ))) := by
  obtain ⟨q₀, hq₀⟩ := exists_forall_isZero_Hgroup_twistingSheaf_reesGrading I
  refine ⟨q₀, fun q hq j hj => ?_⟩
  have hj' : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj.le
  have hz := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (blowUpSpec I).ringCatSheaf ⊤ j.toNat (twistingSheaf (reesGrading I) (q : ℤ))).mpr
        (hq₀ q hq j.toNat (by omega))
  have hz' : IsZero ((((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightDerivedPlus
      ((j.toNat : ℕ) : ℤ)).obj (twistingSheaf (reesGrading I) (q : ℤ)))) :=
    hz.of_iso (((Stacks.DerivedIndexing.rightDerivedIso
      (Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤) j.toNat).app
        (twistingSheaf (reesGrading I) (q : ℤ))).symm)
  rwa [hj'] at hz'

end Stacks.Blowup

end
