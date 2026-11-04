module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectHomAffineLeafColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroDerivedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral

/-!
# Homomorphisms between perfect objects along a limit of algebraic spaces

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated
algebraic spaces over `S` with affine transition morphisms, a limit `X` and a chosen index `0` —
let `E₀` and `K₀` be perfect objects of `D(𝒪_{X₀})`.  This file proves, with no hypothesis beyond
the situation and the chapter's convention of Stacks 07SD,

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) = Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`,

the derived pullbacks being taken with the canonical pseudofunctoriality of Stacks 0D6D
(`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`).  This is Stacks 09RI for a
perfect object `K₀`, and it is the full faithfulness half of Stacks 09RJ.

The proof is the source's.  Reading Situation 09RH as Situation 0DKU with the identity of the
chosen stage (`AlgebraicGeometry.Space.DescentSituation.toRelative`), the induction principle of
Stacks 08GP, run on extensions by zero along étale morphisms with Mayer–Vietoris at the step,
reduces the statement to the base changes along affine algebraic spaces étale over `X₀`, and
there it is `AlgebraicGeometry.Space.DescentSituation.isColim_restrict_toRelative_of_isPerfect`.
The step is
`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_canonical_of_restrict_affine`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.homDescent_toRelative_of_isPerfect`.

## Implementation notes

The chapter's convention of Stacks 07SD (`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`
for the system of the situation) is carried, with the index in the universe of the site.  It is
implied by the size bound `#I < B.cutoff.ord.cof` of Stacks 07SF, and some such hypothesis is
needed in the big fppf sites of this library.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian


attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.system)

include hconv in
/-- **Stacks 09RI for perfect objects, on Situation 09RH read as Situation 0DKU.** -/
theorem homDescent_toRelative_of_isPerfect
    (E₀ K₀ : @DerivedCategory (Modules.{u, u} B S hS (D.stage D.base).obj
      (D.stage D.base).property) _ _ (HasDerivedCategory.standard _))
    (hE₀ : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
        (D.stage D.base).obj (D.stage D.base).property)
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).IsPerfect E₀)
    (hK₀ : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
        (D.stage D.base).obj (D.stage D.base).property)
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).IsPerfect K₀) :
    D.toRelative.HomDescent (DerivedPullbackComposition.canonical B S hS) E₀ K₀ := by
  let := fun (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) =>
    HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  have h := D.toRelative.shiftedHomDescent_canonical_of_restrict_affine E₀ K₀
    fun {U₀} hU₀ g hg _ _ _ _ _ _ n => by
      have hflat := D.toRelative.isFlat_of_isEtale_affine hg
      have hfp := D.toRelative.isFinitePresentation_of_isEtale_affine hU₀ hg
      have hP := isPerfect_smallEtaleDerivedModulePullback
        (D.toRelative.restrictInitial hU₀.isAlgebraicSpace g hflat hfp)
      exact ((D.toRelative.restrict hU₀.isAlgebraicSpace g hflat hfp).homDescent_iff_isColim
        (DerivedPullbackComposition.canonical B S hS) _ _).2
        (isColim_restrict_toRelative_of_isPerfect hU₀.isAlgebraicSpace g hflat hfp hconv hU₀ _ _
          (RingedSite.isPerfect_shift_general _ (hP E₀ hE₀) n) (hP K₀ hK₀))
  exact D.toRelative.homDescent_of_iso (DerivedPullbackComposition.canonical B S hS)
    ((shiftFunctorZero _ ℤ).app E₀) (h 0)

end DescentSituation

end AlgebraicGeometry.Space

end
