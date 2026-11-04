module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.SectionRingMultiplicative

/-!
# The graded localizations of the two section rings agree

`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/SectionRingMultiplicative.lean` identifies two
realisations of Stacks Tag 01CV's graded ring `Γ_*(X, L)` as graded rings:
`Stacks.SectionRingProjTheta.sectionGradedRingHom` goes from
`Stacks.AmpleFiniteAvoidance.grading M`, the family `Proj` is taken of, to
`Stacks.SheafOfModules.sectionRingGrading`, the family the graded localizations of Stacks Tags
0B5L and 01PW are formed at, and `Stacks.SectionRingProjTheta.sectionGradedRingHomInv` goes back.

This file carries that identification down to the degree-zero homogeneous localizations: the ring
of the standard open `D₊(s) ⊆ Proj Γ_*(X, L)` that `AlgebraicGeometry.Proj.basicOpenIsoSpec`
consumes is `HomogeneousLocalization.Away` of the grading `Proj` is taken of, whereas Tag 01PW's
localizations are formed at the other grading.

## Main definitions

* `Stacks.SectionRingProjTheta.homogeneousAwayEquiv`: the degree-zero chart rings agree:
  `HomogeneousLocalization.Away` of the grading `Proj` is taken of, at `x`, is isomorphic as a
  ring to `HomogeneousLocalization.Away` of Tag 01PW's grading, at the image of `x`.
* `Stacks.SectionRingProjTheta.awayEquiv`: the same for the ordinary (ungraded) localization
  `Localization.Away`, which is what a `LocalizedModule` over the section ring is formed over.

## Main results

* `Stacks.SectionRingProjTheta.powers_map_sectionGradedRingHom`: the graded comparison carries
  the powers of `x` onto the powers of its image; both localizations are formed at a
  `Submonoid.powers`.
* `Stacks.SectionRingProjTheta.powers_le_comap_sectionGradedRingHom` and
  `Stacks.SectionRingProjTheta.powers_le_comap_sectionGradedRingHomInv`: that identification in
  the `≤ Submonoid.comap` form `HomogeneousLocalization.map` and
  `IsLocalization.ringEquivOfRingEquiv` ask for, in both directions.
* `Stacks.SectionRingProjTheta.homogeneousAwayMap_leftInverse` and
  `Stacks.SectionRingProjTheta.homogeneousAwayMap_rightInverse`: the two transports are mutually
  inverse, pointwise.
* `Stacks.SectionRingProjTheta.homogeneousAwayEquiv_mk`: the isomorphism on a homogeneous
  fraction is the fraction of the transported numerator and denominator.

## Implementation notes

`Stacks.SectionRingProjTheta.homogeneousLocalizationMap_eq_self_of_eq_id`, the only step that
reasons about `HomogeneousLocalization.map` of a composite, is stated for an arbitrary graded
ring: rewriting `Stacks.SectionRingProjTheta.sectionGradedRingHomInv_comp` underneath
`HomogeneousLocalization.map` at the sheaf-theoretic types exceeds the default heartbeat budget
at `isDefEq`.

`homogeneousAwayEquiv` is built with `RingEquiv.ofRingHom` rather than the anonymous constructor:
supplying `invFun` to a `RingEquiv` built with `__ :=` makes the elaborator check the structure's
fields against the transported ring hom at the full sheaf-theoretic spelling, which also exhausts
the heartbeat budget.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.SectionRingProjTheta

universe u

/-- Transport of a homogeneous localization along a graded ring endomorphism that is the identity
is the identity. -/
theorem homogeneousLocalizationMap_eq_self_of_eq_id
    {ι σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → σ} [GradedRing 𝒜] {P : Submonoid A}
    {g : 𝒜 →+*ᵍ 𝒜} (hg : g = GradedRingHom.id 𝒜) (h : P ≤ P.comap g)
    (y : HomogeneousLocalization 𝒜 P) :
    HomogeneousLocalization.map g h y = y := by
  subst hg
  exact congrArg (fun k => k y) (HomogeneousLocalization.map_id 𝒜 P)

section Scheme

-- Inside `namespace Stacks.SectionRingProjTheta` a bare `open AlgebraicGeometry` resolves to
-- `Stacks.AlgebraicGeometry` instead of the root namespace, leaving `Scheme` unknown.
open _root_.AlgebraicGeometry

-- The local instances of the `Scheme` section of `SectionRingMultiplicative.lean`; the last four
-- are needed because instance search does not cross the two spellings of a scheme's structure
-- sheaf.
attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  schemeStacksIsInvertible
  schemeTensorRightEquiv
  schemeSectionGCommRing
  schemeSectionRingGradingGradedRing

variable {X : Scheme.{u}} (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]

/-- The graded comparison of the two section rings carries the powers of `x` onto the powers of
the image of `x`. -/
theorem powers_map_sectionGradedRingHom (x : Stacks.GradedSections.sectionRing M) :
    (Submonoid.powers x).map (sectionGradedRingHom M) =
      Submonoid.powers (sectionGradedRingHom M x) :=
  Submonoid.map_powers _ _

/-- `powers_map_sectionGradedRingHom` in the `≤ Submonoid.comap` form that
`HomogeneousLocalization.map` and `IsLocalization.ringEquivOfRingEquiv` ask for. -/
theorem powers_le_comap_sectionGradedRingHom (x : Stacks.GradedSections.sectionRing M) :
    Submonoid.powers x ≤
      (Submonoid.powers (sectionGradedRingHom M x)).comap (sectionGradedRingHom M) :=
  Submonoid.le_comap_of_map_le _ (le_of_eq (powers_map_sectionGradedRingHom M x))

/-- `powers_le_comap_sectionGradedRingHom` for the inverse comparison. -/
theorem powers_le_comap_sectionGradedRingHomInv (x : Stacks.GradedSections.sectionRing M) :
    Submonoid.powers (sectionGradedRingHom M x) ≤
      (Submonoid.powers x).comap (sectionGradedRingHomInv M) := by
  refine Submonoid.le_comap_of_map_le _ (le_of_eq ?_)
  refine (Submonoid.map_powers (sectionGradedRingHomInv M) _).trans ?_
  exact congrArg Submonoid.powers ((sectionSiteSectionRingEquiv M).symm_apply_apply x)

/-- Transporting a degree-zero fraction to Tag 01PW's grading and back is the identity. -/
theorem homogeneousAwayMap_leftInverse (x : Stacks.GradedSections.sectionRing M)
    (y : HomogeneousLocalization.Away (Stacks.AmpleFiniteAvoidance.grading M) x) :
    HomogeneousLocalization.map (sectionGradedRingHomInv M)
        (powers_le_comap_sectionGradedRingHomInv M x)
        (HomogeneousLocalization.map (sectionGradedRingHom M)
          (powers_le_comap_sectionGradedRingHom M x) y) = y :=
  (HomogeneousLocalization.map_map (powers_le_comap_sectionGradedRingHom M x)
      (powers_le_comap_sectionGradedRingHomInv M x) y).trans
    (homogeneousLocalizationMap_eq_self_of_eq_id (sectionGradedRingHomInv_comp M) _ y)

/-- Transporting a degree-zero fraction from Tag 01PW's grading and back is the identity. -/
theorem homogeneousAwayMap_rightInverse (x : Stacks.GradedSections.sectionRing M)
    (z : HomogeneousLocalization.Away (Stacks.SheafOfModules.sectionRingGrading
      (Stacks.SheafOfModules.sectionSiteRing X)
      (Stacks.SheafOfModules.sectionSiteSheaf X) M) (sectionGradedRingHom M x)) :
    HomogeneousLocalization.map (sectionGradedRingHom M)
        (powers_le_comap_sectionGradedRingHom M x)
        (HomogeneousLocalization.map (sectionGradedRingHomInv M)
          (powers_le_comap_sectionGradedRingHomInv M x) z) = z :=
  (HomogeneousLocalization.map_map (powers_le_comap_sectionGradedRingHomInv M x)
      (powers_le_comap_sectionGradedRingHom M x) z).trans
    (homogeneousLocalizationMap_eq_self_of_eq_id (sectionGradedRingHom_comp M) _ z)

/-- **The degree-zero chart rings of the two section rings agree.** On the left is the ring of the
standard open `D₊(x) ⊆ Proj Γ_*(X, L)` that `AlgebraicGeometry.Proj.basicOpenIsoSpec` consumes; on
the right is the ring Tag 01PW's graded localization at `x` is formed over. -/
def homogeneousAwayEquiv (x : Stacks.GradedSections.sectionRing M) :
    HomogeneousLocalization.Away (Stacks.AmpleFiniteAvoidance.grading M) x ≃+*
      HomogeneousLocalization.Away (Stacks.SheafOfModules.sectionRingGrading
        (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) M) (sectionGradedRingHom M x) :=
  RingEquiv.ofRingHom
    (HomogeneousLocalization.map (sectionGradedRingHom M)
      (powers_le_comap_sectionGradedRingHom M x))
    (HomogeneousLocalization.map (sectionGradedRingHomInv M)
      (powers_le_comap_sectionGradedRingHomInv M x))
    (RingHom.ext (homogeneousAwayMap_rightInverse M x))
    (RingHom.ext (homogeneousAwayMap_leftInverse M x))

/-- The chart-ring identification is `HomogeneousLocalization.map` along the graded comparison. -/
theorem homogeneousAwayEquiv_apply (x : Stacks.GradedSections.sectionRing M)
    (y : HomogeneousLocalization.Away (Stacks.AmpleFiniteAvoidance.grading M) x) :
    homogeneousAwayEquiv M x y =
      HomogeneousLocalization.map (sectionGradedRingHom M)
        (powers_le_comap_sectionGradedRingHom M x) y :=
  rfl

/-- The chart-ring identification carries a homogeneous fraction to the fraction of the
transported numerator and denominator. -/
theorem homogeneousAwayEquiv_mk (x : Stacks.GradedSections.sectionRing M)
    (c : HomogeneousLocalization.NumDenSameDeg (Stacks.AmpleFiniteAvoidance.grading M)
      (Submonoid.powers x)) :
    homogeneousAwayEquiv M x (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk
        ⟨c.1, ⟨_, GradedRingHom.map_mem (sectionGradedRingHom M) c.2.2⟩,
          ⟨_, GradedRingHom.map_mem (sectionGradedRingHom M) c.3.2⟩,
          powers_le_comap_sectionGradedRingHom M x c.4⟩ :=
  HomogeneousLocalization.map_mk _ _ c

/-- **The ordinary localizations of the two section rings agree**, at the powers of `x`. -/
def awayEquiv (x : Stacks.GradedSections.sectionRing M) :
    Localization.Away x ≃+* Localization.Away (sectionGradedRingHom M x) :=
  IsLocalization.ringEquivOfRingEquiv _ _ (sectionSiteSectionRingEquiv M)
    (powers_map_sectionGradedRingHom M x)

/-- The ordinary transport agrees with the comparison of the section rings on the image of the
structure map. -/
theorem awayEquiv_algebraMap (x : Stacks.GradedSections.sectionRing M)
    (a : Stacks.GradedSections.sectionRing M) :
    awayEquiv M x (algebraMap _ _ a) =
      algebraMap _ (Localization.Away (sectionGradedRingHom M x))
        (sectionSiteSectionRingEquiv M a) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ a

end Scheme

end Stacks.SectionRingProjTheta

end
