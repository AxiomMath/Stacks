module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterLimitGermDeathOfInputs

/-!
# The stalk transition along a refinement as a restriction (Stacks 03Q9), as a statement

Let `π : Y' ⟶ Y` be a refinement of proper models of `η = Spec (Frac B)`, `s : Spec Ω ⟶ Y'` a
geometric point with `Ω` algebraically closed and `s₀ = s ≫ π`. By Stacks 03Q9
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`)
the stalk of `R^q j_* F` at `s₀` is `H^q(P_Y, F|)`, `P_Y = η ×_Y Spec 𝒪^{sh}_{Y, s₀}`, and likewise
on `Y'`. A local homomorphism `m : 𝒪^{sh}_{Y, s₀} → 𝒪^{sh}_{Y', s}` lying over `π` and compatible
with the geometric points gives `ρ_m : P_{Y'} ⟶ P_Y`
(`Scheme.ZariskiRiemann.ProperModel.Refinement.strictHenselizationBaseChangeMap`); the
compatibility clause of 03Q9 says that under the two isomorphisms the stalk transition
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition` is restriction
along `ρ_m`. This file states this compatibility in kernel form:
`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction`.

It is the input from the comparison of the two base change maps (the unbounded
`etaleAbelianInverseImageRightDerivedDirectImageBaseChange` against the bounded
`higherBaseChangeMapAb`) and the stalk formula for the non-cartesian square `𝟙 ≫ j = j' ≫ π`, or
from a direct proof of the compatibility.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.geometricPointOf`: a morphism from the spectrum of an
  algebraically closed field, as a geometric point.
* `Scheme.ZariskiRiemann.ProperModel.Refinement.strictHenselizationBaseChangeMap`: the morphism
  `P_{Y'} ⟶ P_Y` of a map of étale local rings over `π`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction`: the
  statement.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

/-- A morphism `Spec Ω ⟶ X` from the spectrum of an algebraically closed field, as a geometric
point of `X`. -/
abbrev geometricPointOf {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) : GeometricPoint X where
  residueField := Ω
  hom := s

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B]

/-- **The morphism `P_{Y'} ⟶ P_Y` of a map of étale local rings.** For a refinement `π : Y' ⟶ Y`,
geometric points `s₀` of `Y` and `s` of `Y'` and a ring map
`m : 𝒪^{sh}_{Y, s₀} → 𝒪^{sh}_{Y', s}` with `Spec 𝒪^{sh}_{Y', s} ⟶ Y' ⟶ Y` equal to
`Spec 𝒪^{sh}_{Y', s} ⟶ Spec 𝒪^{sh}_{Y, s₀} ⟶ Y`, the morphism
`η ×_{Y'} Spec 𝒪^{sh}_{Y', s} ⟶ η ×_Y Spec 𝒪^{sh}_{Y, s₀}` given by the identity of `η` and
`Spec m` (the strict henselizations taken in the big étale sites
`AlgebraicGeometry.BigEtaleSite.containing Y` and `… Y'`, as in
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`). -/
def Refinement.strictHenselizationBaseChangeMap {M' M : ProperModel B} (φ : Refinement M' M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s₀ : Spec (.of Ω) ⟶ M.Y) (s : Spec (.of Ω) ⟶ M'.Y)
    (m : ↥(etaleLocalRing (BigEtaleSite.containing M.Y) M.Y (BigEtaleSite.contains_containing M.Y)
        (geometricPointOf s₀)) →+*
      ↥(etaleLocalRing (BigEtaleSite.containing M'.Y) M'.Y
        (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s)))
    (hm : strictHenselizationToBase (BigEtaleSite.containing M'.Y) M'.Y
        (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s) ≫ φ.π =
      Spec.map (CommRingCat.ofHom m) ≫ strictHenselizationToBase (BigEtaleSite.containing M.Y)
        M.Y (BigEtaleSite.contains_containing M.Y) (geometricPointOf s₀)) :
    strictHenselizationBaseChange (BigEtaleSite.containing M'.Y)
        (BigEtaleSite.contains_containing M'.Y) M'.j (geometricPointOf s) ⟶
      strictHenselizationBaseChange (BigEtaleSite.containing M.Y)
        (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf s₀) :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom m)) φ.π
    (by rw [Category.id_comp, φ.fac]) hm

end ProperModel

/-- **The stalk transition is restriction along the strict henselizations** (Stacks 03Q9,
compatibility clause, in kernel form). Let `M` be a proper model, `s₀ : Spec Ω ⟶ Y` a geometric
point with `Ω` algebraically closed and `γ` a germ of `R^q j_* F` at `s₀`. There is a class
`ξ ∈ H^q(P_Y, F|)` on `P_Y = η ×_Y Spec 𝒪^{sh}_{Y, s₀}` such that for every refinement
`π : Y' ⟶ Y`, geometric point `s` of `Y'` with `s₀ = s ≫ π`, and ring map
`m : 𝒪^{sh}_{Y, s₀} → 𝒪^{sh}_{Y', s}` lying over `π` and compatible with the canonical geometric
points of the strict henselizations: if `ξ` dies under restriction along `ρ_m : P_{Y'} ⟶ P_Y`,
then `γ` dies under the stalk transition at `s`.

In the source: `ξ` is the image of `γ` under the 03Q9 isomorphism
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`;
the two conditions on `m` determine it (Stacks 04GU: it is
`AlgebraicGeometry.etaleLocalRingHom`), and the 03Q9 isomorphisms carry the stalk of the base
change map of the square `𝟙 ≫ j = j' ≫ π` to restriction along `ρ_m`; the isomorphism on `Y'` is
injective. -/
def StalkTransitionStrictHenselizationRestriction : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B]
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (M : ProperModel B) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s₀ : Spec (.of Ω) ⟶ M.Y)
    (γ : (smallEtaleStalkAb s₀).obj (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)),
    ∃ ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (strictHenselizationBaseChangeToSource (BigEtaleSite.containing M.Y)
          (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf s₀))).obj F) q,
      ∀ (M' : ProperModel B) (φ : ProperModel.Refinement M' M) (s : Spec (.of Ω) ⟶ M'.Y)
        (h : s₀ = s ≫ φ.π)
        (m : ↥(etaleLocalRing (BigEtaleSite.containing M.Y) M.Y
            (BigEtaleSite.contains_containing M.Y) (geometricPointOf s₀)) →+*
          ↥(etaleLocalRing (BigEtaleSite.containing M'.Y) M'.Y
            (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s)))
        (hm : strictHenselizationToBase (BigEtaleSite.containing M'.Y) M'.Y
            (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s) ≫ φ.π =
          Spec.map (CommRingCat.ofHom m) ≫ strictHenselizationToBase
            (BigEtaleSite.containing M.Y) M.Y (BigEtaleSite.contains_containing M.Y)
            (geometricPointOf s₀)),
        geometricPointToStrictHenselization (BigEtaleSite.containing M'.Y) M'.Y
            (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s) ≫
            Spec.map (CommRingCat.ofHom m) =
          geometricPointToStrictHenselization (BigEtaleSite.containing M.Y) M.Y
            (BigEtaleSite.contains_containing M.Y) (geometricPointOf s₀) →
        etaleCohomologyRestrictionMap.{u, 0, u + 1}
            (φ.strictHenselizationBaseChangeMap s₀ s m hm) _ q ξ = 0 →
          (eqToHom (by rw [h]) ≫ φ.stalkTransition F q s) γ = 0

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
