module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bijection between sections of `𝐏(ℰ) ⟶ X` and invertible quotients commutes with base change

Let `g : X ⟶ Y` be a morphism of schemes and `E` a quasi-coherent `𝒪_Y`-module. Tag 0B3V's
bijection `Stacks.RelativeProj.projectiveBundleSectionsEquiv` exists on both sides: between the
sections of `𝐏(E) ⟶ Y` and the invertible quotients of `E`, and between the sections of
`𝐏(g^*E) ⟶ X` and the invertible quotients of `g^*E`. This file proves that the two bijections
form a commuting square with the two base-change maps: `Stacks.RelativeProj.sectionBaseChange` on
sections and `Stacks.ProjectiveBundleQuotients.baseChangeClass` on classes of quotients.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.sectionsMap_eq_of_univ_comp`: two tautological data
  whose universal quotients agree up to an isomorphism of twists have the same `sectionsMap`.
* `Stacks.RelativeProj.projectiveBundleSectionsEquiv_sectionBaseChange`: **the bijection of
  [Stacks, Tag 0B3V] is compatible with base change**, stated for the canonical bijections of
  both projective bundles.

## Implementation notes

`Stacks.RelativeProj.sectionsMap_sectionBaseChange` proves the square for an arbitrary datum `D`
on `𝐏(E)` and the *base-changed* datum `D.baseChange` on `𝐏(g^*E)`. The canonical datum
`Stacks.RelativeProj.tautologicalDatum` of `𝐏(g^*E)` is not that datum on the nose, but its
universal quotient is the base-changed one followed by
`Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso`
(`RelativeProj.tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom`), so
the two data classify the same quotients.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

namespace TautologicalDatum

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

/-- **Two tautological data with the same universal quotient classify the same quotients**: if
the universal quotient of `D` followed by an isomorphism of twists is that of `D'`, the maps from
sections to classes of invertible quotients agree. -/
theorem sectionsMap_eq_of_univ_comp (D D' : TautologicalDatum X F) (φ : D.twist ≅ D'.twist)
    (h : D.univ ≫ φ.hom = D'.univ) : D.sectionsMap = D'.sectionsMap := by
  funext σ
  refine Quotient.sound ⟨(Scheme.Modules.pullback σ.1).mapIso φ, ?_⟩
  change (D.pullbackQuotientMap σ.1 σ.2) ≫ (Scheme.Modules.pullback σ.1).map φ.hom =
    D'.pullbackQuotientMap σ.1 σ.2
  simp only [pullbackQuotientMap, Category.assoc, ← Functor.map_comp, h]

end TautologicalDatum

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]

/-- The base change of the canonical tautological datum and the canonical tautological datum of
the base-changed bundle classify the same quotients. -/
theorem sectionsMap_baseChange_tautologicalDatum :
    ((tautologicalDatum E).baseChange g E _ (Iso.refl _)).sectionsMap =
      (tautologicalDatum ((Scheme.Modules.pullback g).obj E)).sectionsMap :=
  TautologicalDatum.sectionsMap_eq_of_univ_comp _ _
    (tautologicalDatumTwistBaseChangeIso g E _ (Iso.refl _))
    (tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom g E _
      (Iso.refl _))

/-- **[Stacks, Tag 0B3V]: the bijection between sections of `𝐏(ℰ) ⟶ X` and invertible quotients
of `ℰ` is compatible with base change.** For a morphism `g : X ⟶ Y` and a quasi-coherent `E` on
`Y`, the canonical bijection of `𝐏(g^*E) ⟶ X` sends the base change of a section `σ` of
`𝐏(E) ⟶ Y` to the base change of the class of invertible quotients that the canonical bijection
of `𝐏(E) ⟶ Y` assigns to `σ`. No hypothesis on `g`, on `E` beyond quasi-coherence, or on the
schemes. -/
@[ega "II 4.2.10" "special case"]
theorem projectiveBundleSectionsEquiv_sectionBaseChange (σ : Y ⟶ projectiveBundle Y E)
    (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) :
    projectiveBundleSectionsEquiv
        ⟨sectionBaseChange g E σ hσ, sectionBaseChange_comp_projectiveBundleToBase g E σ hσ⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass g (Iso.refl _)
        (projectiveBundleSectionsEquiv ⟨σ, hσ⟩) := by
  have h := sectionsMap_sectionBaseChange g E (tautologicalDatum E) σ hσ
  rw [sectionsMap_baseChange_tautologicalDatum] at h
  exact h

end Stacks.RelativeProj

end
