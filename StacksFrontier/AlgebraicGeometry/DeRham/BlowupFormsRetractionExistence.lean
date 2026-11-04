module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedRetraction
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsRetractionUniqueness
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsMono
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentrePoleBound
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDerivedLocal
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorTwistedRetraction

/-!
# Existence of the retraction of `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}`

Let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S` and `b : X' ⟶ X` the blowup of
`X` along `Z`, with twisting divisor `𝒟 = Σ_c (c - 1)E_c` (`Stacks.DeRham.blowupTwistDivisor`).
The proof of [Stacks, Tag 0G5J] produces the retraction from two maps

`b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S} ⟶ b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟)`

whose composite is multiplication by the canonical section of `𝒪_{X'}(𝒟)`: the first is the
canonical map, a monomorphism, and the second exists because `ℐ_𝒟 · Ω^a_{X'/S} ⊆ b^*Ω^a_{X/S}`.
Applying `Rb_*`, the composite `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` is
the twist map of [Stacks, Tag 0G5H], an isomorphism; so the canonical map has a retraction.

## Main definitions

* `Stacks.DeRham.blowupFormsTwistRetraction`: the second map
  `Ω^a_{X'/S} ⟶ b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟)`, from the pole bound of 0FUU's
  `Stacks.DeRham.blowupTwistDivisor_poleBound`.

## Main results

* `Stacks.DeRham.blowupFormsPullbackMap_comp_twistRetraction`: the composite of the two maps is
  multiplication by the canonical section.
* `Stacks.DeRham.blowUpFormsDerivedDirectImage_comp_twistRetraction`: after `Rb_*`, the canonical
  map followed by the second map is `Stacks.DeRham.TwistDerived.twistDerivedMap`.
* `Stacks.DeRham.isIso_twistDerivedMap_blowupTwistDivisor`: the twist map is an isomorphism.
* `Stacks.DeRham.existsUnique_blowUpFormsRetraction_of_isIso_homology`: the unique retraction,
  from clause (3) of [Stacks, Tag 0FUU].
* `Stacks.DeRham.existsUnique_blowUpFormsRetraction_of_isIso_twistDerivedMap`: the unique
  retraction, from the invertibility of the twist map and the description of the higher direct
  images.

## References

* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 0G5H](https://stacks.math.columbia.edu/tag/0G5H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f]
  [Smooth (i ≫ f)]

/-- **The second canonical map** `Ω^a_{X'/S} ⟶ b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟)` for the blowup of a
smooth centre and its twisting divisor `𝒟 = Σ_c (c - 1)E_c`: the twisted retraction of the
monomorphism `b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}`
(`Stacks.DeRham.mono_blowupFormsPullbackMap_blowUpToBase`) along the pole bound
`ℐ_𝒟 · Ω^a_{X'/S} ⊆ b^*Ω^a_{X/S}` (`Stacks.DeRham.blowupTwistDivisor_poleBound`). -/
def blowupFormsTwistRetraction (a : ℕ) :
    Scheme.Hom.relativeDifferentialForms (blowUpToBase i.ker ≫ f) a ⟶
      Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback (blowUpToBase i.ker)).obj
          (Scheme.Hom.relativeDifferentialForms f a))
        (Stacks.Divisors.invertibleSheaf' (blowupTwistDivisor f i)) :=
  haveI := mono_blowupFormsPullbackMap_blowUpToBase (f := f) (i := i) a
  Stacks.Divisors.twistedRetraction (blowupTwistDivisor f i) _ (blowupTwistDivisor_poleBound a)

/-- **The composite of the two canonical maps** `b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S} ⟶
b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟)` is multiplication by the canonical section of `𝒪_{X'}(𝒟)`. -/
theorem blowupFormsPullbackMap_comp_twistRetraction (a : ℕ) :
    Scheme.Hom.relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f)
        (𝟙 S) (by simp) a ≫ blowupFormsTwistRetraction f i a =
      Stacks.Divisors.tensorCanonicalSection (blowupTwistDivisor f i)
        ((Scheme.Modules.pullback (blowUpToBase i.ker)).obj
          (Scheme.Hom.relativeDifferentialForms f a)) :=
  have := mono_blowupFormsPullbackMap_blowUpToBase (f := f) (i := i) a
  Stacks.Divisors.comp_twistedRetraction (blowupTwistDivisor f i) _ (blowupTwistDivisor_poleBound a)

/-- **After `Rb_*`, the canonical map followed by the second map is the twist map**
`Ω^a_{X/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` of [Stacks, Tag 0G5H]: both are the unit of
`b^* ⊣ b_*` followed by `Rb_*` of multiplication by the canonical section. -/
theorem blowUpFormsDerivedDirectImage_comp_twistRetraction (a : ℕ) :
    blowUpFormsDerivedDirectImage f i.ker (a : ℤ) ≫
        (schemeDerivedPushforward (blowUpToBase i.ker)).map
          ((DerivedCategory.singleFunctor _ 0).map (blowupFormsTwistRetraction f i a)) =
      TwistDerived.twistDerivedMap (blowUpToBase i.ker) (blowupTwistDivisor f i)
        (Scheme.Hom.relativeDifferentialForms f a) := by
  rw [blowUpFormsDerivedDirectImage, formsDerivedDirectImage_eq, TwistDerived.twistDerivedMap,
    TwistDerived.derivedPullbackUnit, Scheme.Hom.formsDirectImageComparison, Functor.map_comp,
    Category.assoc, Category.assoc,
    reassoc_of% (TwistDerived.pushforwardSingleToDerived_naturality (blowUpToBase i.ker)
      (Scheme.Hom.relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f)
        (𝟙 S) (by simp) a)),
    ← Functor.map_comp, ← Functor.map_comp, blowupFormsPullbackMap_comp_twistRetraction,
    Category.assoc]

/-- **The twist map of the blowup of a smooth centre is an isomorphism**:
`Ω^a_{X/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` for the twisting divisor `𝒟 = Σ_c (c - 1)E_c`,
when `Z` has empty interior in `X`.  This is [Stacks, Tag 0G5H] étale locally
(`Stacks.DeRham.TwistDerived.isIso_twistDerivedMap_forms_of_etaleLocal`): off the centre `𝒟` is
empty, and on a chart it is the pullback of `(n - 1)E`. -/
theorem isIso_twistDerivedMap_blowupTwistDivisor (hint : interior (Set.range i.base) = ∅)
    (a : ℕ) :
    IsIso (TwistDerived.twistDerivedMap (blowUpToBase i.ker) (blowupTwistDivisor f i)
      (Scheme.Hom.relativeDifferentialForms f a)) := by
  refine TwistDerived.isIso_twistDerivedMap_forms_of_etaleLocal f i hint _ a
    (comap_blowupTwistDivisor_of_disjoint f i _ ?_) fun z => ?_
  · refine eq_bot_iff.2 fun w hw => ?_
    change i.base w ∉ (i.ker.support : Set X) at hw
    rw [Scheme.Hom.support_ker] at hw
    exact hw (subset_closure ⟨w, rfl⟩)
  · obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
    exact ⟨c, hzc, c.comap_blowupTwistDivisor⟩

/-- **The higher direct images are pushed forward from the centre**, granted clause (3) of
[Stacks, Tag 0FUU]: for `q ≥ 1`,
`R^qb_*Ω^a_{X'/S} ≅ H^q(i_*Rp_*Ω^a_{E/S}) ≅ i_*R^qp_*Ω^a_{E/S}`. -/
theorem exists_homology_blowUpFormsObj_iso_pushforward (a : ℕ)
    (h3 : ∀ q : ℤ, 1 ≤ q → IsIso ((DerivedCategory.homologyFunctor X.Modules q).map
      (blowupFormsDerivedComparison f i (a : ℤ))))
    (q : ℤ) (hq : 1 ≤ q) : ∃ G : Z.Modules,
      Nonempty ((DerivedCategory.homologyFunctor X.Modules q).obj
        (blowUpFormsObj f i.ker (a : ℤ)) ≅ (Scheme.Modules.pushforward i).obj G) :=
  have := h3 q hq
  ⟨_, ⟨asIso ((DerivedCategory.homologyFunctor X.Modules q).map
      (blowupFormsDerivedComparison f i (a : ℤ))) ≪≫
    derivedPushforwardHomologyIsoOfIsClosedImmersion i q _⟩⟩

/-- **[Stacks, Tag 0G5J] from its two remaining inputs.**  If `Z` has empty interior in `X`, the
canonical map `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` has exactly one retraction in `D(𝒪_X)`, given

* `hiso`: the twist map `Ω^a_{X/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` is invertible (Tag 0G5H,
  étale locally);
* `h3`: the higher direct images `R^qb_*Ω^a_{X'/S}`, `q ≥ 1`, are pushed forward from the centre
  (Tag 0FUU (3)).

Existence is `v ≫ (u ≫ v)⁻¹` for `v` the image under `Rb_*` of the second canonical map, and
uniqueness is `Stacks.DeRham.subsingleton_hom_cone_blowUpForms_of_homology`. -/
theorem existsUnique_blowUpFormsRetraction_of_isIso_twistDerivedMap
    (hint : interior (Set.range i.base) = ∅) (a : ℕ)
    (hiso : IsIso (TwistDerived.twistDerivedMap (blowUpToBase i.ker) (blowupTwistDivisor f i)
        (Scheme.Hom.relativeDifferentialForms f a)))
    (h3 : ∀ q : ℤ, 1 ≤ q → ∃ G : Z.Modules,
      Nonempty ((DerivedCategory.homologyFunctor X.Modules q).obj
        (blowUpFormsObj f i.ker (a : ℤ)) ≅ (Scheme.Modules.pushforward i).obj G)) :
    ∃! r : blowUpFormsObj f i.ker (a : ℤ) ⟶ formsSingle f (a : ℤ),
      blowUpFormsDerivedDirectImage f i.ker (a : ℤ) ≫ r = 𝟙 (formsSingle f (a : ℤ)) := by
  obtain ⟨C, p, w, hT⟩ :=
    distinguished_cocone_triangle (blowUpFormsDerivedDirectImage f i.ker (a : ℤ))
  have hsub := subsingleton_hom_cone_blowUpForms_of_homology f i hint a h3 hT
  refine Retraction.existsUnique_comp_eq_id hT (fun g => Subsingleton.elim g 0)
    ((schemeDerivedPushforward (blowUpToBase i.ker)).map
      ((DerivedCategory.singleFunctor _ 0).map (blowupFormsTwistRetraction f i a))) ?_
  rw [blowUpFormsDerivedDirectImage_comp_twistRetraction]
  exact hiso

/-- **[Stacks, Tag 0G5J] from clause (3) of [Stacks, Tag 0FUU].**  If `Z` has empty interior in
`X` and `R^qb_*Ω^a_{X'/S} ⟶ H^q(i_*Rp_*Ω^a_{E/S})` is invertible for `q ≥ 1`, the canonical map
`Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` has exactly one retraction in `D(𝒪_X)`. -/
theorem existsUnique_blowUpFormsRetraction_of_isIso_homology
    (hint : interior (Set.range i.base) = ∅) (a : ℕ)
    (h3 : ∀ q : ℤ, 1 ≤ q → IsIso ((DerivedCategory.homologyFunctor X.Modules q).map
      (blowupFormsDerivedComparison f i (a : ℤ)))) :
    ∃! r : blowUpFormsObj f i.ker (a : ℤ) ⟶ formsSingle f (a : ℤ),
      blowUpFormsDerivedDirectImage f i.ker (a : ℤ) ≫ r = 𝟙 (formsSingle f (a : ℤ)) :=
  existsUnique_blowUpFormsRetraction_of_isIso_twistDerivedMap f i hint a
    (isIso_twistDerivedMap_blowupTwistDivisor f i hint a)
    (exists_homology_blowUpFormsObj_iso_pushforward f i a h3)

end Stacks.DeRham

end
