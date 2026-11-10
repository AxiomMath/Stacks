module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotient

/-!
# The closed immersion of `X` into the thickened quotient `X' = U'/R'`

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
over `S` by a quasi-coherent ideal (the data of Stacks 05ZT), `X = U/R` an étale presentation,
and suppose the chart thickenings `U'`, `R'` lie in the site. The inclusions `U ⟶ U'` and
`R ⟶ R'` form a morphism of étale equivalence relations whose square on the source maps is
cartesian (`isPullback_chartRealizedSchemeMap`), so they induce a morphism `X = U/R ⟶ U'/R' = X'`
whose base change along the surjective étale quotient map `U' ⟶ X'` is `U ⟶ U'`
(Stacks 07S3). As `U ⟶ U'` is a closed immersion, so is `X ⟶ X'`: closed immersions descend
along surjective étale morphisms. This is the third paragraph of the proof of Stacks 05ZT:
"The morphism `U ⟶ U'` induces a morphism `X ⟶ X'` ... a closed immersion".

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.chartInclusionOver`: `U ⟶ U'` in the site.
* `AlgebraicGeometry.Space.SquareZeroExtension.presentationQuotientIso`: `U/R ≅ X`.
* `AlgebraicGeometry.Space.SquareZeroExtension.thickeningImmersion`: `X ⟶ X'`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.isPullback_thickeningImmersion`: `U = X ×_{X'} U'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.isClosedImmersion_thickeningImmersion`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

open AlgebraicGeometry in
/-- **First-order thickenings of schemes satisfy fppf descent**: Stacks 0BPF (fpqc locality on
the target, `Stacks.Thickenings.isFirstOrderThickening_isLocalAtTarget_fpqc`) read along a single
surjective flat morphism, then passed from quasi-compact to locally finitely presented morphisms
by Zariski locality on the target. -/
theorem _root_.Stacks.Thickenings.isFirstOrderThickening_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (@Stacks.Thickenings.IsFirstOrderThickening : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  have hri : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsFirstOrderThickening : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.DescendsAlong
      (@Stacks.Thickenings.IsFirstOrderThickening : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    refine ⟨fun {A X' Y' Z} {fst snd f g} h hf hfst ↦ ?_⟩
    obtain ⟨⟨_, _⟩, _⟩ := hf
    refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
      (P := @Stacks.Thickenings.IsFirstOrderThickening) (K := Scheme.fpqcPrecoverage)
      f.singleton_mem_fpqcPrecoverage).2 ?_
    rintro U g' _ ⟨⟩
    rw [← h.flip.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hfst
  have := Stacks.Thickenings.isFirstOrderThickening_isZariskiLocalAtTarget.{u}
  exact AlgebraicGeometry.descendsAlong_fppf_of _

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **The inclusion `U ⟶ U'` of an étale chart into its thickening**, as a morphism of the big
fppf site of `S`, when the site contains `U'`. -/
noncomputable def chartInclusionOver (U : SmallEtale B S hS X.1)
    (hU : B.Contains (E.chartRealizedScheme U)) :
    U.obj.left ⟶ E.chartRealizedSchemeOver hS U hU :=
  BigFppfOver.homMk B S hS hU _ (E.chartInclusion U)
    (E.chartInclusion_comp_chartRealizedSchemeToBaseScheme U)

/-- The underlying morphism of schemes of `chartInclusionOver` is `chartInclusion`. -/
theorem toScheme_map_chartInclusionOver (U : SmallEtale B S hS X.1)
    (hU : B.Contains (E.chartRealizedScheme U)) :
    (BigFppfOver.toScheme B S hS).map (E.chartInclusionOver U hU) = E.chartInclusion U :=
  BigFppfOver.toScheme_map_homMk B S hS hU _ _ _

/-- `U ⟶ U'` is natural in the chart. -/
theorem chartInclusionOver_comp_chartRealizedSchemeOverMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (hU : B.Contains (E.chartRealizedScheme U)) (hV : B.Contains (E.chartRealizedScheme V)) :
    E.chartInclusionOver V hV ≫ E.chartRealizedSchemeOverMap hS g hU hV =
      (SmallEtale.toOver B S hS X.1).map g ≫ E.chartInclusionOver U hU :=
  BigFppfOver.map_toScheme_injective B S hS (by
    change (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
    rw [Functor.map_comp, Functor.map_comp, toScheme_map_chartInclusionOver,
      toScheme_map_chartInclusionOver, toScheme_map_chartRealizedSchemeOverMap]
    exact E.chartInclusion_comp_chartRealizedSchemeMap g)

variable (P : Presentation B S hS X.obj X.property)
  (hU : B.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- The relation `R ⇉ U` of an étale presentation is an étale equivalence relation. -/
instance : Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS P.source P.target) :=
  P.isEtaleEquivalenceRelation

/-- **`X ≅ U/R`**: an algebraic space is the quotient sheaf of the relation of any of its étale
presentations, compatibly with the two maps from `U`. -/
noncomputable def presentationQuotientIso :
    letI := hasSheafify_bigFppfOver B S hS
    (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (relation B S hS P.source P.target)).obj ≅ X.1 :=
  letI _ := hasSheafify_bigFppfOver B S hS
  Classical.choose (exists_quotientSheaf_iso B S hS (hX := X.property) P.toSpace P.source
    P.target P.isPullback P.surjective P.etale)

/-- The quotient map `U ⟶ U/R` followed by `U/R ≅ X` is the presentation map `U ⟶ X`. -/
theorem quotientMap_comp_presentationQuotientIso_hom :
    letI := hasSheafify_bigFppfOver B S hS
    Space.quotientMap B S hS P.source P.target ≫ (presentationQuotientIso P).hom = P.toSpace :=
  let _ := hasSheafify_bigFppfOver B S hS
  Classical.choose_spec (exists_quotientSheaf_iso B S hS (hX := X.property) P.toSpace P.source
    P.target P.isPullback P.surjective P.etale)

/-- The inclusions `R ⟶ R'` and `U ⟶ U'` commute with the source maps `R ⟶ U` and
`R' ⟶ U'`. -/
theorem presentation_source_comp_chartInclusionOver :
    E.chartInclusionOver (presentationRelationChart P) hR ≫
        E.chartRealizedSchemeOverMap hS (presentationRelationSourceHom P) hU hR =
      P.source ≫ E.chartInclusionOver (presentationChart P) hU :=
  E.chartInclusionOver_comp_chartRealizedSchemeOverMap _ hU hR

/-- The inclusions `R ⟶ R'` and `U ⟶ U'` commute with the target maps `R ⟶ U` and
`R' ⟶ U'`. -/
theorem presentation_target_comp_chartInclusionOver :
    E.chartInclusionOver (presentationRelationChart P) hR ≫
        E.chartRealizedSchemeOverMap hS (presentationRelationTargetHom P) hU hR =
      P.target ≫ E.chartInclusionOver (presentationChart P) hU :=
  E.chartInclusionOver_comp_chartRealizedSchemeOverMap _ hU hR

/-- The square of schemes formed by `R ⟶ R'`, `U ⟶ U'` and the source maps `R ⟶ U`,
`R' ⟶ U'` is cartesian. -/
theorem isPullback_presentation_chartInclusion :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map (E.chartInclusionOver (presentationRelationChart P) hR))
      ((BigFppfOver.toScheme B S hS).map P.source)
      ((BigFppfOver.toScheme B S hS).map
        (E.chartRealizedSchemeOverMap hS (presentationRelationSourceHom P) hU hR))
      ((BigFppfOver.toScheme B S hS).map (E.chartInclusionOver (presentationChart P) hU)) :=
  E.isPullback_chartRealizedSchemeMap (presentationRelationSourceHom P)

/-- **The morphism `X ⟶ X'`** induced by the inclusions `U ⟶ U'` and `R ⟶ R'`. -/
noncomputable def thickeningImmersion : X ⟶ E.thickeningQuotient hS P hU hR :=
  letI _ := hasSheafify_bigFppfOver B S hS
  ObjectProperty.homMk ((presentationQuotientIso P).inv ≫
    quotientHom B S hS P.source P.target _ _ (E.chartInclusionOver _ hR)
      (E.chartInclusionOver _ hU) (E.presentation_source_comp_chartInclusionOver P hU hR)
      (E.presentation_target_comp_chartInclusionOver P hU hR))

/-- The quotient map `U' ⟶ X'`. -/
noncomputable abbrev thickeningQuotientMap :
    yoneda.obj (E.chartRealizedSchemeOver hS (presentationChart P) hU) ⟶
      (E.thickeningQuotient hS P hU hR).1 :=
  letI _ := hasSheafify_bigFppfOver B S hS
  Space.quotientMap B S hS (E.chartRealizedSchemeOverMap hS (presentationRelationSourceHom P) hU hR)
    (E.chartRealizedSchemeOverMap hS (presentationRelationTargetHom P) hU hR)

/-- **`U = X ×_{X'} U'`** (Stacks 07S3): the base change of `X ⟶ X'` along the quotient map
`U' ⟶ X'` is the inclusion `U ⟶ U'`. -/
theorem isPullback_thickeningImmersion :
    IsPullback P.toSpace (yoneda.map (E.chartInclusionOver (presentationChart P) hU))
      (E.thickeningImmersion P hU hR).hom (E.thickeningQuotientMap P hU hR) := by
  let _ := hasSheafify_bigFppfOver B S hS
  have sq := isPullback_quotientMap B S hS P.source P.target _ _ (E.chartInclusionOver _ hR)
    (E.chartInclusionOver _ hU) (E.presentation_source_comp_chartInclusionOver P hU hR)
    (E.presentation_target_comp_chartInclusionOver P hU hR)
    (E.isPullback_presentation_chartInclusion P hU hR)
  refine sq.of_iso (Iso.refl _) (presentationQuotientIso P) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    exact (quotientMap_comp_presentationQuotientIso_hom P)
  · simp
  · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- If a property of schemes respects isomorphisms and holds (as a presheaf property) for one
leg of a cartesian square, it holds for the corresponding leg of the chosen pullback. -/
private theorem presheaf_pullback_snd_of_isPullback (Q : MorphismProperty Scheme.{u})
    [Q.RespectsIso] {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fst : F ⟶ G} {snd : F ⟶ H}
    {f : G ⟶ K} {g : H ⟶ K} (sq : IsPullback fst snd f g)
    (h : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf snd) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f g) := by
  have := MorphismProperty.RespectsIso.inverseImage Q (BigFppfOver.toScheme B S hS)
  rw [← sq.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp _ _ _ h

/-- **`X ⟶ X'` is a closed immersion**: its base change along the surjective étale quotient
map `U' ⟶ X'` is the closed immersion `U ⟶ U'`, and closed immersions descend effectively
along surjective étale morphisms. -/
theorem isClosedImmersion_thickeningImmersion :
    IsClosedImmersion B S hS (E.thickeningImmersion P hU hR).hom := by
  let _ := hasSheafify_bigFppfOver B S hS
  have hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have sq := E.isPullback_thickeningImmersion P hU hR
  have hci : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (E.chartInclusionOver (presentationChart P) hU)) :=
    (presheaf_yoneda_map_iff B S hS inferInstance _).mpr
      (E.isFirstOrderThickening_chartInclusion (presentationChart P)).1
  have hV := presheaf_pullback_snd_of_isPullback _ sq hci
  exact presheaf_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) X.property.isSheaf
    (E.thickeningQuotient hS P hU hR).property.isSheaf
    (quotientMap_surjective_unconditional B S hS _ _) (quotientMap_etale_unconditional B S hS _ _)
    hV

/-- **`X ⟶ X'` is a first-order thickening on every represented base change**: its base change
along the surjective étale quotient map `U' ⟶ X'` is the first-order thickening `U ⟶ U'`, and
first-order thickenings descend effectively along surjective étale morphisms (they are closed
immersions, and the first-order condition descends by Stacks 0BPF). -/
theorem presheaf_isFirstOrderThickening_thickeningImmersion :
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsFirstOrderThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (E.thickeningImmersion P hU hR).hom := by
  let _ := hasSheafify_bigFppfOver B S hS
  have hri : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsFirstOrderThickening.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := Stacks.Thickenings.isFirstOrderThickening_descendsAlong_fppf.{u}
  have hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@Stacks.Thickenings.IsFirstOrderThickening.{u} : MorphismProperty Scheme.{u}) :=
    isEffectiveDescentAlongSurjectiveEtale_of_le
      (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) (fun _ _ _ h ↦ h.1)
  have sq := E.isPullback_thickeningImmersion P hU hR
  have hfo : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsFirstOrderThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (E.chartInclusionOver (presentationChart P) hU)) :=
    (presheaf_yoneda_map_iff B S hS inferInstance _).mpr
      (E.isFirstOrderThickening_chartInclusion (presentationChart P))
  have hV := presheaf_pullback_snd_of_isPullback _ sq hfo
  exact presheaf_of_surjectiveEtaleChart hdesc X.property.isSheaf
    (E.thickeningQuotient hS P hU hR).property.isSheaf
    (quotientMap_surjective_unconditional B S hS _ _) (quotientMap_etale_unconditional B S hS _ _)
    hV

/-- **The range of `X ⟶ X'` is a thickening of `X'`**: `X ⟶ X'` is a closed immersion, and it
is surjective on points because each of its represented base changes is a thickening. -/
theorem isThickening_range_thickeningImmersion :
    IsThickening B S hS (E.thickeningQuotient hS P hU hR)
      (Subfunctor.range (E.thickeningImmersion P hU hR).hom) :=
  isThickening_range_of_isClosedImmersion_isSurjective B S hS X.property _ _
    (E.isClosedImmersion_thickeningImmersion P hU hR)
    (isSurjective_of_presheafSurjective B S hS _
      (MorphismProperty.relative_monotone
        (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
          (fun _ _ _ h ↦ ⟨h.isThickening.2⟩)) _
        (E.presheaf_isFirstOrderThickening_thickeningImmersion P hU hR)))

/-- **`X ⊂ X'` is a first-order thickening** (Stacks 05ZK, part (2)): the range of `X ⟶ X'` is
a thickening, and at every étale chart `W` of `X'` its defining ideal is the kernel of the
represented base change of `X ⟶ X'` to `W`, a first-order thickening of schemes. -/
theorem isFirstOrderThickening_range_thickeningImmersion :
    IsFirstOrderThickening B S hS (E.thickeningQuotient hS P hU hR)
      (Subfunctor.range (E.thickeningImmersion P hU hR).hom) := by
  classical
  have hth := E.isThickening_range_thickeningImmersion P hU hR
  have hmono : Mono (E.thickeningImmersion P hU hR).hom :=
    mono_of_isClosedImmersion B S hS _ (E.isClosedImmersion_thickeningImmersion P hU hR)
  have hQ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsFirstOrderThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (Subfunctor.range (E.thickeningImmersion P hU hR).hom).ι := by
    have hri : MorphismProperty.RespectsIso
        (@Stacks.Thickenings.IsFirstOrderThickening.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have := MorphismProperty.RespectsIso.inverseImage
      (@Stacks.Thickenings.IsFirstOrderThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    have heq : inv (Subfunctor.toRange (E.thickeningImmersion P hU hR).hom) ≫
        (E.thickeningImmersion P hU hR).hom =
          (Subfunctor.range (E.thickeningImmersion P hU hR).hom).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
    rw [← heq]
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (E.presheaf_isFirstOrderThickening_thickeningImmersion P hU hR)
  refine ⟨hth, fun W ↦ ?_⟩
  have hn : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (hth.1.2.rep.snd W.1.hom)) :=
    hQ.property_snd _
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hth.1.2.rep.snd W.1.hom)) := by
    have hci := hn.1
    infer_instance
  rw [definingIdealAt_eq_ker B S hS (E.thickeningQuotient hS P hU hR)
    ⟨Subfunctor.range (E.thickeningImmersion P hU hR).hom, hth.1⟩ W, Scheme.Γ_map_op]
  exact Scheme.ker_appTop_pow_eq_bot _ hqc hn.2

end AlgebraicGeometry.Space.SquareZeroExtension

end
