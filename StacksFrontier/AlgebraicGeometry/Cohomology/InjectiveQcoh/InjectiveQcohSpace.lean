module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Artinian.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Injective quasi-coherent modules on a Noetherian algebraic space

Let `X` be a Noetherian algebraic space over a scheme `S`.  This file shows that every injective
object `J` of the category `QCoh(𝒪_X)` of quasi-coherent modules on the small étale site of `X`
is a direct summand of a filtered colimit of quasi-coherent modules of the form
`(Z_i ⟶ X)_* 𝒢_i`, where `Z_i` is the spectrum of an Artinian ring and `𝒢_i` is a coherent
module on `Z_i`.

The route is the one of the source.  A Noetherian algebraic space is quasi-compact, so it has a
surjective étale chart `j : U ⟶ X` whose source is an affine scheme, and `U` is then a
Noetherian affine scheme because local Noetherianity is an étale-local property of schemes.
The inverse image `j^*J` is again quasi-coherent, étale inverse image preserving
quasi-coherence unconditionally; embedding it into an injective object `J'` of `QCoh(𝒪_U)` and
transposing along the adjunction `j^* ⊣ j_*` gives a morphism `J ⟶ j_*J'`.  That morphism is a
monomorphism because `j^*` is faithful, hence reflects monomorphisms — faithfulness of `j^*`
along a surjective étale chart being `AlgebraicGeometry.Space.faithful_modulePullback` — and
since `J` is injective the monomorphism splits: `J` is a *retract* of `j_*J'`.  This retraction
is the only source of "direct summand", and it is what distinguishes the statement here from
its affine counterpart.  Finally `J'` is a filtered colimit of Artinian
direct images over `U`, and `j_*` carries that colimit to a filtered colimit over `X` whose terms
are Artinian direct images along the composites `Z_i ⟶ U ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.IsArtinianPushforward`: a module on an algebraic space is the direct
  image of a coherent module along a morphism whose source is the spectrum of an Artinian ring,
  that ring being read off as the global sections of an affine object of the site.
* `AlgebraicGeometry.Space.chartQuasicoherentPushforward`: the direct image along a morphism,
  restricted to the quasi-coherent modules, granted that it preserves quasi-coherence.
* `AlgebraicGeometry.Space.chartQuasicoherentAdjunction`: the adjunction of Stacks 03LU along an
  étale morphism, restricted to the quasi-coherent modules.
* `AlgebraicGeometry.Space.ChartArtinianPresentation`: the four inputs that the argument needs at
  the chart and that are carried as hypotheses; see the implementation notes.

## Main results

* `AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract`: the
  reduction of Stacks 09TJ to `ChartArtinianPresentation` at the affine surjective étale chart.
  Stacks 09TJ itself, with every chart input proved, is
  `AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract_of_isNoetherian`
  in `UnconditionalArtinianPresentation.lean` of this directory.
* `AlgebraicGeometry.Space.isArtinianPushforward_modulePushforward`: an Artinian direct image
  stays one after a further direct image, by the composition comparison of Stacks 03LU.
* `AlgebraicGeometry.Space.faithful_quasicoherentPullbackOfIsEtale`: the inverse image of
  quasi-coherent modules along an étale morphism is faithful as soon as the ambient inverse
  image of modules is.
* `AlgebraicGeometry.Space.nonempty_retract_chartQuasicoherentPushforward`: an injective
  quasi-coherent module is a retract of the direct image of an injective quasi-coherent module
  from the chart.

## Implementation notes

Everything is at module universe equal to the universe `u` of the schemes, which is the universe
at which the direct image `AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU and its
adjunction are available, and also the universe of the affine statement that the chart hypothesis
transports.

A scheme of the site is read as an algebraic space by `AlgebraicGeometry.schemeSpace`, the one
such reading in the library; it is the auxiliary of Stacks 04U8, and it is what the
unconditional faithfulness of the inverse image along a surjective étale chart,
`AlgebraicGeometry.Space.faithful_modulePullback`, is stated with — that result is what proves
the key monomorphy.

The category `QCoh(𝒪_X)` of Stacks 03G9 is not known to be abelian here, and it carries no
colimit instances, so the colimit is not written `colim`: the statement provides a cocone
together with the assertion that it is colimiting, which needs no instance.  "Direct summand" is
`CategoryTheory.Retract`, a morphism into the colimit split by a retraction; in an additive
category this is exactly the splitting off of a direct summand.

`AlgebraicGeometry.Space.ChartArtinianPresentation` bundles the inputs the argument needs at
the chart, which this file takes as a hypothesis so that the reduction is independent of how
they are proved:

* `pushforwardQuasicoherent` is Stacks 03M9 for the chart: the direct image of a quasi-coherent
  module along `j` is quasi-coherent.  Without it there is no functor `QCoh(𝒪_U) ⥤ QCoh(𝒪_X)`
  to transport the colimit along.
* `enoughInjectives` is Stacks 077V for the chart: `QCoh(𝒪_U)` has enough injectives.  This is
  what embeds `j^*J` into an injective object.
* `pushforwardPreservesFilteredColimits` is Stacks 07U6 for the chart, read in `QCoh`: the
  direct image along `j` preserves filtered colimits of quasi-coherent modules.  It is stated for
  the restricted functor, which is what the argument consumes.
* `artinianPresentation` is Stacks 09TI at the chart: every injective object of `QCoh(𝒪_U)` is
  a retract of a filtered colimit of Artinian direct images over `U`.  The field asks only for a
  *retract* of the colimit, which is weaker than the conclusion of Stacks 09TI (there the
  injective object *is* the colimit) and is all the argument consumes.

All four are proved at an affine locally Noetherian chart of a quasi-separated algebraic space by
`AlgebraicGeometry.Space.chartArtinianPresentation_of_isAffine` (in
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/NoetherianInjectiveEtaleAcyclicity.lean`)
together with
`AlgebraicGeometry.Space.preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_of_isAffine`,
which is how
`AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract_of_isNoetherian`
obtains Stacks 09TJ from the reduction here.

The hypothesis of the main theorem is quantified over affine surjective étale charts with
locally Noetherian source, so that the chart produced by Stacks 03H6 and the local Noetherianity
of its source are proved here and not assumed; the antecedents are exactly the properties of the
chart that make the four inputs legitimate.

## References

* [Stacks Project, Tag 09TJ](https://stacks.math.columbia.edu/tag/09TJ)
* [Stacks Project, Tag 09TI](https://stacks.math.columbia.edu/tag/09TI)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A module on an algebraic space `X` over `S` is an *Artinian direct image* when it is
isomorphic to the direct image, along some morphism `Z ⟶ X` of algebraic spaces, of a coherent
module on an object `Z` of the site whose underlying scheme is affine with Artinian ring of
global sections — that is, on the spectrum of an Artinian ring, regarded as an algebraic space
by `AlgebraicGeometry.schemeSpace`.

Coherence is `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA, coherence on the small étale
ringed site, and the direct image is `AlgebraicGeometry.Space.modulePushforward` of
Stacks 03LU. -/
def IsArtinianPushforward (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ Z : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) ∧
        ∃ (g : schemeSpace Z ⟶ X)
          (G : Modules.{u, u} B S hS (schemeSpace Z).1
            (schemeSpace Z).2),
          IsCoherent B S hS (schemeSpace Z).1
              (schemeSpace Z).2 G ∧
            Nonempty ((modulePushforward B S hS g).obj G ≅ M)

variable {X Y : AlgebraicSpaces B S hS}

/-- The direct image of an Artinian direct image is again an Artinian direct image: the direct
image along `Z ⟶ Y` followed by the one along `j : Y ⟶ X` is the direct image along the
composite, by the comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of
Stacks 03LU. -/
theorem isArtinianPushforward_modulePushforward (j : Y ⟶ X)
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : IsArtinianPushforward B S hS Y M) :
    IsArtinianPushforward B S hS X ((modulePushforward B S hS j).obj M) := by
  obtain ⟨Z, hZaff, hZart, g, G, hGcoh, ⟨e⟩⟩ := hM
  exact ⟨Z, hZaff, hZart, g ≫ j, G, hGcoh,
    ⟨((modulePushforwardCompIso B S hS g j).app G).symm ≪≫
      (modulePushforward B S hS j).mapIso e⟩⟩

/-- The direct image of Stacks 03LU along a morphism `j : Y ⟶ X` of algebraic spaces, restricted
to the quasi-coherent modules of Stacks 03G9, granted that it preserves quasi-coherence.

The hypothesis is the content of Stacks 03M9 for `j`; for a quasi-compact and quasi-separated
`j` it is `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`. -/
noncomputable def chartQuasicoherentPushforward (j : Y ⟶ X)
    (hqc : ∀ M : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2,
      ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ modulePushforward B S hS j) hqc

/-- The inputs at an étale chart `j : Y ⟶ X` of an algebraic space that the proof of Stacks 09TJ
consumes, bundled.

The fields are, in order: Stacks 03M9 for `j`; Stacks 077V for the source; Stacks 07U6 for `j`
read in the quasi-coherent categories; and Stacks 09TI transported to the chart, which is the
main input and asks that every injective object of `QCoh(𝒪_Y)` be a retract of a filtered
colimit of direct images of coherent modules from spectra of Artinian rings over `Y`. -/
structure ChartArtinianPresentation (X Y : AlgebraicSpaces B S hS) (j : Y ⟶ X) : Prop where
  /-- **Stacks 03M9** for the chart: the direct image along `j` of a quasi-coherent module is
  quasi-coherent. -/
  pushforwardQuasicoherent : ∀ M : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2,
    ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite
  /-- **Stacks 077V** for the chart: the quasi-coherent modules on `Y` have enough
  injectives. -/
  enoughInjectives : EnoughInjectives (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)
  /-- **Stacks 07U6** for the chart: the direct image along `j` preserves filtered colimits of
  quasi-coherent modules. -/
  pushforwardPreservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u}
      (chartQuasicoherentPushforward B S hS j pushforwardQuasicoherent)
  /-- **Stacks 09TI** transported to the chart: every injective object of `QCoh(𝒪_Y)` is a
  retract of a filtered colimit of direct images of coherent modules from spectra of Artinian
  rings over `Y`. -/
  artinianPresentation : ∀ JY : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2, Injective JY →
    ∃ (I : Type u) (inst : SmallCategory I),
      letI := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)
        (c : Cocone D),
        (∀ i, IsArtinianPushforward B S hS Y (D.obj i).obj) ∧
          Nonempty (IsColimit c) ∧ Nonempty (Retract JY c.pt)

/-- The adjunction of Stacks 03LU along an étale morphism `j : Y ⟶ X` of algebraic spaces,
restricted to the quasi-coherent modules of Stacks 03G9.

The left adjoint is `AlgebraicGeometry.Space.quasicoherentPullbackOfIsEtale`, which needs no
hypothesis beyond étaleness of `j`, and the right adjoint is
`AlgebraicGeometry.Space.chartQuasicoherentPushforward`.  Both inclusions of the quasi-coherent
modules are fully faithful and both restrictions commute with them on the nose, so this is
`CategoryTheory.Adjunction.restrictFullyFaithful` at two identity comparisons. -/
noncomputable def chartQuasicoherentAdjunction (j : Y ⟶ X) (hjet : IsEtale B S hS j.hom)
    (hqc : ∀ M : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2,
      ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite) :
    quasicoherentPullbackOfIsEtale B S hS j hjet ⊣
      chartQuasicoherentPushforward B S hS j hqc :=
  (modulePullbackAdjunction B S hS j).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

/-- The inverse image of quasi-coherent modules along an étale morphism of algebraic spaces is
faithful as soon as the ambient inverse image of modules of Stacks 03LU is.

A morphism of quasi-coherent modules *is* a morphism of modules and the restricted inverse
image is the ambient one, so this is only the passage to the full subcategory. -/
theorem faithful_quasicoherentPullbackOfIsEtale (j : Y ⟶ X) (hjet : IsEtale B S hS j.hom)
    [(modulePullback B S hS j).Faithful] :
    (quasicoherentPullbackOfIsEtale B S hS j hjet).Faithful := by
  constructor
  intro M N g h hgh
  have hgh0 := congrArg CategoryTheory.InducedCategory.Hom.hom hgh
  have hgh' : (modulePullback B S hS j).map g.hom = (modulePullback B S hS j).map h.hom := hgh0
  exact CategoryTheory.InducedCategory.hom_ext ((modulePullback B S hS j).map_injective hgh')

/-- An injective object `J` of `QCoh(𝒪_X)` is a retract of the direct image along an étale
morphism `j : Y ⟶ X` of an injective object of `QCoh(𝒪_Y)`.

The inverse image `j^*J` is quasi-coherent by Stacks 03GA along an étale morphism, it embeds
into an injective object `J'` of `QCoh(𝒪_U)` because that category has enough injectives, and
the transpose `J ⟶ j_*J'` of that embedding is a monomorphism because `j^*` is faithful — which
for a surjective étale chart is
`AlgebraicGeometry.Space.faithful_modulePullback`, Stacks Equation 03LW — hence reflects
monomorphisms.  Injectivity of `J` splits the monomorphism. -/
theorem nonempty_retract_chartQuasicoherentPushforward (U : BigFppfOver B S hS)
    (j : schemeSpace U ⟶ X) (hjet : IsEtale B S hS j.hom)
    (hjsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.hom)
    (hH : ChartArtinianPresentation B S hS X (schemeSpace U) j)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J] :
    ∃ J' : QuasicoherentSheaves.{u, u} B S hS
        (schemeSpace U).1 (schemeSpace U).2, Injective J' ∧
      Nonempty (Retract J
        ((chartQuasicoherentPushforward B S hS j hH.pushforwardQuasicoherent).obj J')) := by
  have hinj := hH.enoughInjectives
  obtain ⟨P⟩ := EnoughInjectives.presentation
    (C := QuasicoherentSheaves.{u, u} B S hS
      (schemeSpace U).1 (schemeSpace U).2)
    ((quasicoherentPullbackOfIsEtale B S hS j hjet).obj J)
  have hfaithM := faithful_modulePullback B S hS U j hjet hjsurj
  have hfaith := faithful_quasicoherentPullbackOfIsEtale B S hS j hjet
  obtain ⟨μ, hμ⟩ : ∃ μ : J ⟶ (chartQuasicoherentPushforward B S hS j
      hH.pushforwardQuasicoherent).obj P.J, Mono μ :=
    ⟨(chartQuasicoherentAdjunction B S hS j hjet
      hH.pushforwardQuasicoherent).homEquiv J P.J P.f, inferInstance⟩
  exact ⟨P.J, P.injective, ⟨{ i := μ
                              r := Injective.factorThru (𝟙 J) μ
                              retract := Injective.comp_factorThru (𝟙 J) μ }⟩⟩

/-- **Stacks 09TJ at a chart.**  Granted the inputs of
`AlgebraicGeometry.Space.ChartArtinianPresentation` at an étale morphism `j : Y ⟶ X` of
algebraic spaces, every injective object of `QCoh(𝒪_X)` is a retract of a filtered colimit of
Artinian direct images over `X`.

`J` is a retract of `j_*J'` for an injective `J'` of `QCoh(𝒪_Y)`, that `J'` is a retract of a
filtered colimit of Artinian direct images over `Y`, and `j_*` carries the colimit to a colimit
and the Artinian direct images to Artinian direct images over `X`. -/
theorem exists_filtered_colimit_artinian_pushforwards_retract_of_chart
    (U : BigFppfOver B S hS) (j : schemeSpace U ⟶ X) (hjet : IsEtale B S hS j.hom)
    (hjsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.hom)
    (hH : ChartArtinianPresentation B S hS X (schemeSpace U) j)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J] :
    ∃ (I : Type u) (inst : SmallCategory I),
      letI := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (c : Cocone D),
        (∀ i, IsArtinianPushforward B S hS X (D.obj i).obj) ∧
          Nonempty (IsColimit c) ∧ Nonempty (Retract J c.pt) := by
  obtain ⟨J', hJ', ⟨hretJ⟩⟩ :=
    nonempty_retract_chartQuasicoherentPushforward B S hS U j hjet hjsurj hH J
  obtain ⟨I, inst, hfilt, D, c, hart, ⟨hc⟩, ⟨hretJ'⟩⟩ := hH.artinianPresentation J' hJ'
  let := inst
  let := hfilt
  have hpres := hH.pushforwardPreservesFilteredColimits
  exact ⟨I, inst, hfilt,
    D ⋙ chartQuasicoherentPushforward B S hS j hH.pushforwardQuasicoherent,
    (chartQuasicoherentPushforward B S hS j hH.pushforwardQuasicoherent).mapCocone c,
    fun i => isArtinianPushforward_modulePushforward B S hS j (hart i),
    ⟨isColimitOfPreserves _ hc⟩, ⟨hretJ.trans (hretJ'.map _)⟩⟩

/-- The chart reduction of Stacks 09TJ: the conclusion of Stacks 09TJ for a Noetherian `X`,
from `AlgebraicGeometry.Space.ChartArtinianPresentation` at every affine surjective étale chart
with locally Noetherian source.  Those inputs are all proved in
`AlgebraicGeometry.Space.chartArtinianPresentation_of_isAffine` and
`AlgebraicGeometry.Space.preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_of_isAffine`,
and Stacks 09TJ itself is
`AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract_of_isNoetherian`.

Let `X` be a Noetherian algebraic space over a scheme `S` of a big fppf site.  Every injective
object `J` of the category `QCoh(𝒪_X)` of quasi-coherent modules on the small étale site of `X`
is a direct summand — a retract — of a filtered colimit of quasi-coherent modules of the form
`(Z_i ⟶ X)_* 𝒢_i` with `Z_i` the spectrum of an Artinian ring and `𝒢_i` a coherent module on
`Z_i`. -/
theorem exists_filtered_colimit_artinian_pushforwards_retract
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hX : IsNoetherian B S hS hZ X.1)
    (hchart : ∀ (U : BigFppfOver B S hS)
      (j : schemeSpace U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) →
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf j.hom →
      IsEtale B S hS j.hom →
      ChartArtinianPresentation B S hS X
        (schemeSpace U) j)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J] :
    ∃ (I : Type u) (inst : SmallCategory I),
      letI := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (c : Cocone D),
        (∀ i, IsArtinianPushforward B S hS X (D.obj i).obj) ∧
          Nonempty (IsColimit c) ∧ Nonempty (Retract J c.pt) := by
  -- Stacks 03H6 produces an affine surjective étale chart of the quasi-compact `X`.
  obtain ⟨U, f, hUaff, hfsurj, hfet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).mp hX.1
  -- The chart is a Noetherian affine scheme, local Noetherianity being étale-local.
  have hUnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS X.1
        (fun T : Scheme.{u} => IsLocallyNoetherian T) X.2).mp hX.2.2 U f
      ((isEtale_iff_presheaf_of_yoneda B S hS f).1 hfet)
  exact exists_filtered_colimit_artinian_pushforwards_retract_of_chart B S hS U
    (ObjectProperty.homMk f) hfet hfsurj
    (hchart U (ObjectProperty.homMk f) hUaff hUnoeth hfsurj hfet) J

end AlgebraicGeometry.Space

end
