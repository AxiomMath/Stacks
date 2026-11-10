module

public import Mathlib.Algebra.FreeAlgebra.Cardinality
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleIffFormallyEtale
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallyEtale.Lifting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFirstOrder
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf
public import StacksFrontier.RingTheory.Unramified.Thickening
public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubschemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealOrderIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickeningDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine

/-!
# Universal thickening existence: the first-order clause and affine size bounds

Stacks 05ZH for the spaces-étale site in the form consumed by the construction of the universal
first order thickening, the first-order clause of Stacks 0BPI along a surjective étale scheme
chart, and the cardinal bounds placing the affine universal first order thickening of Stacks 04F3
inside the big fppf site, with the comparison isomorphism between two such thickenings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Spaces.UniversalThickening

open AlgebraicGeometry.Space

/-- **Stacks 05ZH, essential surjectivity of the spaces-étale pullback at a thickening.** Every
algebraic space étale over the closed subspace of a first-order thickening is the base change
along the inclusion of an algebraic space étale over the ambient space.

This is the form in which the construction below consumes Stacks 05ZH; it is proved
unconditionally by `Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening`. -/
abbrev EtaleExtendsAlongFirstOrderThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {Y' Z : AlgebraicGeometry.AlgebraicSpaces B S hS} (Y : Subfunctor Y'.1),
    AlgebraicGeometry.Space.IsFirstOrderThickening B S hS Y' Y →
    ∀ (a : Z.1 ⟶ Y.toFunctor), AlgebraicGeometry.Space.IsEtale B S hS a →
    ∃ (W' : AlgebraicGeometry.AlgebraicSpaces B S hS) (g : W' ⟶ Y') (j : Z.1 ⟶ W'.1),
      AlgebraicGeometry.Space.IsEtale B S hS g.hom ∧ IsPullback a j Y.ι g.hom

/-- **Stacks 05ZH for the spaces-étale site**, in the form the construction below consumes it.

The closed subspace `Y` of the thickening is an algebraic space — that is part of the
thickening datum — so the inclusion `Y.ι` is a morphism of algebraic spaces, and it is a
monomorphism whose range is `Y` itself. Base change along it is therefore essentially
surjective by `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening`, so
the given algebraic space étale over `Y`, read as an object of the spaces-étale site of `Y`, is
isomorphic over `Y` to the base change of an object `W'` étale over the ambient space. The
cartesian square of the statement is the cartesian square of that base change, transported
along the isomorphism and read in presheaves by
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`. -/
theorem etaleExtendsAlongFirstOrderThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    EtaleExtendsAlongFirstOrderThickening B S hS := by
  intro Y' Z Y hY a ha
  let X : AlgebraicGeometry.AlgebraicSpaces B S hS :=
    ⟨Y.toFunctor, (hY.isThickening B S hS).1.1⟩
  let f : X ⟶ Y' := ObjectProperty.homMk Y.ι
  have : Mono f.hom := (inferInstance : Mono Y.ι)
  have hrange : Subfunctor.range f.hom = Y := Subfunctor.range_ι Y
  have hT : AlgebraicGeometry.Space.IsFirstOrderThickening B S hS Y'
      (Subfunctor.range f.hom) := by
    rw [hrange]; exact hY
  let C : AlgebraicGeometry.Space.SpacesEtale B S hS X :=
    ⟨Over.mk (ObjectProperty.homMk a : Z ⟶ X), ha⟩
  have :=
    AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening B S hS f hT
  obtain ⟨V, ⟨e⟩⟩ :=
    Functor.EssSurj.mem_essImage
      (F := (AlgebraicGeometry.Space.spacesBaseChange B S hS f).functor) C
  let eZ := (AlgebraicGeometry.Space.SpacesEtale.toSpaces B S hS X).mapIso e
  have hw : eZ.hom ≫ C.1.hom =
      ((AlgebraicGeometry.Space.spacesBaseChange B S hS f).functor.obj V).1.hom :=
    Over.w e.hom.hom
  have hsq : IsPullback C.1.hom
      (eZ.inv ≫ (AlgebraicGeometry.Space.spacesBaseChange B S hS f).projection.app V)
      f V.1.hom := by
    refine ((AlgebraicGeometry.Space.spacesBaseChange B S hS f).isPullback V).flip.of_iso
      eZ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, hw]
    · simp
    · simp
    · simp
  exact ⟨V.1.left, V.1.hom,
    (eZ.inv ≫ (AlgebraicGeometry.Space.spacesBaseChange B S hS f).projection.app V).hom,
    V.property, AlgebraicGeometry.AlgebraicSpaces.isPullback_hom B S hS hsq⟩

/-! ### The first-order clause of Stacks 0BPI along a surjective étale chart -/

/-- An étale chart of `Q` is covered by a single chart which factors through a given surjective
étale chart `q`, namely by the base change of the chart along `q`. -/
private theorem exists_smallEtaleChart_over_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Q : AlgebraicGeometry.AlgebraicSpaces B S hS}
    {V : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj V ⟶ Q.1)
    (hqsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : AlgebraicGeometry.Space.IsEtale B S hS q)
    (W : AlgebraicGeometry.Space.SmallEtale B S hS Q.1) :
    ∃ (W' : AlgebraicGeometry.Space.SmallEtale B S hS (AlgebraicGeometry.schemeSpace V).1)
      (a : (AlgebraicGeometry.Space.smallEtalePostcomp B S hS
          (ObjectProperty.homMk q : AlgebraicGeometry.schemeSpace V ⟶ Q) hqe).obj W' ⟶ W),
      Presieve.ofArrows
        (fun _ : PUnit.{u + 1} => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
          ((AlgebraicGeometry.Space.SmallEtale.toOver B S hS Q.1).obj
            ((AlgebraicGeometry.Space.smallEtalePostcomp B S hS
              (ObjectProperty.homMk q : AlgebraicGeometry.schemeSpace V ⟶ Q) hqe).obj W')))
        (fun _ : PUnit.{u + 1} => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          ((AlgebraicGeometry.Space.SmallEtale.toOver B S hS Q.1).map a)) ∈
      Scheme.etalePrecoverage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        ((AlgebraicGeometry.Space.SmallEtale.toOver B S hS Q.1).obj W)) := by
  classical
  set Tsite := AlgebraicGeometry.BigFppfOver.toScheme B S hS with hTsite
  have hrep : yoneda.relativelyRepresentable q := hqetale.rep
  set φ : yoneda.obj W.1.left ⟶ Q.1 := W.1.hom with hφ
  set T : AlgebraicGeometry.BigFppfOver B S hS := hrep.pullback φ with hT
  set π : T ⟶ W.1.left := hrep.snd φ with hπ
  set m : T ⟶ V := yoneda.preimage (hrep.fst φ) with hm
  have hmmap : yoneda.map m = hrep.fst φ := yoneda.map_preimage _
  have hpb : IsPullback (yoneda.map m) (yoneda.map π) q φ := by
    rw [hmmap]
    exact hrep.isPullback φ
  have hstE : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Tsite)) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hstS : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) Tsite)) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hmEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Tsite).presheaf
        (yoneda.map m) :=
    MorphismProperty.of_isPullback hpb.flip W.property
  have hπEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Tsite).presheaf
        (yoneda.map π) :=
    MorphismProperty.of_isPullback hpb hqetale
  have hπSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) Tsite).presheaf
        (yoneda.map π) :=
    MorphismProperty.of_isPullback hpb hqsurj
  have hπEt' : MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Tsite π :=
    MorphismProperty.of_relative_map hπEt
  have hπSurj' : MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) Tsite π :=
    MorphismProperty.of_relative_map hπSurj
  have hπEtale : AlgebraicGeometry.Etale (Tsite.map π) := hπEt'
  have hπSurjective : AlgebraicGeometry.Surjective (Tsite.map π) := hπSurj'
  refine ⟨⟨CostructuredArrow.mk (yoneda.map m), hmEt⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk π hpb.w.symm), ?_⟩
  refine (AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff
    (@AlgebraicGeometry.Etale.{u})).mpr ⟨fun x => ⟨PUnit.unit, ?_⟩, fun _ => hπEtale⟩
  obtain ⟨y, hy⟩ := hπSurjective.1 x
  exact ⟨y, hy⟩

/-- **The vanishing of a power of the defining ideal descends along a surjective étale chart.**
If the defining ideal of the inverse image of a closed subspace `Z ⊆ Q` in a surjective étale
chart `q : V ⟶ Q` has vanishing `(n+1)`st power on every chart of `V`, then the defining ideal
of `Z` has vanishing `(n+1)`st power on every chart of `Q`.

Every chart `W` of `Q` is covered by its base change along `q`, which is a chart of `V` read as
a chart of `Q`, and the defining ideal of `Z` on a chart coming from `V` is the defining ideal
of the inverse image there. -/
private theorem definingIdealAt_pow_eq_bot_of_surjectiveEtaleChart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) {Q : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (Z : AlgebraicGeometry.Space.ClosedSubspaces B S hS Q.1)
    {V : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj V ⟶ Q.1)
    (hqsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : AlgebraicGeometry.Space.IsEtale B S hS q)
    (hpre : ∀ W' : AlgebraicGeometry.Space.SmallEtale B S hS
        (AlgebraicGeometry.schemeSpace V).1,
      AlgebraicGeometry.Space.definingIdealAt B S hS (AlgebraicGeometry.schemeSpace V)
          ⟨Z.1.preimage q, AlgebraicGeometry.Space.isClosedSubspace_preimage B S hS q Z.1
            Q.2 (AlgebraicGeometry.schemeSpace V).2 Z.2⟩ (Opposite.op W') ^ (n + 1) = ⊥)
    (W : AlgebraicGeometry.Space.SmallEtale B S hS Q.1) :
    AlgebraicGeometry.Space.definingIdealAt B S hS Q Z (Opposite.op W) ^ (n + 1) = ⊥ := by
  obtain ⟨W', a, hcov⟩ :=
    exists_smallEtaleChart_over_chart B S hS q hqsurj hqetale hqe W
  refine AlgebraicGeometry.Space.definingIdealAt_pow_eq_bot_of_ofArrows B S hS Q Z n W
    (fun _ : PUnit.{u + 1} => (AlgebraicGeometry.Space.smallEtalePostcomp B S hS
      (ObjectProperty.homMk q : AlgebraicGeometry.schemeSpace V ⟶ Q) hqe).obj W')
    (fun _ => a)
    (AlgebraicGeometry.Space.SmallEtale.ofArrows_mem_topology B S hS Q.1 _ _ hcov)
    (fun _ => ?_)
  rw [AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_smallEtalePostcomp
    B S hS (ObjectProperty.homMk q : AlgebraicGeometry.schemeSpace V ⟶ Q) hqe Z W']
  exact hpre W'

/-- **Stacks 0BPI, the first-order clause, along a surjective étale chart.** Let `Y` be a
subfunctor of an algebraic space `Q` over `S` which is a sheaf for the big fppf topology, and
let `q : V ⟶ Q` be a surjective étale chart of `Q` by an object of the site. If the base change
of the inclusion of `Y` along `q` is a closed immersion whose range is a first-order thickening
of `V`, then `Y` is a closed subspace of `Q` and a first-order thickening of it.

The source states the clause for an arbitrary fpqc covering of the target; this is the case of
a one-member covering by a surjective étale scheme chart, which is the case the construction
below consumes, together with the sheaf condition on `Y` that the fpqc statement does not ask
for. Algebraicity of `Y` and closedness of its inclusion are Stacks 03I2 at the closed
immersions, whose effective-descent input is discharged outright by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`;
surjectivity on points follows from surjectivity of `q` and of the base change; and the order
clause is `Stacks.Spaces.UniversalThickening.definingIdealAt_pow_eq_bot_of_surjectiveEtaleChart`,
which descends the vanishing of the square of the defining ideal from the charts of `V` to the
charts of `Q`. -/
@[stacks 0BPI "first-order clause, along a surjective etale chart"]
theorem isClosedSubspace_and_isFirstOrderThickening_of_surjectiveEtaleChart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Q : AlgebraicGeometry.AlgebraicSpaces B S hS} (Y : Subfunctor Q.1)
    (hYsheaf : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) Y.toFunctor)
    {V : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj V ⟶ Q.1)
    (hqsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hclosed : AlgebraicGeometry.Space.IsClosedImmersion B S hS
      (Limits.pullback.snd Y.ι q))
    (hfirst : AlgebraicGeometry.Space.IsFirstOrderThickening B S hS
      (AlgebraicGeometry.schemeSpace V)
      (Subfunctor.range (Limits.pullback.snd Y.ι q))) :
    AlgebraicGeometry.Space.IsClosedSubspace B S hS Y ∧
      AlgebraicGeometry.Space.IsFirstOrderThickening B S hS Q Y := by
  classical
  have hri : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hqe : AlgebraicGeometry.Space.IsEtale B S hS q :=
    AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS hqetale
  -- The range of the base change is the inverse image of `Y`.
  have hrange : Subfunctor.range (Limits.pullback.snd Y.ι q) = Y.preimage q := by
    have h := Subfunctor.range_eq_preimage_of_isPullback
      (IsPullback.of_hasPullback Y.ι q).flip
    rwa [Subfunctor.range_ι] at h
  -- Algebraicity of `Y` and closedness of its inclusion, by Stacks 03I2.
  obtain ⟨hYalg, hYci⟩ :=
    AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
      (AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS)
      hYsheaf Q.property hqsurj hqetale hclosed
  have hYclosed : AlgebraicGeometry.Space.IsClosedSubspace B S hS Y := ⟨hYalg, hYci⟩
  -- Surjectivity on points.
  have hqpts : Function.Surjective
      (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) q) :=
    (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS
      Q.1 Q.property V q).mp hqsurj
  have hsndpts : Function.Surjective (AlgebraicGeometry.Space.pointsMap B S hS
      (Limits.pullback Y.ι q) (Limits.pullback.snd Y.ι q)) := by
    have hfac : Subfunctor.toRange (Limits.pullback.snd Y.ι q) ≫
        (Subfunctor.range (Limits.pullback.snd Y.ι q)).ι = Limits.pullback.snd Y.ι q :=
      Subfunctor.toRange_ι _
    have hmono : Mono (Limits.pullback.snd Y.ι q) :=
      AlgebraicGeometry.Space.mono_of_isClosedImmersion B S hS
        (Limits.pullback.snd Y.ι q) hclosed
    have hiso : IsIso (Subfunctor.toRange (Limits.pullback.snd Y.ι q)) := inferInstance
    have htr : Function.Surjective (AlgebraicGeometry.Space.pointsMap B S hS
        (Limits.pullback Y.ι q) (Subfunctor.toRange (Limits.pullback.snd Y.ι q))) := by
      have hkey : AlgebraicGeometry.Space.pointsMap B S hS (Limits.pullback Y.ι q)
            (Subfunctor.toRange (Limits.pullback.snd Y.ι q)) ∘
          AlgebraicGeometry.Space.pointsMap B S hS
            (Subfunctor.range (Limits.pullback.snd Y.ι q)).toFunctor
            (inv (Subfunctor.toRange (Limits.pullback.snd Y.ι q))) = id := by
        rw [← AlgebraicGeometry.Space.pointsMap_comp, IsIso.inv_hom_id,
          AlgebraicGeometry.Space.pointsMap_id]
      have hsurj : Function.Surjective (AlgebraicGeometry.Space.pointsMap B S hS
            (Limits.pullback Y.ι q) (Subfunctor.toRange (Limits.pullback.snd Y.ι q)) ∘
          AlgebraicGeometry.Space.pointsMap B S hS
            (Subfunctor.range (Limits.pullback.snd Y.ι q)).toFunctor
            (inv (Subfunctor.toRange (Limits.pullback.snd Y.ι q)))) := by
        rw [hkey]
        exact Function.surjective_id
      exact hsurj.of_comp
    rw [← hfac, AlgebraicGeometry.Space.pointsMap_comp]
    exact hfirst.1.2.comp htr
  have hYpts : Function.Surjective
      (AlgebraicGeometry.Space.pointsMap B S hS Y.toFunctor Y.ι) := by
    have hw : Limits.pullback.fst Y.ι q ≫ Y.ι = Limits.pullback.snd Y.ι q ≫ q :=
      Limits.pullback.condition
    have hcomp := congrArg (AlgebraicGeometry.Space.pointsMap B S hS
      (Limits.pullback Y.ι q)) hw
    rw [AlgebraicGeometry.Space.pointsMap_comp,
      AlgebraicGeometry.Space.pointsMap_comp] at hcomp
    exact Function.Surjective.of_comp
      (g := AlgebraicGeometry.Space.pointsMap B S hS (Limits.pullback Y.ι q)
        (Limits.pullback.fst Y.ι q))
      (hcomp ▸ hqpts.comp hsndpts)
  -- The order clause.
  refine ⟨hYclosed, ⟨hYclosed, hYpts⟩, fun W => ?_⟩
  refine definingIdealAt_pow_eq_bot_of_surjectiveEtaleChart B S hS 1 ⟨Y, hYclosed⟩ q
    hqsurj hqetale hqe (fun W' => ?_) W
  have hZeq : (⟨Subfunctor.range (Limits.pullback.snd Y.ι q), hfirst.1.1⟩ :
      AlgebraicGeometry.Space.ClosedSubspaces B S hS
        (AlgebraicGeometry.schemeSpace V).1) =
      ⟨Y.preimage q, AlgebraicGeometry.Space.isClosedSubspace_preimage B S hS q Y
        Q.2 (AlgebraicGeometry.schemeSpace V).2 hYclosed⟩ := Subtype.ext hrange
  rw [← hZeq]
  exact hfirst.2 W'

/-- The descent of an invariant subscheme is a sheaf: it is by construction the sheafification
of a subfunctor of the quotient, which is one. -/
private theorem isSheaf_descendedInvariantSubfunctor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X}
    (P : AlgebraicGeometry.Space.Presentation B S hS X hX)
    [Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.sitePreRelation B S hS P.target P.source)]
    (Z : AlgebraicGeometry.Space.GroupoidInvariantLocallyClosedSubscheme B S hS
      P.target P.source) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (AlgebraicGeometry.Space.descendedInvariantSubfunctor B S hS P Z).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Subfunctor.sheafify_isSheaf _ ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)

private lemma universal_extension_lift_of_squareZero_surjection
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (P : Algebra.Extension.{u} R S)
    (hP : P.IsUniversalFirstOrderThickening)
    (f : T →ₐ[R] S) (hf : Function.Surjective f)
    (hI : RingHom.ker f ^ 2 = ⊥) :
    ∃ c : P.Ring →ₐ[R] T,
      f.comp c = IsScalarTower.toAlgHom R P.Ring S := by
  let I : Ideal T := RingHom.ker f
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  obtain ⟨c, hc, _⟩ := hP.existsUnique_lift I hI e.symm.toAlgHom
  refine ⟨c, ?_⟩
  apply AlgHom.ext
  intro x
  have h := congrArg (fun k : P.Ring →ₐ[R] T ⧸ I => e (k x)) hc
  change (Ideal.quotientKerAlgEquivOfSurjective hf)
      ((Ideal.Quotient.mk (RingHom.ker f)) (c x)) =
    (Ideal.quotientKerAlgEquivOfSurjective hf)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm
        ((IsScalarTower.toAlgHom R P.Ring S) x)) at h
  rw [Ideal.quotientKerAlgEquivOfSurjective_mk, AlgEquiv.apply_symm_apply] at h
  exact h

/-- The square of the kernel vanishes on a subalgebra if it vanishes on the ambient ring. -/
private lemma ker_comp_subalgebra_val_sq_eq_bot
    {R T S : Type u} [CommRing R] [CommRing T] [CommRing S] [Algebra R T]
    (A : Subalgebra R T) (g : T →+* S) (hg : RingHom.ker g ^ 2 = ⊥) :
    RingHom.ker (g.comp (Subalgebra.val A).toRingHom) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hmap : Ideal.map (Subalgebra.val A).toRingHom
      (RingHom.ker (g.comp (Subalgebra.val A).toRingHom)) ≤ RingHom.ker g :=
    Ideal.map_le_iff_le_comap.mpr fun _ hz => hz
  have hm : (Subalgebra.val A) x ∈ (Ideal.map (Subalgebra.val A).toRingHom
      (RingHom.ker (g.comp (Subalgebra.val A).toRingHom))) ^ 2 := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (Subalgebra.val A).toRingHom hx
  have hm' := (pow_le_pow_left' hmap 2) hm
  rw [hg] at hm'
  exact Subtype.val_injective (Ideal.mem_bot.mp hm')

/-- The subalgebra generated by the range of a map from `S` has cardinality at most
`max (max #R #S) ℵ₀`. -/
private lemma cardinalMk_adjoin_range_le
    (R : Type u) {T S : Type u} [CommRing R] [CommRing T] [Algebra R T] (σ : S → T) :
    Cardinal.mk (Algebra.adjoin R (Set.range σ)) ≤
      max (max (Cardinal.mk R) (Cardinal.mk S)) Cardinal.aleph0 :=
  (Algebra.cardinalMk_adjoin_le R (Set.range σ)).trans (by gcongr; exact Cardinal.mk_range_le)

private lemma cardinalMk_universalExtension_le_max
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S)
    (hP : P.IsUniversalFirstOrderThickening) :
    Cardinal.mk P.Ring ≤ max (max (Cardinal.mk R) (Cardinal.mk S)) Cardinal.aleph0 := by
  classical
  let A := Algebra.adjoin R (Set.range P.σ)
  let f : A →ₐ[R] S := (IsScalarTower.toAlgHom R P.Ring S).comp (Subalgebra.val A)
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨P.σ s, Algebra.subset_adjoin (Set.mem_range_self s)⟩, ?_⟩
    simp [f]
  have hI : RingHom.ker f ^ 2 = ⊥ :=
    ker_comp_subalgebra_val_sq_eq_bot A (algebraMap P.Ring S) hP.ker_sq_eq_bot
  obtain ⟨c, hfc⟩ := universal_extension_lift_of_squareZero_surjection P hP f hf hI
  have hsurj : Function.Surjective (Subalgebra.val A) := by
    let b : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom R P.Ring S
    let eP := Ideal.quotientKerAlgEquivOfSurjective (f := b)
      (by simpa [b] using P.algebraMap_surjective)
    have hcomp (d : P.Ring →ₐ[R] P.Ring) (hd : b.comp d = b) :
        (Ideal.Quotient.mkₐ R P.ker).comp d = eP.symm.toAlgHom.comp b := by
      apply AlgHom.ext
      intro x
      apply eP.injective
      change eP ((Ideal.Quotient.mk (RingHom.ker b)) (d x)) =
        eP (eP.symm (b x))
      rw [Ideal.quotientKerAlgEquivOfSurjective_mk, AlgEquiv.apply_symm_apply]
      exact congrArg (fun k : P.Ring →ₐ[R] S => k x) hd
    obtain ⟨_, _, huniqP⟩ := hP.existsUnique_lift P.ker hP.ker_sq_eq_bot
      eP.symm.toAlgHom
    have hvc : b.comp ((Subalgebra.val A).comp c) = b := by
      change f.comp c = IsScalarTower.toAlgHom R P.Ring S
      exact hfc
    have hid : b.comp (AlgHom.id R P.Ring) = b := by simp
    have heq : (Subalgebra.val A).comp c = AlgHom.id R P.Ring :=
      (huniqP _ (hcomp _ hvc)).trans (huniqP _ (hcomp _ hid)).symm
    intro x
    exact ⟨c x, congrArg (fun d : P.Ring →ₐ[R] P.Ring => d x) heq⟩
  calc
    Cardinal.mk P.Ring ≤ Cardinal.mk A := Cardinal.mk_le_of_surjective hsurj
    _ ≤ max (max (Cardinal.mk R) (Cardinal.mk S)) Cardinal.aleph0 :=
      cardinalMk_adjoin_range_le R P.σ

private lemma contains_spec_universalExtension
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S)
    (hP : P.IsUniversalFirstOrderThickening)
    (hR : Cardinal.mk R < B.cutoff) (hS : Cardinal.mk S < B.cutoff) :
    B.Contains (AlgebraicGeometry.Spec (CommRingCat.of P.Ring)) := by
  change (AlgebraicGeometry.Spec (CommRingCat.of P.Ring)).size < B.cutoff
  rw [AlgebraicGeometry.Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff
    ((cardinalMk_universalExtension_le_max P hP).trans_lt
      (max_lt (max_lt hR hS) B.aleph0_lt_cutoff))

private lemma contains_affine_universal_thickening
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {V U : Scheme.{u}}
    [IsAffine V] [IsAffine U]
    (hV : B.Contains V) (hU : B.Contains U)
    (q : V ⟶ U) [FormallyUnramified q] :
    let R := Γ(U, ⊤)
    let S := Γ(V, ⊤)
    letI : Algebra R S := q.appTop.hom.toAlgebra
    ∃ P : Algebra.Extension.{u} R S,
      P.IsUniversalFirstOrderThickening ∧ B.Contains (Spec (CommRingCat.of P.Ring)) := by
  dsimp only
  let R := Γ(U, ⊤)
  let S := Γ(V, ⊤)
  let : Algebra R S := q.appTop.hom.toAlgebra
  have htop : q.appTop = q.appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  have hFU : Algebra.FormallyUnramified R S := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    rw [htop]
    exact q.formallyUnramified_appLE (isAffineOpen_top U) (isAffineOpen_top V) (by simp)
  let : Algebra.FormallyUnramified R S := hFU
  let P := Algebra.FormallyUnramified.universalFirstOrderThickening R S
  let hP := Algebra.FormallyUnramified.isUniversalFirstOrderThickening R S
  have hR : Cardinal.mk R < B.cutoff :=
    (U.mk_sections_le_size ⟨⊤, isAffineOpen_top U⟩).trans_lt hU
  have hS : Cardinal.mk S < B.cutoff :=
    (V.mk_sections_le_size ⟨⊤, isAffineOpen_top V⟩).trans_lt hV
  exact ⟨P, hP, contains_spec_universalExtension B P hP hR hS⟩



private lemma size_le_of_universalThickening_affine_comparison
    {V U H A : Scheme.{u}} [IsAffine H] [IsAffine A]
    (q : V ⟶ U) (i : V ⟶ H) (p : H ⟶ U)
    (hH : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (j : V ⟶ A) (r : A ⟶ U)
    (hj : Stacks.Thickenings.IsFirstOrderThickening j)
    (hjr : j ≫ r = q)
    (g : H ⟶ A) (hgi : i ≫ g = j) (hgr : g ≫ r = p) :
    H.size ≤ A.size := by
  obtain ⟨f, hf, _⟩ := hH.existsUnique_lift j hj (𝟙 V) r (by simpa using hjr)
  have hgf : g ≫ f = 𝟙 H := by
    apply (hH.existsUnique_lift i hH.isFirstOrderThickening (𝟙 V) p
      (by simp [hH.inclusion_toBase])).unique
    · constructor
      · rw [← Category.assoc, hgi, hf.1]
      · rw [Category.assoc, hf.2, hgr]
    · simp
  have hinj : Function.Injective f.appTop.hom := by
    have hring : g.appTop.hom.comp f.appTop.hom = RingHom.id _ := by
      simpa [hgf, CommRingCat.hom_comp] using
        (congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop g f)).symm
    intro x y hxy
    have hx := congrArg g.appTop.hom hxy
    simpa only [← RingHom.comp_apply, hring, RingHom.id_apply] using hx
  rw [Scheme.size_of_isAffine H, Scheme.size_of_isAffine A]
  gcongr
  exact Cardinal.mk_le_of_injective hinj

private lemma bridge_size_le_universalThickening_affine
    {V U H : Scheme.{u}} [IsAffine V] [IsAffine U]
    (q : V ⟶ U) (i : V ⟶ H) (p : H ⟶ U)
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p) :
    H.size ≤ max V.size U.size := by
  classical
  let : IsClosedImmersion i := hi.isFirstOrderThickening.1
  let : IsAffine H :=
    Stacks.Thickenings.isAffine_of_isFirstOrderThickening hi.isFirstOrderThickening
  let R := Γ(U, ⊤)
  let S := Γ(V, ⊤)
  let T := Γ(H, ⊤)
  let : Algebra R T := p.appTop.hom.toAlgebra
  have hcomp : i.appTop.hom.comp p.appTop.hom = q.appTop.hom := by
    have h := congrArg (fun f : V ⟶ U => f.appTop.hom) hi.inclusion_toBase
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using h
  have hsurj : Function.Surjective i.appTop.hom :=
    i.app_surjective ⊤ (isAffineOpen_top H)
  let σ : S → T := fun s => Classical.choose (hsurj s)
  have hσ (s : S) : i.appTop.hom (σ s) = s := Classical.choose_spec (hsurj s)
  let A := Algebra.adjoin R (Set.range σ)
  let f : A →+* S := i.appTop.hom.comp (Subalgebra.val A).toRingHom
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨σ s, Algebra.subset_adjoin (Set.mem_range_self s)⟩, ?_⟩
    exact hσ s
  let r : R →+* A := algebraMap R A
  have hri : (Subalgebra.val A).toRingHom.comp r = p.appTop.hom := by
    ext x
    rfl
  have hfr : f.comp r = q.appTop.hom := by
    calc
      f.comp r = i.appTop.hom.comp ((Subalgebra.val A).toRingHom.comp r) := rfl
      _ = i.appTop.hom.comp p.appTop.hom := by rw [hri]
      _ = q.appTop.hom := hcomp
  have hker : RingHom.ker i.appTop.hom ^ 2 = ⊥ :=
    AlgebraicGeometry.Scheme.ker_appTop_pow_eq_bot i inferInstance hi.isFirstOrderThickening.2
  have hfker : RingHom.ker f ^ 2 = ⊥ := ker_comp_subalgebra_val_sq_eq_bot A _ hker
  let X := Spec (CommRingCat.of A)
  let j : V ⟶ X := V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f)
  let b : X ⟶ U := Spec.map (CommRingCat.ofHom r) ≫ U.isoSpec.inv
  let g : H ⟶ X := H.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (Subalgebra.val A).toRingHom)
  have hgi : i ≫ g = j := by
    change (i ≫ H.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.val A).toRingHom) =
      V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
    rw [Scheme.toSpecΓ_naturality i, Category.assoc, ← Spec.map_comp]
    rfl
  have hgb : g ≫ b = p := by
    change (H.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Subalgebra.val A).toRingHom) ≫
      Spec.map (CommRingCat.ofHom r)) ≫ U.isoSpec.inv = p
    rw [Category.assoc H.toSpecΓ]
    rw [← Spec.map_comp]
    rw [show (CommRingCat.ofHom r) ≫
        (CommRingCat.ofHom (Subalgebra.val A).toRingHom) =
        CommRingCat.ofHom p.appTop.hom from by
          apply CommRingCat.hom_ext
          exact hri]
    change H.toSpecΓ ≫ Spec.map p.appTop ≫ U.isoSpec.inv = p
    rw [← Category.assoc]
    rw [← Scheme.toSpecΓ_naturality p]
    simp [Scheme.isoSpec]
  have hj : Stacks.Thickenings.IsFirstOrderThickening j := by
    have hspec := specMap_isFirstOrderThickening (CommRingCat.ofHom f) hf hfker
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom f)) := hspec.1
    have : IsClosedImmersion j := by
      dsimp [j]
      infer_instance
    refine ⟨inferInstance, ?_⟩
    dsimp [j]
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact hspec.2
  have hjb : j ≫ b = q := by
    rw [← hgi, Category.assoc, hgb]
    exact hi.inclusion_toBase
  have hR : Cardinal.mk R ≤ U.size := U.mk_sections_le_size ⟨⊤, isAffineOpen_top U⟩
  have hS : Cardinal.mk S ≤ V.size := V.mk_sections_le_size ⟨⊤, isAffineOpen_top V⟩
  have hA : X.size ≤ max V.size U.size := by
    rw [Scheme.size_Spec]
    have hcard := cardinalMk_adjoin_range_le R σ
    have hbound : max (max (Cardinal.mk R) (Cardinal.mk S)) Cardinal.aleph0 ≤
        max V.size U.size := by
      apply max_le
      · exact max_le (hR.trans (le_max_right _ _))
          (hS.trans (le_max_left _ _))
      · exact V.aleph0_le_size.trans (le_max_left _ _)
    exact max_le (V.aleph0_le_size.trans (le_max_left _ _))
      (hcard.trans hbound)
  exact (size_le_of_universalThickening_affine_comparison q i p hi j b hj hjb g hgi hgb).trans hA

private lemma bridge_contains_universalThickening_affine
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {V U H : Scheme.{u}} [IsAffine V] [IsAffine U]
    (hV : B.Contains V) (hU : B.Contains U)
    (q : V ⟶ U) (i : V ⟶ H) (p : H ⟶ U)
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p) :
    B.Contains H :=
  (bridge_size_le_universalThickening_affine q i p hi).trans_lt (max_lt hV hU)

private lemma universalThickening_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y' Z' : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (Z : Subfunctor Z'.1)
    (p : Y' ⟶ X) (q : Z' ⟶ X)
    (hY : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Y p)
    (hZ : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Z q)
    (e : Z.toFunctor ≅ Y.toFunctor)
    (he : Z.ι ≫ q.hom = e.hom ≫ Y.ι ≫ p.hom) :
    ∃ e' : Z'.1 ≅ Y'.1,
      Z.ι ≫ e'.hom = e.hom ≫ Y.ι ∧ e'.hom ≫ p.hom = q.hom := by
  obtain ⟨f, hf, _⟩ := hY.existsUnique_lift Z hZ.firstOrder e.hom q.hom he
  have he' : Y.ι ≫ p.hom = e.inv ≫ Z.ι ≫ q.hom := by
    rw [he]
    simp
  obtain ⟨g, hg, _⟩ := hZ.existsUnique_lift Y hY.firstOrder e.inv p.hom he'
  have hfg : f ≫ g = 𝟙 Z'.1 := by
    apply (hZ.existsUnique_lift Z hZ.firstOrder (𝟙 _) q.hom (by simp)).unique
    · constructor
      · simp only [← Category.assoc, hf.1]
        simp only [Category.assoc, hg.1, Iso.hom_inv_id_assoc, Category.id_comp]
      · simp only [Category.assoc, hg.2, hf.2]
    · simp
  have hgf : g ≫ f = 𝟙 Y'.1 := by
    apply (hY.existsUnique_lift Y hY.firstOrder (𝟙 _) p.hom (by simp)).unique
    · constructor
      · simp only [← Category.assoc, hg.1]
        simp only [Category.assoc, hf.1, Iso.inv_hom_id_assoc, Category.id_comp]
      · simp only [Category.assoc, hf.2, hg.2]
    · simp
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

private lemma isEtale_of_universalThickening_comparison
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y' Z' W' : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (Z : Subfunctor Z'.1) (W : Subfunctor W'.1)
    (p : Y' ⟶ X) (q : Z' ⟶ X)
    (hY : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Y p)
    (hZ : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Z q)
    (g : W' ⟶ Y') (hg : AlgebraicGeometry.Space.IsEtale B S hS g.hom)
    (a : W.toFunctor ⟶ Y.toFunctor)
    (hsq : IsPullback a W.ι Y.ι g.hom)
    (e : Z.toFunctor ≅ W.toFunctor)
    (k : Z' ⟶ Y') (hk : k ≫ p = q)
    (hki : Z.ι ≫ k.hom = e.hom ≫ a ≫ Y.ι) :
    AlgebraicGeometry.Space.IsEtale B S hS k.hom ∧
      IsPullback (e.hom ≫ a) Z.ι Y.ι k.hom := by
  have hW := AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etalePullback
    B S hS Y p hY g hg W a hsq
  have hbase : k.hom ≫ p.hom = q.hom := congrArg (fun f => f.hom) hk
  have he : Z.ι ≫ q.hom = e.hom ≫ W.ι ≫ (g ≫ p).hom := by
    rw [← hbase, ← Category.assoc, hki]
    simpa only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using
      congrArg (fun f => e.hom ≫ f ≫ p.hom) hsq.w
  obtain ⟨e', he'i, he'b⟩ := universalThickening_iso B S hS W Z (g ≫ p) q hW hZ e he
  have hcomm : Z.ι ≫ q.hom = (e.hom ≫ a) ≫ Y.ι ≫ p.hom := by
    rw [← hbase, ← Category.assoc, hki]
    simp only [Category.assoc]
  have hke : k.hom = e'.hom ≫ g.hom := by
    apply (hY.existsUnique_lift Z hZ.firstOrder (e.hom ≫ a) q.hom hcomm).unique
    · exact ⟨by simpa only [Category.assoc] using hki, hbase⟩
    · constructor
      · rw [← Category.assoc, he'i, Category.assoc, ← hsq.w]
        simp only [Category.assoc]
      · exact he'b
  constructor
  · rw [hke]
    exact AlgebraicGeometry.Space.isEtale_comp B S hS
      (AlgebraicGeometry.Space.isEtale_of_isIso B S hS e'.hom) hg
  · apply hsq.of_iso' e (Iso.refl _) e' (Iso.refl _)
    · simp
    · exact he'i.symm
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id] using hke.symm

end Stacks.Spaces.UniversalThickening

end
