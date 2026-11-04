module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleRigidityOverColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFibreCondition
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionStageBelow

/-!
# The formal spectrum of the completion of an étale algebra is étale over the base

Let `S` be a scheme contained in a big fppf site `B`, let `R` be a weakly admissible
topological ring over `S` by a quotient system `D`, and let `R → A` be an étale ring map. The
relative completion `A^∧ = lim_J A ⧸ JA` carries a quotient system over `S` and the induced
morphism `Spf A^∧ ⟶ Spf R` of formal spectra is affine and étale after every represented base
change.

This is the direction of the equivalence of **Stacks 0AN8** which the source proves first: the
quotient stages of `Spf A^∧ ⟶ Spf R` are the spectra of the étale ring maps
`R ⧸ J → A ⧸ JA` of **Stacks 0AN8**, first step, and every represented base change of
`Spf A^∧ ⟶ Spf R` is computed by one of them.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_of_compact_tests`: a morphism property which is
  Zariski-local at the target holds for every represented base change of a relatively
  representable morphism of fppf sheaves as soon as it holds for the base changes along points
  out of quasi-compact objects of the site.
* `AlgebraicGeometry.FormalSpace.etale_toScheme_map_stageMap_kerProjectionIdeal`: the stage map
  `Spec (A ⧸ JA) ⟶ Spec (R ⧸ J)` of the completion is étale.
* `AlgebraicGeometry.FormalSpace.relative_isAffineHom_formalSpectrumMap_completionOver` and
  `AlgebraicGeometry.FormalSpace.relative_etale_formalSpectrumMap_completionOver`: every
  represented base change of `Spf A^∧ ⟶ Spf R` is affine, respectively étale.

## Implementation notes

The affineness clause is Stacks 0AKN,
`AlgebraicGeometry.FormalSpace.relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`,
applied to the morphism of affine formal algebraic spaces `Spf A^∧ ⟶ Spf R`, whose
representability by algebraic spaces is Stacks 0ANM, namely
`isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_completionOver` in this namespace.

The étaleness clause is local on the target: a point of `Spf R` out of an arbitrary object of
the site is covered by points out of its affine opens, and those are quasi-compact, so they
factor through a quotient stage by Stacks 0AIA. Over a stage the base change is the affine one
of Stacks 0ANM, `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_kerProjection`,
whose stage map is étale by Stacks 0AN8, first step.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

section CompactTests

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A relative morphism property of fppf sheaves may be tested at the quasi-compact points of
the target.** Let `P` be a property of morphisms of schemes which is Zariski-local at the target
and invariant under isomorphism, and let `f : X ⟶ Y` be a relatively representable morphism of
fppf sheaves over `S`. If every represented base change of `f` along a point of `Y` out of an
object of the site with compact underlying scheme has `P`, then so does every represented base
change of `f`.

An arbitrary object of the site is covered by its affine opens, which again lie in the site and
are quasi-compact; the base change of the represented base change along one of them is the
represented base change along the composite point, which the hypothesis covers. -/
theorem relative_of_compact_tests (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.RespectsIso]
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f)
    (hc : ∀ (T W : BigFppfOver B S hS),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (t : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y)
        (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ X) (q : W ⟶ T),
        IsPullback a ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f t →
        P ((BigFppfOver.toScheme B S hS).map q)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f := by
  refine ⟨hf, fun T W t a q hp ↦ ?_⟩
  change P ((BigFppfOver.toScheme B S hS).map q)
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
    dsimp only [Sheaf.sheafifiedYoneda]
    infer_instance
  refine IsZariskiLocalAtTarget.of_openCover
    ((BigFppfOver.toScheme B S hS).obj T).affineCover fun i ↦ ?_
  have hUi : B.Contains (((BigFppfOver.toScheme B S hS).obj T).affineCover.X i) :=
    Scheme.size_lt_of_isOpenImmersion
      (((BigFppfOver.toScheme B S hS).obj T).affineCover.f i) T.left.property
  let fO : B.obj hUi ⟶ T.left :=
    B.inclusion.preimage (show B.inclusion.obj (B.obj hUi) ⟶ B.inclusion.obj T.left from
      ((BigFppfOver.toScheme B S hS).obj T).affineCover.f i)
  let Ti : BigFppfOver B S hS := Over.mk (fO ≫ T.hom)
  let aa : Ti ⟶ T := Over.homMk fO (by simp [Ti])
  have hfmap : (BigFppfOver.toScheme B S hS).map aa =
      ((BigFppfOver.toScheme B S hS).obj T).affineCover.f i :=
    B.inclusion.map_preimage _
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj Ti) := by
    change CompactSpace (((BigFppfOver.toScheme B S hS).obj T).affineCover.X i)
    infer_instance
  have hsite : IsPullback (pullback.fst q aa) (pullback.snd q aa) q aa :=
    IsPullback.of_hasPullback q aa
  have hc' := hc Ti (pullback q aa) inferInstance
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map aa ≫ t)
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (pullback.fst q aa) ≫ a)
    (pullback.snd q aa)
    ((hsite.map (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))).paste_horiz hp)
  have hsch := hsite.map (BigFppfOver.toScheme B S hS)
  rw [hfmap] at hsch
  rw [← hsch.isoPullback_hom_snd] at hc'
  exact (MorphismProperty.cancel_left_of_respectsIso (P := P) hsch.isoPullback.hom _).mp hc'

/-- Two represented base changes of the same morphism of fppf sheaves along the same point of
its target have the same properties: the sources are isomorphic over the point, and the
sheafified Yoneda embedding is fully faithful, so the isomorphism comes from the site. -/
theorem prop_toScheme_map_of_isPullback_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X Y : FppfSheaf B S hS} {f : X ⟶ Y} {T W W' : BigFppfOver B S hS}
    {t : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ X} {q : W ⟶ T}
    {a' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W' ⟶ X} {q' : W' ⟶ T}
    (h : IsPullback a ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f t)
    (h' : IsPullback a' ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q') f t)
    (hP : P ((BigFppfOver.toScheme B S hS).map q')) :
    P ((BigFppfOver.toScheme B S hS).map q) := by
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have hY := Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)
  let e := h.isoIsPullback _ _ h'
  have hmap : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (hY.preimageIso e).hom = e.hom := hY.map_preimage e.hom
  have he₀ : (hY.preimageIso e).hom ≫ q' = q := hY.map_injective (by
    rw [Functor.map_comp, hmap]
    exact h.isoIsPullback_hom_snd _ _ h')
  rw [← he₀, Functor.map_comp]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := P) _ _).mpr hP

end CompactTests

section Completion

open TopologicalRing TopologicalRing.CompletionOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R A : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R] [CommRing A]

/-- **Stacks 0AN8, first step, on the stages of a formal spectrum.** The stage map of the
morphism `Spf A^∧ ⟶ Spf R` attached to an étale ring map `f : R →+* A`, at a weak ideal of
definition `J` of `R` and the kernel of the projection of `A^∧` onto `A ⧸ JA`, is the spectrum
of the étale ring map `R ⧸ J → A^∧ ⧸ ker (A^∧ → A ⧸ JA)`. -/
theorem etale_quotientMap_kerProjectionIdeal_of_eq (f : R →+* A) (hf : f.Etale)
    (φ : R →+* CompletionOver f) (hφ : φ = canonicalMap f) (J : WeakIdealOfDefinitionIndex R)
    (hJK : J.1 ≤ Ideal.comap φ (kerProjectionIdeal f J).1) :
    RingHom.Etale (Ideal.quotientMap (kerProjectionIdeal f J).1 φ hJK) := by
  subst hφ
  exact etale_quotientMap_canonicalMap hf J

/-- **Stacks 0AN8, first step, on the stages of a formal spectrum.** The stage map of the
morphism `Spf A^∧ ⟶ Spf R` attached to an étale ring map `f : R →+* A`, at a weak ideal of
definition `J` of `R` and the kernel of the projection of `A^∧` onto `A ⧸ JA`, is the spectrum
of the étale ring map `R ⧸ J → A^∧ ⧸ ker (A^∧ → A ⧸ JA)`. -/
theorem etale_toScheme_map_stageMap_kerProjectionIdeal (f : R →+* A) (hf : f.Etale)
    {D : QuotientSystem B S hS R} {E : QuotientSystem B S hS (CompletionOver f)}
    (g : ContinuousHom D E) (hg : g.toRingHom = canonicalMap f)
    (J : WeakIdealOfDefinitionIndex R)
    (hJK : J.1 ≤ Ideal.comap g.toRingHom (kerProjectionIdeal f J).1) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (g.stageMap J (kerProjectionIdeal f J) hJK))) := by
  change AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap (kerProjectionIdeal f J).1 g.toRingHom hJK)))
  exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale.{u})).mpr
    (etale_quotientMap_kerProjectionIdeal_of_eq f hf g.toRingHom hg J hJK)

variable (hR : IsWeaklyAdmissible R)

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] in
/-- The relative completion of an étale algebra is a finite type algebra, so the statements of
Stacks 0ANM about relative completions along finite type ring maps apply to it. -/
theorem finiteType_of_etale (f : R →+* A) (hf : f.Etale) : f.FiniteType := by
  let : Algebra R A := f.toAlgebra
  have : Algebra.Etale R A := hf
  exact (inferInstance : Algebra.FiniteType R A)

/-- **Stacks 0AKN for the completion of an étale algebra.** Every represented base change of
`Spf A^∧ ⟶ Spf R` is an affine morphism of the site: both formal spectra are affine formal
algebraic spaces and the morphism is representable by algebraic spaces by Stacks 0ANM. -/
theorem relative_isAffineHom_formalSpectrumMap_completionOver (f : R →+* A) (hf : f.FiniteType)
    (D : QuotientSystem B S hS R) (hD : D.HasLargeSite)
    (E : QuotientSystem B S hS (CompletionOver f)) (g : ContinuousHom D E)
    (hg : g.toRingHom = canonicalMap f) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (formalSpectrumMap hR g) :=
  relative_isAffineHom_of_hasThickeningPresentation B S hS (formalSpectrumMap hR g)
    (isAffineFormalAlgebraicSpace_formalSpectrum (completionOver_isWeaklyAdmissible f hR) E
      (hasLargeSite_completionOver_of_finiteType B S hS f hf hD E)).2
    (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD).2
    (isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_completionOver f hR hf D E g hg)

/-- **Stacks 0AN8, the étaleness of the functor.** Every represented base change of
`Spf A^∧ ⟶ Spf R`, for `f : R →+* A` étale, is an étale morphism of the site.

Étaleness is Zariski-local at the target, so by
`AlgebraicGeometry.FormalSpace.relative_of_compact_tests` it suffices to test at points of
`Spf R` out of quasi-compact objects of the site. Such a point factors through a quotient stage
by Stacks 0AIA, and over a stage the base change is the one of Stacks 0ANM, whose projection is
the étale stage map `Spec (A^∧ ⧸ ker) ⟶ Spec (R ⧸ J)`. -/
theorem relative_etale_formalSpectrumMap_completionOver (f : R →+* A) (hf : f.Etale)
    (D : QuotientSystem B S hS R) (hD : D.HasLargeSite)
    (E : QuotientSystem B S hS (CompletionOver f)) (g : ContinuousHom D E)
    (hg : g.toRingHom = canonicalMap f) :
    (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (formalSpectrumMap hR g) := by
  classical
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have := preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.respectsIso
  have : IsZariskiLocalAtTarget (@AlgebraicGeometry.Etale.{u}) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget
      (@AlgebraicGeometry.Etale.{u}) (Q := @RingHom.Etale)
  refine relative_of_compact_tests B S hS (@AlgebraicGeometry.Etale.{u})
    (formalSpectrumMap hR g)
    (relative_isAffineHom_formalSpectrumMap_completionOver hR f
      (finiteType_of_etale f hf) D hD E g hg).rep fun T W hT t a q hpb ↦ ?_
  obtain ⟨J, pJ, hpJ⟩ := exists_factorsThroughStage_of_compactSpace hR.1 D T hT t
  have hJK : J.1 ≤ Ideal.comap g.toRingHom (kerProjectionIdeal f J).1 :=
    le_comap_kerProjectionIdeal f g hg J
  have hinner := IsPullback.of_hasPullback
    ((BigAffineFppf.inclusion B S hS).map (g.stageMap J (kerProjectionIdeal f J) hJK)) pJ
  have hother := (hinner.map
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))).paste_horiz
    (isPullback_formalSpectrumMap_kerProjection f hR g hg J hJK).flip
  rw [show (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map pJ ≫
    formalSpectrumInclusion D (OrderDual.toDual J) = t from hpJ] at hother
  exact prop_toScheme_map_of_isPullback_of_isPullback B S hS (@AlgebraicGeometry.Etale.{u}) hpb
    hother (MorphismProperty.of_isPullback (hinner.map (BigFppfOver.toScheme B S hS))
      (etale_toScheme_map_stageMap_kerProjectionIdeal f hf g hg J hJK))

/-- **Stacks 0AN8: both conditions of Definition 0AIM for the formal spectrum of the completion
of an étale algebra.** For an étale ring map `f : R →+* A`, the morphism `Spf A^∧ ⟶ Spf R` is
representable by algebraic spaces and étale. These are conditions (1) and (2) that an object of
the category of Stacks 0DEE has to satisfy over `Spf R`.

Representability by algebraic spaces is Stacks 0ANM, in the form
`isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_completionOver`, an étale ring map being
of finite type by `finiteType_of_etale`. The étaleness condition of Definition 0AIM is the
relative étaleness of `relative_etale_formalSpectrumMap_completionOver` read through
`isRepresentableEtale_of_relative_etale'`: the two differ only in whether the base change is
tested at the objects of the site or at the universe-lifted scheme-valued points of the target,
and for a morphism representable by objects of the site — which this one is, by Stacks 0AKN in
the form `relative_isAffineHom_formalSpectrumMap_completionOver` — those agree. -/
theorem isRepresentableEtale_formalSpectrumMap_completionOver (f : R →+* A) (hf : f.Etale)
    (D : QuotientSystem B S hS R) (hD : D.HasLargeSite)
    (E : QuotientSystem B S hS (CompletionOver f)) (g : ContinuousHom D E)
    (hg : g.toRingHom = canonicalMap f) :
    IsRepresentableEtale B S hS (formalSpectrumMap hR g) :=
  isRepresentableEtale_of_relative_etale' B S hS (formalSpectrumMap hR g)
    (relative_etale_formalSpectrumMap_completionOver hR f hf D hD E g hg)

attribute [local instance] sheaf_hasColimits

omit [IsTopologicalRing R] [IsLinearTopology R R] in
/-- **Two representable étale morphisms to a formal spectrum with a common base change to one
quotient stage are isomorphic over the formal spectrum.**

The weak ideals of definition contained in the chosen one are cofinal among all of them, so the
quotient stages they index already present `Spf R` as a colimit of thickenings of objects of the
site, with the chosen stage least; the statement is then
`AlgebraicGeometry.FormalSpace.exists_iso_of_isPullback_least_stage`. The containment has to be
spelled out at the level of ideals: writing `J₀ ≤ J` in the index of the presentation, which is
ordered by reverse inclusion, names the ideals *containing* `J₀`. -/
theorem exists_iso_of_isPullback_stage (D : QuotientSystem B S hS R)
    (J₀ : WeakIdealOfDefinitionIndex R)
    {X Z : FppfSheaf B S hS} (p : X ⟶ formalSpectrum D) (q : Z ⟶ formalSpectrum D)
    (hpEt : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) p)
    (hqEt : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q)
    {N : FppfSheaf B S hS}
    {n₀ : N ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.stage J₀))}
    {nX : N ⟶ X} {nZ : N ⟶ Z}
    (hX : IsPullback nX n₀ p (formalSpectrumInclusion D J₀))
    (hZ : IsPullback nZ n₀ q (formalSpectrumInclusion D J₀)) :
    ∃ t : X ≅ Z, p = t.hom ≫ q := by
  let I := WeakIdealsBelow R J₀
  let ι := weakIdealsBelowInclusion R J₀
  have := nonempty_weakIdealsBelow R J₀
  have := isDirectedOrder_weakIdealsBelow R J₀
  let P₀ : I ⥤ BigFppfOver B S hS := ι ⋙ D.diagram ⋙ BigAffineFppf.inclusion B S hS
  let cι : (P₀ ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ⟶
      (Functor.const I).obj (formalSpectrum D) :=
    { app := fun i ↦ formalSpectrumInclusion D i.1
      naturality := fun i j g ↦ by
        change (formalSpectrumDiagram D).map (ι.map g) ≫
          formalSpectrumInclusion D j.1 = formalSpectrumInclusion D i.1 ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w (formalSpectrumDiagram D) (ι.map g) }
  have hcw : IsColimit ((colimit.cocone (formalSpectrumDiagram D)).whisker ι) :=
    (Functor.Final.isColimitWhiskerEquiv ι _).symm (colimit.isColimit _)
  have hcc : IsColimit (Cocone.mk (formalSpectrum D) cι) :=
    hcw.ofIsoColimit (Cocone.ext (Iso.refl _) fun i ↦ Category.comp_id _)
  have hc : IsUniversalColimit (Cocone.mk (formalSpectrum D) cι) :=
    (sheaf_filteredColimit_isUniversalColimit (BigFppfOver.topology B S hS)
      (P₀ ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))).of_iso
      ((colimit.isColimit _).uniqueUpToIso hcc)
  exact exists_iso_of_isPullback_least_stage B S hS (⟨OrderDual.toDual J₀, le_rfl⟩ : I)
    (fun i ↦ i.2) P₀ (fun _ _ g ↦ quotientSystem_transition_isThickening' D (leOfHom (ι.map g)))
    (Cocone.mk (formalSpectrum D) cι) hc p q hpEt hqEt hX hZ

end Completion

end AlgebraicGeometry.FormalSpace

end
