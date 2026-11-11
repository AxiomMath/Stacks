module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeRefined
import all StacksFrontier.Topology.Algebra.AdicTopology.FiniteType

/-!
# Finite type morphisms of formal spectra at every scheme-valued point

Let `S` be a scheme contained in a big fppf site `B` and let `φ : A ⟶ C` be a continuous
homomorphism of weakly admissible topological rings over `S`. **Stacks 0ANT** says that
`Spf (φ) : Spf C ⟶ Spf A` is of finite type exactly when `φ` is taut and `C` is topologically
of finite type over `A`. This file proves the implication from the ring condition to the
geometric one, at every scheme-valued point of `Spf A`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPullback_affineFiniteType_formalSpectrumMap_of_isAffine`:
  for a taut `φ` of finite type modulo every weak ideal of definition, the base change of
  `Spf (φ)` along a point of `Spf A` out of an affine object of the site is represented by an
  object of the site, by a morphism which is affine and locally of finite type.
* `AlgebraicGeometry.FormalSpace.isFiniteType_formalSpectrumMap_of_isTaut`: **Stacks 0ANT**,
  the implication (2) ⟹ (1).

## Implementation notes

The source's proof factors a point of `Spf A` out of a quasi-compact scheme through a
thickening stage `Spec (A ⧸ I)` — **Stacks 0AIA**,
`AlgebraicGeometry.FormalSpace.exists_factor_to_affine_stage` for an affine source — and then
computes the base change as `T ×_{Spec (A ⧸ I)} Spec (C ⧸ J(I))`, with `J(I)` the closure of
`φ(I)C`. The cartesian stage square is
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`, which is where
tautness enters, and the ring homomorphism `A ⧸ I ⟶ C ⧸ J(I)` presenting the stage map is of
finite type because `φ` is of finite type modulo every weak ideal of definition. So over an
affine point the base change is an affine morphism of finite type of the site, and the two
properties pass to the base change along the point by stability of each under base change.

Condition (1) of Stacks 0ANT, however, quantifies over *every* scheme-valued point of `Spf A`,
and a point out of a scheme which is not quasi-compact factors through no single stage. The
passage from the affine points to all of them is Zariski locality at the target of being
affine and of being locally of finite type, in the form
`AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges`: the charts over
the affine opens of a test object glue, under a uniform bound on their sizes, which here is
immediate from `AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType` because the charts over
an affine open are affine and of finite type over it. Smallness of the source sheaf, which that
glueing asks for, is the set-theoretic condition of **Stacks 0AIS** for `Spf C`.

That `φ` is of finite type modulo every weak ideal of definition — condition (a) of **Stacks
0ANU** — follows from condition (2) of Stacks 0ANT with no countability hypothesis, by
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType`.

The two formal spectra are assumed to be affine formal algebraic spaces. This is **Stacks
0AIF** for a weakly admissible ring and belongs to the situation of Stacks 0ANT, whose
condition (1) speaks of a finite type morphism of them; in this library it needs the big site
to contain the coproduct of the thickening stages, which is a side condition on the site rather
than a mathematical input, and it is a hypothesis of the library's Stacks 0ANT (1) ⟹ (2) and of
its Stacks 0ANV for the same reason.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- Being affine and locally of finite type respects isomorphisms. -/
private theorem respectsIso_isAffineHom_inf_locallyOfFiniteType :
    MorphismProperty.RespectsIso
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u}) := by
  have _ : MorphismProperty.RespectsIso
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inf _ _

/-- **The base change of a formal spectrum map over an affine point.** Let `φ : A ⟶ C` be a
continuous homomorphism of weakly admissible topological rings over `S` which is taut and of
finite type modulo every weak ideal of definition, and let `U ⟶ Spf A` be a point of the target
out of an affine object of the site. Then the base change of `Spf (φ)` along it is represented
by an object of the site, by a morphism which is affine and locally of finite type.

The point factors through a thickening stage `Spec (A ⧸ I)` by **Stacks 0AIA**, the stage square
is cartesian by tautness, and the stage map is the spectrum of the finite type homomorphism
`A ⧸ I ⟶ C ⧸ J(I)`. -/
theorem exists_isPullback_affineFiniteType_formalSpectrumMap_of_isAffine
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hmod : TopologicalRing.FiniteTypeModuloEveryWeakIdeal f.toRingHom)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E)
      (q : V ⟶ U),
      IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
        (formalSpectrumMap hA f) ξ ∧
      IsAffineHom ((BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) := by
  classical
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let W := BigAffineFppf.inclusion B S hS
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  have _ : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have _ : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  -- Stacks 0AIA: the point factors through a thickening stage.
  obtain ⟨j, g, hg⟩ := exists_factor_to_affine_stage B S hS (formalSpectrum D)
    (WeakIdeals A) D.diagram (fun _ _ k => D.isThickening_map_diagram k) (Iso.refl _)
    ⟨U, hU⟩ ξ
  have hbottom : F.map (W.map g) ≫ formalSpectrumInclusion D (OrderDual.ofDual j) = ξ := by
    rw [← hg]
    exact congrArg (fun h => F.map (W.map g) ≫ h)
      (Category.comp_id (formalSpectrumInclusion D (OrderDual.ofDual j))).symm
  -- The cartesian stage square, with `J(I)` the closure of the extension of `I`.
  obtain ⟨⟨Kv, hKw⟩, hKeq, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hmod.1
      (OrderDual.ofDual j)
  subst hKeq
  -- The stage map is the spectrum of a finite type homomorphism of rings.
  have hPk : (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS))
        (W.map (f.stageMap (OrderDual.ofDual j) ⟨_, hKw⟩ hIK)) := by
    refine ⟨?_, ?_⟩
    · change IsAffineHom (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap _ f.toRingHom hIK)))
      infer_instance
    · change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap _ f.toRingHom hIK)))
      exact HasRingHomProperty.Spec_iff.mpr
        (hmod.2 (OrderDual.ofDual j).1 (OrderDual.ofDual j).2)
  have _ := respectsIso_isAffineHom_inf_locallyOfFiniteType
  have _ : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : MorphismProperty.IsStableUnderBaseChange (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)) :=
    Space.inverseImage_isStableUnderBaseChange B S hS
      (P := (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      MorphismProperty.IsStableUnderBaseChange.inf
  have hrelk := MorphismProperty.relative_map (F := F) hPk
  refine ⟨hrelk.rep.pullback (F.map (W.map g)),
    F.map (hrelk.rep.fst' (F.map (W.map g))) ≫ formalSpectrumInclusion E ⟨_, hKw⟩,
    hrelk.rep.snd (F.map (W.map g)), ?_, (hrelk.property_snd (F.map (W.map g))).1,
    (hrelk.property_snd (F.map (W.map g))).2⟩
  rw [← hbottom]
  exact ((hrelk.rep.isPullback' (F.map (W.map g))).flip.paste_vert hsq.flip).flip

/-- **Stacks 0ANT, the implication (2) ⟹ (1).** Let `φ : A ⟶ C` be a continuous homomorphism of
weakly admissible topological rings over `S` which is taut and such that `C` is topologically of
finite type over `A`. Then `Spf (φ) : Spf C ⟶ Spf A` is of finite type.

The base change of `Spf (φ)` along a point of `Spf A` out of an affine object of the site is an
affine morphism of finite type of the site, and those two properties are Zariski local at the
target, so the charts over the affine opens of an arbitrary test object glue. -/
theorem isFiniteType_formalSpectrumMap_of_isTaut
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hE : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E))
    (htaut : RingHom.IsTaut f.toRingHom)
    (hfin : TopologicalRing.IsTopologicallyOfFiniteType f.toRingHom) :
    IsFiniteType B S hS (formalSpectrumMap hA f) := by
  classical
  let L := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  -- Condition (a) of Stacks 0ANU, with no countability hypothesis.
  have hmod : TopologicalRing.FiniteTypeModuloEveryWeakIdeal f.toRingHom :=
    TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType
      f.toRingHom htaut hfin
  have _ : FunctorToTypes.Small.{u} (formalSpectrum E).obj :=
    CartesianColimit.small_of_setTheoreticCondition B S hS _ hE.1
  have _ := respectsIso_isAffineHom_inf_locallyOfFiniteType
  have _ : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hzlA : IsZariskiLocalAtTarget (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have hzlT : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  -- The affine charts glue, being affine and of finite type over an affine open.
  have hrel : (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (formalSpectrumMap hA f) := by
    refine CartesianColimit.relative_of_affineBaseChanges B S hS _
      (MorphismProperty.IsLocalAtTarget.inf _ _) _ (κ := 0)
      (lt_of_lt_of_le Cardinal.aleph0_pos B.aleph0_lt_cutoff.le) fun U hU ξ => ?_
    obtain ⟨V, p, q, hq, hqa, hqt⟩ :=
      exists_isPullback_affineFiniteType_formalSpectrumMap_of_isAffine B S hS hA hC D E f
        hmod U hU ξ
    refine ⟨V, p, q, hq, ⟨hqa, hqt⟩, ?_⟩
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map q) := hqa
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
      isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map q)
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) := hqt
    exact (Scheme.size_le_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map q)).trans (le_max_right _ _)
  have hrel' := relative_ulift_of_relative_sheaf B S hS
    (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (BigFppfOver.toScheme B S hS)) (formalSpectrumMap hA f) hrel
  refine ⟨isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS hrel'.rep,
    fun U ξ => ?_⟩
  obtain ⟨hqa, hqt⟩ := hrel'.property_snd ξ
  have hinv : (hrel'.rep.isPullback ξ).flip.isoPullback.inv ≫ L.map (hrel'.rep.snd ξ) =
      pullback.fst ξ (formalSpectrumMap hA f).hom :=
    (Iso.inv_comp_eq _).mpr (hrel'.rep.isPullback ξ).flip.isoPullback_hom_fst.symm
  refine ⟨?_, ?_⟩
  · have h2 := Space.holdsOnEveryEtaleChartULift_precomp B S hS
      (@LocallyOfFiniteType.{u}) (hrel'.rep.isPullback ξ).flip.isoPullback.inv
      (L.map (hrel'.rep.snd ξ))
      (Space.isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS (hrel'.rep.snd ξ) hqt)
    rwa [hinv] at h2
  · have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map (hrel'.rep.snd ξ)) := hqa
    have h2 : Space.IsQuasiCompactULift.{u + 1} B S hS
        ((hrel'.rep.isPullback ξ).flip.isoPullback.inv ≫ L.map (hrel'.rep.snd ξ)) :=
      Space.isQuasiCompactULift_precomp B S hS
        (hrel'.rep.isPullback ξ).flip.isoPullback.symm (L.map (hrel'.rep.snd ξ))
        (Space.isQuasiCompactULift_uliftYoneda_map B S hS (hrel'.rep.snd ξ) inferInstance)
    rwa [hinv] at h2

end AlgebraicGeometry.FormalSpace

end
