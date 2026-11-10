module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence

/-!
# Dominating a quasi-compact étale scheme by the base change of an affine one

Let `f : X ⟶ Y` be a universal homeomorphism and let `p : U ⟶ X` be étale with `U`
quasi-compact. Then there is an **affine** scheme `W` étale over `Y` and a surjection
`W ×_Y X ⟶ U` over `X`.

Property (C) for `f`, [Stacks, Tag 04DW], already produces a scheme `V` étale over `Y` and a
surjection `V ×_Y X ⟶ U` over `X`; what is added here is that `V` may be taken affine. The
surjection is étale, hence an open map, so the images of the open subschemes of `V ×_Y X` lying
over the affine opens of `V` cover `U`; finitely many of them suffice because `U` is
quasi-compact, and the coproduct of the corresponding affine opens of `V` is an affine scheme
étale over `Y` which still dominates `U`.

This is the first step of the inductive argument in the second proof of Stacks Project,
Tag 04DZ, where the induction hypothesis is applied to a scheme over `W ×_Y X` and therefore
needs `W` affine.

## Main results

* `Stacks.Etale.isPullback_of_comp_mono` — a morphism which factors through a monomorphism is
  the base change of itself along that monomorphism.
* `Stacks.Etale.isClosedEmbedding_of_universalHomeomorphism` — a universal homeomorphism is a
  homeomorphism onto a closed subset, which is the hypothesis under which this library proves
  property (C).
* `Stacks.Etale.exists_isAffine_etale_dominating` — the statement above.

## Implementation notes

Property (C) is stated with the fibre product written `X ×_Y V`, with `X` in the first slot; the
statement here uses the other orientation, which is the one the rest of the topological-invariance
development uses, so a symmetry isomorphism intervenes.

The comparison between the fibre product of the coproduct and the fibre product of `V` is
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, which identifies `W ×_Y X` with
`W ×_V (V ×_Y X)`; surjectivity is then read off a point of a fibre product above a prescribed
pair of points.

## References

* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **A morphism factoring through a monomorphism does so by a cartesian square.** If
`p' ≫ ι = p` with `ι` a monomorphism, then `p'` is the base change of `p` along `ι`: the
projection `U ×_X V ⟶ U` is a monomorphism, because `ι` is, and a split epimorphism, because `p`
factors through `ι`, hence an isomorphism.

This is what transfers to `p'` every property of `p` which is stable under base change — being
affine, being étale, and a bound on the degrees of the fibres. -/
theorem isPullback_of_comp_mono {U V : Scheme.{u}} (p : U ⟶ X) (ι : V ⟶ X) [Mono ι]
    (p' : U ⟶ V) (h : p' ≫ ι = p) : IsPullback (𝟙 U) p' p ι := by
  have hc : (𝟙 U) ≫ p = p' ≫ ι := by rw [Category.id_comp, h]
  have hmono : Mono (pullback.fst p ι) := pullback.fst_of_mono
  have hsplit : IsSplitEpi (pullback.fst p ι) :=
    IsSplitEpi.mk' ⟨pullback.lift (𝟙 U) p' hc, pullback.lift_fst _ _ _⟩
  have hiso : IsIso (pullback.fst p ι) := isIso_of_mono_of_isSplitEpi _
  have hinv : pullback.lift (𝟙 U) p' hc = inv (pullback.fst p ι) := by
    rw [← Category.comp_id (pullback.lift (𝟙 U) p' hc), ← IsIso.hom_inv_id (pullback.fst p ι),
      ← Category.assoc, pullback.lift_fst, Category.id_comp]
  refine IsPullback.of_iso_pullback ⟨hc⟩ (asIso (pullback.fst p ι)).symm ?_ ?_
  · simp
  · change inv (pullback.fst p ι) ≫ pullback.snd p ι = p'
    rw [← hinv, pullback.lift_snd]

/-- A universal homeomorphism is a homeomorphism onto a closed subset of its target: it is a
homeomorphism, so an embedding with closed image. -/
theorem isClosedEmbedding_of_universalHomeomorphism (f : X ⟶ Y) [UniversalHomeomorphism f] :
    Topology.IsClosedEmbedding f.base :=
  have hf : IsHomeomorph f.base :=
    UniversalHomeomorphism.universally_isHomeomorph _ _ _ .of_id_snd
  ⟨hf.isEmbedding, hf.isClosedMap.isClosed_range⟩

/-- **A quasi-compact étale scheme is dominated by the base change of an affine one.** Let
`f : X ⟶ Y` be a universal homeomorphism and let `p : U ⟶ X` be étale with `U` quasi-compact.
There is an affine scheme `W` étale over `Y` and a surjection `W ×_Y X ⟶ U` over `X`.

This is property (C) of Stacks Project, Tag 04DW with the dominating scheme taken affine, which
is what the induction in the second proof of Stacks Project, Tag 04DZ consumes. -/
theorem exists_isAffine_etale_dominating (f : X ⟶ Y) [UniversalHomeomorphism f]
    {U : Scheme.{u}} (p : U ⟶ X) [Etale p] [CompactSpace U] :
    ∃ (W : Scheme.{u}) (w : W ⟶ Y) (_ : Etale w) (_ : IsAffine W) (h : pullback w f ⟶ U),
      Surjective h ∧ h ≫ p = pullback.snd w f := by
  classical
  obtain ⟨hint, -, -⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance
  have : IsIntegralHom f := hint
  obtain ⟨V₁, v₁, hv₁, h₀, hh₀surj, hh₀⟩ :=
    EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding f
      (isClosedEmbedding_of_universalHomeomorphism f) p inferInstance
  have : Etale v₁ := hv₁
  have : Surjective h₀ := hh₀surj
  -- the same domination in the orientation the rest of the development uses
  have hh₁ : ((pullbackSymmetry v₁ f).hom ≫ h₀) ≫ p = pullback.snd v₁ f := by
    rw [Category.assoc, hh₀, pullbackSymmetry_hom_comp_fst]
  have : Surjective ((pullbackSymmetry v₁ f).hom ≫ h₀) := inferInstance
  have : Etale (pullback.snd v₁ f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback v₁ f) inferInstance
  have hEt₁ : Etale ((pullbackSymmetry v₁ f).hom ≫ h₀) := by
    have : Etale (((pullbackSymmetry v₁ f).hom ≫ h₀) ≫ p) := by rw [hh₁]; infer_instance
    exact Etale.of_comp (f := (pullbackSymmetry v₁ f).hom ≫ h₀) (g := p)
  -- the images of the pieces of `V₁ ×_Y X` over the affine opens of `V₁` cover `U`
  set h₁ : pullback v₁ f ⟶ U := (pullbackSymmetry v₁ f).hom ≫ h₀ with hh₁def
  set S : V₁.affineOpens → Set U := fun A ↦
    h₁.base '' ((pullback.fst v₁ f ⁻¹ᵁ A.1 : (pullback v₁ f).Opens) : Set _) with hSdef
  have hSopen : ∀ A, IsOpen (S A) :=
    fun A ↦ h₁.isOpenMap _ (pullback.fst v₁ f ⁻¹ᵁ A.1 : (pullback v₁ f).Opens).2
  have hcov : (Set.univ : Set U) ⊆ ⋃ A : V₁.affineOpens, S A := by
    intro u _
    obtain ⟨z, hz⟩ := ‹Surjective h₁›.1 u
    obtain ⟨A, hA, hzA, -⟩ := exists_isAffineOpen_mem_and_subset (X := V₁)
      (x := (pullback.fst v₁ f).base z) (U := ⊤) (TopologicalSpace.Opens.mem_top _)
    exact Set.mem_iUnion.2 ⟨⟨A, hA⟩, ⟨z, hzA, hz⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover S hSopen hcov
  -- the affine scheme étale over `Y` built from a finite subfamily
  set Xs : {A : V₁.affineOpens // A ∈ s} → Scheme.{u} :=
    fun j ↦ (j.1.1 : V₁.Opens).toScheme with hXsdef
  set c : (∐ Xs) ⟶ V₁ := Sigma.desc fun j ↦ (j.1.1 : V₁.Opens).ι with hcdef
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  have hcEt : Etale c := IsZariskiLocalAtSource.sigmaDesc fun j ↦ inferInstance
  refine ⟨∐ Xs, c ≫ v₁, inferInstance, inferInstance,
    (pullbackRightPullbackFstIso v₁ f c).inv ≫ pullback.snd c (pullback.fst v₁ f) ≫ h₁,
    ⟨?_⟩, ?_⟩
  · -- surjectivity
    intro u
    obtain ⟨A, hAs, z, hzA, hzu⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ u))
    have hci : Sigma.ι Xs ⟨A, hAs⟩ ≫ c = (A.1 : V₁.Opens).ι := by
      rw [hcdef]
      exact Sigma.ι_comp_desc _ _
    have hcy : c.base ((Sigma.ι Xs ⟨A, hAs⟩).base ⟨(pullback.fst v₁ f).base z, hzA⟩)
        = (pullback.fst v₁ f).base z := by
      have hap := congrArg (fun m : Xs ⟨A, hAs⟩ ⟶ V₁ ↦
        m.base ⟨(pullback.fst v₁ f).base z, hzA⟩) hci
      exact hap
    obtain ⟨r, -, hr₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := c) (g := pullback.fst v₁ f) ((Sigma.ι Xs ⟨A, hAs⟩).base
        ⟨(pullback.fst v₁ f).base z, hzA⟩) z hcy
    refine ⟨(pullbackRightPullbackFstIso v₁ f c).hom.base r, ?_⟩
    have hcomp : (pullbackRightPullbackFstIso v₁ f c).hom ≫
        (pullbackRightPullbackFstIso v₁ f c).inv ≫ pullback.snd c (pullback.fst v₁ f) ≫ h₁
        = pullback.snd c (pullback.fst v₁ f) ≫ h₁ := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    refine Eq.trans ?_ hzu
    change ((pullbackRightPullbackFstIso v₁ f c).hom ≫
      (pullbackRightPullbackFstIso v₁ f c).inv ≫ pullback.snd c (pullback.fst v₁ f) ≫
        h₁).base r = h₁.base z
    rw [hcomp]
    change h₁.base ((pullback.snd c (pullback.fst v₁ f)).base r) = h₁.base z
    rw [hr₂]
  · -- the morphism lies over `X`
    rw [Category.assoc, Category.assoc, hh₁, ← pullbackRightPullbackFstIso_hom_snd v₁ f c,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Stacks.Etale

end

end
