module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumHomEquiv
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperValuativeLifting
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap

/-!
# Naturality of the comparison `Spf (A^∧) ⟶ X_{/V(I)}` in a ring map

Let `S` be a scheme contained in a big fppf site `B`, let `φ : A ⟶ C` be a homomorphism of
rings whose spectra lie in that site, let `I ⊆ A` be an ideal and let `I' ⊆ C` be an ideal
containing the extension `IC`. Then `Spec C ⟶ Spec A` carries `V(I')` into `V(I)`, so it
induces a morphism of completions `(Spec C)_{/V(I')} ⟶ (Spec A)_{/V(I)}`, while a continuous
homomorphism `g : A^∧ ⟶ C^∧` of the adic completions lifting `φ` induces a morphism of formal
spectra `Spf (C^∧) ⟶ Spf (A^∧)` in the same variance.

`AlgebraicGeometry.FormalSpace.completionComparison` relates the two columns, and
`AlgebraicGeometry.FormalSpace.isIso_completionComparison` (**Stacks 0GBA (2)**) says that each
of them is an isomorphism. What is proved here is that the square they form commutes: the chart
identification of Stacks 0GBA (2) is natural in a ring map, so a chart square of a completed
morphism of affine schemes *is* the formal spectrum of a map of adic completions.

## Main results

* `AlgebraicGeometry.FormalSpace.completionComparison_naturality`: the naturality square, in
  the form that composes, using `AlgebraicGeometry.Space.completionSheafRestrict` for the
  morphism of completions.
* `AlgebraicGeometry.FormalSpace.completionComparison_naturality_completionSheafMap`: the same
  square for `I' = IC`, where the set of points of `Spec C` being completed along *is* the
  inverse image of `V(I)`, so that the morphism of completions is the one of Stacks 0AMC,
  `AlgebraicGeometry.Space.completionSheafMap`, up to the transport along that equality of sets
  of points. This is the form in which the square is consumed.
* `AlgebraicGeometry.FormalSpace.completionComparison_naturality_adicCompletionMap`: the square
  for the *canonical* lift of `φ`, so that no continuous homomorphism of the completions need be
  supplied at all. The lift is
  `AlgebraicGeometry.FormalSpace.adicCompletionContinuousHom`, built on `adicCompletionMap` and
  continuous by `AlgebraicGeometry.FormalSpace.continuous_adicCompletionMap`.
* `AlgebraicGeometry.FormalSpace.zeroLocusPoints_map_eq_preimage_zeroLocusPoints`: the points of
  `Spec C` supported on `V(IC)` are exactly those lying over points of `Spec A` supported on
  `V(I)`.

## Implementation notes

The hypothesis `hg` of the general form says that `g` lifts `φ`, that is, that
`g ∘ (A → A^∧) = (C → C^∧) ∘ φ`; it is what the square needs and all that it needs, and for the
canonical lift it is `adicCompletionMap_comp_algebraMap`. Weak admissibility of `A^∧`, and the
topological ring and linear topology instances for its `I`-adic module topology, are hypotheses,
as they are wherever the formal spectrum of an adic completion is used: they hold for a finitely
generated `I`, by `AlgebraicGeometry.FormalSpace.isWeaklyAdmissible_adicCompletion` together
with `AlgebraicGeometry.FormalSpace.adicCompletionLimitTopology_eq_adicModuleTopology`.

The morphism `Spec C ⟶ Spec A` of site objects over `S` is carried as a variable `specMap`
together with the hypothesis `hspec` that it is `AlgebraicGeometry.Space.specSiteObjectMap`,
rather than written as that term. The reason is that the statements here all name the site
object through `AlgebraicGeometry.FormalSpace.affineOver`, since that is the presentation
`AlgebraicGeometry.FormalSpace.zeroLocusPoints` uses, whereas
`AlgebraicGeometry.Space.specSiteObjectMap` is typed through `AlgebraicGeometry.siteObject`:
the same object by definition, but only one of the two spellings can be the one a given
statement is elaborated in. Consumers supply `rfl`.

For the same reason the proofs below are written with `Eq.trans` and `congrArg` rather than
`rw`: a statement about `AlgebraicGeometry.FormalSpace.zeroLocusPoints` is type-correct only
once `AlgebraicGeometry.FormalSpace.affineOver` is unfolded, which the rewrite tactic's
transparency does not do, so `rw` reports its pattern as absent on goals where it plainly
occurs. This is the style of `AlgebraicGeometry.FormalSpace.completionComparison_overAffine`
and its neighbours.

No Stacks tag is registered here. Stacks 0GBA (2) asserts the identification of `X_{/T}` with
`Spf (A^∧)`, which `AlgebraicGeometry.FormalSpace.isIso_completionComparison` carries; its
compatibility with a ring map is a step in the proofs that consume it, not a clause of it.

## References

* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

/-- The adic topology of the `K`-adic completion of `R` as an `R`-module. -/
local instance adicCompletionAdicModuleTopology {R : Type u} [CommRing R] (K : Ideal R) :
    TopologicalSpace (AdicCompletion K R) :=
  K.adicModuleTopology (AdicCompletion K R)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C : Type u} [CommRing A] [CommRing C]
  (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
  (f : Spec (.of A) ⟶ S) (φ : A →+* C) (I : Ideal A) (I' : Ideal C)
  (specMap : affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) ⟶
    affineOver B S hS hA f)

/-! ### The zero locus of the extended ideal -/

/-- A point of `Spec C` supported on `V(I')` lies over a point of `Spec A` supported on `V(I)`,
whenever the extension `IC` of `I` is contained in `I'`. -/
theorem zeroLocusPoints_subset_preimage_zeroLocusPoints
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f) (hII' : I.map φ ≤ I') :
    zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' ⊆
      Space.pointsMap B S hS
          (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)))
          (yoneda.map specMap) ⁻¹'
        zeroLocusPoints B S hS hA f I := by
  subst hspec
  intro x hx q hq
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hr : Space.schemePoint B S hS (affineOver B S hS hA f) q =
      PrimeSpectrum.comap φ (Space.schemePoint B S hS
        (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)) p) :=
    (congrArg (Space.pointsToScheme B S hS (affineOver B S hS hA f)) hq).trans
      (Space.pointsToScheme_pointsMap B S hS (Space.specSiteObjectMap φ hA hC f) (Quot.mk _ p))
  exact Set.mem_of_eq_of_mem hr fun a ha => hx p rfl (hII' (Ideal.mem_map_of_mem φ ha))

/-- The points of `Spec C` supported on `V(IC)` are exactly those lying over points of `Spec A`
supported on `V(I)`: a prime of `C` contains `IC` exactly when its contraction contains `I`. -/
theorem zeroLocusPoints_map_eq_preimage_zeroLocusPoints
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f) :
    zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) (I.map φ) =
      Space.pointsMap B S hS
          (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)))
          (yoneda.map specMap) ⁻¹'
        zeroLocusPoints B S hS hA f I := by
  refine Set.Subset.antisymm
    (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I (I.map φ) specMap hspec
      le_rfl) ?_
  subst hspec
  intro x hx p hp
  have hmem : PrimeSpectrum.comap φ (Space.schemePoint B S hS
        (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)) p) ∈
      PrimeSpectrum.zeroLocus (I : Set A) :=
    Set.mem_of_eq_of_mem
      (Space.schemePoint_map_yoneda B S hS (Space.specSiteObjectMap φ hA hC f) p).symm
      (hx (Space.FieldValuedPoint.map B S hS
            (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)))
            (yoneda.map (Space.specSiteObjectMap φ hA hC f)) p)
        (congrArg (Space.pointsMap B S hS
          (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)))
          (yoneda.map (Space.specSiteObjectMap φ hA hC f))) hp))
  exact Ideal.map_le_iff_le_comap.mpr fun a ha => hmem ha

/-! ### The canonical lift of a ring map to the adic completions -/

/-- The `I`-adic module topology on `M` makes it a topological additive group. -/
private theorem isTopologicalAddGroup_adicModuleTopology {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    @IsTopologicalAddGroup M (I.adicModuleTopology M) _ :=
  letI := I.adicTopology
  (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis
    |>.isTopologicalAddGroup

/-- The submodules `I ^ n • ⊤` form a neighbourhood basis of zero for the `I`-adic module
topology on `M`. -/
private theorem hasBasis_nhds_zero_adicModuleTopology {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    letI := I.adicTopology
    @Filter.HasBasis M (Set M) (@nhds M (I.adicModuleTopology M) 0)
      (· ∈ (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis)
        id :=
  letI := I.adicTopology
  (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis
    |>.nhds_zero_hasBasis

/-- The induced map of adic completions is continuous for the adic module topologies: it
carries the extension of `I ^ n` to `A^∧` into the extension of `I' ^ n` to `C^∧`, because it
agrees with `φ` on the images of `A` and `C`. -/
theorem continuous_adicCompletionMap (hII' : I.map φ ≤ I') :
    @Continuous (AdicCompletion I A) (AdicCompletion I' C)
      (I.adicModuleTopology (AdicCompletion I A))
      (I'.adicModuleTopology (AdicCompletion I' C))
      (adicCompletionMap φ I I' hII') := by
  have key : ∀ n : ℕ, ∀ x ∈ (I ^ n • (⊤ : Submodule A (AdicCompletion I A)) :
      Submodule A (AdicCompletion I A)),
      adicCompletionMap φ I I' hII' x ∈
        (I' ^ n • (⊤ : Submodule C (AdicCompletion I' C)) :
          Submodule C (AdicCompletion I' C)) := by
    intro n x hx
    rw [Ideal.smul_top_eq_map] at hx ⊢
    have hle : Ideal.map (adicCompletionMap φ I I' hII')
        (Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ n)) ≤
          Ideal.map (algebraMap C (AdicCompletion I' C)) (I' ^ n) := by
      rw [Ideal.map_map, adicCompletionMap_comp_algebraMap, ← Ideal.map_map]
      exact Ideal.map_mono (by rw [Ideal.map_pow]; exact pow_le_pow_left' hII' n)
    exact hle (Ideal.mem_map_of_mem (adicCompletionMap φ I I' hII') hx)
  have := isTopologicalAddGroup_adicModuleTopology I (AdicCompletion I A)
  have := isTopologicalAddGroup_adicModuleTopology I' (AdicCompletion I' C)
  refine continuous_of_continuousAt_zero
    (adicCompletionMap φ I I' hII').toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((hasBasis_nhds_zero_adicModuleTopology I (AdicCompletion I A)).tendsto_iff
    (hasBasis_nhds_zero_adicModuleTopology I' (AdicCompletion I' C))).2 ?_
  rintro V ⟨n, rfl⟩
  exact ⟨_, ⟨n, rfl⟩, key n⟩

/-! ### The naturality square -/

/-- If `g ∘ α = β ∘ ψ`, then the map of quotients induced by `g` commutes with the composites of
`α` and `β` with the quotient maps. -/
private theorem _root_.Ideal.quotientMap_comp_mk_comp_of_comp_eq {R R' P Q : Type*}
    [CommRing R] [CommRing R'] [CommRing P] [CommRing Q] {g : R →+* R'} {α : P →+* R}
    {β : Q →+* R'} {ψ : P →+* Q} (hg : g.comp α = β.comp ψ) (J : Ideal R) (K : Ideal R')
    (h : J ≤ K.comap g) :
    (Ideal.quotientMap K g h).comp ((Ideal.Quotient.mk J).comp α) =
      ((Ideal.Quotient.mk K).comp β).comp ψ := by
  refine RingHom.ext fun a => ?_
  change Ideal.quotientMap K g h (Ideal.Quotient.mk J (α a)) = Ideal.Quotient.mk K (β (ψ a))
  rw [Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk K) (RingHom.congr_fun hg a)

variable (D : AdicQuotientSystem B S hS I)
  (hD : QuotientSystemCompatible B S hS f I D)
  (E : AdicQuotientSystem B S hS I')
  (hE : QuotientSystemCompatible B S hS (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E)

include hD hE in
/-- The continuous homomorphism `A^∧ ⟶ C^∧` of adic completions over `S` induced by
`φ : A ⟶ C`: the induced map of adic completions, which is continuous by
`AlgebraicGeometry.FormalSpace.continuous_adicCompletionMap` and compatible with the structure
morphisms of the two quotient systems because it agrees with `φ` on the images of `A` and
`C`. -/
def adicCompletionContinuousHom (hII' : I.map φ ≤ I') : ContinuousHom D E where
  toRingHom := adicCompletionMap φ I I' hII'
  continuous := continuous_adicCompletionMap φ I I' hII'
  overS J K h := by
    rw [hD J, hE K, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk_comp_of_comp_eq (adicCompletionMap_comp_algebraMap φ I I' hII')
        J.1 K.1 h, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- The quotient stages of the two adic completions commute with the two morphisms to
`Spec A`: on `Spec (C^∧ ⧸ K)` the composite through `Spec C` and the composite through
`Spec (A^∧ ⧸ J)` are the spectrum of one ring map, because `g` lifts `φ`. -/
theorem stageMap_comp_quotientStageToAffine
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (g : ContinuousHom D E)
    (hg : g.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion I' C)).comp φ)
    (J : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L })
    (K : { L : Ideal (AdicCompletion I' C) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I'.adicModuleTopology (AdicCompletion I' C)) L })
    (hJ : J.1 ≤ Ideal.comap g.toRingHom K.1) :
    (BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJ) ≫
        quotientStageToAffine B S hS hA f I D hD J =
      quotientStageToAffine B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K ≫
        specMap := by
  subst hspec
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 g.toRingHom hJ)) ≫
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A)))) =
    Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk K.1).comp (algebraMap C (AdicCompletion I' C)))) ≫
      Spec.map (CommRingCat.ofHom φ)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    Ideal.quotientMap_comp_mk_comp_of_comp_eq hg J.1 K.1 hJ]

/-- On each quotient stage of `C^∧` the canonical section of `(Spec C)_{/V(I')}` is carried by
the morphism of completion subfunctors to the restriction, along the stage map, of the
canonical section of `(Spec A)_{/V(I)}` over the corresponding stage of `A^∧`. This is the
naturality square read on sections. -/
theorem completionSubfunctorRestrict_quotientStage
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (g : ContinuousHom D E)
    (hg : g.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion I' C)).comp φ)
    (hII' : I.map φ ≤ I')
    (J : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L })
    (K : { L : Ideal (AdicCompletion I' C) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I'.adicModuleTopology (AdicCompletion I' C)) L })
    (hJ : J.1 ≤ Ideal.comap g.toRingHom K.1) :
    (Space.completionSubfunctorRestrict B S hS (yoneda.map specMap)
          (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
          (zeroLocusPoints B S hS hA f I)
          (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec
            hII')).app
        (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (E.stage K)))
        ⟨ULift.up (quotientStageToAffine B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E
            hE K),
          quotientStage_hasImageIn B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K⟩ =
      (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor.map
        ((BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJ)).op
        ⟨ULift.up (quotientStageToAffine B S hS hA f I D hD J),
          quotientStage_hasImageIn B S hS hA f I D hD J⟩ :=
  Subtype.ext (ULift.ext (stageMap_comp_quotientStageToAffine B S hS hA hC f φ I I' specMap
    D hD E hE hspec g hg J K hJ).symm)

/-- The morphism of completion subfunctors carries the canonical section of `(Spec C)_{/V(I')}`
over a quotient stage of `C^∧`, sheafified, to the restriction along the stage map of the
canonical section of `(Spec A)_{/V(I)}` over the corresponding stage of `A^∧`. -/
theorem sheafifyMap_completionSubfunctorRestrict_quotientStageSection
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (g : ContinuousHom D E)
    (hg : g.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion I' C)).comp φ)
    (hII' : I.map φ ≤ I')
    (J : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L })
    (K : { L : Ideal (AdicCompletion I' C) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I'.adicModuleTopology (AdicCompletion I' C)) L })
    (hJ : J.1 ≤ Ideal.comap g.toRingHom K.1) :
    ((BigFppfOver.topology B S hS).sheafifyMap
          (Space.completionSubfunctorRestrict B S hS (yoneda.map specMap)
            (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
            (zeroLocusPoints B S hS hA f I)
            (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec
              hII'))).app
        (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (E.stage K)))
        (quotientStageSection B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K) =
      ((BigFppfOver.topology B S hS).sheafify
          (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
            (zeroLocusPoints B S hS hA f I)).toFunctor).map
        ((BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJ)).op
        (quotientStageSection B S hS hA f I D hD J) :=
  ((congrArg
      (fun t => t
        (⟨ULift.up (quotientStageToAffine B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E
            hE K),
          quotientStage_hasImageIn B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K⟩ :
          (Space.completionSubfunctor B S hS
            (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)))
            (zeroLocusPoints B S hS hC
              (Spec.map (CommRingCat.ofHom φ) ≫ f) I')).toFunctor.obj
            (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (E.stage K)))))
      (congrArg
        (fun β => β.app (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (E.stage K))))
        (GrothendieckTopology.toSheafify_naturality (BigFppfOver.topology B S hS)
          (Space.completionSubfunctorRestrict B S hS (yoneda.map specMap)
            (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
            (zeroLocusPoints B S hS hA f I)
            (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec
              hII'))).symm)).trans
    (congrArg
      ((GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
        (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor).app
        (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (E.stage K))))
      (completionSubfunctorRestrict_quotientStage B S hS hA hC f φ I I' specMap D hD E hE hspec
        g hg hII' J K hJ))).trans
    (NatTrans.naturality_apply
      (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
        (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor)
      ((BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJ)).op
      ⟨ULift.up (quotientStageToAffine B S hS hA f I D hD J),
        quotientStage_hasImageIn B S hS hA f I D hD J⟩)

/-- On each quotient stage of `C^∧` the naturality square commutes: the stage's morphism into
`(Spec C)_{/V(I')}` followed by the morphism of completions is the stage map into
`Spec (A^∧ ⧸ J)` followed by that stage's morphism into `(Spec A)_{/V(I)}`. -/
theorem quotientStageToCompletion_comp_completionSheafRestrict
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (g : ContinuousHom D E)
    (hg : g.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion I' C)).comp φ)
    (hII' : I.map φ ≤ I')
    (J : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L })
    (K : { L : Ideal (AdicCompletion I' C) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I'.adicModuleTopology (AdicCompletion I' C)) L })
    (hJ : J.1 ≤ Ideal.comap g.toRingHom K.1) :
    quotientStageToCompletion B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K ≫
        Space.completionSheafRestrict B S hS (yoneda.map specMap)
          (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
          (zeroLocusPoints B S hS hA f I)
          (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec
            hII') =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJ)) ≫
        quotientStageToCompletion B S hS hA f I D hD J := by
  let R := Space.completionSheafRestrict B S hS (yoneda.map specMap)
    (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
    (zeroLocusPoints B S hS hA f I)
    (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec hII')
  let UK := (BigAffineFppf.inclusion B S hS).obj (E.stage K)
  let UJ := (BigAffineFppf.inclusion B S hS).obj (D.stage J)
  let m : UK ⟶ UJ := (BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJ)
  refine (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective ?_
  refine Eq.trans (Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS)
    (quotientStageToCompletion B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K) R) ?_
  refine Eq.trans ?_ (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) m
    (quotientStageToCompletion B S hS hA f I D hD J)).symm
  refine Eq.trans (congrArg (fun s => R.hom.app (Opposite.op UK) s)
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (X := UK)
        (F := Space.completionSheaf B S hS
          (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f)))
          (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I'))).apply_symm_apply
      (quotientStageSection B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K))) ?_
  refine Eq.trans ?_ (congrArg (fun s => (Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)).obj.map m.op s)
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (X := UJ)
        (F := Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I))).apply_symm_apply
      (quotientStageSection B S hS hA f I D hD J))).symm
  exact sheafifyMap_completionSubfunctorRestrict_quotientStageSection B S hS hA hC f φ I I'
    specMap D hD E hE hspec g hg hII' J K hJ

variable [IsTopologicalRing (AdicCompletion I A)]
  [IsLinearTopology (AdicCompletion I A) (AdicCompletion I A)]

/-- The comparison morphism of **Stacks 0GBA (2)** is natural in a ring map: for a homomorphism
`φ : A ⟶ C` of rings whose spectra lie in the site, an ideal `I ⊆ A`, an ideal `I' ⊆ C`
containing `IC`, and a continuous homomorphism `g : A^∧ ⟶ C^∧` of the adic completions lifting
`φ`, the square formed by the two comparison morphisms, the morphism of completions
`(Spec C)_{/V(I')} ⟶ (Spec A)_{/V(I)}` and the morphism of formal spectra
`Spf (C^∧) ⟶ Spf (A^∧)` commutes.

Both comparison morphisms are isomorphisms by
`AlgebraicGeometry.FormalSpace.isIso_completionComparison`, so this identifies the morphism of
completions with the formal spectrum of `g`. -/
theorem completionComparison_naturality
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (hwa : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A))
    (g : ContinuousHom D E)
    (hg : g.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion I' C)).comp φ)
    (hII' : I.map φ ≤ I') :
    completionComparison B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE ≫
        Space.completionSheafRestrict B S hS (yoneda.map specMap)
          (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
          (zeroLocusPoints B S hS hA f I)
          (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec
            hII') =
      formalSpectrumMap hwa g ≫ completionComparison B S hS hA f I D hD := by
  let R := Space.completionSheafRestrict B S hS (yoneda.map specMap)
    (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
    (zeroLocusPoints B S hS hA f I)
    (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec hII')
  refine formalSpectrum_hom_ext E _ fun K => ?_
  obtain ⟨J, hJ⟩ : ∃ J : { L : Ideal (AdicCompletion I A) //
      @TopologicalRing.IsWeakIdealOfDefinition _ _
        (I.adicModuleTopology (AdicCompletion I A)) L },
      J.1 ≤ Ideal.comap g.toRingHom K.1 := by
    obtain ⟨L, hL⟩ := hwa.1
    refine ⟨⟨L ⊓ Ideal.comap g.toRingHom K.1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hL ?_⟩, inf_le_right⟩
    change IsOpen (g.toRingHom ⁻¹' (K.1 : Set (AdicCompletion I' C)))
    exact K.2.1.preimage g.continuous
  let sYm := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
    ((BigAffineFppf.inclusion B S hS).map (g.stageMap J K hJ))
  refine Eq.trans (Category.assoc (formalSpectrumInclusion E (OrderDual.toDual K))
    (completionComparison B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE) R).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ R)
    (completionComparison_stage B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE K)) ?_
  refine Eq.trans (quotientStageToCompletion_comp_completionSheafRestrict B S hS hA hC f φ I I'
    specMap D hD E hE hspec g hg hII' J K hJ) ?_
  refine Eq.trans (congrArg (fun t => sYm ≫ t)
    (completionComparison_stage B S hS hA f I D hD J).symm) ?_
  refine Eq.trans (Category.assoc sYm (formalSpectrumInclusion D (OrderDual.toDual J))
    (completionComparison B S hS hA f I D hD)).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ completionComparison B S hS hA f I D hD)
    (formalSpectrumMap_spec hwa g J K hJ).symm) ?_
  exact Category.assoc (formalSpectrumInclusion E (OrderDual.toDual K)) (formalSpectrumMap hwa g)
    (completionComparison B S hS hA f I D hD)

/-- The naturality square of the comparison morphism of **Stacks 0GBA (2)** for the extended
ideal `I' = IC`, where the set of points of `Spec C` being completed along is literally the
inverse image of `V(I)`, so that the morphism of completions is the one of Stacks 0AMC. This is
the form in which the square is used: it exhibits the chart square of a completed morphism of
affine schemes as the formal spectrum of the induced map of adic completions. -/
theorem completionComparison_naturality_completionSheafMap
    (E' : AdicQuotientSystem B S hS (I.map φ))
    (hE' : QuotientSystemCompatible B S hS (Spec.map (CommRingCat.ofHom φ) ≫ f) (I.map φ) E')
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (hwa : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A))
    (g : ContinuousHom D E')
    (hg : g.toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap C (AdicCompletion (I.map φ) C)).comp φ) :
    completionComparison B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) (I.map φ) E' hE' ≫
        eqToHom (congrArg
          (Space.completionSheaf B S hS
            (yoneda.obj (affineOver B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f))))
          (zeroLocusPoints_map_eq_preimage_zeroLocusPoints B S hS hA hC f φ I specMap hspec)) ≫
        Space.completionSheafMap B S hS (yoneda.map specMap)
          (zeroLocusPoints B S hS hA f I) =
      formalSpectrumMap hwa g ≫ completionComparison B S hS hA f I D hD :=
  (congrArg
      (fun t => completionComparison B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) (I.map φ)
        E' hE' ≫ t)
      (Space.completionSheafRestrict_eq_eqToHom_comp B S hS (yoneda.map specMap)
        (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) (I.map φ))
        (zeroLocusPoints B S hS hA f I)
        (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I (I.map φ) specMap
          hspec le_rfl)
        (zeroLocusPoints_map_eq_preimage_zeroLocusPoints B S hS hA hC f φ I specMap
          hspec))).symm.trans
    (completionComparison_naturality B S hS hA hC f φ I (I.map φ) specMap D hD E' hE' hspec hwa
      g hg le_rfl)

/-- The naturality square of **Stacks 0GBA (2)** for the canonical lift of `φ`: no continuous
homomorphism of the adic completions need be supplied, because `φ` induces one. This is the
form in which the square says that a chart square of a completed morphism of affine schemes
*is* the formal spectrum of the induced map of adic completions. -/
theorem completionComparison_naturality_adicCompletionMap
    (hspec : specMap = Space.specSiteObjectMap φ hA hC f)
    (hwa : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A))
    (hII' : I.map φ ≤ I') :
    completionComparison B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I' E hE ≫
        Space.completionSheafRestrict B S hS (yoneda.map specMap)
          (zeroLocusPoints B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ f) I')
          (zeroLocusPoints B S hS hA f I)
          (zeroLocusPoints_subset_preimage_zeroLocusPoints B S hS hA hC f φ I I' specMap hspec
            hII') =
      formalSpectrumMap hwa (adicCompletionContinuousHom B S hS f φ I I' D hD E hE hII') ≫
        completionComparison B S hS hA f I D hD :=
  completionComparison_naturality B S hS hA hC f φ I I' specMap D hD E hE hspec hwa
    (adicCompletionContinuousHom B S hS f φ I I' D hD E hE hII')
    (adicCompletionMap_comp_algebraMap φ I I' hII') hII'

end AlgebraicGeometry.FormalSpace

end
