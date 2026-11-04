module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCompactificationProperExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOverClosureOfMonoLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePointwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteTypeMorphismByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverStratificationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointLiftQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFiniteEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedIdealSheafOfClosedSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsoNearClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
import all StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteLocallyFreeOverOpenBlowup

/-!
# Finite flat étale local rings near the closure of an étale part

Let `S` be a scheme, let `f : X ⟶ Y` be a proper morphism of quasi-compact and quasi-separated
algebraic spaces over `S`, let `V ⊆ Y` be a quasi-compact open subspace with inverse image
`U = f⁻¹(V)`, and let `A ⊆ U` and `Bc ⊆ V` be closed subspaces such that `f` restricts to an
isomorphism `A ≅ Bc` and is étale at every point of `A`.  Stacks 0F48 produces a `V`-admissible
blowup `Y' ⟶ Y` such that the strict transform `f' : X' ⟶ Y'` of `f` has the following property
at every geometric point `ā` of the closure of `|A|` in `|X'|`: there is a quotient
`𝒪_{X', ā} ⟶ 𝒪` onto a local ring such that `𝒪_{Y', f'(ā)} ⟶ 𝒪` is finite and flat.  The ring
`𝒪` is the étale local ring of a further algebraic space `E` at a geometric point over `ā`,
where `E ⟶ Y'` is flat, of finite presentation and quasi-finite there.

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_surjective_finite_flat_etaleLocalRing`:
  Stacks 0F48.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_finite_flat_etaleLocalRing`: without any
  hypothesis on the image of `A` in `V`, the same holds with a local homomorphism
  `𝒪_{X', ā} ⟶ 𝒪` into a local ring in place of a quotient.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isFlat_cover_closure`: the space form of
  the construction, a morphism `p₀ : E ⟶ X'` with `p₀ ≫ f'` flat whose image contains the
  closure of `|A|`; this is the form Stacks 0F4B uses.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_mem_closure_of_isFlat`: a flat morphism locally
  of finite presentation which is quasi-finite over an open is quasi-finite over its closure.
* `AlgebraicGeometry.Space.isOpen_setOf_isEtaleAt`: the étale locus is open.

## Implementation notes

The proof is the source's, with three changes.  Let `T' ⊆ |U|` be the non-étale locus, a closed set
disjoint from `|A|`.  The first change is that the set `T'c` below is also made to contain
`T'' = |f⁻¹(Bc)| ∖ |A|`.  This set is closed in `|U|`: `f⁻¹(Bc) ⟶ Bc` is étale at the points of
`A`, and the composite `Bc ≅ A ⊆ f⁻¹(Bc)` is a section of it, so `A` is open in `f⁻¹(Bc)`; this is
the only use of the isomorphism `A ≅ Bc`.  There are disjoint constructible closed sets `Tc ⊇ |A|`
and `T'c ⊇ T' ∪ T''` in the spectral space `|U|`, and Stacks 0F46 gives a `U`-admissible blowup
`X₁ ⟶ X` in which their closures `K, K'` are disjoint.  The source works over `X₁ ∖ K'`, which need
not be quasi-compact; here `X₁₀` is a quasi-compact open with `K ⊆ X₁₀ ⊆ X₁ ∖ K'`, as in the proof
of Stacks 0F47.  The morphism `g : X₁₀ ⟶ Y` is of finite type, and it is étale over `V`, since
there `X₁₀` lies over `U ∖ T'`; so Stacks 087E applies to it directly and gives a `V`-admissible
blowup `Y' ⟶ Y` such that the strict transform `F₀ : E = X'₁₀ ⟶ Y'` of `g` is flat and of finite
presentation.

The source then cites Stacks 0878 for quasi-finiteness of `F₀`, which needs the inverse image `V'`
of `V` to be dense in `Y'`; it need not be.  Here 0878 is applied after base change to a closed
subspace of `Y'` with underlying set the closure of `|V'|`, in which the trace of `V'` is dense,
and gives quasi-finiteness of `F₀` at every point over that closure
(`AlgebraicGeometry.Space.isQuasiFiniteAt_of_mem_closure_of_isFlat`).

A point of the closure of `|A|` in `|X'|` is the image of a point of the strict transform `X'₁` of
`X₁ ⟶ Y` in the closure of the part over `Tc`, the morphism `X'₁ ⟶ X'` being proper; such a point
lies over `K ⊆ X₁₀`, hence comes from `X'₁₀`, which is the inverse image of `X'₁` over `X₁₀`
(Stacks 0863), and lies over the closure of `|V'|`.  There `X'₁₀ ⟶ X'` is quasi-finite, so the
geometric point lifts (`AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isQuasiFiniteAt`),
and at the lift the map of étale local rings of `F₀` is finite (Stacks 05WR, in the form
`AlgebraicGeometry.Space.finite_etaleLocalRingMap_of_isQuasiFiniteAt`) and flat.

Finally, the source takes `𝒪` to be the étale local ring of `X₁` at a lift of `ā` and does not
say why `𝒪_{X', ā} ⟶ 𝒪` is surjective; this is where `T''` is used.  Over `V` the points of
`X₁₀` over `Bc` lie over `|f⁻¹(Bc)| ∖ T'' = |A|`, and `X₁₀ ⟶ X` is a monomorphism over `U`, so
`E ×_{Y'} Bc ⟶ Bc` factors as a monomorphism into the open `A` of `f⁻¹(Bc)` followed by
`A ≅ Bc`, and is a monomorphism.  The flat, separated morphism `F₀`, locally of finite
presentation, is then étale over the closure of `|Bc|` in `|Y'|`
(`AlgebraicGeometry.Space.isEtaleAt_of_mono_pullback_snd`), which contains `f'(ā)`.  Hence
`𝒪_{Y', f'(ā)} ⟶ 𝒪` is bijective
(`AlgebraicGeometry.Space.bijective_etaleLocalRingMap_of_isEtaleAt`), and as it factors through
`𝒪_{X', ā} ⟶ 𝒪`, the latter is surjective.

## References

* [Stacks Project, Tag 0F48](https://stacks.math.columbia.edu/tag/0F48)
* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0878](https://stacks.math.columbia.edu/tag/0878)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 05WR](https://stacks.math.columbia.edu/tag/05WR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The étale locus -/

/-- **The étale locus of a morphism is open.** -/
theorem isOpen_setOf_isEtaleAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsOpen {x : points B S hS X | IsEtaleAt B S hS f x} := by
  refine isOpen_iff_forall_mem_open.2 fun x ⟨U, hU, x', hx', het⟩ => ?_
  refine ⟨Set.range (pointsMap B S hS U.toFunctor U.ι), ?_,
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hU.2, ⟨x', hx'⟩⟩
  rintro _ ⟨y', rfl⟩
  exact ⟨U, hU, y', rfl, het⟩

/-- **Étaleness at a point is preserved by precomposition with an étale morphism.** -/
theorem isEtaleAt_comp_of_isEtale {N X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hN : IsAlgebraicSpace B S hS N) (hX : IsAlgebraicSpace B S hS X) (ψ : N ⟶ X)
    (hψ : IsEtale B S hS ψ) (f : X ⟶ Y) (n : points B S hS N)
    (h : IsEtaleAt B S hS f (pointsMap B S hS N ψ n)) :
    IsEtaleAt B S hS (ψ ≫ f) n := by
  obtain ⟨U, hU, x', hx', het⟩ := h
  have hN' : IsOpenSubspace B S hS (U.preimage ψ) := isOpenSubspace_preimage B S hS ψ U hX hN hU
  obtain ⟨n', hn'⟩ : n ∈ Set.range (pointsMap B S hS _ (U.preimage ψ).ι) := by
    rw [range_pointsMap_preimage_ι]
    exact ⟨x', hx'⟩
  refine ⟨U.preimage ψ, hN', n', hn', ?_⟩
  rw [← Category.assoc, ← Subfunctor.fromPreimage_ι U ψ, Category.assoc]
  exact isEtale_comp B S hS (isEtale_fromPreimage_of_isOpenSubspace hN hX ψ hψ U hU) het

/-- **A blowup is étale over an open subspace missing its centre**, read on morphisms into the
inverse image of that open: an étale morphism `ν : N ⟶ X₁` landing in `c₁⁻¹(U)` stays étale
after composing with the blowup `c₁ : X₁ ⟶ X`, since `c₁⁻¹(U) ⟶ U` is an isomorphism
(Stacks 085T). -/
theorem isEtale_comp_of_range_le_preimage {X X₁ : AlgebraicSpaces B S hS}
    {Zc : ClosedSubspaces B S hS X.1} {c₁ : X₁ ⟶ X} (hb : IsBlowupAlong B S hS Zc c₁)
    (U : OpenSubspaces B S hS X.1)
    (hUZ : Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Zc.1))
    {N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ν : N ⟶ X₁.1) (hν : IsEtale B S hS ν)
    (hrange : Subfunctor.range ν ≤ U.1.preimage c₁.hom) : IsEtale B S hS (ν ≫ c₁.hom) := by
  set C := openComplementOfClosedSubspace B S hS X Zc
  have hUC : U.1 ≤ C.1 := le_openComplementOfClosedSubspace Zc U hUZ
  have hle : Subfunctor.range ν ≤ C.1.preimage c₁.hom :=
    hrange.trans fun _ _ hx => hUC _ hx
  have := isIso_fromPreimage_openComplement hb
  have hν' : ν = Subfunctor.lift ν hle ≫ (C.1.preimage c₁.hom).ι := (Subfunctor.lift_ι ν hle).symm
  have hlift : IsEtale B S hS (Subfunctor.lift ν hle) :=
    isEtale_of_comp_mono B S hS _ (C.1.preimage c₁.hom).ι (hν' ▸ hν)
  rw [hν', Category.assoc, ← Subfunctor.fromPreimage_ι]
  exact isEtale_comp B S hS hlift (isEtale_comp B S hS (isEtale_of_isIso B S hS _)
    (isEtale_ι_of_isOpenSubspace C.2))

/-- **A blowup is a monomorphism over an open subspace missing its centre**: two morphisms into
the blowup `c₁ : X₁ ⟶ X` which agree after composing with `c₁` and land over `U` are equal, since
`c₁⁻¹(U) ⟶ U` is an isomorphism (Stacks 085T). -/
theorem eq_of_comp_eq_of_range_le_preimage {X X₁ : AlgebraicSpaces B S hS}
    {Zc : ClosedSubspaces B S hS X.1} {c₁ : X₁ ⟶ X} (hb : IsBlowupAlong B S hS Zc c₁)
    (U : OpenSubspaces B S hS X.1)
    (hUZ : Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Zc.1))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w w' : T ⟶ X₁.1) (h : w ≫ c₁.hom = w' ≫ c₁.hom)
    (hrange : Subfunctor.range (w ≫ c₁.hom) ≤ U.1) : w = w' := by
  set C := openComplementOfClosedSubspace B S hS X Zc
  have hUC : U.1 ≤ C.1 := le_openComplementOfClosedSubspace Zc U hUZ
  have := isIso_fromPreimage_openComplement hb
  have hle : ∀ k : T ⟶ X₁.1, Subfunctor.range (k ≫ c₁.hom) ≤ U.1 →
      Subfunctor.range k ≤ C.1.preimage c₁.hom := by
    rintro k hk T' _ ⟨y, rfl⟩
    exact hUC _ (hk _ ⟨y, rfl⟩)
  have hw := hle w hrange
  have hw' := hle w' (h ▸ hrange)
  have hlift : Subfunctor.lift w hw = Subfunctor.lift w' hw' := by
    refine (cancel_mono (C.1.fromPreimage c₁.hom ≫ C.1.ι)).1 ?_
    rw [Subfunctor.fromPreimage_ι, ← Category.assoc, ← Category.assoc, Subfunctor.lift_ι,
      Subfunctor.lift_ι, h]
  rw [← Subfunctor.lift_ι w hw, ← Subfunctor.lift_ι w' hw', hlift]

/-! ### Quasi-finiteness over the closure of a dense open -/

/-- **Quasi-finiteness at a point cancels on the right.**  If `f ≫ g` is quasi-finite at `x`,
then so is `f`: an open neighbourhood of `x` which is locally quasi-finite over the target of
`g` is locally quasi-finite over that of `f` (Stacks 03XN). -/
theorem isQuasiFiniteAt_of_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : points B S hS X) (h : IsQuasiFiniteAt B S hS (f ≫ g) x) :
    IsQuasiFiniteAt B S hS f x := by
  obtain ⟨U, hU, x', hx', hqf⟩ := h
  exact ⟨U, hU, x', hx', isLocallyQuasiFinite_of_comp B S hS hU.1 hY hZ (U.ι ≫ f) g
    (by rwa [Category.assoc])⟩

/-- **A flat morphism locally of finite presentation which is quasi-finite over an open is
quasi-finite over the closure of that open.**  Let `f : X ⟶ Y` be flat and locally of finite
presentation and let `V ⊆ Y` be an open subspace such that `f` is quasi-finite at every point
of `X` over `|V|`.  Then `f` is quasi-finite at every point of `X` over the closure of `|V|`.

Base change to a closed subspace `Z` of `Y` with `|Z|` the closure of `|V|`: there `|V| ∩ |Z|`
is dense, the base change is quasi-finite over it, hence of relative dimension `≤ 0` over all of
`Z` by Stacks 0878, `AlgebraicGeometry.Space.relativeDimensionLE_of_dense_open`, and
quasi-finiteness descends from the base change. -/
theorem isQuasiFiniteAt_of_mem_closure_of_isFlat {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hflat : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (V : OpenSubspaces B S hS Y.1)
    (hqf : ∀ x : points B S hS X.1, pointsMap B S hS _ f.hom x ∈
      subspacePointSet B S hS Y.1 V.1 → IsQuasiFiniteAt B S hS f.hom x)
    (x : points B S hS X.1)
    (hx : pointsMap B S hS _ f.hom x ∈ closure (subspacePointSet B S hS Y.1 V.1)) :
    IsQuasiFiniteAt B S hS f.hom x := by
  have hlft : IsLocallyOfFiniteType B S hS f.hom :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp
  obtain ⟨Z, ⟨hZcl, hZpts, -⟩, -⟩ := existsUnique_reducedClosedSubspace' B S hS Y.2
    (closure (subspacePointSet B S hS Y.1 V.1)) isClosed_closure
  set Zs : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZcl.1⟩
  set ιZ : Zs ⟶ Y := ObjectProperty.homMk Z.ι
  have sqA := AlgebraicSpaces.isPullback_fiberProduct B S hS f ιZ
  have sq : IsPullback (pullback.snd f.hom Z.ι) (pullback.fst f.hom Z.ι) Z.ι f.hom :=
    (IsPullback.of_hasPullback f.hom Z.ι).flip
  set P := AlgebraicSpaces.fiberProduct B S hS f ιZ
  set F := pullback.snd f.hom Z.ι with hF
  have hFflat : IsFlat B S hS F := by
    have _ := isFlat_isStableUnderBaseChange B S hS
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ IsFlat B S hS k.hom) sqA hflat
  have hFlfp : IsLocallyOfFinitePresentation B S hS F := by
    have _ := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦
        IsLocallyOfFinitePresentation B S hS k.hom) sqA hlfp
  have hFlft : IsLocallyOfFiniteType B S hS F :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hFlfp
  -- the open `W = V ∩ Z` of `Z`, which is dense
  set W := V.1.preimage Z.ι
  have hWo : IsOpenSubspace B S hS W := isOpenSubspace_preimage B S hS Z.ι V.1 Y.2 hZcl.1 V.2
  have hWdense : Dense (Set.range (pointsMap B S hS W.toFunctor W.ι)) := by
    have hind := isInducing_pointsMap_of_isImmersion B S hS Y.2 Z.ι
      (isImmersion_of_isClosedImmersion B S hS hZcl.2)
    rw [range_pointsMap_preimage_ι, dense_iff_closure_eq, hind.closure_eq_preimage_closure_image,
      Set.image_preimage_eq_inter_range, hZpts,
      Set.inter_eq_left.2 (subset_closure : subspacePointSet B S hS Y.1 V.1 ⊆ _)]
    exact Set.preimage_eq_univ_iff.2 (by rw [hZpts])
  -- the base change is quasi-finite over `W`
  have hdim : HasRelativeDimensionLE 0 B S hS (pullback.snd F W.ι) := by
    intro w
    refine ⟨0, le_rfl, ?_⟩
    have sq₂ : IsPullback (pullback.snd F W.ι) (pullback.fst F W.ι) W.ι F :=
      (IsPullback.of_hasPullback F W.ι).flip
    have hsndlft : IsLocallyOfFiniteType B S hS (pullback.snd F W.ι) :=
      IsLocallyOfFiniteType.of_isPullback B S hS sq₂ P.2 hZcl.1 hFlft
    have hP₂ : IsAlgebraicSpace B S hS (pullback F W.ι) :=
      isAlgebraicSpace_pullback B S hS F W.ι P.2 hWo.1 hZcl.1
    rw [Nat.cast_zero, ← isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hP₂ hWo.1 _ hsndlft,
      isQuasiFiniteAt_iff_of_isPullback B S hS sq₂ P.2 hZcl.1 hWo.1 hFlft,
      isQuasiFiniteAt_iff_of_isPullback B S hS sq X.2 Y.2 hZcl.1 hlft]
    apply hqf
    rw [← pointsMap_comp_apply, pullback.condition, pointsMap_comp_apply,
      ← pointsMap_comp_apply _ _ _ (pullback.fst F W.ι), ← hF, pullback.condition,
      pointsMap_comp_apply, ← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι V.1 Z.ι,
      pointsMap_comp_apply]
    exact Set.mem_range_self _
  have hFdim := relativeDimensionLE_of_dense_open B S hS P.2 hZcl.1 F W hWo hWdense hFflat
    hFlft 0 hdim (Or.inl hFlfp)
  have hFlqf := isLocallyQuasiFinite_of_hasRelativeDimensionLE_zero B S hS F hFlft hFdim
  obtain ⟨z, hz⟩ : pointsMap B S hS _ f.hom x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
    rwa [hZpts]
  obtain ⟨w, hw₁, -⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback f.hom Z.ι)
    x z hz.symm
  have h : IsQuasiFiniteAt B S hS F w := isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS P.2 hFlqf w
  rwa [isQuasiFiniteAt_iff_of_isPullback B S hS sq X.2 Y.2 hZcl.1 hlft, hw₁] at h

/-! ### Stacks 0F48 -/

/-- **Lifting a geometric point through a quasi-finite point of a flat morphism.**  If `p ≫ F` is
flat, locally of finite presentation and quasi-finite at `a₀`, and `a₀` maps to the image of `abar`,
then `abar` lifts to a geometric point `abar₀` over `a₀` at which the map of étale local rings
`𝒪_{Y', F(abar)} ⟶ 𝒪_{E, abar₀}` is finite and flat. -/
private theorem exists_geometricPoint_lift_finite_flat {E X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hE : IsAlgebraicSpace B S hS E) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y') (p : E ⟶ X') (F : X' ⟶ Y') (hflat : IsFlat B S hS (p ≫ F))
    (hfp : IsLocallyOfFinitePresentation B S hS (p ≫ F)) (abar : GeometricPoint B S hS X')
    (a₀ : points B S hS E) (hpa : pointsMap B S hS _ p a₀ = abar.image)
    (hqf : IsQuasiFiniteAt B S hS (p ≫ F) a₀) :
    ∃ abar₀ : GeometricPoint B S hS E, abar₀.image = a₀ ∧ geometricPointMap p abar₀ = abar ∧
      ((etaleLocalRingMap hE p abar₀).comp
        (etaleLocalRingMap hX' F (geometricPointMap p abar₀))).Finite ∧
      ((etaleLocalRingMap hE p abar₀).comp
        (etaleLocalRingMap hX' F (geometricPointMap p abar₀))).Flat := by
  have hlft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp
  obtain ⟨abar₀, habar₀, hmap⟩ := exists_geometricPoint_lift_of_isQuasiFiniteAt hE hX' p
    (isLocallyOfFiniteType_of_comp B S hS hE hX' hY' p F hlft) abar a₀ hpa
    (isQuasiFiniteAt_of_comp hX' hY' p F a₀ hqf)
  refine ⟨abar₀, habar₀, hmap, ?_⟩
  rw [etaleLocalRingMap_comp hE hX' p F abar₀]
  exact ⟨finite_etaleLocalRingMap_of_isQuasiFiniteAt hE hY' _ hlft abar₀ (habar₀ ▸ hqf),
    (isFlatAt_iff_etaleLocalRingMap_flat hE hY' _ abar₀).1
      (isFlatAt_of_isFlat B S hS _ hflat abar₀.image)⟩

/-- **Morphisms into a strict transform are determined by their two projections**, to the source
and to the blowup. -/
private theorem strictTransformSpace_hom_ext {X A A' : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (b : A' ⟶ A) (E : Subfunctor A'.1) {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (w w' : T ⟶ (strictTransformSpace B S hS f b E).1)
    (hX : w ≫ (strictTransformSpaceι B S hS f b E ≫
      strictTransformPullbackToSource B S hS f b).hom = w' ≫
        (strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToSource B S hS f b).hom)
    (hA : w ≫ (strictTransformSpaceToBlowUp B S hS f b E).hom =
      w' ≫ (strictTransformSpaceToBlowUp B S hS f b E).hom) : w = w' := by
  have : Mono (strictTransformSpaceι B S hS f b E).hom :=
    inferInstanceAs (Mono (strictTransform B S hS f b E).1.ι)
  refine (cancel_mono (strictTransformSpaceι B S hS f b E).hom).1 (pullback.hom_ext ?_ ?_)
  · exact (Category.assoc _ _ _).trans (hX.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (hA.trans (Category.assoc _ _ _).symm)

/-- **The flat cover of Stacks 0F48.**  In the situation of
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_finite_flat_etaleLocalRing`, let moreover
`T'' ⊆ |U|` be a closed set disjoint from `|A|`.  There are a `V`-admissible blowup
`b : Y' ⟶ Y`, with centre `Yc`, and a morphism `p₀ : E ⟶ X'` into the strict transform
`f' : X' ⟶ Y'` of `f`, such that

* `p₀ ≫ f'` is flat, separated and locally of finite presentation,
* no point of `E` lies over `T''` in `X`,
* `p₀` is a monomorphism over `U`: two morphisms into `E` which agree after `p₀`, and whose
  composite to `X` lands in `U`, are equal,
* every point of the closure of the inverse image of `|A|` in `|X'|` is the image of a point of
  `E` at which `p₀ ≫ f'` is quasi-finite.

This is what the proof of Stacks 0F48 constructs: `E` is the strict transform of a quasi-compact
open `X₁₀` of a `U`-admissible blowup of `X` (see the module documentation).  Its flatness over
`Y'` is what Stacks 0F4B uses, with `T'' = ∅`. -/
theorem exists_isAdmissibleBlowup_isFlat_cover_closure
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (V : OpenSubspaces B S hS Y.1) (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (A : ClosedSubspaces B S hS (V.1.preimage f.hom).toFunctor)
    (het : ∀ a : points B S hS A.1.toFunctor,
      IsEtaleAt B S hS f.hom (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι) a))
    (T'' : Set (points B S hS (V.1.preimage f.hom).toFunctor)) (hT'' : IsClosed T'')
    (hAT'' : Disjoint (Set.range (pointsMap B S hS _ A.1.ι)) T'') :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y) (Yc : ClosedSubspaces B S hS Y.1),
      IsAdmissibleBlowup B S hS V b ∧ IsFinitePresentation B S hS Yc.1.ι ∧
        Disjoint (subspacePointSet B S hS Y.1 V.1) (subspacePointSet B S hS Y.1 Yc.1) ∧
          IsBlowupAlong B S hS Yc b ∧
            ∃ (E : AlgebraicSpaces B S hS)
              (p₀ : E ⟶ strictTransformSpace B S hS f b (Yc.1.preimage b.hom)),
              IsFlat B S hS (p₀.hom ≫
                (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom) ∧
              IsLocallyOfFinitePresentation B S hS (p₀.hom ≫
                (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom) ∧
              IsSeparated B S hS (p₀.hom ≫
                (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom) ∧
              (∀ (e : points B S hS E.1) (u : points B S hS (V.1.preimage f.hom).toFunctor),
                pointsMap B S hS _ (V.1.preimage f.hom).ι u = pointsMap B S hS _ (p₀.hom ≫
                  (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom) ≫
                    strictTransformPullbackToSource B S hS f b).hom) e → u ∉ T'') ∧
              (∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (w w' : T ⟶ E.1),
                w ≫ p₀.hom = w' ≫ p₀.hom →
                Subfunctor.range (w ≫ p₀.hom ≫
                  (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom) ≫
                    strictTransformPullbackToSource B S hS f b).hom) ≤ V.1.preimage f.hom →
                w = w') ∧
              ∀ a ∈ closure (pointsMap B S hS _
                  (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom) ≫
                    strictTransformPullbackToSource B S hS f b).hom ⁻¹'
                  Set.range (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι))),
                ∃ a₀ : points B S hS E.1, pointsMap B S hS _ p₀.hom a₀ = a ∧
                  IsQuasiFiniteAt B S hS (p₀.hom ≫
                    (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom) a₀ := by
  classical
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  -- the open `U = f⁻¹(V)` and its topology
  set U : OpenSubspaces B S hS X.1 :=
    ⟨V.1.preimage f.hom, isOpenSubspace_preimage B S hS f.hom V.1 Y.2 X.2 V.2⟩
  have hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS Y.2 X.2 f.hom hf.2.1.2 V.2 hVqc
  have : CompactSpace (points B S hS U.1.toFunctor) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS U.2.1 hUqc
  have hUemb : Topology.IsOpenEmbedding (pointsMap B S hS _ U.1.ι) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS _) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ U.2.2)
  have : QuasiSeparatedSpace (points B S hS X.1) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS X.1 X.2 hXqs
  have : QuasiSeparatedSpace (points B S hS U.1.toFunctor) := hUemb.quasiSeparatedSpace
  have : PrespectralSpace (points B S hS U.1.toFunctor) := prespectralSpace_points B S hS _ U.2.1
  -- the non-étale locus `T'` and the points of `A`
  set Eset := {x : points B S hS X.1 | IsEtaleAt B S hS f.hom x}
  set T' : Set (points B S hS U.1.toFunctor) := pointsMap B S hS _ U.1.ι ⁻¹' Esetᶜ
  have hT' : IsClosed T' :=
    (isOpen_setOf_isEtaleAt f.hom).isClosed_compl.preimage (continuous_pointsMap B S hS _)
  set AU := Set.range (pointsMap B S hS _ A.1.ι)
  have hAU : IsClosed AU := isClosed_range_pointsMap_of_isClosedImmersion B S hS U.2.1 _ A.2.2
  have hAT' : Disjoint AU T' := by
    rintro _ hsub hsub' _ hx
    obtain ⟨a, rfl⟩ := hsub hx
    exact hsub' hx (by
      change IsEtaleAt B S hS f.hom (pointsMap B S hS _ U.1.ι (pointsMap B S hS _ A.1.ι a))
      rw [← pointsMap_comp_apply]
      exact het a)
  obtain ⟨Tc, T'c, hTc, hT'c, hcTc, hcT'c, hAUTc, hT'T'c, hTcT'c⟩ :=
    Topology.exists_isConstructible_isClosed_supersets_of_disjoint hAU (hT'.union hT'')
      (hAT'.union_right hAT'')
  -- the blowup of `X` separating the closures
  obtain ⟨X₁, c₁, ⟨Z₁, hZ₁fp, hZ₁U, hc₁⟩, hsep⟩ :=
    exists_isAdmissibleBlowup_disjoint_closure hZ hXqc hXqs U hUqc Tc T'c hTc hT'c hcTc hcT'c
      hTcT'c
  have hc₁P := isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z₁ c₁ hZ₁fp hc₁
  obtain ⟨hX₁qc, hX₁qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ hXqc hXqs hZ₁fp hc₁
  have : CompactSpace (points B S hS X₁.1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS X₁.2 hX₁qc
  have : QuasiSeparatedSpace (points B S hS X₁.1) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS X₁.1 X₁.2 hX₁qs
  have : PrespectralSpace (points B S hS X₁.1) := prespectralSpace_points B S hS _ X₁.2
  obtain ⟨G, hGc, hGo, hKG, hGK'⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    isClosed_closure.isCompact isClosed_closure.isOpen_compl
    (Set.subset_compl_iff_disjoint_right.2 hsep)
  set X₁₀s := openSubspaceOfPoints B S hS X₁.1 G
  have hX₁₀ : IsOpenSubspace B S hS X₁₀s := isOpenSubspace_openSubspaceOfPoints B S hS X₁.2 G hGo
  have hX₁₀pts : subspacePointSet B S hS X₁.1 X₁₀s = G :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS G
  have hX₁₀qc : IsQuasiCompactSpace B S hS X₁₀s.toFunctor :=
    isQuasiCompactSpace_openSubspaceOfPoints hGo hGc
  set X₁₀ : AlgebraicSpaces B S hS := ⟨X₁₀s.toFunctor, hX₁₀.1⟩
  -- the morphism `g : X₁₀ ⟶ Y`
  set ι₀ : X₁₀ ⟶ X₁ := ObjectProperty.homMk X₁₀s.ι
  set g : X₁₀ ⟶ Y := ι₀ ≫ (c₁ ≫ f)
  have hc₁fP : IsProper B S hS (c₁.hom ≫ f.hom) :=
    isProper_comp B S hS X₁.2 X.2 Y.2 _ _ hc₁P hf
  have hιqc : IsQuasiCompact B S hS X₁₀s.ι :=
    (isQuasiCompact_iff_isQuasiCompactSpace_openSubspace B S hS hZ X₁ hX₁qc hX₁qs
      ⟨X₁₀s, hX₁₀⟩).2 hX₁₀qc
  have hgft : IsFiniteType B S hS g.hom :=
    isFiniteType_comp' B S hS _ _ X₁.2 Y.2
      ⟨isLocallyOfFiniteType_of_isEtale B S hS X₁.2 (isEtale_ι_of_isOpenSubspace hX₁₀), hιqc⟩
      hc₁fP.2.1
  have hgqs : IsQuasiSeparated B S hS g.hom :=
    isQuasiSeparated_comp B S hS hX₁₀.1 X₁.2 X₁₀s.ι _
      (isQuasiSeparated_of_mono B S hS _ inferInstance)
      (isQuasiSeparated_of_isSeparated B S hS hc₁fP.1)
  -- `g` is étale over `V`
  set N := V.1.preimage g.hom with hNdef
  have hN : IsOpenSubspace B S hS N := isOpenSubspace_preimage B S hS g.hom V.1 Y.2 hX₁₀.1 V.2
  set ψ : N.toFunctor ⟶ X.1 := N.ι ≫ X₁₀s.ι ≫ c₁.hom
  have hψ : IsEtale B S hS ψ := by
    refine isEtale_comp_of_range_le_preimage hc₁ U hZ₁U (N.ι ≫ X₁₀s.ι)
      (isEtale_comp B S hS (isEtale_ι_of_isOpenSubspace hN) (isEtale_ι_of_isOpenSubspace hX₁₀))
      ?_
    rintro T _ ⟨y, rfl⟩
    exact y.2
  have hψE : ∀ n : points B S hS N.toFunctor, pointsMap B S hS _ ψ n ∈ Eset := by
    intro n
    have hmG : pointsMap B S hS _ (N.ι ≫ X₁₀s.ι) n ∈ G := by
      rw [← hX₁₀pts, pointsMap_comp_apply]
      exact Set.mem_range_self _
    have hnU : pointsMap B S hS _ ψ n ∈ subspacePointSet B S hS X.1 U.1 := by
      change _ ∈ Set.range (pointsMap B S hS _ (V.1.preimage f.hom).ι)
      rw [range_pointsMap_preimage_ι, Set.mem_preimage, ← pointsMap_comp_apply]
      change pointsMap B S hS _ (N.ι ≫ g.hom) n ∈ _
      rw [← Subfunctor.fromPreimage_ι V.1 g.hom, pointsMap_comp_apply]
      exact Set.mem_range_self _
    obtain ⟨u, hu⟩ := hnU
    by_contra hnE
    refine hGK' hmG (subset_closure ⟨u, hT'T'c (Or.inl ?_), ?_⟩)
    · change pointsMap B S hS _ U.1.ι u ∈ Esetᶜ
      rw [hu]
      exact hnE
    · rw [hu]
      exact pointsMap_comp_apply B S hS (N.ι ≫ X₁₀s.ι) c₁.hom n
  have hNetale : IsEtale B S hS (V.1.fromPreimage g.hom) := by
    refine isEtale_of_comp_mono B S hS _ V.1.ι ?_
    rw [Subfunctor.fromPreimage_ι]
    exact isEtale_of_forall_isEtaleAt B S hS hN.1 Y.2 _ fun n =>
      isEtaleAt_comp_of_isEtale hN.1 X.2 ψ hψ f.hom n (hψE n)
  have hsnd : IsEtale B S hS (pullback.snd g.hom V.1.ι) := by
    have hsq := (Subfunctor.isPullback_preimage g.hom V.1).flip
    rw [← hsq.isoPullback_inv_snd]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) hNetale
  -- flattening by blowing up
  obtain ⟨Y', b, Yc, hYcfp, hYcV, hb, hF₀flat, hF₀fp⟩ :=
    exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp_of_isFiniteType
      hZ g V hYqc hYqs hVqc hgft hgqs (isFlat_of_isEtale B S hS hsnd)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hsnd)
  refine ⟨Y', b, Yc, ⟨Yc, hYcfp, hYcV, hb⟩, hYcfp, hYcV, hb, ?_⟩
  -- the morphisms of strict transforms `ST(X₁₀) ⟶ ST(X₁) ⟶ ST(X)`
  obtain ⟨p₁, hp₁ι, hp₁S, hp₁B⟩ := exists_strictTransformSpace_map Yc hb f c₁
  obtain ⟨p₀₁, hp₀₁ι, hp₀₁S, hp₀₁B⟩ := exists_strictTransformSpace_map Yc hb (c₁ ≫ f) ι₀
  -- the composite `p₀ : ST(X₁₀) ⟶ ST(X)` and the lift of the geometric point
  set p₀ := p₀₁ ≫ p₁ with hp₀
  have hp₀F : p₀ ≫ strictTransformSpaceToBlowUp B S hS f b (preimageClosedSubspace b Yc).1 =
      strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Yc).1 := by
    rw [hp₀, Category.assoc, hp₁B, hp₀₁B]
  have hp₀F' : p₀.hom ≫ (strictTransformSpaceToBlowUp B S hS f b
      (preimageClosedSubspace b Yc).1).hom =
      (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Yc).1).hom :=
    congrArg (fun k => k.hom) hp₀F
  -- `p₀` followed by the projection to `X` is the projection `ST(X₁₀) ⟶ X₁₀ ⊆ X₁ ⟶ X`
  have hp₀S : p₀.hom ≫ (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Yc).1 ≫
      strictTransformPullbackToSource B S hS f b).hom =
      (strictTransformSpaceι B S hS g b (preimageClosedSubspace b Yc).1 ≫
        strictTransformPullbackToSource B S hS g b).hom ≫ X₁₀s.ι ≫ c₁.hom := by
    have h1 := hp₀₁S =≫ c₁
    simp only [Category.assoc] at h1
    have h : p₀ ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Yc).1 ≫
        strictTransformPullbackToSource B S hS f b =
        strictTransformSpaceι B S hS g b (preimageClosedSubspace b Yc).1 ≫
          strictTransformPullbackToSource B S hS g b ≫ ι₀ ≫ c₁ := by
      rw [hp₀, Category.assoc, hp₁S, h1]
    exact congrArg (fun k => k.hom) h
  have hgsep : IsSeparated B S hS g.hom :=
    isSeparated_comp B S hS X₁₀s.ι _ (isSeparated_of_mono _ inferInstance) hc₁fP.1
  have hF₀sep := isSeparated_strictTransformSpaceToBlowUp g b (preimageClosedSubspace b Yc).1 hgsep
  -- the points of `ST(X₁₀)` lie over `X₁₀`, which misses the closure of `T'c ⊇ T''`
  have hT''E : ∀ (e : points B S hS
      (strictTransformSpace B S hS g b (preimageClosedSubspace b Yc).1).1)
      (u : points B S hS U.1.toFunctor),
      pointsMap B S hS _ U.1.ι u = pointsMap B S hS _ (p₀.hom ≫ (strictTransformSpaceι B S hS f b
        (preimageClosedSubspace b Yc).1 ≫ strictTransformPullbackToSource B S hS f b).hom) e →
      u ∉ T'' := by
    intro e u hu huT
    have hmG : pointsMap B S hS _ X₁₀s.ι (pointsMap B S hS _ (strictTransformSpaceι B S hS g b
        (preimageClosedSubspace b Yc).1 ≫ strictTransformPullbackToSource B S hS g b).hom e) ∈
        G := by
      rw [← hX₁₀pts]
      exact Set.mem_range_self _
    refine hGK' hmG (subset_closure ⟨u, hT'T'c (Or.inr huT), ?_⟩)
    rw [hu, hp₀S, pointsMap_comp_apply, pointsMap_comp_apply]
  -- `p₀` is a monomorphism over `U`
  have hmonoU : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (w w' : T ⟶
      (strictTransformSpace B S hS g b (preimageClosedSubspace b Yc).1).1),
      w ≫ p₀.hom = w' ≫ p₀.hom →
      Subfunctor.range (w ≫ p₀.hom ≫ (strictTransformSpaceι B S hS f b
        (preimageClosedSubspace b Yc).1 ≫ strictTransformPullbackToSource B S hS f b).hom) ≤
        V.1.preimage f.hom → w = w' := by
    intro T w w' hww hw
    have hk : ∀ k : T ⟶ (strictTransformSpace B S hS g b (preimageClosedSubspace b Yc).1).1,
        k ≫ p₀.hom ≫ (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Yc).1 ≫
          strictTransformPullbackToSource B S hS f b).hom =
        (k ≫ (strictTransformSpaceι B S hS g b (preimageClosedSubspace b Yc).1 ≫
          strictTransformPullbackToSource B S hS g b).hom ≫ X₁₀s.ι) ≫ c₁.hom := by
      intro k
      rw [hp₀S]
      simp only [Category.assoc]
    have hx : w ≫ (strictTransformSpaceι B S hS g b (preimageClosedSubspace b Yc).1 ≫
        strictTransformPullbackToSource B S hS g b).hom = w' ≫
          (strictTransformSpaceι B S hS g b (preimageClosedSubspace b Yc).1 ≫
            strictTransformPullbackToSource B S hS g b).hom := by
      refine (cancel_mono X₁₀s.ι).1 ?_
      rw [Category.assoc, Category.assoc]
      refine eq_of_comp_eq_of_range_le_preimage hc₁ U hZ₁U _ _ ?_ ?_
      · rw [← hk, ← hk, ← Category.assoc, hww, Category.assoc]
      · rwa [← hk]
    refine strictTransformSpace_hom_ext g b _ w w' hx ?_
    rw [← hp₀F', ← Category.assoc, hww, Category.assoc]
  refine ⟨_, p₀, (congrArg (IsFlat B S hS) hp₀F').mpr hF₀flat,
    (congrArg (IsLocallyOfFinitePresentation B S hS) hp₀F').mpr hF₀fp.1,
    (congrArg (IsSeparated B S hS) hp₀F').mpr hF₀sep, hT''E, hmonoU, fun abar habar => ?_⟩
  have hF₁P : IsProper B S hS (strictTransformSpaceToBlowUp B S hS (c₁ ≫ f) b
      (preimageClosedSubspace b Yc).1).hom :=
    isProper_strictTransformSpaceToBlowUp_of_isProper (c₁ ≫ f) b _ hc₁fP
  have hFsep : IsSeparated B S hS (strictTransformSpaceToBlowUp B S hS f b
      (preimageClosedSubspace b Yc).1).hom :=
    isSeparated_strictTransformSpaceToBlowUp f b _ hf.1
  have hp₁P : IsProper B S hS p₁.hom := by
    refine isProper_of_comp_of_isSeparated B S hS
      (strictTransformSpace B S hS (c₁ ≫ f) b (preimageClosedSubspace b Yc).1).2
      (strictTransformSpace B S hS f b (preimageClosedSubspace b Yc).1).2 Y'.2 p₁.hom _ ?_ hFsep
    rwa [← hp₁B] at hF₁P
  have hp₁cl : IsClosedMap (pointsMap B S hS _ p₁.hom) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS p₁.hom
      (hp₁P.2.2 _ (strictTransformSpace B S hS f b (preimageClosedSubspace b Yc).1).2 (𝟙 _))
  -- the points of `ST(X₁)` over the closed set `Tc ⊇ |A|`
  set S₁ : Set (points B S hS
      (strictTransformSpace B S hS (c₁ ≫ f) b (preimageClosedSubspace b Yc).1).1) :=
    pointsMap B S hS _ (strictTransformSpaceι B S hS (c₁ ≫ f) b (preimageClosedSubspace b Yc).1 ≫
      strictTransformPullbackToSource B S hS (c₁ ≫ f) b).hom ⁻¹'
        (pointsMap B S hS _ c₁.hom ⁻¹' (pointsMap B S hS _ U.1.ι '' Tc)) with hS₁
  set C := openComplementOfClosedSubspace B S hS X Z₁
  have hUC : U.1 ≤ C.1 := le_openComplementOfClosedSubspace Z₁ U hZ₁U
  have := isIso_fromPreimage_openComplement hc₁
  have hAS₁ : pointsMap B S hS _ (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Yc).1 ≫
      strictTransformPullbackToSource B S hS f b).hom ⁻¹'
        Set.range (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι)) ⊆
      pointsMap B S hS _ p₁.hom '' S₁ := by
    rintro a ⟨α, hα⟩
    set u := pointsMap B S hS _ A.1.ι α with hu
    have hπa : pointsMap B S hS _ U.1.ι u = pointsMap B S hS _
        (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Yc).1 ≫
          strictTransformPullbackToSource B S hS f b).hom a := by
      rw [hu, ← pointsMap_comp_apply]
      exact hα
    -- a point of `X₁` over the image of `a`, which lies in `U`
    set y := pointsMap B S hS _ (Subfunctor.homOfLe hUC) u with hy
    set x₁ := pointsMap B S hS _ (C.1.preimage c₁.hom).ι
      (pointsMap B S hS _ (inv (C.1.fromPreimage c₁.hom)) y) with hx₁
    have hx₁c : pointsMap B S hS _ c₁.hom x₁ = pointsMap B S hS _ U.1.ι u := by
      rw [hx₁, ← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι, pointsMap_comp_apply,
        ← pointsMap_comp_apply _ _ _ (inv (C.1.fromPreimage c₁.hom)), IsIso.inv_hom_id,
        pointsMap_id, id, hy, ← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
    have hfV : pointsMap B S hS _ f.hom (pointsMap B S hS _ c₁.hom x₁) ∈
        subspacePointSet B S hS Y.1 V.1 := by
      rw [hx₁c, ← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι V.1 f.hom,
        pointsMap_comp_apply]
      exact Set.mem_range_self _
    obtain ⟨a₁, ha₁, hπa₁⟩ := exists_strictTransformSpace_point_of_notMem Yc hb f c₁ p₁ hp₁ι a
      x₁ (hx₁c.trans hπa) (fun h => Set.disjoint_left.1 hYcV hfV h)
    refine ⟨a₁, ?_, ha₁⟩
    rw [hS₁, Set.mem_preimage, Set.mem_preimage, hπa₁, hx₁c]
    exact Set.mem_image_of_mem _ (hAUTc ⟨α, rfl⟩)
  obtain ⟨a₁, ha₁cl, ha₁⟩ : abar ∈ pointsMap B S hS _ p₁.hom '' closure S₁ :=
    closure_minimal (hAS₁.trans (Set.image_mono subset_closure)) (hp₁cl _ isClosed_closure) habar
  -- `a₁` lies over `X₁₀`, so it comes from `ST(X₁₀)`
  have hπ₁G : pointsMap B S hS _ (strictTransformSpaceι B S hS (c₁ ≫ f) b
      (preimageClosedSubspace b Yc).1 ≫ strictTransformPullbackToSource B S hS (c₁ ≫ f) b).hom
        a₁ ∈ G :=
    hKG (Continuous.closure_preimage_subset (continuous_pointsMap B S hS _) _ ha₁cl)
  rw [← hX₁₀pts] at hπ₁G
  obtain ⟨x₀, hx₀⟩ := hπ₁G
  obtain ⟨a₀, ha₀, -⟩ := exists_strictTransformSpace_point_of_isEtale Yc hb (c₁ ≫ f) ι₀
    (isEtale_ι_of_isOpenSubspace hX₁₀) p₀₁ hp₀₁ι a₁ x₀ hx₀
  -- the open `V' = b⁻¹(V)` of the blowup
  set V' : OpenSubspaces B S hS Y'.1 :=
    ⟨V.1.preimage b.hom, isOpenSubspace_preimage B S hS b.hom V.1 Y.2 Y'.2 V.2⟩
  have hF₁V' : ∀ s ∈ S₁, pointsMap B S hS _ (strictTransformSpaceToBlowUp B S hS (c₁ ≫ f) b
      (preimageClosedSubspace b Yc).1).hom s ∈ subspacePointSet B S hS Y'.1 V'.1 := by
    rintro s ⟨w, hw, hws⟩
    change _ ∈ Set.range (pointsMap B S hS _ (V.1.preimage b.hom).ι)
    rw [range_pointsMap_preimage_ι, Set.mem_preimage, ← pointsMap_comp_apply]
    have hsqA : strictTransformSpaceToBlowUp B S hS (c₁ ≫ f) b
        (preimageClosedSubspace b Yc).1 ≫ b =
        (strictTransformSpaceι B S hS (c₁ ≫ f) b (preimageClosedSubspace b Yc).1 ≫
          strictTransformPullbackToSource B S hS (c₁ ≫ f) b) ≫ (c₁ ≫ f) := by
      rw [Category.assoc, Category.assoc,
        (AlgebraicSpaces.isPullback_fiberProduct B S hS (c₁ ≫ f) b).w]
    have hsq : (strictTransformSpaceToBlowUp B S hS (c₁ ≫ f) b
        (preimageClosedSubspace b Yc).1).hom ≫ b.hom =
        (strictTransformSpaceι B S hS (c₁ ≫ f) b (preimageClosedSubspace b Yc).1 ≫
          strictTransformPullbackToSource B S hS (c₁ ≫ f) b).hom ≫ c₁.hom ≫ f.hom :=
      congrArg (fun k => k.hom) hsqA
    rw [hsq, pointsMap_comp_apply, pointsMap_comp_apply, ← hws, ← pointsMap_comp_apply,
      ← Subfunctor.fromPreimage_ι V.1 f.hom, pointsMap_comp_apply]
    exact Set.mem_range_self _
  have hF₀a₀ : pointsMap B S hS _ (strictTransformSpaceToBlowUp B S hS g b
      (preimageClosedSubspace b Yc).1).hom a₀ ∈ closure (subspacePointSet B S hS Y'.1 V'.1) := by
    have hS₁V' : S₁ ⊆ pointsMap B S hS _ (strictTransformSpaceToBlowUp B S hS (c₁ ≫ f) b
        (preimageClosedSubspace b Yc).1).hom ⁻¹' subspacePointSet B S hS Y'.1 V'.1 := hF₁V'
    have h := Continuous.closure_preimage_subset (continuous_pointsMap B S hS _) _
      (closure_mono hS₁V' ha₁cl)
    rw [Set.mem_preimage, ← ha₀, ← pointsMap_comp_apply] at h
    rwa [← hp₀₁B]
  -- `F₀ : ST(X₁₀) ⟶ Y'` is quasi-finite over `V'`, hence over its closure
  have hF₀qfV : ∀ x, pointsMap B S hS _ (strictTransformSpaceToBlowUp B S hS g b
      (preimageClosedSubspace b Yc).1).hom x ∈ subspacePointSet B S hS Y'.1 V'.1 →
      IsQuasiFiniteAt B S hS (strictTransformSpaceToBlowUp B S hS g b
        (preimageClosedSubspace b Yc).1).hom x := by
    intro x hx
    refine isQuasiFiniteAt_comp B S hS (strictTransformPullback B S hS g b).2 Y'.2 _ _ x
      (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS
        (strictTransformSpace B S hS g b (preimageClosedSubspace b Yc).1).2
        (isLocallyQuasiFinite_of_isImmersion B S hS _ (isImmersion_of_isClosedImmersion B S hS
          (strictTransform B S hS g b (preimageClosedSubspace b Yc).1).2.2)) x) ?_
    have sq := AlgebraicSpaces.isPullback_hom B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g b).flip
    refine (isQuasiFiniteAt_iff_of_isPullback B S hS sq hX₁₀.1 Y.2 Y'.2 hgft.1 _).2 ?_
    have hn : pointsMap B S hS _ (strictTransformPullbackToSource B S hS g b).hom
        (pointsMap B S hS _ (strictTransformSpaceι B S hS g b (preimageClosedSubspace b Yc).1).hom
          x) ∈ Set.range (pointsMap B S hS _ N.ι) := by
      rw [hNdef, range_pointsMap_preimage_ι, Set.mem_preimage, ← pointsMap_comp_apply,
        ← sq.w, pointsMap_comp_apply]
      change pointsMap B S hS _ ((strictTransformSpaceι B S hS g b
        (preimageClosedSubspace b Yc).1).hom ≫ (strictTransformPullbackToBlowUp B S hS g b).hom)
          x ∈ Set.range (pointsMap B S hS _ (V.1.preimage b.hom).ι) at hx
      rwa [range_pointsMap_preimage_ι, Set.mem_preimage, pointsMap_comp_apply] at hx
    obtain ⟨n, hn⟩ := hn
    have hNqf : IsLocallyQuasiFinite B S hS (N.ι ≫ g.hom) := by
      rw [← Subfunctor.fromPreimage_ι V.1 g.hom]
      exact isLocallyQuasiFinite_of_isEtale B S hS Y.2
        (isEtale_comp B S hS hNetale (isEtale_ι_of_isOpenSubspace V.2))
    have h := isQuasiFiniteAt_of_isOpenSubspace B S hS N hN hNqf n
    rwa [hn] at h
  have hF₀qf := isQuasiFiniteAt_of_mem_closure_of_isFlat _ hF₀flat hF₀fp.1 V' hF₀qfV a₀ hF₀a₀
  have hp₀a₀ : pointsMap B S hS _ p₀.hom a₀ = abar := by
    change pointsMap B S hS _ (p₀₁.hom ≫ p₁.hom) a₀ = _
    rw [pointsMap_comp_apply, ha₀, ha₁]
  exact ⟨a₀, hp₀a₀, (congrArg (fun m => IsQuasiFiniteAt B S hS m a₀) hp₀F').mpr hF₀qf⟩

/-- **Finite flat local rings dominating the strict transform near the closure of `A`.**  Let
`S` be a scheme, let `f : X ⟶ Y` be a proper morphism of quasi-compact and quasi-separated
algebraic spaces over `S`, let `V ⊆ Y` be a quasi-compact open subspace and let `A` be a closed
subspace of `U = f⁻¹(V)` such that `f` is étale at every point of `A`.  Then there is a
`V`-admissible blowup `b : Y' ⟶ Y`, with centre `Yc`, such that the strict transform
`f' : X' ⟶ Y'` of `f` satisfies: for every geometric point `ā` of `X'` whose image lies in the
closure of the inverse image of `|A|` in `|X'|`, there are a local ring `𝒪` and a local
homomorphism `φ : 𝒪_{X', ā} ⟶ 𝒪` such that `φ ∘ (𝒪_{Y', f'(ā)} ⟶ 𝒪_{X', ā})` is finite and flat.

This needs no hypothesis on the image of `A` in `V`.  When `f` maps `A` isomorphically onto a
closed subspace of `V`, `φ` can be taken surjective: this is Stacks 0F48,
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_surjective_finite_flat_etaleLocalRing`.

See the module documentation for the proof. -/
theorem exists_isAdmissibleBlowup_finite_flat_etaleLocalRing
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (V : OpenSubspaces B S hS Y.1) (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (A : ClosedSubspaces B S hS (V.1.preimage f.hom).toFunctor)
    (het : ∀ a : points B S hS A.1.toFunctor,
      IsEtaleAt B S hS f.hom (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι) a)) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y) (Yc : ClosedSubspaces B S hS Y.1),
      IsAdmissibleBlowup B S hS V b ∧ IsFinitePresentation B S hS Yc.1.ι ∧
        Disjoint (subspacePointSet B S hS Y.1 V.1) (subspacePointSet B S hS Y.1 Yc.1) ∧
          IsBlowupAlong B S hS Yc b ∧
            ∀ abar : GeometricPoint B S hS
                (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).1,
              abar.image ∈ closure (pointsMap B S hS _
                  (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom) ≫
                    strictTransformPullbackToSource B S hS f b).hom ⁻¹'
                  Set.range (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι))) →
              ∃ (O : CommRingCat.{u + 1})
                (φ : etaleLocalRing B S hS
                  (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).1 abar →+* O),
                IsLocalRing O ∧ IsLocalHom φ ∧
                  (φ.comp (etaleLocalRingMap
                    (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).2
                    (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom
                    abar)).Finite ∧
                  (φ.comp (etaleLocalRingMap
                    (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).2
                    (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom
                    abar)).Flat := by
  obtain ⟨Y', b, Yc, hadm, hYcfp, hYcV, hb, E, p₀, hF₀flat, hF₀fp, -, -, -, hcov⟩ :=
    exists_isAdmissibleBlowup_isFlat_cover_closure hZ hXqc hXqs hYqc hYqs f hf V hVqc A het ∅
      isClosed_empty (Set.disjoint_empty _)
  refine ⟨Y', b, Yc, hadm, hYcfp, hYcV, hb, fun abar habar => ?_⟩
  obtain ⟨a₀, hp₀a₀, hF₀qf⟩ := hcov abar.image habar
  obtain ⟨abar₀, -, rfl, hfin, hflat⟩ := exists_geometricPoint_lift_finite_flat E.2
    (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).2 Y'.2 p₀.hom _ hF₀flat hF₀fp abar a₀
    hp₀a₀ hF₀qf
  exact ⟨etaleLocalRing B S hS _ abar₀, etaleLocalRingMap E.2 p₀.hom abar₀,
    isLocalRing_etaleLocalRing B S hS _ E.2 abar₀,
    isLocalHom_etaleLocalRingMap B S hS _
      (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).2 _ abar₀, hfin, hflat⟩

/-- **Stacks 0F48.**  Let `S` be a scheme, let `f : X ⟶ Y` be a proper morphism of quasi-compact
and quasi-separated algebraic spaces over `S`, let `V ⊆ Y` be a quasi-compact open subspace with
inverse image `U = f⁻¹(V)`, let `A ⊆ U` and `Bc ⊆ V` be closed subspaces such that `f`
restricts to an isomorphism `e : A ≅ Bc`, and assume `f` is étale at every point of `A`.  Then
there is a `V`-admissible blowup `b : Y' ⟶ Y`, with centre `Yc`, such that the strict transform
`f' : X' ⟶ Y'` of `f` satisfies: for every geometric point `ā` of `X'` lying in the closure of
the inverse image of `|A|` in `|X'|` there is a quotient `φ : 𝒪_{X', ā} ⟶ 𝒪`, a surjection onto
a local ring, such that `φ ∘ (𝒪_{Y', f'(ā)} ⟶ 𝒪_{X', ā})` is finite and flat.

The ring `𝒪` is the étale local ring of the strict transform `E` of a quasi-compact open `X₁₀`
of a `U`-admissible blowup of `X`, at a geometric point over `ā`
(`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isFlat_cover_closure`), chosen so that the
part of `X₁₀` over `Bc` lies over `A`.  As `A` is open in `f⁻¹(Bc)`, being the image of a section
of `f⁻¹(Bc) ⟶ Bc` near which that morphism is étale, `E ×_{Y'} Bc ⟶ Bc` is a monomorphism, and
`E ⟶ Y'` is étale at every point over the closure of `|Bc|`
(`AlgebraicGeometry.Space.isEtaleAt_of_mono_pullback_snd`), which contains `f'(ā)`.  So the map
`𝒪_{Y', f'(ā)} ⟶ 𝒪` is bijective
(`AlgebraicGeometry.Space.bijective_etaleLocalRingMap_of_isEtaleAt`) and `φ` is surjective. -/
@[stacks 0F48]
theorem exists_isAdmissibleBlowup_surjective_finite_flat_etaleLocalRing
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (V : OpenSubspaces B S hS Y.1) (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (A : ClosedSubspaces B S hS (V.1.preimage f.hom).toFunctor)
    (Bc : ClosedSubspaces B S hS V.1.toFunctor) (e : A.1.toFunctor ≅ Bc.1.toFunctor)
    (he : e.hom ≫ Bc.1.ι = A.1.ι ≫ V.1.fromPreimage f.hom)
    (het : ∀ a : points B S hS A.1.toFunctor,
      IsEtaleAt B S hS f.hom (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι) a)) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y) (Yc : ClosedSubspaces B S hS Y.1),
      IsAdmissibleBlowup B S hS V b ∧ IsFinitePresentation B S hS Yc.1.ι ∧
        Disjoint (subspacePointSet B S hS Y.1 V.1) (subspacePointSet B S hS Y.1 Yc.1) ∧
          IsBlowupAlong B S hS Yc b ∧
            ∀ abar : GeometricPoint B S hS
                (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).1,
              abar.image ∈ closure (pointsMap B S hS _
                  (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom) ≫
                    strictTransformPullbackToSource B S hS f b).hom ⁻¹'
                  Set.range (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι))) →
              ∃ (O : CommRingCat.{u + 1})
                (φ : etaleLocalRing B S hS
                  (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).1 abar →+* O),
                IsLocalRing O ∧ Function.Surjective φ ∧
                  (φ.comp (etaleLocalRingMap
                    (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).2
                    (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom
                    abar)).Finite ∧
                  (φ.comp (etaleLocalRingMap
                    (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).2
                    (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom
                    abar)).Flat := by
  classical
  have hUo : IsOpenSubspace B S hS (V.1.preimage f.hom) :=
    isOpenSubspace_preimage B S hS f.hom V.1 Y.2 X.2 V.2
  have sqU : IsPullback (V.1.fromPreimage f.hom) (V.1.preimage f.hom).ι V.1.ι f.hom :=
    Subfunctor.isPullback_preimage f.hom V.1
  -- the closed subspace `P = f⁻¹(Bc)` of `U` and its projection `p : P ⟶ Bc`
  set P := Bc.1.preimage (V.1.fromPreimage f.hom)
  have hPcl : IsClosedSubspace B S hS P :=
    isClosedSubspace_preimage B S hS (V.1.fromPreimage f.hom) Bc.1 V.2.1 hUo.1 Bc.2
  set p := Bc.1.fromPreimage (V.1.fromPreimage f.hom)
  have sqP : IsPullback p P.ι Bc.1.ι (V.1.fromPreimage f.hom) :=
    Subfunctor.isPullback_preimage _ Bc.1
  -- the section `s₀ : Bc ⟶ P` given by `A`
  set ℓ : A.1.toFunctor ⟶ P.toFunctor := sqP.lift e.hom A.1.ι he with hℓ
  have hℓp : ℓ ≫ p = e.hom := sqP.lift_fst _ _ _
  have hℓι : ℓ ≫ P.ι = A.1.ι := sqP.lift_snd _ _ _
  set s₀ : Bc.1.toFunctor ⟶ P.toFunctor := e.inv ≫ ℓ with hs₀def
  have hs₀ : s₀ ≫ p = 𝟙 _ := by rw [hs₀def, Category.assoc, hℓp, Iso.inv_hom_id]
  have : Mono s₀ := mono_of_mono_fac hs₀
  -- `p` is étale at the points of `A`
  have hetP : ∀ a : points B S hS A.1.toFunctor, IsEtaleAt B S hS p (pointsMap B S hS _ ℓ a) := by
    intro a
    refine IsEtaleAt.of_isPullback sqP.flip hPcl.1 hUo.1 Bc.2.1 V.2.1 ?_
    rw [← pointsMap_comp_apply, hℓι]
    refine IsEtaleAt.of_isPullback sqU.flip hUo.1 X.2 V.2.1 Y.2 ?_
    rw [← pointsMap_comp_apply]
    exact het a
  -- the étale locus `Ω` of `p`, through which `s₀` factors as an open immersion
  set Ω := {x : points B S hS P.toFunctor | IsEtaleAt B S hS p x}
  set Ωs := openSubspaceOfPoints B S hS P.toFunctor Ω
  have hΩo : IsOpenSubspace B S hS Ωs :=
    isOpenSubspace_openSubspaceOfPoints B S hS hPcl.1 Ω (isOpen_setOf_isEtaleAt p)
  have hΩpts : subspacePointSet B S hS P.toFunctor Ωs = Ω :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Ω
  have hΩet : IsEtale B S hS (Ωs.ι ≫ p) :=
    isEtale_of_forall_isEtaleAt B S hS hΩo.1 Bc.2.1 _ fun n =>
      isEtaleAt_comp_of_isEtale hΩo.1 hPcl.1 Ωs.ι (isEtale_ι_of_isOpenSubspace hΩo) p n
        (by
          have h : pointsMap B S hS _ Ωs.ι n ∈ subspacePointSet B S hS P.toFunctor Ωs :=
            Set.mem_range_self n
          rwa [hΩpts] at h)
  have hs₀Ω : Subfunctor.range s₀ ≤ Ωs := by
    refine le_of_range_pointsMap_ι_subset B S hS hΩo ?_
    rw [range_pointsMap_ι_range B S hS s₀]
    rintro _ ⟨y, rfl⟩
    change _ ∈ subspacePointSet B S hS P.toFunctor Ωs
    rw [hΩpts, hs₀def, pointsMap_comp_apply]
    exact hetP _
  have hs' : Subfunctor.lift s₀ hs₀Ω ≫ (Ωs.ι ≫ p) = 𝟙 _ := by
    rw [← Category.assoc, Subfunctor.lift_ι, hs₀]
  have hs₀o : IsOpenImmersion B S hS s₀ := by
    rw [← Subfunctor.lift_ι s₀ hs₀Ω]
    exact isOpenImmersion_comp B S hS _ _
      (isOpenImmersion_of_isEtale_of_section B S hS hΩo.1 Bc.2.1 _ hΩet _ hs') hΩo.2
  -- the closed set `T''` of points of `f⁻¹(Bc)` off `A`
  set R := Set.range (pointsMap B S hS _ s₀)
  have hRo : IsOpen R := isOpen_range_pointsMap_of_isOpenImmersion B S hS s₀ hs₀o
  set T'' := pointsMap B S hS _ P.ι '' Rᶜ
  have hPemb : Topology.IsClosedEmbedding (pointsMap B S hS _ P.ι) :=
    ⟨⟨isInducing_pointsMap_of_isImmersion B S hS hUo.1 P.ι
        (isImmersion_of_isClosedImmersion B S hS hPcl.2),
      pointsMap_injective_of_mono B S hS P.ι⟩,
      isClosed_range_pointsMap_of_isClosedImmersion B S hS hUo.1 P.ι hPcl.2⟩
  have hT'' : IsClosed T'' := hPemb.isClosedMap _ hRo.isClosed_compl
  have hAT'' : Disjoint (Set.range (pointsMap B S hS _ A.1.ι)) T'' := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨x, hxR, hx⟩
    refine hxR ⟨pointsMap B S hS _ e.hom a, ?_⟩
    have h1 : e.hom ≫ s₀ ≫ P.ι = A.1.ι := by
      rw [hs₀def, Category.assoc, Iso.hom_inv_id_assoc, hℓι]
    refine pointsMap_injective_of_mono B S hS P.ι ?_
    have h2 := congrArg (fun φ => pointsMap B S hS _ φ a) h1
    simp only [pointsMap_comp_apply] at h2
    rw [h2, hx]
  -- the flat cover
  obtain ⟨Y', b, Yc, hadm, hYcfp, hYcV, hb, E, p₀, hF₀flat, hF₀fp, hF₀sep, hT''E, hmonoU,
    hcov⟩ := exists_isAdmissibleBlowup_isFlat_cover_closure hZ hXqc hXqs hYqc hYqs f hf V hVqc
      A het T'' hT'' hAT''
  refine ⟨Y', b, Yc, hadm, hYcfp, hYcV, hb, fun abar habar => ?_⟩
  have hX' := (strictTransformSpace B S hS f b (Yc.1.preimage b.hom)).2
  set π := (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom) ≫
    strictTransformPullbackToSource B S hS f b).hom
  set F := (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom
  have hπF : π ≫ f.hom = F ≫ b.hom := by
    have h := (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom)).hom ≫=
      (pullback.condition (f := f.hom) (g := b.hom))
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  -- the open immersion `ι' : V ⟶ Y'` and the quasi-compact immersion `Bc ⟶ Y'`
  obtain ⟨ι', hι'b, hι'r⟩ := exists_lift_range_eq_preimage_of_isBlowupAlong V.2.1 hb V.1.ι
    (by rwa [Subfunctor.range_ι])
  have : Mono ι' := mono_of_mono_fac hι'b
  have hι'o : IsOpenImmersion B S hS ι' := by
    have hro : IsOpenSubspace B S hS (Subfunctor.range ι') := by
      rw [hι'r]
      exact isOpenSubspace_preimage B S hS b.hom _ Y.2 Y'.2 (by rw [Subfunctor.range_ι]; exact V.2)
    rw [← Subfunctor.toRange_ι ι']
    exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hro.2
  obtain ⟨hY'qc, hY'qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ hYqc hYqs hYcfp hb
  set W : AlgebraicSpaces B S hS := ⟨Bc.1.toFunctor, Bc.2.1⟩
  set j : W ⟶ Y' := ObjectProperty.homMk (Bc.1.ι ≫ ι')
  have hjimm : IsImmersion B S hS j.hom :=
    isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS Bc.2.2)
      (isImmersion_of_isOpenImmersion B S hS hι'o)
  have hjqc : IsQuasiCompact B S hS j.hom :=
    isQuasiCompact_comp B S hS V.2.1 Y'.2 _ _ (isQuasiCompact_of_isClosedImmersion' B S hS Bc.2.2)
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs hVqc ι')
  -- `E ×_{Y'} Bc ⟶ Bc` is a monomorphism
  have hcondU : (pullback.snd (p₀.hom ≫ F) j.hom ≫ Bc.1.ι) ≫ V.1.ι =
      (pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ π) ≫ f.hom := by
    have h : pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ F =
        pullback.snd (p₀.hom ≫ F) j.hom ≫ Bc.1.ι ≫ ι' := pullback.condition
    simp only [Category.assoc, hπF, ← hι'b, reassoc_of% h]
  set mU := sqU.lift (pullback.snd (p₀.hom ≫ F) j.hom ≫ Bc.1.ι)
    (pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ π) hcondU with hmU
  have hmUι : mU ≫ (V.1.preimage f.hom).ι = pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ π :=
    sqU.lift_snd _ _ _
  set m := sqP.lift (pullback.snd (p₀.hom ≫ F) j.hom) mU (sqU.lift_fst _ _ _).symm with hm
  have hmp : m ≫ p = pullback.snd (p₀.hom ≫ F) j.hom := sqP.lift_fst _ _ _
  have hmι : m ≫ P.ι = mU := sqP.lift_snd _ _ _
  have hmono : Mono m := by
    refine ⟨fun {T} u v huv => ?_⟩
    have hsnd : u ≫ pullback.snd (p₀.hom ≫ F) j.hom = v ≫ pullback.snd (p₀.hom ≫ F) j.hom := by
      rw [← hmp, ← Category.assoc, huv, Category.assoc]
    have hfst : u ≫ pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ π =
        v ≫ pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ π := by
      rw [← hmUι, ← hmι]
      simp only [← Category.assoc, huv]
    refine pullback.hom_ext ?_ hsnd
    refine hmonoU T _ _ ?_ ?_
    · refine strictTransformSpace_hom_ext f b _ _ _ ?_ ?_
      · simpa only [Category.assoc] using hfst
      · have h : u ≫ pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ F =
            v ≫ pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ F := by
          rw [pullback.condition, ← Category.assoc, hsnd, Category.assoc]
        simpa only [Category.assoc] using h
    · rw [Category.assoc, ← hmUι]
      rintro T' _ ⟨y, rfl⟩
      exact ((u ≫ mU).app T' y).2
  have hmR : Subfunctor.range m ≤ Subfunctor.range s₀ := by
    refine le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isAlgebraicSpace B S hS Bc.2.1 s₀ hs₀o) ?_
    rw [range_pointsMap_ι_range B S hS m, range_pointsMap_ι_range B S hS s₀]
    rintro _ ⟨z, rfl⟩
    by_contra hz
    refine hT''E (pointsMap B S hS _ (pullback.fst (p₀.hom ≫ F) j.hom) z)
      (pointsMap B S hS _ P.ι (pointsMap B S hS _ m z)) ?_ ⟨_, hz, rfl⟩
    have h : m ≫ P.ι ≫ (V.1.preimage f.hom).ι =
        pullback.fst (p₀.hom ≫ F) j.hom ≫ p₀.hom ≫ π := by
      rw [← Category.assoc, hmι, hmUι]
    simpa only [pointsMap_comp_apply] using congrArg (fun φ => pointsMap B S hS _ φ z) h
  set k := Subfunctor.lift m hmR ≫ inv (Subfunctor.toRange s₀) with hk
  have hks : k ≫ s₀ = m := by
    calc k ≫ s₀ = Subfunctor.lift m hmR ≫ inv (Subfunctor.toRange s₀) ≫
          Subfunctor.toRange s₀ ≫ (Subfunctor.range s₀).ι := by
          rw [Subfunctor.toRange_ι s₀, hk, Category.assoc]
      _ = m := by rw [IsIso.inv_hom_id_assoc, Subfunctor.lift_ι]
  have hsndk : pullback.snd (p₀.hom ≫ F) j.hom = k := by
    rw [← hmp, ← hks, Category.assoc, hs₀, Category.comp_id]
  have hsndmono : Mono (pullback.snd (p₀.hom ≫ F) j.hom) := by
    rw [hsndk]
    exact mono_of_mono_fac hks
  -- the cover point, at which `E ⟶ Y'` is étale
  obtain ⟨a₀, hp₀a₀, hF₀qf⟩ := hcov abar.image habar
  have h1 : A.1.ι ≫ (V.1.preimage f.hom).ι ≫ f.hom = e.hom ≫ Bc.1.ι ≫ V.1.ι := by
    rw [← sqU.w, ← Category.assoc, ← he, Category.assoc]
  have hFcl : pointsMap B S hS _ F abar.image ∈
      closure (Set.range (pointsMap B S hS _ j.hom)) := by
    refine map_mem_closure (continuous_pointsMap B S hS _) habar ?_
    rintro x' ⟨a, ha⟩
    have hb' : pointsMap B S hS _ b.hom (pointsMap B S hS _ F x') =
        pointsMap B S hS _ V.1.ι (pointsMap B S hS _ Bc.1.ι (pointsMap B S hS _ e.hom a)) := by
      have h2 := congrArg (fun φ => pointsMap B S hS _ φ x') hπF
      have h3 := congrArg (fun φ => pointsMap B S hS _ φ a) h1
      simp only [pointsMap_comp_apply] at h2 h3 ha
      rw [← h2, ← ha, h3]
    obtain ⟨v, hv⟩ : pointsMap B S hS _ F x' ∈ Set.range (pointsMap B S hS _ ι') := by
      rw [← range_pointsMap_ι_range B S hS ι', hι'r, range_pointsMap_preimage_ι,
        Set.mem_preimage, hb', range_pointsMap_ι_range B S hS V.1.ι]
      exact ⟨_, rfl⟩
    have hv' : v = pointsMap B S hS _ Bc.1.ι (pointsMap B S hS _ e.hom a) := by
      refine pointsMap_injective_of_mono B S hS V.1.ι ?_
      rw [← hb', ← hv, ← pointsMap_comp_apply, hι'b]
    refine ⟨pointsMap B S hS _ e.hom a, ?_⟩
    change pointsMap B S hS _ (Bc.1.ι ≫ ι') _ = _
    rw [pointsMap_comp_apply, ← hv', hv]
  have hF₀et : IsEtaleAt B S hS (p₀.hom ≫ F) a₀ :=
    isEtaleAt_of_mono_pullback_snd (p₀ ≫ strictTransformSpaceToBlowUp B S hS f b
      (Yc.1.preimage b.hom)) j hF₀flat hF₀fp hF₀sep hjimm hjqc hsndmono a₀
      (by
        change pointsMap B S hS _ (p₀.hom ≫ F) a₀ ∈ _
        rw [pointsMap_comp_apply, hp₀a₀]
        exact hFcl)
  -- the lift of the geometric point
  obtain ⟨abar₀, habar₀, rfl, hfin, hflat⟩ := exists_geometricPoint_lift_finite_flat E.2 hX' Y'.2
    p₀.hom F hF₀flat hF₀fp abar a₀ hp₀a₀ hF₀qf
  have hcomp := etaleLocalRingMap_comp E.2 hX' p₀.hom F abar₀
  have hbij : Function.Bijective (etaleLocalRingMap E.2 (p₀.hom ≫ F) abar₀) :=
    bijective_etaleLocalRingMap_of_isEtaleAt (p₀ ≫ strictTransformSpaceToBlowUp B S hS f b
      (Yc.1.preimage b.hom)) abar₀ (habar₀ ▸ hF₀et)
  rw [← hcomp] at hbij
  refine ⟨etaleLocalRing B S hS _ abar₀, etaleLocalRingMap E.2 p₀.hom abar₀,
    isLocalRing_etaleLocalRing B S hS _ E.2 abar₀, fun y => ?_,
    hfin, hflat⟩
  obtain ⟨x, hx⟩ := hbij.2 y
  exact ⟨_, hx⟩

end AlgebraicGeometry.Space
