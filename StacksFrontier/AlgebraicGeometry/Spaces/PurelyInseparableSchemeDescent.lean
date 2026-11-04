module

public import StacksFrontier.AlgebraicGeometry.Spaces.PurelyInseparableBaseChangeScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
import StacksFrontier.AlgebraicGeometry.Spaces.FlatSurjectiveMonomorphism
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism

/-!
# A space which is a scheme after a purely inseparable extension is a scheme

An algebraic space `X` over a field `k` such that `X_{k'}` is a scheme for some purely
inseparable extension `k'/k` is itself a scheme (Stacks 0B83). Being a scheme is
`CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the space, and the base
change `X_{k'}` is `AlgebraicGeometry.Space.extensionBaseChange`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective_of_isAffineSpace`:
  the target of an integral morphism of algebraic spaces which is bijective on points and has
  scheme source is a scheme, as soon as every open subspace of the target whose preimage is
  affine is itself affine.
* `AlgebraicGeometry.Space.isAffineSpace_of_isPullback_specExtensionToBase`: an algebraic space
  over a field `k` whose base change to an arbitrary field extension `k'` is affine is affine.
* `AlgebraicGeometry.Space.isRepresentable_of_isPurelyInseparable_of_isRepresentable`:
  **Stacks 0B83.**

## Implementation notes

The source deduces Stacks 0B83 from Stacks 07VV, applied to the projection `X_{k'} ⟶ X`, which
is integral and bijective on points. The proof of Stacks 07VV places every point of `X` in an
open subspace `W` whose preimage in `X_{k'}` is affine, and then makes `W` affine by Stacks 07VT.
Here that preimage is the base change `W_{k'}` of `W` along `Spec k' ⟶ Spec k`, so Stacks 07VT
is not needed: `Spec k' ⟶ Spec k` is quasi-compact, flat and surjective, hence a one-member
fpqc covering, the structure morphism of `W` becomes affine after base change along it, and
affineness of a morphism of algebraic spaces is fpqc local on the base by Stacks 041Z,
`AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc`. So the structure morphism of `W`
to the affine base is affine, and `W` is affine. This step uses no property of `k'/k` beyond
its being a field extension; pure inseparability enters only through bijectivity of
`X_{k'} ⟶ X` on points, which identifies the open subspaces of `X_{k'}` with those of `X`.

The first part of the proof of Stacks 07VV is recorded with the affineness of the open
subspaces as its hypothesis, as
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective_of_isAffineSpace`; the
hypothesis is about the given morphism only and is discharged below for `X_{k'} ⟶ X`.

## References

* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 0B83](https://stacks.math.columbia.edu/tag/0B83)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Schemes under an integral bijection -/

section IntegralBijection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An affine open neighbourhood of a point of a representable presheaf: a member of the
standard affine cover of the representing object through which the point factors. -/
private theorem exists_affineChart_isOpenImmersion_mem_range
    (U : BigFppfOver B S hS) (e : yoneda.obj U ≅ F) (x : points B S hS F) :
    ∃ (V : BigFppfOver B S hS) (α : yoneda.obj V ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ IsOpenImmersion B S hS α ∧
        x ∈ Set.range (pointsMap B S hS (yoneda.obj V) α) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨i, q, hq⟩ := exists_affineChart_pointsMap_eq B S hS U e p
  refine ⟨affineChart B S hS U i, yoneda.map (affineChartι B S hS U i) ≫ e.hom,
    isAffine_affineChart B S hS U i, ?_, ⟨_, hq⟩⟩
  refine MorphismProperty.RespectsIso.postcomp _ e.hom _ ?_
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
    (isOpenImmersion_toScheme_map_affineChartι B S hS U i)

/-- Over an injective map on points, the base change along an open subspace `W` of the target
whose points are the image of the points of `α` has the same image on points as `α`. -/
theorem range_pointsMap_pullback_fst_eq_of_injective {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : Function.Injective (pointsMap B S hS F f)) (α : X ⟶ F) (W : Subfunctor G)
    (hW : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS F f '' Set.range (pointsMap B S hS X α)) :
    Set.range (pointsMap B S hS (pullback f W.ι) (pullback.fst f W.ι)) =
      Set.range (pointsMap B S hS X α) := by
  refine subset_antisymm ?_ ?_
  · rintro z ⟨w, rfl⟩
    have hmem : pointsMap B S hS F f (pointsMap B S hS (pullback f W.ι)
        (pullback.fst f W.ι) w) ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
      rw [pointsMap_apply_comm B S hS pullback.condition w]
      exact ⟨_, rfl⟩
    rw [hW] at hmem
    obtain ⟨z', hz', hfz'⟩ := hmem
    exact hf hfz' ▸ hz'
  · rintro z ⟨w, rfl⟩
    have hmem : pointsMap B S hS F f (pointsMap B S hS X α w) ∈
        Set.range (pointsMap B S hS W.toFunctor W.ι) := by
      rw [hW]
      exact ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c, hc, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback f W.ι) _ b hb.symm
    exact ⟨c, hc⟩

/-- **The target of an integral bijection with scheme source is a scheme, granted affineness
of the open subspaces of the target with affine preimage.** Let `f : X ⟶ Y` be an integral
morphism of algebraic spaces over `S` which is bijective on points, with `X` a scheme. If every
open subspace `W ⊆ Y` with `X ×_Y W` affine is affine, then `Y` is a scheme.

This is the proof of Stacks 07VV,
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`, up to its last step.
Let `α : h_V ⟶ X` be an affine open of the source through a given point.
The morphism is universally closed by Stacks 0415, hence closed on points, so the image of `|V|`
is open and cuts out an open subspace `W` of the target by part (1) of Tag 03BZ. Bijectivity
identifies the point set of `X ×_Y W` with `|V|`, so the two open subspaces of `X` agree and
`X ×_Y W` is affine; then `W` is affine by hypothesis, and the given point lies in the
schematic locus of Stacks 03JH. -/
theorem isRepresentable_of_isIntegralHom_of_bijective_of_isAffineSpace
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsIntegralHom B S hS f) (hbij : Function.Bijective (pointsMap B S hS F f))
    (hFrep : F.IsRepresentable)
    (haff : ∀ W : Subfunctor G, IsOpenSubspace B S hS W →
      IsAffineSpace B S hS (pullback f W.ι) → IsAffineSpace B S hS W.toFunctor) :
    G.IsRepresentable := by
  classical
  let _ : F.IsRepresentable := hFrep
  have hclosedmap : IsClosedMap (pointsMap B S hS F f) :=
    isClosed_of_universallyClosed B S hS hG f
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hF hG f).1 hf).2
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hG fun y => ?_
  obtain ⟨x, hx⟩ := hbij.2 y
  obtain ⟨V, α, hVaff, hαopen, v, hv⟩ := exists_affineChart_isOpenImmersion_mem_range B S hS
    (Functor.reprX F) (Functor.reprW F) x
  have _ : Mono α := mono_of_presheaf_isOpenImmersion hαopen
  -- The open subspace of the target cut out by the image of the point set of `V`.
  have himage : IsOpen (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) := by
    rw [← isClosed_compl_iff, ← Set.image_compl_eq hbij]
    exact hclosedmap _ (isOpen_range_pointsMap_of_isOpenImmersion B S hS α hαopen).isClosed_compl
  set W : Subfunctor G := openSubspaceOfPoints B S hS G
    (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) with hWdef
  have hW : IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints B S hS hG _ himage
  have hWpts : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hyW : y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hWpts]
    exact ⟨x, ⟨v, hv⟩, hx⟩
  -- The base change of the morphism along that open subspace is the affine open `V`.
  have hQalg : IsAlgebraicSpace B S hS (pullback f W.ι) :=
    isAlgebraicSpace_pullback B S hS f W.ι hF hW.1 hG
  have hfstopen : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f W.ι).flip hW.2
  have _ : Mono (pullback.fst f W.ι) := mono_of_presheaf_isOpenImmersion hfstopen
  have hfstpts := range_pointsMap_pullback_fst_eq_of_injective B S hS f hbij.1 α W hWpts
  have hrange : Subfunctor.range (pullback.fst f W.ι) = Subfunctor.range α := by
    have hP := range_pointsMap_ι_range B S hS (pullback.fst f W.ι)
    have hA := range_pointsMap_ι_range B S hS α
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isOpenImmersion V α hαopen) ?_)
      (le_of_range_pointsMap_ι_subset B S hS
        (isOpenSubspace_range_of_isAlgebraicSpace B S hS hQalg _ hfstopen) ?_) <;>
      rw [hP, hA, hfstpts]
  have hQaff : IsAffineSpace B S hS (pullback f W.ι) := by
    refine ⟨V, hVaff, ⟨?_⟩⟩
    refine rangeIsoOfMono B S hS (pullback.fst f W.ι) ≪≫ ?_
    rw [hrange]
    exact (rangeIsoOfMono B S hS α).symm
  obtain ⟨T, -, ⟨eT⟩⟩ := haff W hW hQaff
  exact (mem_range_pointsMap_schematicLocus_iff B S hS G y).2
    ⟨W, hW, isRepresentable_of_natIso _ eT.symm, hyW⟩

end IntegralBijection

/-! ### Affineness descends along a field extension -/

section FieldExtension

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (.of k))) (hk' : B.Contains (Spec (.of k')))

/-- The structure morphism of `Spec k'` over `Spec k`, as a morphism of algebraic spaces over
`Spec k`, is quasi-compact, flat and surjective, hence a one-member fpqc covering of the base in
the sense of Stacks 03MQ. -/
theorem isFpqcCovering_yoneda_map_specExtensionToBase :
    IsFpqcCovering B (Spec (.of k)) hk
      (fun _ : PUnit.{1} => yoneda.map (specExtensionToBase k k' B hk hk')) :=
  isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective B (Spec (.of k)) hk
    (X := representedAlgebraicSpace B (Spec (.of k)) hk (specExtension k k' B hk hk'))
    (Y := representedAlgebraicSpace B (Spec (.of k)) hk (Over.mk (𝟙 (B.obj hk))))
    (ObjectProperty.homMk (yoneda.map (specExtensionToBase k k' B hk hk')))
    (isQuasiCompact_yoneda_map_of_isAffineHom B (Spec (.of k)) hk _
      (show _root_.AlgebraicGeometry.IsAffineHom
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) from inferInstance))
    (isFlat_yoneda_map B (Spec (.of k)) hk _
      (show Flat (Spec.map (CommRingCat.ofHom (algebraMap k k'))) from
        Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)))
    (isSurjective_yoneda_map B (Spec (.of k)) hk _
      (show _root_.AlgebraicGeometry.Surjective
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) from
        (AlgebraicGeometry.surjective_iff _).2 (Function.surjective_to_subsingleton _)))

/-- **An algebraic space over a field which becomes affine after a field extension is affine.**
Let `Y` be an algebraic space over `k` and `k'/k` a field extension. If a base change of `Y`
along `Spec k' ⟶ Spec k` is affine, then `Y` is affine.

`Spec k' ⟶ Spec k` is an fpqc covering of the base by
`AlgebraicGeometry.Space.isFpqcCovering_yoneda_map_specExtensionToBase`, and the base change of
the structure morphism of `Y` along it is a morphism from an affine space to the affine scheme
`Spec k'`, hence affine by Stacks 08GB. Affineness is fpqc local on the base by Stacks 041Z, so
the structure morphism of `Y` is affine, and its base change along the identity of the affine
base is `Y`. -/
theorem isAffineSpace_of_isPullback_specExtensionToBase
    {Y P : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y) {a : P ⟶ Y}
    {b : P ⟶ yoneda.obj (specExtension k k' B hk hk')}
    {t : Y ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))}
    (sq : IsPullback a b t (yoneda.map (specExtensionToBase k k' B hk hk')))
    (hP : IsAffineSpace B (Spec (.of k)) hk P) :
    IsAffineSpace B (Spec (.of k)) hk Y := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let K := representedAlgebraicSpace B (Spec (.of k)) hk (specExtension k k' B hk hk')
  let T := representedAlgebraicSpace B (Spec (.of k)) hk (Over.mk (𝟙 (B.obj hk)))
  let p : K ⟶ T := ObjectProperty.homMk (yoneda.map (specExtensionToBase k k' B hk hk'))
  let t' : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of k)) hk) ⟶ T := ObjectProperty.homMk t
  have hKaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      (specExtension k k' B hk hk')) :=
    inferInstanceAs (IsAffine (Spec (.of k')))
  -- The base change of `t'` along `p` is a morphism from an affine space to `Spec k'`.
  have hbc : IsAffineHom B (Spec (.of k)) hk (pullback.snd t' p).hom := by
    have sq' := AlgebraicSpaces.isPullback_hom B (Spec (.of k)) hk
      (IsPullback.of_hasPullback t' p)
    rw [← sq'.isoIsPullback_hom_snd _ _ sq]
    refine isAffineHom_iso_comp _ ?_
    obtain ⟨V, hV, ⟨eV⟩⟩ := hP
    rw [← eV.hom_inv_id_assoc b]
    exact isAffineHom_iso_comp _
      (isAffineHom_of_affine_source_of_isAbsolutelySeparated B (Spec (.of k)) hk hZ ⟨V, hV⟩
        (eV.inv ≫ b) (isAbsolutelySeparated_of_isAffineSpace B (Spec (.of k)) hk hZ
          (isAffineSpace_yoneda B (Spec (.of k)) hk _ hKaff)))
  -- Stacks 041Z along the one-member fpqc covering `p`.
  have ht : IsAffineHom B (Spec (.of k)) hk t := by
    refine (isLocalAtTarget_isAffineHom_fpqc.{u, 0} B (Spec (.of k)) hk).of_forall_pullbackSnd
      (f := t') (R := Presieve.ofArrows (fun _ : PUnit.{1} => K) fun _ => p)
      ⟨PUnit.{1}, fun _ => K, fun _ => p, rfl, T.property, fun _ => K.property,
        isFpqcCovering_yoneda_map_specExtensionToBase k k' B hk hk'⟩ ?_
    rintro _ _ _ ⟨⟩
    exact hbc
  -- The base change of `t` along the identity of the affine base is `Y`.
  let Z : BigAffineFppf B (Spec (.of k)) hk :=
    ⟨Over.mk (𝟙 (B.obj hk)), inferInstanceAs (IsAffine (Spec (.of k)))⟩
  obtain ⟨W, a', q, hpb⟩ := ht Z (𝟙 _)
  have _ : IsIso a' := hpb.isIso_fst_of_isIso
  exact ⟨(BigAffineFppf.inclusion B (Spec (.of k)) hk).obj W, W.property, ⟨(asIso a').symm⟩⟩

/-! ### Stacks 0B83 -/

/-- **Stacks 0B83.** Let `k` be a field and let `X` be an algebraic space over `k`. If there
exists a purely inseparable field extension `k'/k` such that the base change `X_{k'}` is a
scheme, then `X` is a scheme.

The projection `X_{k'} ⟶ X` is integral, surjective and universally injective, hence integral
and bijective on the points of Stacks 03BU, so the proof of Stacks 07VV,
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective_of_isAffineSpace`,
applies once every open subspace `W ⊆ X` with affine preimage `W_{k'}` is known to be affine.
That preimage is a base change of `W` along `Spec k' ⟶ Spec k`, so `W` is affine by
`AlgebraicGeometry.Space.isAffineSpace_of_isPullback_specExtensionToBase`, which descends
affineness along the fpqc covering `Spec k' ⟶ Spec k` by Stacks 041Z; this replaces the appeal
to Stacks 07VT in the proof of Stacks 07VV.

The spectrum of `k'` lies in the chosen big fppf site as soon as the spectrum of `k` does, by
`AlgebraicGeometry.Space.contains_spec_of_isAlgebraic`; membership of the site is a
proposition, so the statement is unchanged if another proof of it is substituted. -/
@[stacks 0B83]
theorem isRepresentable_of_isPurelyInseparable_of_isRepresentable [IsPurelyInseparable k k']
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXk' : (extensionBaseChange k k' B hk
      (contains_spec_of_isAlgebraic B k k' hk) X).IsRepresentable) :
    X.IsRepresentable := by
  have hk' : B.Contains (Spec (.of k')) := contains_spec_of_isAlgebraic B k k' hk
  exact isRepresentable_of_isIntegralHom_of_bijective_of_isAffineSpace B (Spec (.of k)) hk
    (isAlgebraicSpace_extensionBaseChange k k' B hk hk' X hX) hX
    (extensionBaseChangeProj k k' B hk hk' X)
    (isIntegralHom_extensionBaseChangeProj k k' B hk hk' X)
    ⟨injective_pointsMap_of_universallyInjective B (Spec (.of k)) hk hX
      (universallyInjective_extensionBaseChangeProj k k' B hk hk' hX),
      isSurjective_extensionBaseChangeProj k k' B hk hk' X⟩
    hXk' fun W hW hQ => isAffineSpace_of_isPullback_specExtensionToBase k k' B hk hk' hW.1
      ((IsPullback.of_hasPullback _ W.ι).flip.paste_vert
        (isPullback_extensionBaseChangeProj k k' B hk hk' X).flip) hQ

end FieldExtension

end AlgebraicGeometry.Space

end
