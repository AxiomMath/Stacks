module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyBlowupStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffineMain
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsBlowup

/-!
# The chain of Stacks 0GV6 pulls back along an affine morphism

Step 1 of the proof of Stacks 0GV6 reduces the general quasi-compact quasi-separated case to the
Noetherian one like this: an affine morphism `X ⟶ X₀` with `X₀` Noetherian is produced by
absolute Noetherian approximation, and then "if we can prove the lemma for `X₀`, then we can
pull back the stratification and the centers of the blowing ups to `X` and get the result for
`X`; this uses that the resolution property goes up along affine morphisms (Stacks 0GUU) and
that the strict transform of an affine morphism is affine — details omitted".

**This file is those omitted details.**  Its main result,
`AlgebraicGeometry.Space.IsResolutionBlowupStratified.pullback_of_isAffineHom`, says that the
predicate `AlgebraicGeometry.Space.IsResolutionBlowupStratified` at `⊤` — which is the
conclusion of Stacks 0GV6 by
`AlgebraicGeometry.Space.exists_thickening_filtration_of_isResolutionBlowupStratified_top` —
descends along an affine morphism to a quasi-compact, quasi-separated target.  It is stated over
an arbitrary base scheme `S`, since nothing in it is particular to `Spec ℤ`; the base crossing
of the source's *first* sentence is a separate matter, discussed in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyStep1.lean`.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_preimage_fromPreimage_ι_comp`: for a closed subspace
  `G` of `F` and a subspace `T ⊆ G`, the points of the pullback of `T` along `g : F' ⟶ F`,
  measured in `F'`, are the `g`-preimage of the points of `T` measured in `F`.  This is what
  turns the chain's point-set conditions into conditions on preimages.
* `AlgebraicGeometry.Space.isAdmissibleBlowup_strictTransform_preimage`: the strict transform of
  the pullback of a stratum along a `V`-admissible blowing up of the stratum is a
  `(V`-pullback`)`-admissible blowing up of the pulled-back stratum, and its source is affine
  over the original blowup.  This is the source's "the strict transform of an affine morphism is
  affine" together with Stacks 0864 part (1).
* `AlgebraicGeometry.Space.IsResolutionBlowupStratified.pullback_of_isAffineHom`: **the omitted
  details of Step 1** — the chain of Stacks 0GV6 over `X₀` pulls back to one over `X` along an
  affine `X ⟶ X₀`.

## Implementation notes

**No composite-strict-transform lemma is needed.**  The natural guess is that identifying "the
strict transform of the stratum's blowup" with "the blowup of the pulled-back centre" needs a
comparison of `strictTransform` of a composite with `strictTransform` of a factor, which the
library does not have.  It does not: Stacks 0864 part (1),
`AlgebraicGeometry.Space.isBlowupAlong_strictTransform`, already says that the strict transform
`X' ⟶ X` of `f : X ⟶ A` along a blowing up of `A` in `Z` *is* a blowing up of `X` in `f⁻¹Z`, and
that is exactly the clause `AlgebraicGeometry.Space.IsAdmissibleBlowup` asks for.  (The
composite comparison is still a real gap, and is filled for its own sake in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyStep1StrictTransformComp.lean`.)

**Where each hypothesis is used.**  `ha`, affineness of `X ⟶ X₀`, is used three times: to make
the pulled-back stratum affine over the stratum (base change, Stacks 03WI), hence to make the
strict transform affine over the blowup (`isAffineHom_strictTransformSpaceToBlowUp`), hence to
carry the resolution property up (Stacks 0GUU).  `hX₀qc` and `hX₀qs` are used only to see that
the blowup `Y_i` of a stratum is quasi-compact and quasi-separated, which is what Stacks 0GUU
asks of the space the resolution property comes from: a stratum is a closed subspace of `X₀` and
an admissible blowing up is proper (Stacks 085Z, via
`AlgebraicGeometry.Space.IsAdmissibleBlowup.isProper`).  Both hold for the `X₀` that Step 1
produces, which is Noetherian.  **Nothing else is assumed, and no clause of the conclusion is
dropped**: the output is the same predicate at `⊤` for `X`.

**The strata are pulled back as subfunctors, not as spaces.**  As in
`AlgebraicGeometry.Space.IsResolutionBlowupStratified` itself the chain's members are
subfunctors of the ambient space, so `Z_i ⊆ X₀` is pulled back to the subfunctor
`(Z_i).preimage a` of `X`, whose inclusion is the base change of `(Z_i).ι` — this is Stacks
083Q, `CategoryTheory.Subfunctor.isPullback_preimage`.  Closedness, finite presentation and the
point set of the pullback are then the three base-change statements
`AlgebraicGeometry.Space.isClosedSubspace_preimage`,
`AlgebraicGeometry.Space.isFinitePresentation_of_isPullback` and
`AlgebraicGeometry.Space.subspacePointSet_preimage`.

## References

* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 085Z](https://stacks.math.columbia.edu/tag/085Z)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of a subspace of a closed subspace, pulled back -/

/-- **The point set of a pulled-back subspace of a closed subspace.**  Let `G` be a closed
subspace of `F`, let `T ⊆ G` be any subfunctor and let `g : F' ⟶ F`.  Pulling `G` back along `g`
gives a closed subspace `g⁻¹G ⊆ F'` with its map `g⁻¹G ⟶ G`, and pulling `T` back along that map
gives a subspace of `g⁻¹G`.  Its set of points *measured in `F'`* is the `g`-preimage of the set
of points of `T` measured in `F`.

This is the only point-set computation Step 1 of Stacks 0GV6 needs beyond
`AlgebraicGeometry.Space.subspacePointSet_preimage`, and it is where closedness of `G` enters:
the inclusion of a closed subspace is injective on points (Stacks 0ABJ), which is what makes the
inclusion `⊇` work. -/
theorem range_pointsMap_preimage_fromPreimage_ι_comp
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (g : F' ⟶ F) {G : Subfunctor F} (hG : IsClosedSubspace B S hS G)
    (T : Subfunctor G.toFunctor) :
    Set.range (pointsMap B S hS (T.preimage (G.fromPreimage g)).toFunctor
        ((T.preimage (G.fromPreimage g)).ι ≫ (G.preimage g).ι)) =
      pointsMap B S hS F' g ⁻¹' Set.range (pointsMap B S hS T.toFunctor (T.ι ≫ G.ι)) := by
  have hinj : Function.Injective (pointsMap B S hS G.toFunctor G.ι) :=
    (isEmbedding_pointsMap_of_isImmersion B S hS hF G.ι
      (isImmersion_of_isClosedImmersion B S hS hG.2)).injective
  have hcompat : ∀ x, pointsMap B S hS F' g
      (pointsMap B S hS (G.preimage g).toFunctor (G.preimage g).ι x) =
        pointsMap B S hS G.toFunctor G.ι
          (pointsMap B S hS (G.preimage g).toFunctor (G.fromPreimage g) x) := by
    have hmap := congrArg (pointsMap B S hS (G.preimage g).toFunctor)
      (Subfunctor.fromPreimage_ι G g).symm
    rw [pointsMap_comp, pointsMap_comp] at hmap
    exact congrFun hmap
  rw [pointsMap_comp, Set.range_comp, range_pointsMap_preimage_ι, pointsMap_comp, Set.range_comp]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_preimage, hcompat x]
    exact Set.mem_image_of_mem _ hx
  · rintro ⟨s, hs, hsy⟩
    obtain ⟨x, rfl⟩ :
        y ∈ Set.range (pointsMap B S hS (G.preimage g).toFunctor (G.preimage g).ι) := by
      rw [range_pointsMap_preimage_ι]
      exact ⟨s, hsy⟩
    refine ⟨x, ?_, rfl⟩
    rw [Set.mem_preimage, hinj ((hcompat x).symm.trans hsy.symm)]
    exact hs

/-! ### The strict transform of the pullback of a stratum -/

/-- **The strict transform of the pullback of a stratum is an admissible blowing up of it, and
its source is affine over the original blowup.**  Let `b : Y ⟶ A` be a `V`-admissible blowing up
of an algebraic space `A`, let `c : A₁ ⟶ A` be an *affine* morphism, and let `Y₁` be the strict
transform of `A₁` with respect to `b` and the inverse image in `Y` of the centre of `b`.  Then
`Y₁ ⟶ A₁` is a `c⁻¹V`-admissible blowing up, and `Y₁ ⟶ Y` is affine.

The blowing-up clause is Stacks 0864 part (1),
`AlgebraicGeometry.Space.isBlowupAlong_strictTransform`: the strict transform of `c` along the
blowing up of `A` in the centre `Z` is a blowing up of `A₁` in `c⁻¹Z`.  Admissibility adds that
`c⁻¹Z` is of finite presentation — base change, Stacks 084Q through
`AlgebraicGeometry.Space.isFinitePresentation_of_isPullback` — and that its points avoid those
of `c⁻¹V`, which holds because preimages of disjoint sets are disjoint.  Affineness over `Y` is
`AlgebraicGeometry.Space.isAffineHom_strictTransformSpaceToBlowUp`, the source's "the strict
transform of an affine morphism is affine". -/
theorem isAdmissibleBlowup_strictTransform_preimage {A A₁ Y : AlgebraicSpaces B S hS}
    (c : A₁ ⟶ A) (hc : IsAffineHom B S hS c.hom) (V : OpenSubspaces B S hS A.1) (b : Y ⟶ A)
    (hb : IsAdmissibleBlowup B S hS V b) :
    ∃ (Y₁ : AlgebraicSpaces B S hS) (b₁ : Y₁ ⟶ A₁) (q : Y₁ ⟶ Y),
      IsAdmissibleBlowup B S hS
          ⟨V.1.preimage c.hom, isOpenSubspace_preimage B S hS c.hom V.1 A.2 A₁.2 V.2⟩ b₁ ∧
        IsAffineHom B S hS q.hom := by
  obtain ⟨Z, hZfp, hZdisj, hZbl⟩ := hb
  refine ⟨strictTransformSpace B S hS c b (preimageClosedSubspace b Z).1,
    strictTransformSpaceι B S hS c b (preimageClosedSubspace b Z).1 ≫
      strictTransformPullbackToSource B S hS c b,
    strictTransformSpaceToBlowUp B S hS c b (preimageClosedSubspace b Z).1,
    ⟨preimageClosedSubspace c Z, ?_, ?_, isBlowupAlong_strictTransform B S hS c b Z hZbl⟩,
    isAffineHom_strictTransformSpaceToBlowUp B S hS c b hc _⟩
  · exact isFinitePresentation_of_isPullback B S hS (preimageClosedSubspace c Z).2.1 Z.2.1 A₁.2
      A.2 (Subfunctor.isPullback_preimage c.hom Z.1) hZfp
  · rw [subspacePointSet_preimage B S hS c.hom V.1]
    exact (hZdisj.preimage _).mono_right (subspacePointSet_preimage B S hS c.hom Z.1).le

/-! ### Step 1's pullback of the whole chain -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The omitted details of Step 1 of the proof of Stacks 0GV6.**  Let `a : X ⟶ X₀` be an
affine morphism of algebraic spaces over `S` with `X₀` quasi-compact and quasi-separated.  If
`X₀` carries the chain of Stacks 0GV6 then so does `X`.

The chain over `X` is the chain over `X₀` pulled back: `Z_i` becomes `a⁻¹Z_i`, the open
`U_i ⊆ Z_i` becomes its inverse image in `a⁻¹Z_i`, and the blowing up `Y_i ⟶ Z_i` becomes the
strict transform of `a⁻¹Z_i ⟶ Z_i` with respect to it.  Closedness, finite presentation and
point sets of the strata are base change (Stacks 083Q, 084Q); that the strict transform is an
admissible blowing up of `a⁻¹Z_i` is Stacks 0864 part (1); and that it has the resolution
property is Stacks 0GUU applied to the affine morphism from it to `Y_i`, which is affine because
`a` is — the source's "the strict transform of an affine morphism is affine",
`AlgebraicGeometry.Space.isAffineHom_strictTransformSpaceToBlowUp`.

No hypothesis beyond the source's own is used, and no clause of the conclusion is dropped; see
the module documentation for where `ha`, `hX₀qc` and `hX₀qs` are used, all three of which hold
for the `X₀` that absolute Noetherian approximation supplies. -/
theorem IsResolutionBlowupStratified.pullback_of_isAffineHom {X X₀ : AlgebraicSpaces B S hS}
    (a : X ⟶ X₀) (ha : IsAffineHom B S hS a.hom)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀.1)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1)
    (h : IsResolutionBlowupStratified B S hS X₀ ⊤) :
    IsResolutionBlowupStratified B S hS X ⊤ := by
  obtain ⟨t, Z, hZcl, hZfp, hZmono, -, hZ₀pts, hZt, hstep⟩ := h
  -- the pulled-back strata, and their three base-change properties
  have hWcl : ∀ i, IsClosedSubspace B S hS ((Z i).preimage a.hom) := fun i =>
    isClosedSubspace_preimage B S hS a.hom (Z i) X₀.2 X.2 (hZcl i)
  have hWpts : ∀ i, subspacePointSet B S hS X.1 ((Z i).preimage a.hom) =
      pointsMap B S hS X.1 a.hom ⁻¹' subspacePointSet B S hS X₀.1 (Z i) := fun i =>
    subspacePointSet_preimage B S hS a.hom (Z i)
  have htop : ∀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      subspacePointSet B S hS F (⊤ : Subfunctor F) = Set.univ := fun F =>
    Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor F).ι)
  refine ⟨t, fun i => (Z i).preimage a.hom, hWcl, fun i => ?_, fun i => ?_, le_top, ?_, ?_,
    fun i hi => ?_⟩
  · exact isFinitePresentation_of_isPullback B S hS (hWcl i).1 (hZcl i).1 X.2 X₀.2
      (Subfunctor.isPullback_preimage a.hom (Z i)) (hZfp i)
  · exact fun n x hx => hZmono i n hx
  · rw [hWpts 0, hZ₀pts, htop, htop, Set.preimage_univ]
  · rw [hWpts t, hZt, Set.preimage_empty]
  -- the stratum `i`, its blowup, and the strict transform
  obtain ⟨U, Y, f, hUpts, hadm, hres⟩ := hstep i hi
  have hAiqc : IsQuasiCompactSpace B S hS (Z i).toFunctor :=
    isQuasiCompactSpace_of_isClosedImmersion B S hS hX₀qc (Z i).ι (hZcl i).2
  have hAiqs : IsAbsolutelyQuasiSeparated B S hS hZ (Z i).toFunctor :=
    isAbsolutelyQuasiSeparated_of_mono B S hS hZ (hZcl i).1 (Z i).ι inferInstance hX₀qs
  have hproper : IsProper B S hS f.hom := hadm.isProper B S hS
  have hYqc : IsQuasiCompactSpace B S hS Y.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS (hZcl i).1 hAiqc hproper.2.1.2
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ Y.2 hAiqs
      (isQuasiSeparated_of_isSeparated B S hS hproper.1)
  have hc : IsAffineHom B S hS
      (ObjectProperty.homMk ((Z i).fromPreimage a.hom) :
        (⟨((Z i).preimage a.hom).toFunctor, (hWcl i).1⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(Z i).toFunctor, (hZcl i).1⟩).hom :=
    IsAffineHom.of_isPullback (Subfunctor.isPullback_preimage a.hom (Z i)).flip ha
  obtain ⟨Y₁, b₁, q, hb₁, hq⟩ :=
    isAdmissibleBlowup_strictTransform_preimage B S hS _ hc U f hadm
  refine ⟨⟨U.1.preimage ((Z i).fromPreimage a.hom),
    isOpenSubspace_preimage B S hS _ U.1 (hZcl i).1 (hWcl i).1 U.2⟩, Y₁, b₁, ?_, hb₁,
    hasResolutionProperty_source_of_isAffineHom hZ q hq hYqc hYqs hres⟩
  rw [range_pointsMap_preimage_fromPreimage_ι_comp B S hS X₀.2 a.hom (hZcl i) U.1, hUpts,
    hWpts i, hWpts (i + 1), Set.preimage_diff]

end AlgebraicGeometry.Space

end
