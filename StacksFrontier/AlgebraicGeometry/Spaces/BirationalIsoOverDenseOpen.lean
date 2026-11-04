module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalDenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalGenericStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# A birational morphism is an isomorphism over a dense open subspace

Let `f : X ⟶ Y` be a birational morphism of algebraic spaces over a scheme `S` which are
decent and have finitely many irreducible components. Assume that `f` is quasi-compact or
separated, and that `f` is locally of finite type with `Y` reduced or locally of finite
presentation. Then there is a dense open subspace `V ⊂ Y` over which `f` becomes an
isomorphism. This is **Stacks 0BBF**.

## Main results

* `AlgebraicGeometry.Space.exists_isDenseOpenSubspace_isIso_pullback_snd_of_isBirational`:
  **Stacks 0BBF**.

## Implementation notes

Density of an open subspace is density of the range of its map on points for the canonical
topology of Stacks 03BX, and the restriction of `f` over an open subspace is the second
projection of the fibre product, as in Stacks 0BBC.

The source shrinks the target twice and the two shrinkings are intersected here. Stacks 0BBC
supplies a dense open `V₀ ⊂ Y` over which `f` is finite; its hypotheses are the finiteness of
the two sets of codimension-zero points, which is condition (2) of Stacks 0BB9, and the
equality `f^{-1}(Y⁰) = X⁰`. One inclusion of that equality is
`AlgebraicGeometry.Space.localRingDimension_eq_zero_of_isBirational`; the other says that a
point over a codimension-zero point of `Y` is itself of codimension zero, and is read off
Stacks 0BBD: the base change of `f` to the spectrum of the local ring of `Y` at a generic
point `y` is an isomorphism, hence injective on points, so any two points of `X` over `y`
lift to the same point of the base change along one and the same point of that spectrum, and
are therefore equal; one of them is the generic point of `X` over `y` supplied by
birationality. The point of that spectrum lying over `y` is its closed point.

Stacks 0BBE supplies dense opens `U ⊂ X` and `V ⊂ Y` and an isomorphism `ψ : U ⟶ V` over `f`.
Over a dense open `W ⊂ V` the isomorphism gives a section `t : W ⟶ f^{-1}(W)` of the
projection `f^{-1}(W) ⟶ W`, namely the composite of `W ⟶ V`, the inverse of `ψ` and
`U ⟶ X`. That section is an open immersion, since its composite with the open immersion
`f^{-1}(W) ⟶ X` is one; its range is dense, being the preimage of the dense range of `U ⟶ X`
along the open map `f^{-1}(W) ⟶ X`; and its range is closed by Stacks 04NX, since the
identity is universally closed and `f^{-1}(W) ⟶ W` is separated, which is where finiteness
over `V₀` is used. So the section is surjective on points, hence an isomorphism by
Stacks 03MD, and therefore so is `f^{-1}(W) ⟶ W`.

## References

* [Stacks Project, Tag 0BBF](https://stacks.math.columbia.edu/tag/0BBF)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 0BB9](https://stacks.math.columbia.edu/tag/0BB9)
* [Stacks Project, Tag 0BBC](https://stacks.math.columbia.edu/tag/0BBC)
* [Stacks Project, Tag 0BBD](https://stacks.math.columbia.edu/tag/0BBD)
* [Stacks Project, Tag 0BBE](https://stacks.math.columbia.edu/tag/0BBE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre over a generic point -/

/-- The spectrum of the local ring of an algebraic space at a generic point has a point
lying over that generic point, namely its closed point. -/
private theorem exists_pointsMap_fromGenericStalk_eq
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (y : points B S hS Y)
    (hy : letI := pointTopology B S hS Y
      y ∈ genericPoints (points B S hS Y)) :
    ∃ z : points B S hS
        (yoneda.obj (genericStalkSpec B S hS hY hdenseY hfiniteY y hy)),
      pointsMap B S hS _ (fromGenericStalk B S hS hY hdenseY hfiniteY y hy) z = y := by
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS
    (genericStalkSpec B S hS hY hdenseY hfiniteY y hy)
    (IsLocalRing.closedPoint (genericLocalRing B S hS hY hdenseY hfiniteY y hy))
  refine ⟨z, ?_⟩
  have hfac : fromGenericStalk B S hS hY hdenseY hfiniteY y hy =
      yoneda.map (genericStalkInclusion B S hS hY hdenseY hfiniteY y hy) ≫
        schematicChart B S hS hY := rfl
  have hpt : pointsMap B S hS _
        (yoneda.map (genericStalkInclusion B S hS hY hdenseY hfiniteY y hy)) z =
      (schematicRepresentative B S hS hY hdenseY hfiniteY y hy).class B S hS
        (yoneda.obj (schematicScheme B S hS hY)) := by
    apply injective_pointsToScheme B S hS (schematicScheme B S hS hY)
    rw [pointsToScheme_pointsMap, hz, toScheme_map_genericStalkInclusion]
    exact Scheme.fromSpecStalk_closedPoint
  rw [hfac, pointsMap_comp_apply, hpt]
  exact (exists_schematicRepresentative B S hS hY hdenseY hfiniteY y hy).choose_spec

/-- **A birational morphism of decent algebraic spaces reflects codimension zero.** Together
with `AlgebraicGeometry.Space.localRingDimension_eq_zero_of_isBirational` this identifies the
preimage of the set of codimension-zero points of the target with the set of codimension-zero
points of the source.

Birationality supplies a generic point of the source over a given generic point `y` of the
target, and Stacks 0BBD makes the base change of the morphism to the spectrum of the local
ring at `y` an isomorphism, so there is no room for a second point over `y`. -/
private theorem preimage_codimensionZeroPoints_of_isBirational
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f) :
    (pointsMap B S hS X f) ⁻¹' {y : points B S hS Y | localRingDimension B S hS y = 0} =
      {x : points B S hS X | localRingDimension B S hS x = 0} := by
  have hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hygen : pointsMap B S hS X f x ∈ genericPoints (points B S hS Y) :=
      (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hdecentY _).2 hx
    obtain ⟨η, hη, hηy⟩ :=
      (hf.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY).surjOn hygen
    have : IsIso (pullback.snd f
        (fromGenericStalk B S hS hY hdenseY hfiniteY _ hygen)) :=
      isIso_pullback_snd_fromGenericStalk_of_isBirational B S hS hY hfiniteY _ hygen
        hdecentY hX hdecentX hfiniteX f hf
    obtain ⟨z, hz⟩ := exists_pointsMap_fromGenericStalk_eq B S hS hY hdenseY hfiniteY _ hygen
    have sq := IsPullback.of_hasPullback f (fromGenericStalk B S hS hY hdenseY hfiniteY _ hygen)
    obtain ⟨w, hwx, hwz⟩ := exists_points_of_isPullback B S hS sq x z (by rw [hz])
    obtain ⟨w', hw'η, hw'z⟩ := exists_points_of_isPullback B S hS sq η z (by rw [hz, hηy])
    obtain rfl : x = η := by
      rw [← hwx, pointsMap_injective_of_mono B S hS _ (hwz.trans hw'z.symm), hw'η]
    exact (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hdecentX _).1 hη
  · exact localRingDimension_eq_zero_of_isBirational B S hS hX hY
      hfiniteX hfiniteY hdecentX hdecentY hf x hx

/-! ### Gluing an isomorphism over a dense open subspace -/

/-- A separated morphism of algebraic spaces with a section which is an open immersion with
dense range is an isomorphism. -/
theorem isIso_of_isOpenImmersion_section_of_dense
    {P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hW : IsAlgebraicSpace B S hS W)
    (p : P ⟶ W) (t : W ⟶ P) (ht : t ≫ p = 𝟙 _)
    (htopen : IsOpenImmersion B S hS t)
    (hdense : Dense (Set.range (pointsMap B S hS W t)))
    (hsep : IsSeparated B S hS p) : IsIso p := by
  have htclosed : _root_.IsClosed (Set.range (pointsMap B S hS W t)) :=
    isClosed_range_of_comp_of_isSeparated B S hS hW hP hW _ p
      (ht ▸ universallyClosed_of_isIso B S hS _) hsep
  have hsurj : Function.Surjective (pointsMap B S hS W t) := by
    apply Set.range_eq_univ.mp
    simpa only [htclosed.closure_eq] using hdense.closure_eq
  have : IsIso t :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _ htopen
      (presheafSurjective_of_isSurjective B S hS _ htopen.rep hsurj)
  have : IsIso (t ≫ p) := by
    rw [ht]
    infer_instance
  exact IsIso.of_isIso_comp_left t p

/-- **A morphism which restricts to an isomorphism of dense open subspaces is an isomorphism
over any dense open subspace of the target over which it is separated.** The inverse of the
given isomorphism provides a section of the restriction whose range is open, dense and
closed, hence everything. -/
private theorem isIso_pullback_snd_of_isIso_restriction
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) {U : Subfunctor X} {V W : Subfunctor Y}
    (hU : IsOpenSubspace B S hS U) (hV : IsOpenSubspace B S hS V)
    (hW : IsOpenSubspace B S hS W)
    (ψ : U.toFunctor ⟶ V.toFunctor) [IsIso ψ] (hψ : ψ ≫ V.ι = U.ι ≫ f)
    (hUdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hWV : W ≤ V) (hfin : IsFinite B S hS (pullback.snd f W.ι)) :
    IsIso (pullback.snd f W.ι) := by
  have : Mono V.ι := mono_of_presheaf_isOpenImmersion hV.2
  have : Mono W.ι := mono_of_presheaf_isOpenImmersion hW.2
  have hP := isAlgebraicSpace_pullback B S hS f W.ι hX hW.1 hY
  have hal : Subfunctor.homOfLe hWV ≫ V.ι = W.ι := Subfunctor.homOfLe_ι hWV
  have hcond : (Subfunctor.homOfLe hWV ≫ inv ψ ≫ U.ι) ≫ f = 𝟙 W.toFunctor ≫ W.ι := by
    calc (Subfunctor.homOfLe hWV ≫ inv ψ ≫ U.ι) ≫ f
        = Subfunctor.homOfLe hWV ≫ inv ψ ≫ (U.ι ≫ f) := by simp
      _ = Subfunctor.homOfLe hWV ≫ inv ψ ≫ (ψ ≫ V.ι) := by rw [hψ]
      _ = Subfunctor.homOfLe hWV ≫ V.ι := by simp
      _ = 𝟙 W.toFunctor ≫ W.ι := by rw [hal, Category.id_comp]
  obtain ⟨t, ht, htj⟩ : ∃ t : W.toFunctor ⟶ pullback f W.ι,
      t ≫ pullback.snd f W.ι = 𝟙 _ ∧
        t ≫ pullback.fst f W.ι = Subfunctor.homOfLe hWV ≫ inv ψ ≫ U.ι :=
    ⟨_, pullback.lift_snd _ _ hcond, pullback.lift_fst _ _ hcond⟩
  have hfst : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f W.ι).flip hW.2
  have : Mono (pullback.fst f W.ι) := mono_of_presheaf_isOpenImmersion hfst
  have ha : IsOpenImmersion B S hS (Subfunctor.homOfLe hWV) := by
    refine MorphismProperty.presheaf_of_comp_mono _ (m := V.ι) ?_
    rw [hal]
    exact hW.2
  have htopen : IsOpenImmersion B S hS t := by
    refine MorphismProperty.presheaf_of_comp_mono _ (m := pullback.fst f W.ι) ?_
    rw [htj]
    exact isOpenImmersion_comp B S hS _ _ ha
      (MorphismProperty.RespectsIso.precomp _ (inv ψ) U.ι hU.2)
  have : Mono (U.ι ≫ f) := by
    rw [← hψ]
    infer_instance
  have outer : IsPullback (Subfunctor.homOfLe hWV ≫ inv ψ) (𝟙 W.toFunctor) (U.ι ≫ f) W.ι :=
    IsPullback.of_vert_isIso_mono ⟨by simpa only [Category.assoc] using hcond⟩
  have sq : IsPullback (Subfunctor.homOfLe hWV ≫ inv ψ) t U.ι (pullback.fst f W.ι) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f W.ι) (v₂₂ := f) (h₃₁ := W.ι) ?_ ?_ ?_
    · simpa only [ht] using outer
    · simpa only [Category.assoc] using htj.symm
    · exact IsPullback.of_hasPullback f W.ι
  have hrange : Set.range (pointsMap B S hS W.toFunctor t) =
      (pointsMap B S hS (pullback f W.ι) (pullback.fst f W.ι)) ⁻¹'
        Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    simpa only [Set.image_univ, Set.preimage_univ] using
      (preimage_image_pointsMap_of_isPullback B S hS sq Set.univ).symm
  have htdense : Dense (Set.range (pointsMap B S hS W.toFunctor t)) := by
    rw [hrange]
    exact hUdense.preimage
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS (pullback.fst f W.ι) hfst)
  exact isIso_of_isOpenImmersion_section_of_dense B S hS hP hW.1 _ t ht htopen htdense
    (isSeparated_of_isFinite B S hS _ hP hW.1 hfin)

/-! ### Stacks 0BBF -/

/-- **Stacks 0BBF.** Let `f : X ⟶ Y` be a birational morphism of algebraic spaces over a
scheme `S` which are decent and have finitely many irreducible components. Assume that `f` is
quasi-compact or separated, and that `f` is locally of finite type with `Y` reduced or locally
of finite presentation. Then there is a dense open subspace `V ⊂ Y` such that `f^{-1}(V) ⟶ V`
is an isomorphism.

The source shrinks `Y` to a dense open over which `f` is finite, by Stacks 0BBC, and
separately to a dense open over which `f` restricts to an isomorphism of dense opens, by
Stacks 0BBE; the intersection of the two is the open subspace produced here. See the module
docstring. -/
@[stacks 0BBF]
theorem exists_isDenseOpenSubspace_isIso_pullback_snd_of_isBirational
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hbir : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (hqc_or_sep : IsQuasiCompact B S hS f ∨ IsSeparated B S hS f)
    (hfin : (IsLocallyOfFiniteType B S hS f ∧
        HasEtaleLocalProperty B S hS Y
          (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z)) ∨
      IsLocallyOfFinitePresentation B S hS f) :
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
        Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
          IsIso (pullback.snd f V.ι) := by
  have hLft : IsLocallyOfFiniteType B S hS f :=
    hfin.elim (·.1) (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS)
  have hXzero : {x : points B S hS X | localRingDimension B S hS x = 0}.Finite :=
    (IsDecentWithFinitelyManyComponents.hasQuasiCompactGenericDenseOpenScheme B S hS hX
      ⟨hdecentX, hfiniteX⟩).hasFiniteCodimensionZeroPoints B S hS hX
  have hYzero : {y : points B S hS Y | localRingDimension B S hS y = 0}.Finite :=
    (IsDecentWithFinitelyManyComponents.hasQuasiCompactGenericDenseOpenScheme B S hS hY
      ⟨hdecentY, hfiniteY⟩).hasFiniteCodimensionZeroPoints B S hS hY
  obtain ⟨V₀, hV₀, hV₀dense, hV₀finite⟩ :=
    exists_isDenseOpenSubspace_isFinite_pullback_snd B S hS hX hY f hLft hdecentY hXzero hYzero
      (preimage_codimensionZeroPoints_of_isBirational B S hS hX hY hdecentX hdecentY
        hfiniteX hfiniteY f hbir)
      hqc_or_sep
  obtain ⟨U, V, ψ, hU, hV, hUdense, hVdense, hψ, hψiso⟩ :=
    exists_dense_isOpenSubspace_isIso_of_isBirational B S hS hX hY hdecentX hdecentY
      hfiniteX hfiniteY f hbir hfin
  have : IsIso ψ := hψiso
  -- The intersection of the two dense open subspaces, again an open subspace.
  obtain ⟨W, hW, hWpoints⟩ :=
    exists_isOpenSubspace_range_pointsMap_eq B S hS hY
      (Set.range (pointsMap B S hS V₀.toFunctor V₀.ι) ∩
        Set.range (pointsMap B S hS V.toFunctor V.ι))
      ((isOpen_range_pointsMap_of_isOpenImmersion B S hS V₀.ι hV₀.2).inter
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2))
  have hW₀ : W ≤ V₀ :=
    le_of_range_pointsMap_ι_subset B S hS hV₀ (hWpoints.subset.trans Set.inter_subset_left)
  have hWV : W ≤ V :=
    le_of_range_pointsMap_ι_subset B S hS hV (hWpoints.subset.trans Set.inter_subset_right)
  have hWdense : Dense (Set.range (pointsMap B S hS W.toFunctor W.ι)) := by
    rw [hWpoints]
    exact hV₀dense.inter_of_isOpen_right hVdense
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2)
  -- Finiteness over `V₀` descends to `W` and makes the restriction separated.
  have hcond : pullback.fst f W.ι ≫ f = (pullback.snd f W.ι ≫ Subfunctor.homOfLe hW₀) ≫ V₀.ι := by
    rw [Category.assoc, Subfunctor.homOfLe_ι]
    exact pullback.condition
  have sqW : IsPullback
      (pullback.lift (pullback.fst f W.ι) (pullback.snd f W.ι ≫ Subfunctor.homOfLe hW₀) hcond)
      (pullback.snd f W.ι) (pullback.snd f V₀.ι) (Subfunctor.homOfLe hW₀) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f V₀.ι) (h₂₂ := V₀.ι)
      (v₁₃ := f) ?_ ?_ ?_
    · simpa only [pullback.lift_fst, Subfunctor.homOfLe_ι] using IsPullback.of_hasPullback f W.ι
    · exact pullback.lift_snd _ _ _
    · exact IsPullback.of_hasPullback f V₀.ι
  have hWfinite : IsFinite B S hS (pullback.snd f W.ι) :=
    isFinite_of_isPullback B S hS sqW hV₀finite
  exact ⟨W, hW, hWdense, isIso_pullback_snd_of_isIso_restriction B S hS hX hY f hU hV hW ψ
    hψ hUdense hWV hWfinite⟩

end AlgebraicGeometry.Space

end
