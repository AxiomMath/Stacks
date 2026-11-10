module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.PointsRelocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspaceOfSubspace

/-!
# Elementary distinguished squares of algebraic spaces

An *elementary distinguished square* on an algebraic space `W` over a scheme `S` consists of
an open subspace `U` of `W` and an étale morphism `f : V ⟶ W` which restricts to an
isomorphism over the reduced closed complement of `U`. Such squares are the induction data
for algebraic spaces: a property of quasi-compact and quasi-separated algebraic spaces which
holds on affine schemes and descends along elementary distinguished squares holds in general.

## Main definitions

* `AlgebraicGeometry.Space.IsElementaryDistinguishedSquare` is the elementary
  distinguished square condition for an open subspace and a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_iff` unfolds the condition into
  openness of the subspace, étaleness of the morphism and an isomorphism over the reduced
  complement.
* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_openRestriction` restricts a
  square to an open subspace of the source and a larger open subspace of the target: the
  union of the two is an open subspace over which the restricted square is again elementary
  distinguished.
* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_preimage` base changes a square
  along a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_relocalizeRestrict` restricts a
  square along a morphism of base schemes of the site.

The last three are the three parts of Stacks 08GN.

## Implementation notes

The open subspace is a `CategoryTheory.Subfunctor`, so its inclusion is `U.ι` and its point
set is the range of `AlgebraicGeometry.Space.pointsMap` on that inclusion. The complement
`T = W \ U` of the source is the set-theoretic complement of that range; the field
`isClosedComplement` records that it is closed in the point topology, which is what allows
the reduced closed subspace `AlgebraicGeometry.Space.reducedClosedSubspace` on it to be
formed. The restriction `f^{-1}(T) ⟶ T` of the source is the canonical morphism
`CategoryTheory.Subfunctor.fromPreimage` out of the preimage subspace, and the last field
asks exactly that it be an isomorphism. The square `U ×_W V` of the source is the preimage
of `U` along `f`; it is not part of the data, since it is determined by `U` and `f`.

Each of the three parts of Stacks 08GN produces a morphism into the reduced closed subspace on
the complement from a containment of point sets. That is the factorization criterion of Stacks
03JJ, which for a general closed subspace needs the subspace to be *closed* — the inclusion to
be representable by closed immersions. At the reduced closed subspace it does not:
`AlgebraicGeometry.Space.exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset` proves it
with no descent hypothesis, and
`AlgebraicGeometry.Space.isAlgebraicSpace_reducedClosedSubspace` supplies the algebraic-space
structure of the source of the lift, also unconditionally.

The ambient presheaf `W` is required to be an algebraic space, because the reduced closed
subspace is only constructed for one; `V` is required to be an algebraic space by a field of
the structure rather than by a binder, so that the condition can be stated for an arbitrary
morphism of presheaves into `W`.

## References

* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **Stacks 08GM.** An open subspace `U` of an algebraic space `W` together with an étale
morphism `f : V ⟶ W` which is an isomorphism over the reduced closed subspace on the
complement of `U` form an *elementary distinguished square*. -/
@[stacks 08GM]
structure IsElementaryDistinguishedSquare (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W) : Prop where
  /-- The source of the étale morphism is an algebraic space over `S`. -/
  isAlgebraicSpace : IsAlgebraicSpace B S hS V
  /-- The subfunctor `U` is an open subspace of `W`. -/
  isOpenSubspace : IsOpenSubspace B S hS U
  /-- The morphism `f` is étale. -/
  isEtale : IsEtale B S hS f
  /-- The complement of the point set of `U` is closed, so it carries a reduced closed
  subspace. -/
  isClosedComplement : IsClosed (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
  /-- The morphism `f` restricts to an isomorphism over the reduced closed complement
  of `U`. -/
  isIsoOverComplement :
    IsIso ((reducedClosedSubspace B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ isClosedComplement).fromPreimage f)

/-- An elementary distinguished square is exactly an open subspace together with an étale
morphism which is an isomorphism over the reduced closed complement of that subspace. -/
@[stacks 08GM "characterization"]
theorem isElementaryDistinguishedSquare_iff (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W) :
    IsElementaryDistinguishedSquare B S hS hW U f ↔
      (IsAlgebraicSpace B S hS V ∧ IsOpenSubspace B S hS U ∧ IsEtale B S hS f ∧
        ∃ hT : IsClosed (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ,
          IsIso ((reducedClosedSubspace B S hS W hW
            (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hT).fromPreimage f)) :=
  ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-! ### Base change -/

/-- Points over a pullback square of algebraic spaces with a common image lift to the
pullback. -/
private theorem exists_point_of_isPullback_of_isAlgebraicSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g)
    (x : points B S hS X) (y : points B S hS Y)
    (h : pointsMap B S hS X f x = pointsMap B S hS Y g y) :
    ∃ w : points B S hS P, pointsMap B S hS P p w = x ∧ pointsMap B S hS P q w = y :=
  exists_point_of_isPullback B S hS (W := ⟨P, hP⟩) (Z := ⟨X, hX⟩) (X := ⟨Y, hY⟩)
    (Y := ⟨Z, hZ⟩) (IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) sq) x y h

/-- Étaleness is stable under base change along a pullback square of algebraic spaces. -/
private theorem isEtale_of_isPullback_of_isAlgebraicSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g)
    (hf : IsEtale B S hS f) : IsEtale B S hS q :=
  isEtale_of_isPullback B S hS (X' := ⟨P, hP⟩) (X := ⟨X, hX⟩) (Z := ⟨Y, hY⟩) (Y := ⟨Z, hZ⟩)
    (ObjectProperty.homMk p) (ObjectProperty.homMk q) (ObjectProperty.homMk f)
    (ObjectProperty.homMk g) (IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) sq) hf

/-- **Stacks 08GN, part (2).** An elementary distinguished square stays elementary
distinguished after base change along any morphism of algebraic spaces: the open subspace is
replaced by its preimage and the étale morphism by its base change. -/
@[stacks 08GN "base_change"]
theorem isElementaryDistinguishedSquare_preimage (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {W V W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hW' : IsAlgebraicSpace B S hS W') (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) (p : W' ⟶ W) :
    IsElementaryDistinguishedSquare B S hS hW' (U.preimage p) (Limits.pullback.snd f p) := by
  classical
  have hUalg : IsAlgebraicSpace B S hS U.toFunctor := h.isOpenSubspace.1
  have hVAlg : IsAlgebraicSpace B S hS (Limits.pullback f p) :=
    isAlgebraicSpace_pullback B S hS f p h.isAlgebraicSpace hW' hW
  have hsqU : IsPullback (U.fromPreimage p) (U.preimage p).ι U.ι p :=
    Subfunctor.isPullback_preimage p U
  have hPreOpen : IsOpenSubspace B S hS (U.preimage p) :=
    isOpenSubspace_preimage B S hS p U hW hW' h.isOpenSubspace
  have hPreAlg : IsAlgebraicSpace B S hS (U.preimage p).toFunctor := hPreOpen.1
  have hEtale : IsEtale B S hS (Limits.pullback.snd f p) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hVAlg h.isAlgebraicSpace hW' hW
      (IsPullback.of_hasPullback f p) h.isEtale
  -- The point set of the preimage is the preimage of the point set.
  have hSupport : Set.range (pointsMap B S hS (U.preimage p).toFunctor (U.preimage p).ι) =
      pointsMap B S hS W' p ⁻¹' Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨pointsMap B S hS _ (U.fromPreimage p) z, ?_⟩
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, U.fromPreimage_ι p]
    · rintro ⟨z, hz⟩
      obtain ⟨w, _, hw⟩ := exists_point_of_isPullback_of_isAlgebraicSpace B S hS hPreAlg hUalg
        hW' hW hsqU z x hz
      exact ⟨w, hw⟩
  have hComplementClosed :
      IsClosed (Set.range (pointsMap B S hS (U.preimage p).toFunctor (U.preimage p).ι))ᶜ := by
    simpa only [hSupport, Set.preimage_compl] using
      h.isClosedComplement.preimage (continuous_pointsMap B S hS p)
  refine ⟨hVAlg, hPreOpen, hEtale, hComplementClosed, ?_⟩
  -- The two reduced closed complements, and the lift of the new one into the old one.
  set T : Subfunctor W :=
    reducedClosedSubspace B S hS W hW (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
      h.isClosedComplement with hT
  set T' : Subfunctor W' := reducedClosedSubspace B S hS W' hW'
    (Set.range (pointsMap B S hS (U.preimage p).toFunctor (U.preimage p).ι))ᶜ
    hComplementClosed with hT'
  have hT'alg : IsAlgebraicSpace B S hS T'.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS W' hW' _ _
  have hT'red : HasEtaleLocalProperty B S hS T'.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS W' hW' _ _
  have hTsupp : Set.range (pointsMap B S hS T.toFunctor T.ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS W hW _ _
  have hT'supp : Set.range (pointsMap B S hS T'.toFunctor T'.ι) =
      (Set.range (pointsMap B S hS (U.preimage p).toFunctor (U.preimage p).ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS W' hW' _ _
  have hfactorPoints : Set.range (pointsMap B S hS T'.toFunctor (T'.ι ≫ p)) ⊆
      Set.range (pointsMap B S hS T.toFunctor T.ι) := by
    rw [pointsMap_comp, Set.range_comp, hT'supp, hTsupp, hSupport, ← Set.preimage_compl]
    exact Set.image_preimage_subset _ _
  obtain ⟨g, hg⟩ : ∃ g : T'.toFunctor ⟶ T.toFunctor, g ≫ T.ι = T'.ι ≫ p :=
    (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ h.isClosedComplement hT'alg hT'red
      (T'.ι ≫ p)).2 (hTsupp ▸ hfactorPoints)
  -- The restriction of the base-changed morphism over the new complement is a base change of
  -- the restriction of `f` over the old one, hence an isomorphism.
  have hTiso : IsIso (T.fromPreimage f) := by rw [hT]; exact h.isIsoOverComplement
  have h1 : T'.fromPreimage (Limits.pullback.snd f p) ≫ T'.ι =
      (T'.preimage (Limits.pullback.snd f p)).ι ≫ Limits.pullback.snd f p :=
    Subfunctor.fromPreimage_ι T' (Limits.pullback.snd f p)
  have htf : ((T'.preimage (Limits.pullback.snd f p)).ι ≫ Limits.pullback.fst f p) ≫ f =
      (T'.fromPreimage (Limits.pullback.snd f p) ≫ g) ≫ T.ι :=
    calc ((T'.preimage (Limits.pullback.snd f p)).ι ≫ Limits.pullback.fst f p) ≫ f
        = (T'.preimage (Limits.pullback.snd f p)).ι ≫ Limits.pullback.snd f p ≫ p := by
          rw [Category.assoc, Limits.pullback.condition]
      _ = (T'.fromPreimage (Limits.pullback.snd f p) ≫ T'.ι) ≫ p := by
          rw [← Category.assoc, h1]
      _ = (T'.fromPreimage (Limits.pullback.snd f p) ≫ g) ≫ T.ι := by
          rw [Category.assoc, Category.assoc, hg]
  have sqT : IsPullback (T.fromPreimage f) (T.preimage f).ι T.ι f :=
    Subfunctor.isPullback_preimage f T
  have hOuter : IsPullback ((T'.preimage (Limits.pullback.snd f p)).ι ≫ Limits.pullback.fst f p)
      (T'.fromPreimage (Limits.pullback.snd f p)) f (g ≫ T.ι) := by
    simpa only [hg] using
      (Subfunctor.isPullback_preimage (Limits.pullback.snd f p) T').flip.paste_horiz
        (IsPullback.of_hasPullback f p)
  have hSmall : IsPullback
      (sqT.lift (T'.fromPreimage (Limits.pullback.snd f p) ≫ g)
        ((T'.preimage (Limits.pullback.snd f p)).ι ≫ Limits.pullback.fst f p) htf.symm)
      (T'.fromPreimage (Limits.pullback.snd f p)) (T.fromPreimage f) g := by
    refine IsPullback.of_right ?_ (sqT.lift_fst _ _ htf.symm) sqT.flip
    simpa only [sqT.lift_snd _ _ htf.symm] using hOuter
  exact hSmall.isIso_snd_of_isIso

/-! ### Restriction to open subspaces -/

/-- **Stacks 08GN, restriction to open subspaces.** Let `U ⊆ U'` be open subspaces of `W` and
let `V'` be an open subspace of `V`. The union of the point set of `U'` with the image of the
point set of `V'` is the point set of an open subspace `W'` of `W`; the morphism `V' ⟶ W`
factors through `W'`, and the square formed by `U'` inside `W'` and that factorisation is
again elementary distinguished.

The union is described by its set of points rather than as the range of `V'.ι ≫ f`, which
need not be an open subspace, and `U'` is presented inside `W'` as the range of the canonical
inclusion `U' ⟶ W'`. -/
@[stacks 08GN "open_restriction"]
theorem isElementaryDistinguishedSquare_openRestriction (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (f : V ⟶ W)
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f)
    (V' : Subfunctor V) (hV' : IsOpenSubspace B S hS V')
    (U' : Subfunctor W) (hU' : IsOpenSubspace B S hS U') (hUU' : U ≤ U') :
    ∃ (W' : Subfunctor W) (hW' : IsOpenSubspace B S hS W') (hU'W' : U' ≤ W')
      (f' : V'.toFunctor ⟶ W'.toFunctor),
      (Set.range (pointsMap B S hS W'.toFunctor W'.ι) =
        Set.range (pointsMap B S hS U'.toFunctor U'.ι) ∪
          Set.range (pointsMap B S hS V'.toFunctor (V'.ι ≫ f))) ∧
      (f' ≫ W'.ι = V'.ι ≫ f) ∧
      IsElementaryDistinguishedSquare B S hS hW'.1
        (Subfunctor.range (Subfunctor.homOfLe hU'W')) f' := by
  classical
  -- The open sets of points of `W` and of `V` corresponding to `U'` and to `V'`.
  let eW := openSubspacesOrderIso B S hS W hW
  let uo : {G : Subfunctor W // IsOpenSubspace B S hS G} := ⟨U', hU'⟩
  let sU : TopologicalSpace.Opens (points B S hS W) := eW uo
  let eV := openSubspacesOrderIso B S hS V hsq.isAlgebraicSpace
  let vo : {G : Subfunctor V // IsOpenSubspace B S hS G} := ⟨V', hV'⟩
  let sV : TopologicalSpace.Opens (points B S hS V) := eV vo
  have hsU : (sU : Set (points B S hS W)) =
      Set.range (pointsMap B S hS U'.toFunctor U'.ι) := by
    simpa [sU, uo] using openSubspacesOrderIso_apply B S hS W hW uo
  have hsV : (sV : Set (points B S hS V)) =
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    simpa [sV, vo] using openSubspacesOrderIso_apply B S hS V hsq.isAlgebraicSpace vo
  -- The image of the second is open, `f` being étale, so the union is an open subspace.
  have hImgOpen : IsOpen (pointsMap B S hS V f '' (sV : Set (points B S hS V))) :=
    isOpenMap_pointsMap_of_isEtale B S hS f hsq.isAlgebraicSpace hW hsq.isEtale _ sV.2
  let sW : TopologicalSpace.Opens (points B S hS W) :=
    ⟨(sU : Set (points B S hS W)) ∪
      pointsMap B S hS V f '' (sV : Set (points B S hS V)), sU.2.union hImgOpen⟩
  let wo : {G : Subfunctor W // IsOpenSubspace B S hS G} := eW.symm sW
  let W' : Subfunctor W := wo.1
  have hW' : IsOpenSubspace B S hS W' := wo.2
  have hrangeComp : Set.range (pointsMap B S hS V'.toFunctor (V'.ι ≫ f)) =
      pointsMap B S hS V f '' Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    rw [pointsMap_comp]
    exact Set.range_comp _ _
  have hWrange : Set.range (pointsMap B S hS W'.toFunctor W'.ι) =
      Set.range (pointsMap B S hS U'.toFunctor U'.ι) ∪
        Set.range (pointsMap B S hS V'.toFunctor (V'.ι ≫ f)) := by
    calc Set.range (pointsMap B S hS W'.toFunctor W'.ι) = (eW wo).1 := by
          simpa [W', wo, eW] using (openSubspacesOrderIso_apply B S hS W hW wo).symm
      _ = sW.1 := by rw [eW.apply_symm_apply]
      _ = Set.range (pointsMap B S hS U'.toFunctor U'.ι) ∪
          Set.range (pointsMap B S hS V'.toFunctor (V'.ι ≫ f)) := by
            dsimp only [sW]
            rw [hsU, hrangeComp, ← hsV]
  have hU'W' : U' ≤ W' := by
    change uo ≤ wo
    apply eW.le_iff_le.mp
    have hwo : eW wo = sW := eW.apply_symm_apply sW
    rw [hwo]
    change sU.1 ⊆ sW.1
    exact fun _ hx => Or.inl hx
  -- `V' ⟶ W` lands in `W'`, so it factors through it.
  have hpoints : Set.range (pointsMap B S hS V'.toFunctor (V'.ι ≫ f)) ⊆
      Set.range (pointsMap B S hS W'.toFunctor W'.ι) := by
    rw [hWrange]
    intro x hx
    exact Set.mem_union_right _ hx
  obtain ⟨f', hf'⟩ := (factorsThrough_openSubspace_iff_points B S hS hW hV'.1 W' hW'
    (V'.ι ≫ f)).2 hpoints
  refine ⟨W', hW', hU'W', f', hWrange, hf', ?_⟩
  let U'' := Subfunctor.range (Subfunctor.homOfLe hU'W')
  have hU'' : IsOpenSubspace B S hS U'' := isOpenSubspace_of_le B S hS U' W' hU' hU'W'
  have hClosed : IsClosed (Set.range (pointsMap B S hS U''.toFunctor U''.ι))ᶜ := by
    refine isClosed_compl_iff.mpr ?_
    rw [← openSubspacesOrderIso_apply B S hS W'.toFunctor hW'.1 ⟨U'', hU''⟩]
    exact (openSubspacesOrderIso B S hS W'.toFunctor hW'.1 ⟨U'', hU''⟩).2
  -- Étaleness of the factorisation: it is the inclusion of `V'` into the preimage of `W'`,
  -- which is an open subspace, followed by the base change of `f` over `W'`.
  have hRopen : IsOpenSubspace B S hS (W'.preimage f) :=
    isOpenSubspace_preimage B S hS f W' hW hsq.isAlgebraicSpace hW'
  have hpre : IsPullback (W'.fromPreimage f) (W'.preimage f).ι W'.ι f :=
    Subfunctor.isPullback_preimage f W'
  have hrEtale : IsEtale B S hS (W'.fromPreimage f) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hRopen.1 hsq.isAlgebraicSpace hW'.1 hW
      hpre.flip hsq.isEtale
  have hle : V' ≤ W'.preimage f := by
    intro A x hx
    change f.app A x ∈ W'.obj A
    have heq := congrArg (fun k : V'.toFunctor ⟶ W => k.app A ⟨x, hx⟩) hf'
    change (W'.ι.app A) (f'.app A ⟨x, hx⟩) = f.app A x at heq
    rw [← heq]
    exact (f'.app A ⟨x, hx⟩).property
  have hlEtale : IsEtale B S hS (Subfunctor.homOfLe hle) := by
    have h := isEtale_comp B S hS
      (isEtale_of_isIso B S hS (Subfunctor.toRange (Subfunctor.homOfLe hle)))
      (isEtale_ι_of_isOpenSubspace
        (isOpenSubspace_of_le B S hS V' (W'.preimage f) hV' hle))
    simpa only [Subfunctor.toRange_ι] using h
  have hlf : Subfunctor.homOfLe hle ≫ W'.fromPreimage f = f' := by
    apply (cancel_mono W'.ι).1
    calc (Subfunctor.homOfLe hle ≫ W'.fromPreimage f) ≫ W'.ι = V'.ι ≫ f := by
          rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
            Subfunctor.homOfLe_ι]
      _ = f' ≫ W'.ι := hf'.symm
  have hf'etale : IsEtale B S hS f' := by
    rw [← hlf]
    exact isEtale_comp B S hS hlEtale hrEtale
  -- The two reduced closed complements and a lift of the new one into the old one.
  let Tnew : Subfunctor W'.toFunctor := reducedClosedSubspace B S hS W'.toFunctor hW'.1
    (Set.range (pointsMap B S hS U''.toFunctor U''.ι))ᶜ hClosed
  let Told : Subfunctor W := reducedClosedSubspace B S hS W hW
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hsq.isClosedComplement
  have hTnewAlg : IsAlgebraicSpace B S hS Tnew.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS W'.toFunctor hW'.1 _ hClosed
  have hToldAlg : IsAlgebraicSpace B S hS Told.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS W hW _ hsq.isClosedComplement
  have hTnewRed : HasEtaleLocalProperty B S hS Tnew.toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS W'.toFunctor hW'.1 _ hClosed
  have hTnewSupport : Set.range (pointsMap B S hS Tnew.toFunctor Tnew.ι) =
      (Set.range (pointsMap B S hS U''.toFunctor U''.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS W'.toFunctor hW'.1 _ hClosed
  have hTnewAvoidsU' : Set.range (pointsMap B S hS Tnew.toFunctor (Tnew.ι ≫ W'.ι)) ⊆
      (Set.range (pointsMap B S hS U'.toFunctor U'.ι))ᶜ := by
    intro x hx
    obtain ⟨p, rfl⟩ := hx
    intro hpU'
    obtain ⟨q, hq⟩ := hpU'
    have hkW : Subfunctor.homOfLe hU'W' ≫ W'.ι = U'.ι := Subfunctor.homOfLe_ι hU'W'
    have hEqW' : pointsMap B S hS Tnew.toFunctor Tnew.ι p =
        pointsMap B S hS U'.toFunctor (Subfunctor.homOfLe hU'W') q := by
      apply pointsMap_injective_of_mono B S hS W'.ι
      simpa only [← pointsMap_comp_apply, hkW] using hq.symm
    have hr : Subfunctor.toRange (Subfunctor.homOfLe hU'W') ≫ U''.ι =
        Subfunctor.homOfLe hU'W' :=
      Subfunctor.toRange_ι (Subfunctor.homOfLe hU'W')
    have hU''map : pointsMap B S hS U''.toFunctor U''.ι
          (pointsMap B S hS U'.toFunctor
            (Subfunctor.toRange (Subfunctor.homOfLe hU'W')) q) =
        pointsMap B S hS U'.toFunctor (Subfunctor.homOfLe hU'W') q := by
      simp only [← pointsMap_comp_apply, hr]
    have hptRange : pointsMap B S hS Tnew.toFunctor Tnew.ι p ∈
        Set.range (pointsMap B S hS U''.toFunctor U''.ι) :=
      ⟨pointsMap B S hS U'.toFunctor
        (Subfunctor.toRange (Subfunctor.homOfLe hU'W')) q, hU''map.trans hEqW'.symm⟩
    exact (hTnewSupport ▸ (show pointsMap B S hS Tnew.toFunctor Tnew.ι p ∈
      Set.range (pointsMap B S hS Tnew.toFunctor Tnew.ι) from ⟨p, rfl⟩)) hptRange
  have hTnewAvoidsU : Set.range (pointsMap B S hS Tnew.toFunctor (Tnew.ι ≫ W'.ι)) ⊆
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ := by
    intro x hx hp
    obtain ⟨q, hq⟩ := hp
    refine hTnewAvoidsU' hx
      ⟨pointsMap B S hS U.toFunctor (Subfunctor.homOfLe hUU') q, ?_⟩
    calc _ = pointsMap B S hS U.toFunctor (Subfunctor.homOfLe hUU' ≫ U'.ι) q :=
          (congrFun (pointsMap_comp B S hS U.toFunctor
            (Subfunctor.homOfLe hUU') U'.ι) q).symm
      _ = pointsMap B S hS U.toFunctor U.ι q := by rw [Subfunctor.homOfLe_ι]
      _ = x := hq
  obtain ⟨j, hj⟩ : ∃ j : Tnew.toFunctor ⟶ Told.toFunctor, j ≫ Told.ι = Tnew.ι ≫ W'.ι :=
    (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hsq.isClosedComplement hTnewAlg hTnewRed
      (Tnew.ι ≫ W'.ι)).2 hTnewAvoidsU
  -- The preimage of the old complement in `V`, over which `f` is an isomorphism.
  have hpreOld : IsPullback (Told.fromPreimage f) (Told.preimage f).ι Told.ι f :=
    Subfunctor.isPullback_preimage f Told
  have hOldPreAlg : IsAlgebraicSpace B S hS (Told.preimage f).toFunctor :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS hpreOld.isoPullback
      (isAlgebraicSpace_pullback B S hS Told.ι f hToldAlg hsq.isAlgebraicSpace hW)
  have hIsoOld : IsIso (Told.fromPreimage f) := hsq.isIsoOverComplement
  let oldInv : Tnew.toFunctor ⟶ (Told.preimage f).toFunctor :=
    j ≫ inv (Told.fromPreimage f)
  let g : Tnew.toFunctor ⟶ V := oldInv ≫ (Told.preimage f).ι
  have holdInv : oldInv ≫ Told.fromPreimage f = j := by simp [oldInv]
  have hgf : g ≫ f = Tnew.ι ≫ W'.ι := by
    calc g ≫ f = oldInv ≫ ((Told.preimage f).ι ≫ f) := by simp [g]
      _ = oldInv ≫ (Told.fromPreimage f ≫ Told.ι) := by rw [← Subfunctor.fromPreimage_ι]
      _ = (oldInv ≫ Told.fromPreimage f) ≫ Told.ι := by rw [← Category.assoc]
      _ = Tnew.ι ≫ W'.ι := by rw [holdInv, hj]
  -- That morphism lands in `V'`, because the new complement avoids `U'`.
  have hgPoints : Set.range (pointsMap B S hS Tnew.toFunctor g) ⊆
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    intro x hx
    obtain ⟨p, rfl⟩ := hx
    have hpW : pointsMap B S hS Tnew.toFunctor (Tnew.ι ≫ W'.ι) p ∈
        Set.range (pointsMap B S hS W'.toFunctor W'.ι) :=
      ⟨pointsMap B S hS Tnew.toFunctor Tnew.ι p,
        (congrFun (pointsMap_comp B S hS Tnew.toFunctor Tnew.ι W'.ι) p).symm⟩
    rw [hWrange] at hpW
    rcases hpW with hpU' | hpV'
    · exact absurd hpU' (hTnewAvoidsU' ⟨p, rfl⟩)
    · obtain ⟨v, hv⟩ := hpV'
      have hcompat : pointsMap B S hS Told.toFunctor Told.ι
            (pointsMap B S hS Tnew.toFunctor j p) =
          pointsMap B S hS V f (pointsMap B S hS V'.toFunctor V'.ι v) := by
        simpa only [← pointsMap_comp_apply, hj] using hv.symm
      obtain ⟨z, hzT, hzV⟩ := exists_point_of_isPullback_of_isAlgebraicSpace B S hS
        hOldPreAlg hToldAlg hsq.isAlgebraicSpace hW hpreOld
        (pointsMap B S hS Tnew.toFunctor j p)
        (pointsMap B S hS V'.toFunctor V'.ι v) hcompat
      have hOldInv : pointsMap B S hS (Told.preimage f).toFunctor (Told.fromPreimage f)
            (pointsMap B S hS Tnew.toFunctor oldInv p) =
          pointsMap B S hS Tnew.toFunctor j p := by
        simp only [← pointsMap_comp_apply, holdInv]
      have hMonoOld : Mono (Told.fromPreimage f) := inferInstance
      have hz : pointsMap B S hS Tnew.toFunctor oldInv p = z :=
        pointsMap_injective_of_mono B S hS (Told.fromPreimage f)
          (hOldInv.trans hzT.symm)
      refine ⟨v, ?_⟩
      change pointsMap B S hS (Told.preimage f).toFunctor (Told.preimage f).ι z =
        pointsMap B S hS V'.toFunctor V'.ι v at hzV
      simpa only [g, pointsMap_comp_apply, hz] using hzV.symm
  obtain ⟨g', hg'⟩ := (factorsThrough_openSubspace_iff_points B S hS
    hsq.isAlgebraicSpace hTnewAlg V' hV' g).2 hgPoints
  have hg'f : g' ≫ f' = Tnew.ι := by
    apply (cancel_mono W'.ι).1
    calc (g' ≫ f') ≫ W'.ι = (g' ≫ V'.ι) ≫ f := by
          rw [Category.assoc, hf', ← Category.assoc]
      _ = g ≫ f := by rw [hg']
      _ = Tnew.ι ≫ W'.ι := hgf
  -- The restriction of `f'` over the new complement is a split epimorphism onto it which is
  -- also a monomorphism, hence an isomorphism.
  have hpreNew : IsPullback (Tnew.fromPreimage f') (Tnew.preimage f').ι Tnew.ι f' :=
    Subfunctor.isPullback_preimage f' Tnew
  let sec : Tnew.toFunctor ⟶ (Tnew.preimage f').toFunctor :=
    hpreNew.lift (𝟙 Tnew.toFunctor) g' hg'f.symm
  have hsecMap : sec ≫ Tnew.fromPreimage f' = 𝟙 Tnew.toFunctor :=
    hpreNew.lift_fst (𝟙 Tnew.toFunctor) g' hg'f.symm
  have hsecIn : sec ≫ (Tnew.preimage f').ι = g' :=
    hpreNew.lift_snd (𝟙 Tnew.toFunctor) g' hg'f.symm
  have hcommOld : (Tnew.fromPreimage f' ≫ j) ≫ Told.ι =
      ((Tnew.preimage f').ι ≫ V'.ι) ≫ f := by
    rw [Category.assoc, hj, ← Category.assoc, hpreNew.w, Category.assoc, hf',
      ← Category.assoc]
  let kOld : (Tnew.preimage f').toFunctor ⟶ (Told.preimage f).toFunctor :=
    hpreOld.lift (Tnew.fromPreimage f' ≫ j) ((Tnew.preimage f').ι ≫ V'.ι) hcommOld
  have hkOldMap : kOld ≫ Told.fromPreimage f = Tnew.fromPreimage f' ≫ j :=
    hpreOld.lift_fst _ _ hcommOld
  have hkOldIn : kOld ≫ (Told.preimage f).ι = (Tnew.preimage f').ι ≫ V'.ι :=
    hpreOld.lift_snd _ _ hcommOld
  have hkOldInv : kOld = (Tnew.fromPreimage f' ≫ j) ≫ inv (Told.fromPreimage f) := by
    calc kOld = (kOld ≫ Told.fromPreimage f) ≫ inv (Told.fromPreimage f) := by simp
      _ = (Tnew.fromPreimage f' ≫ j) ≫ inv (Told.fromPreimage f) := by rw [hkOldMap]
  have hnewMapG : Tnew.fromPreimage f' ≫ g = (Tnew.preimage f').ι ≫ V'.ι := by
    calc Tnew.fromPreimage f' ≫ g =
          ((Tnew.fromPreimage f' ≫ j) ≫ inv (Told.fromPreimage f)) ≫
            (Told.preimage f).ι := by
            simp [g, oldInv, Category.assoc]
      _ = kOld ≫ (Told.preimage f).ι := by rw [← hkOldInv]
      _ = (Tnew.preimage f').ι ≫ V'.ι := hkOldIn
  have hnewFactor : Tnew.fromPreimage f' ≫ g' = (Tnew.preimage f').ι := by
    apply (cancel_mono V'.ι).1
    calc (Tnew.fromPreimage f' ≫ g') ≫ V'.ι = Tnew.fromPreimage f' ≫ (g' ≫ V'.ι) := by
          rw [Category.assoc]
      _ = Tnew.fromPreimage f' ≫ g := by rw [hg']
      _ = (Tnew.preimage f').ι ≫ V'.ι := hnewMapG
  have hnewPreId : Tnew.fromPreimage f' ≫ sec = 𝟙 (Tnew.preimage f').toFunctor := by
    refine hpreNew.hom_ext ?_ ?_
    · rw [Category.assoc, hsecMap, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hsecIn, hnewFactor, Category.id_comp]
  have hNewIso : IsIso (Tnew.fromPreimage f') := ⟨⟨sec, hnewPreId, hsecMap⟩⟩
  exact ⟨hV'.1, hU'', hf'etale, hClosed, hNewIso⟩

/-! ### Change of base scheme -/

/-- An étale morphism of algebraic spaces over `S` stays étale after restriction along a
morphism `g : S' ⟶ S` of the site. An étale chart of the source restricts to an étale chart of
the restricted source by `CategoryTheory.OverShriek.restrictYonedaIso`, and the restriction of
a relative property of morphisms is
`CategoryTheory.OverShriek.relative_relocalizeRestrict_map`. -/
private theorem isEtale_relocalizeRestrict (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS' ⟶ B.obj hS)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsEtale B S hS f) :
    IsEtale B S' hS' ((OverShriek.relocalizeRestrict g).map f) := by
  have _ : Limits.HasPullbacks B.Schemes := inferInstance
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).RespectsIso :=
    have := etale_scheme_respectsIso.{u}
    MorphismProperty.RespectsIso.inverseImage _ _
  obtain ⟨A, a, hsurj, hetale⟩ := hF.exists_atlas
  refine (isEtale_iff_exists_source_chart B S' hS'
    (isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g F hF)
    (isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g G hG) _).2
    ⟨(Over.pullback g).obj A, (OverShriek.restrictYonedaIso g A).hom ≫
      (OverShriek.relocalizeRestrict g).map a, ?_, ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.relative_relocalizeRestrict_map g
        (inverseImage_restrictReindexSnd B S' S hS' hS g
          (@AlgebraicGeometry.Surjective.{u})) hsurj)
  · exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.relative_relocalizeRestrict_map g
        (inverseImage_restrictReindexSnd B S' S hS' hS g
          (@AlgebraicGeometry.Etale.{u})) hetale)
  · refine (isEtale_iff_presheaf_of_yoneda B S' hS' _).2 ?_
    have hcomp := OverShriek.relative_relocalizeRestrict_map g
      (inverseImage_restrictReindexSnd B S' S hS' hS g
        (@AlgebraicGeometry.Etale.{u})) (hf A a hetale)
    rw [Functor.map_comp] at hcomp
    simpa only [Category.assoc] using MorphismProperty.RespectsIso.precomp _
      (OverShriek.restrictYonedaIso g A).hom _ hcomp

/-- An étale-local property of schemes enjoyed by an algebraic space over `S'` is enjoyed by
the same space viewed over `S` along the lower-shriek extension of `g : S' ⟶ S`: the extension
of an étale atlas is an étale atlas by the same scheme. -/
private theorem hasEtaleLocalProperty_relocalizePresheafFunctor (B : BigFppfSite.{u})
    (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS' ⟶ B.obj hS) {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (hF : HasEtaleLocalProperty B S' hS' F P) :
    HasEtaleLocalProperty B S hS ((OverShriek.relocalizePresheafFunctor g).obj F) P := by
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    etale_scheme_respectsIso.{u}
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  obtain ⟨A, a, hsurj, hetale, hP⟩ := hF
  refine ⟨(Over.map g).obj A, (relocalizedYonedaIso B (B.obj hS') (B.obj hS) g A).inv ≫
    (OverShriek.relocalizePresheafFunctor g).map a, ?_, ?_, hP⟩
  · exact MorphismProperty.RespectsIso.precomp _ _ _
      (presheaf_relocalized B S' S hS' hS g (@AlgebraicGeometry.Surjective.{u}) a hsurj)
  · exact MorphismProperty.RespectsIso.precomp _ _ _
      (presheaf_relocalized B S' S hS' hS g (@AlgebraicGeometry.Etale.{u}) a hetale)

/-- Points of an algebraic space over `S'` which avoid the subspace cut out by a subfunctor
`U` of `W` still avoid `U` after the lower-shriek extension along `g : S' ⟶ S`.

A field-valued point of the extension is a field-valued point of the original together with a
factorisation of its structure morphism through `S'`; a common extension witnessing that it
meets `U` therefore produces a field-valued point of the restricted `U` meeting the
restriction of the morphism, which is what the hypothesis excludes. -/
private theorem disjoint_range_pointsMap_relocalizeOfRestricted (B : BigFppfSite.{u})
    (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS' ⟶ B.obj hS) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (U : Subfunctor W)
    (a : F ⟶ (OverShriek.relocalizeRestrict g).obj W)
    (ha : Disjoint (Set.range (pointsMap B S' hS' F a))
      (Set.range (pointsMap B S' hS'
        (Subfunctor.range ((OverShriek.relocalizeRestrict g).map U.ι)).toFunctor
        (Subfunctor.range ((OverShriek.relocalizeRestrict g).map U.ι)).ι))) :
    Disjoint (Set.range (pointsMap B S hS
        ((OverShriek.relocalizePresheafFunctor g).obj F)
        (OverShriek.relocalizeOfRestricted g a)))
      (Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
  rw [Set.disjoint_left] at ha ⊢
  rintro x ⟨p, rfl⟩ ⟨q, heq⟩
  induction p using Quot.inductionOn with | h p =>
  induction q using Quot.inductionOn with | h q =>
  obtain ⟨r, ⟨s, hs⟩, ⟨t, ht⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS W (q.map B S hS U.toFunctor U.ι)
      (p.map B S hS ((OverShriek.relocalizePresheafFunctor g).obj F)
        (OverShriek.relocalizeOfRestricted g a))).1 heq
  change r.siteObject ⟶ q.siteObject at s
  change r.siteObject ⟶ p.siteObject at t
  -- The factorisation of the structure morphism of `p` through `S'` carried by `p`.
  let ψ : p.siteObject.left ⟶ B.obj hS' := p.value.1.1
  let A : BigFppfOver B S' hS' := Over.mk ψ
  let A' : BigFppfOver B S' hS' := Over.mk (t.left ≫ ψ)
  let t' : A' ⟶ A := Over.homMk t.left rfl
  have hp : ψ ≫ g = p.siteObject.hom := p.value.2
  let e : (Over.map g).obj A' ⟶ r.siteObject := Over.homMk (𝟙 _) (by
    change (𝟙 _) ≫ r.siteObject.hom = (t.left ≫ ψ) ≫ g
    rw [Category.id_comp, Category.assoc, hp]
    exact t.w.symm)
  let i : p.siteObject ⟶ (Over.map g).obj A := Over.homMk (𝟙 _) (by
    change (𝟙 _) ≫ ψ ≫ g = p.siteObject.hom
    simpa using hp)
  have hti : e ≫ t ≫ i = (Over.map g).map t' := Over.OverMorphism.ext (by simp [e, i, t'])
  let r' : FieldValuedPoint B S' hS' F :=
    { carrier := r.carrier
      field := r.field
      contained := r.contained
      toBase := B.inclusion.map (t.left ≫ ψ)
      value := F.map t'.op p.value.1.2 }
  have hval : a.app (op A') r'.value = W.map (e ≫ s).op q.value.val := by
    have ht' : W.map t.op (W.map i.op (a.app (op A) p.value.1.2)) = r.value := ht
    have hs' : W.map s.op q.value.val = r.value := hs
    calc a.app (op A') r'.value = W.map ((Over.map g).map t').op (a.app (op A) p.value.1.2) :=
          NatTrans.naturality_apply a t'.op p.value.1.2
      _ = W.map e.op (W.map t.op (W.map i.op (a.app (op A) p.value.1.2))) := by
          simp only [← hti, op_comp, Functor.map_comp, types_comp_apply]
      _ = W.map e.op r.value := by rw [ht']
      _ = W.map (e ≫ s).op q.value.val := by
          rw [← hs', op_comp, W.map_comp_apply]
  have hm : a.app (op A') r'.value ∈ U.obj (op ((Over.map g).obj A')) :=
    hval ▸ U.map (e ≫ s).op q.value.property
  let z : FieldValuedPoint B S' hS'
      (Subfunctor.range ((OverShriek.relocalizeRestrict g).map U.ι)).toFunctor :=
    { carrier := r.carrier
      field := r.field
      contained := r.contained
      toBase := r'.toBase
      value := ⟨a.app (op A') r'.value, ⟨⟨a.app (op A') r'.value, hm⟩, rfl⟩⟩ }
  exact ha ⟨r'.class B S' hS' F, rfl⟩ ⟨z.class B S' hS' _, rfl⟩

/-- A subfunctor contained in one over which a morphism restricts to an isomorphism also has
that property: on each object the restriction of `f` over the smaller subfunctor is the
restriction over the larger one cut down to it, hence injective and surjective. -/
private theorem isIso_fromPreimage_of_lift {D : Type*} [Category D] {X Y : D ⥤ Type u}
    (f : X ⟶ Y) (T T' : Subfunctor Y) [IsIso (T.fromPreimage f)]
    (a : T'.toFunctor ⟶ T.toFunctor) (ha : a ≫ T.ι = T'.ι) :
    IsIso (T'.fromPreimage f) := by
  have hb (Z : D) : Function.Bijective ((T.fromPreimage f).app Z) :=
    (isIso_iff_bijective _).1 inferInstance
  refine (NatTrans.isIso_iff_isIso_app _).2 fun Z => (isIso_iff_bijective _).2 ⟨?_, ?_⟩
  · intro x y hxy
    have hmem (z : T'.toFunctor.obj Z) : z.val ∈ T.obj Z := by
      have he : (a.app Z z).val = z.val := congrArg (fun k => k.app Z z) ha
      exact he ▸ (a.app Z z).property
    have hx := hmem ⟨f.app Z x.val, x.property⟩
    have hy := hmem ⟨f.app Z y.val, y.property⟩
    have hv : f.app Z x.val = f.app Z y.val :=
      congrArg (fun z : T'.toFunctor.obj Z => z.val) hxy
    have hinj := (hb Z).1 (show (T.fromPreimage f).app Z ⟨x.val, hx⟩ =
      (T.fromPreimage f).app Z ⟨y.val, hy⟩ from Subtype.ext hv)
    exact Subtype.ext (congrArg (fun z : (T.preimage f).toFunctor.obj Z => z.val) hinj)
  · intro x
    obtain ⟨y, hy⟩ := (hb Z).2 (a.app Z x)
    have he : f.app Z y.val = x.val :=
      (congrArg Subtype.val hy).trans (congrArg (fun k => k.app Z x) ha)
    exact ⟨⟨y.val, show f.app Z y.val ∈ T'.obj Z from he ▸ x.property⟩, Subtype.ext he⟩

/-- **Stacks 08GN, change of base scheme.** An elementary distinguished square over `S` stays
elementary distinguished after restriction along a morphism `g : S' ⟶ S` of the site: the open
subspace is replaced by the image of the restricted inclusion and the étale morphism by its
restriction. -/
@[stacks 08GN "scheme_change"]
theorem isElementaryDistinguishedSquare_relocalizeRestrict (B : BigFppfSite.{u})
    (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS' ⟶ B.obj hS) {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsElementaryDistinguishedSquare B S' hS'
      (isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g W hW)
      (Subfunctor.range ((OverShriek.relocalizeRestrict g).map U.ι))
      ((OverShriek.relocalizeRestrict g).map f) := by
  classical
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hW' : IsAlgebraicSpace B S' hS'
      ((OverShriek.relocalizeRestrict g).obj W) :=
    isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g W hW
  have hVres : IsAlgebraicSpace B S' hS'
      ((OverShriek.relocalizeRestrict g).obj V) :=
    isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g V h.isAlgebraicSpace
  -- The restricted inclusion is a monomorphism, so its image is a copy of the restriction
  -- of `U`, and it is an open subspace.
  have hmono : Mono ((OverShriek.relocalizeRestrict g).map U.ι) :=
    Functor.map_mono _ U.ι
  let U' : Subfunctor ((OverShriek.relocalizeRestrict g).obj W) :=
    Subfunctor.range ((OverShriek.relocalizeRestrict g).map U.ι)
  let eU : (OverShriek.relocalizeRestrict g).obj U.toFunctor ≅ U'.toFunctor :=
    asIso (Subfunctor.toRange ((OverShriek.relocalizeRestrict g).map U.ι))
  have hU'alg : IsAlgebraicSpace B S' hS' U'.toFunctor :=
    isAlgebraicSpace_of_iso B S' hS' eU
      (isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g U.toFunctor h.isOpenSubspace.1)
  have hU'open : IsOpenSubspace B S' hS' U' := by
    refine ⟨hU'alg, ?_⟩
    have hopen := OverShriek.relative_relocalizeRestrict_map g
      (inverseImage_restrictReindexSnd B S' S hS' hS g
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})) h.isOpenSubspace.2
    have heq : eU.inv ≫ (OverShriek.relocalizeRestrict g).map U.ι = U'.ι :=
      calc eU.inv ≫ (OverShriek.relocalizeRestrict g).map U.ι =
            eU.inv ≫ (Subfunctor.toRange ((OverShriek.relocalizeRestrict g).map U.ι) ≫ U'.ι) :=
            congrArg (fun k => eU.inv ≫ k)
              (Subfunctor.toRange_ι ((OverShriek.relocalizeRestrict g).map U.ι)).symm
        _ = U'.ι := by simp [eU]
    rw [← heq]
    exact MorphismProperty.RespectsIso.precomp _ eU.inv _ hopen
  -- Its complement is closed, the inclusion of an open subspace being étale.
  have hc : IsClosed (Set.range (pointsMap B S' hS' U'.toFunctor U'.ι))ᶜ := by
    refine IsOpen.isClosed_compl ?_
    have ho := isOpenMap_pointsMap_of_isEtale B S' hS' U'.ι hU'open.1 hW'
      (isEtale_ι_of_isOpenSubspace hU'open)
    simpa only [Set.image_univ] using ho Set.univ isOpen_univ
  -- The two reduced closed complements, and the lift of the extension of the new one.
  let T : Subfunctor W := reducedClosedSubspace B S hS W hW
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ h.isClosedComplement
  let T' : Subfunctor ((OverShriek.relocalizeRestrict g).obj W) :=
    reducedClosedSubspace B S' hS' ((OverShriek.relocalizeRestrict g).obj W) hW'
      (Set.range (pointsMap B S' hS' U'.toFunctor U'.ι))ᶜ hc
  have hT'alg : IsAlgebraicSpace B S' hS' T'.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S' hS'
      ((OverShriek.relocalizeRestrict g).obj W) hW' _ hc
  have hT'supp : Set.range (pointsMap B S' hS' T'.toFunctor T'.ι) =
      (Set.range (pointsMap B S' hS' U'.toFunctor U'.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S' hS'
      ((OverShriek.relocalizeRestrict g).obj W) hW' _ hc
  let b := OverShriek.relocalizeOfRestricted g T'.ι
  have hb : Disjoint (Set.range (pointsMap B S hS
        ((OverShriek.relocalizePresheafFunctor g).obj T'.toFunctor) b))
      (Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
    refine disjoint_range_pointsMap_relocalizeOfRestricted B S S' hS hS' g U T'.ι ?_
    rw [Set.disjoint_left]
    intro x hx hxU
    exact (hT'supp ▸ hx) hxU
  have hbT : Set.range (pointsMap B S hS
        ((OverShriek.relocalizePresheafFunctor g).obj T'.toFunctor) b) ⊆
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
    fun x hx hxU => Set.disjoint_left.1 hb hx hxU
  obtain ⟨k, hk⟩ : ∃ k : (OverShriek.relocalizePresheafFunctor g).obj T'.toFunctor ⟶
      T.toFunctor, k ≫ T.ι = b :=
    (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ h.isClosedComplement
      (isAlgebraicSpace_viewOver B S' S hS' hS g T'.toFunctor hT'alg)
      (hasEtaleLocalProperty_relocalizePresheafFunctor B S S' hS hS' g _
        (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S' hS'
          ((OverShriek.relocalizeRestrict g).obj W) hW' _ hc)) b).2 hbT
  -- The restriction of `T`, which `T'` maps into, and over which `f` restricts to an
  -- isomorphism because its restriction does.
  let Tr : Subfunctor ((OverShriek.relocalizeRestrict g).obj W) :=
    { obj X := T.obj ((Over.map g).op.obj X)
      map {_ _} m := T.map ((Over.map g).op.map m) }
  let k' : T'.toFunctor ⟶ Tr.toFunctor := OverShriek.relocalizeToRestricted g k
  have hk' : k' ≫ Tr.ι = T'.ι :=
    calc k' ≫ Tr.ι = OverShriek.relocalizeToRestricted g (k ≫ T.ι) := rfl
      _ = OverShriek.relocalizeToRestricted g b := by rw [hk]
      _ = T'.ι := OverShriek.relocalizeToRestricted_relocalizeOfRestricted g T'.ι
  have hTiso : IsIso (T.fromPreimage f) := h.isIsoOverComplement
  have hTriso : IsIso (Tr.fromPreimage ((OverShriek.relocalizeRestrict g).map f)) := by
    change IsIso ((OverShriek.relocalizeRestrict g).map (T.fromPreimage f))
    infer_instance
  exact ⟨hVres, hU'open,
    isEtale_relocalizeRestrict B S S' hS hS' g h.isAlgebraicSpace hW f h.isEtale, hc,
    isIso_fromPreimage_of_lift ((OverShriek.relocalizeRestrict g).map f) Tr T' k' hk'⟩

end AlgebraicGeometry.Space

end
