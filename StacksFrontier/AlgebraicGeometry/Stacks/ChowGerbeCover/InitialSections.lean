module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.SectionFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# The first family of local sections in the proof of Stacks 0CQ7

Let `f : 𝒳 ⟶ Y` be a flat 1-morphism of finite type and locally of finite presentation from an
algebraic stack to a quasi-compact quasi-separated algebraic space. The third paragraph of the
proof of [Stacks, Tag 0CQ7] reads: the image of `|f|` is an open `W ⊆ Y` (Stacks 06R7), which is
quasi-compact because `|𝒳|` is; by Stacks 0CQ6 there is a finite surjective `g : Y' ⟶ Y` such that
`g⁻¹(W) ⟶ Y` factors Zariski locally through `𝒳 ⟶ Y`; so after the base change along `g` there
are finitely many quasi-compact opens `Wᵢ` with sections `xᵢ : Wᵢ ⟶ 𝒳` covering `g⁻¹(W)`.

This file proves that step, with Stacks 0CQ6 as the hypothesis `h0CQ6`, in the shape of
`AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily` over the proper morphism `g`. The open
`W` is the open subspace of `Y` whose points are the image of `|f|`; all values of `f` lie in it,
and it contains every open subspace `V` over which the base change of `f` is surjective.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_sectionFamily_of_isFlat`: the step above.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The points of the stack of an algebraic space, read as the points of the space through the
tautological chart, are carried along the 1-morphism attached to a morphism of algebraic spaces
the way the points of the space are carried along the morphism. -/
private theorem pointsMap_algebraicSpaceStackMap_spacePointMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (g : F ⟶ G) (x : Space.points B S hS F) :
    AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hF hG g)
        (spacePointMap B S hS F (fibredCategory B S hS F)
          (representingEquivalence B S hS F (fibredCategory B S hS F)
            (StacksRepresentableCFG.EquivalenceOver.refl _)).functor x) =
      spacePointMap B S hS G (fibredCategory B S hS G)
        (representingEquivalence B S hS G (fibredCategory B S hS G)
          (StacksRepresentableCFG.EquivalenceOver.refl _)).functor
        (Space.pointsMap B S hS F g x) := by
  have hnat := spacePointMap_representing_naturality B S hS F G
    (fibredCategory B S hS F) (fibredCategory B S hS G)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS g).1 x
  rw [representingMap_associatedMap] at hnat
  exact hnat.symm

/-- Every element named by a 1-morphism `f : 𝒳 ⟶ Y` has all of its points in the image of
`|f|`, read on the points of `Y`. -/
private theorem mem_range_pointsMap_of_section {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (ξ : 𝒳.val.val.obj)
    (t : Space.points B S hS (yoneda.obj (𝒳.val.val.p.obj ξ))) :
    spacePointMap B S hS Y (fibredCategory B S hS Y)
        (representingEquivalence B S hS Y (fibredCategory B S hS Y)
          (StacksRepresentableCFG.EquivalenceOver.refl _)).functor
        (Space.pointsMap B S hS _ (yonedaEquiv.symm (algebraicSpaceStackSection f ξ)) t) ∈
      Set.range (AlgebraicStacks.pointsMap B S hS f) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep t
  obtain ⟨w', φ, hφ⟩ := 𝒳.val.isFiberedInGroupoids.exists_lift p.value ξ rfl
  have hdom : 𝒳.val.val.p.obj w' = p.siteObject := IsHomLift.domain_eq 𝒳.val.val.p p.value φ
  let q : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := p.carrier
      field := p.field
      base := p.siteObject
      isSpec := Iso.refl _
      obj := w'
      «over» := hdom }
  refine ⟨pointClass B S hS _ _ q, ?_⟩
  rw [Space.pointsMap_class, spacePointMap_class]
  apply (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
  refine ⟨fieldValuedPointMap B S hS _ f.hom.hom q, ⟨𝟙 _⟩, ⟨?_⟩⟩
  have hsec := obj_eq_mk_section B S hS f.hom w'
  let H := (Y ⋙ typeToGrpd) ⋙ Grpd.forgetToCat
  refine eqToHom hsec ≫ (PresheafOfCategories.homEquiv H _ _).symm
    ⟨eqToHom hdom, eqToHom (congrArg Discrete.mk ?_)⟩
  have h1 := PresheafOfCategories.sectionOfBasedFunctor_map f.hom.hom.toFunctor f.hom.hom.w φ
  have hfac := IsHomLift.fac' 𝒳.val.val.p p.value φ
  change _ = Y.map (eqToHom hdom).op (Y.map p.value.op (algebraicSpaceStackSection f ξ))
  rw [← h1, hfac, ← Functor.map_comp_apply, ← op_comp]
  simp

/-- **The first family of local sections in the proof of Stacks 0CQ7.** Let `f : 𝒳 ⟶ Y` be a flat
1-morphism of finite type and locally of finite presentation from an algebraic stack to a
quasi-compact quasi-separated algebraic space. Let `W ⊆ Y` be the open subspace whose points are
the image of `|f|` (open by Stacks 06R7). Then all values of `f` lie in `W`, every open subspace
`V ⊆ Y` over which the base change of `f` is surjective lies in `W`, and, given Stacks 0CQ6 as the
input `h0CQ6`, there are a proper surjective `g : Y₀ ⟶ Y` from a quasi-compact quasi-separated
algebraic space and finitely many quasi-compact opens of `g⁻¹(W)` covering it, each with a
1-morphism `xᵢ` to `𝒳` over `Y`. -/
theorem exists_sectionFamily_of_isFlat
    (h0CQ6 : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hY : IsAlgebraicSpace B S hS Y)
      (_hYqc : Space.IsQuasiCompactSpace B S hS Y)
      (_hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
      (_hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
      {𝒳 : AlgebraicStacks.{u, w} B S hS}
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
      (_hfs : IsSurjective B S hS f) (_hff : AlgebraicStacks.IsFlat B S hS f)
      (_hfl : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f),
      ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
        Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
        ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
          (q : ∀ j, W j ⟶ V.toFunctor)
          (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
          (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
          (∀ y : Space.points B S hS Y',
            Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
              ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
          ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hft : IsFiniteType B S hS f) (hfl : IsFlat B S hS f)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (W : Subfunctor Y) (_ : Space.IsOpenSubspace B S hS W),
      (∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (Opposite.op (𝒳.val.val.p.obj ξ))) ∧
      (∀ (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
        IsSurjective B S hS (twoFibreProductSquareAlgebraicStacks B S hS
          (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst → V ≤ W) ∧
      ∃ (Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY₀ : IsAlgebraicSpace B S hS Y₀) (g : Y₀ ⟶ Y),
        Space.IsProper B S hS g ∧ Space.IsSurjective B S hS g ∧
          Space.IsQuasiCompactSpace B S hS Y₀ ∧
          Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ ∧
          ∃ n : ℕ, Nonempty (SectionFamily hY f W hY₀ g (Fin n)) := by
  classical
  let := Space.pointTopology B S hS Y
  let := pointTopology B S hS (fibredCategory B S hS Y)
  let := pointTopology B S hS 𝒳.val
  -- the image `O` of `|f|`, read on the points of `Y`, and the open subspace `W` it cuts out
  have hσY := isHomeomorph_spacePointMap_representing B S hS Y hY (fibredCategory B S hS Y)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  let O : Set (Space.points B S hS Y) :=
    spacePointMap B S hS Y (fibredCategory B S hS Y)
      (representingEquivalence B S hS Y (fibredCategory B S hS Y)
        (StacksRepresentableCFG.EquivalenceOver.refl _)).functor ⁻¹'
      Set.range (AlgebraicStacks.pointsMap B S hS f)
  have hO : _root_.IsOpen O :=
    ((isOpenMap_pointsMap B S hS f hfl hfp).isOpen_range).preimage hσY.continuous
  have hW : Space.IsOpenSubspace B S hS (Space.openSubspaceOfPoints B S hS Y O) :=
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hY O hO
  have hWpts : Set.range (Space.pointsMap B S hS (Space.openSubspaceOfPoints B S hS Y O).toFunctor
      (Space.openSubspaceOfPoints B S hS Y O).ι) = O :=
    Space.range_pointsMap_ι_openSubspaceOfPoints B S hS O
  -- all values of `f` lie in `W`
  have hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈
      (Space.openSubspaceOfPoints B S hS Y O).obj (Opposite.op (𝒳.val.val.p.obj ξ)) := by
    intro ξ
    change Set.range _ ⊆ O
    rintro _ ⟨t, rfl⟩
    exact mem_range_pointsMap_of_section f ξ t
  -- an open subspace over which the base change of `f` is surjective lies in `W`
  have hle : ∀ (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      IsSurjective B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
        V ≤ Space.openSubspaceOfPoints B S hS Y O := by
    intro V hV hsurj
    refine Space.le_of_range_pointsMap_ι_subset B S hS hW ?_
    rw [hWpts]
    rintro _ ⟨v, rfl⟩
    obtain ⟨z, hz⟩ := hsurj (spacePointMap B S hS V.toFunctor (fibredCategory B S hS V.toFunctor)
      (representingEquivalence B S hS V.toFunctor (fibredCategory B S hS V.toFunctor)
        (StacksRepresentableCFG.EquivalenceOver.refl _)).functor v)
    have hcomm := AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).iso.hom
    rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at hcomm
    refine ⟨AlgebraicStacks.pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).snd z, ?_⟩
    show _ = spacePointMap B S hS Y (fibredCategory B S hS Y)
      (representingEquivalence B S hS Y (fibredCategory B S hS Y)
        (StacksRepresentableCFG.EquivalenceOver.refl _)).functor _
    rw [← pointsMap_algebraicSpaceStackMap_spacePointMap.{u, w} hV.1 hY V.ι v, ← hz]
    exact (congrFun hcomm z).symm
  refine ⟨Space.openSubspaceOfPoints B S hS Y O, hW, hfW, hle, ?_⟩
  -- `W` is quasi-compact: `|𝒳|` is, since `f` is quasi-compact and `Y` is quasi-compact
  have hYst : IsQuasiCompactStack.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS Y hY).val
      (algebraicSpaceStack.{u, w} B S hS Y hY).property := by
    have := (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS Y hY).1 hYqc
    exact (hσY.homeomorph _).compactSpace
  have h𝒳qc := isQuasiCompactStack_of_isQuasiCompactMorphism B S hS f hft.2 hYst
  have hOc : IsCompact O := by
    have hc : IsCompact (Set.range (AlgebraicStacks.pointsMap B S hS f)) :=
      @isCompact_range _ _ _ _ h𝒳qc _ (continuous_pointsMap B S hS 𝒳.val _ f.hom.hom)
    have := hc.image (hσY.homeomorph _).symm.continuous
    rwa [Homeomorph.image_symm] at this
  have hWqc : Space.IsQuasiCompactSpace B S hS (Space.openSubspaceOfPoints B S hS Y O).toFunctor :=
    Space.isQuasiCompactSpace_of_isCompact_range B S hS hY hW (by rw [hWpts]; exact hOc)
  generalize Space.openSubspaceOfPoints B S hS Y O = W at hW hWpts hWqc ⊢
  clear hfW hle hYst h𝒳qc hOc hO
  -- the base change `P.fst : W ×_Y 𝒳 ⟶ W` of `f` is surjective, flat and locally of finite
  -- presentation
  let P := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι) f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f
  have hPeq : P.fst ≫ algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι = P.snd ≫ f :=
    Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS P.iso.hom.hom)
  have hσW := bijective_spacePointMap_representing B S hS W.toFunctor
    (fibredCategory B S hS W.toFunctor) (StacksRepresentableCFG.EquivalenceOver.refl _)
  have hPsurj : IsSurjective B S hS P.fst := by
    intro z
    obtain ⟨v, rfl⟩ := hσW.2 z
    have hv : Space.pointsMap B S hS W.toFunctor W.ι v ∈ O := hWpts ▸ ⟨v, rfl⟩
    obtain ⟨x, hx⟩ := hv
    obtain ⟨p, hp, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP _ x
      ((pointsMap_algebraicSpaceStackMap_spacePointMap.{u, w} hW.1 hY W.ι v).trans hx.symm)
    exact ⟨p, hp⟩
  -- Stacks 0CQ6
  obtain ⟨Y₀, hY₀, g, hgfin, hgsurj, J, Wj, hWj, ιj, qj, xj, hιj, hιq, hcov, hx⟩ :=
    h0CQ6 hY hYqc hYqs W hW hWqc P.fst hPsurj (isFlat_baseChange B S hS f _ P hP hfl)
      (isLocallyOfFinitePresentation_baseChange B S hS f _ P hP hfp)
  have hgint := Space.IsFinite.isIntegralHom B S hS hgfin
  have hgprop : Space.IsProper B S hS g :=
    ((Space.isFinite_iff_isAffineHom_and_isProper B S hS hY₀ hY g).1 hgfin).2
  have hgqc : Space.IsQuasiCompact B S hS g := Space.isQuasiCompact_of_isIntegralHom g hY₀ hY hgint
  have hY₀qc : Space.IsQuasiCompactSpace B S hS Y₀ :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hgqc
  have hY₀qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY₀ hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hgprop.1)
  -- the sections `xj ≫ P.snd` lie over `ιj ≫ g`
  have hxj : ∀ j, xj j ≫ P.snd ≫ f =
      algebraicSpaceStackMap.{u, w} B S hS (hWj j) hY (ιj j ≫ g) := by
    intro j
    obtain ⟨e⟩ := hx j
    have h1 : xj j ≫ P.fst = algebraicSpaceStackMap.{u, w} B S hS (hWj j) hW.1 (qj j) :=
      Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS e.hom.hom)
    rw [← hPeq, ← Category.assoc, h1, ← algebraicSpaceStackMap_comp, hιq j]
  -- every point of `g⁻¹(W)` has a quasi-compact open neighbourhood on which a section lives
  let := Space.pointTopology B S hS Y₀
  have hloc : ∀ y ∈ Set.range (Space.pointsMap B S hS (W.preimage g).toFunctor (W.preimage g).ι),
      ∃ (j : J) (V : Subfunctor Y₀), Space.IsOpenSubspace B S hS V ∧
        Space.IsQuasiCompactSpace B S hS V.toFunctor ∧
        y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧ V ≤ W.preimage g ∧
        ∃ m : V.toFunctor ⟶ Wj j, m ≫ ιj j = V.ι := by
    intro y hy
    rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage] at hy
    obtain ⟨j, hj⟩ := hcov y hy
    obtain ⟨V, hV, hVqc, hyV, hVsub⟩ :=
      Space.exists_isQuasiCompactSpace_isOpenSubspace_range_subset B S hS hY₀ _
        (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (ιj j) (hιj j)) y hj
    have : Mono (ιj j) := Space.mono_of_presheaf_isOpenImmersion (hιj j)
    have hVle : V ≤ Subfunctor.range (ιj j) := by
      refine Space.le_of_range_pointsMap_ι_subset B S hS
        (Space.isOpenSubspace_subfunctorRange B S hS (hWj j) (hιj j)) (hVsub.trans ?_)
      rintro _ ⟨a, rfl⟩
      exact ⟨Space.pointsMap B S hS _ (Subfunctor.toRange (ιj j)) a, by
        rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
    obtain ⟨m, hm⟩ : ∃ m : V.toFunctor ⟶ Wj j, m ≫ ιj j = V.ι := by
      refine ⟨Subfunctor.homOfLe hVle ≫ inv (Subfunctor.toRange (ιj j)), ?_⟩
      rw [Category.assoc, (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι (ιj j)).symm]
      exact Subfunctor.homOfLe_ι hVle
    refine ⟨j, V, hV, hVqc, hyV, ?_, m, hm⟩
    intro T v hv
    have hcomp : V.ι ≫ g = (m ≫ qj j) ≫ W.ι := by
      rw [← hm, Category.assoc, hιq j, ← Category.assoc]
    have h : g.app T v = ((m ≫ qj j).app T ⟨v, hv⟩).1 :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hcomp T) (⟨v, hv⟩ : V.toFunctor.obj T)
    change g.app T v ∈ W.obj T
    rw [h]
    exact ((m ≫ qj j).app T ⟨v, hv⟩).2
  choose j V hVo hVqc hyV hVle m hm using hloc
  -- `g⁻¹(W)` is quasi-compact, so finitely many of these neighbourhoods cover it
  have hpre := Space.isOpenSubspace_preimage B S hS g W hY hY₀ hW
  have hKc : IsCompact (Set.range (Space.pointsMap B S hS (W.preimage g).toFunctor
      (W.preimage g).ι)) := by
    let := Space.pointTopology B S hS (W.preimage g).toFunctor
    have := (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS _ hpre.1).1
      (Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY hY₀ g hgqc hW hWqc)
    exact isCompact_range (Space.continuous_pointsMap B S hS _)
  obtain ⟨t, ht⟩ := hKc.elim_nhds_subcover'
    (fun y hy => Set.range (Space.pointsMap B S hS (V y hy).toFunctor (V y hy).ι))
    (fun y hy => (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hVo y hy).2).mem_nhds
      (hyV y hy))
  refine ⟨Y₀, hY₀, g, hgprop, hgsurj, hY₀qc, hY₀qs, t.card, ⟨?_⟩⟩
  exact
    { U := fun i => V _ (t.equivFin.symm i).1.2
      isOpen := fun i => hVo _ _
      isQC := fun i => hVqc _ _
      le := fun i => hVle _ _
      cover := by
        intro y hy
        obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (ht hy)
        obtain ⟨i, hi⟩ : ∃ i, t.equivFin.symm i = ⟨k, hk⟩ :=
          ⟨_, t.equivFin.symm_apply_apply _⟩
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        rw [hi]
        exact hyk
      x := fun i => algebraicSpaceStackMap.{u, w} B S hS (hVo _ _).1 (hWj _) (m _ _) ≫
        xj _ ≫ P.snd
      hx := fun i => by
        simp only [Category.assoc]
        rw [hxj, ← algebraicSpaceStackMap_comp, ← Category.assoc, hm] }

end AlgebraicGeometry.Stack.AlgebraicStacks

end
