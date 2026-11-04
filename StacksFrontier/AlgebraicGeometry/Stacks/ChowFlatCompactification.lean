module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSectionsGerbeInduction
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFlatteningChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedNearSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints

/-!
# Stacks 0CQ7 for a flat morphism

Let `f : 𝒳 ⟶ Y` be a separated, flat 1-morphism of finite presentation from an algebraic stack to
a quasi-compact quasi-separated algebraic space, which is a gerbe over a quasi-compact open
`V ⊆ Y`. Then the conclusion of [Stacks, Tag 0CQ7] holds for `(f, V)`. This is the part of the
proof of [Stacks, Tag 0CQ7] after the flattening step: the image `W` of `|f|` is open, `f` takes
its values in `W`, and by [Stacks, Tag 0CQ6] after a finite surjective base change `𝒳 ⟶ W` has
sections over the members of an open covering of the inverse image of `W`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasCompactifiableCovers_of_isFlat`: [Stacks, Tag 0CQ7]
  for a flat `f` of finite presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isOpenSubspace_range_eq_image_of_isFlat`: the
  image of a flat `f` of finite type is a quasi-compact open.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mem_openSubspaceOfPoints_of_pointsMap_mem`: the
  values of a 1-morphism into the stack of an algebraic space lie in the open subspace of the
  points of its image.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The values of a 1-morphism into the stack of an algebraic space lie in the subspace cut out
by any set of points containing its image.** Let `f : 𝒳 ⟶ Y` and let `E ⊆ |Y|` contain the image
of `|𝒳|`. For an object `ξ` of `𝒳` over `T`, every point of `T` maps into `E` under the section
`f(ξ)`: the point is the image of the restriction of `ξ` to it. -/
theorem mem_openSubspaceOfPoints_of_pointsMap_mem {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (E : Set (Space.points B S hS Y))
    (hE : ∀ z, AlgebraicStacks.pointsMap B S hS f z ∈
      spacePointMap B S hS Y (fibredCategory B S hS Y)
        (BasedFunctor.id (fibredCategory B S hS Y).val) '' E)
    (ξ : 𝒳.val.val.obj) :
    algebraicSpaceStackSection f ξ ∈
      (Space.openSubspaceOfPoints B S hS Y E).obj (op (𝒳.val.val.p.obj ξ)) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  rw [Space.mem_openSubspaceOfPoints_iff]
  rintro _ ⟨t, rfl⟩
  induction t using Quot.ind with
  | mk q =>
    -- the restriction of `ξ` to the field point `q`
    let ξq := Functor.IsPreFibered.pullbackObj (p := 𝒳.val.val.p) (a := ξ) rfl q.value
    let π : ξq ⟶ ξ := Functor.IsPreFibered.pullbackMap (p := 𝒳.val.val.p) (a := ξ) rfl q.value
    have hπ : 𝒳.val.val.p.IsHomLift q.value π :=
      (Functor.IsPreFibered.pullbackMap.IsCartesian (p := 𝒳.val.val.p) (a := ξ) rfl
        q.value).toIsHomLift
    let z₀ : FieldValuedPoint B S hS 𝒳.val.val :=
      { carrier := q.carrier
        base := q.siteObject
        isSpec := Iso.refl _
        obj := ξq
        «over» := Functor.IsPreFibered.pullbackObj_proj (p := 𝒳.val.val.p) rfl q.value }
    obtain ⟨e, he, hez⟩ := hE (pointClass B S hS 𝒳.val.val _ z₀)
    -- the image of `ξq` is the canonical object of the value of the section at `q`
    have hobj : f.hom.hom.obj ξq = ⟨q.siteObject, Discrete.mk
        ((yonedaEquiv.symm (algebraicSpaceStackSection f ξ)).app (op q.siteObject) q.value)⟩ := by
      refine PresheafOfCategories.obj_eq_of_elementOf_eq (P := Y)
        (BasedFunctor.w_obj f.hom.hom ξq |>.trans z₀.over) rfl ?_
      exact PresheafOfCategories.elementOf_eq_map (P := Y)
        (BasedFunctor.w_obj f.hom.hom ξq |>.trans z₀.over) (BasedFunctor.w_obj f.hom.hom ξ) q.value
        (f.hom.hom.map π) (BasedFunctor.preserves_isHomLift f.hom.hom q.value π)
    have key : spacePointMap B S hS Y (fibredCategory B S hS Y)
        (BasedFunctor.id (fibredCategory B S hS Y).val) e =
      spacePointMap B S hS Y (fibredCategory B S hS Y)
        (BasedFunctor.id (fibredCategory B S hS Y).val)
        (Space.pointsMap B S hS _ (yonedaEquiv.symm (algebraicSpaceStackSection f ξ))
          (Space.FieldValuedPoint.class B S hS _ q)) := by
      refine hez.trans ?_
      rw [Space.pointsMap_class, spacePointMap_class]
      exact (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
        ⟨fieldValuedPointMap B S hS _ f.hom.hom z₀, ⟨𝟙 _⟩, ⟨eqToHom hobj⟩⟩
    rw [← (spacePointMap_id_bijective B S hS Y).1 key]
    exact he

/-- A 2-isomorphism `a ≫ f ≅ g` identifies the maps on points of `a ≫ f` and `g`. -/
private theorem pointsMap_pointsMap_eq_of_iso {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {a : 𝒳 ⟶ 𝒴} {f : 𝒴 ⟶ 𝒵} {g : 𝒳 ⟶ 𝒵} (e : a ≫ f ≅ g) (p : Stack.points B S hS 𝒳.val.val
      𝒳.val.property) :
    AlgebraicStacks.pointsMap B S hS f (AlgebraicStacks.pointsMap B S hS a p) =
      AlgebraicStacks.pointsMap B S hS g p := by
  rw [← Function.comp_apply (f := AlgebraicStacks.pointsMap B S hS f), ← pointsMap_comp]
  exact congrFun (AlgebraicStacks.pointsMap_eq_of_iso B S hS e) p

/-- **The image of a flat 1-morphism of finite type to an algebraic space is a quasi-compact
open.** Let `f : 𝒳 ⟶ Y` be flat, locally of finite presentation and of finite type, with `Y`
quasi-compact and quasi-separated. Then there is a quasi-compact open subspace `W ⊆ Y` whose
points are exactly the points of `Y` in the image of `|𝒳|`: it is the image of an affine smooth
surjective chart `U ⟶ 𝒳` (`exists_isAffine_smooth_surjective_chart`), and `U ⟶ Y` is flat and
locally of finite presentation, hence open on points (Stacks 042S). -/
theorem exists_isOpenSubspace_range_eq_image_of_isFlat {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hft : IsFiniteType B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) :
    ∃ (E : Set (Space.points B S hS Y)) (_ : @_root_.IsOpen _ (Space.pointTopology B S hS Y) E),
      Space.IsQuasiCompactSpace B S hS (Space.openSubspaceOfPoints B S hS Y E).toFunctor ∧
      ∀ y : Space.points B S hS Y,
        y ∈ E ↔
          spacePointMap B S hS Y (fibredCategory B S hS Y)
            (BasedFunctor.id (fibredCategory B S hS Y).val) y ∈
            Set.range (AlgebraicStacks.pointsMap B S hS f) := by
  let := Space.pointTopology B S hS Y
  obtain ⟨U, hUaff, c, φ, hcsm, hcsu, ⟨ec⟩, -, -, -⟩ :=
    Stack.exists_isAffine_smooth_surjective_chart B S hS hY hYqc hYqs f hft
  have hU := isAlgebraicSpace_yoneda B S hS U
  let := Space.pointTopology B S hS (yoneda.obj U)
  have hcf : IsFlat B S hS (c ≫ f) :=
    isFlat_comp B S hS c f (isFlat_of_isSmooth B S hS c hcsm) hflat
  have hcl : IsLocallyOfFinitePresentation B S hS (c ≫ f) :=
    isLocallyOfFinitePresentation_comp B S hS c f
      (isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) hlfp
  have hφf : Space.IsFlat B S hS φ :=
    (isFlat_algebraicSpaceStackMap_iff.{u, w} B S hS hU hY φ).1
      ((isFlat_iff_of_twoIso B S hS _ _ (algStackHomIso B S hS ec)).1 hcf)
  have hφl : Space.IsLocallyOfFinitePresentation B S hS φ :=
    (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hU hY φ).1
      ((isLocallyOfFinitePresentation_iff_of_twoIso B S hS _ _ (algStackHomIso B S hS ec)).1 hcl)
  let E := Set.range (Space.pointsMap B S hS (yoneda.obj U) φ)
  have hEo : _root_.IsOpen E := by
    simpa [E, Set.image_univ] using
      Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hU hY φ hφf hφl
        Set.univ isOpen_univ
  have hEc : IsCompact E := by
    have := Space.compactSpace_points_of_isQuasiCompactSpace B S hS hU
      (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS U hUaff)
    exact isCompact_range (Space.continuous_pointsMap B S hS φ)
  refine ⟨E, hEo, Space.isQuasiCompactSpace_of_isCompact_range B S hS hY
    (Space.isOpenSubspace_openSubspaceOfPoints B S hS hY E hEo)
    (by rwa [Space.range_pointsMap_ι_openSubspaceOfPoints B S hS E (F := Y)]), fun y => ?_⟩
  -- the image of a point of `U` in `|Y|` is the image of its image in `|𝒳|`
  have hpt : ∀ u : Space.points B S hS (yoneda.obj U),
      spacePointMap B S hS Y (fibredCategory B S hS Y)
          (BasedFunctor.id (fibredCategory B S hS Y).val) (Space.pointsMap B S hS _ φ u) =
        AlgebraicStacks.pointsMap B S hS f (AlgebraicStacks.pointsMap B S hS c
          (spacePointMap B S hS (yoneda.obj U) (fibredCategory B S hS (yoneda.obj U))
            (BasedFunctor.id (fibredCategory B S hS (yoneda.obj U)).val) u)) := by
    intro u
    rw [spacePointMap_algebraicSpaceStackMap B S hS hU hY φ u]
    exact (pointsMap_pointsMap_eq_of_iso ec _).symm
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (hpt u).symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z', rfl⟩ := hcsu z
    obtain ⟨u, rfl⟩ := (spacePointMap_id_bijective B S hS (yoneda.obj U)).2 z'
    exact ⟨u, (spacePointMap_id_bijective B S hS Y).1 ((hpt u).trans hz)⟩

/-- **[Stacks, Tag 0CQ7] for a flat morphism of finite presentation.** Let `f : 𝒳 ⟶ Y` be
separated, flat and of finite type and locally of finite presentation, with `Y` quasi-compact and
quasi-separated, and a gerbe over a quasi-compact open `V ⊆ Y`. Then one proper
compactifiable cover of `f` covers `|V|`.

The image `W` of `|f|` is a quasi-compact open containing `V` and the values of `f`
(`exists_isOpenSubspace_range_eq_image_of_isFlat`, `mem_openSubspaceOfPoints_of_pointsMap_mem`);
the base change `𝒳 ×_Y W ⟶ W` is surjective, flat and locally of finite presentation, so by
[Stacks, Tag 0CQ6] there is a finite surjective `g : Y' ⟶ Y` with sections of `𝒳` over the
members of an open covering of `g⁻¹(W)`; finitely many quasi-compact opens contained in them cover
`g⁻¹(W)`, and `hasCompactifiableCovers_of_sections_of_isGerbeOver_cover` applies to `g` and
`g⁻¹(V)`, whose image is `|V|`. -/
theorem hasCompactifiableCovers_of_isFlat {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) (V : Subfunctor Y)
    (hV : Space.IsOpenSubspace B S hS V) (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasCompactifiableCover hY f (Set.range (Space.pointsMap B S hS V.toFunctor V.ι)) := by
  let := Space.pointTopology B S hS Y
  obtain ⟨E, hEo, hWqc, hEr⟩ := exists_isOpenSubspace_range_eq_image_of_isFlat hY hYqc hYqs f hft
    hflat hlfp
  let W := Space.openSubspaceOfPoints B S hS Y E
  have hW : Space.IsOpenSubspace B S hS W :=
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hY E hEo
  have hWr : Set.range (Space.pointsMap B S hS W.toFunctor W.ι) = E :=
    Space.range_pointsMap_ι_openSubspaceOfPoints B S hS E (F := Y)
  let sp : ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), Space.points B S hS F →
      Stack.points B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property :=
    fun F => spacePointMap B S hS F (fibredCategory B S hS F)
      (BasedFunctor.id (fibredCategory B S hS F).val)
  -- the values of `f` lie in `W`
  have hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)) := by
    refine mem_openSubspaceOfPoints_of_pointsMap_mem f E fun z => ?_
    obtain ⟨y, hy⟩ := (spacePointMap_id_bijective B S hS Y).2 (AlgebraicStacks.pointsMap B S hS f z)
    exact ⟨y, (hEr y).2 ⟨z, hy.symm⟩, hy⟩
  -- `V ⊆ W`, the gerbe being surjective onto `V`
  let P := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  have hVW : V ≤ W := by
    refine Space.le_of_range_pointsMap_ι_subset B S hS hW ?_
    rintro _ ⟨v, rfl⟩
    rw [hWr, hEr]
    obtain ⟨p, hp⟩ := (isSurjective_of_isGerbeOver B S hS P.fst hG) (sp V.toFunctor v)
    refine ⟨AlgebraicStacks.pointsMap B S hS P.snd p, ?_⟩
    have h1 := pointsMap_pointsMap_eq_of_iso P.iso p
    rw [hp, ← spacePointMap_algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι v,
      pointsMap_comp] at h1
    exact h1.symm
  -- the base change `𝒳 ×_Y W ⟶ W` is surjective, flat and locally of finite presentation
  let Q := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι) f
  have hQ : IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f
  have hQs : IsSurjective B S hS Q.fst := by
    intro w
    obtain ⟨w₀, rfl⟩ := (spacePointMap_id_bijective B S hS W.toFunctor).2 w
    have hw : Space.pointsMap B S hS _ W.ι w₀ ∈ E := by
      rw [← hWr]
      exact ⟨w₀, rfl⟩
    obtain ⟨z, hz⟩ := (hEr _).1 hw
    obtain ⟨p, hp, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Q hQ _ z
      ((spacePointMap_algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι w₀).symm.trans hz.symm)
    exact ⟨p, hp⟩
  have hQf : IsFlat B S hS Q.fst := isFlat_baseChange B S hS f _ Q hQ hflat
  have hQl : IsLocallyOfFinitePresentation B S hS Q.fst :=
    isLocallyOfFinitePresentation_baseChange B S hS f _ Q hQ hlfp
  -- Stacks 0CQ6: sections over an open covering of the inverse image of `W` in a finite cover
  obtain ⟨Y', hY', g, hgf, hgs, J, Wj, hWj, ι, q, σ, hι, hιq, hcov, hσ⟩ :=
    Stack.exists_finite_surjective_zariskiLocal_factorization B S hS hY hYqc hYqs W
      hW hWqc Q.fst hQs hQf hQl
  let := Space.pointTopology B S hS Y'
  have hgp : Space.IsProper B S hS g :=
    ((Space.isFinite_iff_isAffineHom_and_isProper B S hS hY' hY g).1 hgf).2
  have hY'qc : Space.IsQuasiCompactSpace B S hS Y' :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hgp.2.1.2
  have hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY' hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hgp.1)
  -- the sections of `𝒳` over the members, read on their ranges in `Y'`
  have hO : ∀ j, Space.IsOpenSubspace B S hS (Subfunctor.range (ι j)) := fun j =>
    Space.isOpenSubspace_subfunctorRange B S hS (hWj j) (hι j)
  have hOW : ∀ j, Subfunctor.range (ι j) ≤ W.preimage g := by
    rintro j T _ ⟨y, rfl⟩
    show g.app T ((ι j).app T y) ∈ W.obj T
    rw [← FunctorToTypes.comp, hιq j, FunctorToTypes.comp]
    exact ((q j).app T y).2
  have hx : ∀ j, ∃ x : algebraicSpaceStack.{u, w} B S hS (Subfunctor.range (ι j)).toFunctor
      (hO j).1 ⟶ 𝒳, Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hO j).1 hY
        ((Subfunctor.range (ι j)).ι ≫ g)) := by
    intro j
    obtain ⟨eσ⟩ := hσ j
    have : Mono (ι j) := Space.mono_of_isOpenImmersion B S hS (ι j) (hι j)
    let e : Wj j ≅ (Subfunctor.range (ι j)).toFunctor := asIso (Subfunctor.toRange (ι j))
    have hfac : (Subfunctor.range (ι j)).ι ≫ g = e.inv ≫ q j ≫ W.ι := by
      rw [← hιq j, ← Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp]
      exact Subfunctor.toRange_ι (ι j)
    refine ⟨algebraicSpaceStackMap.{u, w} B S hS (hO j).1 (hWj j) e.inv ≫ σ j ≫ Q.snd, ⟨?_⟩⟩
    refine α_ _ _ _ ≪≫ whiskerLeftIso _ (α_ _ _ _ ≪≫ whiskerLeftIso _ Q.iso.symm ≪≫
      (α_ _ _ _).symm ≪≫ whiskerRightIso eσ _) ≪≫ eqToIso ?_
    rw [hfac, Stack.algebraicSpaceStackMap_comp B S hS (hWj j) hW.1 hY,
      Stack.algebraicSpaceStackMap_comp B S hS (hO j).1 (hWj j) hY]
  choose x ex using hx
  -- finitely many quasi-compact opens inside the members cover `g⁻¹(W)`
  have hWg : Space.IsOpenSubspace B S hS (W.preimage g) :=
    Space.isOpenSubspace_preimage B S hS g W hY hY' hW
  have hWgqc : Space.IsQuasiCompactSpace B S hS (W.preimage g).toFunctor :=
    Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY hY' g hgp.2.1.2 hW hWqc
  let K := Set.range (Space.pointsMap B S hS (W.preimage g).toFunctor (W.preimage g).ι)
  have hpiece : ∀ y ∈ K, ∃ (N : Subfunctor Y') (_ : Space.IsOpenSubspace B S hS N)
      (_ : Space.IsQuasiCompactSpace B S hS N.toFunctor) (j : J)
      (_ : N ≤ Subfunctor.range (ι j)), y ∈ Set.range (Space.pointsMap B S hS N.toFunctor N.ι) := by
    intro y hy
    have hy' : Space.pointsMap B S hS Y' g y ∈
        Set.range (Space.pointsMap B S hS W.toFunctor W.ι) := by
      change y ∈ Set.range (Space.pointsMap B S hS (W.preimage g).toFunctor (W.preimage g).ι) at hy
      rw [Space.range_pointsMap_preimage_ι] at hy
      exact hy
    obtain ⟨j, z, rfl⟩ := hcov y hy'
    have hj : Space.pointsMap B S hS _ (ι j) z ∈
        Set.range (Space.pointsMap B S hS (Subfunctor.range (ι j)).toFunctor
          (Subfunctor.range (ι j)).ι) :=
      ⟨Space.pointsMap B S hS _ (Subfunctor.toRange (ι j)) z, by
        rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
    obtain ⟨N, hN, hNqc, hyN, hNsub⟩ :=
      Space.exists_isQuasiCompactSpace_isOpenSubspace_range_subset B S hS hY' _
        (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hO j).2) _ hj
    exact ⟨N, hN, hNqc, j, Space.le_of_range_pointsMap_ι_subset B S hS (hO j) hNsub, hyN⟩
  choose Nf hNf hNfqc jf hNfO hyNf using hpiece
  have hK : IsCompact K := Space.isCompact_range_of_isQuasiCompactSpace B S hS hWg hWgqc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun y : K => Set.range (Space.pointsMap B S hS (Nf y.1 y.2).toFunctor (Nf y.1 y.2).ι))
    (fun y => Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hNf y.1 y.2).2)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyNf y hy⟩)
  let idx : Fin t.card → K := fun k => (t.equivFin.symm k).1
  let U : Fin t.card → Subfunctor Y' := fun k => Nf (idx k).1 (idx k).2
  have hU : ∀ k, Space.IsOpenSubspace B S hS (U k) := fun k => hNf _ _
  have hUO : ∀ k, U k ≤ Subfunctor.range (ι (jf (idx k).1 (idx k).2)) := fun k => hNfO _ _
  refine HasSectionCovers.hasCompactifiableCover
    ((hasSectionCovers_of_sections_of_isGerbeOver_cover f hf W hW hfW V hV hG t.card
    hY' hY'qc hY'qs g hgp (V.preimage g) (Space.isOpenSubspace_preimage B S hS g V hY hY' hV)
    (Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY hY' g hgp.2.1.2 hV hVqc) le_rfl
    (fun T _ h => hVW T h) U hU (fun k => hNfqc _ _) (fun k => (hUO k).trans (hOW _))
    (fun k => algebraicSpaceStackMap.{u, w} B S hS (hU k).1 (hO _).1
      (Subfunctor.homOfLe (hUO k)) ≫ x _)
    (fun k => (ex _).map fun e => α_ _ _ _ ≪≫ whiskerLeftIso _ e ≪≫
      eqToIso ((Stack.algebraicSpaceStackMap_comp B S hS (hU k).1 (hO _).1 hY _ _).trans
        (congrArg _ (by rw [← Category.assoc, Subfunctor.homOfLe_ι])))) ?_).mono ?_)
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨i, hi⟩, ?_⟩
    have hidx : idx (t.equivFin ⟨i, hi⟩) = i := by
      simp only [idx, Equiv.symm_apply_apply]
    show y ∈ Set.range (Space.pointsMap B S hS (Nf (idx (t.equivFin ⟨i, hi⟩)).1
      (idx (t.equivFin ⟨i, hi⟩)).2).toFunctor (Nf (idx (t.equivFin ⟨i, hi⟩)).1
        (idx (t.equivFin ⟨i, hi⟩)).2).ι)
    rw [hidx]
    exact hyi
  · rintro _ ⟨v, rfl⟩
    obtain ⟨y, hy⟩ := hgs (Space.pointsMap B S hS _ V.ι v)
    refine ⟨y, ?_, hy⟩
    rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, hy]
    exact ⟨v, rfl⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
