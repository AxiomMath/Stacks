module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRefiningFiniteCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace

/-!
# Quasi-compactness of a morphism of algebraic spaces is Zariski-local on the target

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is quasi-compact if and only if
there is a Zariski covering `Y = ⋃ Y i` such that each `f⁻¹(Y i) ⟶ Y i` is quasi-compact.

A Zariski covering of `Y` is a family of open subspaces `W i` of `Y` whose point sets cover the
space of points of `Y`, and the morphism `f⁻¹(W i) ⟶ W i` is the projection
`pullback.snd f (W i).ι`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_zariskiCover`: if each `f⁻¹(W i) ⟶ W i` is
  quasi-compact for a Zariski covering `W` of `Y`, then `f` is quasi-compact;
  `AlgebraicGeometry.Space.exists_zariskiCover_isQuasiCompact_pullback_snd` is the converse.
* `AlgebraicGeometry.Space.isQuasiCompact_pullback_snd_of_openCover`: quasi-compactness of the
  base change of `f` along a morphism `φ : h_V ⟶ Y` from a represented presheaf may be checked
  on a Zariski open covering of `V` by objects of the site.
* `AlgebraicGeometry.Space.isQuasiCompact_of_openImmersion_cover`: quasi-compactness of `f` may
  be checked after base change along a family of open immersions of presheaves into `Y` which is
  jointly surjective on points.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_finite_jointly_surjective'`: an algebraic
  space is quasi-compact as soon as finitely many morphisms from quasi-compact algebraic
  spaces into it are jointly surjective on points.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point set of the range of a monomorphism of presheaves is the image of its map on
points. -/
theorem range_pointsMap_ι_subfunctorRange {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ G) [Mono k] :
    Set.range (pointsMap B S hS (Subfunctor.range k).toFunctor (Subfunctor.range k).ι) =
      Set.range (pointsMap B S hS F k) := by
  have hcomp : pointsMap B S hS F k =
      pointsMap B S hS (Subfunctor.range k).toFunctor (Subfunctor.range k).ι ∘
        pointsMap B S hS F (Subfunctor.toRange k) := by
    rw [← pointsMap_comp, Subfunctor.toRange_ι]
  rw [hcomp, Set.range_comp,
    (pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange k)).range_eq, Set.image_univ]


/-- A morphism from a represented presheaf into a coproduct of presheaves factors through one
summand. -/
private theorem exists_factor_sigma {I : Type u} (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {A : BigFppfOver B S hS} (c : yoneda.obj A ⟶ ∐ F) :
    ∃ (i : I) (l : yoneda.obj A ⟶ F i), l ≫ Sigma.ι F i = c := by
  have hcolim := isColimitOfPreserves
    ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (Opposite.op A))
    (colimit.isColimit (Discrete.functor F))
  obtain ⟨j, s, hs⟩ := Types.jointly_surjective_of_isColimit hcolim (yonedaEquiv c)
  refine ⟨j.as, yonedaEquiv.symm s, ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  simpa using hs

/-- Quasi-compactness of a morphism of presheaves transfers across a commuting square whose
two horizontal arrows are isomorphisms. -/
private theorem isQuasiCompact_of_isIso_comp
    {F F' G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : F ⟶ G) (p : F' ⟶ G')
    (u : F ⟶ F') (v : G ⟶ G') [IsIso u] [IsIso v] (hcomm : u ≫ p = b ≫ v)
    (hp : IsQuasiCompact B S hS p) : IsQuasiCompact B S hS b :=
  isQuasiCompact_of_isPullback B S hS (IsPullback.of_horiz_isIso ⟨hcomm⟩) hp

/-- If `a j : A j ⟶ P` is a finite family of morphisms of algebraic spaces over `S` whose
sources are quasi-compact and whose maps on points jointly cover the points of `P`, then `P` is
quasi-compact. -/
theorem isQuasiCompactSpace_of_finite_jointly_surjective'
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {J : Type*} [Finite J] {A : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : ∀ j, IsAlgebraicSpace B S hS (A j)) (a : ∀ j, A j ⟶ P)
    (hAqc : ∀ j, IsQuasiCompactSpace B S hS (A j))
    (hcov : ∀ w : points B S hS P, ∃ j, w ∈ Set.range (pointsMap B S hS (A j) (a j))) :
    IsQuasiCompactSpace B S hS P := by
  refine isQuasiCompactSpace_of_compactSpace_points B S hS hP ⟨?_⟩
  have hcpt : IsCompact (⋃ j, Set.range (pointsMap B S hS (A j) (a j))) :=
    isCompact_iUnion fun j => by
      have := compactSpace_points_of_isQuasiCompactSpace B S hS (hA j) (hAqc j)
      exact isCompact_range (continuous_pointsMap B S hS (a j))
  have heq : (⋃ j, Set.range (pointsMap B S hS (A j) (a j))) = Set.univ :=
    Set.eq_univ_of_univ_subset fun w _ => Set.mem_iUnion.2 (hcov w)
  exact heq ▸ hcpt

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `k i : Y' i ⟶ Y` be a
family of open immersions of presheaves, with each `Y' i` an algebraic space over `S`, which
is jointly surjective on points. If each base change `pullback.snd f (k i)` is quasi-compact,
then so is `f`. -/
theorem isQuasiCompact_of_openImmersion_cover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {I : Type u} {Y' : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : ∀ i, IsAlgebraicSpace B S hS (Y' i)) (k : ∀ i, Y' i ⟶ Y)
    (hk : ∀ i, IsOpenImmersion B S hS (k i))
    (hcov : ∀ y : points B S hS Y, ∃ i, y ∈ Set.range (pointsMap B S hS (Y' i) (k i)))
    (h : ∀ i, IsQuasiCompact B S hS (pullback.snd f (k i))) :
    IsQuasiCompact B S hS f := by
  classical
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine' B S hS f hX hY
    fun Z g hZaff => ?_
  refine isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry g f) ?_
  have hZcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj Z) :=
    @Scheme.compactSpace_of_isAffine _ hZaff
  have hmono : ∀ i, Mono (k i) := fun i => mono_of_presheaf_isOpenImmersion (hk i)
  have hΩ : ∀ i, IsOpenSubspace B S hS (Subfunctor.range (k i)) := fun i =>
    isOpenSubspace_subfunctorRange B S hS (hY' i) (hk i)
  have hΩrange : ∀ i, Set.range (pointsMap B S hS (Subfunctor.range (k i)).toFunctor
      (Subfunctor.range (k i)).ι) = Set.range (pointsMap B S hS (Y' i) (k i)) := fun i =>
    have _ := hmono i
    range_pointsMap_ι_subfunctorRange B S hS (k i)
  have hloc : ∀ y : points B S hS (yoneda.obj Z),
      ∃ W : Subfunctor (yoneda.obj Z), IsOpenSubspace B S hS W ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ q : W.toFunctor ⟶ (∐ Y'), W.ι ≫ g = q ≫ Sigma.desc k := by
    intro y
    obtain ⟨i, hi⟩ := hcov (pointsMap B S hS (yoneda.obj Z) g y)
    have _ := hmono i
    have hopen : IsOpen (pointsMap B S hS (yoneda.obj Z) g ⁻¹'
        Set.range (pointsMap B S hS (Y' i) (k i))) :=
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS (k i) (hk i)).preimage
        (continuous_pointsMap B S hS g)
    set W := openSubspaceOfPoints B S hS (yoneda.obj Z)
      (pointsMap B S hS (yoneda.obj Z) g ⁻¹' Set.range (pointsMap B S hS (Y' i) (k i)))
      with hWdef
    have hWrange : Set.range (pointsMap B S hS W.toFunctor W.ι) =
        pointsMap B S hS (yoneda.obj Z) g ⁻¹' Set.range (pointsMap B S hS (Y' i) (k i)) := by
      rw [hWdef, range_pointsMap_ι_openSubspaceOfPoints]
    have hsub : Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ g)) ⊆
        Set.range (pointsMap B S hS (Y' i) (k i)) := by
      rw [pointsMap_comp, Set.range_comp, hWrange]
      exact Set.image_preimage_subset _ _
    have hle : Subfunctor.range (W.ι ≫ g) ≤ Subfunctor.range (k i) :=
      (range_le_openSubspaceOfPoints_range_pointsMap (W.ι ≫ g)).trans
        ((openSubspaceOfPoints_mono B S hS hsub).trans
          (le_of_range_pointsMap_ι_subset B S hS (hΩ i) (by
            rw [range_pointsMap_ι_openSubspaceOfPoints, hΩrange i])))
    have hι : inv (Subfunctor.toRange (k i)) ≫ k i = (Subfunctor.range (k i)).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι (k i)).symm
    refine ⟨W, isOpenSubspace_openSubspaceOfPoints B S hS
      (isAlgebraicSpace_yoneda B S hS Z) _ hopen, by rwa [hWrange],
      Subfunctor.lift (W.ι ≫ g) hle ≫ inv (Subfunctor.toRange (k i)) ≫ Sigma.ι Y' i, ?_⟩
    rw [Category.assoc, Category.assoc, Sigma.ι_desc, hι, Subfunctor.lift_ι]
  obtain ⟨J, hJ, Zk, q, hqoi, hqaff, hqcov, hqfac⟩ :=
    exists_finite_affine_cover_factoring B S hS (Sigma.desc k) Z g hZcpt hloc
  have hsplit : ∀ j, ∃ (i : I) (l : yoneda.obj (Zk j) ⟶ Y' i),
      yoneda.map (q j) ≫ g = l ≫ k i := by
    intro j
    obtain ⟨c, hc⟩ := hqfac j
    obtain ⟨i, l, hl⟩ := exists_factor_sigma B S hS Y' c
    exact ⟨i, l, by rw [hc, ← hl, Category.assoc, Sigma.ι_desc]⟩
  choose idx l hl using hsplit
  have hqc : ∀ j, IsQuasiCompactSpace B S hS (pullback (yoneda.map (q j) ≫ g) f) := by
    intro j
    have hZkcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj (Zk j)) :=
      @Scheme.compactSpace_of_isAffine _ (hqaff j)
    exact isQuasiCompactSpace_of_iso B S hS
      (pullbackSymmetry (l j) (pullback.snd f (k (idx j))) ≪≫
        pullbackLeftPullbackSndIso f (k (idx j)) (l j) ≪≫
        pullbackSymmetry f (l j ≫ k (idx j)) ≪≫
        pullback.congrHom (hl j).symm rfl)
      (h (idx j) (yoneda.obj (Zk j)) (isAlgebraicSpace_yoneda B S hS (Zk j))
        (isQuasiCompactSpace_yoneda_obj B S hS hZkcpt) (l j))
  have hsq : ∀ j, ∃ c : pullback (yoneda.map (q j) ≫ g) f ⟶ pullback g f,
      IsPullback c (pullback.fst (yoneda.map (q j) ≫ g) f) (pullback.fst g f)
        (yoneda.map (q j)) := fun j =>
    ⟨_, IsPullback.of_right' ((IsPullback.of_hasPullback (yoneda.map (q j) ≫ g) f).flip)
      ((IsPullback.of_hasPullback g f).flip)⟩
  choose c hc using hsq
  refine isQuasiCompactSpace_of_finite_jointly_surjective' B S hS
    (isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS Z) hX hY)
    (fun j => isAlgebraicSpace_pullback B S hS (yoneda.map (q j) ≫ g) f
      (isAlgebraicSpace_yoneda B S hS (Zk j)) hX hY) c hqc ?_
  intro w
  obtain ⟨j, hj⟩ := hqcov
    (pointsToScheme B S hS Z (pointsMap B S hS (pullback g f) (pullback.fst g f) w))
  obtain ⟨zk, hzk⟩ := mem_range_pointsMap_yoneda_map B S hS (q j) _ hj
  obtain ⟨v, hv, -⟩ := exists_points_of_isPullback B S hS (hc j) w zk hzk.symm
  exact ⟨j, v, hv⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`. If there is a Zariski covering
of `Y` by open subspaces `W i`, that is one whose point sets cover the space of points of `Y`,
such that each of the morphisms `f⁻¹(W i) ⟶ W i`, that is `pullback.snd f (W i).ι`, is
quasi-compact, then `f` is quasi-compact. -/
@[stacks 03KG "part (6) implies part (1)"]
theorem isQuasiCompact_of_zariskiCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {I : Type u} (W : I → Subfunctor Y) (hW : ∀ i, IsOpenSubspace B S hS (W i))
    (hcov : ∀ y : points B S hS Y, ∃ i,
      y ∈ Set.range (pointsMap B S hS (W i).toFunctor (W i).ι))
    (h : ∀ i, IsQuasiCompact B S hS (pullback.snd f (W i).ι)) :
    IsQuasiCompact B S hS f :=
  isQuasiCompact_of_openImmersion_cover B S hS f hX hY (fun i => (hW i).1)
    (fun i => (W i).ι) (fun i => (hW i).2) hcov h

/-- A quasi-compact morphism `f : X ⟶ Y` of algebraic spaces over `S` admits a Zariski
covering of `Y` over each member of which its restriction is quasi-compact. -/
@[stacks 03KG "part (1) implies part (6)"]
theorem exists_zariskiCover_isQuasiCompact_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsQuasiCompact B S hS f) :
    ∃ (I : Type u) (W : I → Subfunctor Y), (∀ i, IsOpenSubspace B S hS (W i)) ∧
      (∀ y : points B S hS Y, ∃ i,
        y ∈ Set.range (pointsMap B S hS (W i).toFunctor (W i).ι)) ∧
      ∀ i, IsQuasiCompact B S hS (pullback.snd f (W i).ι) :=
  ⟨PUnit.{u + 1}, fun _ => ⊤, fun _ => isOpenSubspace_top hY,
    fun y => ⟨⟨⟩, pointsMap_surjective_of_isIso B S hS (Subfunctor.ι (⊤ : Subfunctor Y)) y⟩,
    fun _ => isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f _) hf⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let
`φ : h_V ⟶ Y` be a morphism from the presheaf represented by an object `V` of the site, and
let `j i : W i ⟶ V` be a family of morphisms of the site whose underlying morphisms of schemes
are open immersions with images covering `V`. If the base change of `f` along each composite
`h_{W i} ⟶ h_V ⟶ Y` is quasi-compact, then so is the projection `V ×_Y X ⟶ h_V`. -/
theorem isQuasiCompact_pullback_snd_of_openCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y)
    {I : Type u} (W : I → BigFppfOver B S hS) (j : ∀ i, W i ⟶ V)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcov : ∀ v : (BigFppfOver.toScheme B S hS).obj V,
      ∃ i, v ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)))
    (h : ∀ i, IsQuasiCompact B S hS (pullback.snd f (yoneda.map (j i) ≫ φ))) :
    IsQuasiCompact B S hS (pullback.snd f φ) := by
  refine isQuasiCompact_of_openImmersion_cover B S hS (pullback.snd f φ)
    (isAlgebraicSpace_pullback B S hS f φ hX (isAlgebraicSpace_yoneda B S hS V) hY)
    (isAlgebraicSpace_yoneda B S hS V)
    (fun i => isAlgebraicSpace_yoneda B S hS (W i)) (fun i => yoneda.map (j i))
    (fun i => presheaf_yoneda_map_of_inverseImage B S hS inferInstance (j i) (hj i))
    (fun y => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := hcov (pointsToScheme B S hS V y)
    exact ⟨i, mem_range_pointsMap_yoneda_map B S hS (j i) y hi⟩
  · exact isQuasiCompact_of_isIso_comp B S hS _ _
      (pullbackLeftPullbackSndIso f φ (yoneda.map (j i))).hom (𝟙 _) (by simp) (h i)

end AlgebraicGeometry.Space

end
