module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Refining a Zariski-local factorization to a finite affine open covering

Let `X` be a presheaf on the big fppf site of a scheme `S`, let `p : U ⟶ X` be a morphism of
presheaves, and let `f : h_Y ⟶ X` be a morphism from the presheaf represented by an object
`Y` of the site. Suppose that `f` factors through `p` *Zariski locally on `Y`*: every point
of `Y` has an open subspace neighbourhood in `h_Y` over which `f` factors through `p`.

If the scheme underlying `Y` is quasi-compact, the covering by those neighbourhoods can then
be refined to a covering by *finitely many affine open subschemes of `Y`*, each of which
still factors through `p`.

## Main results

* `AlgebraicGeometry.Space.exists_finite_affine_cover_factoring`: the refinement, with the
  members of the refined covering produced as objects of the site together with their open
  immersions into `Y`.
* `AlgebraicGeometry.Space.exists_finite_affine_cover_factoring_of_isQuasiCompactSpace`: the
  same with quasi-compactness of `Y` asked for at the level of the algebraic space `h_Y`
  rather than of the scheme.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_factoring_of_openCover`: given
  a covering of `Y` by open immersions along each of which `f` factors through `p`, every point
  of `h_Y` lies in a representable open subspace over which `f` factors through `p`, as in the
  local clause of Stacks 09YC (2).

## References

* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `p : U ⟶ X` be a morphism of presheaves on the big fppf site of `S` and let
`f : h_Y ⟶ X` be a morphism from the presheaf represented by an object `Y` of the site whose
underlying scheme is quasi-compact. Assume that every point of `h_Y` lies in the point set of an
open subspace of `h_Y` over which `f` factors through `p`. Then there are finitely many objects
`Z i` of the site, with affine underlying schemes, and open immersions `Z i ⟶ Y` whose images
cover `Y`, such that `f` restricted along each of them factors through `p`. -/
theorem exists_finite_affine_cover_factoring
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : U ⟶ X) (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (hY : CompactSpace ((BigFppfOver.toScheme B S hS).obj Y))
    (hloc : ∀ y : points B S hS (yoneda.obj Y),
      ∃ W : Subfunctor (yoneda.obj Y), IsOpenSubspace B S hS W ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p) :
    ∃ (ι : Type u) (_ : Finite ι) (Z : ι → BigFppfOver B S hS) (q : ∀ i, Z i ⟶ Y),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z i))) ∧
      (∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      ∀ i, ∃ g : yoneda.obj (Z i) ⟶ U, yoneda.map (q i) ≫ f = g ≫ p := by
  classical
  have key : ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
      ∃ (Z : BigFppfOver B S hS) (q : Z ⟶ Y),
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map q) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
        IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map q)) ∧
        y ∈ Set.range ((BigFppfOver.toScheme B S hS).map q) ∧
        ∃ g : yoneda.obj Z ⟶ U, yoneda.map q ≫ f = g ≫ p := by
    intro y
    obtain ⟨W, hW, hyW, g₀, hg₀⟩ := hloc ((pointsEquivScheme B S hS Y).symm y)
    have hOopen : IsOpen (Set.range (pointsMap B S hS W.toFunctor W.ι)) :=
      isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hW.2
    have hOimg : IsOpen (pointsToScheme B S hS Y ''
        Set.range (pointsMap B S hS W.toFunctor W.ι)) :=
      (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS Y _).1 hOopen
    have hymem : y ∈ pointsToScheme B S hS Y ''
        Set.range (pointsMap B S hS W.toFunctor W.ι) :=
      ⟨_, hyW, (pointsEquivScheme B S hS Y).apply_symm_apply y⟩
    obtain ⟨V, hVaff, hyV, hVsub⟩ :=
      Opens.isBasis_iff_nbhd.1 ((BigFppfOver.toScheme B S hS).obj Y).isBasis_affineOpens
        (show y ∈ (⟨_, hOimg⟩ : Opens _) from hymem)
    obtain ⟨Z, q, hqoi, hqrange, hquniv⟩ := exists_restrict_bigFppfOver Y V
    have hle : Subfunctor.range (yoneda.map q) ≤ W := by
      have hVeq : Subfunctor.range (yoneda.map q) =
          openSubspaceOfPoints B S hS (yoneda.obj Y)
            (pointsToScheme B S hS Y ⁻¹' (V : Set _)) := by
        rw [← Subfunctor.preimage_id (openSubspaceOfPoints B S hS (yoneda.obj Y)
          (pointsToScheme B S hS Y ⁻¹' (V : Set _)))]
        refine range_yoneda_map_eq_preimage_openSubspaceOfPoints B S hS _
          (𝟙 (yoneda.obj Y)) q (V : Set _) hqrange (fun g hg ↦ hquniv g hg) fun P ↦ ?_
        rw [pointsMap_id]
        exact Iff.rfl
      rw [hVeq]
      refine le_of_range_pointsMap_ι_subset B S hS hW ?_
      rw [range_pointsMap_ι_openSubspaceOfPoints]
      intro w hw
      obtain ⟨w', hw'O, hw'eq⟩ := hVsub hw
      exact injective_pointsToScheme B S hS Y hw'eq ▸ hw'O
    have hor : ((BigFppfOver.toScheme B S hS).map q).opensRange = V :=
      Opens.ext hqrange
    have haff : IsAffine ((BigFppfOver.toScheme B S hS).map q).opensRange := by
      rwa [hor]
    refine ⟨Z, q, hqoi, IsAffine.of_isIso
      ((BigFppfOver.toScheme B S hS).map q).isoOpensRange.hom, ?_, ?_,
      Subfunctor.lift (yoneda.map q) hle ≫ g₀, ?_⟩
    · rw [hqrange]; exact V.2
    · rwa [hqrange]
    · rw [Category.assoc, ← hg₀, ← Category.assoc, Subfunctor.lift_ι]
  choose Z q hqoi hqaff hqopen hqmem hqfac using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y ↦ Set.range ((BigFppfOver.toScheme B S hS).map (q y))) hqopen
    fun y _ ↦ Set.mem_iUnion.2 ⟨y, hqmem y⟩
  refine ⟨{y // y ∈ t}, inferInstance, fun i ↦ Z i.1, fun i ↦ q i.1,
    fun i ↦ hqoi i.1, fun i ↦ hqaff i.1, fun y ↦ ?_, fun i ↦ hqfac i.1⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact ⟨⟨z, hz⟩, hyz⟩

/-- `AlgebraicGeometry.Space.exists_finite_affine_cover_factoring` with quasi-compactness of
`Y` in its space-level form: the space of points of `h_Y` is quasi-compact in the sense of
Stacks 03E4. -/
theorem exists_finite_affine_cover_factoring_of_isQuasiCompactSpace
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : U ⟶ X) (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (hY : IsQuasiCompactSpace B S hS (yoneda.obj Y))
    (hloc : ∀ y : points B S hS (yoneda.obj Y),
      ∃ W : Subfunctor (yoneda.obj Y), IsOpenSubspace B S hS W ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p) :
    ∃ (ι : Type u) (_ : Finite ι) (Z : ι → BigFppfOver B S hS) (q : ∀ i, Z i ⟶ Y),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z i))) ∧
      (∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      ∀ i, ∃ g : yoneda.obj (Z i) ⟶ U, yoneda.map (q i) ≫ f = g ≫ p := by
  refine exists_finite_affine_cover_factoring B S hS p Y f ?_ hloc
  have hpts : CompactSpace (points B S hS (yoneda.obj Y)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _
      (isAlgebraicSpace_yoneda B S hS Y)).1 hY
  have hcont : Continuous (pointsToScheme B S hS Y) := continuous_def.2 fun V hV ↦ by
    refine (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS Y _).2 ?_
    rwa [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS Y)]
  refine ⟨?_⟩
  rw [← Set.image_univ_of_surjective (surjective_pointsToScheme B S hS Y)]
  exact isCompact_univ.image hcont

/-- A family of open immersions `Z i ⟶ Y` of objects of the site whose images cover the scheme
underlying `Y`, and along each of which `f : h_Y ⟶ X` factors through `p : U ⟶ X`, exhibits
every point of `h_Y` as lying in an open subspace of `h_Y` which is representable and over which
`f` factors through `p`. -/
theorem exists_isOpenSubspace_isRepresentable_factoring_of_openCover
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : U ⟶ X) (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) {ι : Type u} (Z : ι → BigFppfOver B S hS) (q : ∀ i, Z i ⟶ Y)
    (hqoi : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (q i)))
    (hcov : ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i)))
    (hfac : ∀ i, ∃ g : yoneda.obj (Z i) ⟶ U, yoneda.map (q i) ≫ f = g ≫ p)
    (y : points B S hS (yoneda.obj Y)) :
    ∃ W : Subfunctor (yoneda.obj Y), IsOpenSubspace B S hS W ∧
      W.toFunctor.IsRepresentable ∧
      y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
      ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p := by
  obtain ⟨i, hi⟩ := hcov (pointsToScheme B S hS Y y)
  obtain ⟨g₀, hg₀⟩ := hfac i
  have hoi := hqoi i
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (q i)) := inferInstance
  have : Mono (q i) := (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono
  have hmy : Mono (yoneda.map (q i)) := inferInstance
  have hfacι : Subfunctor.toRange (yoneda.map (q i)) ≫
      (Subfunctor.range (yoneda.map (q i))).ι = yoneda.map (q i) :=
    Subfunctor.toRange_ι _
  set e := Subfunctor.toRange (yoneda.map (q i))
  have hiso : IsIso e := inferInstance
  have hpi : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (q i)) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance (q i) hoi
  have hι : inv e ≫ yoneda.map (q i) = (Subfunctor.range (yoneda.map (q i))).ι :=
    (IsIso.inv_comp_eq e).2 hfacι.symm
  have hcomp : pointsMap B S hS (yoneda.obj (Z i)) (yoneda.map (q i)) =
      pointsMap B S hS _ (Subfunctor.range (yoneda.map (q i))).ι ∘
        pointsMap B S hS (yoneda.obj (Z i)) e := by
    rw [← pointsMap_comp, hfacι]
  refine ⟨Subfunctor.range (yoneda.map (q i)),
    ⟨(isAlgebraicSpace_yoneda B S hS (Z i)).of_iso (asIso e), ?_⟩, ?_, ?_,
    inv e ≫ g₀, ?_⟩
  · rw [← hι]
    exact MorphismProperty.RespectsIso.precomp _ (inv e) _ hpi
  · obtain ⟨A, ⟨r⟩⟩ := (inferInstance : (yoneda.obj (Z i)).IsRepresentable)
    exact ⟨A, ⟨r.ofIso (asIso e)⟩⟩
  · obtain ⟨w, hw⟩ := mem_range_pointsMap_yoneda_map B S hS (q i) y hi
    refine ⟨pointsMap B S hS (yoneda.obj (Z i)) e w, ?_⟩
    rw [← hw, hcomp, Function.comp_apply]
  · rw [Category.assoc, ← hg₀, ← hι, Category.assoc]

end AlgebraicGeometry.Space

end
