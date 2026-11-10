module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Affine atlases of algebraic spaces

Every algebraic space over a scheme `S` admits a surjective étale chart whose source is a
disjoint union of affine schemes, each of which maps into an affine open of `S`.

## Main results

* `AlgebraicGeometry.Scheme.iSup_affineOpens_le_preimage_affineOpens`: the affine opens of
  `X` which are contained in the preimage of an affine open of the target of a morphism
  `q : X ⟶ Y` already cover `X`.
* `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`: for a property of
  scheme morphisms stable under base change, the represented morphism `yoneda.map j` has the
  relatively representable form of that property exactly when the underlying morphism of
  schemes has it.
* `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`: a morphism between the underlying
  schemes of two objects of the big fppf category over `S` which commutes with the structure
  morphisms to `S` comes from a morphism of that category.
* `AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`: an algebraic space has a
  surjective étale chart which is a disjoint union of objects of the big fppf category over `S`
  with affine underlying schemes, each an open subscheme of the chart, étale over the space and
  mapping into an affine open of `S`.
* `AlgebraicGeometry.IsAlgebraicSpace.exists_etale_surjective_coproduct_affine_cover`: an
  algebraic space has a surjective étale chart whose source is a disjoint union of affine
  schemes, each mapping into an affine open of `S`.
* `AlgebraicGeometry.IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover`: an algebraic
  space has a surjective étale chart whose source is a separated scheme.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Affine opens over affine opens -/

/-- Every point of the source of a morphism of schemes `q : X ⟶ Y` has an affine open
neighbourhood which is contained in the preimage of an affine open of `Y`. -/
theorem Scheme.exists_affineOpen_le_preimage_affineOpen {X Y : Scheme.{u}} (q : X ⟶ Y)
    (x : X) : ∃ (A : X.affineOpens) (W : Y.affineOpens), x ∈ A.1 ∧ A.1 ≤ q ⁻¹ᵁ W.1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (a := q x) (Set.mem_univ _) isOpen_univ
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (a := x) hxW (q ⁻¹ᵁ W : X.Opens).2
  exact ⟨⟨A, hA⟩, ⟨W, hW⟩, hxA, hAW⟩

/-- The affine opens of `X` which are contained in the preimage of an affine open of `Y`
along a morphism `q : X ⟶ Y` cover `X`. -/
theorem Scheme.iSup_affineOpens_le_preimage_affineOpens {X Y : Scheme.{u}} (q : X ⟶ Y) :
    (⨆ A : {A : X.affineOpens // ∃ W : Y.affineOpens, A.1 ≤ q ⁻¹ᵁ W.1},
      (A.1.1 : X.Opens)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨A, W, hxA, hAW⟩ := Scheme.exists_affineOpen_le_preimage_affineOpen q x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨A, W, hAW⟩, hxA⟩

/-! ### Representable morphism properties of represented morphisms -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image along `AlgebraicGeometry.BigFppfOver.toScheme` of a property of scheme
morphisms which is stable under base change is again stable under base change. -/
theorem BigFppfOver.isStableUnderBaseChange_inverseImage
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun hs hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
    (hs.map (BigFppfOver.toScheme B S hS)) hg⟩

/-- A represented morphism of presheaves on the big fppf category over `S` satisfies the
relatively representable form of a base-change stable property of scheme morphisms exactly
when the underlying morphism of schemes satisfies that property. -/
theorem BigFppfOver.presheaf_inverseImage_yoneda_map_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {W U : BigFppfOver B S hS} (j : W ⟶ U) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j) ↔
      P ((BigFppfOver.toScheme B S hS).map j) := by
  have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS P
  exact MorphismProperty.relative_map_iff

/-- A morphism between the underlying schemes of two objects of the big fppf category over `S`
which is compatible with their structure morphisms to `S` is the image of a morphism of the
category. -/
theorem BigFppfOver.exists_hom_of_comp_eq {X Y : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hφ : φ ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom) :
    ∃ ψ : X ⟶ Y, (BigFppfOver.toScheme B S hS).map ψ = φ :=
  ⟨Over.homMk (B.inclusion.preimage φ) (B.inclusion.map_injective
    (by rw [Functor.map_comp, B.inclusion.map_preimage]; exact hφ)),
    B.inclusion.map_preimage φ⟩

/-! ### Affine atlases -/

/-- An algebraic space over `S` has a surjective étale chart `f : yoneda.obj U ⟶ F` whose
underlying scheme is the coproduct of the underlying schemes of objects `W i`, compatibly with
morphisms `j i : W i ⟶ U`. Each `W i` has affine underlying scheme mapping into an affine open
of `S`, each `j i` is an open immersion on underlying schemes, and each composite
`yoneda.map (j i) ≫ f` is étale. -/
theorem IsAlgebraicSpace.exists_affine_coproduct_atlas
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS)
      (f : yoneda.obj U ⟶ F)
      (I : Type u) (W : I → BigFppfOver B S hS) (j : ∀ i, W i ⟶ U)
      (e : (∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) ≅
        (BigFppfOver.toScheme B S hS).obj U),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i))) ∧
      (∀ i, Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) i ≫ e.hom =
        (BigFppfOver.toScheme B S hS).map (j i)) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i))) ∧
      (∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (yoneda.map (j i) ≫ f)) ∧
      (∀ i, ∃ (V : S.Opens), IsAffineOpen V ∧
        ∀ y : (BigFppfOver.toScheme B S hS).obj (W i),
          ((BigFppfOver.toScheme B S hS).map (j i) ≫ B.inclusion.map U.hom) y ∈ V) := by
  obtain ⟨V, p, hpS, hpE⟩ := hF.exists_atlas
  set X : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj V
  set q : X ⟶ S := B.inclusion.map V.hom
  set I : Type u := {A : X.affineOpens // ∃ W : S.affineOpens, A.1 ≤ q ⁻¹ᵁ W.1}
  set Y : I → Scheme.{u} := fun i ↦ (i.1.1 : X.Opens)
  set a : (∐ Y) ⟶ X := Sigma.desc fun i ↦ (i.1.1 : X.Opens).ι with ha
  have hcover : (⨆ i : I, (i.1.1 : X.Opens)) = ⊤ :=
    Scheme.iSup_affineOpens_le_preimage_affineOpens q
  have hmkI : Cardinal.mk I ≤ X.size :=
    (Cardinal.mk_le_of_injective (f := fun i : I ↦ i.1)
      fun _ _ hij ↦ Subtype.ext hij).trans (Scheme.mk_affineOpens_le_size X)
  have hZ : (∐ Y).size < B.cutoff :=
    (schemeSize_coproduct_le Y X.size (Scheme.aleph0_le_size X) hmkI
      fun i ↦ Scheme.size_coe_opens_le X i.1.1).trans_lt V.left.2
  set mk : ∀ {T : Scheme.{u}}, B.Contains T → (T ⟶ X) → BigFppfOver B S hS := fun hT h ↦
    Over.mk ((B.inclusion.preimage (X := B.obj hT) (Y := V.left)
      (show B.inclusion.obj (B.obj hT) ⟶ B.inclusion.obj V.left from h)) ≫ V.hom)
  have hmk : ∀ {T : Scheme.{u}} (hT : B.Contains T) (h : T ⟶ X),
      B.inclusion.map (mk hT h).hom = h ≫ q := fun _ _ ↦
    (B.inclusion.map_comp _ _).trans (by rw [B.inclusion.map_preimage])
  set U := mk hZ a
  set g : U ⟶ V := Over.homMk (B.inclusion.preimage
    (show B.inclusion.obj (B.obj hZ) ⟶ B.inclusion.obj V.left from a))
  have hgmap : (BigFppfOver.toScheme B S hS).map g = a := B.inclusion.map_preimage _
  have hasurj : Surjective a := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_iff_forall.mpr fun x ↦ ?_)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover.ge (show x ∈ (⊤ : X.Opens) from trivial))
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi⟩, rfl⟩
  have haetale : Etale a := by
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance
  have hcs : MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) := by
    have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have : MorphismProperty.IsStableUnderComposition
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    infer_instance
  have hce : MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) :=
    (Space.isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  have hgs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map g) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ g).2 (hgmap ▸ hasurj)
  have hge : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map g) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ g).2 (hgmap ▸ haetale)
  have hYlt : ∀ i : I, B.Contains (Y i) := fun i ↦
    (Scheme.size_coe_opens_le X i.1.1).trans_lt V.left.2
  set W : I → BigFppfOver B S hS := fun i ↦ mk (hYlt i) (i.1.1 : X.Opens).ι
  have hj : ∀ i : I, ∃ ψ : W i ⟶ U, (BigFppfOver.toScheme B S hS).map ψ = Sigma.ι Y i := by
    intro i
    refine BigFppfOver.exists_hom_of_comp_eq B S hS (X := W i) (Y := U) (Sigma.ι Y i) ?_
    rw [hmk, hmk, ← Category.assoc, Sigma.ι_comp_desc]
  choose j hjmap using hj
  have hjimm : ∀ i : I, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := fun i ↦
    (hjmap i) ▸ inferInstance
  have hjetale : ∀ i : I, Etale ((BigFppfOver.toScheme B S hS).map (j i)) := fun i ↦
    (hjmap i) ▸ inferInstance
  refine ⟨U, yoneda.map g ≫ p, I, W, j, Iso.refl _,
    MorphismProperty.comp_mem _ _ _ hgs hpS, MorphismProperty.comp_mem _ _ _ hge hpE,
    fun i ↦ i.1.2, fun i ↦ (Category.comp_id _).trans (hjmap i).symm, hjimm, fun i ↦ ?_,
    fun i ↦ ?_⟩
  · exact MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (j i)).2 (hjetale i))
      (MorphismProperty.comp_mem _ _ _ hge hpE)
  · obtain ⟨A, hAW⟩ := i.2
    refine ⟨A.1, A.2, fun y ↦ ?_⟩
    rw [hjmap, hmk, ← Category.assoc, Sigma.ι_comp_desc]
    exact hAW y.property

/-- An algebraic space over `S` has a surjective étale chart whose source is a disjoint union
of affine schemes, each mapping into an affine open of `S`. -/
@[stacks 03FX]
theorem IsAlgebraicSpace.exists_etale_surjective_coproduct_affine_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS)
      (f : yoneda.obj U ⟶ F)
      (I : Type u) (Y : I → Scheme.{u})
      (e : (∐ Y) ≅ (BigFppfOver.toScheme B S hS).obj U),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (∀ i, IsAffine (Y i)) ∧
      (∀ i, ∃ (V : S.Opens), IsAffineOpen V ∧
        ∀ y : Y i,
          (Sigma.ι Y i ≫ e.hom ≫ B.inclusion.map U.hom) y ∈ V) := by
  obtain ⟨U, f, I, W, j, e, hfS, hfE, hWaff, hje, -, -, hWover⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS F hF
  refine ⟨U, f, I, fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i), e, hfS, hfE, hWaff,
    fun i ↦ ?_⟩
  obtain ⟨A, hA, hAover⟩ := hWover i
  exact ⟨A, hA, fun y ↦ by rw [← Category.assoc, hje i]; exact hAover y⟩

/-- An algebraic space over `S` has a surjective étale chart whose underlying scheme is
separated. -/
@[stacks 03FX "the cover may be taken separated"]
theorem IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
      Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f := by
  obtain ⟨U, f, I, Y, e, hfS, hfE, hYaff, -⟩ :=
    IsAlgebraicSpace.exists_etale_surjective_coproduct_affine_cover B S hS F hF
  have := isSeparated_sigma_of_isAffine Y hYaff
  exact ⟨U, f, Scheme.IsSeparated.of_iso e, hfS, hfE⟩

end AlgebraicGeometry

end
