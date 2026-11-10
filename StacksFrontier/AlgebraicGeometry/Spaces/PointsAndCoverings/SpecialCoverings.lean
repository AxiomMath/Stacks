module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Special coverings of an algebraic space

An algebraic space over a scheme `S` can always be covered in a surjective étale way by a
disjoint union of affine schemes, each of whose summands maps into an affine open of `S`.
If the space is in addition quasi-compact, finitely many summands suffice and their
disjoint union is affine, so a quasi-compact algebraic space is exactly one admitting a
surjective étale morphism from an affine scheme.

## Main results

* `AlgebraicGeometry.Space.exists_etale_surjective_coproduct_affine_cover`: the affine
  summands, their disjoint union, and the surjective étale morphism to the space.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`:
  quasi-compactness is equivalent to the existence of an affine surjective étale atlas.

## Implementation notes

The summands of the first result are indexed by the affine opens of a chosen atlas scheme
which are carried into an affine open of `S`; these cover the atlas because the affine opens
of a scheme form a basis of its topology, and the structure morphism is continuous. Their
disjoint union is expressed by an isomorphism of schemes with the atlas object's underlying
scheme rather than by an equality, since the object of the site is built from the coproduct.

Keeping the coproduct inside the chosen size-bounded category is the only point where the
site's cardinal cutoff enters: the index set injects into the affine opens of the atlas
scheme, so `AlgebraicGeometry.schemeSize_coproduct_le` bounds the coproduct's size by that
of the atlas. In the quasi-compact case the index set is finite, so the bound comes instead
from `AlgebraicGeometry.Scheme.size_sigmaObj_lt`, and the disjoint union of finitely many
affine schemes is affine.

Étaleness and surjectivity of the resulting morphism of the site are obtained from the
corresponding scheme properties through `CategoryTheory.MorphismProperty.presheaf`; the
closure properties those need are supplied by
`StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties`.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A coproduct of étale morphisms into a scheme is étale. -/
private theorem etale_sigmaDesc {I : Type u} {Y : I → Scheme.{u}} {X : Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i)] : Etale (Sigma.desc f) := by
  have : HasRingHomProperty @Etale RingHom.Etale := inferInstance
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance

/-- A morphism of the big site whose underlying scheme morphism satisfies a base-change-stable
property `P` has the corresponding relative property after applying `yoneda`. -/
private theorem presheaf_yoneda_map_of_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {U V : BigFppfOver B S hS} (g : U ⟶ V) {a : (BigFppfOver.toScheme B S hS).obj U ⟶
      (BigFppfOver.toScheme B S hS).obj V} (hga : (BigFppfOver.toScheme B S hS).map g = a)
    (h : P a) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map g) := by
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  exact (MorphismProperty.relative_map_iff).2 (show P _ from hga ▸ h)

/-- An algebraic space has a surjective étale atlas which is a disjoint union of affine schemes,
each mapping into an affine open of the base. -/
@[stacks 03FX]
theorem exists_etale_surjective_coproduct_affine_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
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
  obtain ⟨V, p, hpS, hpE⟩ := hF.exists_atlas
  let X : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj V
  let q : X ⟶ S := B.inclusion.map V.hom
  let I : Type u := { A : X.affineOpens // ∃ W : S.affineOpens, A.1 ≤ q ⁻¹ᵁ W.1 }
  let Y : I → Scheme.{u} := fun i ↦ (i.1.1 : X.Opens).toScheme
  have hcover : (⨆ i : I, (i.1.1 : X.Opens)) = ⊤ := by
    apply eq_top_iff.mpr
    intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (a := q x) (Set.mem_univ _) isOpen_univ
    have hpre : IsOpen ((q ⁻¹ᵁ W : X.Opens) : Set X) := (q ⁻¹ᵁ W : X.Opens).2
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) hxW hpre
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨A, hA⟩, ⟨⟨W, hW⟩, hAW⟩⟩, hxA⟩
  let a : (∐ Y) ⟶ X := Sigma.desc fun i ↦ (i.1.1 : X.Opens).ι
  have hI : Cardinal.mk I ≤ X.size :=
    (Cardinal.mk_le_of_injective (f := fun i : I ↦ i.1)
      (fun _ _ hij ↦ Subtype.ext hij)).trans (Scheme.mk_affineOpens_le_size X)
  have hY : ∀ i, (Y i).size ≤ X.size := fun i ↦ Scheme.size_coe_opens_le X i.1.1
  have hZ : (∐ Y).size < B.cutoff :=
    (AlgebraicGeometry.schemeSize_coproduct_le Y X.size (Scheme.aleph0_le_size X)
      hI hY).trans_lt V.left.2
  let U : BigFppfOver B S hS :=
    Over.mk ((B.inclusion.preimage (X := B.obj hZ) (Y := V.left)
      (show B.inclusion.obj (B.obj hZ) ⟶ B.inclusion.obj V.left from a)) ≫ V.hom)
  let g : U ⟶ V := Over.homMk (B.inclusion.preimage a)
  have hasurj : Surjective a := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover.ge (by trivial : x ∈ (⊤ : X.Opens)))
    simp only [Set.mem_iUnion]
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  have haetale : Etale a := etale_sigmaDesc _
  let G := BigFppfOver.toScheme B S hS
  let e : (∐ Y) ≅ G.obj U := Iso.refl (∐ Y)
  let Ps := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) G
  let Pe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G
  let _ := surjective_isStableUnderComposition.{u}
  let _ := etale_isStableUnderComposition.{u}
  let _ : Ps.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : Pe.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : (MorphismProperty.presheaf Ps).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  let _ : (MorphismProperty.presheaf Pe).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hgs := presheaf_yoneda_map_of_map B S hS (P := @Surjective.{u}) g
    (B.inclusion.map_preimage (X := B.obj hZ) (Y := V.left) a) hasurj
  have hge := presheaf_yoneda_map_of_map B S hS (P := @Etale.{u}) g
    (B.inclusion.map_preimage (X := B.obj hZ) (Y := V.left) a) haetale
  refine ⟨U, yoneda.map g ≫ p, I, Y, e, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.comp_mem _ _ _ hgs hpS
  · exact MorphismProperty.comp_mem _ _ _ hge hpE
  · exact fun i ↦ i.1.2
  · intro i
    obtain ⟨W, hAW⟩ := i.2
    refine ⟨W.1, W.2, ?_⟩
    intro y
    have hmap : e.hom ≫ B.inclusion.map U.hom = a ≫ q := by
      change B.inclusion.map U.hom = a ≫ q
      change B.inclusion.map
          ((B.inclusion.preimage
            (show B.inclusion.obj (B.obj hZ) ⟶ B.inclusion.obj V.left from a)) ≫ V.hom) =
        a ≫ q
      rw [Functor.map_comp, B.inclusion.map_preimage]
    rw [hmap]
    change (Sigma.ι Y i ≫ a ≫ q) y ∈ W.1
    have hi : Sigma.ι Y i ≫ a = (i.1.1 : X.Opens).ι := by simp [a]
    rw [← Category.assoc, hi]
    change ((i.1.1 : X.Opens).ι ≫ q) y ∈ W.1
    exact hAW y.property

/-- A quasi-compact algebraic space has an affine, étale, surjective cover, and any algebraic
space with such a cover is quasi-compact. -/
@[stacks 03H6]
theorem isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hF : IsAlgebraicSpace B S hS F) :
    IsQuasiCompactSpace B S hS F ↔
      ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
          (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf f ∧
          IsEtale B S hS f := by
  constructor
  · rintro ⟨U, f, hcompact, hsurj, hetale⟩
    let G := BigFppfOver.toScheme B S hS
    let T : Scheme := G.obj U
    have _ : CompactSpace T := hcompact
    let 𝒰 : T.OpenCover := T.affineCover.finiteSubcover
    let A : Scheme := ∐ 𝒰.X
    let a : A ⟶ T := Sigma.desc 𝒰.f
    have hAsmall : A.size < B.cutoff :=
      Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 𝒰.X
        fun i => Scheme.size_lt_of_isOpenImmersion (𝒰.f i) U.left.property
    have haSurj : Surjective a := Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range
    have haEtale : Etale a := etale_sigmaDesc _
    let V : BigFppfOver B S hS :=
      Over.mk ((B.inclusion.preimage (X := B.obj hAsmall) (Y := U.left)
        (show B.inclusion.obj (B.obj hAsmall) ⟶ B.inclusion.obj U.left from a)) ≫ U.hom)
    let g : V ⟶ U := Over.homMk (B.inclusion.preimage
      (show B.inclusion.obj (B.obj hAsmall) ⟶ B.inclusion.obj U.left from a))
    let Ps := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) G
    let Pe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G
    let _ := surjective_isStableUnderComposition.{u}
    let _ := etale_isStableUnderComposition.{u}
    let _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
    let _ : Pe.IsStableUnderBaseChange :=
      MorphismProperty.inverseImage_isStableUnderBaseChange _ _
    let _ : Ps.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    let _ : (MorphismProperty.presheaf Ps).IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    have hga : Etale (G.map g) := by
      rwa [show G.map g = a from B.inclusion.map_preimage (X := B.obj hAsmall) (Y := U.left) a]
    have hgs := presheaf_yoneda_map_of_map B S hS (P := @Surjective.{u}) g
      (B.inclusion.map_preimage (X := B.obj hAsmall) (Y := U.left) a) haSurj
    have hcompEtale : IsEtale B S hS (yoneda.map g ≫ f) := by
      intro W φ hφ
      let j : W ⟶ V := yoneda.preimage φ
      have hφeq : yoneda.map j = φ := yoneda.map_preimage φ
      have hj : Etale (G.map j) := by
        apply (MorphismProperty.relative_map_iff (P := Pe) (F := yoneda)).1
        simpa only [hφeq] using hφ
      have hjg : Etale (G.map (j ≫ g)) := by
        rw [Functor.map_comp]
        exact Etale.etale_comp (G.map g) (f := G.map j)
      have hjg' : MorphismProperty.presheaf Pe (yoneda.map (j ≫ g)) :=
        (MorphismProperty.relative_map_iff (P := Pe) (F := yoneda)).2 hjg
      simpa only [hφeq, Functor.map_comp, Category.assoc] using
        hetale W (yoneda.map (j ≫ g)) hjg'
    have _ : Finite 𝒰.I₀ := inferInstance
    have _ : ∀ i, IsAffine (𝒰.X i) := fun i => inferInstance
    have _ : IsAffine A := inferInstance
    exact ⟨V, yoneda.map g ≫ f, (by change IsAffine A; infer_instance),
      MorphismProperty.comp_mem _ _ _ hgs hsurj, hcompEtale⟩
  · rintro ⟨U, f, hU, hsurj, hetale⟩
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    exact ⟨U, f, inferInstance, hsurj, hetale⟩

end AlgebraicGeometry.Space

end
