module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertIsomorphismLocusPredicate
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubfunctorDerealization

/-!
# The isomorphism locus of the graph construction

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces which are of finite
presentation, flat and proper. For a test scheme `T` and a point `Y` of the Hilbert functor of the
ambient space `Z ×_Q X` over `T`, the locus in `T` over which the projection
`k = pr_Z|_Y : Y ⟶ Z_T` becomes an isomorphism is an open subscheme of `T`. This is
`AlgebraicGeometry.Space.HasIsomorphismLocus`: the open subspace of Stacks 05XD
(`AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isIso_baseChange`) for the triangle
`Y ⟶ Z_T ⟶ T`, represented by an open immersion of schemes as in Stacks 03KC
(`AlgebraicGeometry.Space.exists_siteOpenImmersion_of_isOpenImmersion`).

## Main results

* `AlgebraicGeometry.Space.isIso_baseChangeOverBase_iff_of_isPullback`: a morphism fitting into
  base-change squares of a triangle over the base is an isomorphism exactly when
  `AlgebraicGeometry.Space.baseChangeOverBase` is.
* `AlgebraicGeometry.Space.graphProjection_comp_mapFst`: the projection of the inverse image of a
  subfunctor of `(Z ×_Q X)_W` is the base change of the projection of that subfunctor.
* `AlgebraicGeometry.Space.graphRetraction_comp_mapFst_of_comparison`: the canonical retraction
  `AlgebraicGeometry.Space.graphRetraction` commutes with the comparison maps of two base changes.
* `AlgebraicGeometry.Space.hasIsomorphismLocus`: `AlgebraicGeometry.Space.HasIsomorphismLocus`,
  the openness of the isomorphism locus of the graph construction.

## References

* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search
for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_hilbertGraphIsomorphismLocus
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_hilbertGraphIsomorphismLocus
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_hilbertGraphIsomorphismLocus (B := B) (S := S) (hS := hS)).has_limit _

/-! ### Recognising a base change of a triangle over the base -/

section BaseChangeTriangle

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z X' Y' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A morphism which fits into base-change squares of a triangle over the base is an
isomorphism exactly when `AlgebraicGeometry.Space.baseChangeOverBase` is.** -/
theorem isIso_baseChangeOverBase_iff_of_isPullback
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p) (g : Z' ⟶ Z)
    (f' : X' ⟶ Y') (p' : X' ⟶ Z') (q' : Y' ⟶ Z') (hfq' : f' ≫ q' = p')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (hu : IsPullback u p' p g) (hv : IsPullback v q' q g)
    (hcomm : f' ≫ v = u ≫ f) :
    IsIso (baseChangeOverBase B S hS f p q hfq g) ↔ IsIso f' := by
  have hbcf : baseChangeOverBase B S hS f p q hfq g ≫ pullback.fst q g =
      pullback.fst p g ≫ f := pullback.lift_fst _ _ _
  have hbcs : baseChangeOverBase B S hS f p q hfq g ≫ pullback.snd q g =
      pullback.snd p g := pullback.lift_snd _ _ _
  have key : hu.isoPullback.hom ≫ baseChangeOverBase B S hS f p q hfq g =
      f' ≫ hv.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, hbcf, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_fst]
      exact hcomm.symm
    · simp only [Category.assoc, hbcs, IsPullback.isoPullback_hom_snd]
      exact hfq'.symm
  rw [(Iso.eq_inv_comp _).2 key, isIso_comp_left_iff, isIso_comp_right_iff]

end BaseChangeTriangle

/-! ### Base change of the graph projection -/

section GraphProjectionBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)

/-- **The canonical retraction of the ambient space of the graph construction commutes with base
change.** A comparison map `k : (Z ×_Q X)_{W'} ⟶ (Z ×_Q X)_W` of the two base changes of the
ambient space along `g : W' ⟶ W`, given by its two components, is carried by the retraction to the
comparison map of the two base changes of `Z`. -/
theorem graphRetraction_comp_mapFst_of_comparison {W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : W ⟶ Q)
    (g : W' ⟶ W)
    (k : pullback (pullback.fst z x ≫ z) (g ≫ a) ⟶ pullback (pullback.fst z x ≫ z) a)
    (hk₁ : k ≫ pullback.fst (pullback.fst z x ≫ z) a =
      pullback.fst (pullback.fst z x ≫ z) (g ≫ a))
    (hk₂ : k ≫ pullback.snd (pullback.fst z x ≫ z) a =
      pullback.snd (pullback.fst z x ≫ z) (g ≫ a) ≫ g) :
    graphRetraction z x (g ≫ a) ≫ pullback.mapFst g a z = k ≫ graphRetraction z x a := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.mapFst_fst, graphRetraction_fst_assoc,
      graphRetraction_fst]
    exact hk₂.symm
  · simp only [Category.assoc, pullback.mapFst_snd, graphRetraction_snd]
    rw [← Category.assoc, hk₁]

/-- **The projection of the inverse image of a subfunctor of `(Z ×_Q X)_W` is the base change of
the projection of that subfunctor.** -/
theorem graphProjection_comp_mapFst {W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Q)
    (g : W' ⟶ W)
    (k : pullback (pullback.fst z x ≫ z) (g ≫ a) ⟶ pullback (pullback.fst z x ≫ z) a)
    (hk₁ : k ≫ pullback.fst (pullback.fst z x ≫ z) a =
      pullback.fst (pullback.fst z x ≫ z) (g ≫ a))
    (hk₂ : k ≫ pullback.snd (pullback.fst z x ≫ z) a =
      pullback.snd (pullback.fst z x ≫ z) (g ≫ a) ≫ g)
    (V : Subfunctor (pullback (pullback.fst z x ≫ z) a)) :
    graphProjection z x (g ≫ a) (V.preimage k) ≫ pullback.mapFst g a z =
      V.fromPreimage k ≫ graphProjection z x a V := by
  rw [graphProjection, graphProjection, Category.assoc,
    graphRetraction_comp_mapFst_of_comparison z x a g k hk₁ hk₂, Subfunctor.fromPreimage_ι_assoc]

end GraphProjectionBaseChange

/-! ### The isomorphism locus -/

section IsomorphismLocus

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The isomorphism locus of the graph construction is open.** For two morphisms of algebraic
spaces to a common base which are both of finite presentation, flat and proper, the locus in a
test scheme over which a point of the Hilbert functor of the ambient space of the graph
construction has an isomorphism as its projection to the base change of `Z` is an open subscheme
of that test scheme. -/
theorem hasIsomorphismLocus : HasIsomorphismLocus B S hS := by
  intro Z X Q z x hZ hX hQ hzfp hzflat hzproper _hxfp _hxflat _hxproper T fam
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hq : IsProper B S hS (pullback.fst fam.toBase z) :=
    isProper_pullback_fst B S hS hZ hQ hT z fam.toBase hzproper
  obtain ⟨W, hW, hWprop⟩ := exists_isOpenSubspace_iff_isIso_baseChange B S hS
    fam.family.closed.1 (isAlgebraicSpace_pullback B S hS fam.toBase z hT hZ hQ) hT
    (graphProjection z x fam.toBase fam.family.Z)
    (fam.family.Z.ι ≫ pullback.snd (pullback.fst z x ≫ z) fam.toBase)
    (pullback.fst fam.toBase z) (graphProjection_comp_fst z x fam.toBase fam.family.Z)
    fam.family.finitePresentation.1 fam.family.flat fam.family.proper.2.2
    hq.2.1.1 (hzproper.2.2 (yoneda.obj T) hT fam.toBase) hq.1
  obtain ⟨V, s, e, hs, he⟩ := exists_siteOpenImmersion_of_isOpenImmersion B hS W hW.2
    (Iso.refl (yoneda.obj T))
  have he' : e.hom ≫ W.ι = yoneda.map s := by simpa using he
  refine ⟨V, s, hs, fun T' h => ?_⟩
  have hfac : (∃ t : T' ⟶ V, t ≫ s = h) ↔
      ∃ r : yoneda.obj T' ⟶ W.toFunctor, r ≫ W.ι = yoneda.map h := by
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨yoneda.map t ≫ e.hom, by rw [Category.assoc, he', ← Functor.map_comp]⟩
    · rintro ⟨r, hr⟩
      refine ⟨yoneda.preimage (r ≫ e.inv), yoneda.map_injective ?_⟩
      rwa [Functor.map_comp, Functor.map_preimage, Category.assoc, ← he',
        Iso.inv_hom_id_assoc]
  rw [hfac, hWprop (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T') (yoneda.map h)]
  exact isIso_baseChangeOverBase_iff_of_isPullback B S hS
    (graphProjection z x fam.toBase fam.family.Z)
    (fam.family.Z.ι ≫ pullback.snd (pullback.fst z x ≫ z) fam.toBase)
    (pullback.fst fam.toBase z) (graphProjection_comp_fst z x fam.toBase fam.family.Z)
    (yoneda.map h) (graphProjection z x (fam.baseChange h).toBase (fam.baseChange h).family.Z)
    ((fam.baseChange h).family.Z.ι ≫
      pullback.snd (pullback.fst z x ≫ z) (fam.baseChange h).toBase)
    (pullback.fst (fam.baseChange h).toBase z)
    (graphProjection_comp_fst z x (fam.baseChange h).toBase (fam.baseChange h).family.Z)
    (fam.family.Z.fromPreimage (schemeBaseChangeMap (graphAmbientMap B S hS z x hZ hX hQ)
      (HilbertFamilyOver.restrict h fam.toBase)))
    (pullback.mapFst (yoneda.map h) fam.toBase z)
    ((Subfunctor.isPullback_preimage (schemeBaseChangeMap
        (graphAmbientMap B S hS z x hZ hX hQ) (HilbertFamilyOver.restrict h fam.toBase))
        fam.family.Z).paste_vert
      (isPullback_schemeBaseChangeMap (graphAmbientMap B S hS z x hZ hX hQ)
        (HilbertFamilyOver.restrict h fam.toBase)))
    (pullback.isPullback_mapFst (yoneda.map h) fam.toBase z).flip
    (graphProjection_comp_mapFst z x fam.toBase (yoneda.map h) _
      (schemeBaseChangeMap_fst (graphAmbientMap B S hS z x hZ hX hQ)
        (HilbertFamilyOver.restrict h fam.toBase))
      (schemeBaseChangeMap_snd (graphAmbientMap B S hS z x hZ hX hQ)
        (HilbertFamilyOver.restrict h fam.toBase))
      fam.family.Z)

end IsomorphismLocus

end AlgebraicGeometry.Space

end
