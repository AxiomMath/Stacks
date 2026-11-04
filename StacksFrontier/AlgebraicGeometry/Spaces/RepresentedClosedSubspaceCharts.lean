module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Closed subspaces of representable algebraic spaces and their representing schemes

A closed subspace `Z` of the algebraic space `h_T` represented by an object `T` of the big fppf
site over a scheme `S` is represented by a closed subscheme `Z₀ ⟶ T`
(`AlgebraicGeometry.Space.representedClosedHom`).  This file records how that construction
interacts with morphisms and with étale charts.

* A morphism of closed subspaces `W ⟶ Z` of `h_T` and `h_{T'}` lying over a morphism
  `g : T ⟶ T'` is induced by a unique morphism of representing schemes, which is an isomorphism
  when the morphism of subspaces is.
* For a morphism `l : T ⟶ T'` and a closed subspace `Y ⊆ h_{T'}`, the representing scheme of the
  inverse image `l⁻¹Y` is the fibre product `Y₀ ×_{T'} T` (Stacks 01JR for closed subschemes,
  read in the site).
* An étale chart `c : h_V ⟶ X` of an algebraic space, surjective on points, restricts on a
  closed subspace `W ⊆ X` to an étale chart of `W`, surjective on points, from the representing
  scheme of `c⁻¹W`.

## Main definitions

* `AlgebraicGeometry.Space.representedClosedLift`: the morphism of representing schemes induced
  by a morphism of closed subspaces.
* `AlgebraicGeometry.Space.representedPreimageProjection`: the chart of a closed subspace
  induced by a chart of the ambient space.

## Main results

* `AlgebraicGeometry.Space.representedClosedHom_comp_eq`: the square of closed immersions.
* `AlgebraicGeometry.Space.isIso_representedClosedLift`: the morphism of representing schemes
  of an isomorphism of closed subspaces is an isomorphism.
* `AlgebraicGeometry.Space.exists_isPullback_representedClosedHom`: the representing scheme of an
  inverse image is a fibre product.
* `AlgebraicGeometry.Space.isEtale_representedPreimageProjection` and
  `AlgebraicGeometry.Space.surjective_representedPreimageProjection`: the induced chart is
  étale and surjective.

## References

* [Stacks Project, Tag 01JR](https://stacks.math.columbia.edu/tag/01JR)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The closed immersion of the representing scheme of a closed subspace is a monomorphism of
the site: its Yoneda image is an isomorphism followed by the inclusion of a subfunctor. -/
theorem mono_representedClosedHom (T : BigFppfOver B S hS)
    (Z : ClosedSubspaces B S hS (yoneda.obj T)) : Mono (representedClosedHom B S hS T Z) := by
  have : IsIso (Z.2.2.rep.fst (idEtaleChart B S hS T).1.hom) :=
    isIso_representedClosedMap_hom B S hS T Z
  have : Mono (yoneda.map (representedClosedHom B S hS T Z)) := by
    rw [yoneda_map_representedClosedHom]
    exact mono_comp _ _
  exact yoneda.mono_of_mono_map inferInstance

section Lift

variable {T T' : BigFppfOver B S hS} (g : T ⟶ T') (W : ClosedSubspaces B S hS (yoneda.obj T))
  (Z : ClosedSubspaces B S hS (yoneda.obj T'))
  (f : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The morphism of representing schemes induced by a morphism of closed subspaces.**  For
closed subspaces `W ⊆ h_T` and `Z ⊆ h_{T'}` and a morphism `f : W ⟶ Z`, the morphism
`W₀ ⟶ Z₀` of their representing schemes whose Yoneda image is `f` read through the
identifications `h_{W₀} ≅ W` and `h_{Z₀} ≅ Z`. -/
noncomputable def representedClosedLift :
    representedClosedObj B S hS T W ⟶ representedClosedObj B S hS T' Z :=
  Yoneda.fullyFaithful.preimage
    ((representedClosedMap B S hS T W).hom ≫ f.hom ≫
      (@asIso _ _ _ _ (representedClosedMap B S hS T' Z).hom
        (isIso_representedClosedMap_hom B S hS T' Z)).inv)

/-- The Yoneda image of `AlgebraicGeometry.Space.representedClosedLift`, followed by the
identification of the target with `Z`, is the identification of the source with `W` followed by
the morphism of subspaces. -/
theorem yoneda_map_representedClosedLift_comp :
    yoneda.map (representedClosedLift B S hS W Z f) ≫ (representedClosedMap B S hS T' Z).hom =
      (representedClosedMap B S hS T W).hom ≫ f.hom := by
  rw [representedClosedLift, Functor.FullyFaithful.map_preimage]
  exact (Category.assoc _ _ _).trans (congrArg ((representedClosedMap B S hS T W).hom ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg (f.hom ≫ ·) (Iso.inv_hom_id _)).trans
      (Category.comp_id _))))

/-- **The square of closed immersions.**  If `f : W ⟶ Z` lies over `g : T ⟶ T'`, then the
closed immersions of the representing schemes form a commutative square with `g` and the
induced morphism `W₀ ⟶ Z₀`. -/
theorem representedClosedHom_comp_eq
    (sq : subspaceInclusion B S hS
        ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ W ≫
          representedSpaceMap B S hS g =
        f ≫ subspaceInclusion B S hS
          ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩ Z) :
    representedClosedHom B S hS T W ≫ g =
      representedClosedLift B S hS W Z f ≫ representedClosedHom B S hS T' Z := by
  apply yoneda.map_injective
  have hsq : W.1.ι ≫ yoneda.map g = f.hom ≫ Z.1.ι := congrArg (fun k => k.hom) sq
  rw [yoneda.map_comp, yoneda.map_comp, yoneda_map_representedClosedHom,
    yoneda_map_representedClosedHom, Category.assoc, hsq]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Z.1.ι) (yoneda_map_representedClosedLift_comp B S hS W Z f).symm).trans
      (Category.assoc _ _ _))

/-- **The morphism of representing schemes of an isomorphism of closed subspaces is an
isomorphism.** -/
theorem isIso_representedClosedLift (hf : IsIso f.hom) :
    IsIso (representedClosedLift B S hS W Z f) := by
  have : IsIso (yoneda.map (representedClosedLift B S hS W Z f)) := by
    rw [representedClosedLift, Functor.FullyFaithful.map_preimage]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_representedClosedMap_hom B S hS T W)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hf (Iso.isIso_inv _))
  exact Yoneda.fullyFaithful.isIso_of_isIso_map _

end Lift

section Pullback

/-- **The representing scheme of an inverse image is a fibre product.**  For a morphism
`l : T ⟶ T'` of the site and a closed subspace `Y ⊆ h_{T'}`, the representing scheme of a closed
subspace `F ⊆ h_T` equal to `l⁻¹Y` is the fibre product `Y₀ ×_{T'} T`, with its closed
immersion into `T` as second projection. -/
theorem exists_isPullback_representedClosedHom {T T' : BigFppfOver B S hS} (l : T ⟶ T')
    (Y : ClosedSubspaces B S hS (yoneda.obj T')) (F : ClosedSubspaces B S hS (yoneda.obj T))
    (hF : F.1 = Y.1.preimage (yoneda.map l)) :
    ∃ ρ : representedClosedObj B S hS T F ⟶ representedClosedObj B S hS T' Y,
      IsPullback ρ (representedClosedHom B S hS T F) (representedClosedHom B S hS T' Y) l := by
  obtain ⟨F, hFc⟩ := F
  dsimp only at hF
  subst hF
  let eF := @asIso _ _ _ _ (representedClosedMap B S hS T
    ⟨Y.1.preimage (yoneda.map l), hFc⟩).hom (isIso_representedClosedMap_hom B S hS T _)
  let eY := @asIso _ _ _ _ (representedClosedMap B S hS T' Y).hom
    (isIso_representedClosedMap_hom B S hS T' Y)
  refine ⟨Yoneda.fullyFaithful.preimage
    (eF.hom ≫ Y.1.fromPreimage (yoneda.map l) ≫ eY.inv), ?_⟩
  refine IsPullback.of_map_of_faithful (F := yoneda) ?_
  refine (Subfunctor.isPullback_preimage (yoneda.map l) Y.1).of_iso eF.symm eY.symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Functor.FullyFaithful.map_preimage, Iso.symm_hom, Iso.symm_hom]
    exact (eF.inv_hom_id_assoc _).symm
  · rw [yoneda_map_representedClosedHom, Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact (eF.inv_hom_id_assoc _).symm
  · rw [yoneda_map_representedClosedHom, Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact (eY.inv_hom_id_assoc _).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

end Pullback

section Chart

variable {X : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
  (c : (⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
    AlgebraicSpaces B S hS) ⟶ X) (W : ClosedSubspaces B S hS X.1)

/-- **The chart of a closed subspace induced by a chart of the ambient space.**  For a morphism
`c : h_V ⟶ X` and a closed subspace `W ⊆ X`, the composite of the identification of the
representing scheme of `c⁻¹W ⊆ h_V` with `c⁻¹W` and the projection `c⁻¹W ⟶ W`. -/
noncomputable def representedPreimageProjection :
    (⟨yoneda.obj (representedClosedObj B S hS V (preimageSubspace B S hS c W)),
        AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) :=
  representedClosedMap B S hS V (preimageSubspace B S hS c W) ≫ preimageProjection B S hS c W

/-- The induced chart of `W` lies over the chart `c` of `X`. -/
theorem representedSpaceMap_comp_eq_representedPreimageProjection_comp :
    representedSpaceMap B S hS (representedClosedHom B S hS V (preimageSubspace B S hS c W)) ≫
        c = representedPreimageProjection B S hS c W ≫ subspaceInclusion B S hS X W :=
  (congrArg (· ≫ c) (representedClosedMap_comp_subspaceInclusion B S hS V
    (preimageSubspace B S hS c W)).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (representedClosedMap B S hS V (preimageSubspace B S hS c W) ≫ ·)
        (conormalEtaleRestrictionSquare B S hS c W)).trans (Category.assoc _ _ _).symm))

/-- The chart of `W` induced by an étale chart of `X` is étale: it is an isomorphism followed by
a base change of the chart. -/
theorem isEtale_representedPreimageProjection (hc : IsEtale B S hS c.hom) :
    IsEtale B S hS (representedPreimageProjection B S hS c W).hom :=
  isEtale_comp B S hS (@isEtale_of_isIso B S hS _ _ (representedClosedMap B S hS V
    (preimageSubspace B S hS c W)).hom (isIso_representedClosedMap_hom B S hS V _))
    (isEtale_preimageProjection B S hS c hc W)

/-- A property of morphisms of presheaves, relative to representables, which holds for a chart `c`
holds for the induced chart of `W`. -/
private theorem presheaf_representedPreimageProjection
    (P : MorphismProperty (BigFppfOver B S hS)) (hc : P.presheaf c.hom) :
    P.presheaf (representedPreimageProjection B S hS c W).hom := by
  have hbc := (MorphismProperty.relative_isStableUnderBaseChange P (F := yoneda)).of_isPullback
    (Subfunctor.isPullback_preimage c.hom W.1).flip hc
  exact @MorphismProperty.RespectsIso.precomp _ _ _ _ _ _ _
    (representedClosedMap B S hS V (preimageSubspace B S hS c W)).hom
    (isIso_representedClosedMap_hom B S hS V _) _ hbc

/-- The chart of `W` induced by a chart of `X` which is étale after every representable base
change is so too: it is an isomorphism followed by a base change of the chart. -/
theorem etale_representedPreimageProjection
    (hc : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c.hom) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (representedPreimageProjection B S hS c W).hom :=
  presheaf_representedPreimageProjection B S hS c W _ hc

/-- The chart of `W` induced by a chart of `X` surjective on points is surjective on points: it is
an isomorphism followed by a base change of the chart. -/
theorem surjective_representedPreimageProjection
    (hc : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c.hom) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (representedPreimageProjection B S hS c W).hom :=
  presheaf_representedPreimageProjection B S hS c W _ hc

end Chart

section PreimageLift

variable {A A' P P' : AlgebraicSpaces B S hS} {c' : A' ⟶ A} {c : P' ⟶ P} {g : A ⟶ P}
  {g' : A' ⟶ P'} (hc : g' ≫ c = c' ≫ g) (Z : ClosedSubspaces B S hS A.1)
  (Y : ClosedSubspaces B S hS P.1)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
  (sq : subspaceInclusion B S hS A Z ≫ g = f ≫ subspaceInclusion B S hS P Y)

include sq in
/-- A closed subspace carried into `Y` by `g` lies in the inverse image `g⁻¹Y`. -/
theorem le_preimage_of_comp_eq : Z.1 ≤ Y.1.preimage g.hom := by
  intro T z hz
  have h₂ : g.hom.app T z = (f.hom.app T ⟨z, hz⟩).1 :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k => k.hom) sq) T) ⟨z, hz⟩
  show g.hom.app T z ∈ Y.1.obj T
  rw [h₂]
  exact (f.hom.app T ⟨z, hz⟩).2

/-- Pointwise, `g'` carries a point of `c'⁻¹Z` to the image under `c` of the point `f` gives. -/
private theorem app_comp_eq_of_mem_preimage (hc : g' ≫ c = c' ≫ g)
    (sq : subspaceInclusion B S hS A Z ≫ g = f ≫ subspaceInclusion B S hS P Y)
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : (Z.1.preimage c'.hom).toFunctor.obj T) :
    c.hom.app T (g'.hom.app T x.1) = (f.hom.app T ⟨_, x.2⟩).1 :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k => k.hom) hc) T) x.1).trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k => k.hom) sq) T) ⟨_, x.2⟩)

include hc sq in
/-- A morphism `g'` over `g` carries the inverse image `c'⁻¹Z` into the inverse image `c⁻¹Y`
whenever `g` carries `Z` into `Y`. -/
theorem range_le_preimage_of_comp_eq :
    Subfunctor.range ((Z.1.preimage c'.hom).ι ≫ g'.hom) ≤ Y.1.preimage c.hom := by
  rintro T _ ⟨x, rfl⟩
  show c.hom.app T (g'.hom.app T x.1) ∈ Y.1.obj T
  rw [app_comp_eq_of_mem_preimage B S hS Z Y f hc sq x]
  exact (f.hom.app T ⟨_, x.2⟩).2

/-- **The morphism of inverse images over a square.**  For a commutative square
`g' ≫ c = c' ≫ g` of algebraic spaces and a morphism `f : Z ⟶ Y` of closed subspaces lying over
`g`, the morphism `c'⁻¹Z ⟶ c⁻¹Y` induced by `g'`. -/
noncomputable def preimageLift :
    (⟨(preimageSubspace B S hS c' Z).1.toFunctor, (preimageSubspace B S hS c' Z).2.1⟩ :
      AlgebraicSpaces B S hS) ⟶
    (⟨(preimageSubspace B S hS c Y).1.toFunctor, (preimageSubspace B S hS c Y).2.1⟩ :
      AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (Subfunctor.lift ((Z.1.preimage c'.hom).ι ≫ g'.hom)
    (range_le_preimage_of_comp_eq B S hS hc Z Y f sq))

/-- `AlgebraicGeometry.Space.preimageLift` lies over `g'`. -/
theorem subspaceInclusion_comp_eq_preimageLift_comp :
    subspaceInclusion B S hS A' (preimageSubspace B S hS c' Z) ≫ g' =
      preimageLift B S hS hc Z Y f sq ≫ subspaceInclusion B S hS P' (preimageSubspace B S hS c Y) :=
  rfl

/-- `AlgebraicGeometry.Space.preimageLift` lies over `f`. -/
theorem preimageLift_comp_preimageProjection :
    preimageLift B S hS hc Z Y f sq ≫ preimageProjection B S hS c Y =
      preimageProjection B S hS c' Z ≫ f := by
  refine ObjectProperty.hom_ext _ ?_
  ext T x
  refine Subtype.ext ?_
  exact app_comp_eq_of_mem_preimage B S hS Z Y f hc sq x

end PreimageLift

section Copy

variable {A : AlgebraicSpaces B S hS} (F Z : ClosedSubspaces B S hS A.1) {V : BigFppfOver B S hS}
  (c : (⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
    AlgebraicSpaces B S hS) ⟶ A)

/-- **The copy of `Z` inside a chart of `F ⊇ Z` is the inverse image of `Z`.**  For closed
subspaces `Z ⊆ F` of `A` and a chart `c : h_V ⟶ A`, the inverse image of `Z ⊆ F` along the induced
chart `h_{F'} ⟶ F` of `F` (`F'` the representing scheme of `c⁻¹F`) is carried isomorphically
onto `c⁻¹Z` by the closed immersion `F' ⟶ V`. -/
theorem isIso_preimageLift_hom (hZF : Z.1 ≤ F.1) :
    IsIso (preimageLift B S hS
      (representedSpaceMap_comp_eq_representedPreimageProjection_comp B S hS c F)
      (preimageSubspace B S hS (subspaceInclusion B S hS A F) Z) Z
      (preimageProjection B S hS (subspaceInclusion B S hS A F) Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS A F) Z)).hom := by
  have : Mono (representedClosedHom B S hS V (preimageSubspace B S hS c F)) :=
    mono_representedClosedHom B S hS V _
  have := isIso_representedClosedMap_hom B S hS V (preimageSubspace B S hS c F)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun T => ?_
  refine (isIso_iff_bijective _).mpr ⟨fun x y hxy => ?_, fun z => ?_⟩
  · exact Subtype.ext ((cancel_mono
      (representedClosedHom B S hS V (preimageSubspace B S hS c F))).1 (congrArg Subtype.val hxy))
  · let zF : (preimageSubspace B S hS c F).1.toFunctor.obj T := ⟨z.1, hZF T z.2⟩
    let t := (inv (representedClosedMap B S hS V (preimageSubspace B S hS c F)).hom).app T zF
    have ht : (representedClosedMap B S hS V (preimageSubspace B S hS c F)).hom.app T t = zF :=
      ConcreteCategory.congr_hom (NatTrans.congr_app
        (IsIso.inv_hom_id (representedClosedMap B S hS V (preimageSubspace B S hS c F)).hom) T) zF
    have hv : (yoneda.map (representedClosedHom B S hS V (preimageSubspace B S hS c F))).app T t =
        z.1 := by
      rw [ConcreteCategory.congr_hom (NatTrans.congr_app
        (yoneda_map_representedClosedHom B S hS V (preimageSubspace B S hS c F)) T) t]
      exact congrArg Subtype.val ht
    refine ⟨⟨t, ?_⟩, Subtype.ext hv⟩
    show c.hom.app T ((representedClosedMap B S hS V (preimageSubspace B S hS c F)).hom.app T
      t).1 ∈ Z.1.obj T
    rw [ht]
    exact z.2

end Copy

end AlgebraicGeometry.Space

end
