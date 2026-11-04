module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.DescentTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ConstructibleSets
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedImmersionAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The open immersion of Hilbert functors is quasi-compact over a qcqs test scheme

Let `π : X ⟶ Y` be an open immersion of algebraic spaces over an algebraic space `A`, with `Y`
separated over `A` and `π` quasi-compact. By Stacks 0DPE
(`AlgebraicGeometry.Space.isOpenImmersion_hilbertModelMap`) the induced morphism of Hilbert
functors `Hilb_{X/A} ⟶ Hilb_{Y/A}` is an open immersion. This file shows that its base change to
a quasi-compact quasi-separated scheme `H` of the site is a *quasi-compact* open of `H`.

A morphism `ξ : h_H ⟶ Hilb_{Y/A}` is a family `Z ⊆ Y_H`, and the inverse image of the range of
the induced morphism along `ξ` is the factorization locus of `Z ⟶ Y_H` through the open
immersion `X_H ⟶ Y_H` (`AlgebraicGeometry.Space.preimage_range_hilbertModelMap_eq`). Its point
set is the complement of the image in `H` of the points of `Z` not in `X_H`. The range of
`X_H ⟶ Y_H` is étale-locally constructible by Chevalley's theorem for algebraic spaces
(Stacks 0ECX), because `X_H ⟶ Y_H` is quasi-compact and locally of finite presentation; so are
its complement, the inverse image of that complement in `Z` (Stacks 0ECW), and the image of that
in `H` under the quasi-compact morphism of finite presentation `Z ⟶ H` (Stacks 0ECX again). On
the scheme `H` an étale-locally constructible set is locally constructible, hence constructible
since `H` is quasi-compact and quasi-separated, hence compact.

## Main results

* `AlgebraicGeometry.Space.preimage_range_hilbertModelMap_eq`: the inverse image of the range of
  the induced morphism along a scheme-valued point is the factorization locus.
* `AlgebraicGeometry.Space.exists_isPullback_compactSpace_hilbertModelMap`: the base change of
  the induced morphism to a quasi-compact quasi-separated scheme is a quasi-compact open of it.

## References

* [Stacks Project, Tag 0DPE](https://stacks.math.columbia.edu/tag/0DPE)
* [Stacks Project, Tag 0ECW](https://stacks.math.columbia.edu/tag/0ECW)
* [Stacks Project, Tag 0ECX](https://stacks.math.columbia.edu/tag/0ECX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

/-- A morphism factors through one leg of a pullback square exactly when its composite with the
opposite leg factors through the other. -/
private theorem CategoryTheory.IsPullback.exists_comp_snd_eq_iff {C : Type*} [Category C]
    {P Q D E W : C} {a : P ⟶ Q} {b : P ⟶ D} {c : Q ⟶ E} {d : D ⟶ E} (sq : IsPullback a b c d)
    (r : W ⟶ D) : (∃ k : W ⟶ P, k ≫ b = r) ↔ ∃ k : W ⟶ Q, k ≫ c = r ≫ d :=
  ⟨fun ⟨k, hk⟩ ↦ ⟨k ≫ a, by rw [Category.assoc, sq.w, ← Category.assoc, hk]⟩,
    fun ⟨k, hk⟩ ↦ ⟨sq.lift k r hk, sq.lift_snd _ _ _⟩⟩

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y A : AlgebraicSpaces B S hS} {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- Étale-local constructibility is stable under complements. -/
private theorem isEtaleLocallyConstructible_compl {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {E : Set (points B S hS W)} (hE : IsEtaleLocallyConstructible B S hS W E) :
    IsEtaleLocallyConstructible B S hS W Eᶜ := by
  intro U f hf
  rw [Set.preimage_compl]
  intro x
  obtain ⟨O, hxO, hO, hOE⟩ := hE U f hf x
  exact ⟨O, hxO, hO, by simpa using hOE.compl⟩

/-- Given `i : Xs ⟶ Ys` and `qq : Zs ⟶ T` quasi-compact and locally of finite presentation, and
any `r : Zs ⟶ Ys`, the complement of the image under `qq` of the points of `Zs` not mapping into
the range of `i` is étale-locally constructible. -/
private theorem isEtaleLocallyConstructible_compl_image_preimage_compl_range
    {Xs Ys Zs T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXs : IsAlgebraicSpace B S hS Xs) (hYs : IsAlgebraicSpace B S hS Ys)
    (hZs : IsAlgebraicSpace B S hS Zs) (hT : IsAlgebraicSpace B S hS T)
    (i : Xs ⟶ Ys) (hi : IsQuasiCompact B S hS i) (hil : IsLocallyOfFinitePresentation B S hS i)
    (r : Zs ⟶ Ys) (qq : Zs ⟶ T) (hq : IsQuasiCompact B S hS qq)
    (hql : IsLocallyOfFinitePresentation B S hS qq) :
    IsEtaleLocallyConstructible B S hS T
      (pointsMap B S hS Zs qq ''
        (pointsMap B S hS Zs r ⁻¹' (Set.range (pointsMap B S hS Xs i))ᶜ))ᶜ := by
  have hE : IsEtaleLocallyConstructible B S hS Ys (Set.range (pointsMap B S hS Xs i)) := by
    rw [← Set.image_univ]
    exact isEtaleLocallyConstructible_image B S hS hXs hYs i hi hil _
      (fun U f _ ↦ by rw [Set.preimage_univ]; exact IsLocallyConstructible.univ)
  exact isEtaleLocallyConstructible_compl <|
    isEtaleLocallyConstructible_image B S hS hZs hT qq hq hql _ <|
      isEtaleLocallyConstructible_preimage B S hS hZs hYs r _
        (isEtaleLocallyConstructible_compl hE)

/-- The inverse image of the range of the morphism of Hilbert functors induced by an open
immersion, along a scheme-valued point `q` of the model of `Hilb_{Y/A}`, is the factorization
locus of the closed subspace `Z ⊆ Y_T` carried by `q` through the open immersion `X_T ⟶ Y_T`,
relative to the structure morphism of `Z` over `T`. -/
theorem preimage_range_hilbertModelMap_eq (hπ : π ≫ bY = bX)
    (hopen : IsOpenImmersion B S hS π.hom) (hsep : IsSeparated B S hS bY.hom)
    (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY) {T : BigFppfOver B S hS}
    (q : yoneda.obj T ⟶ MY.presheaf) :
    (Subfunctor.range (hilbertModelMap hπ hopen hsep MX MY)).preimage q =
      factorizationLocus B S hS
        (schemeBaseChangeOfMap hπ
          (CostructuredArrow.mk (MY.familyEquiv T (yonedaEquiv q)).toBase))
        (MY.familyEquiv T (yonedaEquiv q)).family.Z.ι
        ((MY.familyEquiv T (yonedaEquiv q)).family.Z.ι ≫
          pullback.snd bY.hom
            (CostructuredArrow.mk (MY.familyEquiv T (yonedaEquiv q)).toBase).hom) := by
  set Z := MY.familyEquiv T (yonedaEquiv q)
  set Ta : SchemesOverPresheaf B S hS A := CostructuredArrow.mk Z.toBase
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hXT : IsAlgebraicSpace B S hS (schemeBaseChange bX Ta) :=
    isAlgebraicSpace_schemeBaseChange bX Ta
  have hYT : IsAlgebraicSpace B S hS (schemeBaseChange bY Ta) :=
    isAlgebraicSpace_schemeBaseChange bY Ta
  have hj := isOpenImmersion_schemeBaseChangeOfMap hπ hopen Ta
  have hqq : IsClosedMorphism B S hS (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom) :=
    isClosed_of_universallyClosed B S hS hT _ Z.family.proper.2.2
  ext U g
  have hqg : q.app U g = MY.presheaf.map (Quiver.Hom.op g) (yonedaEquiv q) := by
    rw [yonedaEquiv_apply]
    simpa using NatTrans.naturality_apply q (Quiver.Hom.op g) (𝟙 T)
  have hmono := mono_schemeBaseChangeOfMap hπ hopen
    (CostructuredArrow.mk (yoneda.map g ≫ Z.toBase))
  have hsq := (Subfunctor.isPullback_preimage
      (schemeBaseChangeMap bY (HilbertFamilyOver.restrict g Z.toBase))
      Z.family.Z).paste_vert
    (isPullback_schemeBaseChangeMap bY (HilbertFamilyOver.restrict g Z.toBase))
  set e := hsq.isoIsPullback _ _
    (IsPullback.of_hasPullback (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom) (yoneda.map g))
  have hefst : e.hom ≫ pullback.fst _ _ = _ := hsq.isoIsPullback_hom_fst _ _ _
  show q.app U g ∈ Set.range ((hilbertModelMap hπ hopen hsep MX MY).app U) ↔
    g ∈ (factorizationLocus B S hS (schemeBaseChangeOfMap hπ Ta) Z.family.Z.ι
      (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom)).obj U
  rw [hqg, mem_range_hilbertModelMap_iff, HilbertPresheafModel.familyEquiv_map]
  show Z.family.Z.preimage
        (schemeBaseChangeMap bY (HilbertFamilyOver.restrict g Z.toBase)) ≤
      Subfunctor.range (schemeBaseChangeOfMap hπ
        (CostructuredArrow.mk (yoneda.map g ≫ Z.toBase))) ↔
    g ∈ (factorizationLocus B S hS (schemeBaseChangeOfMap hπ Ta) Z.family.Z.ι
      (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom)).obj U
  rw [Subfunctor.mem_yoneda_iff,
    factorsThrough_factorizationLocus_iff B S hS hXT hYT Z.family.closed.1 hT hj
      Z.family.Z.ι hqq (isAlgebraicSpace_yoneda B S hS U.unop) (yoneda.map g),
    ← Subfunctor.factorsThrough_iff_le_range,
    (isPullback_schemeBaseChangeOfMap_comm hπ
      (HilbertFamilyOver.restrict g Z.toBase)).exists_comp_snd_eq_iff,
    ← Subfunctor.fromPreimage_ι]
  rw [← hefst, Category.assoc]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨e.inv ≫ k, by rw [Category.assoc, hk, Iso.inv_hom_id_assoc]⟩,
    fun ⟨k, hk⟩ ↦ ⟨e.hom ≫ k, by rw [Category.assoc, hk]⟩⟩

/-- The base change of the open immersion of Hilbert functors of Stacks 0DPE, induced by a
quasi-compact open immersion `π`, to a quasi-compact quasi-separated test scheme `H` is a
quasi-compact open of `H`: it is represented by an open immersion `V ⟶ H` of schemes with `V`
quasi-compact. -/
theorem exists_isPullback_compactSpace_hilbertModelMap (hπ : π ≫ bY = bX)
    (hopen : IsOpenImmersion B S hS π.hom) (hsep : IsSeparated B S hS bY.hom)
    (hqc : IsQuasiCompact B S hS π.hom)
    (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY)
    (H : BigFppfOver B S hS) [CompactSpace ((𝒯).obj H)] [QuasiSeparatedSpace ((𝒯).obj H)]
    (ξ : yoneda.obj H ⟶ MY.presheaf) :
    ∃ (V : BigFppfOver B S hS) (s : yoneda.obj V ⟶ MX.presheaf) (q : V ⟶ H),
      IsPullback s (yoneda.map q) (hilbertModelMap hπ hopen hsep MX MY) ξ ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map q) ∧ CompactSpace ((𝒯).obj V) := by
  have hO := isOpenImmersion_hilbertModelMap hπ hopen hsep MX MY
  have hmono := mono_hilbertModelMap hπ hopen hsep MX MY
  have hpb := hO.rep.isPullback ξ
  have hoq : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map (hO.rep.snd ξ)) :=
    hO.property_snd ξ
  refine ⟨hO.rep.pullback ξ, hO.rep.fst ξ, hO.rep.snd ξ, hpb, hoq, ?_⟩
  set q := hO.rep.snd ξ
  set Z := MY.familyEquiv H (yonedaEquiv ξ)
  set Ta : SchemesOverPresheaf B S hS A := CostructuredArrow.mk Z.toBase
  set i := schemeBaseChangeOfMap hπ Ta
  set r := Z.family.Z.ι
  set qq := Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom
  set L : Set (points B S hS (yoneda.obj H)) :=
    (pointsMap B S hS _ qq ''
      (pointsMap B S hS _ r ⁻¹' (Set.range (pointsMap B S hS _ i))ᶜ))ᶜ
  -- The point set of the open `V ⟶ H` is the complement of the image of the points of `Z`
  -- not in `X_H`.
  have hmq : Mono (yoneda.map q) := hpb.mono_snd_of_mono
  have hrange : Set.range (pointsMap B S hS _ (yoneda.map q)) = L := by
    rw [← range_pointsMap_ι_range B S hS (yoneda.map q),
      Subfunctor.range_eq_preimage_of_isPullback hpb.flip,
      preimage_range_hilbertModelMap_eq hπ hopen hsep MX MY ξ]
    exact range_pointsMap_ι_factorizationLocus B S hS i r qq
  -- Étale-local constructibility of `L`.
  have hEL : IsEtaleLocallyConstructible B S hS _ L :=
    isEtaleLocallyConstructible_compl_image_preimage_compl_range
      (isAlgebraicSpace_schemeBaseChange bX Ta) (isAlgebraicSpace_schemeBaseChange bY Ta)
      Z.family.closed.1 (isAlgebraicSpace_yoneda B S hS H) i
      (isQuasiCompact_of_isPullback B S hS (isPullback_schemeBaseChangeOfMap hπ Ta).flip hqc)
      (isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_of_isOpenImmersion B S hS (isOpenImmersion_schemeBaseChangeOfMap hπ hopen Ta)))
      r qq Z.family.finitePresentation.2.1 Z.family.finitePresentation.1
  have hLlc : IsLocallyConstructible L := by
    have h := hEL H (𝟙 _) (fun _ _ hφ ↦ by simpa using hφ)
    rwa [pointsMap_id, Set.preimage_id] at h
  -- Transport to the scheme `H`.
  set e := schemePointsHomeomorph B S hS H with he
  have hR : Set.range ((𝒯).map q).base = e.symm ⁻¹' L := by
    rw [← hrange, range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage B S hS q]
    ext x
    simp [he]
  refine isCompact_univ_iff.mp ?_
  rw [((𝒯).map q).isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ, hR]
  exact ConnectedComponentSection.isCompact_of_isConstructible
    ((e.symm.isLocallyConstructible_preimage_iff L).mpr hLlc).isConstructible

end AlgebraicGeometry.Space

end
