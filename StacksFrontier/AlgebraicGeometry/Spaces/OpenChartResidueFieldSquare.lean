module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EqualDeltaDimension

/-!
# The residue field square on open charts

Let `f : X ⟶ Y` be a morphism of decent algebraic spaces over `S`, and let `α : h_{C_X} ⟶ X`
and `β : h_{C_Y} ⟶ Y` be open immersions out of representable presheaves through which `f` is
induced by a morphism `h : C_X ⟶ C_Y` of the site. At a point `u` of `C_X` lying over `x ∈ |X|`
the residue fields of the two spaces are the residue fields of the two schemes (an open
immersion is a monomorphism, Stacks 0EMW), and under these identifications the homomorphism of
residue fields induced by `f` is the one induced by the morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.exists_ringEquiv_residueFieldHom_comm_of_isOpenImmersion`: the
  commuting square of residue fields.
* `AlgebraicGeometry.Space.finrank_residueFieldHom_eq_residueDegree_of_isOpenImmersion`: the
  degree of the extension of residue fields of `f` at `x` is the residue degree of the morphism
  of schemes at `u`.

## Implementation notes

The square is extracted from the proof of
`AlgebraicGeometry.Space.finite_residueFieldHom_of_hasTranscendenceDegreeAt_zero`, where it is
used for finiteness only.

## References

* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The residue field square on open charts.** Let `f : X ⟶ Y` be a morphism of decent
algebraic spaces over `S`, induced on open charts `α : h_{C_X} ⟶ X` and `β : h_{C_Y} ⟶ Y` by a
morphism `h : C_X ⟶ C_Y` of the site, and let `u ∈ C_X` lie over `x ∈ |X|`. The residue fields
of `X` at `x` and of `Y` at `f x` are those of the two schemes at `u` and at `h u`, and the
homomorphism of residue fields induced by `f` corresponds to the one induced by `h`. -/
theorem exists_ringEquiv_residueFieldHom_comm_of_isOpenImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X)
    (CX CY : BigFppfOver B S hS) (α : yoneda.obj CX ⟶ X) (β : yoneda.obj CY ⟶ Y)
    (hα : IsOpenImmersion B S hS α) (hβ : IsOpenImmersion B S hS β) (h : CX ⟶ CY)
    (hcomm : yoneda.map h ≫ β = α ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj CX)
    (hu : pointsMap B S hS (yoneda.obj CX) α
      ((schemePointRepresentative B S hS CX u).class B S hS (yoneda.obj CX)) = x) :
    ∃ (φX : residueField B S hS X hXdec x ≃+*
        ((BigFppfOver.toScheme B S hS).obj CX).residueField u)
      (φY : residueField B S hS Y hYdec (pointsMap B S hS X f x) ≃+*
        ((BigFppfOver.toScheme B S hS).obj CY).residueField
          ((BigFppfOver.toScheme B S hS).map h u)),
      ∀ a, φX (residueFieldHom B S hS X Y hY hXdec hYdec f x a) =
        ((((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom) (φY a) := by
  classical
  set v := (BigFppfOver.toScheme B S hS).map h u with hvdef
  set qu := schemePointRepresentative B S hS CX u with hqudef
  set qv := schemePointRepresentative B S hS CY v with hqvdef
  have hvclass : pointsMap B S hS (yoneda.obj CX) (yoneda.map h)
      (qu.class B S hS (yoneda.obj CX)) = qv.class B S hS (yoneda.obj CY) := by
    refine injective_pointsToScheme B S hS CY ?_
    rw [pointsToScheme_pointsMap, hqudef, hqvdef, pointsToScheme_class,
      schemePointRepresentative_point B S hS CX u, pointsToScheme_class,
      schemePointRepresentative_point B S hS CY v]
  set qX := FieldValuedPoint.map B S hS (yoneda.obj CX) α qu with hqXdef
  set qY := FieldValuedPoint.map B S hS (yoneda.obj CY) β qv with hqYdef
  have hqXclass : qX.class B S hS X = x := hu
  have hqYclass : qY.class B S hS Y = pointsMap B S hS X f x := by
    have h1 : pointsMap B S hS X f x =
        pointsMap B S hS (yoneda.obj CX) (α ≫ f) (qu.class B S hS (yoneda.obj CX)) := by
      rw [pointsMap_comp, Function.comp_apply, hu]
    rw [h1, ← hcomm, pointsMap_comp, Function.comp_apply, hvclass]
    rfl
  have hmonoα : Mono α :=
    mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hα)
  have hmonoβ : Mono β :=
    mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hβ)
  have hmonoqu : Mono (yoneda.map qu.siteHom) := by
    rw [← fieldMorphism_yoneda B S hS qu, hqudef]
    exact mono_fieldMorphism_schemePointRepresentative B S hS CX u
  have hmonoqv : Mono (yoneda.map qv.siteHom) := by
    rw [← fieldMorphism_yoneda B S hS qv, hqvdef]
    exact mono_fieldMorphism_schemePointRepresentative B S hS CY v
  have hqXmor : fieldMorphism B S hS X qX = yoneda.map qu.siteHom ≫ α :=
    fieldMorphism_map_yoneda B S hS X α qu
  have hqYmor : fieldMorphism B S hS Y qY = yoneda.map qv.siteHom ≫ β :=
    fieldMorphism_map_yoneda B S hS Y β qv
  have hmonoqX : Mono (fieldMorphism B S hS X qX) := by
    rw [hqXmor]; exact mono_comp' hmonoqu hmonoα
  have hmonoqY : Mono (fieldMorphism B S hS Y qY) := by
    rw [hqYmor]; exact mono_comp' hmonoqv hmonoβ
  obtain ⟨φX, gX, hφXbij, hgXspec, hgXsq⟩ :=
    exists_bijective_residueFieldHom_of_mono B S hS hX hXdec x qX hqXclass hmonoqX
  obtain ⟨φY, gY, hφYbij, hgYspec, hgYsq⟩ :=
    exists_bijective_residueFieldHom_of_mono B S hS hY hYdec
      (pointsMap B S hS X f x) qY hqYclass hmonoqY
  have hmonoqv' : Mono (yonedaEquiv.symm qv.value) := by
    rw [show yonedaEquiv.symm qv.value = yoneda.map qv.siteHom from
      fieldMorphism_yoneda B S hS qv]
    exact hmonoqv
  obtain ⟨gh, hgh, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS
    (yoneda.obj CY) (isAlgebraicSpace_yoneda B S hS CY) qv
    (FieldValuedPoint.map B S hS (yoneda.obj CX) (yoneda.map h) qu) hvclass.symm
  have hghsq : gh ≫ qv.siteHom = qu.siteHom ≫ h := hgh
  have e1 : (BigFppfOver.toScheme B S hS).map qu.siteHom =
      ((BigFppfOver.toScheme B S hS).obj CX).fromSpecResidueField u :=
    toScheme_map_siteHom_schemePointRepresentative B S hS CX u
  have e2 : (BigFppfOver.toScheme B S hS).map qv.siteHom =
      ((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v :=
    toScheme_map_siteHom_schemePointRepresentative B S hS CY v
  have hghspec : B.inclusion.map gh.left =
      Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) := by
    have k1 : (BigFppfOver.toScheme B S hS).map gh ≫
          (BigFppfOver.toScheme B S hS).map qv.siteHom =
        (BigFppfOver.toScheme B S hS).map qu.siteHom ≫
          (BigFppfOver.toScheme B S hS).map h :=
      ((BigFppfOver.toScheme B S hS).map_comp gh qv.siteHom).symm.trans
        ((congrArg (fun k : qu.siteObject B S hS (yoneda.obj CX) ⟶ CY ↦
            (BigFppfOver.toScheme B S hS).map k) hghsq).trans
          ((BigFppfOver.toScheme B S hS).map_comp qu.siteHom h))
    have hcan : (BigFppfOver.toScheme B S hS).map gh ≫
          ((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v =
        ((BigFppfOver.toScheme B S hS).obj CX).fromSpecResidueField u ≫
          (BigFppfOver.toScheme B S hS).map h := by
      rw [← e2, ← e1]
      exact k1
    have hsqScheme :
        Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫
            ((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v =
          ((BigFppfOver.toScheme B S hS).obj CX).fromSpecResidueField u ≫
            (BigFppfOver.toScheme B S hS).map h :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ u
    change (BigFppfOver.toScheme B S hS).map gh = _
    exact (cancel_mono
      (((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v)).1
      (hcan.trans hsqScheme.symm)
  have hspec0 := residueFieldHom_spec B S hS X Y hY hXdec hYdec f x
  change ∃ g : _, _ ∧ _ at hspec0
  obtain ⟨g₀, hg₀spec, hg₀sq⟩ := hspec0
  have hmonoY : Mono (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) :=
    (residueFieldRepresentative B S hS Y hYdec (pointsMap B S hS X f x)).2.2
  have hsq1 : yoneda.map gX ≫ (yoneda.map g₀ ≫
        residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) =
      yoneda.map qu.siteHom ≫ (α ≫ f) :=
    (congrArg (fun k ↦ yoneda.map gX ≫ k) hg₀sq).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ f) hgXsq)).trans
        ((congrArg (fun k ↦ k ≫ f) hqXmor).trans (Category.assoc _ _ _)))
  have hsq2 : yoneda.map gh ≫ (yoneda.map gY ≫
        residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) =
      yoneda.map qu.siteHom ≫ (α ≫ f) :=
    (congrArg (fun k ↦ yoneda.map gh ≫ k) (hgYsq.trans hqYmor)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ β) (yoneda.map_comp gh qv.siteHom).symm).trans
          ((congrArg (fun k : qu.siteObject B S hS (yoneda.obj CX) ⟶ CY ↦
              yoneda.map k ≫ β) hghsq).trans
            ((congrArg (fun k ↦ k ≫ β) (yoneda.map_comp qu.siteHom h)).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun k ↦ yoneda.map qu.siteHom ≫ k) hcomm))))))
  have key : yoneda.map gX ≫ yoneda.map g₀ = yoneda.map gh ≫ yoneda.map gY :=
    (cancel_mono (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x))).1
      (((Category.assoc _ _ _).trans hsq1).trans ((Category.assoc _ _ _).trans hsq2).symm)
  have hm : gX ≫ g₀ = gh ≫ gY :=
    yoneda.map_injective
      ((yoneda.map_comp gX g₀).trans (key.trans (yoneda.map_comp gh gY).symm))
  have hA : B.inclusion.map gX.left ≫ B.inclusion.map g₀.left =
      B.inclusion.map gh.left ≫ B.inclusion.map gY.left := by
    have e := congrArg (fun k : qu.siteObject B S hS (yoneda.obj CX) ⟶
        (residueFieldRepresentative B S hS Y hYdec
          (pointsMap B S hS X f x)).1.siteObject B S hS Y ↦
      B.inclusion.map k.left) hm
    exact ((B.inclusion.map_comp gX.left g₀.left).symm.trans e).trans
      (B.inclusion.map_comp gh.left gY.left)
  have hA2 : Spec.map (CommRingCat.ofHom φX) ≫
        Spec.map (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x)) =
      Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫
        Spec.map (CommRingCat.ofHom φY) := by
    have eL : Spec.map (CommRingCat.ofHom φX) ≫
        Spec.map (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x)) =
        B.inclusion.map gX.left ≫ B.inclusion.map g₀.left := by
      rw [hgXspec, hg₀spec]
    have eR : Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫
        Spec.map (CommRingCat.ofHom φY) =
        B.inclusion.map gh.left ≫ B.inclusion.map gY.left :=
      (congrArg (fun k ↦ Spec.map
          ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫ k)
          hgYspec.symm).trans
        (congrArg (fun k ↦ k ≫ B.inclusion.map gY.left) hghspec.symm)
    exact (eL.trans hA).trans eR.symm
  have h0 : CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x) ≫
        CommRingCat.ofHom φX =
      CommRingCat.ofHom φY ≫
        (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u) :=
    Spec.map_injective
      ((Spec.map_comp _ _).trans (hA2.trans (Spec.map_comp _ _).symm))
  refine ⟨RingEquiv.ofBijective φX hφXbij, RingEquiv.ofBijective φY hφYbij, fun a ↦ ?_⟩
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h0) a

/-- **The degree of the residue field extension, read on open charts.** In the situation of
`AlgebraicGeometry.Space.exists_ringEquiv_residueFieldHom_comm_of_isOpenImmersion`, the degree of
the extension of residue fields induced by `f` at `x` is the residue degree at `u` of the
morphism of schemes induced by `h`. -/
theorem finrank_residueFieldHom_eq_residueDegree_of_isOpenImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X)
    (CX CY : BigFppfOver B S hS) (α : yoneda.obj CX ⟶ X) (β : yoneda.obj CY ⟶ Y)
    (hα : IsOpenImmersion B S hS α) (hβ : IsOpenImmersion B S hS β) (h : CX ⟶ CY)
    (hcomm : yoneda.map h ≫ β = α ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj CX)
    (hu : pointsMap B S hS (yoneda.obj CX) α
      ((schemePointRepresentative B S hS CX u).class B S hS (yoneda.obj CX)) = x) :
    letI := (residueFieldHom B S hS X Y hY hXdec hYdec f x).toAlgebra
    Module.finrank (residueField B S hS Y hYdec (pointsMap B S hS X f x))
        (residueField B S hS X hXdec x) =
      ((BigFppfOver.toScheme B S hS).map h).residueDegree u := by
  obtain ⟨φX, φY, hφ⟩ := exists_ringEquiv_residueFieldHom_comm_of_isOpenImmersion B S hS hX hY
    hXdec hYdec f x CX CY α β hα hβ h hcomm u hu
  let := (residueFieldHom B S hS X Y hY hXdec hYdec f x).toAlgebra
  let := ((((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom).toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv φY φX ?_
  ext a
  exact (hφ a).symm

end AlgebraicGeometry.Space

end
