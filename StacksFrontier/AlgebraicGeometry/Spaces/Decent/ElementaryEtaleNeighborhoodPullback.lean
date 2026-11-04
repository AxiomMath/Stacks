module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints

/-!
# Pulling an elementary étale neighborhood back along a morphism of spaces

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` with `Y` decent, let `q` be a point
of `Y` and let `E` be an elementary étale neighborhood of the image of `q` in `X`. Then `q` has
an elementary étale neighborhood `F` in `Y` admitting a morphism of schemes `F.scheme ⟶ E.scheme`
over `f`.

## Main results

* `AlgebraicGeometry.Space.exists_elementaryEtaleNeighborhood_pullback`: the elementary étale
  neighborhood of `q` lying over `E`.

## Implementation notes

The fibre product `V := yoneda.obj E.scheme ×_X Y` is an algebraic space whose projection to
`Y` is étale, hence `V` is decent. The monomorphic field-valued representative of `q` supplied
by decency of `Y` maps to `X` with the same class as the residue-field point of `E`, so it
factors through the latter and therefore lifts to a monomorphism `l` from its field spectrum to
`V`; write `v` for the point of `V` that `l` represents. An elementary étale neighborhood `G` of
`v` in `V` exists by Stacks 0BBP, and composing `G.toSpace` with the projection to `Y` gives the
required neighborhood of `q`.

Its only delicate field is the monomorphy of the residue-field point. The residue-field point of
`G` and the morphism `l` are two monomorphic field-valued representatives of `v`, hence differ by
an isomorphism of field spectra over `V` by Stacks 03E1; composing with the projection to `Y`
turns the residue-field point of `G` into an isomorphism followed by the monomorphic
representative of `q`, which is again a monomorphism.

The morphism to `E.scheme` is the Yoneda preimage of `G.toSpace` followed by the projection of
the fibre product to `yoneda.obj E.scheme`, and the square commutes because the fibre product
square does.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Precomposing the morphism of a field-valued point with a factorisation of its value. -/
private theorem yoneda_map_comp_fieldMorphism {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p r : FieldValuedPoint B S hS F} {e : p.siteObject B S hS F ⟶ r.siteObject B S hS F}
    (he : F.map e.op r.value = p.value) :
    yoneda.map e ≫ fieldMorphism B S hS F r = fieldMorphism B S hS F p := by
  show yoneda.map e ≫ yonedaEquiv.symm r.value = yonedaEquiv.symm p.value
  rw [yonedaEquiv_symm_naturality_left e F r.value, he]

/-- The base change of an elementary étale neighborhood, together with the fact that the
morphism of schemes carries the distinguished point to the distinguished point. -/
private theorem exists_pullback_neighborhood_aux
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYd : IsDecentSpace B S hS Y) (f : Y ⟶ X) (q : points B S hS Y)
    (E : ElementaryEtaleNeighborhood B S hS X hX (pointsMap B S hS Y f q)) :
    ∃ (F : ElementaryEtaleNeighborhood B S hS Y hY q) (j : F.scheme ⟶ E.scheme),
      yoneda.map j ≫ E.toSpace = F.toSpace ≫ f ∧ j.left.1 F.point = E.point := by
  classical
  have hEy : IsAlgebraicSpace B S hS (yoneda.obj E.scheme) :=
    isAlgebraicSpace_yoneda B S hS E.scheme
  have hV : IsAlgebraicSpace B S hS (pullback E.toSpace f) :=
    isAlgebraicSpace_pullback B S hS E.toSpace f hEy hY hX
  have hsnd : IsEtale B S hS (pullback.snd E.toSpace f) :=
    isEtale_pullback_snd B S hS hY hX hEy E.toSpace f E.etale_toSpace
  have hVd : IsDecentSpace B S hS (pullback E.toSpace f) :=
    isDecentSpace_of_isEtale B S hS (pullback.snd E.toSpace f) hV hY hsnd hYd
  -- The monomorphic field-valued representative of `q`.
  let pRep : FieldValuedPoint B S hS Y := (residueFieldRepresentative B S hS Y hYd q).1
  have hpMono : Mono (fieldMorphism B S hS Y pRep) :=
    (residueFieldRepresentative B S hS Y hYd q).2.2
  have hpClass : pRep.class B S hS Y = q := (residueFieldRepresentative B S hS Y hYd q).2.1
  -- The residue-field point of `E`, read in `X`.
  let q0 : FieldValuedPoint B S hS (yoneda.obj E.scheme) :=
    { carrier := E.scheme.left.1.residueField E.point
      contained := E.residueField_contained
      toBase := E.scheme.left.1.fromSpecResidueField E.point ≫ E.scheme.hom.1
      value := residueFieldMap B S hS E.scheme E.point E.residueField_contained }
  let q0X : FieldValuedPoint B S hS X :=
    FieldValuedPoint.map B S hS (yoneda.obj E.scheme) E.toSpace q0
  have hq0Xmor : fieldMorphism B S hS X q0X =
      yoneda.map (residueFieldMap B S hS E.scheme E.point E.residueField_contained) ≫
        E.toSpace :=
    fieldMorphism_map_yoneda B S hS X E.toSpace q0
  have hq0Xmono : Mono (fieldMorphism B S hS X q0X) := by
    rw [hq0Xmor]; exact E.mono_residueField
  have hq0Xclass : q0X.class B S hS X = pointsMap B S hS Y f q := E.map_point
  -- The image in `X` of the representative of `q`.
  let pX : FieldValuedPoint B S hS X := FieldValuedPoint.map B S hS Y f pRep
  have hpXmor : fieldMorphism B S hS X pX = fieldMorphism B S hS Y pRep ≫ f :=
    fieldMorphism_map B S hS Y f pRep
  have hpXclass : pX.class B S hS X = pointsMap B S hS Y f q := by
    rw [← hpClass]; rfl
  have hq0Xmono' : Mono (yonedaEquiv.symm q0X.value) := hq0Xmono
  obtain ⟨e, he, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS X hX
    q0X pX (hq0Xclass.trans hpXclass.symm)
  have heArrow : yoneda.map e ≫ fieldMorphism B S hS X q0X = fieldMorphism B S hS X pX :=
    yoneda_map_comp_fieldMorphism B S hS he
  -- The lift of that representative to the fibre product.
  have hcompat : yoneda.map
        (e ≫ residueFieldMap B S hS E.scheme E.point E.residueField_contained) ≫ E.toSpace =
      fieldMorphism B S hS Y pRep ≫ f :=
    (congrArg (fun k ↦ k ≫ E.toSpace) (yoneda.map_comp e
        (residueFieldMap B S hS E.scheme E.point E.residueField_contained))).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k ↦ yoneda.map e ≫ k) hq0Xmor.symm)) |>.trans
        (heArrow.trans hpXmor)
  let l : yoneda.obj (pRep.siteObject B S hS Y) ⟶ pullback E.toSpace f :=
    pullback.lift
      (yoneda.map (e ≫ residueFieldMap B S hS E.scheme E.point E.residueField_contained))
      (fieldMorphism B S hS Y pRep) hcompat
  have hlsnd : l ≫ pullback.snd E.toSpace f = fieldMorphism B S hS Y pRep :=
    pullback.lift_snd _ _ _
  have hlfst : l ≫ pullback.fst E.toSpace f =
      yoneda.map (e ≫ residueFieldMap B S hS E.scheme E.point E.residueField_contained) :=
    pullback.lift_fst _ _ _
  have hlmono : Mono l := by
    have : Mono (l ≫ pullback.snd E.toSpace f) := hlsnd ▸ hpMono
    exact mono_of_mono l (pullback.snd E.toSpace f)
  let tV : FieldValuedPoint B S hS (pullback E.toSpace f) :=
    { carrier := pRep.carrier
      field := pRep.field
      contained := pRep.contained
      toBase := pRep.toBase
      value := yonedaEquiv l }
  have htVmor : fieldMorphism B S hS (pullback E.toSpace f) tV = l :=
    Equiv.symm_apply_apply yonedaEquiv l
  have htVmono : Mono (fieldMorphism B S hS (pullback E.toSpace f) tV) := by
    rw [htVmor]; exact hlmono
  -- The point of the fibre product it represents, and its image in `Y`.
  have hvq : pointsMap B S hS (pullback E.toSpace f) (pullback.snd E.toSpace f)
      (tV.class B S hS (pullback E.toSpace f)) = q := by
    rw [pointsMap_class]
    refine Eq.trans ?_ hpClass
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y
      ⟨pRep, ⟨𝟙 (pRep.siteObject B S hS Y), ?_⟩,
        FieldValuedPoint.dominates_refl B S hS Y pRep⟩
    have hval : (FieldValuedPoint.map B S hS (pullback E.toSpace f)
        (pullback.snd E.toSpace f) tV).value = pRep.value := by
      show (pullback.snd E.toSpace f).app (Opposite.op (pRep.siteObject B S hS Y))
        (yonedaEquiv l) = pRep.value
      rw [← yonedaEquiv_comp l (pullback.snd E.toSpace f), hlsnd]
      exact yonedaEquiv_fieldMorphism B S hS Y pRep
    rw [hval]
    exact Functor.map_id_apply Y (Opposite.op (pRep.siteObject B S hS Y)) pRep.value
  -- An elementary étale neighborhood of that point in the fibre product.
  obtain ⟨G, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hV hVd
    (tV.class B S hS (pullback E.toSpace f))
  let g0 : FieldValuedPoint B S hS (yoneda.obj G.scheme) :=
    { carrier := G.scheme.left.1.residueField G.point
      contained := G.residueField_contained
      toBase := G.scheme.left.1.fromSpecResidueField G.point ≫ G.scheme.hom.1
      value := residueFieldMap B S hS G.scheme G.point G.residueField_contained }
  let uV : FieldValuedPoint B S hS (pullback E.toSpace f) :=
    FieldValuedPoint.map B S hS (yoneda.obj G.scheme) G.toSpace g0
  have huVmor : fieldMorphism B S hS (pullback E.toSpace f) uV =
      yoneda.map (residueFieldMap B S hS G.scheme G.point G.residueField_contained) ≫
        G.toSpace :=
    fieldMorphism_map_yoneda B S hS (pullback E.toSpace f) G.toSpace g0
  have huVmono : Mono (fieldMorphism B S hS (pullback E.toSpace f) uV) := by
    rw [huVmor]; exact G.mono_residueField
  have huVclass : uV.class B S hS (pullback E.toSpace f) =
    tV.class B S hS (pullback E.toSpace f) := G.map_point
  -- The two monomorphic representatives differ by an isomorphism of field spectra.
  have huVmono' : Mono (yonedaEquiv.symm uV.value) := huVmono
  have htVmono' : Mono (yonedaEquiv.symm tV.value) := htVmono
  obtain ⟨ε, hε⟩ := iso_of_mono_of_point_eq B S hS (pullback E.toSpace f) hV uV tV huVclass
  have hεArrow : yoneda.map ε.hom ≫ fieldMorphism B S hS (pullback E.toSpace f) tV =
      fieldMorphism B S hS (pullback E.toSpace f) uV :=
    yoneda_map_comp_fieldMorphism B S hS hε
  have hfac : fieldMorphism B S hS (pullback E.toSpace f) uV ≫ pullback.snd E.toSpace f =
      yoneda.map ε.hom ≫ fieldMorphism B S hS Y pRep := by
    rw [← hεArrow, Category.assoc, htVmor, hlsnd]
  have key : Mono (yoneda.map ε.hom ≫ fieldMorphism B S hS Y pRep) := by
    have : Mono (fieldMorphism B S hS Y pRep) := hpMono
    infer_instance
  have hcross : yoneda.map
        (residueFieldMap B S hS G.scheme G.point G.residueField_contained) ≫
        (G.toSpace ≫ pullback.snd E.toSpace f) =
      yoneda.map ε.hom ≫ fieldMorphism B S hS Y pRep := by
    rw [← Category.assoc, ← huVmor]
    exact hfac
  have hmono : Mono (yoneda.map
      (residueFieldMap B S hS G.scheme G.point G.residueField_contained) ≫
        (G.toSpace ≫ pullback.snd E.toSpace f)) := mono_of_eq_of_mono hcross key
  have hmap : pointsMap B S hS (yoneda.obj G.scheme)
      (G.toSpace ≫ pullback.snd E.toSpace f)
      (presheafPoint B S hS G.scheme G.point G.residueField_contained) = q :=
    (congrArg (pointsMap B S hS _ (pullback.snd E.toSpace f)) G.map_point).trans hvq
  -- The morphism to the given neighborhood, and the image of the distinguished point.
  have hεl : yoneda.map ε.hom ≫ l =
      yoneda.map (residueFieldMap B S hS G.scheme G.point G.residueField_contained) ≫
        G.toSpace := by
    rw [← htVmor, hεArrow, huVmor]
  have hyj : yoneda.map
        (residueFieldMap B S hS G.scheme G.point G.residueField_contained) ≫
        yoneda.map (yoneda.preimage (G.toSpace ≫ pullback.fst E.toSpace f)) =
      yoneda.map ε.hom ≫
        yoneda.map (e ≫ residueFieldMap B S hS E.scheme E.point E.residueField_contained) :=
    (congrArg (fun k ↦ yoneda.map (residueFieldMap B S hS G.scheme G.point
        G.residueField_contained) ≫ k) (Functor.map_preimage yoneda _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ pullback.fst E.toSpace f) hεl.symm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k ↦ yoneda.map ε.hom ≫ k) hlfst))))
  have hsite : residueFieldMap B S hS G.scheme G.point G.residueField_contained ≫
      yoneda.preimage (G.toSpace ≫ pullback.fst E.toSpace f) =
      ε.hom ≫ e ≫ residueFieldMap B S hS E.scheme E.point E.residueField_contained :=
    yoneda.map_injective
      ((yoneda.map_comp _ _).trans (hyj.trans (yoneda.map_comp _ _).symm))
  have hjpoint : (yoneda.preimage (G.toSpace ≫ pullback.fst E.toSpace f)).left.1 G.point =
      E.point := by
    have hG : (BigFppfOver.toScheme B S hS).map
        (residueFieldMap B S hS G.scheme G.point G.residueField_contained)
        (IsLocalRing.closedPoint (G.scheme.left.1.residueField G.point)) = G.point :=
      G.scheme.left.1.fromSpecResidueField_apply G.point _
    have hE : ∀ z, (BigFppfOver.toScheme B S hS).map
        (residueFieldMap B S hS E.scheme E.point E.residueField_contained) z = E.point :=
      fun z ↦ E.scheme.left.1.fromSpecResidueField_apply E.point z
    have happ : ∀ {U V W : BigFppfOver B S hS} (a : U ⟶ V) (b : V ⟶ W)
        (z : (BigFppfOver.toScheme B S hS).obj U),
        (BigFppfOver.toScheme B S hS).map (a ≫ b) z =
          (BigFppfOver.toScheme B S hS).map b ((BigFppfOver.toScheme B S hS).map a z) := by
      intro U V W a b z
      rw [Functor.map_comp]
      exact Scheme.Hom.comp_apply _ _ z
    have h := congrArg (fun k : residueFieldObject B S hS G.scheme G.point
        G.residueField_contained ⟶ E.scheme ↦ (BigFppfOver.toScheme B S hS).map k
          (IsLocalRing.closedPoint (G.scheme.left.1.residueField G.point))) hsite
    exact ((happ _ _ _).trans (congrArg (fun z ↦ (BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (G.toSpace ≫ pullback.fst E.toSpace f)) z) hG)).symm.trans
        (h.trans ((happ _ _ _).trans ((happ _ _ _).trans (hE _))))
  refine ⟨{ scheme := G.scheme
            point := G.point
            residueField_contained := G.residueField_contained
            toSpace := G.toSpace ≫ pullback.snd E.toSpace f
            etale_toSpace := isEtale_comp B S hS G.etale_toSpace hsnd
            map_point := hmap
            mono_residueField := hmono },
    yoneda.preimage (G.toSpace ≫ pullback.fst E.toSpace f), ?_, hjpoint⟩
  rw [Functor.map_preimage, Category.assoc, Category.assoc, pullback.condition]

/-- An elementary étale neighborhood base-changes to an elementary étale neighborhood. Let
`f : Y ⟶ X` be a morphism of algebraic spaces over `S` with `Y` decent, let `q` be a point of
`Y` and let `E` be an elementary étale neighborhood of the image of `q`. Then `q` has an
elementary étale neighborhood `F` together with a morphism `F.scheme ⟶ E.scheme` of the site
making the square with `f` commute. -/
theorem exists_elementaryEtaleNeighborhood_pullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYd : IsDecentSpace B S hS Y) (f : Y ⟶ X) (q : points B S hS Y)
    (E : ElementaryEtaleNeighborhood B S hS X hX (pointsMap B S hS Y f q)) :
    ∃ (F : ElementaryEtaleNeighborhood B S hS Y hY q) (j : F.scheme ⟶ E.scheme),
      yoneda.map j ≫ E.toSpace = F.toSpace ≫ f :=
  let ⟨F, j, hsq, _⟩ := exists_pullback_neighborhood_aux B S hS hX hY hYd f q E
  ⟨F, j, hsq⟩

/-- The neighborhood produced by
`AlgebraicGeometry.Space.exists_elementaryEtaleNeighborhood_pullback` carries its
distinguished point to the distinguished point of the given neighborhood, and the induced
homomorphism on the stalks of the two schemes at those points is a local homomorphism. -/
theorem exists_elementaryEtaleNeighborhood_pullback_isLocalHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYd : IsDecentSpace B S hS Y) (f : Y ⟶ X) (q : points B S hS Y)
    (E : ElementaryEtaleNeighborhood B S hS X hX (pointsMap B S hS Y f q)) :
    ∃ (F : ElementaryEtaleNeighborhood B S hS Y hY q) (j : F.scheme ⟶ E.scheme)
      (hj : j.left.1 F.point = E.point),
      yoneda.map j ≫ E.toSpace = F.toSpace ≫ f ∧
        IsLocalHom ((E.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
          j.left.1.stalkMap F.point).hom := by
  obtain ⟨F, j, hsq, hj⟩ := exists_pullback_neighborhood_aux B S hS hX hY hYd f q E
  exact ⟨F, j, hj, hsq, inferInstance⟩

end AlgebraicGeometry.Space

end
