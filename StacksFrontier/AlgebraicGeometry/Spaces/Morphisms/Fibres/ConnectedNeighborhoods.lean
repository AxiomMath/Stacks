module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Connected fibres and étale neighborhoods of a geometric point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`ȳ` be a geometric point of `Y`. Connectedness of the fibre of `f` above a field-valued point
of `Y` is the connectedness of the point space of the presheaf fibre product of `f` with the
morphism represented by that point. This file assembles the machinery that compares the fibre
above `ȳ` itself with the fibres read inside the scheme-valued étale neighborhoods of `ȳ`.

Two mechanisms are developed. The first replaces an arbitrary field-valued point of a
represented presheaf by the residue field point at the underlying point of the representing
scheme: the replacement has the same class, and the morphism it represents is a quasi-compact
monomorphism, which is what the comparison of fibres needs. The second produces, from a finite
separable extension of the residue field at the image of the geometric point, an affine étale
neighborhood realizing that extension, lifts the geometric point into it, and places the
resulting scheme in the site; this turns a statement about all scheme-valued étale
neighborhoods into a statement about all finite separable extensions of one residue field.

## Main definitions

* `AlgebraicGeometry.Space.ConnectedPoints`: the point space of a presheaf is connected.
* `AlgebraicGeometry.Space.ConnectedPullback`: the fibre of a morphism above a morphism out of
  a representable presheaf has connected point space.
* `AlgebraicGeometry.Space.schemeResidueFieldPoint`: the residue field point of a represented
  presheaf at a point of the representing scheme.
* `AlgebraicGeometry.Space.liftedPoint`: the chosen lift in an étale neighborhood, regarded as
  a field-valued point of the neighborhood.
* `AlgebraicGeometry.Space.representedResidueFieldPointInNeighborhood`: the residue field point
  of a scheme-valued étale neighborhood at the image of its chosen lift.

## Main results

* `AlgebraicGeometry.Space.fieldPoint_class_eq_schemeResidueFieldPoint`: a field-valued point of
  a represented presheaf has the same class as the residue field point below it.
* `AlgebraicGeometry.Space.representedResidueFieldPointInNeighborhood_qc_mono`: the morphism
  represented by that residue field point is a quasi-compact monomorphism.
* `AlgebraicGeometry.exists_etaleNeighborhood_residueField_extension_lift`: a finite separable
  extension of the residue field at the image of a geometric point is realized by an étale
  neighborhood into which the geometric point lifts.
* `AlgebraicGeometry.Space.exists_siteEtaleNeighborhood_residueField_extension_lift`: the
  neighborhood realizing a prescribed finite separable residue extension, together with the lift
  of the geometric point and the resulting scheme-valued étale neighborhood of the site.
* `AlgebraicGeometry.Space.connectedPullback_finite_residueExtension`: connectedness of the
  fibres in all scheme-valued étale neighborhoods gives connectedness of the fibre above the
  residue field point after any finite separable extension.

## References

* [Stacks Project, Tag 02LF](https://stacks.math.columbia.edu/tag/02LF)
* [Stacks Project, Tag 0A1A](https://stacks.math.columbia.edu/tag/0A1A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Limits

/-- Absorbing an isomorphism of the base into the first leg of a fibre product. -/
noncomputable def pullback_compIso_of_iso {C : Type u} [Category.{u} C] [HasPullbacks C]
    {F G H Z : C} (f : F ⟶ G) (e : G ≅ H) (g : Z ⟶ H) :
    pullback g (f ≫ e.hom) ≅ pullback (g ≫ e.inv) f := by
  let a : pullback g (f ≫ e.hom) ⟶ pullback (g ≫ e.inv) f :=
    pullback.lift (pullback.fst g (f ≫ e.hom)) (pullback.snd g (f ≫ e.hom)) (by
      have h := congrArg (fun k => k ≫ e.inv) (pullback.condition (f := g) (g := f ≫ e.hom))
      simpa [Category.assoc, e.hom_inv_id] using h)
  let b : pullback (g ≫ e.inv) f ⟶ pullback g (f ≫ e.hom) :=
    pullback.lift (pullback.fst (g ≫ e.inv) f) (pullback.snd (g ≫ e.inv) f) (by
      have h := congrArg (fun k => k ≫ e.hom) (pullback.condition (f := g ≫ e.inv) (g := f))
      simpa [Category.assoc, e.inv_hom_id] using h)
  refine ⟨a, b, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp [a, b]
    · simp [a, b]
  · apply pullback.hom_ext
    · simp [a, b]
    · simp [a, b]

end CategoryTheory.Limits

namespace AlgebraicGeometry



/-- A finite separable extension of the residue field at the image of a geometric point is
realized by an étale neighborhood into which the geometric point lifts. -/
@[ega "IV 18.8.6" "more general", sga "2 XIV 3.4" "partial"]
theorem exists_etaleNeighborhood_residueField_extension_lift {V : Scheme.{u}} (v : V)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ V) (hp : p default = v)
    (K : Type u) [Field K] [Algebra (V.residueField v) K]
    [Module.Finite (V.residueField v) K] [Algebra.IsSeparable (V.residueField v) K] :
    ∃ U : EtaleNeighborhood V v,
      letI := U.residueFieldMap.hom.toAlgebra
      Nonempty (U.scheme.residueField U.point ≃ₐ[V.residueField v] K) ∧
        ∃ l : Spec (.of Ω) ⟶ U.scheme, l ≫ U.toBase = p ∧ l default = U.point := by
  obtain ⟨U, he⟩ := exists_etaleNeighborhood_residueField_algEquiv V v K
  refine ⟨U, ?_⟩
  let := U.residueFieldMap.hom.toAlgebra
  exact ⟨he, Scheme.exists_fac_of_etale_of_isSepClosed U.toBase p U.point
    (by rw [U.map_point, hp])⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point space of a presheaf on the big fppf site of `S`, with the point topology of
Stacks 03BX, is connected. For an algebraic space this is connectedness in the sense of the
Stacks project. -/
abbrev ConnectedPoints (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  @ConnectedSpace (points B S hS F) (pointTopology B S hS F)

/-- The fibre of `f : X ⟶ Y` above a morphism `a` from a representable presheaf — the presheaf
fibre product of `f` and `a` — has connected point space. For `a` the morphism represented by a
field-valued point of `Y` this is the connectedness of the fibre of `f` above that point. -/
abbrev ConnectedPullback {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Y) : Prop :=
  ConnectedPoints B S hS (pullback f a)

/-- Connectedness of the point space is invariant under an isomorphism of presheaves. -/
theorem connectedSpace_of_presheafIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hconn : ConnectedPoints B S hS F) : ConnectedPoints B S hS G :=
  (pointsHomeomorphOfIso B S hS e).connectedSpace_iff.mp hconn

/-- The field-valued point of a represented presheaf given by the residue field at a point of
the representing scheme. -/
noncomputable def schemeResidueFieldPoint (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) : FieldValuedPoint B S hS (yoneda.obj U) := by
  let X := (BigFppfOver.toScheme B S hS).obj U
  let hx : B.Contains (Spec (.of (X.residueField x))) :=
    Scheme.size_lt_of_mono_quasiCompact (X.fromSpecResidueField x) U.left.property
  exact ⟨X.residueField x, hx, X.fromSpecResidueField x ≫ U.hom.1,
    residueFieldMap B S hS U x hx⟩

/-- A field-valued point of a represented presheaf dominates the residue field point at its
underlying scheme point. -/
theorem dominates_schemeResidueFieldPoint (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    FieldValuedPoint.Dominates B S hS (yoneda.obj U) p
      (schemeResidueFieldPoint B S hS U (schemePoint B S hS U p)) := by
  let X := (BigFppfOver.toScheme B S hS).obj U
  let x := schemePoint B S hS U p
  let hx : B.Contains (Spec (.of (X.residueField x))) :=
    Scheme.size_lt_of_mono_quasiCompact (X.fromSpecResidueField x) U.left.property
  let R := residueFieldObject B S hS U x hx
  let rmap := residueFieldMap B S hS U x hx
  let pm : FieldValuedPoint.siteObject B S hS (yoneda.obj U) p ⟶ U := p.value
  let sp : Spec (.of p.carrier) ⟶ X := (BigFppfOver.toScheme B S hS).map pm
  let ep := X.SpecToEquivOfField p.carrier sp
  have hsp : Spec.map ep.2 ≫ X.fromSpecResidueField ep.1 = sp :=
    (X.SpecToEquivOfField p.carrier).symm_apply_apply sp
  have hpbase : sp ≫ U.hom.1 = p.toBase := by
    have h := congrArg B.inclusion.map p.value.w
    rwa [B.inclusion.map_comp] at h
  let e₀ : B.obj p.contained ⟶ B.obj hx := B.inclusion.preimage (Spec.map ep.2)
  have he₀ : e₀ ≫ R.hom = (FieldValuedPoint.siteObject B S hS (yoneda.obj U) p).hom := by
    apply B.inclusion.map_injective
    change B.inclusion.map e₀ ≫ B.inclusion.map R.hom =
      B.inclusion.map (FieldValuedPoint.siteObject B S hS (yoneda.obj U) p).hom
    rw [B.inclusion.map_preimage]
    change Spec.map ep.2 ≫ X.fromSpecResidueField ep.1 ≫ U.hom.1 = p.toBase
    rw [← Category.assoc, hsp, hpbase]
  let e : FieldValuedPoint.siteObject B S hS (yoneda.obj U) p ⟶ R := Over.homMk e₀ he₀
  refine ⟨e, ?_⟩
  change e ≫ rmap = p.value
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change B.inclusion.map e₀ ≫ B.inclusion.map (Over.Hom.left rmap) =
    B.inclusion.map (Over.Hom.left pm)
  rw [B.inclusion.map_preimage]
  change Spec.map ep.2 ≫ X.fromSpecResidueField x = sp
  exact hsp

/-- A field-valued point of a represented presheaf has the same class as the residue field point
at its underlying scheme point. -/
theorem fieldPoint_class_eq_schemeResidueFieldPoint (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    p.class B S hS (yoneda.obj U) =
      (schemeResidueFieldPoint B S hS U (schemePoint B S hS U p)).class B S hS
        (yoneda.obj U) :=
  FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
    ⟨p, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) p,
      dominates_schemeResidueFieldPoint B S hS U p⟩

/-- A morphism of the big fppf site over `S` whose underlying morphism of schemes is
quasi-compact induces a quasi-compact morphism of algebraic spaces. -/
theorem quasiCompact_schemeMap_isQuasiCompact {A D : BigFppfOver B S hS} (s : A ⟶ D)
    (h : QuasiCompact ((BigFppfOver.toScheme B S hS).map s)) :
    IsQuasiCompact B S hS (yoneda.map s) := by
  intro Z hZ hZqc g
  rcases hZqc with ⟨U, φ, hUc, hφSurj, hφEtale⟩
  let Q := BigFppfOver.toScheme B S hS
  let Dsp : AlgebraicSpaces B S hS := ⟨yoneda.obj D, isAlgebraicSpace_yoneda B S hS D⟩
  let Asp : AlgebraicSpaces B S hS := ⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩
  let Zsp : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let Usp : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let ssp : Asp ⟶ Dsp := ObjectProperty.homMk (yoneda.map s)
  let gsp : Zsp ⟶ Dsp := ObjectProperty.homMk g
  let φsp : Usp ⟶ Zsp := ObjectProperty.homMk φ
  let Psp := AlgebraicSpaces.fiberProduct B S hS gsp ssp
  let pZ : Psp ⟶ Zsp := ObjectProperty.homMk (pullback.fst g (yoneda.map s))
  let Ksp := AlgebraicSpaces.fiberProduct B S hS φsp pZ
  let kU : Ksp ⟶ Usp := ObjectProperty.homMk (pullback.fst φ pZ.hom)
  let kP : Ksp ⟶ Psp := ObjectProperty.homMk (pullback.snd φ pZ.hom)
  have hKpb := AlgebraicSpaces.isPullback_fiberProduct B S hS φsp pZ
  let QKSurj :=
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q).presheaf
  let : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Q).IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro X Y Y' T f' g f g' hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Surjective) (hs.map Q) hg
  let : QKSurj.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have hKetale : IsEtale B S hS kP.hom :=
    isEtale_of_isPullback B S hS kU kP φsp pZ hKpb hφEtale
  let m : U ⟶ D := yoneda.preimage (φ ≫ g)
  have hm : yoneda.map m = φ ≫ g := yoneda.map_preimage (φ ≫ g)
  let t := pullback.fst m s
  let P := pullback m s
  have hschemePB : IsPullback (yoneda.map (pullback.fst m s)) (yoneda.map (pullback.snd m s))
      (yoneda.map m) (yoneda.map s) :=
    Functor.map_isPullback yoneda (IsPullback.of_hasPullback m s)
  have hschemeCan : IsPullback (pullback.fst (yoneda.map m) (yoneda.map s))
      (pullback.snd (yoneda.map m) (yoneda.map s)) (yoneda.map m) (yoneda.map s) :=
    IsPullback.of_hasPullback _ _
  let eY : yoneda.obj P ≅ pullback (yoneda.map m) (yoneda.map s) :=
    hschemePB.isoIsPullback _ _ hschemeCan
  let eAssoc := pullbackRightPullbackFstIso g (yoneda.map s) φ
  have hcomm : φ ≫ g = yoneda.map m := hm.symm
  let eCompare : pullback (yoneda.map m) (yoneda.map s) ≅ pullback (φ ≫ g) (yoneda.map s) :=
    eqToIso (congrArg (fun k => pullback k (yoneda.map s)) hcomm.symm)
  let e : yoneda.obj P ≅ pullback φ (pullback.fst g (yoneda.map s)) :=
    eY ≪≫ eCompare ≪≫ eAssoc.symm
  let j : yoneda.obj P ⟶ pullback g (yoneda.map s) :=
    e.hom ≫ pullback.snd φ (pullback.fst g (yoneda.map s))
  let : QuasiCompact (Q.map t) := by
    have hmap : IsPullback (Q.map (pullback.fst m s)) (Q.map (pullback.snd m s)) (Q.map m)
        (Q.map s) := Functor.map_isPullback Q (IsPullback.of_hasPullback m s)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hmap.flip h
  have hPcompact : CompactSpace (Q.obj P) := QuasiCompact.compactSpace_of_compactSpace (Q.map t)
  have hjSurj : QKSurj j := by
    have hbase : QKSurj (pullback.snd φ (pullback.fst g (yoneda.map s))) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback φ (pullback.fst g (yoneda.map s))) hφSurj
    let : QKSurj.RespectsIso := inferInstance
    exact MorphismProperty.RespectsIso.precomp QKSurj e.hom _ hbase
  have hjEtale : IsEtale B S hS j := by
    intro T ψ hψ
    let QEtale :=
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q).presheaf
    let : QEtale.RespectsIso := inferInstance
    have hψ' : QEtale (ψ ≫ e.hom) := MorphismProperty.RespectsIso.postcomp QEtale e.hom ψ hψ
    exact hKetale T (ψ ≫ e.hom) hψ'
  exact ⟨P, j, hPcompact, hjSurj, hjEtale⟩

/-- The morphism represented by a residue field point of a represented presheaf is a
monomorphism. -/
theorem mono_schemeResidueFieldPoint (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    Mono (yonedaEquiv.symm (schemeResidueFieldPoint B S hS U x).value) := by
  let hx : B.Contains
      (Spec (.of (((BigFppfOver.toScheme B S hS).obj U).residueField x))) :=
    Scheme.size_lt_of_mono_quasiCompact
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x) U.left.property
  let rmap := residueFieldMap B S hS U x hx
  have : Mono ((BigFppfOver.toScheme B S hS).map rmap) := by
    change Mono (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x)
    infer_instance
  have : Mono rmap := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  change Mono (yoneda.map rmap)
  infer_instance

/-- The morphism represented by a residue field point of a represented presheaf is
quasi-compact. -/
theorem quasiCompact_schemeResidueFieldPoint (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    IsQuasiCompact B S hS (yonedaEquiv.symm (schemeResidueFieldPoint B S hS U x).value) := by
  let X := (BigFppfOver.toScheme B S hS).obj U
  let hx : B.Contains (Spec (.of (X.residueField x))) :=
    Scheme.size_lt_of_mono_quasiCompact (X.fromSpecResidueField x) U.left.property
  let rmap := residueFieldMap B S hS U x hx
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map rmap) := by
    change QuasiCompact (X.fromSpecResidueField x)
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro W hW
    exact (Set.toFinite (X.fromSpecResidueField x ⁻¹' (W : Set X))).isCompact
  exact quasiCompact_schemeMap_isQuasiCompact B S hS rmap hqc

/-- Composing with an isomorphism of the target preserves quasi-compactness of a morphism in
the sense of Stacks 03HE. -/
theorem IsQuasiCompact.postcomp_iso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (e : G ≅ H) (h : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (f ≫ e.hom) :=
  IsQuasiCompact.of_isPullback B S hS
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 F) (snd := f ≫ e.hom) (f := f) (g := e.inv)
      ⟨by simp⟩) h

/-- An étale chart of an étale neighborhood of a geometric point, together with a lift of the
chosen point, is again an étale neighborhood. -/
noncomputable def representedEtaleRefinement {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {y : GeometricPoint B S hS Y}
    (U : EtaleNeighborhood B S hS Y hY y) (V : BigFppfOver B S hS)
    (g : yoneda.obj V ⟶ U.space) (hg : IsEtale B S hS g)
    (q : (yoneda.obj V).obj (op y.val.siteObject))
    (hq : g.app (op y.val.siteObject) q = U.point) :
    EtaleNeighborhood B S hS Y hY y where
  space := yoneda.obj V
  isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS V
  toBase := g ≫ U.toBase
  etale_toBase := isEtale_comp B S hS hg U.etale_toBase
  point := q
  point_comp := by
    change U.toBase.app (op y.val.siteObject) (g.app (op y.val.siteObject) q) = y.val.value
    rw [hq]
    exact U.point_comp

/-- The lift in an étale neighborhood, regarded as a field-valued point of the neighborhood. -/
noncomputable def liftedPoint {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {y : GeometricPoint B S hS Y}
    (U : EtaleNeighborhood B S hS Y hY y) : FieldValuedPoint B S hS U.space where
  carrier := y.val.carrier
  field := y.val.field
  contained := y.val.contained
  toBase := y.val.toBase
  value := U.point


/-- For a scheme-valued étale neighborhood, the class of the lifted point is the class of the
residue field point at the scheme point below it, read back through the identification of the
neighborhood with a represented presheaf. -/
theorem represented_fieldPoint_class_eq_residueFieldPoint
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {y : GeometricPoint B S hS Y} (U : EtaleNeighborhood B S hS Y hY y)
    (V : BigFppfOver B S hS) (e : U.space ≅ yoneda.obj V) :
    pointsMap B S hS (yoneda.obj V) e.inv
        ((schemeResidueFieldPoint B S hS V (schemePoint B S hS V
          (FieldValuedPoint.map B S hS U.space e.hom (liftedPoint U)))).class B S hS
            (yoneda.obj V)) = (liftedPoint U).class B S hS U.space := by
  let p := FieldValuedPoint.map B S hS U.space e.hom (liftedPoint U)
  let q := schemeResidueFieldPoint B S hS V (schemePoint B S hS V p)
  have hp : p.class B S hS (yoneda.obj V) =
      pointsMap B S hS U.space e.hom (liftedPoint U).class := by
    rw [pointsMap_class]
  have hq : p.class B S hS (yoneda.obj V) = q.class B S hS (yoneda.obj V) :=
    fieldPoint_class_eq_schemeResidueFieldPoint B S hS V p
  calc
    pointsMap B S hS (yoneda.obj V) e.inv q.class =
        pointsMap B S hS (yoneda.obj V) e.inv p.class := by rw [← hq]
    _ = pointsMap B S hS U.space (e.hom ≫ e.inv) (liftedPoint U).class := by
          rw [hp]
          exact (pointsMap_comp_apply B S hS e.hom e.inv _).symm
    _ = pointsMap B S hS U.space (𝟙 U.space) (liftedPoint U).class := by rw [e.hom_inv_id]
    _ = (liftedPoint U).class B S hS U.space := by rw [pointsMap_id, id_eq]

/-- The residue field point of a scheme-valued étale neighborhood at the scheme point below its
chosen lift, read as a field-valued point of the neighborhood itself. -/
noncomputable def representedResidueFieldPointInNeighborhood
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {y : GeometricPoint B S hS Y} (U : EtaleNeighborhood B S hS Y hY y)
    (V : BigFppfOver B S hS) (e : U.space ≅ yoneda.obj V) :
    FieldValuedPoint B S hS U.space :=
  FieldValuedPoint.map B S hS (yoneda.obj V) e.inv
    (schemeResidueFieldPoint B S hS V
      (schemePoint B S hS V (FieldValuedPoint.map B S hS U.space e.hom (liftedPoint U))))

/-- The residue field point of a scheme-valued étale neighborhood has the same class as the
chosen lift. -/
theorem representedResidueFieldPointInNeighborhood_class
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {y : GeometricPoint B S hS Y} (U : EtaleNeighborhood B S hS Y hY y)
    (V : BigFppfOver B S hS) (e : U.space ≅ yoneda.obj V) :
    (representedResidueFieldPointInNeighborhood B S hS U V e).class B S hS U.space =
      (liftedPoint U).class B S hS U.space := by
  simpa only [representedResidueFieldPointInNeighborhood, pointsMap_class] using
    represented_fieldPoint_class_eq_residueFieldPoint B S hS U V e

/-- The morphism represented by the residue field point of a scheme-valued étale neighborhood is
a quasi-compact monomorphism. -/
theorem representedResidueFieldPointInNeighborhood_qc_mono
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {y : GeometricPoint B S hS Y} (U : EtaleNeighborhood B S hS Y hY y)
    (V : BigFppfOver B S hS) (e : U.space ≅ yoneda.obj V) :
    IsQuasiCompact B S hS
        (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U V e).value) ∧
      Mono (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U V e).value) := by
  let pV := FieldValuedPoint.map B S hS U.space e.hom (liftedPoint U)
  let x := schemePoint B S hS V pV
  let q := schemeResidueFieldPoint B S hS V x
  let rmap := residueFieldMap B S hS V x q.contained
  have hqmap : yonedaEquiv.symm q.value = yoneda.map rmap := by
    apply yonedaEquiv.injective
    rfl
  let p := representedResidueFieldPointInNeighborhood B S hS U V e
  have hmap : yonedaEquiv.symm p.value = yoneda.map rmap ≫ e.inv := by
    change yonedaEquiv.symm (e.inv.app (op q.siteObject) q.value) = _
    exact Eq.trans (yonedaEquiv_symm_naturality_right q.siteObject e.inv q.value).symm
      (congrArg (fun k => k ≫ e.inv) hqmap)
  have hqcR : IsQuasiCompact B S hS (yoneda.map rmap) := by
    rw [← hqmap]
    exact quasiCompact_schemeResidueFieldPoint B S hS V x
  have hqc : IsQuasiCompact B S hS (yonedaEquiv.symm p.value) := by
    rw [hmap]
    exact IsQuasiCompact.postcomp_iso B S hS (yoneda.map rmap) e.symm hqcR
  have hmR : Mono (yoneda.map rmap) := by
    rw [← hqmap]
    exact mono_schemeResidueFieldPoint B S hS V x
  have hm : Mono (yonedaEquiv.symm p.value) := by
    rw [hmap]
    exact mono_comp (yoneda.map rmap) e.inv
  exact ⟨hqc, hm⟩


/-- Connectedness of a fibre is unchanged by replacing the morphism out of a representable
presheaf by an isomorphic one. -/
theorem connectedPullback_of_iso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {T T' : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Y) (a' : yoneda.obj T' ⟶ Y) (e : T ≅ T')
    (he : yoneda.map e.hom ≫ a' = a) (hc : ConnectedPullback B S hS f a) :
    ConnectedPullback B S hS f a' := by
  let m := pullback.map f a f a' (𝟙 X) (yoneda.map e.hom) (𝟙 Y) (by simp) (by simpa using he.symm)
  exact connectedSpace_of_presheafIso B S hS (asIso m) hc

/-- A morphism of the big fppf site over `S` whose underlying morphism of schemes is étale is
étale as a morphism of algebraic spaces. -/
theorem etale_yoneda {W V : BigFppfOver B S hS} (m : W ⟶ V)
    (hm : Etale ((BigFppfOver.toScheme B S hS).map m)) : IsEtale B S hS (yoneda.map m) := by
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : P.IsStableUnderBaseChange := by
    constructor
    intro A D E T a b c d hp hb
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (hp.map (BigFppfOver.toScheme B S hS)) hb
  let : P.IsStableUnderComposition := by
    constructor
    intro A D E a b ha hb
    change Etale ((BigFppfOver.toScheme B S hS).map a) at ha
    change Etale ((BigFppfOver.toScheme B S hS).map b) at hb
    change Etale ((BigFppfOver.toScheme B S hS).map (a ≫ b))
    rw [Functor.map_comp]
    exact Etale.etale_comp _ _
  have hp : P.presheaf (yoneda.map m) :=
    (MorphismProperty.relative_map_iff (P := P) (F := yoneda)).mpr hm
  intro T φ hφ
  exact MorphismProperty.comp_mem P.presheaf _ _ hφ hp

/-- The morphism of the big fppf site over `S` underlying a geometric point of a represented
presheaf. -/
noncomputable def geometricPointRepresentableMap (V : BigFppfOver B S hS)
    (p : GeometricPoint B S hS (yoneda.obj V)) : p.val.siteObject ⟶ V :=
  yoneda.preimage
    ((CategoryTheory.yonedaEquiv (X := p.val.siteObject) (F := yoneda.obj V)).symm p.val.value)

/-- An affine étale neighborhood of a point of a scheme of the site lies in the site. -/
private theorem contains_etaleNeighborhood_of_isAffine {V : BigFppfOver B S hS}
    {v : (BigFppfOver.toScheme B S hS).obj V}
    (U₀ : AlgebraicGeometry.EtaleNeighborhood ((BigFppfOver.toScheme B S hS).obj V) v)
    [IsAffine U₀.scheme] :
    B.Contains U₀.scheme := by
  apply Scheme.size_lt_of_locallyOfFiniteType_of_affineCover B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit U₀.toBase (fun _ : PUnit => ⟨⊤, isAffineOpen_top U₀.scheme⟩)
  · simp
  · exact (Cardinal.mk_le_aleph0.trans
      (Scheme.aleph0_le_size ((BigFppfOver.toScheme B S hS).obj V))).trans
      (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
  · exact V.left.property

/-- A finite separable extension of the residue field at the image of a geometric point of a
represented presheaf is realized by an affine étale neighborhood which lies in the site, into
which the geometric point lifts, and which therefore gives a scheme-valued étale neighborhood of
the geometric point. -/
@[sga "2 XIV 3.4" "partial"]
theorem exists_siteEtaleNeighborhood_residueField_extension_lift (V : BigFppfOver B S hS)
    (p : GeometricPoint B S hS (yoneda.obj V)) (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (B.inclusion.map (Over.Hom.left (geometricPointRepresentableMap B S hS V p)))
      (IsLocalRing.closedPoint p.val.carrier) = v)
    (K : Type u) [Field K]
    [Algebra (((BigFppfOver.toScheme B S hS).obj V).residueField v) K]
    [Module.Finite (((BigFppfOver.toScheme B S hS).obj V).residueField v) K]
    [Algebra.IsSeparable (((BigFppfOver.toScheme B S hS).obj V).residueField v) K] :
    ∃ U₀ : AlgebraicGeometry.EtaleNeighborhood ((BigFppfOver.toScheme B S hS).obj V) v,
      letI := U₀.residueFieldMap.hom.toAlgebra
      Nonempty (U₀.scheme.residueField U₀.point ≃ₐ[
          ((BigFppfOver.toScheme B S hS).obj V).residueField v] K) ∧
        ∃ (_hU : B.Contains U₀.scheme) (l : Spec (.of p.val.carrier) ⟶ U₀.scheme),
          l ≫ U₀.toBase =
            B.inclusion.map (Over.Hom.left (geometricPointRepresentableMap B S hS V p)) ∧
          l default = U₀.point ∧
          ∃ (W : BigFppfOver B S hS) (_m : W ⟶ V)
            (U : EtaleNeighborhood B S hS (yoneda.obj V)
              (isAlgebraicSpace_yoneda B S hS V) p),
            Nonempty (U.space ≅ yoneda.obj W) := by
  let Vsch := (BigFppfOver.toScheme B S hS).obj V
  let : IsAlgClosed p.val.carrier := p.property
  let pSpec : Spec (.of p.val.carrier) ⟶ Vsch :=
    B.inclusion.map (Over.Hom.left (geometricPointRepresentableMap B S hS V p))
  have hpSpec : pSpec default = v :=
    (congrArg pSpec (Subsingleton.elim (default : Spec (.of p.val.carrier))
      (IsLocalRing.closedPoint p.val.carrier))).trans hv
  obtain ⟨U₀, hdata⟩ := exists_etaleNeighborhood_residueField_algEquiv_and_isAffine Vsch v K
  let : Algebra (Vsch.residueField v) (U₀.scheme.residueField U₀.point) :=
    U₀.residueFieldMap.hom.toAlgebra
  rcases hdata with ⟨he₀, hUaff⟩
  let : IsAffine U₀.scheme := hUaff
  let : IsSepClosed p.val.carrier := inferInstance
  have hp' : U₀.toBase U₀.point = pSpec default := by rw [U₀.map_point, hpSpec]
  obtain ⟨l, hl, hlpt⟩ :=
    Scheme.exists_fac_of_etale_of_isSepClosed U₀.toBase pSpec U₀.point hp'
  let : LocallyOfFiniteType U₀.toBase := inferInstance
  have hsize : U₀.scheme.size < B.cutoff := contains_etaleNeighborhood_of_isAffine B S hS U₀
  let Wsite := B.obj hsize
  let mleft : Wsite ⟶ V.left := B.inclusion.preimage (X := Wsite) (Y := V.left) U₀.toBase
  let W : BigFppfOver B S hS := Over.mk (mleft ≫ V.hom)
  let m : W ⟶ V := Over.homMk mleft
  let qleft : p.val.siteObject.left ⟶ W.left := B.inclusion.preimage l
  have hgeom : B.inclusion.map (Over.Hom.left (geometricPointRepresentableMap B S hS V p)) ≫
      B.inclusion.map V.hom = B.inclusion.map p.val.siteObject.hom := by
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map (Over.w (geometricPointRepresentableMap B S hS V p))
  have hqover : qleft ≫ W.hom = p.val.siteObject.hom := by
    apply B.inclusion.map_injective
    change B.inclusion.map qleft ≫ (B.inclusion.map mleft ≫ B.inclusion.map V.hom) =
      B.inclusion.map p.val.siteObject.hom
    rw [B.inclusion.map_preimage, B.inclusion.map_preimage]
    calc
      (l ≫ U₀.toBase) ≫ B.inclusion.map V.hom = pSpec ≫ B.inclusion.map V.hom := by rw [hl]
      _ = B.inclusion.map p.val.siteObject.hom := by simpa [pSpec] using hgeom
  let q : p.val.siteObject ⟶ W := Over.homMk qleft hqover
  let qval : (yoneda.obj W).obj (op p.val.siteObject) := yonedaEquiv (yoneda.map q)
  let U : EtaleNeighborhood B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) p :=
    { space := yoneda.obj W
      isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS W
      toBase := yoneda.map m
      etale_toBase := by
        apply etale_yoneda B S hS m
        change Etale (B.inclusion.map mleft)
        rw [B.inclusion.map_preimage]
        exact U₀.etale_toBase
      point := qval
      point_comp := by
        change yonedaEquiv (yoneda.map (q ≫ m)) = p.val.value
        rw [show q ≫ m = geometricPointRepresentableMap B S hS V p by
          apply Over.OverMorphism.ext
          apply B.inclusion.map_injective
          change B.inclusion.map qleft ≫ B.inclusion.map mleft =
            B.inclusion.map (Over.Hom.left (geometricPointRepresentableMap B S hS V p))
          rw [B.inclusion.map_preimage, B.inclusion.map_preimage]
          simpa [pSpec] using hl]
        simp [geometricPointRepresentableMap] }
  refine ⟨U₀, ?_⟩
  let := U₀.residueFieldMap.hom.toAlgebra
  exact ⟨he₀, ⟨hsize, l, hl, hlpt, ⟨W, m, U, ⟨Iso.refl _⟩⟩⟩⟩

/-- **The reduction to one residue field.** Suppose the fibre of `f` above the residue field
point of every scheme-valued étale neighborhood of the geometric point `y` is connected. Then,
for an étale chart `a` of the target through which `y` factors and any finite separable
extension `K` of the residue field at the image point, the fibre of `f` above the induced
`K`-valued point is connected. -/
theorem connectedPullback_finite_residueExtension
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (y : GeometricPoint B S hS Y)
    (hres : ∀ (U : EtaleNeighborhood B S hS Y hY y) (W : BigFppfOver B S hS)
      (e : U.space ≅ yoneda.obj W),
      ConnectedPullback B S hS f
        (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value ≫
          U.toBase))
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y) (ha : IsEtale B S hS a)
    (q : y.val.siteObject ⟶ V) (hq : a.app (op y.val.siteObject) q = y.val.value)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (BigFppfOver.toScheme B S hS).map q (IsLocalRing.closedPoint y.val.carrier) = v)
    (K : Type u) [Field K]
    [Algebra (((BigFppfOver.toScheme B S hS).obj V).residueField v) K]
    [FiniteDimensional (((BigFppfOver.toScheme B S hS).obj V).residueField v) K]
    [Algebra.IsSeparable (((BigFppfOver.toScheme B S hS).obj V).residueField v) K]
    (hK : B.Contains (Spec (.of K))) :
    let r := schemeResidueFieldPoint B S hS V v
    let g := r.siteObject.hom
    let h : B.obj hK ⟶ B.obj r.contained :=
      B.inclusion.preimage (Spec.map (CommRingCat.ofHom (algebraMap
        (((BigFppfOver.toScheme B S hS).obj V).residueField v) K)))
    ConnectedPullback B S hS f
      (yoneda.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ r.siteObject) ≫
        yoneda.map r.value ≫ a) := by
  let Vsch := (BigFppfOver.toScheme B S hS).obj V
  let pSpec : Spec (.of y.val.carrier) ⟶ Vsch := (BigFppfOver.toScheme B S hS).map q
  let : IsAlgClosed y.val.carrier := y.property
  obtain ⟨U₀, he₀, hUaff⟩ := exists_etaleNeighborhood_residueField_algEquiv_and_isAffine Vsch v K
  let := U₀.residueFieldMap.hom.toAlgebra
  obtain ⟨e₀⟩ := he₀
  let : IsAffine U₀.scheme := hUaff
  have hp' : U₀.toBase U₀.point = pSpec default := by
    rw [U₀.map_point]
    exact hv.symm.trans (congrArg pSpec (Subsingleton.elim _ _))
  obtain ⟨l, hl, hlpt⟩ :=
    Scheme.exists_fac_of_etale_of_isSepClosed U₀.toBase pSpec U₀.point hp'
  have hsize : B.Contains U₀.scheme := contains_etaleNeighborhood_of_isAffine B S hS U₀
  let mleft : B.obj hsize ⟶ V.left := ⟨U₀.toBase⟩
  let W : BigFppfOver B S hS := Over.mk (mleft ≫ V.hom)
  let m : W ⟶ V := Over.homMk mleft
  let qW : y.val.siteObject ⟶ W :=
    Over.homMk (⟨l⟩ : B.obj y.val.contained ⟶ B.obj hsize) (by
      apply B.inclusion.map_injective
      change l ≫ (U₀.toBase ≫ V.hom.hom) = y.val.toBase
      rw [← Category.assoc, hl]
      exact congrArg B.inclusion.map q.w)
  have hqm : qW ≫ m = q := Over.OverMorphism.ext (B.inclusion.map_injective hl)
  let U : EtaleNeighborhood B S hS Y hY y :=
    { space := yoneda.obj W
      isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS W
      toBase := yoneda.map m ≫ a
      etale_toBase := isEtale_comp B S hS (etale_yoneda B S hS m U₀.etale_toBase) ha
      point := qW
      point_comp := by
        change a.app _ (qW ≫ m) = y.val.value
        rw [hqm]
        exact hq }
  have hpoint : schemePoint B S hS W (liftedPoint U) = U₀.point := by
    change l (IsLocalRing.closedPoint y.val.carrier) = U₀.point
    exact (congrArg l (Subsingleton.elim _ _)).trans hlpt
  have hc := hres U W (Iso.refl _)
  change ConnectedPullback B S hS f
    (yoneda.map (schemeResidueFieldPoint B S hS W
      (schemePoint B S hS W (liftedPoint U))).value ≫ (yoneda.map m ≫ a)) at hc
  rw [hpoint] at hc
  let rW := schemeResidueFieldPoint B S hS W U₀.point
  let r := schemeResidueFieldPoint B S hS V v
  let g := r.siteObject.hom
  let h : B.obj hK ⟶ B.obj r.contained :=
    B.inclusion.preimage (Spec.map (CommRingCat.ofHom (algebraMap (Vsch.residueField v) K)))
  let RK : BigFppfOver B S hS := Over.mk (h ≫ g)
  let toR : RK ⟶ r.siteObject := Over.homMk h rfl
  have hr : Spec.map U₀.residueFieldMap ≫ Vsch.fromSpecResidueField v =
      U₀.scheme.fromSpecResidueField U₀.point ≫ U₀.toBase := by
    simp [AlgebraicGeometry.EtaleNeighborhood.residueFieldMap, Spec.map_comp,
      Category.assoc]
  have halg : U₀.residueFieldMap ≫ CommRingCat.ofHom e₀.toRingHom =
      CommRingCat.ofHom (algebraMap (Vsch.residueField v) K) := by
    ext z
    exact e₀.commutes z
  have hfac : Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
      U₀.scheme.fromSpecResidueField U₀.point ≫ U₀.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap (Vsch.residueField v) K)) ≫
        Vsch.fromSpecResidueField v := by
    rw [← hr, ← Spec.map_comp_assoc]
    exact congrArg (fun φ => Spec.map φ ≫ Vsch.fromSpecResidueField v) halg
  let i : B.obj hK ≅ B.obj rW.contained :=
    B.inclusion.preimageIso (Scheme.Spec.mapIso e₀.toRingEquiv.toCommRingCatIso.op)
  have hi : i.hom ≫ rW.value.left ≫ m.left = h ≫ r.value.left := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp]
    have hi_map : B.inclusion.map i.hom = Spec.map (CommRingCat.ofHom e₀.toRingHom) := by
      change B.inclusion.map (B.inclusion.preimage _) = _
      rw [B.inclusion.map_preimage]
      change (Scheme.Spec.mapIso e₀.toRingEquiv.toCommRingCatIso.op).hom = _
      rw [Functor.mapIso_hom, Scheme.Spec_map]
      rfl
    rw [hi_map]
    change Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
      U₀.scheme.fromSpecResidueField U₀.point ≫ U₀.toBase =
      B.inclusion.map h ≫ Vsch.fromSpecResidueField v
    rw [B.inclusion.map_preimage]
    exact hfac
  let e : RK ≅ rW.siteObject := Over.isoMk i (by
    change i.hom ≫ (rW.value.left ≫ (m.left ≫ V.hom)) = h ≫ (r.value.left ≫ V.hom)
    simpa only [Category.assoc] using congrArg (fun z => z ≫ V.hom) hi)
  have he : yoneda.map e.hom ≫ (yoneda.map rW.value ≫ (yoneda.map m ≫ a)) =
      yoneda.map toR ≫ yoneda.map r.value ≫ a := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 1
    exact congrArg yoneda.map (Over.OverMorphism.ext hi)
  exact connectedPullback_of_iso B S hS f (yoneda.map rW.value ≫ (yoneda.map m ≫ a))
    (yoneda.map toR ≫ yoneda.map r.value ≫ a) e.symm
    (by simpa using (congrArg (fun z => yoneda.map e.inv ≫ z) he).symm) hc

end AlgebraicGeometry.Space

end
