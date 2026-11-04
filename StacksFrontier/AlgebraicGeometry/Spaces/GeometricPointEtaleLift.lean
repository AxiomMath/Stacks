module

public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Lifting geometric points along étale morphisms of algebraic spaces

Let `φ : U ⟶ X` be an étale morphism of algebraic spaces over `S` and let `x̄` be a geometric
point of `X`, that is a point of `X` with values in an algebraically closed field `k`. Every
point of `U` lying over the image of `x̄` in `|X|` carries a geometric point of `U` over `x̄`
with the same field `k`.

## Main results

* `AlgebraicGeometry.factor_through_coproduct_of_field`: a morphism from the spectrum of a
  field to a coproduct of schemes factors through one summand.
* `AlgebraicGeometry.etale_field_map_factors`: a field-valued point of a scheme étale over the
  spectrum of an algebraically closed field `k` factors through a section of the structure
  morphism over `Spec k`.
* `AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isEtale`: the lift of the geometric
  point over a prescribed point of the source, over the original field.

## Implementation notes

Equality of field-valued points after applying the morphism records equality of the actual
maps from the same field spectrum, not merely equality of their images in the point set. The
point of `X` below the given point of `U` is taken to be the image of the given geometric point.

## References

* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism from the spectrum of a field into a coproduct of schemes factors through one
of the summands. -/
theorem factor_through_coproduct_of_field
    {ι : Type u} [Small.{u} ι] (Y : ι → Scheme.{u})
    (L : Type u) [Field L] (g : Spec (.of L) ⟶ ∐ Y) :
    ∃ i, ∃ t : Spec (.of L) ⟶ Y i, t ≫ Sigma.ι Y i = g := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  let q : Spec (.of L) → ι := fun x => ((sigmaMk Y).symm (g x)).1
  have hfst : Continuous (fun p : (Σ i, Y i) => p.1) :=
    continuous_sigma fun _ => continuous_const
  have hq : Continuous q :=
    hfst.comp ((sigmaMk Y).symm.continuous.comp g.continuous)
  let x : Spec (.of L) := IsLocalRing.closedPoint L
  let i := q x
  have hrange : Set.range g ⊆ Set.range (Sigma.ι Y i) := by
    rintro z ⟨y, rfl⟩
    cases h : (sigmaMk Y).symm (g y) with
    | mk j y' =>
      have hj : j = i := (show q y = j by simp [q, h]).symm.trans
        (PreconnectedSpace.constant (inferInstance : PreconnectedSpace (Spec (.of L))) hq)
      have hy : (sigmaMk Y) ⟨j, y'⟩ = g y := by
        simpa [h] using (sigmaMk Y).apply_symm_apply (g y)
      subst j
      exact ⟨y', by simpa [sigmaMk_mk] using hy⟩
  exact ⟨i, IsOpenImmersion.lift (Sigma.ι Y i) g hrange,
    IsOpenImmersion.lift_fac (Sigma.ι Y i) g hrange⟩

/-- An étale scheme over the spectrum of an algebraically closed field `k` admits, through any
field-valued point of it, a section of its structure morphism over `Spec k` through which that
point factors. -/
theorem etale_field_map_factors
    (k : Type u) [Field k] [IsAlgClosed k]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) (hf : Etale f)
    (L : Type u) [Field L] (q : Spec (.of L) ⟶ V) :
    ∃ l : Spec (.of k) ⟶ V,
      l ≫ f = 𝟙 _ ∧ q = (q ≫ f) ≫ l := by
  let : Etale f := hf
  obtain ⟨ι, K, hField, hAlgebra, hFinite, hSeparable, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k f).mp hf
  let Y : ι → Scheme.{u} := fun i => Spec (.of (K i))
  have hsplit : e.hom ≫ Sigma.desc (fun i =>
      Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
    simpa [Y] using he
  obtain ⟨i, t, ht⟩ := factor_through_coproduct_of_field Y L (q ≫ e.hom)
  let : Field (K i) := hField i
  let : Algebra k (K i) := hAlgebra i
  let : Module.Finite k (K i) := hFinite i
  let : Algebra.IsSeparable k (K i) := hSeparable i
  let b : Spec (.of (K i)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (K i)))
  have hb : Function.Bijective (algebraMap k (K i)) :=
    IsSepClosed.algebraMap_bijective k (K i)
  let eK : k ≃+* K i := RingEquiv.ofBijective (algebraMap k (K i)) hb
  let eSpec : Spec (.of (K i)) ≅ Spec (.of k) :=
    Scheme.Spec.mapIso eK.toCommRingCatIso.op
  have hbIso : eSpec.hom = b := rfl
  have hsplitAt : q ≫ f = t ≫ b := by
    rw [← hsplit, ← Category.assoc, ← ht, Category.assoc, Sigma.ι_desc]
  let l : Spec (.of k) ⟶ V := eSpec.inv ≫ Sigma.ι Y i ≫ e.inv
  have hinv : e.inv ≫ f = Sigma.desc (fun j =>
      Spec.map (CommRingCat.ofHom (algebraMap k (K j)))) := by
    rw [← hsplit]
    simp
  have hl : l ≫ f = 𝟙 _ := by
    dsimp [l]
    rw [Category.assoc, Category.assoc, hinv, Sigma.ι_desc]
    exact eSpec.inv_hom_id
  have hle : l ≫ e.hom = eSpec.inv ≫ Sigma.ι Y i := by
    simp only [l, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hq : q = (q ≫ f) ≫ l := by
    apply (cancel_mono e.hom).1
    calc
      q ≫ e.hom = t ≫ Sigma.ι Y i := ht.symm
      _ = t ≫ (eSpec.hom ≫ eSpec.inv) ≫ Sigma.ι Y i := by
        rw [eSpec.hom_inv_id, Category.id_comp]
      _ = (t ≫ b) ≫ eSpec.inv ≫ Sigma.ι Y i := by
        rw [← hbIso]
        simp only [Category.assoc]
      _ = (q ≫ f) ≫ l ≫ e.hom := by rw [hle, hsplitAt]
  exact ⟨l, hl, hq⟩

namespace Space

/-- The scheme-level field-valued point of the scheme underlying a site object carried by a
field-valued point of the presheaf it represents. -/
private noncomputable def schemeFieldPointOfFieldPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj T)) :
    _root_.AlgebraicGeometry.FieldValuedPoint
      ((BigFppfOver.toScheme B S hS).obj T) where
  carrier := p.carrier
  map := by
    change (BigFppfOver.toScheme B S hS).obj p.siteObject ⟶ _
    exact (BigFppfOver.toScheme B S hS).map p.value

/-- Étaleness of the underlying scheme morphism is stable under base change of site morphisms. -/
private theorem inverseImage_etale_isStableUnderBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  let G := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan
      (Over.forget (B.obj hS)) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  let : PreservesLimitsOfShape WalkingCospan G :=
    CategoryTheory.Limits.comp_preservesLimitsOfShape _ _
  constructor
  intro V W W' T f g f' g' hf hg
  change _root_.AlgebraicGeometry.Etale (G.map g')
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))
    (hf.map G) hg

/-- A geometric point lifts along an étale morphism of algebraic spaces to any
specified point of the source above its image, without extending its field. -/
@[stacks 05VN]
theorem exists_geometricPoint_lift_of_isEtale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ)
    (xbar : GeometricPoint B S hS X)
    (u : points B S hS U)
    (hu : pointsMap B S hS U φ u = xbar.image) :
    ∃ ubar : GeometricPoint B S hS U,
      ubar.LiesOver u ∧
        FieldValuedPoint.map B S hS U φ ubar.val = xbar.val := by
  classical
  let Psize := schemeSizeBelow B.cutoff
  let : Psize.IsClosedUnderIsomorphisms := ⟨by
    intro V W e hV
    change V.size < B.cutoff at hV
    show W.size < B.cutoff
    rwa [← Scheme.size_congr e]⟩
  let : Psize.IsClosedUnderLimitsOfShape WalkingCospan := .mk' (by
    rintro _ ⟨F, hF⟩
    show (limit F).size < B.cutoff
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))
  let : HasPullbacks B.Schemes := inferInstance
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨A, aToU, I, Y, eA, haSurj, haEtale, _, _⟩ :=
    IsAlgebraicSpace.exists_etale_surjective_coproduct_affine_cover B S hS U hU
  obtain ⟨aPoint, haPoint⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS U hU A aToU).mp haSurj u
  have haEtale' : IsEtale B S hS aToU := by
    let G := BigFppfOver.toScheme B S hS
    let Pe := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) G
    have : Pe.IsStableUnderBaseChange := inverseImage_etale_isStableUnderBaseChange B S hS
    intro T ψ hψ
    let ρ : T ⟶ A := yoneda.preimage ψ
    have hρ : _root_.AlgebraicGeometry.Etale (G.map ρ) :=
      (MorphismProperty.relative_map_iff (F := yoneda) (P := Pe)).1 (by simpa [ρ] using hψ)
    simpa [ρ] using etale_comp_of_scheme B S hS ρ aToU hρ haEtale
  let f : yoneda.obj A ⟶ X := aToU ≫ φ
  have hf : IsEtale B S hS f := isEtale_comp B S hS haEtale' hφ
  let T₀ := xbar.val.siteObject B S hS X
  let zPointVal : FieldValuedPoint B S hS (yoneda.obj T₀) :=
    { carrier := xbar.val.carrier
      contained := xbar.val.contained
      toBase := xbar.val.toBase
      value := 𝟙 T₀ }
  let zbar : GeometricPoint B S hS (yoneda.obj T₀) :=
    ⟨zPointVal, xbar.property⟩
  let Z : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩
  let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Asp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩
  let z : yoneda.obj T₀ ⟶ X := yonedaEquiv.symm xbar.val.value
  let zsp : Z ⟶ Xsp := ObjectProperty.homMk z
  let fsp : Asp ⟶ Xsp := ObjectProperty.homMk f
  have hz : pointsMap B S hS (yoneda.obj T₀) z zbar.image = xbar.image := by
    rw [pointsMap_class]
    apply congrArg (FieldValuedPoint.class B S hS X)
    cases xbar with
    | mk p hp =>
      cases p with
      | mk carrier contained toBase value =>
        simp [FieldValuedPoint.map, z, zbar, zPointVal, T₀,
          FieldValuedPoint.siteObject]
  have hcomp : pointsMap B S hS (yoneda.obj A) f aPoint =
      pointsMap B S hS U φ
        (pointsMap B S hS (yoneda.obj A) aToU aPoint) :=
    pointsMap_comp_apply B S hS aToU φ aPoint
  have hpoint : pointsMap B S hS (yoneda.obj A) f aPoint =
      pointsMap B S hS (yoneda.obj T₀) z zbar.image := by
    rw [hcomp, haPoint, hu, hz]
  let P := AlgebraicSpaces.fiberProduct B S hS zsp fsp
  let pb := AlgebraicSpaces.isPullback_fiberProduct B S hS zsp fsp
  obtain ⟨w, hwZ, hwA⟩ :=
    exists_points_of_isPullback B S hS (IsPullback.of_hasPullback z f)
      zbar.image aPoint hpoint.symm
  have hrepF : yoneda.relativelyRepresentable f := hX.diagonal_representable.of_diag f
  have hrep : (pullback z f).IsRepresentable :=
    (yoneda_relativelyRepresentable_iff_pullback_representable f).mp hrepF T₀ xbar.val.value
  obtain ⟨V, ⟨repV⟩⟩ := hrep.has_representation
  let eRep : yoneda.obj V ≅ pullback z f := repV.toIso
  let : IsAlgClosed xbar.val.carrier := xbar.property
  let pA : P ⟶ Asp := ObjectProperty.homMk (pullback.snd zsp.hom fsp.hom)
  let pZ : P ⟶ Z := ObjectProperty.homMk (pullback.fst zsp.hom fsp.hom)
  have hpbFlip : IsPullback pA pZ fsp zsp := pb.flip
  have hfstEtale : IsEtale B S hS (pullback.fst z f) := by
    simpa [P, Z, Asp, Xsp, pZ, zsp, fsp, ObjectProperty.homMk,
      AlgebraicSpaces.fiberProduct] using isEtale_of_isPullback B S hS pA pZ fsp zsp hpbFlip hf
  have hRepEtale : IsEtale B S hS eRep.hom := isEtale_of_isIso B S hS eRep.hom
  have hCompEtale : IsEtale B S hS (eRep.hom ≫ pullback.fst z f) :=
    isEtale_comp B S hS hRepEtale hfstEtale
  let vToT0 : V ⟶ T₀ := yoneda.preimage (eRep.hom ≫ pullback.fst z f)
  let vToA : V ⟶ A := yoneda.preimage (eRep.hom ≫ pullback.snd z f)
  let G := BigFppfOver.toScheme B S hS
  let Pe := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) G
  have : Pe.IsStableUnderBaseChange := inverseImage_etale_isStableUnderBaseChange B S hS
  have hVEtale : _root_.AlgebraicGeometry.Etale (G.map vToT0) := by
    have hId : Pe.presheaf (𝟙 (yoneda.obj V)) := by
      have h : Pe (𝟙 V) := by
        show _root_.AlgebraicGeometry.Etale (G.map (𝟙 V))
        infer_instance
      simpa using (MorphismProperty.relative_map_iff (F := yoneda) (P := Pe)).2 h
    exact (MorphismProperty.relative_map_iff (F := yoneda) (P := Pe)).1
      (by simpa [vToT0] using hCompEtale V (𝟙 (yoneda.obj V)) hId)
  obtain ⟨pP, hpP⟩ : ∃ p : FieldValuedPoint B S hS (pullback z f),
      p.class B S hS (pullback z f) = w := Quot.exists_rep w
  let pV := FieldValuedPoint.map B S hS (pullback z f) eRep.inv pP
  let pVscheme := schemeFieldPointOfFieldPoint B S hS V pV
  let q : Spec (.of pV.carrier) ⟶ G.obj V := pVscheme.map
  obtain ⟨l, hl, hq⟩ := etale_field_map_factors xbar.val.carrier
    (G.map vToT0) hVEtale pV.carrier q
  let lInclusion : B.inclusion.obj T₀.left ⟶ B.inclusion.obj V.left := l
  change lInclusion ≫ B.inclusion.map vToT0.left = 𝟙 _ at hl
  have hleft : B.inclusion.preimage lInclusion ≫ vToT0.left = 𝟙 T₀.left := by
    apply B.inclusion.map_injective
    simpa only [Functor.map_comp, B.inclusion.map_preimage,
      B.inclusion.map_id] using hl
  let lOver : T₀ ⟶ V := Over.homMk (B.inclusion.preimage lInclusion) (by
    rw [← Over.w vToT0, ← Category.assoc, hleft, Category.id_comp])
  have hlOver : lOver ≫ vToT0 = 𝟙 T₀ := by
    apply Over.OverMorphism.ext
    simpa [lOver] using hleft
  let pLift : FieldValuedPoint B S hS (yoneda.obj V) :=
    { carrier := xbar.val.carrier
      contained := xbar.val.contained
      toBase := xbar.val.toBase
      value := lOver }
  let gOver : pV.siteObject B S hS (yoneda.obj V) ⟶ T₀ := pV.value ≫ vToT0
  have hpreL : (B.inclusion.preimage lInclusion).hom = l := by
    show B.inclusion.map (B.inclusion.preimage lInclusion) = l
    simpa [lInclusion] using B.inclusion.map_preimage lInclusion
  have hqOver : pV.value = gOver ≫ lOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    simpa [q, pVscheme, schemeFieldPointOfFieldPoint, G,
      gOver, lOver, lInclusion, Category.assoc,
      B.inclusion.map_preimage, hpreL] using hq
  have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj V) pV pLift := ⟨gOver, hqOver.symm⟩
  have hpClass : pV.class B S hS (yoneda.obj V) =
      pLift.class B S hS (yoneda.obj V) :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension
      B S hS (yoneda.obj V)
      ⟨pV, FieldValuedPoint.dominates_refl B S hS (yoneda.obj V) pV, hdom⟩
  let beta : yoneda.obj V ⟶ U := yoneda.map vToA ≫ aToU
  let ubarVal := FieldValuedPoint.map B S hS (yoneda.obj V) beta pLift
  let ubar : GeometricPoint B S hS U := ⟨ubarVal, xbar.property⟩
  have hpVclass : pV.class B S hS (yoneda.obj V) =
      pointsMap B S hS (pullback z f) eRep.inv (pP.class B S hS (pullback z f)) := by
    simp [pV]
  have hvA : yoneda.map vToA = eRep.hom ≫ pullback.snd z f := by
    simp [vToA]
  have heA : eRep.inv ≫ yoneda.map vToA = pullback.snd z f := by simp [hvA]
  have heABeta : eRep.inv ≫ beta = pullback.snd z f ≫ aToU := by
    dsimp [beta]
    rw [← Category.assoc, heA]
  have hclassU : pointsMap B S hS (yoneda.obj V) beta
      (pLift.class B S hS (yoneda.obj V)) =
      pointsMap B S hS (yoneda.obj A) aToU aPoint := by
    calc
      pointsMap B S hS (yoneda.obj V) beta
          (pLift.class B S hS (yoneda.obj V)) =
          pointsMap B S hS (yoneda.obj V) beta
            (pV.class B S hS (yoneda.obj V)) := by rw [hpClass]
      _ = pointsMap B S hS (pullback z f) (eRep.inv ≫ beta) (pP.class B S hS (pullback z f)) := by
          rw [hpVclass]
          exact (pointsMap_comp_apply B S hS eRep.inv beta (pP.class B S hS (pullback z f))).symm
      _ = pointsMap B S hS (pullback z f) (pullback.snd z f ≫ aToU)
            (pP.class B S hS (pullback z f)) :=
          congrArg
            (fun α => pointsMap B S hS (pullback z f) α (pP.class B S hS (pullback z f))) heABeta
      _ = pointsMap B S hS (yoneda.obj A) aToU
            (pointsMap B S hS (pullback z f) (pullback.snd z f) (pP.class B S hS (pullback z f))) :=
          pointsMap_comp_apply B S hS (pullback.snd z f) aToU (pP.class B S hS (pullback z f))
      _ = pointsMap B S hS (yoneda.obj A) aToU aPoint := by
          rw [hpP, hwA]
  have hLies : ubar.LiesOver u := hclassU.trans haPoint
  have hvT : yoneda.map vToT0 = eRep.hom ≫ pullback.fst z f := by
    simp [vToT0]
  have hfstSec : (yoneda.map lOver ≫ eRep.hom) ≫ pullback.fst z f =
      𝟙 (yoneda.obj T₀) := by
    rw [Category.assoc, ← hvT, ← Functor.map_comp, hlOver, yoneda.map_id]
  have hsq : pullback.fst z f ≫ z = pullback.snd z f ≫ f := pullback.condition
  have hmain : (yoneda.map lOver ≫ eRep.hom ≫ pullback.snd z f) ≫ f = z := by
    calc
      (yoneda.map lOver ≫ eRep.hom ≫ pullback.snd z f) ≫ f =
          (yoneda.map lOver ≫ eRep.hom ≫ pullback.fst z f) ≫ z := by
            simpa only [Category.assoc] using
              congrArg (fun m => (yoneda.map lOver ≫ eRep.hom) ≫ m) hsq.symm
      _ = z := by
        rw [← Category.assoc, hfstSec]
        simp
  have hvAapp : (yoneda.map vToA).app (Opposite.op T₀) lOver =
      (pullback.snd z f).app (Opposite.op T₀)
        ((eRep.hom.app (Opposite.op T₀)) lOver) := by
    simpa only [NatTrans.comp_app, types_comp_apply] using
      congrArg (fun α => α.app (Opposite.op T₀) lOver) hvA
  have hvAsection : lOver ≫ vToA =
      (pullback.snd z f).app (Opposite.op T₀)
        ((eRep.hom.app (Opposite.op T₀)) lOver) := hvAapp
  have hmapValue : (FieldValuedPoint.map B S hS U φ ubarVal).value =
      xbar.val.value := by
    have h := congrArg (fun α : yoneda.obj T₀ ⟶ X =>
      α.app (Opposite.op T₀) (𝟙 T₀)) hmain
    show φ.app (Opposite.op T₀)
      (aToU.app (Opposite.op T₀) (lOver ≫ vToA)) = xbar.val.value
    rw [hvAsection]
    simpa [f, NatTrans.comp_app, types_comp_apply, z, yonedaEquiv_apply] using h
  have hMap : FieldValuedPoint.map B S hS U φ ubarVal = xbar.val := by
    have h := congrArg (fun v => { xbar.val with value := v }) hmapValue
    exact h
  exact ⟨ubar, hLies, hMap⟩

end Space

end AlgebraicGeometry

end
