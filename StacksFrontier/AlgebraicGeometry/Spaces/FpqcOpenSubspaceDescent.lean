module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# Descent of open subspaces along an fpqc covering of algebraic spaces

An fpqc covering of an algebraic space over `S` is effective for open subspaces: a family of
open subspaces `W i ⊆ T i` of the members of a covering `{T i ⟶ T}` whose two pullbacks to
`T i ×_T T j` agree descends to a unique open subspace `W ⊆ T` with `W i` the preimage of `W`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_openSubspace_of_fpqcCovering`: a compatible family of
  open subspaces of the members of an fpqc covering descends to a unique open subspace of the
  target.
* `AlgebraicGeometry.Space.isOpenSubspace_preimage`: the preimage of an open subspace along a
  morphism of algebraic spaces is an open subspace.
* `AlgebraicGeometry.Space.isOpen_of_fpqc_preimages`: a subset of a scheme is open as soon as
  its preimage along every member of an fpqc covering family is open.
* `AlgebraicGeometry.Space.isOpen_of_fpqcCovering_preimages`: the same statement for a set of
  points of an algebraic space and an fpqc covering family of algebraic spaces.
* `AlgebraicGeometry.Space.jointly_surjective_points_of_fpqcCovering`: an fpqc covering family of
  algebraic spaces is jointly surjective on points.

## References

* [Stacks Project, Tag 04P1](https://stacks.math.columbia.edu/tag/04P1)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

attribute [local instance] pointTopology

/-! ### The points of a represented presheaf, read from the scheme -/

/-- The homeomorphism between the points of the scheme representing an object of the site and
the points of the presheaf it represents. -/
private noncomputable abbrev schemePointHomeomorph
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).obj U ≃ₜ points B S hS (yoneda.obj U) :=
  (schemePointsHomeomorph B S hS U).symm

/-- The point of the presheaf attached to a point of the representing scheme is the class of
the canonical field-valued representative at that point. -/
private theorem schemePointHomeomorph_apply_representative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) (x : (BigFppfOver.toScheme B S hS).obj U) :
    schemePointHomeomorph B S hS U x =
      (schemePointRepresentative B S hS U x).class B S hS (yoneda.obj U) :=
  (schemePointsHomeomorph B S hS U).symm_apply_eq.mpr
    (schemePointRepresentative_point B S hS U x).symm

/-- The class of a field-valued point of a represented presheaf is the point attached to its
underlying point of the representing scheme. -/
private theorem schemePointHomeomorph_schemePoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    schemePointHomeomorph B S hS U (schemePoint B S hS U p) =
      p.class B S hS (yoneda.obj U) :=
  (schemePointsHomeomorph B S hS U).symm_apply_eq.mpr rfl

/-- The identification of points with scheme points is natural in the site object. -/
private theorem schemePointHomeomorph_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map h) (schemePointHomeomorph B S hS U x) =
      schemePointHomeomorph B S hS V ((BigFppfOver.toScheme B S hS).map h x) := by
  apply (schemePointsHomeomorph B S hS V).injective
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply,
    pointsToScheme_pointsMap]
  exact congrArg ((BigFppfOver.toScheme B S hS).map h)
    ((schemePointsHomeomorph B S hS U).apply_symm_apply x)

/-! ### Preimages of open subspaces -/

private lemma pointsRange_preimage_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X) (x : points B S hS Y) :
    x ∈ Set.range (pointsMap B S hS (Z.preimage f).toFunctor
      (Z.preimage f).ι) ↔
    pointsMap B S hS Y f x ∈
      Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
  induction x using Quot.ind with
  | _ p =>
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨qrep, rfl⟩ := Quot.exists_rep q
      refine ⟨pointsMap B S hS (Z.preimage f).toFunctor
        (Z.fromPreimage f) (qrep.class B S hS (Z.preimage f).toFunctor), ?_⟩
      calc
        pointsMap B S hS Z.toFunctor Z.ι
            (pointsMap B S hS (Z.preimage f).toFunctor
              (Z.fromPreimage f) qrep.class) =
            pointsMap B S hS (Z.preimage f).toFunctor
              (Z.fromPreimage f ≫ Z.ι) qrep.class := by
                rw [pointsMap_comp]
                rfl
        _ = pointsMap B S hS (Z.preimage f).toFunctor
              ((Z.preimage f).ι ≫ f) qrep.class := by
              rw [Subfunctor.fromPreimage_ι]
        _ = pointsMap B S hS Y f
              (pointsMap B S hS (Z.preimage f).toFunctor
                (Z.preimage f).ι qrep.class) := by
              rw [pointsMap_comp]
              rfl
        _ = pointsMap B S hS Y f p.class := congrArg (pointsMap B S hS Y f) hq
    · rintro ⟨q, hq⟩
      obtain ⟨qrep, rfl⟩ := Quot.exists_rep q
      have heq : (FieldValuedPoint.map B S hS Y f p).class B S hS X =
          (FieldValuedPoint.map B S hS Z.toFunctor Z.ι qrep).class B S hS X := by
        simpa only [pointsMap_class] using hq.symm
      obtain ⟨r, ⟨t, htp⟩, ⟨s, hsq⟩⟩ :=
        (FieldValuedPoint.class_eq_class_iff
          B S hS X (FieldValuedPoint.map B S hS Y f p)
          (FieldValuedPoint.map B S hS Z.toFunctor Z.ι qrep)).mp heq
      let yr : FieldValuedPoint B S hS Y := {
        carrier := r.carrier
        field := r.field
        contained := r.contained
        toBase := r.toBase
        value := Y.map t.op p.value }
      have hobjr : yr.siteObject B S hS Y = r.siteObject B S hS X := rfl
      have hobjp : p.siteObject B S hS Y =
          (FieldValuedPoint.map B S hS Y f p).siteObject B S hS X := rfl
      have hfval : f.app (Opposite.op (yr.siteObject B S hS Y)) yr.value = r.value := by
        cases hobjr
        cases hobjp
        exact (NatTrans.naturality_apply f t.op p.value).trans htp
      have hyZ : f.app (Opposite.op (yr.siteObject B S hS Y)) yr.value ∈
          Z.obj (Opposite.op (yr.siteObject B S hS Y)) := by
        rw [hfval]
        show r.value ∈ Z.obj (Opposite.op r.siteObject)
        rw [← hsq]
        exact Z.map s.op qrep.value.property
      let lift : FieldValuedPoint B S hS (Z.preimage f).toFunctor := {
        carrier := r.carrier
        field := r.field
        contained := r.contained
        toBase := r.toBase
        value := ⟨yr.value, hyZ⟩ }
      have hclass : (FieldValuedPoint.map B S hS
          (Z.preimage f).toFunctor (Z.preimage f).ι lift).class B S hS Y =
          p.class B S hS Y := by
        apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
        refine ⟨yr, ?_, ?_⟩
        · refine ⟨𝟙 yr.siteObject, ?_⟩
          show Y.map (𝟙 yr.siteObject).op (lift.value.1) = yr.value
          simp [lift, yr]
        · exact ⟨t, rfl⟩
      refine ⟨lift.class B S hS (Z.preimage f).toFunctor, ?_⟩
      simpa only [pointsMap_class] using hclass

/-- The preimage of an open subspace along a morphism of algebraic spaces is an open subspace of
the source. -/
public theorem isOpenSubspace_preimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X)
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsOpenSubspace B S hS Z) :
    IsOpenSubspace B S hS (Z.preimage f) :=
  isSubspaceWith_preimage f Z hX hY hZ


/-- A subset of a scheme whose preimage along every member of an fpqc covering family is open
is itself open. -/
theorem isOpen_of_fpqc_preimages
    {Y : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage Y)
    (W : Set Y) (hW : ∀ i, IsOpen ((f i) ⁻¹' W)) : IsOpen W := by
  obtain ⟨V, heq, -⟩ := existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage X f hf
    (fun i => ⟨(f i) ⁻¹' W, hW i⟩) (fun i j => TopologicalSpace.Opens.ext (by
      show ((pullback.fst (f i) (f j)) ≫ f i) ⁻¹' W =
        ((pullback.snd (f i) (f j)) ≫ f j) ⁻¹' W
      rw [pullback.condition]))
  have hVW : (V : Set Y) = W := by
    ext y
    obtain ⟨i, x, rfl⟩ := AlgebraicGeometry.fpqc_jointly_surjective f hf y
    exact Set.ext_iff.mp
      (congrArg (fun U : (X i).Opens => (U : Set (X i))) (heq i)) x
  exact hVW ▸ V.2

private theorem isOpen_preimage_affine_of_fpqcCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : ∀ i, X i ⟶ Y) (hf : IsFpqcCovering B S hS f)
    (W : Set (points B S hS Y))
    (hW : ∀ i, @IsOpen _ (pointTopology B S hS (X i))
      (pointsMap B S hS (X i) (f i) ⁻¹' W))
    (A : BigFppfOver B S hS)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (g : yoneda.obj A ⟶ Y) :
    @IsOpen _ (pointTopology B S hS (yoneda.obj A))
      (pointsMap B S hS (yoneda.obj A) g ⁻¹' W) := by
  let G := BigFppfOver.toScheme B S hS
  let J := BigAffineFppf.inclusion B S hS
  let A' : BigAffineFppf B S hS := ⟨A, hA⟩
  obtain ⟨U, _, hU, hfactor⟩ := hf.2 A' g
  have hcover : Presieve.ofArrows (fun j => G.obj (J.obj (U.X j)))
      (fun j => G.map (J.map (U.f j))) ∈ Scheme.fpqcPrecoverage (G.obj A) := by
    simpa [PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
      BigAffineFppf.toScheme, G, J, A'] using hU
  let : TopologicalSpace (points B S hS (yoneda.obj A)) :=
    pointTopology B S hS (yoneda.obj A)
  let eA := schemePointHomeomorph B S hS A
  let V := eA ⁻¹' (pointsMap B S hS (yoneda.obj A) g ⁻¹' W)
  have hV : IsOpen V := by
    apply isOpen_of_fpqc_preimages _ hcover
    intro j
    obtain ⟨i, a, ha⟩ := hfactor j
    let D := J.obj (U.X j)
    let : TopologicalSpace (points B S hS (yoneda.obj D)) :=
      pointTopology B S hS (yoneda.obj D)
    let : TopologicalSpace (points B S hS (X i)) :=
      pointTopology B S hS (X i)
    have hopen := (hW i).preimage (continuous_pointsMap B S hS a)
    have hopen' := hopen.preimage (schemePointHomeomorph B S hS D).continuous
    convert hopen' using 1
    ext x
    show pointsMap B S hS (yoneda.obj A) g
        (eA (G.map (J.map (U.f j)) x)) ∈ W ↔ _
    have hmap := schemePointHomeomorph_map B S hS (J.map (U.f j)) x
    change pointsMap B S hS (yoneda.obj D) (yoneda.map (J.map (U.f j)))
      (schemePointHomeomorph B S hS D x) = eA (G.map (J.map (U.f j)) x) at hmap
    rw [← hmap]
    show pointsMap B S hS (yoneda.obj A) g
        (pointsMap B S hS (yoneda.obj D) (yoneda.map (J.map (U.f j)))
          (schemePointHomeomorph B S hS D x)) ∈ W ↔
      pointsMap B S hS (X i) (f i)
        (pointsMap B S hS (yoneda.obj D) a
          (schemePointHomeomorph B S hS D x)) ∈ W
    have hh := congrArg (fun k => pointsMap B S hS (yoneda.obj D) k
      (schemePointHomeomorph B S hS D x)) ha
    simpa [pointsMap_comp, Function.comp_apply, J, A'] using
      Iff.of_eq (congrArg (fun z => z ∈ W) hh.symm)
  rw [← Set.image_preimage_eq (pointsMap B S hS (yoneda.obj A) g ⁻¹' W) eA.surjective]
  exact eA.isOpenMap _ hV

/-- An fpqc covering family of algebraic spaces over `S` is jointly surjective on points. -/
theorem jointly_surjective_points_of_fpqcCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : ∀ i, X i ⟶ Y) (hf : IsFpqcCovering B S hS f)
    (y : points B S hS Y) :
    ∃ i, y ∈ Set.range (pointsMap B S hS (X i) (f i)) := by
  induction y using Quot.ind with
  | _ p =>
    let A := p.siteObject B S hS Y
    let A' : BigAffineFppf B S hS := ⟨A, by
      show IsAffine (Spec (.of p.carrier))
      infer_instance⟩
    let g : yoneda.obj A ⟶ Y := yonedaEquiv.symm p.value
    let q : FieldValuedPoint B S hS (yoneda.obj A) :=
      ⟨p.carrier, p.contained, p.toBase, 𝟙 A⟩
    have hp : pointsMap B S hS (yoneda.obj A) g q.class = p.class := by
      show (FieldValuedPoint.map B S hS (yoneda.obj A) g q).class = _
      congr 1
      show (⟨p.carrier, p.contained, p.toBase, Y.map (𝟙 A).op p.value⟩ :
        FieldValuedPoint B S hS Y) = p
      simp
    obtain ⟨U, _, hU, hfactor⟩ := hf.2 A' g
    let J := BigAffineFppf.inclusion B S hS
    let G := BigFppfOver.toScheme B S hS
    have hcover : Presieve.ofArrows (fun j => G.obj (J.obj (U.X j)))
        (fun j => G.map (J.map (U.f j))) ∈ Scheme.fpqcPrecoverage (G.obj A) := by
      simpa [PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
      BigAffineFppf.toScheme, G, J, A'] using hU
    obtain ⟨j, x, hx⟩ := AlgebraicGeometry.fpqc_jointly_surjective _ hcover
      (schemePoint B S hS A q)
    obtain ⟨i, a, ha⟩ := hfactor j
    let D := J.obj (U.X j)
    let z := schemePointHomeomorph B S hS D x
    refine ⟨i, pointsMap B S hS (yoneda.obj D) a z, ?_⟩
    show (pointsMap B S hS (X i) (f i) ∘
      pointsMap B S hS (yoneda.obj D) a) z = _
    rw [← pointsMap_comp, ha, pointsMap_comp]
    show pointsMap B S hS (yoneda.obj A) g
      (pointsMap B S hS (yoneda.obj D) (yoneda.map (J.map (U.f j)))
        (schemePointHomeomorph B S hS D x)) = _
    rw [schemePointHomeomorph_map, hx, schemePointHomeomorph_schemePoint]
    exact hp

/-- A set of points of an algebraic space over `S` whose preimage along every member of an fpqc
covering family is open is itself open. -/
theorem isOpen_of_fpqcCovering_preimages
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (f : ∀ i, X i ⟶ Y) (hf : IsFpqcCovering B S hS f)
    (T : Set (points B S hS Y))
    (hT : ∀ i, @IsOpen _ (pointTopology B S hS (X i))
      (pointsMap B S hS (X i) (f i) ⁻¹' T)) :
    @IsOpen _ (pointTopology B S hS Y) T := by
  let : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨U, a, haSurj, haEtale⟩ := hY.exists_atlas
  let : TopologicalSpace (points B S hS (yoneda.obj U)) :=
    pointTopology B S hS (yoneda.obj U)
  let eU := schemePointHomeomorph B S hS U
  let W := (pointsMap B S hS (yoneda.obj U) a) ⁻¹' T
  let V := eU ⁻¹' W
  have hVopen : IsOpen V := by
    apply (isOpen_iff_of_cover
      (fun i => (G.obj U).affineCover.f i |>.isOpenEmbedding.isOpen_range)
      (G.obj U).affineCover.iUnion_range).2
    intro i
    let Z := G.obj U
    let fi := Z.affineCover.f i
    let : AlgebraicGeometry.IsOpenImmersion fi := by
      dsimp [fi, Z]
      infer_instance
    have hAi : (Z.affineCover.X i).size < B.cutoff :=
      Scheme.size_lt_of_isOpenImmersion fi U.left.property
    let A₀ : B.Schemes := B.obj hAi
    let b : A₀ ⟶ U.left := B.inclusion.preimage
      (X := A₀) (Y := U.left) fi
    let A : BigFppfOver B S hS := Over.mk (b ≫ U.hom)
    let j : A ⟶ U := Over.homMk b
    have hj : G.map j = fi := by
      show B.inclusion.map b = fi
      rw [B.inclusion.map_preimage]
    let gi : yoneda.obj A ⟶ Y := yoneda.map j ≫ a
    have hAaff : IsAffine (G.obj A) := by
      show IsAffine (Z.affineCover.X i)
      infer_instance
    have hAiopen := isOpen_preimage_affine_of_fpqcCovering B S hS f hf T hT A hAaff gi
    let eA := schemePointHomeomorph B S hS A
    let Wi := (pointsMap B S hS (yoneda.obj A) gi) ⁻¹' T
    obtain ⟨Vi, hVi, hVimem⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS A Wi).mp hAiopen
    have hchart : fi ⁻¹' V = Vi := by
      ext y
      show eU (fi y) ∈ W ↔ y ∈ Vi
      rw [← hj, ← schemePointHomeomorph_map B S hS j y]
      show pointsMap B S hS (yoneda.obj U) a
          (pointsMap B S hS (yoneda.obj A) (yoneda.map j) (eA y)) ∈ T ↔
        y ∈ Vi
      have hcomp : pointsMap B S hS (yoneda.obj U) a
          (pointsMap B S hS (yoneda.obj A) (yoneda.map j) (eA y)) =
        pointsMap B S hS (yoneda.obj A) (yoneda.map j ≫ a) (eA y) := by
        simpa only [Function.comp_apply] using
          (congrFun (pointsMap_comp B S hS (yoneda.obj A) (yoneda.map j) a) (eA y)).symm
      rw [hcomp]
      have hmem := hVimem (schemePointRepresentative B S hS A y)
      rw [schemePointRepresentative_point] at hmem
      rw [show eA y = (schemePointRepresentative B S hS A y).class B S hS
        (yoneda.obj A) from schemePointHomeomorph_apply_representative B S hS A y]
      exact hmem
    rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
    exact fi.isOpenEmbedding.isOpenMap _ (hchart ▸ hVi)
  have hWopen : @IsOpen _
      (pointTopology B S hS (yoneda.obj U)) W := by
    apply (isOpen_yoneda_iff_isSchemeOpen B S hS U W).2
    refine ⟨V, hVopen, ?_⟩
    intro p
    show pointsMap B S hS (yoneda.obj U) a
        (p.class B S hS (yoneda.obj U)) ∈ T ↔
      schemePoint B S hS U p ∈ V
    rw [← schemePointHomeomorph_schemePoint B S hS U p]
    rfl
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (surjective_iff_surjective_pointsMap B S hS
      Y hY U a).mp haSurj
  rw [← Set.image_preimage_eq T hsurj]
  exact (isOpenMap_pointsMap_of_etale B S hS hY U a haEtale) W hWopen

private theorem openSubspace_ext
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {V W : Subfunctor F} (hV : IsOpenSubspace B S hS V)
    (hW : IsOpenSubspace B S hS W)
    (heq : Set.range (pointsMap B S hS V.toFunctor V.ι) =
      Set.range (pointsMap B S hS W.toFunctor W.ι)) : V = W := by
  let : TopologicalSpace (points B S hS F) :=
    pointTopology B S hS F
  have h := (openSubspacesOrderIso B S hS F hF).injective
    (a₁ := ⟨V, hV⟩) (a₂ := ⟨W, hW⟩) (TopologicalSpace.Opens.ext <|
      (openSubspacesOrderIso_apply B S hS F hF ⟨V, hV⟩).trans
        (heq.trans (openSubspacesOrderIso_apply B S hS F hF ⟨W, hW⟩).symm))
  exact congrArg Subtype.val h

/-- A family of open subspaces `Wᵢ i` of the members of an fpqc covering `f i : Tᵢ i ⟶ T` whose
two pullbacks to each `Tᵢ i ×_T Tᵢ j` agree is the family of preimages of a unique open subspace
of `T`. -/
@[stacks 04P1]
public theorem existsUnique_openSubspace_of_fpqcCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {T : AlgebraicSpaces B S hS}
    {Tᵢ : I → AlgebraicSpaces B S hS}
    (f : ∀ i, Tᵢ i ⟶ T)
    (hf : IsFpqcCovering B S hS (fun i => (f i).hom))
    (Wᵢ : ∀ i, {W : Subfunctor (Tᵢ i).1 // IsOpenSubspace B S hS W})
    (hW : ∀ i j,
      (Wᵢ i).1.preimage (pullback.fst (f i).hom (f j).hom) =
        (Wᵢ j).1.preimage (pullback.snd (f i).hom (f j).hom)) :
    ∃! W : {W : Subfunctor T.1 // IsOpenSubspace B S hS W},
      ∀ i, W.1.preimage (f i).hom = (Wᵢ i).1 := by
  classical
  let : TopologicalSpace (points B S hS T.1) :=
    pointTopology B S hS T.1
  let V i := Set.range (pointsMap B S hS (Wᵢ i).1.toFunctor (Wᵢ i).1.ι)
  let W := ⋃ i, pointsMap B S hS (Tᵢ i).1 (f i).hom '' V i
  have hpre (j : I) : pointsMap B S hS (Tᵢ j).1 (f j).hom ⁻¹' W = V j := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, y, hy, hyx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨z, hz₁, hz₂⟩ := exists_point_of_isPullback B S hS
        (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)) y x hyx
      change pointsMap B S hS (pullback (f i).hom (f j).hom)
        (pullback.fst (f i).hom (f j).hom) z = y at hz₁
      change pointsMap B S hS (pullback (f i).hom (f j).hom)
        (pullback.snd (f i).hom (f j).hom) z = x at hz₂
      have hz : z ∈ Set.range (pointsMap B S hS
          ((Wᵢ i).1.preimage (pullback.fst (f i).hom (f j).hom)).toFunctor
          ((Wᵢ i).1.preimage (pullback.fst (f i).hom (f j).hom)).ι) :=
        (pointsRange_preimage_iff B S hS _ _ z).2 (by
          show pointsMap B S hS (pullback (f i).hom (f j).hom)
            (pullback.fst (f i).hom (f j).hom) z ∈ V i
          rwa [hz₁])
      rw [hW i j] at hz
      have hz' := (pointsRange_preimage_iff B S hS _ _ z).1 hz
      change pointsMap B S hS (pullback (f i).hom (f j).hom)
        (pullback.snd (f i).hom (f j).hom) z ∈ V j at hz'
      rwa [hz₂] at hz'
    · intro hx
      exact Set.mem_iUnion.mpr ⟨j, x, hx, rfl⟩
  have hopen : @IsOpen _ (pointTopology B S hS T.1) W := by
    apply isOpen_of_fpqcCovering_preimages B S hS
      T.property (fun i => (f i).hom) hf W
    intro i
    let : TopologicalSpace (points B S hS (Tᵢ i).1) :=
      pointTopology B S hS (Tᵢ i).1
    rw [hpre]
    have h := (openSubspacesOrderIso B S hS
      (Tᵢ i).1 (Tᵢ i).property (Wᵢ i)).isOpen
    change IsOpen (openSubspacesOrderIso
      B S hS (Tᵢ i).1 (Tᵢ i).property (Wᵢ i)).1 at h
    rwa [openSubspacesOrderIso_apply] at h
  let e := openSubspacesOrderIso B S hS T.1 T.property
  let O := e.symm ⟨W, hopen⟩
  have hO : Set.range (pointsMap B S hS O.1.toFunctor O.1.ι) = W := by
    rw [← openSubspacesOrderIso_apply B S hS T.1 T.property O]
    exact congrArg (fun U : TopologicalSpace.Opens (points B S hS T.1) => U.1)
      (e.apply_symm_apply ⟨W, hopen⟩)
  have hpull (i : I) : O.1.preimage (f i).hom = (Wᵢ i).1 := by
    apply openSubspace_ext B S hS (Tᵢ i).property
      (isOpenSubspace_preimage B S hS (f i).hom O.1 T.property (Tᵢ i).property O.2)
      (Wᵢ i).2
    ext x
    rw [pointsRange_preimage_iff, hO]
    exact Set.ext_iff.mp (hpre i) x
  refine ⟨O, hpull, ?_⟩
  intro O' hO'
  apply Subtype.ext
  apply openSubspace_ext B S hS T.property O'.2 O.2
  ext y
  obtain ⟨i, x, rfl⟩ := jointly_surjective_points_of_fpqcCovering B S hS
    (fun i => (f i).hom) hf y
  rw [← pointsRange_preimage_iff, ← pointsRange_preimage_iff, hO' i, hpull i]


end AlgebraicGeometry.Space

end
