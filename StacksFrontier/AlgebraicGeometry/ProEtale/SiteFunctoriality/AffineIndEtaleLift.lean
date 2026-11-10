module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.CategoryTheory.Sites.Cocontinuous.CocontinuousDefs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineHomOfRingHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.QuotientLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleDense
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleCardinality
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SiteFunctorLimits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.Topology.Specialization.Defs

/-!
# The affine ind-étale lift along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of affine schemes in a chosen big pro-étale site. Base
change along `i` carries the affine ind-étale site of `X` to that of `Z`; it is continuous and
has a fully faithful, cocontinuous left adjoint, the *lift*, which takes coverings to coverings.
The lift of an object `V` over `Z` contains `V` as its closed fibre over `Z`, the inclusion is a
closed immersion, and every point of the lift specializes to a point of `V`.

## Main definitions

* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChange`: base change from the affine ind-étale
  site of `X` to that of `Z`.
* `AlgebraicGeometry.ProEtale.affineIndEtaleLift`: its left-adjoint lift.
* `AlgebraicGeometry.ProEtale.closedFiberInclusion`: the natural map from an object over `Z` to
  its lift over `X`.

## Main results

* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChange_isContinuous`: base change is continuous.
* `AlgebraicGeometry.ProEtale.affineIndEtaleLift_adj_baseChange`: the adjunction.
* `AlgebraicGeometry.ProEtale.affineIndEtaleLift_fullyFaithful`: the lift is fully faithful.
* `AlgebraicGeometry.ProEtale.closedFiberInclusion_isPullback`: an object is the closed fibre of
  its lift.
* `AlgebraicGeometry.ProEtale.closedFiberInclusion_isClosedImmersion`: that inclusion is a closed
  immersion.
* `AlgebraicGeometry.ProEtale.exists_specialization_closedFiber`: every point of the lift
  specializes to a point of the original object.
* `AlgebraicGeometry.ProEtale.affineIndEtaleLift_isCocontinuous`: the lift is cocontinuous.
* `AlgebraicGeometry.ProEtale.affineIndEtaleLift_isCovering`: the lift takes coverings to
  coverings.

## Implementation notes

Both sites lie in the same chosen big pro-étale site, so base change is the pullback in the
slice, computed by `CategoryTheory.Over.pullback`. The lift is built on global sections, from
`AlgebraicGeometry.ProEtale.indEtaleQuotientLift`: an affine ind-étale object of the site of `Z`
is the spectrum of an ind-étale `Γ(Z, ⊤)`-algebra, the quotient-lift functor produces an
ind-étale `Γ(X, ⊤)`-algebra, and a cardinality estimate places its spectrum back inside the
chosen big site. The hom-set bijection of the adjunction is transported along the fully faithful
comparison between the site and the opposite category of ind-étale algebras, and the
specialization statement comes from the fact that the kernel of the counit consists of elements
whose non-units lift.

Coverings of the affine ind-étale site are the finite small-site covering families of
`AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.IsCovering`.

## References

* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) {X Z : B.Scheme}

private def weaklyEtaleMor (B : BigProetaleSite.{u}) : MorphismProperty B.Scheme :=
  fun _ _ f => WeaklyEtale (B.inclusion.map f)

private lemma weaklyEtaleMor_stable (B : BigProetaleSite.{u}) :
    (weaklyEtaleMor B).IsStableUnderBaseChange :=
  ⟨fun hPB hg => WeaklyEtale.instIsStableUnderBaseChangeScheme.of_isPullback
    (B.inclusion.map_isPullback hPB) hg⟩

private lemma affineIndEtalePullback_isAffine (B : BigProetaleSite.{u})
    {X Z : B.Scheme} (i : Z ⟶ X) [IsAffine X.obj] [IsAffine Z.obj]
    (U : AffineIndEtaleProetale B X) :
    IsAffine (B.inclusion.obj ((Over.forget Z).obj ((Over.pullback i).obj
      ((AffineIndEtaleProetale.inclusion B X ⋙
        SmallProetale.inclusion B X.obj X.property).obj U)))) := by
  let U0 : SmallProetale B X.obj X.property :=
    (AffineIndEtaleProetale.inclusion B X).obj U
  let U1 : BigProetaleOver B X.obj X.property :=
    (SmallProetale.inclusion B X.obj X.property).obj U0
  let : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
  let : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
  let hpbB := IsPullback.of_hasPullback U1.hom i
  have hpb : IsPullback (B.inclusion.map (pullback.fst U1.hom i))
      (B.inclusion.map (pullback.snd U1.hom i)) (B.inclusion.map U1.hom)
      (B.inclusion.map i) := B.inclusion.map_isPullback hpbB
  let : IsAffine (B.inclusion.obj U1.left) := U.property.1
  exact IsAffine.of_isPullback hpb

private instance affineIndEtaleProetale_isClosedUnderIsomorphisms
    (B : BigProetaleSite.{u}) (X : B.Scheme) [IsAffine X.obj] :
    (IsAffineIndEtale B X).IsClosedUnderIsomorphisms where
  of_iso {U V} e hU := by
    let eSmall := (SmallProetale.inclusion B X.obj X.property).map e.inv
    let eOver := (Over.forget X).map eSmall
    let f := B.inclusion.map eOver
    have : IsIso eSmall := Functor.map_isIso _ _
    have : IsIso eOver := Functor.map_isIso _ _
    have : IsIso f := Functor.map_isIso _ _
    refine ⟨?_, ?_⟩
    · let : IsAffine (B.inclusion.obj
          ((Over.forget X).obj
            ((SmallProetale.inclusion B X.obj X.property).obj U))) := by
        change IsAffine U.obj.left.obj
        exact hU.1
      exact IsAffine.of_isIso (f := f)
    · have : IsIso f.appTop := by
        change IsIso (f.app ⊤)
        infer_instance
      have h : (B.inclusion.map U.obj.hom).appTop ≫ f.appTop =
          (B.inclusion.map V.obj.hom).appTop := by
        have h := congrArg (fun q => (B.inclusion.map q).appTop)
          (Over.w ((SmallProetale.inclusion B X.obj X.property).map e.inv))
        change (B.inclusion.map U.obj.hom).appTop ≫ f.appTop =
          (B.inclusion.map V.obj.hom).appTop
        exact h
      exact (ObjectProperty.ind _).prop_of_iso (Under.isoMk (asIso f.appTop) h) hU.2

private instance affineIndEtaleProetale_isClosedUnderPullbacks
    (B : BigProetaleSite.{u}) (X : B.Scheme) [IsAffine X.obj] :
    (IsAffineIndEtale B X).IsClosedUnderLimitsOfShape WalkingCospan := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  intro Y hY
  obtain ⟨F, hF⟩ := hY
  let : HasPullbacks (SmallProetale B X.obj X.property) :=
    smallProetale_hasPullbacks B X.obj X.property
  let : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B X.obj X.property) :=
    smallProetaleInclusion_preservesPullbacks B X.obj X.property
  let G := SmallProetale.inclusion B X.obj X.property ⋙
    BigProetaleOver.forget B X.obj X.property
  have : PreservesLimitsOfShape WalkingCospan G := by infer_instance
  have hlim : IsLimit (G.mapCone (limit.cone F)) := isLimitOfPreserves G (limit.isLimit F)
  let hpb := IsPullback.of_isLimit_cone hlim
  let U := F.obj .left
  let V := F.obj .right
  let W := F.obj .one
  let P := limit F
  let pU := G.map (limit.π F .left)
  let pV := G.map (limit.π F .right)
  let f := F.map WalkingCospan.Hom.inl
  let g := F.map WalkingCospan.Hom.inr
  have hU : IsAffineIndEtale B X U := hF .left
  have hV : IsAffineIndEtale B X V := hF .right
  have hW : IsAffineIndEtale B X W := hF .one
  change IsAffine (B.inclusion.obj P.obj.left) ∧
    ObjectProperty.ind.{u}
      (fun C : Under Γ(X.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk (B.inclusion.map P.obj.hom).appTop)
  have hPAff : IsAffine (B.inclusion.obj P.obj.left) := by
    let : IsAffine (B.inclusion.obj ((F ⋙ G).obj .left)) := by
      change IsAffine U.obj.left.obj
      exact hU.1
    let : IsAffine (B.inclusion.obj ((F ⋙ G).obj .right)) := by
      change IsAffine V.obj.left.obj
      exact hV.1
    let : IsAffine (B.inclusion.obj ((F ⋙ G).obj .one)) := by
      change IsAffine W.obj.left.obj
      exact hW.1
    exact IsAffine.of_isPullback (hpb.map B.inclusion)
  refine ⟨hPAff, ?_⟩
  have hpV : pV ≫ V.obj.hom = P.obj.hom :=
    Over.w ((SmallProetale.inclusion B X.obj X.property).map (limit.π F .right))
  rw [← hpV]
  let : IsAffine (G.obj P).obj := by
    change IsAffine (B.inclusion.obj P.obj.left)
    exact hPAff
  exact indEtale_pullback_small B hU hV hW f g pU pV hpb

private instance affineIndEtaleProetale_hasPullbacks
    (B : BigProetaleSite.{u}) (X : B.Scheme) [IsAffine X.obj] :
    HasPullbacks (AffineIndEtaleProetale B X) := by
  change HasLimitsOfShape WalkingCospan
    ((IsAffineIndEtale B X).FullSubcategory)
  infer_instance

public noncomputable def affineIndEtaleGlobalSections
    (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj] :
    AffineIndEtaleProetale B S ⥤
      (IndEtaleAlgebra Γ(S.obj, ⊤))ᵒᵖ where
  obj U := Opposite.op ⟨
    Under.mk (B.inclusion.map U.obj.obj.hom).appTop, U.property.2⟩
  map {U V} f := by
    let f₀ := (AffineIndEtaleProetale.inclusion B S).map f
    let f₁ := (SmallProetale.inclusion B S.obj S.property).map f₀
    let q := (B.inclusion.map f₁.left).appTop
    let U' : IndEtaleAlgebra Γ(S.obj, ⊤) :=
      ⟨Under.mk (B.inclusion.map U.obj.obj.hom).appTop, U.property.2⟩
    let V' : IndEtaleAlgebra Γ(S.obj, ⊤) :=
      ⟨Under.mk (B.inclusion.map V.obj.obj.hom).appTop, V.property.2⟩
    let m : V' ⟶ U' := by
      apply ObjectProperty.homMk
      refine Under.homMk (CommRingCat.ofHom q.hom) ?_
      have hw : (B.inclusion.map V.obj.obj.hom).appTop ≫ q =
          (B.inclusion.map U.obj.obj.hom).appTop := by
        have hh := congrArg (fun g => (B.inclusion.map g).appTop) (Over.w f₁)
        simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at hh
        change (B.inclusion.map V.obj.obj.hom).appTop ≫ q =
          (B.inclusion.map U.obj.obj.hom).appTop at hh
        exact hh
      change (B.inclusion.map V.obj.obj.hom).appTop ≫
        CommRingCat.ofHom q.hom = (B.inclusion.map U.obj.obj.hom).appTop
      apply CommRingCat.hom_ext
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
        congrArg CommRingCat.Hom.hom hw
    exact Opposite.op m

private lemma affineIndEtaleGlobalSections_map_right
    (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj]
    {U V : AffineIndEtaleProetale B S} (f : U ⟶ V) :
    Under.Hom.right (((affineIndEtaleGlobalSections B S).map f).unop.hom) =
      (B.inclusion.map (((SmallProetale.inclusion B S.obj S.property).map
        ((AffineIndEtaleProetale.inclusion B S).map f)).left)).appTop := by
  rfl

public noncomputable def rebaseIndEtaleAlongIso
    {A R : Type u} [CommRing A] [CommRing R]
    (e : CommRingCat.of A ≅ CommRingCat.of R) :
    (IndEtaleAlgebra R)ᵒᵖ ⥤
      (IndEtaleAlgebra A)ᵒᵖ := by
  let b := e.hom
  let G : IndEtaleAlgebra R ⥤
      IndEtaleAlgebra A :=
    ObjectProperty.lift _ ((ObjectProperty.ι _) ⋙ Under.map b) (by
      intro V
      let : CommRingCat.etale.ContainsIdentities := ⟨fun _ => by
        rw [CommRingCat.etale_iff]
        exact RingHom.etale_algebraMap.2 (inferInstance : Algebra.Etale _ _)⟩
      let : IsIso b := by dsimp [b]; infer_instance
      let : Algebra A R := b.hom.toAlgebra
      let : Algebra R V.obj.right := V.obj.hom.hom.toAlgebra
      let : Algebra A V.obj.right := (V.obj.hom.hom.comp b.hom).toAlgebra
      let : IsScalarTower A R V.obj.right := IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        rfl)
      have hbEtale : CommRingCat.etale b := CommRingCat.etale.of_isIso b
      have hbRing : MorphismProperty.ind.{u} CommRingCat.etale b :=
        (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale) (f := b)).mpr
          (ObjectProperty.le_ind _ _ hbEtale)
      have hbAlg : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A R) :=
        CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hbRing
      have hVRing : MorphismProperty.ind.{u} CommRingCat.etale V.obj.hom :=
        (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale)
          (f := V.obj.hom)).mpr V.property
      have hVAlg : (CommAlgCat.etale R).ind.{u}
          (CommAlgCat.of R V.obj.right) :=
        CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hVRing
      have hcomp := CommAlgCat.ind_etale_comp hbAlg hVAlg
      have hcompRing : MorphismProperty.ind.{u} CommRingCat.etale
          (b ≫ V.obj.hom) := by
        rw [show b ≫ V.obj.hom =
          CommRingCat.ofHom (algebraMap A V.obj.right) from by
            ext x
            exact (IsScalarTower.algebraMap_apply A R V.obj.right x).symm]
        exact CommAlgCat.ind_etale_iff_ind_algebraMap.mp hcomp
      exact (MorphismProperty.ind_iff_ind_underMk
        (P := CommRingCat.etale) (f := b ≫ V.obj.hom)).mp hcompRing)
  exact G.op

public noncomputable def specIndEtaleOver
    (A : Type u) [CommRing A] :
    (IndEtaleAlgebra A)ᵒᵖ ⥤
      Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of A))) where
  obj V := Over.mk (Scheme.Spec.map V.unop.obj.hom.op)
  map {U V} f := Over.homMk (Scheme.Spec.map f.unop.hom.right.op) (by
    change Scheme.Spec.map f.unop.hom.right.op ≫
      Scheme.Spec.map V.unop.obj.hom.op = Scheme.Spec.map U.unop.obj.hom.op
    rw [← Scheme.Spec.map_comp]
    exact congrArg (fun g => Scheme.Spec.map g.op) (Under.w f.unop.hom))

public noncomputable def boundedOver
    (B : BigProetaleSite.{u}) (X : B.Scheme)
    {C : Type*} [Category C] (F : C ⥤ Over X.obj)
    (hsize : ∀ c, (F.obj c).left.size < B.cutoff) :
    C ⥤ BigProetaleOver B X.obj X.property where
  obj c := by
    let Y : B.Scheme := ⟨(F.obj c).left, hsize c⟩
    let g : Y ⟶ X := B.inclusion.preimage (F.obj c).hom
    exact Over.mk g
  map {c d} f := by
    let Y : B.Scheme := ⟨(F.obj c).left, hsize c⟩
    let Z : B.Scheme := ⟨(F.obj d).left, hsize d⟩
    let g : Y ⟶ Z := B.inclusion.preimage (F.map f).left
    exact Over.homMk g (by
      apply B.inclusion.map_injective
      change B.inclusion.map g ≫ B.inclusion.map (Over.mk _).hom =
        B.inclusion.map (Over.mk _).hom
      simpa only [g, Over.mk_hom, B.inclusion.map_preimage] using Over.w (F.map f))
  map_id c := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    let Y : B.Scheme := ⟨(F.obj c).left, hsize c⟩
    change B.inclusion.map (B.inclusion.preimage
        (show B.inclusion.obj Y ⟶ B.inclusion.obj Y from (F.map (𝟙 c)).left)) =
      B.inclusion.map (𝟙 Y)
    rw [F.map_id]
    simp only [B.inclusion.map_preimage, B.inclusion.map_id]
    simp only [Over.id_left]
    rfl
  map_comp {a b c} f g := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    let Y : B.Scheme := ⟨(F.obj a).left, hsize a⟩
    let Z : B.Scheme := ⟨(F.obj b).left, hsize b⟩
    let W : B.Scheme := ⟨(F.obj c).left, hsize c⟩
    change B.inclusion.map (B.inclusion.preimage
        (show B.inclusion.obj Y ⟶ B.inclusion.obj W from (F.map (f ≫ g)).left)) =
      B.inclusion.map (B.inclusion.preimage
          (show B.inclusion.obj Y ⟶ B.inclusion.obj Z from (F.map f).left) ≫
        B.inclusion.preimage
          (show B.inclusion.obj Z ⟶ B.inclusion.obj W from (F.map g).left))
    rw [F.map_comp]
    simp only [B.inclusion.map_preimage, B.inclusion.map_comp]
    rfl

public noncomputable def affineClosedImmersionRingData
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    Σ I : Ideal Γ(X.obj, ⊤),
      CommRingCat.of (Γ(X.obj, ⊤) ⧸ I) ≅ CommRingCat.of Γ(Z.obj, ⊤) := by
  letI : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
  letI : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
  let f := (B.inclusion.map i).appTop
  let hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine
    (B.inclusion.map i)).2
  refine ⟨RingHom.ker f.hom, ?_⟩
  exact (RingHom.quotientKerEquivOfSurjective (f := f.hom) hsurj).toCommRingCatIso

public noncomputable def affineIndEtaleLiftAlgebra
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    AffineIndEtaleProetale B Z ⥤
      (IndEtaleAlgebra Γ(X.obj, ⊤))ᵒᵖ := by
  let d := affineClosedImmersionRingData B i
  exact affineIndEtaleGlobalSections B Z ⋙
    rebaseIndEtaleAlongIso d.2 ⋙
    (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).op

public noncomputable def affineIndEtaleLiftRawOverSpec
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    AffineIndEtaleProetale B Z ⥤
      Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of Γ(X.obj, ⊤)))) :=
  affineIndEtaleLiftAlgebra B i ⋙ specIndEtaleOver Γ(X.obj, ⊤)

public noncomputable def affineIndEtaleLiftRawOver
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    AffineIndEtaleProetale B Z ⥤ Over X.obj :=
  affineIndEtaleLiftRawOverSpec B i ⋙ Over.map X.obj.isoSpec.inv

public lemma affineIndEtaleLiftRawOver_size
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (V : AffineIndEtaleProetale B Z) :
    ((affineIndEtaleLiftRawOver B i).obj V).left.size < B.cutoff := by
  let d := affineClosedImmersionRingData B i
  let W := ((affineIndEtaleGlobalSections B Z).obj V).unop
  let V' := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op W)).unop
  let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V'
  have hV : Cardinal.mk V'.obj.right ≤ V.obj.obj.left.obj.size := by
    let : IsAffine V.obj.obj.left.obj := V.property.1
    change Cardinal.mk Γ(V.obj.obj.left.obj, ⊤) ≤ V.obj.obj.left.obj.size
    exact section_ring_le_size_of_affine V.obj.obj.left.obj
  change (Spec (CommRingCat.of C.obj.right)).size < B.cutoff
  exact liftedSpec_size_lt_cutoff B d.1 V' X.property
    V.obj.obj.left.property (section_ring_le_size_of_affine X.obj) hV

private lemma affineIndEtaleLiftRawOver_weaklyEtale
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (V : AffineIndEtaleProetale B Z) :
    WeaklyEtale ((affineIndEtaleLiftRawOver B i).obj V).hom := by
  let d := affineClosedImmersionRingData B i
  let W := ((affineIndEtaleGlobalSections B Z).obj V).unop
  let V' := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op W)).unop
  let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V'
  let : Algebra Γ(X.obj, ⊤) C.obj.right := C.obj.hom.hom.toAlgebra
  have hindR : MorphismProperty.ind.{u} CommRingCat.etale C.obj.hom :=
    (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale)
      (f := C.obj.hom)).mpr C.property
  have hindAlg : (CommAlgCat.etale Γ(X.obj, ⊤)).ind
      (CommAlgCat.of Γ(X.obj, ⊤) C.obj.right) :=
    CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hindR
  have hweakAlg : @Algebra.WeaklyEtale Γ(X.obj, ⊤) C.obj.right _ _
      C.obj.hom.hom.toAlgebra :=
    Algebra.weaklyEtale_of_ind_etale (StacksDraft.indEtale_iff.mpr hindAlg)
  have hweakSpec : WeaklyEtale (Spec.map C.obj.hom) :=
    (weaklyEtale_specMap_iff C.obj.hom).2 hweakAlg
  change WeaklyEtale (Scheme.Spec.map C.obj.hom.op ≫ X.obj.isoSpec.inv)
  have : IsIso X.obj.isoSpec.inv := inferInstance
  let : WeaklyEtale (Spec.map C.obj.hom) := hweakSpec
  have : WeaklyEtale (Scheme.Spec.map C.obj.hom.op) := by simpa using hweakSpec
  infer_instance

private lemma affineIndEtaleLiftRawOver_indEtale
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (V : AffineIndEtaleProetale B Z) :
    ObjectProperty.ind.{u}
      (fun C : Under Γ(X.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop) := by
  let d := affineClosedImmersionRingData B i
  let W := ((affineIndEtaleGlobalSections B Z).obj V).unop
  let V' := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op W)).unop
  let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V'
  let eA := Scheme.ΓSpecIso (CommRingCat.of Γ(X.obj, ⊤))
  let eC := Scheme.ΓSpecIso (CommRingCat.of C.obj.right)
  have hspec : X.obj.isoSpec.hom.appTop = eA.hom := by
    change X.obj.toSpecΓ.appTop = eA.hom
    rw [Scheme.toSpecΓ_appTop]
    rfl
  have hbase : X.obj.isoSpec.inv.appTop = eA.inv := by
    apply (cancel_mono eA.hom).mp
    calc
      X.obj.isoSpec.inv.appTop ≫ eA.hom =
          (X.obj.isoSpec.hom ≫ X.obj.isoSpec.inv).appTop := by
        rw [Scheme.Hom.comp_appTop, hspec]
      _ = eA.inv ≫ eA.hom := by
        rw [X.obj.isoSpec.hom_inv_id]
        rw [Scheme.Hom.id_appTop]
        exact eA.inv_hom_id.symm
  have hraw : ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop =
      X.obj.isoSpec.inv.appTop ≫ (Spec.map C.obj.hom).appTop := by
    change (Spec.map C.obj.hom ≫ X.obj.isoSpec.inv).appTop = _
    rw [Scheme.Hom.comp_appTop]
  have hmaps : (Spec.map C.obj.hom).appTop =
      (Scheme.Spec.map C.obj.hom.op).appTop := rfl
  have hraw' : ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop =
      X.obj.isoSpec.inv.appTop ≫ (Scheme.Spec.map C.obj.hom.op).appTop := by
    rw [hraw, hmaps]
  have hcomm : C.obj.hom ≫ eC.inv =
      ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop := by
    have hfirst : C.obj.hom ≫ eC.inv = eA.inv ≫ (Spec.map C.obj.hom).appTop :=
      Scheme.ΓSpecIso_inv_naturality C.obj.hom
    have hsecond : eA.inv ≫ (Spec.map C.obj.hom).appTop =
        ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop := by
      rw [← hbase, hmaps]
      exact hraw'.symm
    exact hfirst.trans hsecond
  have hU : ObjectProperty.ind.{u}
      (fun C : Under Γ(X.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk C.obj.hom) := C.property
  exact (ObjectProperty.ind _).prop_of_iso
    (Under.isoMk (eC.symm) hcomm) hU

private lemma cardinal_mk_colimit_le {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hJ : Cardinal.mk J ≤ κ) (hF : ∀ j, Cardinal.mk (F.obj j) ≤ κ) :
    Cardinal.mk (CommRingCat.FilteredColimits.colimit F) ≤ κ := by
  classical
  let c := (forget CommRingCat).mapCocone (CommRingCat.FilteredColimits.colimitCocone F)
  have hsurj : Function.Surjective
      (fun p : Σ j, F.obj j => c.ι.app p.1 p.2) := by
    intro x
    have hc : IsColimit c := isColimitOfPreserves (forget CommRingCat)
      (CommRingCat.FilteredColimits.colimitCoconeIsColimit F)
    obtain ⟨j, y, hy⟩ := Limits.Types.jointly_surjective (F ⋙ forget CommRingCat) hc x
    exact ⟨⟨j, y⟩, hy⟩
  have hcard : Cardinal.mk c.pt ≤ Cardinal.mk (Σ j, F.obj j) :=
    Cardinal.mk_le_of_surjective hsurj
  calc
    Cardinal.mk (CommRingCat.FilteredColimits.colimit F) ≤ Cardinal.mk (Σ j, F.obj j) := by
      simpa [c, CommRingCat.FilteredColimits.colimitCocone] using hcard
    _ ≤ κ := by
      rw [Cardinal.mk_sigma]
      calc
        Cardinal.sum (fun j : J => Cardinal.mk (F.obj j)) ≤ Cardinal.sum (fun _ : J => κ) :=
          Cardinal.sum_le_sum _ _ hF
        _ ≤ κ := by
          rw [Cardinal.sum_const']
          exact (mul_le_mul' hJ le_rfl).trans (Cardinal.mul_eq_self.{u} hκ).le

private lemma spec_size_le_proetaleBound {R : Type u} [CommRing R]
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ) (hR : Cardinal.mk R ≤ κ) :
    (Scheme.Spec.obj (Opposite.op (CommRingCat.of R))).size ≤
      Cardinal.proetaleBound κ := by
  change (Spec (CommRingCat.of R)).size ≤ Cardinal.proetaleBound κ
  rw [Scheme.size_Spec]
  apply max_le
  · have hpow : κ ≤ κ ^ Cardinal.aleph0 :=
      Cardinal.self_le_power κ Cardinal.one_le_aleph0
    have hκpow : κ ^ Cardinal.aleph0 ≤ Cardinal.proetaleBound κ := by
      change κ ^ Cardinal.aleph0 ≤
        max (κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))))
          (max (κ ^ Cardinal.aleph0) (Order.succ κ))
      exact (le_max_left _ _).trans (le_max_right _ _)
    exact hκ.trans (hpow.trans hκpow)
  · calc
      Cardinal.mk R ≤ κ := hR
      _ ≤ Order.succ κ := Order.le_succ _
      _ ≤ max (κ ^ Cardinal.aleph0) (Order.succ κ) := le_max_right _ _
      _ ≤ Cardinal.proetaleBound κ := le_max_right _ _

/-- Pullback along a morphism of the base, on affine ind-étale pro-étale sites. -/
@[stacks 09BK "the base-change functor"]
public noncomputable def affineIndEtaleBaseChange (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] :
    AffineIndEtaleProetale B X ⥤ AffineIndEtaleProetale B Z := by
  let F0 : AffineIndEtaleProetale B X ⥤ BigProetaleOver B Z.obj Z.property :=
    AffineIndEtaleProetale.inclusion B X ⋙
      SmallProetale.inclusion B X.obj X.property ⋙ Over.pullback i
  let P : MorphismProperty B.Scheme := fun _ _ f => WeaklyEtale (B.inclusion.map f)
  have hP : P.IsStableUnderBaseChange := by
    constructor
    intro T Y Y' S f g f' g' hPB hg
    exact WeaklyEtale.instIsStableUnderBaseChangeScheme.of_isPullback
      (B.inclusion.map_isPullback hPB) hg
  let F1 : AffineIndEtaleProetale B X ⥤ SmallProetale B Z.obj Z.property :=
    ObjectProperty.lift (IsWeaklyEtaleOver B Z.obj Z.property) F0 (by
      intro U
      let U0 := (AffineIndEtaleProetale.inclusion B X).obj U
      let U1 := (SmallProetale.inclusion B X.obj X.property).obj U0
      change P ((Over.pullback i).obj U1).hom
      let : P.IsStableUnderBaseChange := hP
      exact MorphismProperty.pullback_snd (P := P) U1.hom i U0.property)
  exact ObjectProperty.lift (IsAffineIndEtale B Z) F1 (by
    intro U
    refine ⟨?_, ?_⟩
    · let U0 : SmallProetale B X.obj X.property :=
        (AffineIndEtaleProetale.inclusion B X).obj U
      let U1 : BigProetaleOver B X.obj X.property :=
        (SmallProetale.inclusion B X.obj X.property).obj U0
      let hpbB := IsPullback.of_hasPullback U1.hom i
      have hpb : IsPullback (B.inclusion.map (pullback.fst U1.hom i))
          (B.inclusion.map (pullback.snd U1.hom i)) (B.inclusion.map U1.hom)
          (B.inclusion.map i) := B.inclusion.map_isPullback hpbB
      let : IsAffine (B.inclusion.obj U1.left) := U.property.1
      let : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
      let : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
      exact IsAffine.of_isPullback hpb
    · let U0 : SmallProetale B X.obj X.property :=
        (AffineIndEtaleProetale.inclusion B X).obj U
      let U1 : BigProetaleOver B X.obj X.property :=
        (SmallProetale.inclusion B X.obj X.property).obj U0
      let hpbB := IsPullback.of_hasPullback U1.hom i
      let : IsAffine (B.inclusion.obj U1.left) := U.property.1
      let : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
      let : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
      have hpb : IsPullback (B.inclusion.map (pullback.fst U1.hom i))
          (B.inclusion.map (pullback.snd U1.hom i)) (B.inclusion.map U1.hom)
          (B.inclusion.map i) := B.inclusion.map_isPullback hpbB
      let : IsAffine (B.inclusion.obj ((Over.forget Z).obj ((Over.pullback i).obj U1))) :=
        IsAffine.of_isPullback hpb
      let A := Γ(X.obj, ⊤)
      let S := Γ(U1.left.obj, ⊤)
      let R := Γ(Z.obj, ⊤)
      let T := Γ(((Over.forget Z).obj ((Over.pullback i).obj U1)).obj, ⊤)
      let f := (B.inclusion.map U1.hom).appTop
      let g := (B.inclusion.map i).appTop
      let f' := (B.inclusion.map (pullback.fst U1.hom i)).appTop
      let g' := (B.inclusion.map (pullback.snd U1.hom i)).appTop
      have hpush0 : IsPushout f g f' g' := isPushout_appTop_of_isPullback hpb
      have hpush : IsPushout g f g' f' := hpush0.flip
      let : Algebra A S := f.hom.toAlgebra
      let : Algebra A R := g.hom.toAlgebra
      let : Algebra S T := f'.hom.toAlgebra
      let : Algebra R T := g'.hom.toAlgebra
      let : Algebra A T := (f ≫ f').hom.toAlgebra
      have hfg : (f ≫ f') = (g ≫ g') := by
        have h := congrArg (fun q => (B.inclusion.map q).appTop) hpbB.w
        simpa [f, g, f', g', Scheme.Hom.comp_appTop] using h
      let : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        rfl)
      let : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of T => k.hom x) hfg)
      have hf : CommRingCat.ofHom (algebraMap A S) = f := by ext x; rfl
      have hg : CommRingCat.ofHom (algebraMap A R) = g := by ext x; rfl
      have hf' : CommRingCat.ofHom (algebraMap S T) = f' := by ext x; rfl
      have hg' : CommRingCat.ofHom (algebraMap R T) = g' := by ext x; rfl
      have hpushAlg : Algebra.IsPushout A R S T := by
        apply CommRingCat.isPushout_iff_isPushout.mp
        rw [hg, hf, hg', hf']
        exact hpush
      have hU : (CommAlgCat.etale A).ind (CommAlgCat.of A S) := by
        rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk]
        exact U.property.2
      let : Algebra.IsPushout A R S T := hpushAlg
      have hT : (CommAlgCat.etale R).ind (CommAlgCat.of R T) :=
        CommAlgCat.ind_etale_of_isPushout A R S T hU
      have hT' : CommRingCat.etale.ind (CommRingCat.ofHom (algebraMap R T)) :=
        CommAlgCat.ind_etale_iff_ind_algebraMap.mp hT
      change (CommRingCat.etale).underObj.ind
        (Under.mk (CommRingCat.ofHom (algebraMap R T)))
      exact (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale)
        (f := CommRingCat.ofHom (algebraMap R T))).mp hT')

/-- Base change on the affine ind-étale sites is continuous. -/
@[stacks 09BK]
public instance affineIndEtaleBaseChange_isContinuous (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] :
    (affineIndEtaleBaseChange B i).IsContinuous (AffineIndEtaleProetale.topology B X)
      (AffineIndEtaleProetale.topology B Z) := by
  let F := smallProetaleBaseChange B Z X i
  let G := affineIndEtaleBaseChange B i
  let iX := AffineIndEtaleProetale.inclusion B X
  let iZ := AffineIndEtaleProetale.inclusion B Z
  let JX := SmallProetale.topology B X.obj X.property
  let JZ := SmallProetale.topology B Z.obj Z.property
  let KX := AffineIndEtaleProetale.topology B X
  let KZ := AffineIndEtaleProetale.topology B Z
  let : F.IsContinuous JX JZ :=
    (smallProetaleBaseChange_isMorphismOfSites B Z X i).toIsContinuous
  let : (iX ⋙ F).IsContinuous KX JZ := Functor.isContinuous_comp iX F KX JX JZ
  let H := iZ.sheafPushforwardContinuous (Type (u + 1)) KZ JZ
  let : H.IsEquivalence := AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B Z
  constructor
  intro Q
  let E := H.objPreimage Q
  let e := H.objObjPreimageIso Q
  have h : Presieve.IsSheaf KX (G.op ⋙ (H.obj E).obj) := by
    change Presieve.IsSheaf KX ((iX ⋙ F).op ⋙ E.obj)
    exact (iX ⋙ F).op_comp_isSheaf_of_types KX JZ E
  exact Presieve.isSheaf_iso KX
    (Functor.isoWhiskerLeft G.op ((sheafToPresheaf KZ (Type (u + 1))).mapIso e)) h

/-- The left-adjoint lift of an affine ind-étale object across the closed immersion. -/
public noncomputable def affineIndEtaleLift (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    AffineIndEtaleProetale B Z ⥤ AffineIndEtaleProetale B X := by
  classical
  let F0 : AffineIndEtaleProetale B Z ⥤
      BigProetaleOver B X.obj X.property :=
    boundedOver B X (affineIndEtaleLiftRawOver B i) (affineIndEtaleLiftRawOver_size B i)
  let d := affineClosedImmersionRingData B i
  let F1 : AffineIndEtaleProetale B Z ⥤
      SmallProetale B X.obj X.property :=
    ObjectProperty.lift (IsWeaklyEtaleOver B X.obj X.property) F0 (by
      intro V
      let Y : B.Scheme :=
        ⟨((affineIndEtaleLiftRawOver B i).obj V).left, affineIndEtaleLiftRawOver_size B i V⟩
      change WeaklyEtale (B.inclusion.map (B.inclusion.preimage
        (show B.inclusion.obj Y ⟶ B.inclusion.obj X from
          ((affineIndEtaleLiftRawOver B i).obj V).hom)))
      rw [B.inclusion.map_preimage]
      exact affineIndEtaleLiftRawOver_weaklyEtale B i V)
  exact ObjectProperty.lift (IsAffineIndEtale B X) F1 (by
    intro V
    let V0 := ((affineIndEtaleGlobalSections B Z).obj V).unop
    let V1 := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op V0)).unop
    let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V1
    let Y : B.Scheme :=
      ⟨((affineIndEtaleLiftRawOver B i).obj V).left, affineIndEtaleLiftRawOver_size B i V⟩
    refine ⟨?_, ?_⟩
    · change IsAffine (B.inclusion.obj ((F1.obj V).obj.left))
      change IsAffine ((affineIndEtaleLiftRawOver B i).obj V).left
      let : IsAffine ((affineIndEtaleLiftRawOver B i).obj V).left := by
        change IsAffine (Scheme.Spec.obj (Opposite.op (CommRingCat.of C.obj.right)))
        infer_instance
      infer_instance
    · change ObjectProperty.ind.{u}
        (fun C : Under Γ(X.obj, ⊤) ↦ C.hom.hom.Etale)
        (Under.mk (B.inclusion.map (F0.obj V).hom).appTop)
      change ObjectProperty.ind.{u}
        (fun C : Under Γ(X.obj, ⊤) ↦ C.hom.hom.Etale)
        (Under.mk (B.inclusion.map (B.inclusion.preimage
          (show B.inclusion.obj Y ⟶ B.inclusion.obj X from
            ((affineIndEtaleLiftRawOver B i).obj V).hom))).appTop)
      rw [B.inclusion.map_preimage]
      exact affineIndEtaleLiftRawOver_indEtale B i V)

public noncomputable def quotientLiftCounitUnder
    {A : Type u} [CommRing A] (I : Ideal A)
    (adj : indEtaleQuotientBaseChange A I ⊣
      indEtaleQuotientLift A I)
    (V : IndEtaleAlgebra (A ⧸ I)) :
    (Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))).obj
        ((indEtaleQuotientLift A I).obj V).obj ⟶ V.obj := by
  change ((indEtaleQuotientLift A I ⋙
    indEtaleQuotientBaseChange A I).obj V).obj ⟶ V.obj
  exact (adj.counit.app V).hom

public noncomputable def quotientLiftCounitRingMap
    {A : Type u} [CommRing A] (I : Ideal A)
    (adj : indEtaleQuotientBaseChange A I ⊣
      indEtaleQuotientLift A I)
    (V : IndEtaleAlgebra (A ⧸ I)) :
    ((indEtaleQuotientLift A I).obj V).obj.right ⟶ V.obj.right := by
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  simpa only [Under.map_obj_right] using
    (Under.mapPushoutAdj b).homEquiv
      ((indEtaleQuotientLift A I).obj V).obj V.obj
      (quotientLiftCounitUnder I adj V) |>.right

private lemma quotientLiftCounitRingMap_naturality
    {A : Type u} [CommRing A] (I : Ideal A)
    (adj : indEtaleQuotientBaseChange A I ⊣
      indEtaleQuotientLift A I)
    {V W : IndEtaleAlgebra (A ⧸ I)} (f : V ⟶ W) :
    ((indEtaleQuotientLift A I).map f).hom.right ≫
        quotientLiftCounitRingMap I adj W =
      quotientLiftCounitRingMap I adj V ≫ f.hom.right := by
  classical
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let H := Under.mapPushoutAdj b
  let εV := quotientLiftCounitUnder I adj V
  let εW := quotientLiftCounitUnder I adj W
  have hε := congrArg (fun g => g.hom) (adj.counit.naturality f)
  change (Under.pushout b).map ((indEtaleQuotientLift A I).map f).hom ≫ εW =
    εV ≫ f.hom at hε
  have h := congrArg (H.homEquiv ((indEtaleQuotientLift A I).obj V).obj W.obj) hε
  rw [H.homEquiv_naturality_left, H.homEquiv_naturality_right] at h
  have h' := congrArg Under.Hom.right h
  simpa [H, εV, εW, quotientLiftCounitRingMap, quotientLiftCounitUnder] using h'

private lemma quotientLiftCounit_isPushout
    {A : Type u} [CommRing A] (I : Ideal A)
    (adj : indEtaleQuotientBaseChange A I ⊣
      indEtaleQuotientLift A I)
    (V : IndEtaleAlgebra (A ⧸ I)) :
    let C := (indEtaleQuotientLift A I).obj V
    let t := quotientLiftCounitRingMap I adj V
    IsPushout C.obj.hom (CommRingCat.ofHom (Ideal.Quotient.mk I))
      t V.obj.hom := by
  classical
  dsimp only
  let C := (indEtaleQuotientLift A I).obj V
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let t := quotientLiftCounitRingMap I adj V
  change IsPushout C.obj.hom b t V.obj.hom
  let ε := (adj.counit.app V).hom
  obtain ⟨e⟩ := indEtaleQuotientLift_baseChangeIso A I
  have : IsIso adj.counit := adj.isIso_counit_of_iso e
  have : IsIso ε := by dsimp [ε]; infer_instance
  let F := Under.forget (CommRingCat.of (A ⧸ I))
  have hε : IsIso (F.map ε) := Functor.map_isIso F ε
  let : IsIso (F.map ε) := hε
  let ep : pushout C.obj.hom b ≅ CommRingCat.of V.obj.right := F.mapIso (asIso ε)
  have hp : IsPushout C.obj.hom b (pushout.inl C.obj.hom b)
      (pushout.inr C.obj.hom b) := IsPushout.of_hasPushout _ _
  apply hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ep
  · rfl
  · rfl
  · dsimp [ep, t, quotientLiftCounitRingMap]
    rfl
  · dsimp [ep]
    exact Under.w ε

/-- The counit ring map of the quotient lift is surjective with kernel generated by `I`. -/
private lemma quotientLiftCounitRingMap_surjective_and_ker_le
    {A : Type u} [CommRing A] (I : Ideal A)
    (adj : indEtaleQuotientBaseChange A I ⊣
      indEtaleQuotientLift A I)
    (V : IndEtaleAlgebra (A ⧸ I)) :
    Function.Surjective (quotientLiftCounitRingMap I adj V).hom ∧
      RingHom.ker (quotientLiftCounitRingMap I adj V).hom ≤
        I.map ((indEtaleQuotientLift A I).obj V).obj.hom.hom := by
  classical
  let C := (indEtaleQuotientLift A I).obj V
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let t := quotientLiftCounitRingMap I adj V
  let : Algebra A C.obj.right := C.obj.hom.hom.toAlgebra
  let : Algebra A (A ⧸ I) := (Ideal.Quotient.mk I).toAlgebra
  let : Algebra C.obj.right V.obj.right := t.hom.toAlgebra
  let : Algebra (A ⧸ I) V.obj.right := V.obj.hom.hom.toAlgebra
  let : Algebra A V.obj.right := (C.obj.hom ≫ t).hom.toAlgebra
  have hpush : IsPushout C.obj.hom b t V.obj.hom :=
    quotientLiftCounit_isPushout I adj V
  have hfg : C.obj.hom ≫ t = b ≫ V.obj.hom := hpush.w
  let : IsScalarTower A C.obj.right V.obj.right := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    rfl)
  let : IsScalarTower A (A ⧸ I) V.obj.right := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    have h := congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of V.obj.right => f.hom a)
      hfg
    exact h)
  have hScalarR : IsScalarTower A (A ⧸ I) V.obj.right := inferInstance
  have hScalarC : IsScalarTower A C.obj.right V.obj.right := inferInstance
  let : IsScalarTower A (A ⧸ I) V.obj.right := hScalarR
  let : IsScalarTower A C.obj.right V.obj.right := hScalarC
  have hb : b = CommRingCat.ofHom (algebraMap A (A ⧸ I)) := by ext x; rfl
  have hc : C.obj.hom = CommRingCat.ofHom (algebraMap A C.obj.right) := by ext x; rfl
  have ht : t = CommRingCat.ofHom (algebraMap C.obj.right V.obj.right) := by ext x; rfl
  have hv : V.obj.hom = CommRingCat.ofHom (algebraMap (A ⧸ I) V.obj.right) := by ext x; rfl
  have hcat : IsPushout (CommRingCat.ofHom (algebraMap A (A ⧸ I)))
      (CommRingCat.ofHom (algebraMap A C.obj.right))
      (CommRingCat.ofHom (algebraMap (A ⧸ I) V.obj.right))
      (CommRingCat.ofHom (algebraMap C.obj.right V.obj.right)) := by
    simpa only [hb, hc, hv, ht] using hpush.flip
  have hpushAlg := (@CommRingCat.isPushout_iff_isPushout
    A C.obj.right inferInstance inferInstance inferInstance (A ⧸ I) V.obj.right
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    hScalarR hScalarC).mp hcat
  let e := @Algebra.IsPushout.equiv A (A ⧸ I)
    inferInstance inferInstance inferInstance C.obj.right V.obj.right
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    hScalarC hScalarR hpushAlg
  have he (c : C.obj.right) : e (1 ⊗ₜ[A] c) = t.hom c := by
    have hs := @Algebra.IsPushout.equiv_symm_algebraMap_right A (A ⧸ I)
      inferInstance inferInstance inferInstance C.obj.right V.obj.right
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      hScalarC hScalarR hpushAlg c
    change e (1 ⊗ₜ[A] c) = algebraMap C.obj.right V.obj.right c
    simpa [e] using (congrArg e hs).symm
  refine ⟨fun v => ?_, fun c hc => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨c, hc⟩ := Algebra.TensorProduct.includeRight_surjective C.obj.right
      Ideal.Quotient.mk_surjective x
    exact ⟨c, by rw [← he c]; exact congrArg e hc⟩
  · have hinc : (1 : A ⧸ I) ⊗ₜ[A] c = 0 := by
      apply e.injective
      calc
        e (1 ⊗ₜ[A] c) = t.hom c := he c
        _ = 0 := RingHom.mem_ker.mp hc
        _ = e 0 := by simp
    have hcI : c ∈ I • (⊤ : Submodule A C.obj.right) := by
      have hchar : ((1 : A ⧸ I) ⊗ₜ[A] c = 0) ↔
          c ∈ I • (⊤ : Submodule A C.obj.right) := by
        rw [← (TensorProduct.quotTensorEquivQuotSMul C.obj.right I).map_eq_zero_iff]
        simp only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
          Submodule.Quotient.mk_eq_zero]
      exact hchar.mp hinc
    have hmap : algebraMap A C.obj.right = C.obj.hom.hom := rfl
    have hcI' : c ∈ I.map C.obj.hom.hom := by
      change c ∈ (I.map C.obj.hom.hom).restrictScalars A
      simpa only [Ideal.smul_top_eq_map, hmap] using hcI
    exact hcI'

private lemma quotientLiftCounit_spec_isPullback
    {A : Type u} [CommRing A] (I : Ideal A)
    (adj : indEtaleQuotientBaseChange A I ⊣
      indEtaleQuotientLift A I)
    (V : IndEtaleAlgebra (A ⧸ I)) :
    let C := (indEtaleQuotientLift A I).obj V
    let t := quotientLiftCounitRingMap I adj V
    IsPullback (Scheme.Spec.map t.op)
      (Scheme.Spec.map V.obj.hom.op) (Scheme.Spec.map C.obj.hom.op)
      (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)).op) := by
  classical
  dsimp only
  let C := (indEtaleQuotientLift A I).obj V
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let t := quotientLiftCounitRingMap I adj V
  change IsPullback (Scheme.Spec.map t.op) (Scheme.Spec.map V.obj.hom.op)
    (Scheme.Spec.map C.obj.hom.op) (Scheme.Spec.map b.op)
  exact isPullback_SpecMap_of_isPushout
    C.obj.hom b t V.obj.hom (quotientLiftCounit_isPushout I adj V)

set_option maxHeartbeats 1000000 in
-- the components are built from pushout and adjunction data whose elaboration
-- exceeds the default heartbeat limit
set_option backward.isDefEq.respectTransparency false in
/-- The natural map from an affine ind-étale object over `Z` into its lift over `X`. -/
public noncomputable def closedFiberInclusion (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    (AffineIndEtaleProetale.inclusion B Z ⋙ SmallProetale.inclusion B Z.obj Z.property ⋙
      Over.forget Z ⋙ B.inclusion) ⟶
    (affineIndEtaleLift B i ⋙ AffineIndEtaleProetale.inclusion B X ⋙
      SmallProetale.inclusion B X.obj X.property ⋙ Over.forget X ⋙ B.inclusion) := by
  classical
  let adj := Classical.choice (indEtaleBaseChange_hasFullyFaithfulRightAdjoint
    Γ(X.obj, ⊤) (affineClosedImmersionRingData B i).1)
  refine { app := fun V => ?_, naturality := ?_ }
  · let d := affineClosedImmersionRingData B i
    let V0 := ((affineIndEtaleGlobalSections B Z).obj V).unop
    let V1 := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op V0)).unop
    let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V1
    let t := quotientLiftCounitRingMap d.1 adj V1
    let S := (SmallProetale.toScheme B Z.obj Z.property).obj
      ((AffineIndEtaleProetale.inclusion B Z).obj V)
    letI : IsAffine S := V.property.1
    let eS := S.isoSpec
    change S ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of C.obj.right))
    exact eS.hom ≫ Scheme.Spec.map t.op
  · intro V W f
    let d := affineClosedImmersionRingData B i
    let f₀ := ((affineIndEtaleGlobalSections B Z).map f).unop
    let f₁ := ((rebaseIndEtaleAlongIso d.2).map
      ((affineIndEtaleGlobalSections B Z).map f)).unop
    let g := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).map f₁
    let tV := quotientLiftCounitRingMap d.1 adj
      (((rebaseIndEtaleAlongIso d.2).obj ((affineIndEtaleGlobalSections B Z).obj V)).unop)
    let tW := quotientLiftCounitRingMap d.1 adj
      (((rebaseIndEtaleAlongIso d.2).obj ((affineIndEtaleGlobalSections B Z).obj W)).unop)
    let SV := (SmallProetale.toScheme B Z.obj Z.property).obj
      ((AffineIndEtaleProetale.inclusion B Z).obj V)
    let SW := (SmallProetale.toScheme B Z.obj Z.property).obj
      ((AffineIndEtaleProetale.inclusion B Z).obj W)
    let : IsAffine SV := V.property.1
    let : IsAffine SW := W.property.1
    let fS := (Over.Hom.left f.hom.hom).hom
    have hmap : (affineIndEtaleLift B i ⋙ AffineIndEtaleProetale.inclusion B X ⋙
        SmallProetale.inclusion B X.obj X.property ⋙ Over.forget X ⋙
        B.inclusion).map f = Scheme.Spec.map g.hom.right.op := by
      dsimp [affineIndEtaleLift]
      let F0 := boundedOver B X (affineIndEtaleLiftRawOver B i) (affineIndEtaleLiftRawOver_size B i)
      have hbounded : B.inclusion.map (Over.Hom.left (F0.map f)) =
          Over.Hom.left ((affineIndEtaleLiftRawOver B i).map f) := by
        change B.inclusion.map (B.inclusion.preimage (show
          B.inclusion.obj (F0.obj V).left ⟶ B.inclusion.obj (F0.obj W).left from
            Over.Hom.left ((affineIndEtaleLiftRawOver B i).map f))) = _
        rw [Functor.map_preimage]
      change B.inclusion.map (Over.Hom.left (F0.map f)) = _
      rw [hbounded]
      dsimp [affineIndEtaleLiftRawOver, affineIndEtaleLiftRawOverSpec, affineIndEtaleLiftAlgebra,
        specIndEtaleOver, g, f₀, f₁, affineIndEtaleGlobalSections, rebaseIndEtaleAlongIso]
      apply Spec.homEquiv.injective
      rfl
    change fS ≫ SW.isoSpec.hom ≫ Scheme.Spec.map tW.op =
      SV.isoSpec.hom ≫ Scheme.Spec.map tV.op ≫
        (affineIndEtaleLift B i ⋙ AffineIndEtaleProetale.inclusion B X ⋙
          SmallProetale.inclusion B X.obj X.property ⋙
          Over.forget X ⋙ B.inclusion).map f
    rw [hmap]
    have hspec : SV.isoSpec.hom ≫ Scheme.Spec.map (fS.appTop).op =
        fS ≫ SW.isoSpec.hom := by
      simpa [SV, SW] using Scheme.isoSpec_hom_naturality fS
    calc
      _ = SV.isoSpec.hom ≫ Scheme.Spec.map (fS.appTop).op ≫
          Scheme.Spec.map tW.op := by
            exact congrArg (fun q => q ≫ Scheme.Spec.map tW.op) hspec.symm
      _ = SV.isoSpec.hom ≫ Scheme.Spec.map tV.op ≫
          Scheme.Spec.map g.hom.right.op := by
            rw [← Scheme.Spec.map_comp, ← Scheme.Spec.map_comp]
            have h := quotientLiftCounitRingMap_naturality d.1 adj f₁
            have hSpec := congrArg (fun k => Scheme.Spec.map k.op) h.symm
            have hf : Under.Hom.right f₁.hom = fS.appTop := by
              dsimp [f₁, f₀, fS, affineIndEtaleGlobalSections, rebaseIndEtaleAlongIso]
              rfl
            have hg : Under.Hom.right g.hom = g.hom.right := rfl
            have hSpec' := congrArg (fun q => SV.isoSpec.hom ≫ q) hSpec
            rw [hf, hg] at hSpec'
            simpa only [op_comp, Functor.map_comp, Category.assoc] using
              hSpec'

variable (i : Z ⟶ X) [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]

omit [IsClosedImmersion (B.inclusion.map i)] in
/-- On underlying schemes, affine ind-étale base change is ordinary fibre product. -/
@[stacks 09BK "the base-change comparison"]
public theorem affineIndEtaleBaseChange_comp_forget :
    Nonempty ((affineIndEtaleBaseChange B i ⋙ AffineIndEtaleProetale.inclusion B Z ⋙
      SmallProetale.inclusion B Z.obj Z.property) ≅
      (AffineIndEtaleProetale.inclusion B X ⋙ SmallProetale.inclusion B X.obj X.property ⋙
        Over.pullback i)) := by
  classical
  refine ⟨NatIso.ofComponents (fun U => Iso.refl _) ?_⟩
  intro U V f
  rfl

omit [IsClosedImmersion (B.inclusion.map i)] in
private lemma affineIndEtaleBaseChange_coverPreserving :
    CoverPreserving (AffineIndEtaleProetale.precoverage B X).toGrothendieck
      (AffineIndEtaleProetale.topology B Z) (affineIndEtaleBaseChange B i) := by
  let F := affineIndEtaleBaseChange B i
  let : PreservesLimitsOfShape WalkingCospan
      (AffineIndEtaleProetale.inclusion B X) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B X.obj X.property) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (AffineIndEtaleProetale.inclusion B X ⋙
        SmallProetale.inclusion B X.obj X.property ⋙ Over.pullback i) := inferInstance
  have e : (AffineIndEtaleProetale.inclusion B X ⋙
      SmallProetale.inclusion B X.obj X.property ⋙ Over.pullback i) ≅
      (F ⋙ AffineIndEtaleProetale.inclusion B Z ⋙
        SmallProetale.inclusion B Z.obj Z.property) :=
    NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl
  let := preservesLimitsOfShape_of_natIso (J := WalkingCospan) e
  let T := AffineIndEtaleProetale.inclusion B Z ⋙
    SmallProetale.inclusion B Z.obj Z.property
  have : ReflectsLimitsOfShape WalkingCospan T := by
    apply reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_of_reflects_of_preserves F T
  let : HasPullbacks (AffineIndEtaleProetale B X) := inferInstance
  refine coverPreserving_of_generators F
    (AffineIndEtaleProetale.precoverage B X)
    (AffineIndEtaleProetale.topology B Z) ?_
  intro U R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [← PreZeroHypercover.sieve₀_map]
  apply Precoverage.generate_mem_toGrothendieck
  change (E.map F).presieve₀ ∈ AffineIndEtaleProetale.precoverage B Z (F.obj U)
  change ∃ E' : PreZeroHypercover.{u + 1} (F.obj U),
    (E.map F).presieve₀ = E'.presieve₀ ∧
      AffineIndEtaleProetale.IsCovering B Z ⟨F.obj U, E'⟩
  refine ⟨E.map F, rfl, ?_⟩
  obtain ⟨hE, hfinite⟩ := hE
  change B.covering _ at hE
  obtain ⟨hE, hbound⟩ := (B.covering_iff _).mp hE
  have hbase : B.IsProetaleCovering
      ⟨(Over.forget X).obj ((AffineIndEtaleProetale.inclusion B X ⋙
        SmallProetale.inclusion B X.obj X.property).obj U),
        E.map (AffineIndEtaleProetale.inclusion B X ⋙
          SmallProetale.inclusion B X.obj X.property ⋙ Over.forget X)⟩ := hE
  have hpb := isProetaleCovering_overPullback B i
    (E.map (AffineIndEtaleProetale.inclusion B X ⋙
      SmallProetale.inclusion B X.obj X.property)) hbase
  exact ⟨(B.covering_iff _).2 ⟨hpb, by simpa using hbound⟩, hfinite⟩

private lemma schemeHom_eq_of_appTop {Y X : Scheme.{u}}
    [IsAffine Y] [IsAffine X] (f g : Y ⟶ X) (h : f.appTop = g.appTop) : f = g := by
  have hf : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
    calc
      f = Y.isoSpec.hom ≫ Y.isoSpec.inv ≫ f := by simp
      _ = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
        rw [← Scheme.isoSpec_inv_naturality f]
  have hg : g = Y.isoSpec.hom ≫ Spec.map g.appTop ≫ X.isoSpec.inv := by
    calc
      g = Y.isoSpec.hom ≫ Y.isoSpec.inv ≫ g := by simp
      _ = Y.isoSpec.hom ≫ Spec.map g.appTop ≫ X.isoSpec.inv := by
        rw [← Scheme.isoSpec_inv_naturality g]
  rw [hf, hg, h]

/-- Reading an object of the affine ind-étale site as an ind-étale algebra is full: a map of
algebras of global sections is induced by a morphism of affine schemes, and that morphism is
compatible with the structure morphisms. -/
public lemma affineIndEtaleGlobalSections_full
    (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj] :
    (affineIndEtaleGlobalSections B S).Full := by
  constructor
  intro U V h
  let : IsAffine (B.inclusion.obj S) := by
    change IsAffine S.obj
    infer_instance
  let U0 := (AffineIndEtaleProetale.inclusion B S).obj U
  let V0 := (AffineIndEtaleProetale.inclusion B S).obj V
  let U1 := (SmallProetale.inclusion B S.obj S.property).obj U0
  let V1 := (SmallProetale.inclusion B S.obj S.property).obj V0
  let q : Γ(V1.left.obj, ⊤) →+* Γ(U1.left.obj, ⊤) := h.unop.hom.right.hom
  let : IsAffine (B.inclusion.obj U1.left) := by
    change IsAffine (B.inclusion.obj U.obj.obj.left)
    exact U.property.1
  let : IsAffine (B.inclusion.obj V1.left) := by
    change IsAffine (B.inclusion.obj V.obj.obj.left)
    exact V.property.1
  let : IsAffine U1.left.obj := by
    change IsAffine U.obj.obj.left.obj
    exact U.property.1
  let : IsAffine V1.left.obj := by
    change IsAffine V.obj.obj.left.obj
    exact V.property.1
  let p : B.inclusion.obj U1.left ⟶ B.inclusion.obj V1.left :=
    affineHomOfRingHom q
  have hp : p.appTop.hom = q := affineHomOfRingHom_appTop q
  have hbase : q.comp (B.inclusion.map V1.hom).appTop.hom =
      (B.inclusion.map U1.hom).appTop.hom := by
    have hh := congrArg CommRingCat.Hom.hom (Under.w h.unop.hom)
    change q.comp (B.inclusion.map V1.hom).appTop.hom =
      (B.inclusion.map U1.hom).appTop.hom
    exact hh
  have htop : (p ≫ B.inclusion.map V1.hom).appTop =
      (B.inclusion.map U1.hom).appTop := by
    rw [Scheme.Hom.comp_appTop]
    have hh := congrArg CommRingCat.ofHom hbase
    change CommRingCat.ofHom (Scheme.Hom.appTop (B.inclusion.map V1.hom)).hom ≫
      CommRingCat.ofHom p.appTop.hom =
      CommRingCat.ofHom (Scheme.Hom.appTop (B.inclusion.map U1.hom)).hom
    rw [hp]
    exact hh
  have htriangle : p ≫ B.inclusion.map V1.hom = B.inclusion.map U1.hom :=
    schemeHom_eq_of_appTop _ _ htop
  let pB := B.inclusion.preimage p
  let ov : U1 ⟶ V1 := Over.homMk pB (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    exact htriangle)
  let ovSmall := (SmallProetale.inclusion B S.obj S.property).preimage ov
  let g := (AffineIndEtaleProetale.inclusion B S).preimage ovSmall
  refine ⟨g, ?_⟩
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  change (B.inclusion.map
    (((SmallProetale.inclusion B S.obj S.property).map
      ((AffineIndEtaleProetale.inclusion B S).map g)).left)).appTop.hom = q
  rw [Functor.map_preimage, Functor.map_preimage]
  change (B.inclusion.map pB).appTop.hom = q
  rw [B.inclusion.map_preimage, hp]

/-- Reading an object of the affine ind-étale site as an ind-étale algebra is faithful: a
morphism of affine schemes is determined by its map on global sections. -/
public lemma affineIndEtaleGlobalSections_faithful
    (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj] :
    (affineIndEtaleGlobalSections B S).Faithful := by
  constructor
  intro U V f g h
  let U0 := (AffineIndEtaleProetale.inclusion B S).obj U
  let V0 := (AffineIndEtaleProetale.inclusion B S).obj V
  let U1 := (SmallProetale.inclusion B S.obj S.property).obj U0
  let V1 := (SmallProetale.inclusion B S.obj S.property).obj V0
  let f₀ := (AffineIndEtaleProetale.inclusion B S).map f
  let g₀ := (AffineIndEtaleProetale.inclusion B S).map g
  let f₁ := (SmallProetale.inclusion B S.obj S.property).map f₀
  let g₁ := (SmallProetale.inclusion B S.obj S.property).map g₀
  let fS := B.inclusion.map ((Over.forget S).map f₁)
  let gS := B.inclusion.map ((Over.forget S).map g₁)
  let : IsAffine (B.inclusion.obj ((Over.forget S).obj U1)) := by
    change IsAffine (B.inclusion.obj U.obj.obj.left)
    exact U.property.1
  let : IsAffine (B.inclusion.obj ((Over.forget S).obj V1)) := by
    change IsAffine (B.inclusion.obj V.obj.obj.left)
    exact V.property.1
  have hfgTop : fS.appTop = gS.appTop := by
    change (B.inclusion.map f₁.left).appTop = (B.inclusion.map g₁.left).appTop
    change (affineIndEtaleGlobalSections B S).map f = (affineIndEtaleGlobalSections B S).map g at h
    exact congrArg (fun q => q.unop.hom.right) h
  have hfg : (B.inclusion.obj ((Over.forget S).obj U1)).isoSpec.inv ≫ fS =
      (B.inclusion.obj ((Over.forget S).obj U1)).isoSpec.inv ≫ gS := by
    rw [← Scheme.isoSpec_inv_naturality fS,
      ← Scheme.isoSpec_inv_naturality gS, hfgTop]
  apply (AffineIndEtaleProetale.inclusion B S).map_injective
  apply (SmallProetale.inclusion B S.obj S.property).map_injective
  apply (Over.forget S).map_injective
  apply B.inclusion.map_injective
  exact (cancel_epi (B.inclusion.obj ((Over.forget S).obj U1)).isoSpec.inv).mp hfg

/-- The global sections of the lift along a closed immersion `i : Z ⟶ X` of affine objects:
the ind-étale `Γ(X, ⊤)`-algebra of the lift of `V` is the quotient-lift of the ind-étale
`Γ(Z, ⊤)`-algebra of `V`. -/
public noncomputable def affineIndEtaleLiftGlobalSectionsIso
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (V : AffineIndEtaleProetale B Z) :
    (((affineIndEtaleLift B i ⋙ affineIndEtaleGlobalSections B X).obj V).unop) ≅
      (((affineIndEtaleGlobalSections B Z ⋙
        rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2 ⋙
        (indEtaleQuotientLift Γ(X.obj, ⊤)
          (affineClosedImmersionRingData B i).1).op).obj V).unop) := by
  let d := affineClosedImmersionRingData B i
  let V0 := ((affineIndEtaleGlobalSections B Z).obj V).unop
  let V1 := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op V0)).unop
  let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V1
  let W := ((affineIndEtaleLift B i ⋙ affineIndEtaleGlobalSections B X).obj V).unop
  let eA := Scheme.ΓSpecIso (CommRingCat.of Γ(X.obj, ⊤))
  let eC := Scheme.ΓSpecIso (CommRingCat.of C.obj.right)
  have hspec : X.obj.isoSpec.hom.appTop = eA.hom := by
    change X.obj.toSpecΓ.appTop = eA.hom
    rw [Scheme.toSpecΓ_appTop]
    rfl
  have hbase : X.obj.isoSpec.inv.appTop = eA.inv := by
    apply (cancel_mono eA.hom).mp
    calc
      X.obj.isoSpec.inv.appTop ≫ eA.hom =
          (X.obj.isoSpec.hom ≫ X.obj.isoSpec.inv).appTop := by
        rw [Scheme.Hom.comp_appTop, hspec]
      _ = eA.inv ≫ eA.hom := by
        rw [X.obj.isoSpec.hom_inv_id, Scheme.Hom.id_appTop]
        exact eA.inv_hom_id.symm
  have hraw : ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop =
      X.obj.isoSpec.inv.appTop ≫ (Spec.map C.obj.hom).appTop := by
    change (Spec.map C.obj.hom ≫ X.obj.isoSpec.inv).appTop = _
    rw [Scheme.Hom.comp_appTop]
  have hmaps : (Spec.map C.obj.hom).appTop =
      (Scheme.Spec.map C.obj.hom.op).appTop := rfl
  have hraw' : ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop =
      X.obj.isoSpec.inv.appTop ≫ (Scheme.Spec.map C.obj.hom.op).appTop := by
    rw [hraw, hmaps]
  have hcomm : C.obj.hom ≫ eC.inv =
      ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop := by
    have hfirst : C.obj.hom ≫ eC.inv =
        eA.inv ≫ (Spec.map C.obj.hom).appTop :=
      Scheme.ΓSpecIso_inv_naturality C.obj.hom
    have hsecond : eA.inv ≫ (Spec.map C.obj.hom).appTop =
        ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop := by
      rw [← hbase, hmaps]
      exact hraw'.symm
    exact hfirst.trans hsecond
  have hbounded : (B.inclusion.map ((affineIndEtaleLift B i).obj V).obj.obj.hom).appTop =
      ((affineIndEtaleLiftRawOver B i).obj V).hom.appTop := by
    dsimp [affineIndEtaleLift]
    let Y : B.Scheme := ⟨((affineIndEtaleLiftRawOver B i).obj V).left,
      affineIndEtaleLiftRawOver_size B i V⟩
    change (B.inclusion.map (B.inclusion.preimage (show
      B.inclusion.obj Y ⟶ B.inclusion.obj X from
        ((affineIndEtaleLiftRawOver B i).obj V).hom))).appTop = _
    rw [B.inclusion.map_preimage]
  have hW : C.obj.hom ≫ eC.inv = W.obj.hom := by
    change C.obj.hom ≫ eC.inv = (B.inclusion.map
      ((affineIndEtaleLift B i).obj V).obj.obj.hom).appTop
    rw [hbounded]
    exact hcomm
  have htriangle : W.obj.hom ≫ eC.hom = C.obj.hom := by
    calc
      W.obj.hom ≫ eC.hom = (C.obj.hom ≫ eC.inv) ≫ eC.hom :=
        congrArg (fun f => f ≫ eC.hom) hW.symm
      _ = C.obj.hom := by simp [Category.assoc]
  exact (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of Γ(X.obj, ⊤)))).isoMk (Under.isoMk eC htriangle)

private noncomputable def affineIndEtaleLiftSiteRingIso
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (V : AffineIndEtaleProetale B Z) :
    (((affineIndEtaleLift B i ⋙ affineIndEtaleGlobalSections B X).obj V).unop) ≅
      (((affineIndEtaleGlobalSections B Z ⋙
        rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2 ⋙
        (indEtaleQuotientLift Γ(X.obj, ⊤)
          (affineClosedImmersionRingData B i).1).op).obj V).unop) :=
  affineIndEtaleLiftGlobalSectionsIso B i V

/-- On global sections, the fibre product of an affine ind-étale object over `X` with `Z` is
the pushout. -/
public lemma affineIndEtalePullback_globalSections_isPushout
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj]
    (U : AffineIndEtaleProetale B X) :
    IsPushout (B.inclusion.map U.obj.obj.hom).appTop
      (B.inclusion.map i).appTop
      (B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop
      (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop := by
  let U0 := (AffineIndEtaleProetale.inclusion B X).obj U
  let U1 := (SmallProetale.inclusion B X.obj X.property).obj U0
  let : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
  let : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
  let : IsAffine (B.inclusion.obj U1.left) := by
    change IsAffine (B.inclusion.obj U.obj.obj.left)
    exact U.property.1
  have hpbB := IsPullback.of_hasPullback U1.hom i
  have hpb : IsPullback (B.inclusion.map (pullback.fst U1.hom i))
      (B.inclusion.map (pullback.snd U1.hom i)) (B.inclusion.map U1.hom)
      (B.inclusion.map i) := B.inclusion.map_isPullback hpbB
  simpa [U0, U1] using isPushout_appTop_of_isPullback hpb

/-- The ring of global sections of the base change of `U` along `i` is the quotient base change
of the ring of global sections of `U`, together with the identifications of the two structure
maps with the two pushout inclusions. -/
public noncomputable def affineIndEtaleBaseChangeSiteRingData
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (U : AffineIndEtaleProetale B X) :
    { e : (((affineIndEtaleGlobalSections B X ⋙
      (indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).op).obj U).unop) ≅
      (((affineIndEtaleBaseChange B i ⋙ affineIndEtaleGlobalSections B Z ⋙
        rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).obj U).unop) //
    (pushout.inl (B.inclusion.map U.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right e.hom.hom =
      (B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop) ∧
    ((pushout.inr (B.inclusion.map U.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right e.hom.hom) =
      (affineClosedImmersionRingData B i).2.hom ≫
        (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop) ∧
    ((B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop ≫
      Under.Hom.right e.symm.hom.hom) =
      pushout.inl (B.inclusion.map U.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ∧
    (((affineClosedImmersionRingData B i).2.hom ≫
        (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop) ≫
      Under.Hom.right e.symm.hom.hom) =
      pushout.inr (B.inclusion.map U.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) } := by
  let d := affineClosedImmersionRingData B i
  let P := indEtaleQuotientBaseChange Γ(X.obj, ⊤) d.1
  let Ualg := ((affineIndEtaleGlobalSections B X).obj U).unop
  let L := (P.obj Ualg)
  let Ralg := ((affineIndEtaleGlobalSections B Z).obj ((affineIndEtaleBaseChange B i).obj U)).unop
  let Talg := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op Ralg)).unop
  let A := Γ(X.obj, ⊤)
  let Q := A ⧸ d.1
  let S := Γ(U.obj.obj.left.obj, ⊤)
  let R := Γ(Z.obj, ⊤)
  let T := Γ(((Over.forget Z).obj ((Over.pullback i).obj
    ((SmallProetale.inclusion B X.obj X.property).obj
      ((AffineIndEtaleProetale.inclusion B X).obj U)))).obj, ⊤)
  let b : CommRingCat.of A ⟶ CommRingCat.of Q :=
    CommRingCat.ofHom (Ideal.Quotient.mk d.1)
  let f := (B.inclusion.map U.obj.obj.hom).appTop
  let g := (B.inclusion.map i).appTop
  let f' := (B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop
  let g' := (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop
  let b' : CommRingCat.of Q ⟶ CommRingCat.of T := d.2.hom ≫ g'
  have hdiag : b ≫ d.2.hom = g := by
    dsimp [b, d, affineClosedImmersionRingData, g]
    ext x
    rfl
  have hpush0 : IsPushout f g f' g' := by
    simpa [f, g, f', g'] using affineIndEtalePullback_globalSections_isPushout B i U
  have hpush : IsPushout f b f' b' := by
    refine hpush0.of_iso (Iso.refl _) (Iso.refl _) d.2.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · calc
        g ≫ d.2.symm.hom = (b ≫ d.2.hom) ≫ d.2.symm.hom := by rw [hdiag]
        _ = b := by simp [Category.assoc]
    · simp
    · simp [b']
  have hpushP : IsPushout f b (pushout.inl f b) (pushout.inr f b) :=
    IsPushout.of_hasPushout f b
  let ePT : pushout f b ≅ CommRingCat.of T :=
    hpushP.isoIsPushout _ _ hpush
  have hunder : pushout.inr f b ≫ ePT.hom = b' :=
    hpushP.inr_isoIsPushout_hom _ _ hpush
  let e' : L.obj ≅ Talg.obj := Under.isoMk ePT hunder
  refine ⟨(ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of Q))).isoMk e', ?_⟩
  constructor
  · change pushout.inl f b ≫ ePT.hom = f'
    exact hpushP.inl_isoIsPushout_hom _ _ hpush
  constructor
  · change pushout.inr f b ≫ ePT.hom = b'
    exact hpushP.inr_isoIsPushout_hom _ _ hpush
  constructor
  · change f' ≫ ePT.inv = pushout.inl f b
    exact hpushP.inl_isoIsPushout_inv _ _ hpush
  · change b' ≫ ePT.inv = pushout.inr f b
    exact hpushP.inr_isoIsPushout_inv _ _ hpush

/-- The ring of global sections of the base change of `U` along `i` is the quotient base change
of the ring of global sections of `U`. -/
public noncomputable def affineIndEtaleBaseChangeSiteRingIso
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (U : AffineIndEtaleProetale B X) :
    (((affineIndEtaleGlobalSections B X ⋙
      (indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).op).obj U).unop) ≅
      (((affineIndEtaleBaseChange B i ⋙ affineIndEtaleGlobalSections B Z ⋙
        rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).obj U).unop) :=
  (affineIndEtaleBaseChangeSiteRingData B i U).1

/-- The first pushout inclusion corresponds to the first projection of the fibre product. -/
public lemma affineIndEtaleBaseChangeSiteRingIso_inl
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (U : AffineIndEtaleProetale B X) :
    pushout.inl (B.inclusion.map U.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).hom.hom =
    (B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop :=
  (affineIndEtaleBaseChangeSiteRingData B i U).2.1

/-- The second pushout inclusion corresponds to the second projection of the fibre product. -/
public lemma affineIndEtaleBaseChangeSiteRingIso_inr
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (U : AffineIndEtaleProetale B X) :
    pushout.inr (B.inclusion.map U.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).hom.hom =
    (affineClosedImmersionRingData B i).2.hom ≫
      (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop :=
  (affineIndEtaleBaseChangeSiteRingData B i U).2.2.1

/-- The inverse comparison takes the first projection to the first pushout inclusion. -/
public lemma affineIndEtaleBaseChangeSiteRingIso_inl_inv
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (U : AffineIndEtaleProetale B X) :
    (B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom =
    pushout.inl (B.inclusion.map U.obj.obj.hom).appTop
      (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) :=
  (affineIndEtaleBaseChangeSiteRingData B i U).2.2.2.1

/-- The inverse comparison takes the second projection to the second pushout inclusion. -/
public lemma affineIndEtaleBaseChangeSiteRingIso_inr_inv
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (U : AffineIndEtaleProetale B X) :
    (affineClosedImmersionRingData B i).2.hom ≫
        (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom =
    pushout.inr (B.inclusion.map U.obj.obj.hom).appTop
      (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) :=
  (affineIndEtaleBaseChangeSiteRingData B i U).2.2.2.2

/-- Transport of ind-étale algebras along an isomorphism of base rings is fully faithful, on
the opposite categories. -/
public noncomputable def rebaseIndEtaleAlongIso_fullyFaithful
    {A R : Type u} [CommRing A] [CommRing R]
    (e : CommRingCat.of A ≅ CommRingCat.of R) :
    (rebaseIndEtaleAlongIso e).FullyFaithful := by
  let b := e.hom
  let Psrc : ObjectProperty (Under (CommRingCat.of R)) :=
    ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
      (X := CommRingCat.of R))
  let Ptar : ObjectProperty (Under (CommRingCat.of A)) :=
    ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
      (X := CommRingCat.of A))
  let G : IndEtaleAlgebra R ⥤ IndEtaleAlgebra A :=
    Ptar.lift (Psrc.ι ⋙ Under.map b) (by
      intro V
      let : IsIso b := by dsimp [b]; infer_instance
      let : Algebra A R := b.hom.toAlgebra
      let : Algebra R V.obj.right := V.obj.hom.hom.toAlgebra
      let : Algebra A V.obj.right := (V.obj.hom.hom.comp b.hom).toAlgebra
      let : IsScalarTower A R V.obj.right := IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        rfl)
      let : CommRingCat.etale.ContainsIdentities := ⟨fun _ => by
        rw [CommRingCat.etale_iff]
        exact RingHom.etale_algebraMap.2 (inferInstance : Algebra.Etale _ _)⟩
      have hbEtale : CommRingCat.etale b := CommRingCat.etale.of_isIso b
      have hbRing : MorphismProperty.ind.{u} CommRingCat.etale b :=
        (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale) (f := b)).mpr
          (ObjectProperty.le_ind _ _ hbEtale)
      have hbAlg : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A R) :=
        CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hbRing
      have hVRing : MorphismProperty.ind.{u} CommRingCat.etale V.obj.hom :=
        (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale)
          (f := V.obj.hom)).mpr V.property
      have hVAlg : (CommAlgCat.etale R).ind.{u}
          (CommAlgCat.of R V.obj.right) :=
        CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hVRing
      have hcomp := CommAlgCat.ind_etale_comp hbAlg hVAlg
      have hcompRing : MorphismProperty.ind.{u} CommRingCat.etale
          (b ≫ V.obj.hom) := by
        rw [show b ≫ V.obj.hom =
          CommRingCat.ofHom (algebraMap A V.obj.right) from by
            ext x
            exact (IsScalarTower.algebraMap_apply A R V.obj.right x).symm]
        exact CommAlgCat.ind_etale_iff_ind_algebraMap.mp hcomp
      exact (MorphismProperty.ind_iff_ind_underMk
        (P := CommRingCat.etale) (f := b ≫ V.obj.hom)).mp hcompRing)
  haveI : (Under.map b).IsEquivalence := by
    dsimp [b]
    infer_instance
  have hsrc : Psrc.ι.FullyFaithful := Psrc.fullyFaithfulι
  have hmap : (Under.map b).FullyFaithful :=
    (Under.mapIso (asIso b)).fullyFaithfulFunctor
  haveI : (Psrc.ι ⋙ Under.map b).FullyFaithful := hsrc.comp hmap
  haveI : Ptar.ι.Faithful := Ptar.faithful_ι
  have hGincl : (G ⋙ Ptar.ι).FullyFaithful := by
    change (Psrc.ι ⋙ Under.map b).FullyFaithful
    exact hsrc.comp hmap
  have hG : G.FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (F := G) (G := Ptar.ι) hGincl
  dsimp [rebaseIndEtaleAlongIso, b]
  exact Functor.FullyFaithful.op (F := G) hG

set_option backward.isDefEq.respectTransparency false in
private noncomputable def affineIndEtaleLiftSiteRingCommutingIso
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    (affineIndEtaleGlobalSections B Z ⋙
      rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2 ⋙
      (indEtaleQuotientLift Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).op) ≅
      (affineIndEtaleLift B i ⋙ affineIndEtaleGlobalSections B X) := by
  refine NatIso.ofComponents (fun V => ?_) ?_
  · exact (affineIndEtaleLiftSiteRingIso B i V).op
  · intro V W f
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    let d := affineClosedImmersionRingData B i
    let f₀ := ((affineIndEtaleGlobalSections B Z).map f).unop
    let f₁ := ((rebaseIndEtaleAlongIso d.2).map
      ((affineIndEtaleGlobalSections B Z).map f)).unop
    let g := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).map f₁
    have hmap : (affineIndEtaleLift B i ⋙ AffineIndEtaleProetale.inclusion B X ⋙
        SmallProetale.inclusion B X.obj X.property ⋙ Over.forget X ⋙
        B.inclusion).map f = Scheme.Spec.map g.hom.right.op := by
      dsimp [affineIndEtaleLift]
      let F0 := boundedOver B X (affineIndEtaleLiftRawOver B i) (affineIndEtaleLiftRawOver_size B i)
      have hbounded : B.inclusion.map (Over.Hom.left (F0.map f)) =
          Over.Hom.left ((affineIndEtaleLiftRawOver B i).map f) := by
        change B.inclusion.map (B.inclusion.preimage (show
          B.inclusion.obj (F0.obj V).left ⟶ B.inclusion.obj (F0.obj W).left from
            Over.Hom.left ((affineIndEtaleLiftRawOver B i).map f))) = _
        rw [Functor.map_preimage]
      change B.inclusion.map (Over.Hom.left (F0.map f)) = _
      rw [hbounded]
      dsimp [affineIndEtaleLiftRawOver, affineIndEtaleLiftRawOverSpec, affineIndEtaleLiftAlgebra,
        specIndEtaleOver, g, f₀, f₁, affineIndEtaleGlobalSections, rebaseIndEtaleAlongIso]
      apply Spec.homEquiv.injective
      rfl
    have htop := congrArg Scheme.Hom.appTop hmap
    simp only [Functor.comp_map, Functor.op_map,
      CategoryTheory.unop_comp, ObjectProperty.FullSubcategory.comp_hom,
      Under.comp_right,
      Quiver.Hom.unop_op, affineIndEtaleGlobalSections_map_right] at ⊢
    have hschemeMap : B.inclusion.map (Over.Hom.left
        ((SmallProetale.inclusion B X.obj X.property).map
          ((AffineIndEtaleProetale.inclusion B X).map ((affineIndEtaleLift B i).map f)))) =
        (affineIndEtaleLift B i ⋙ AffineIndEtaleProetale.inclusion B X ⋙
          SmallProetale.inclusion B X.obj X.property ⋙
          Over.forget X ⋙ B.inclusion).map f := by
      rfl
    rw [congrArg Scheme.Hom.appTop hschemeMap]
    rw [htop]
    exact (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_naturality g.hom.right)).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 10000000 in
-- the naturality proof unfolds the quotient base change through pullbacks of affine
-- schemes, which exceeds the default heartbeat limit
private noncomputable def affineIndEtaleBaseChangeSiteRingCommutingIso
    (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    (affineIndEtaleGlobalSections B X ⋙
      (indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).op) ≅
    (affineIndEtaleBaseChange B i ⋙ affineIndEtaleGlobalSections B Z ⋙
        rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2) := by
  refine NatIso.ofComponents (fun U => ?_) ?_
  · change Opposite.op (((affineIndEtaleGlobalSections B X ⋙
        (indEtaleQuotientBaseChange Γ(X.obj, ⊤)
          (affineClosedImmersionRingData B i).1).op).obj U).unop) ≅
      Opposite.op (((affineIndEtaleBaseChange B i ⋙ affineIndEtaleGlobalSections B Z ⋙
        rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).obj U).unop)
    exact (affineIndEtaleBaseChangeSiteRingIso B i U).symm.op
  · intro U V f
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    let eU := affineIndEtaleBaseChangeSiteRingIso B i U
    let eV := affineIndEtaleBaseChangeSiteRingIso B i V
    have hright : IsIso (Under.Hom.right eV.hom.hom) := by
      let P := ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
        (X := CommRingCat.of (Γ(X.obj, ⊤) ⧸
          (affineClosedImmersionRingData B i).1)))
      have h₁ : IsIso (P.ι.map eV.hom) := Functor.map_isIso P.ι eV.hom
      have h₂ : IsIso ((Under.forget _).map (P.ι.map eV.hom)) :=
        Functor.map_isIso (Under.forget _) (P.ι.map eV.hom)
      change IsIso (Under.Hom.right eV.hom.hom) at h₂
      exact h₂
    let := hright
    let : Epi (Under.Hom.right eV.hom.hom) := by infer_instance
    have hcancel : Under.Hom.right eV.hom.hom ≫
        Under.Hom.right eV.symm.hom.hom = 𝟙 _ := by
      exact congrArg (fun q => Under.Hom.right q.hom) eV.hom_inv_id
    have hcancel' : Under.Hom.right eV.hom.hom ≫
        Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i V).symm.op.hom.unop.hom = 𝟙 _ := by
      simp [eV, Quiver.Hom.unop_op]
    simp only [Functor.comp_map, Functor.op_map, CategoryTheory.unop_comp,
      id_def,
      ObjectProperty.FullSubcategory.comp_hom,
      Under.comp_right, Quiver.Hom.unop_op] at ⊢
    have hInvU : Under.Hom.right
        (affineIndEtaleBaseChangeSiteRingIso B i U).op.inv.unop.hom =
        Under.Hom.right eU.symm.hom.hom := by
      simp [eU, Quiver.Hom.unop_op]
    let : Mono (Under.Hom.right eU.symm.hom.hom) := by infer_instance
    apply (cancel_epi (Under.Hom.right eV.hom.hom)).mp
    apply pushout.hom_ext
    · rw [← Category.assoc (f := Under.Hom.right eV.hom.hom)
        (g := Under.Hom.right
          (affineIndEtaleBaseChangeSiteRingIso B i V).symm.op.hom.unop.hom), hcancel']
      rw [Category.id_comp]
      have hbc : pushout.inl
          ((CommRingCat.etale.underObj.ind.ι.obj
            (((affineIndEtaleGlobalSections B X).obj V).unop)).hom)
            (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1) ) ≫
          Under.Hom.right
            ((indEtaleQuotientBaseChange Γ(X.obj, ⊤)
              (affineClosedImmersionRingData B i).1).map
                ((affineIndEtaleGlobalSections B X).map f).unop).hom =
          Under.Hom.right (((affineIndEtaleGlobalSections B X).map f).unop.hom) ≫
            pushout.inl ((CommRingCat.etale.underObj.ind.ι.obj
              (((affineIndEtaleGlobalSections B X).obj U).unop)).hom)
            (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) := by
        dsimp [indEtaleQuotientBaseChange]
        change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
        exact pushout.inl_desc _ _ (by
          dsimp [Under.pushout]
          rw [← Category.assoc]
          rw [Under.w ((affineIndEtaleGlobalSections B X).map f).unop.hom]
          exact pushout.condition)
      have hInlV : pushout.inl
          (((affineIndEtaleGlobalSections B X).obj V).unop.obj.hom)
            (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
          Under.Hom.right eV.hom.hom =
            (B.inclusion.map (pullback.fst V.obj.obj.hom i)).appTop := by
        exact affineIndEtaleBaseChangeSiteRingIso_inl B i V
      have hInlU : (B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop ≫
          Under.Hom.right eU.symm.hom.hom =
            pushout.inl (((affineIndEtaleGlobalSections B X).obj U).unop.obj.hom)
              (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) := by
        exact affineIndEtaleBaseChangeSiteRingIso_inl_inv B i U
      rw [hbc]
      dsimp [indEtaleQuotientBaseChange, Under.pushout] at ⊢
      rw [← Category.assoc, hInlV]
      rw [← hInlU]
      simp only [← Category.assoc]
      rw [hInvU]
      apply (cancel_mono (Under.Hom.right eU.symm.hom.hom)).mpr
      simp only [affineIndEtaleGlobalSections, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        CommRingCat.ofHom_hom, Lean.Elab.WF.paramLet, Under.mk_right, affineIndEtaleBaseChange,
        rebaseIndEtaleAlongIso, Functor.comp_obj, ObjectProperty.lift_obj_obj,
        Over.pullback_obj_left, Over.pullback_obj_hom, Functor.op_obj, Under.map_obj_right,
        Quiver.Hom.unop_op', ObjectProperty.homMk_hom, Under.homMk_right, pullback.fst,
        ObjectProperty.lift_map, Functor.comp_map, Over.pullback_map_left, Functor.op_map,
        Quiver.Hom.unop_op, Under.map_map_right]
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg (fun q => (B.inclusion.map q).appTop)
        (pullback.lift_fst
          (pullback.fst (Over.hom U.obj.obj) i ≫ Over.Hom.left f.hom.hom)
          (pullback.snd (Over.hom U.obj.obj) i)
          (by
            calc
              (pullback.fst (Over.hom U.obj.obj) i ≫ Over.Hom.left f.hom.hom) ≫
                  Over.hom V.obj.obj =
                pullback.fst (Over.hom U.obj.obj) i ≫ Over.hom U.obj.obj := by
                  rw [Category.assoc, Over.w f.hom.hom]
              _ = pullback.snd (Over.hom U.obj.obj) i ≫ i := pullback.condition)).symm
    · rw [← Category.assoc (f := Under.Hom.right eV.hom.hom)
        (g := Under.Hom.right
          (affineIndEtaleBaseChangeSiteRingIso B i V).symm.op.hom.unop.hom), hcancel']
      rw [Category.id_comp]
      have hbc : pushout.inr
          ((CommRingCat.etale.underObj.ind.ι.obj
            (((affineIndEtaleGlobalSections B X).obj V).unop)).hom)
            (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
          Under.Hom.right
            ((indEtaleQuotientBaseChange Γ(X.obj, ⊤)
              (affineClosedImmersionRingData B i).1).map
                ((affineIndEtaleGlobalSections B X).map f).unop).hom =
          pushout.inr ((CommRingCat.etale.underObj.ind.ι.obj
            (((affineIndEtaleGlobalSections B X).obj U).unop)).hom)
            (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) := by
        dsimp [indEtaleQuotientBaseChange]
        change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
        exact pushout.inr_desc _ _ (by
          dsimp [Under.pushout]
          rw [← Category.assoc]
          rw [Under.w ((affineIndEtaleGlobalSections B X).map f).unop.hom]
          exact pushout.condition)
      have hInrV : pushout.inr
          (((affineIndEtaleGlobalSections B X).obj V).unop.obj.hom)
            (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
          Under.Hom.right eV.hom.hom =
            (affineClosedImmersionRingData B i).2.hom ≫
              (B.inclusion.map (pullback.snd V.obj.obj.hom i)).appTop := by
        exact affineIndEtaleBaseChangeSiteRingIso_inr B i V
      have hInrU : (affineClosedImmersionRingData B i).2.hom ≫
          (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop ≫
          Under.Hom.right eU.symm.hom.hom =
            pushout.inr (((affineIndEtaleGlobalSections B X).obj U).unop.obj.hom)
              (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) := by
        exact affineIndEtaleBaseChangeSiteRingIso_inr_inv B i U
      rw [hbc]
      dsimp [indEtaleQuotientBaseChange, Under.pushout] at ⊢
      rw [← Category.assoc, hInrV]
      simp only [← hInrU]
      simp only [← Category.assoc]
      rw [hInvU]
      apply (cancel_mono (Under.Hom.right eU.symm.hom.hom)).mpr
      simp only [affineIndEtaleBaseChange, affineIndEtaleGlobalSections, ObjectProperty.ι_obj,
        ObjectProperty.ι_map, CommRingCat.ofHom_hom, Lean.Elab.WF.paramLet, rebaseIndEtaleAlongIso,
        Functor.comp_obj, ObjectProperty.lift_obj_obj, Over.pullback_obj_left,
        Over.pullback_obj_hom, pullback.snd, Functor.op_obj, Under.map_obj_right, Under.mk_right,
        ObjectProperty.lift_map, Functor.comp_map, ObjectProperty.homMk_hom, Over.pullback_map_left,
        Functor.op_map, Quiver.Hom.unop_op', Quiver.Hom.unop_op, Under.map_map_right,
        Under.homMk_right, Category.assoc, Iso.cancel_iso_hom_left]
      rw [← Scheme.Hom.comp_appTop]
      exact congrArg (fun q => (B.inclusion.map q).appTop)
        (pullback.lift_snd _ _ _).symm

private def homEquivPrecomposeIso {C : Type*} [Category C]
    {X X' Y : C} (e : X ≅ X') : (X' ⟶ Y) ≃ (X ⟶ Y) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := by simp
  right_inv f := by simp

private def homEquivPostcomposeIso {C : Type*} [Category C]
    {X Y Y' : C} (e : Y ≅ Y') : (X ⟶ Y) ≃ (X ⟶ Y') where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp

set_option maxHeartbeats 1000000 in
-- assembling the adjunction from the ring-level adjunction unfolds large `let`-bound
-- functor composites, which exceeds the default heartbeat limit
/-- The lift is left adjoint to base change. -/
@[stacks 09BK]
public theorem affineIndEtaleLift_adj_baseChange :
    Nonempty (affineIndEtaleLift B i ⊣ affineIndEtaleBaseChange B i) := by
  classical
  let RX := affineIndEtaleGlobalSections B X
  let RZ := affineIndEtaleGlobalSections B Z
  let d := affineClosedImmersionRingData B i
  let rb := rebaseIndEtaleAlongIso d.2
  let bc := indEtaleQuotientBaseChange Γ(X.obj, ⊤) d.1
  let lift := indEtaleQuotientLift Γ(X.obj, ⊤) d.1
  have hRX : RX.FullyFaithful := by
    let : RX.Full := affineIndEtaleGlobalSections_full B X
    let : RX.Faithful := affineIndEtaleGlobalSections_faithful B X
    exact .ofFullyFaithful RX
  have hRZ : RZ.FullyFaithful := by
    let : RZ.Full := affineIndEtaleGlobalSections_full B Z
    let : RZ.Faithful := affineIndEtaleGlobalSections_faithful B Z
    exact .ofFullyFaithful RZ
  have hRb : rb.FullyFaithful := rebaseIndEtaleAlongIso_fullyFaithful d.2
  have hRZrb : (RZ ⋙ rb).FullyFaithful := hRZ.comp hRb
  obtain ⟨ringAdj⟩ :=
    indEtaleBaseChange_hasFullyFaithfulRightAdjoint Γ(X.obj, ⊤) d.1
  let ringAdjOp : lift.op ⊣ bc.op := ringAdj.op
  let α := affineIndEtaleLiftSiteRingCommutingIso B i
  let β := affineIndEtaleBaseChangeSiteRingCommutingIso B i
  let core : Adjunction.CoreHomEquiv (affineIndEtaleLift B i) (affineIndEtaleBaseChange B i) := {
    homEquiv := fun V U =>
      ((Functor.FullyFaithful.homEquiv hRX
          (X := (affineIndEtaleLift B i).obj V) (Y := U)).trans
        (homEquivPrecomposeIso (α.app V))).trans
          ((ringAdjOp.homEquiv (rb.obj (RZ.obj V)) (RX.obj U)).trans
            ((homEquivPostcomposeIso (β.app U)).trans
              (Functor.FullyFaithful.homEquiv hRZrb
                (X := V) (Y := (affineIndEtaleBaseChange B i).obj U)).symm))
    homEquiv_naturality_left_symm := by
      intro V' V U f g
      apply (hRX.map_injective (X := (affineIndEtaleLift B i).obj V') (Y := U))
      simp only [Functor.map_comp,
        Equiv.symm_trans_apply]
      simp only [Equiv.symm_symm_apply, homEquivPrecomposeIso,
        homEquivPostcomposeIso,
        Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_symm_apply] at ⊢
      simp only [Functor.map_comp]
      dsimp [homEquivPrecomposeIso, homEquivPostcomposeIso] at ⊢
      rw [Category.assoc]
      rw [ringAdjOp.homEquiv_naturality_left_symm
        (rb.map (RZ.map f)) (rb.map (RZ.map g) ≫ β.inv.app U)]
      have hα : α.inv.app V' ≫ lift.op.map (rb.map (RZ.map f)) =
          RX.map ((affineIndEtaleLift B i).map f) ≫ α.inv.app V := by
        simpa only [Functor.comp_map] using (α.inv.naturality f).symm
      rw [← Category.assoc, hα, Category.assoc]
      rw [← Functor.map_comp]
      have hcomp : hRX.preimage
          (RX.map ((affineIndEtaleLift B i).map f) ≫
            (α.inv.app V ≫
              (ringAdjOp.homEquiv (rb.obj (RZ.obj V)) (RX.obj U)).symm
                (rb.map (RZ.map g) ≫ β.inv.app U))) =
          (affineIndEtaleLift B i).map f ≫ hRX.preimage
            (α.inv.app V ≫
              (ringAdjOp.homEquiv (rb.obj (RZ.obj V)) (RX.obj U)).symm
                (rb.map (RZ.map g) ≫ β.inv.app U)) := by
        apply hRX.map_injective
        simp only [hRX.map_preimage, Functor.map_comp]
      rw [hcomp]
    homEquiv_naturality_right := by
      intro V U U' f g
      apply hRZrb.map_injective
      simp only [Functor.map_comp, Equiv.trans_apply,
        ]
      simp only [homEquivPrecomposeIso,
        homEquivPostcomposeIso,
        Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_symm_apply] at ⊢
      simp only [Functor.map_comp]
      dsimp [homEquivPrecomposeIso, homEquivPostcomposeIso] at ⊢
      rw [← Category.assoc]
      rw [ringAdjOp.homEquiv_naturality_right
        (α.hom.app V ≫ RX.map f) (RX.map g)]
      have hβ : bc.op.map (RX.map g) ≫ β.hom.app U' =
          β.hom.app U ≫
            (affineIndEtaleBaseChange B i ⋙ affineIndEtaleGlobalSections B Z ⋙ rb).map g := by
        simpa only [Functor.comp_map] using β.hom.naturality g
      simp only [Category.assoc, hβ,
        Functor.comp_map]
      have hpre : hRZrb.preimage
          ((ringAdjOp.homEquiv (rb.obj (RZ.obj V)) (RX.obj U)
              (α.hom.app V ≫ RX.map f) ≫ β.hom.app U) ≫
            (RZ ⋙ rb).map ((affineIndEtaleBaseChange B i).map g)) =
          hRZrb.preimage
              (ringAdjOp.homEquiv (rb.obj (RZ.obj V)) (RX.obj U)
                (α.hom.app V ≫ RX.map f) ≫ β.hom.app U) ≫
            (affineIndEtaleBaseChange B i).map g := by
        apply hRZrb.map_injective
        simp only [hRZrb.map_preimage, Functor.map_comp]
      change (RZ ⋙ rb).map (hRZrb.preimage
          ((ringAdjOp.homEquiv (rb.obj (RZ.obj V)) (RX.obj U)
              (α.hom.app V ≫ RX.map f) ≫ β.hom.app U) ≫
            (RZ ⋙ rb).map ((affineIndEtaleBaseChange B i).map g))) =
        (RZ ⋙ rb).map (hRZrb.preimage
            (ringAdjOp.homEquiv (rb.obj (RZ.obj V)) (RX.obj U)
              (α.hom.app V ≫ RX.map f) ≫ β.hom.app U) ≫
          (affineIndEtaleBaseChange B i).map g)
      simp only [hRZrb.map_preimage, Functor.map_comp]
  }
  exact ⟨Adjunction.mkOfHomEquiv core⟩

set_option backward.isDefEq.respectTransparency false in
/-- The natural inclusion identifies an object with the closed fibre of its lift. -/
@[stacks 09BK]
public theorem closedFiberInclusion_isPullback
    (V : AffineIndEtaleProetale B Z) :
    IsPullback ((closedFiberInclusion B i).app V) (B.inclusion.map V.obj.obj.hom)
      (B.inclusion.map ((affineIndEtaleLift B i).obj V).obj.obj.hom) (B.inclusion.map i) := by
  classical
  let d := affineClosedImmersionRingData B i
  let adj := Classical.choice
    (indEtaleBaseChange_hasFullyFaithfulRightAdjoint Γ(X.obj, ⊤) d.1)
  let V0 := ((affineIndEtaleGlobalSections B Z).obj V).unop
  let V1 := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op V0)).unop
  let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V1
  let t := quotientLiftCounitRingMap d.1 adj V1
  let S := (SmallProetale.toScheme B Z.obj Z.property).obj
    ((AffineIndEtaleProetale.inclusion B Z).obj V)
  let T := (SmallProetale.toScheme B X.obj X.property).obj
    ((AffineIndEtaleProetale.inclusion B X).obj ((affineIndEtaleLift B i).obj V))
  let : IsAffine S := V.property.1
  let : IsAffine T := ((affineIndEtaleLift B i).obj V).property.1
  let h := quotientLiftCounit_spec_isPullback d.1 adj V1
  let e₁ : Scheme.Spec.obj (Opposite.op (CommRingCat.of V1.obj.right)) ≅ S := by
    dsimp [V1, V0, rebaseIndEtaleAlongIso, affineIndEtaleGlobalSections]
    exact S.isoSpec.symm
  let e₂ : Scheme.Spec.obj (Opposite.op (CommRingCat.of C.obj.right)) ≅ T := by
    change Scheme.Spec.obj (Opposite.op (CommRingCat.of C.obj.right)) ≅
      Scheme.Spec.obj (Opposite.op (CommRingCat.of C.obj.right))
    exact Iso.refl _
  let e₃ : Scheme.Spec.obj (Opposite.op (CommRingCat.of (Γ(X.obj, ⊤) ⧸ d.1))) ≅ Z.obj :=
    Scheme.Spec.mapIso d.2.symm.op ≪≫ Z.obj.isoSpec.symm
  let e₄ : Scheme.Spec.obj (Opposite.op (CommRingCat.of Γ(X.obj, ⊤))) ≅ X.obj :=
    X.obj.isoSpec.symm
  apply h.of_iso e₁ e₂ e₃ e₄
  · change Scheme.Spec.map t.op ≫ 𝟙 _ =
      S.isoSpec.inv ≫ S.isoSpec.hom ≫ Scheme.Spec.map t.op
    simp
  · dsimp [e₁, e₃]
    let : IsAffine (B.inclusion.obj V.obj.obj.left) := V.property.1
    let : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
    have hRing : d.2.symm.hom ≫ V1.obj.hom = (B.inclusion.map V.obj.obj.hom).appTop := by
      ext x
      simp [V1, V0, d, affineClosedImmersionRingData,
        rebaseIndEtaleAlongIso, affineIndEtaleGlobalSections]
    calc
      Scheme.Spec.map V1.obj.hom.op ≫ Scheme.Spec.map d.2.symm.hom.op ≫ Z.obj.isoSpec.inv =
          Scheme.Spec.map (d.2.symm.hom ≫ V1.obj.hom).op ≫ Z.obj.isoSpec.inv := by
            calc
              _ = Scheme.Spec.map (V1.obj.hom.op ≫ d.2.symm.hom.op) ≫
                    Z.obj.isoSpec.inv := by
                      have hm : Scheme.Spec.map V1.obj.hom.op ≫
                          Scheme.Spec.map d.2.symm.hom.op =
                            Scheme.Spec.map (V1.obj.hom.op ≫ d.2.symm.hom.op) := by
                        rw [← Scheme.Spec.map_comp]
                      exact congrArg (fun q => q ≫ Z.obj.isoSpec.inv) hm
              _ = Scheme.Spec.map (d.2.symm.hom ≫ V1.obj.hom).op ≫
                    Z.obj.isoSpec.inv := by rw [op_comp]
      _ = Scheme.Spec.map ((B.inclusion.map V.obj.obj.hom).appTop).op ≫
          Z.obj.isoSpec.inv := by rw [hRing]
      _ = S.isoSpec.inv ≫ (Over.hom V.obj.obj).hom := by
        simpa [S] using Scheme.isoSpec_inv_naturality (B.inclusion.map V.obj.obj.hom)
  · let Y : B.Scheme := ((affineIndEtaleLift B i).obj V).obj.obj.left
    change Scheme.Spec.map C.obj.hom.op ≫ X.obj.isoSpec.inv =
      B.inclusion.map (B.inclusion.preimage (show
        B.inclusion.obj Y ⟶ B.inclusion.obj X from
          Scheme.Spec.map C.obj.hom.op ≫ X.obj.isoSpec.inv))
    rw [B.inclusion.map_preimage]
  · dsimp [e₃, e₄]
    let : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
    let : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
    let f := (B.inclusion.map i).appTop
    let hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (B.inclusion.map i)).2
    have hRing : f ≫ d.2.inv = CommRingCat.ofHom (Ideal.Quotient.mk d.1) := by
      ext x
      change (RingHom.quotientKerEquivOfSurjective
        (f := f.hom) hsurj).symm (f.hom x) =
          Ideal.Quotient.mk (RingHom.ker f.hom) x
      exact RingHom.quotientKerEquivOfSurjective_symm_apply hsurj x
    have hSpec : Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk d.1)).op =
        Scheme.Spec.map d.2.inv.op ≫ Scheme.Spec.map f.op := by
      calc
        _ = Scheme.Spec.map (f ≫ d.2.inv).op := by rw [hRing]
        _ = Scheme.Spec.map (d.2.inv.op ≫ f.op) := by rw [op_comp]
        _ = Scheme.Spec.map d.2.inv.op ≫ Scheme.Spec.map f.op := by rw [Functor.map_comp]
    calc
      Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk d.1)).op ≫ X.obj.isoSpec.inv =
          Scheme.Spec.map d.2.inv.op ≫ Scheme.Spec.map f.op ≫ X.obj.isoSpec.inv := by
            rw [hSpec]
            simp [Category.assoc]
      _ = Scheme.Spec.map d.2.inv.op ≫ Z.obj.isoSpec.inv ≫ i.hom := by
          simpa [f] using congrArg
            (fun q => Scheme.Spec.map d.2.inv.op ≫ q)
            (Scheme.isoSpec_inv_naturality i.hom)

private lemma closedFiberInclusion_isPullback_internal
    (V : AffineIndEtaleProetale B Z) :
    IsPullback (B.inclusion.preimage (show
      B.inclusion.obj V.obj.obj.left ⟶
        B.inclusion.obj ((affineIndEtaleLift B i).obj V).obj.obj.left from
          (closedFiberInclusion B i).app V))
      V.obj.obj.hom ((affineIndEtaleLift B i).obj V).obj.obj.hom i := by
  apply IsPullback.of_map_of_faithful B.inclusion
  simpa only [B.inclusion.map_preimage] using
    (closedFiberInclusion_isPullback B i V)

private noncomputable def affineIndEtaleLiftBaseChangeIsoComponent
    (V : AffineIndEtaleProetale B Z) :
    ((affineIndEtaleLift B i ⋙ affineIndEtaleBaseChange B i).obj V) ≅ V := by
  let T : AffineIndEtaleProetale B Z ⥤ BigProetaleOver B Z.obj Z.property :=
    AffineIndEtaleProetale.inclusion B Z ⋙
      SmallProetale.inclusion B Z.obj Z.property
  let h := closedFiberInclusion_isPullback_internal B i V
  let e : V.obj.obj.left ≅ pullback
      ((affineIndEtaleLift B i).obj V).obj.obj.hom i :=
    h.isoIsPullback _ _ (IsPullback.of_hasPullback
      ((affineIndEtaleLift B i).obj V).obj.obj.hom i)
  let eOver : Over.mk V.obj.obj.hom ≅
      Over.mk (pullback.snd ((affineIndEtaleLift B i).obj V).obj.obj.hom i) :=
    Over.isoMk e (by
      exact h.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback
        ((affineIndEtaleLift B i).obj V).obj.obj.hom i))
  have eBase : T.obj ((affineIndEtaleBaseChange B i).obj ((affineIndEtaleLift B i).obj V)) ≅
      (AffineIndEtaleProetale.inclusion B X ⋙
        SmallProetale.inclusion B X.obj X.property ⋙
          Over.pullback i).obj ((affineIndEtaleLift B i).obj V) :=
    (affineIndEtaleBaseChange_comp_forget B i).some.app ((affineIndEtaleLift B i).obj V)
  haveI : T.Full := inferInstance
  haveI : T.Faithful := inferInstance
  exact T.preimageIso (eBase ≪≫ eOver.symm)

/-- Base change of the lift is canonically the original object, naturally in that object. -/
@[stacks 09BK]
public theorem affineIndEtaleLift_baseChangeIso :
    Nonempty (affineIndEtaleLift B i ⋙ affineIndEtaleBaseChange B i ≅
      𝟭 (AffineIndEtaleProetale B Z)) := by
  classical
  refine ⟨NatIso.ofComponents (affineIndEtaleLiftBaseChangeIsoComponent B i) ?_⟩
  intro V W f
  let T : AffineIndEtaleProetale B Z ⥤ BigProetaleOver B Z.obj Z.property :=
    AffineIndEtaleProetale.inclusion B Z ⋙
      SmallProetale.inclusion B Z.obj Z.property
  let TX : AffineIndEtaleProetale B X ⥤ BigProetaleOver B X.obj X.property :=
    AffineIndEtaleProetale.inclusion B X ⋙
      SmallProetale.inclusion B X.obj X.property
  have : T.Full := inferInstance
  have : T.Faithful := inferInstance
  let hpb (U : AffineIndEtaleProetale B Z) :=
    closedFiberInclusion_isPullback_internal B i U
  let p (U : AffineIndEtaleProetale B Z) :=
    IsPullback.of_hasPullback ((affineIndEtaleLift B i).obj U).obj.obj.hom i
  let e (U : AffineIndEtaleProetale B Z) :=
    (hpb U).isoIsPullback _ _ (p U)
  let eOver (U : AffineIndEtaleProetale B Z) :
      Over.mk U.obj.obj.hom ≅
        Over.mk (pullback.snd ((affineIndEtaleLift B i).obj U).obj.obj.hom i) :=
    Over.isoMk (e U) (by
      exact (hpb U).isoIsPullback_hom_snd _ _ (p U))
  let eBase (U : AffineIndEtaleProetale B Z) :=
    (affineIndEtaleBaseChange_comp_forget B i).some.app ((affineIndEtaleLift B i).obj U)
  have hmap (U : AffineIndEtaleProetale B Z) :
      T.map (affineIndEtaleLiftBaseChangeIsoComponent B i U).hom =
        (eBase U ≪≫ (eOver U).symm).hom := by
    change T.map (T.preimage ((eBase U ≪≫ (eOver U).symm).hom)) = _
    exact T.map_preimage _
  have hnatC : Over.Hom.left f.hom.hom ≫
        B.inclusion.preimage ((closedFiberInclusion B i).app W) =
      B.inclusion.preimage ((closedFiberInclusion B i).app V) ≫
        Over.Hom.left ((affineIndEtaleLift B i).map f).hom.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage,
      B.inclusion.map_comp, B.inclusion.map_preimage]
    exact (closedFiberInclusion B i).naturality f
  have hEta (U : AffineIndEtaleProetale B Z) :
      (eOver U).inv.left ≫ B.inclusion.preimage ((closedFiberInclusion B i).app U) =
        pullback.fst ((affineIndEtaleLift B i).obj U).obj.obj.hom i := by
    simp [eOver, e]
  have hSnd (U : AffineIndEtaleProetale B Z) :
      (eOver U).inv.left ≫ U.obj.obj.hom =
        pullback.snd ((affineIndEtaleLift B i).obj U).obj.obj.hom i := by
    simp [eOver, e]
  have hOverNat :
      (Over.pullback i).map (TX.map ((affineIndEtaleLift B i).map f)) ≫ (eOver W).symm.hom =
        (eOver V).symm.hom ≫ T.map f := by
    apply Over.OverMorphism.ext
    apply (hpb W).hom_ext
    · simp only [Over.comp_left, Over.pullback_map_left]
      simp only [Iso.symm_hom]
      dsimp [TX, T]
      rw [Category.assoc, hEta W]
      calc
        _ = pullback.fst ((affineIndEtaleLift B i).obj V).obj.obj.hom i ≫
            Over.Hom.left ((affineIndEtaleLift B i).map f).hom.hom := pullback.lift_fst _ _ _
        _ = (Over.Hom.left (eOver V).inv ≫
            B.inclusion.preimage ((closedFiberInclusion B i).app V)) ≫
            Over.Hom.left ((affineIndEtaleLift B i).map f).hom.hom := by rw [← hEta V]
        _ = Over.Hom.left (eOver V).inv ≫
            (B.inclusion.preimage ((closedFiberInclusion B i).app V) ≫
              Over.Hom.left ((affineIndEtaleLift B i).map f).hom.hom) := by rw [Category.assoc]
        _ = Over.Hom.left (eOver V).inv ≫
            (Over.Hom.left f.hom.hom ≫
              B.inclusion.preimage ((closedFiberInclusion B i).app W)) := by rw [← hnatC]
        _ = (Over.Hom.left (eOver V).inv ≫ Over.Hom.left f.hom.hom) ≫
            B.inclusion.preimage ((closedFiberInclusion B i).app W) := by rw [← Category.assoc]
    · simp only [Over.comp_left, Over.pullback_map_left]
      simp only [Iso.symm_hom]
      dsimp [TX, T]
      rw [Category.assoc, hSnd W]
      calc
        _ = pullback.snd ((affineIndEtaleLift B i).obj V).obj.obj.hom i := pullback.lift_snd _ _ _
        _ = Over.Hom.left (eOver V).inv ≫ Over.hom V.obj.obj := (hSnd V).symm
        _ = Over.Hom.left (eOver V).inv ≫
            (Over.Hom.left f.hom.hom ≫ Over.hom W.obj.obj) :=
              congrArg (fun g => Over.Hom.left (eOver V).inv ≫ g) (Over.w f.hom.hom).symm
        _ = (Over.Hom.left (eOver V).inv ≫ Over.Hom.left f.hom.hom) ≫
            Over.hom W.obj.obj := by rw [← Category.assoc]
  apply T.map_injective
  change T.map ((affineIndEtaleBaseChange B i).map ((affineIndEtaleLift B i).map f) ≫
      (affineIndEtaleLiftBaseChangeIsoComponent B i W).hom) =
    T.map ((affineIndEtaleLiftBaseChangeIsoComponent B i V).hom ≫ f)
  rw [Functor.map_comp, Functor.map_comp]
  rw [hmap W, hmap V]
  rw [Iso.trans_hom, Iso.symm_hom]
  have hbase := (affineIndEtaleBaseChange_comp_forget B i).some.hom.naturality
    ((affineIndEtaleLift B i).map f)
  change T.map ((affineIndEtaleBaseChange B i).map ((affineIndEtaleLift B i).map f)) ≫
      (eBase W).hom =
      (eBase V).hom ≫
        (Over.pullback i).map (TX.map ((affineIndEtaleLift B i).map f)) at hbase
  have hb2 := congrArg (fun g => g ≫ (eOver W).symm.hom) hbase
  calc
    T.map ((affineIndEtaleBaseChange B i).map ((affineIndEtaleLift B i).map f)) ≫
        (eBase W).hom ≫ (eOver W).symm.hom =
      (T.map ((affineIndEtaleBaseChange B i).map ((affineIndEtaleLift B i).map f)) ≫
        (eBase W).hom) ≫ (eOver W).symm.hom := by simp [Category.assoc]
    _ = ((eBase V).hom ≫ (Over.pullback i).map (TX.map ((affineIndEtaleLift B i).map f))) ≫
        (eOver W).symm.hom := hb2
    _ = (eBase V).hom ≫
        ((Over.pullback i).map (TX.map ((affineIndEtaleLift B i).map f)) ≫ (eOver W).symm.hom) := by
          rw [Category.assoc]
    _ = (eBase V).hom ≫ ((eOver V).symm.hom ≫ T.map f) := by rw [hOverNat]
    _ = (eBase V ≪≫ (eOver V).symm).hom ≫ T.map f := by simp [Category.assoc]

/-- The left-adjoint lift is fully faithful. -/
@[stacks 09BK]
public theorem affineIndEtaleLift_fullyFaithful :
    Nonempty (affineIndEtaleLift B i).FullyFaithful := by
  classical
  obtain ⟨adj⟩ := affineIndEtaleLift_adj_baseChange B i
  obtain ⟨e⟩ := affineIndEtaleLift_baseChangeIso B i
  have : IsIso adj.unit := adj.isIso_unit_of_iso e
  exact ⟨adj.fullyFaithfulLOfIsIsoUnit⟩

/-- The natural map from an object to its lift is a closed immersion. -/
@[stacks 09BK]
public instance closedFiberInclusion_isClosedImmersion
    (V : AffineIndEtaleProetale B Z) :
    IsClosedImmersion ((closedFiberInclusion B i).app V) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (closedFiberInclusion_isPullback B i V).flip inferInstance

private lemma affineIndEtaleProetale_hom_weaklyEtale
    (B : BigProetaleSite.{u}) (S : B.Scheme)
    {U V : AffineIndEtaleProetale B S} (f : U ⟶ V) :
    WeaklyEtale (B.inclusion.map (((AffineIndEtaleProetale.inclusion B S ⋙
      SmallProetale.inclusion B S.obj S.property).map f).left)) := by
  let F := AffineIndEtaleProetale.inclusion B S ⋙
    SmallProetale.inclusion B S.obj S.property
  let f₀ := (F.map f).left
  have hcomp : B.inclusion.map (f₀ ≫ V.obj.obj.hom) = B.inclusion.map U.obj.obj.hom := by
    rw [B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w (F.map f))
  have : WeaklyEtale (B.inclusion.map f₀ ≫ B.inclusion.map V.obj.obj.hom) := by
    rw [← B.inclusion.map_comp, hcomp]
    exact U.obj.property
  have : WeaklyEtale (B.inclusion.map V.obj.obj.hom) := V.obj.property
  exact WeaklyEtale.of_comp (B.inclusion.map f₀) (B.inclusion.map V.obj.obj.hom)

/-- Every point of the lift specializes to a point of its closed fibre. -/
@[stacks 09BK]
public theorem exists_specialization_closedFiber
    (V : AffineIndEtaleProetale B Z)
    (x : ((affineIndEtaleLift B i).obj V).obj.obj.left.obj) :
    ∃ z : V.obj.obj.left.obj,
      x ⤳ ((closedFiberInclusion B i).app V).base z := by
  classical
  let d := affineClosedImmersionRingData B i
  let adj := Classical.choice
    (indEtaleBaseChange_hasFullyFaithfulRightAdjoint Γ(X.obj, ⊤) d.1)
  let V0 := ((affineIndEtaleGlobalSections B Z).obj V).unop
  let V1 := ((rebaseIndEtaleAlongIso d.2).obj (Opposite.op V0)).unop
  let C := (indEtaleQuotientLift Γ(X.obj, ⊤) d.1).obj V1
  let t := quotientLiftCounitRingMap d.1 adj V1
  let S := (SmallProetale.toScheme B Z.obj Z.property).obj
    ((AffineIndEtaleProetale.inclusion B Z).obj V)
  let : IsAffine S := V.property.1
  let eS := S.isoSpec
  let xP : PrimeSpectrum C.obj.right := x
  obtain ⟨q, hxq, hIq⟩ := exists_specialization_indEtaleQuotientLift
    Γ(X.obj, ⊤) d.1 V1 xP
  obtain ⟨hsurj, hker⟩ := quotientLiftCounitRingMap_surjective_and_ker_le d.1 adj V1
  replace hker := hker.trans hIq
  let zP : PrimeSpectrum V1.obj.right :=
    ⟨q.asIdeal.map t.hom, Ideal.map_isPrime_of_surjective hsurj hker⟩
  refine ⟨eS.inv.base zP, ?_⟩
  have himage : ((closedFiberInclusion B i).app V).base (eS.inv.base zP) = q := by
    change (Scheme.Spec.map t.op).base ((eS.inv ≫ eS.hom).base zP) = q
    rw [eS.inv_hom_id]
    simp only [Scheme.Hom.id_base]
    apply PrimeSpectrum.ext
    simp only [Scheme.Spec_map]
    change (q.asIdeal.map t.hom).comap t.hom = q.asIdeal
    rw [Ideal.comap_map_of_surjective t.hom hsurj]
    change q.asIdeal ⊔ RingHom.ker t.hom = q.asIdeal
    exact sup_eq_left.mpr hker
  rw [himage]
  have hxq' : xP ≤ q := (PrimeSpectrum.asIdeal_le_asIdeal xP q).mp hxq
  exact (PrimeSpectrum.le_iff_specializes xP q).mp hxq'

/-- The lift is cocontinuous for the affine ind-étale topologies. -/
@[stacks 09BK]
public instance affineIndEtaleLift_isCocontinuous :
    (affineIndEtaleLift B i).IsCocontinuous (AffineIndEtaleProetale.topology B Z)
      (AffineIndEtaleProetale.topology B X) := by
  obtain ⟨adj⟩ := affineIndEtaleLift_adj_baseChange B i
  rw [adj.isCocontinuous_iff_coverPreserving]
  exact affineIndEtaleBaseChange_coverPreserving B i

/-- The lift takes finite standard pro-étale coverings to such coverings. -/
@[stacks 09BK]
public theorem affineIndEtaleLift_isCovering
    (E : Covering (AffineIndEtaleProetale B Z))
    (hE : AffineIndEtaleProetale.IsCovering B Z E) :
    AffineIndEtaleProetale.IsCovering B X
      ⟨(affineIndEtaleLift B i).obj E.1, E.2.map (affineIndEtaleLift B i)⟩ :=
  by
    classical
    let FZ := AffineIndEtaleProetale.inclusion B Z ⋙
      SmallProetale.inclusion B Z.obj Z.property ⋙
      Over.forget Z ⋙ B.inclusion
    let FX := AffineIndEtaleProetale.inclusion B X ⋙
      SmallProetale.inclusion B X.obj X.property ⋙
      Over.forget X ⋙ B.inclusion
    let Eorig := E.2.map FZ
    let Elift := (E.2.map (affineIndEtaleLift B i)).map FX
    let Y := FX.obj ((affineIndEtaleLift B i).obj E.1)
    have hEcov : B.covering
        ⟨(Over.forget Z).obj ((AffineIndEtaleProetale.inclusion B Z ⋙
          SmallProetale.inclusion B Z.obj Z.property).obj E.1),
          (E.2.map (AffineIndEtaleProetale.inclusion B Z ⋙
            SmallProetale.inclusion B Z.obj Z.property)).map
              (Over.forget Z)⟩ := hE.1
    have hEpro : B.IsProetaleCovering _ := (B.covering_iff _).mp hEcov |>.1
    have hOrig : Eorig.presieve₀ ∈ Scheme.proetalePrecoverage (FZ.obj E.1) := by
      rw [B.isProetaleCovering_iff] at hEpro
      exact hEpro
    have hOrig' : Eorig.presieve₀ ∈
        (Scheme.qcPrecoverage ⊓ Scheme.precoverage @WeaklyEtale) (FZ.obj E.1) := by
      simpa only [Scheme.proetalePrecoverage, Scheme.propQCPrecoverage] using hOrig
    have hjsOrig : ∀ z : FZ.obj E.1, ∃ j, z ∈ Set.range (Eorig.f j) := by
      intro z
      have h := (Scheme.ofArrows_mem_precoverage_iff
        (P := @WeaklyEtale) (X := Eorig.X) (f := Eorig.f)).mp hOrig'.2
      exact h.1 z
    have hjsLift : ∀ x : Y, ∃ j, x ∈ Set.range (Elift.f j) := by
      intro x
      obtain ⟨z, hxz⟩ := exists_specialization_closedFiber B i E.1 x
      obtain ⟨j, hy'⟩ := hjsOrig z
      obtain ⟨y, hy⟩ := hy'
      let ηV := (closedFiberInclusion B i).app E.1
      let ηW := (closedFiberInclusion B i).app (E.2.X j)
      have hn := (closedFiberInclusion B i).naturality (E.2.f j)
      have hpoint : (Elift.f j).base (ηW.base y) = ηV.base z := by
        have h := congrArg (fun f => f.base) hn
        rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base] at h
        have h' := congrArg (fun f => f y) h
        have hpoint' :
            (FX.map ((affineIndEtaleLift B i).map (E.2.f j))).base (ηW.base y) =
              ηV.base ((FZ.map (E.2.f j)).base y) := by
          exact h'.symm
        have hyF : (FZ.map (E.2.f j)) y = z := by
          change ((PreZeroHypercover.map FZ E.2).f j) y = z
          simpa only [PreZeroHypercover.map_f] using hy
        rw [hyF] at hpoint'
        change (FX.map ((affineIndEtaleLift B i).map (E.2.f j))).base (ηW.base y) = ηV.base z
        exact hpoint'
      have hrel : x ⤳ (Elift.f j).base (ηW.base y) := by
        rw [hpoint]
        exact hxz
      have : WeaklyEtale (Elift.f j) := by
        exact affineIndEtaleProetale_hom_weaklyEtale B X ((affineIndEtaleLift B i).map (E.2.f j))
      have hgen : GeneralizingMap (Elift.f j).base :=
        Flat.generalizingMap (Elift.f j)
      obtain ⟨xj, -, hxj⟩ := hgen hrel
      exact ⟨j, ⟨xj, hxj⟩⟩
    let weaklyEtaleProperty : MorphismProperty Scheme := fun _ _ f => WeaklyEtale f
    let hCover : Scheme.Cover (Scheme.precoverage weaklyEtaleProperty) Y := by
      refine ⟨Elift, ?_⟩
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨hjsLift, ?_⟩
      intro j
      exact affineIndEtaleProetale_hom_weaklyEtale B X ((affineIndEtaleLift B i).map (E.2.f j))
    have : Finite hCover.I₀ := hE.2
    have : ∀ j, QuasiCompact (hCover.f j) := by
      intro j
      have : IsAffine (hCover.X j) := by
        exact (affineIndEtaleLift B i).obj (E.2.X j) |>.property.1
      have : IsAffine Y := by
        exact (affineIndEtaleLift B i).obj E.1 |>.property.1
      have : IsAffineHom (hCover.f j) := inferInstance
      infer_instance
    have : Scheme.JointlySurjective (Scheme.precoverage weaklyEtaleProperty) :=
      inferInstance
    have : QuasiCompactCover Elift := by
      change QuasiCompactCover hCover.toPreZeroHypercover
      exact AlgebraicGeometry.QuasiCompactCover.of_finite (𝒰 := hCover)
    have hLift' : hCover.toPreZeroHypercover.presieve₀ ∈
        (Scheme.qcPrecoverage ⊓ Scheme.precoverage weaklyEtaleProperty) Y := by
      constructor
      · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
        infer_instance
      · exact hCover.mem₀
    have hLift : hCover.toPreZeroHypercover.presieve₀ ∈ Scheme.proetalePrecoverage Y := by
      change hCover.toPreZeroHypercover.presieve₀ ∈
        Scheme.propQCPrecoverage weaklyEtaleProperty Y
      simpa only [Scheme.propQCPrecoverage] using hLift'
    change SmallProetale.IsCovering B X.obj X.property
      ⟨(AffineIndEtaleProetale.inclusion B X).obj ((affineIndEtaleLift B i).obj E.1),
        (E.2.map (affineIndEtaleLift B i)).map (AffineIndEtaleProetale.inclusion B X)⟩ ∧
      Finite E.2.I₀
    constructor
    · apply (B.covering_iff _).2
      constructor
      · rw [B.isProetaleCovering_iff]
        change hCover.toPreZeroHypercover.presieve₀ ∈ Scheme.proetalePrecoverage Y
        exact hLift
      · exact (B.covering_iff _).mp hEcov |>.2
    · exact hE.2

end AlgebraicGeometry.ProEtale

end
