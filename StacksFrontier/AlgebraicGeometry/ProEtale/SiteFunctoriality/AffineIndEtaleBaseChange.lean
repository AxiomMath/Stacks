module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.Permanence
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SiteFunctorLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of affine ind-étale sites along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of affine objects of a big pro-étale site. The affine
ind-étale site of `X` is closed under fibre products, and taking the fibre product with `Z`
carries it into the affine ind-étale site of `Z`: a fibre product of affine schemes is affine,
and on global sections a pullback square of affine schemes is a pushout square of rings, so
ind-étaleness over `Γ(X, ⊤)` base-changes to ind-étaleness over `Γ(Z, ⊤)`.

## Main results

* `AlgebraicGeometry.ProEtale.appProetale_hasPullbacks`: the affine ind-étale site has fibre
  products, computed in the ambient small pro-étale site.

## Implementation notes

The coverings of the affine ind-étale site are finite families, and the two sites sit in one
big pro-étale site, so base change of a chosen covering family is again a chosen covering
family with the same index type, hence within the index bound of the big site.

Cover preservation is reduced to the generating covering families by
`AlgebraicGeometry.ProEtale.coverPreserving_of_generators`, an induction over the saturation of
a precoverage which uses only that the functor preserves fibre products.

## References

* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})

/-! ### Fibre products of affine ind-étale objects -/

/-- The fibre product of an affine ind-étale object over `X` with an affine `Z` over `X` has
affine underlying scheme. -/
theorem appPullback_isAffine {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] (U : AffineIndEtaleProetale B X) :
    IsAffine (B.inclusion.obj ((Over.forget Z).obj ((Over.pullback i).obj
      ((AffineIndEtaleProetale.inclusion B X ⋙
        SmallProetale.inclusion B X.obj X.property).obj U)))) := by
  let U1 : BigProetaleOver B X.obj X.property :=
    (SmallProetale.inclusion B X.obj X.property).obj ((AffineIndEtaleProetale.inclusion B X).obj U)
  let _ : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
  let _ : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
  let _ : IsAffine (B.inclusion.obj U1.left) := U.property.1
  exact IsAffine.of_isPullback
    (B.inclusion.map_isPullback (IsPullback.of_hasPullback U1.hom i))

/-- Ind-étaleness on global sections base-changes: the fibre product of an affine ind-étale
object over `X` with an affine `Z` over `X` is ind-étale over `Γ(Z, ⊤)`. -/
theorem appPullback_indEtale {X Z : B.Scheme} (i : Z ⟶ X)
    [IsAffine X.obj] [IsAffine Z.obj] (U : AffineIndEtaleProetale B X) :
    ObjectProperty.ind.{u} (fun C : Under Γ(Z.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk (B.inclusion.map ((Over.pullback i).obj
        ((AffineIndEtaleProetale.inclusion B X ⋙
          SmallProetale.inclusion B X.obj X.property).obj U)).hom).appTop) := by
  let U1 : BigProetaleOver B X.obj X.property :=
    (SmallProetale.inclusion B X.obj X.property).obj ((AffineIndEtaleProetale.inclusion B X).obj U)
  let _ : IsAffine (B.inclusion.obj X) := ‹IsAffine X.obj›
  let _ : IsAffine (B.inclusion.obj Z) := ‹IsAffine Z.obj›
  let _ : IsAffine (B.inclusion.obj U1.left) := U.property.1
  have hpbB := IsPullback.of_hasPullback U1.hom i
  have hpb : IsPullback (B.inclusion.map (pullback.fst U1.hom i))
      (B.inclusion.map (pullback.snd U1.hom i)) (B.inclusion.map U1.hom)
      (B.inclusion.map i) := B.inclusion.map_isPullback hpbB
  let _ : IsAffine (B.inclusion.obj ((Over.forget Z).obj ((Over.pullback i).obj U1))) :=
    IsAffine.of_isPullback hpb
  let A := Γ(X.obj, ⊤)
  let S := Γ(U1.left.obj, ⊤)
  let R := Γ(Z.obj, ⊤)
  let T := Γ(((Over.forget Z).obj ((Over.pullback i).obj U1)).obj, ⊤)
  let f := (B.inclusion.map U1.hom).appTop
  let g := (B.inclusion.map i).appTop
  let f' := (B.inclusion.map (pullback.fst U1.hom i)).appTop
  let g' := (B.inclusion.map (pullback.snd U1.hom i)).appTop
  have hpush : IsPushout g f g' f' := (isPushout_appTop_of_isPullback hpb).flip
  let _ : Algebra A S := f.hom.toAlgebra
  let _ : Algebra A R := g.hom.toAlgebra
  let _ : Algebra S T := f'.hom.toAlgebra
  let _ : Algebra R T := g'.hom.toAlgebra
  let _ : Algebra A T := (f ≫ f').hom.toAlgebra
  have hfg : (f ≫ f') = (g ≫ g') := by
    simpa [f, g, f', g', Scheme.Hom.comp_appTop] using
      congrArg (fun q => (B.inclusion.map q).appTop) hpbB.w
  let _ : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)
  let _ : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun x => congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of T => k.hom x) hfg)
  have hf : CommRingCat.ofHom (algebraMap A S) = f := by ext x; rfl
  have hg : CommRingCat.ofHom (algebraMap A R) = g := by ext x; rfl
  have hf' : CommRingCat.ofHom (algebraMap S T) = f' := by ext x; rfl
  have hg' : CommRingCat.ofHom (algebraMap R T) = g' := by ext x; rfl
  have : Algebra.IsPushout A R S T :=
    CommRingCat.isPushout_iff_isPushout.mp (by rw [hg, hf, hg', hf']; exact hpush)
  have hU : (CommAlgCat.etale A).ind (CommAlgCat.of A S) := by
    rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk]
    exact U.property.2
  show (CommRingCat.etale).underObj.ind (Under.mk (CommRingCat.ofHom (algebraMap R T)))
  exact (MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale)
    (f := CommRingCat.ofHom (algebraMap R T))).mp
      (CommAlgCat.ind_etale_iff_ind_algebraMap.mp (CommAlgCat.ind_etale_of_isPushout A R S T hU))

/-- Being affine and ind-étale over `X` is invariant under isomorphism in the small pro-étale
site. -/
instance appProetale_isClosedUnderIsomorphisms (X : B.Scheme) [IsAffine X.obj] :
    (IsAffineIndEtale B X).IsClosedUnderIsomorphisms where
  of_iso {U V} e hU := by
    refine ⟨?_, ?_⟩
    · let eSmall := (SmallProetale.inclusion B X.obj X.property).map e.inv
      let eOver := (Over.forget X).map eSmall
      let _ : IsAffine (B.inclusion.obj ((Over.forget X).obj
          ((SmallProetale.inclusion B X.obj X.property).obj U))) := hU.1
      have _ : IsIso eSmall := Functor.map_isIso _ _
      have _ : IsIso eOver := Functor.map_isIso _ _
      exact IsAffine.of_isIso (f := B.inclusion.map eOver)
    · let eSmall := (SmallProetale.inclusion B X.obj X.property).map e.inv
      let eOver := (Over.forget X).map eSmall
      let eScheme := B.inclusion.map eOver
      let f := eScheme.appTop
      have _ : IsIso eSmall := Functor.map_isIso _ _
      have _ : IsIso eOver := Functor.map_isIso _ _
      have _ : IsIso eScheme := Functor.map_isIso _ _
      have _ : IsIso f := by
        change IsIso (eScheme.app ⊤)
        infer_instance
      have h : (B.inclusion.map U.obj.hom).appTop ≫ f = (B.inclusion.map V.obj.hom).appTop :=
        congrArg (fun q => (B.inclusion.map q).appTop)
          (Over.w ((SmallProetale.inclusion B X.obj X.property).map e.inv))
      exact (ObjectProperty.ind _).prop_of_iso (Under.isoMk (asIso f) h) hU.2

/-- Affine ind-étale objects are closed under fibre products in the small pro-étale site. -/
instance appProetale_isClosedUnderPullbacks (X : B.Scheme) [IsAffine X.obj] :
    (IsAffineIndEtale B X).IsClosedUnderLimitsOfShape WalkingCospan := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro Y ⟨F, hF⟩
  let G := SmallProetale.inclusion B X.obj X.property ⋙
    BigProetaleOver.forget B X.obj X.property
  have hlim : IsLimit (G.mapCone (limit.cone F)) := isLimitOfPreserves G (limit.isLimit F)
  have hpb := IsPullback.of_isLimit_cone hlim
  let P := limit F
  have hU : IsAffineIndEtale B X (F.obj .left) := hF .left
  have hV : IsAffineIndEtale B X (F.obj .right) := hF .right
  have hW : IsAffineIndEtale B X (F.obj .one) := hF .one
  let _ : IsAffine (B.inclusion.obj ((F ⋙ G).obj .left)) := hU.1
  let _ : IsAffine (B.inclusion.obj ((F ⋙ G).obj .right)) := hV.1
  let _ : IsAffine (B.inclusion.obj ((F ⋙ G).obj .one)) := hW.1
  have hPAff : IsAffine (B.inclusion.obj P.obj.left) :=
    IsAffine.of_isPullback (hpb.map B.inclusion)
  change IsAffine (B.inclusion.obj P.obj.left) ∧
    ObjectProperty.ind.{u} (fun C : Under Γ(X.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk (B.inclusion.map P.obj.hom).appTop)
  refine ⟨hPAff, ?_⟩
  have hpV : G.map (limit.π F .right) ≫ (F.obj .right).obj.hom = P.obj.hom :=
    Over.w ((SmallProetale.inclusion B X.obj X.property).map (limit.π F .right))
  rw [← hpV]
  let _ : IsAffine (G.obj P).obj := hPAff
  exact indEtale_pullback_small B hU hV hW (F.map WalkingCospan.Hom.inl)
    (F.map WalkingCospan.Hom.inr) (G.map (limit.π F .left))
    (G.map (limit.π F .right)) hpb

/-- The affine ind-étale site has fibre products; they are the fibre products of the ambient
small pro-étale site. -/
instance appProetale_hasPullbacks (X : B.Scheme) [IsAffine X.obj] :
    HasPullbacks (AffineIndEtaleProetale B X) := by
  change HasLimitsOfShape WalkingCospan ((IsAffineIndEtale B X).FullSubcategory)
  infer_instance

end AlgebraicGeometry.ProEtale
