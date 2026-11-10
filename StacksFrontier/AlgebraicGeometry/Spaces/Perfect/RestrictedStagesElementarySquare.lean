module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedStagesEtaleSquares

/-!
# Base change of an elementary distinguished square over the base of a limit

Let `(U ⊆ W₀, f : V₀ ⟶ W₀)` be an elementary distinguished square of algebraic spaces with
intersection `P₀ = U ×_{W₀} V₀`, and `w : W₀ ⟶ X₀`. For `p : T ⟶ X₀` the fibre products
`T ×_{X₀} W₀`, `T ×_{X₀} U`, `T ×_{X₀} V₀`, `T ×_{X₀} P₀` form a commutative square, and it is
isomorphic, compatibly with all four maps, to the elementary distinguished square of
`T ×_{X₀} W₀` obtained from the given one by base change along `T ×_{X₀} W₀ ⟶ W₀` (Stacks 08GN):
both are fibre products of the same cospans.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeOverInterSnd`: the map `T ×_{X₀} P₀ ⟶ T ×_{X₀} V₀`.
* `AlgebraicGeometry.Space.baseChangeOverEdsOpenIso`, `…EdsEtaleIso`, `…EdsInterIso`: the
  identifications of the pieces of the base-changed elementary distinguished square.

## References

* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_RestrictedStagesElementarySquare :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A pullback of presheaves on the big fppf site over `S` exists. -/
local instance (priority := high) hasPullback_presheaf_RestrictedStagesElementarySquare
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Maps

variable {X₀ W₀ V₀ T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : W₀ ⟶ X₀) (U : Subfunctor W₀)
  (f : V₀ ⟶ W₀) (p : T ⟶ X₀)

/-- The morphism `T ×_{X₀} (U ×_{W₀} V₀) ⟶ T ×_{X₀} V₀` induced by the second projection. -/
def baseChangeOverInterSnd :
    pullback p (pullback.fst U.ι f ≫ U.ι ≫ w) ⟶ pullback p (f ≫ w) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd U.ι f) (by
    rw [pullback.condition, Category.assoc]
    exact whisker_eq _ (pullback.condition_assoc w))

/-- The map `T ×_{X₀} P₀ ⟶ T ×_{X₀} V₀` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverInterSnd_fst :
    baseChangeOverInterSnd B S hS w U f p ≫ pullback.fst p (f ≫ w) =
      pullback.fst p (pullback.fst U.ι f ≫ U.ι ≫ w) :=
  pullback.lift_fst _ _ _

/-- The map `T ×_{X₀} P₀ ⟶ T ×_{X₀} V₀` followed by the projection to `V₀` is the projection to
`P₀` followed by `P₀ ⟶ V₀`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverInterSnd_snd :
    baseChangeOverInterSnd B S hS w U f p ≫ pullback.snd p (f ≫ w) =
      pullback.snd p (pullback.fst U.ι f ≫ U.ι ≫ w) ≫ pullback.snd U.ι f :=
  pullback.lift_snd _ _ _

/-- The base change of the square `U ×_{W₀} V₀` commutes. -/
theorem baseChangeOverInterSnd_comp_baseChangeOverRestrict :
    baseChangeOverRestrict B S hS (pullback.fst U.ι f) (U.ι ≫ w) p ≫
        baseChangeOverRestrict B S hS U.ι w p =
      baseChangeOverInterSnd B S hS w U f p ≫ baseChangeOverRestrict B S hS f w p := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp only [Category.assoc, baseChangeOverRestrict_snd, baseChangeOverRestrict_snd_assoc,
      baseChangeOverInterSnd_snd_assoc]
    rw [pullback.condition]

/-- `T ×_{X₀} P₀ ⟶ T ×_{X₀} V₀` commutes with the base changes of a morphism over `X₀`. -/
theorem baseChangeOverInterSnd_comp_baseChangeOverMap (p' : T' ⟶ X₀) (a : T ⟶ T')
    (hcomm : a ≫ p' = p) :
    baseChangeOverInterSnd B S hS w U f p ≫ baseChangeOverMap B S hS p p' a hcomm (f ≫ w) =
      baseChangeOverMap B S hS p p' a hcomm _ ≫ baseChangeOverInterSnd B S hS w U f p' := by
  refine pullback.hom_ext ?_ ?_ <;> simp

end Maps

section Pieces

variable {X₀ W₀ V₀ T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {w : W₀ ⟶ X₀} {U : Subfunctor W₀}
  {f : V₀ ⟶ W₀} {hW₀ : IsAlgebraicSpace B S hS W₀}
  (hsq : IsElementaryDistinguishedSquare B S hS hW₀ U f) (p : T ⟶ X₀)
  (hWp : IsAlgebraicSpace B S hS (pullback p w))

include hsq in
/-- **The base change of an elementary distinguished square** along `T ×_{X₀} W₀ ⟶ W₀`
(Stacks 08GN). -/
theorem isElementaryDistinguishedSquare_baseChangeOver :
    IsElementaryDistinguishedSquare B S hS
      (⟨pullback p w, hWp⟩ : AlgebraicSpaces B S hS).2
      (U.preimage (pullback.snd p w)) (pullback.snd f (pullback.snd p w)) :=
  isElementaryDistinguishedSquare_preimage B S hS hW₀ hWp U f hsq _

variable (hUp : IsAlgebraicSpace B S hS (pullback p (U.ι ≫ w)))
  (hVp : IsAlgebraicSpace B S hS (pullback p (f ≫ w)))
  (hPp : IsAlgebraicSpace B S hS (pullback p (pullback.fst U.ι f ≫ U.ι ≫ w)))

/-- The open piece of the base-changed elementary distinguished square is `T ×_{X₀} U`. -/
def baseChangeOverEdsOpenIso :
    edsOpen B S hS (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp) ≅
      (⟨pullback p (U.ι ≫ w), hUp⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ ((Subfunctor.isPullback_preimage (pullback.snd p w) U).flip.isoIsPullback
    _ _ (isPullback_baseChangeOverRestrict B S hS U.ι w p))

/-- The étale piece of the base-changed elementary distinguished square is `T ×_{X₀} V₀`. -/
def baseChangeOverEdsEtaleIso :
    edsEtale B S hS (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp) ≅
      (⟨pullback p (f ≫ w), hVp⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ ((IsPullback.of_hasPullback f (pullback.snd p w)).flip.isoIsPullback
    _ _ (isPullback_baseChangeOverRestrict B S hS f w p))

/-- The intersection of the base-changed elementary distinguished square is `T ×_{X₀} P₀`. -/
def baseChangeOverEdsInterIso :
    edsInter B S hS (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp) ≅
      (⟨pullback p (pullback.fst U.ι f ≫ U.ι ≫ w), hPp⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ ((isPullback_preimage_inter B S hS U f (pullback.snd p w)).isoIsPullback
    _ _ ((isPullback_baseChangeOverRestrict B S hS (pullback.fst U.ι f) (U.ι ≫ w) p).paste_horiz
      (isPullback_baseChangeOverRestrict B S hS U.ι w p)))

/-- Under `baseChangeOverEdsOpenIso`, the open immersion of the base-changed square is
`T ×_{X₀} U ⟶ T ×_{X₀} W₀`. -/
theorem baseChangeOverEdsOpenIso_hom_comp :
    (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom ≫
        (ObjectProperty.homMk (baseChangeOverRestrict B S hS U.ι w p) :
          (⟨pullback p (U.ι ≫ w), hUp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback p w, hWp⟩) =
      edsOpenHom B S hS (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp) :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- Under `baseChangeOverEdsEtaleIso`, the étale map of the base-changed square is
`T ×_{X₀} V₀ ⟶ T ×_{X₀} W₀`. -/
theorem baseChangeOverEdsEtaleIso_hom_comp :
    (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom ≫
        (ObjectProperty.homMk (baseChangeOverRestrict B S hS f w p) :
          (⟨pullback p (f ≫ w), hVp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback p w, hWp⟩) =
      edsEtaleHom B S hS (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp) :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- `baseChangeOverEdsInterIso` followed by `T ×_{X₀} P₀ ⟶ T ×_{X₀} W₀` is the inclusion of the
intersection of the base-changed square into `T ×_{X₀} W₀`. -/
theorem baseChangeOverEdsInterIso_hom_hom_fst :
    (baseChangeOverEdsInterIso B S hS hsq p hWp hPp).hom.hom ≫
        baseChangeOverRestrict B S hS (pullback.fst U.ι f) (U.ι ≫ w) p ≫
          baseChangeOverRestrict B S hS U.ι w p =
      pullback.fst (U.preimage (pullback.snd p w)).ι (pullback.snd f (pullback.snd p w)) ≫
        (U.preimage (pullback.snd p w)).ι :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `baseChangeOverEdsInterIso` followed by the projection `T ×_{X₀} P₀ ⟶ P₀` is the map induced
by the projections of the intersection of the base-changed square to `U` and to `V₀`. -/
theorem baseChangeOverEdsInterIso_hom_hom_snd :
    (baseChangeOverEdsInterIso B S hS hsq p hWp hPp).hom.hom ≫
        pullback.snd p (pullback.fst U.ι f ≫ U.ι ≫ w) =
      pullback.lift
        (pullback.fst (U.preimage (pullback.snd p w)).ι (pullback.snd f (pullback.snd p w)) ≫
          U.fromPreimage (pullback.snd p w))
        (pullback.snd (U.preimage (pullback.snd p w)).ι (pullback.snd f (pullback.snd p w)) ≫
          pullback.fst f (pullback.snd p w)) (by
          rw [Category.assoc, Category.assoc, (Subfunctor.isPullback_preimage _ U).w,
            pullback.condition_assoc, pullback.condition (f := f) (g := pullback.snd p w)]) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- `baseChangeOverEdsOpenIso` followed by `T ×_{X₀} U ⟶ T ×_{X₀} W₀` is the inclusion of the
preimage of `U`. -/
theorem baseChangeOverEdsOpenIso_hom_hom_fst :
    (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom.hom ≫
        baseChangeOverRestrict B S hS U.ι w p = (U.preimage (pullback.snd p w)).ι :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `baseChangeOverEdsOpenIso` followed by the projection `T ×_{X₀} U ⟶ U` is the map from the
preimage of `U` to `U`. -/
theorem baseChangeOverEdsOpenIso_hom_hom_snd :
    (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom.hom ≫ pullback.snd p (U.ι ≫ w) =
      U.fromPreimage (pullback.snd p w) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- `baseChangeOverEdsEtaleIso` followed by `T ×_{X₀} V₀ ⟶ T ×_{X₀} W₀` is the second projection
of `V₀ ×_{W₀} (T ×_{X₀} W₀)`. -/
theorem baseChangeOverEdsEtaleIso_hom_hom_fst :
    (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom.hom ≫
        baseChangeOverRestrict B S hS f w p = pullback.snd f (pullback.snd p w) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `baseChangeOverEdsEtaleIso` followed by the projection `T ×_{X₀} V₀ ⟶ V₀` is the first
projection of `V₀ ×_{W₀} (T ×_{X₀} W₀)`. -/
theorem baseChangeOverEdsEtaleIso_hom_hom_snd :
    (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom.hom ≫ pullback.snd p (f ≫ w) =
      pullback.fst f (pullback.snd p w) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The identifications `baseChangeOverEdsInterIso` and `baseChangeOverEdsOpenIso` are compatible
with the first projection of the intersection and `T ×_{X₀} P₀ ⟶ T ×_{X₀} U`. -/
theorem baseChangeOverEdsInterIso_hom_comp_fst :
    (baseChangeOverEdsInterIso B S hS hsq p hWp hPp).hom ≫
        (ObjectProperty.homMk (baseChangeOverRestrict B S hS (pullback.fst U.ι f) (U.ι ≫ w) p) :
          (⟨pullback p (pullback.fst U.ι f ≫ U.ι ≫ w), hPp⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨pullback p (U.ι ≫ w), hUp⟩) =
      edsFst B S hS (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp) ≫
        (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom := by
  refine ObjectProperty.hom_ext _ ((isPullback_baseChangeOverRestrict B S hS U.ι w p).hom_ext ?_ ?_)
  · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, Category.assoc,
      baseChangeOverEdsInterIso_hom_hom_fst, baseChangeOverEdsOpenIso_hom_hom_fst]
    rfl
  · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, Category.assoc,
      baseChangeOverRestrict_snd,
      reassoc_of% (baseChangeOverEdsInterIso_hom_hom_snd B S hS hsq p hWp hPp),
      baseChangeOverEdsOpenIso_hom_hom_snd]
    exact pullback.lift_fst _ _ _

/-- The identifications `baseChangeOverEdsInterIso` and `baseChangeOverEdsEtaleIso` are
compatible with the second projection of the intersection and `T ×_{X₀} P₀ ⟶ T ×_{X₀} V₀`. -/
theorem baseChangeOverEdsInterIso_hom_comp_snd :
    (baseChangeOverEdsInterIso B S hS hsq p hWp hPp).hom ≫
        (ObjectProperty.homMk (baseChangeOverInterSnd B S hS w U f p) :
          (⟨pullback p (pullback.fst U.ι f ≫ U.ι ≫ w), hPp⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨pullback p (f ≫ w), hVp⟩) =
      edsSnd B S hS (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp) ≫
        (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom := by
  refine ObjectProperty.hom_ext _ ((isPullback_baseChangeOverRestrict B S hS f w p).hom_ext ?_ ?_)
  · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, Category.assoc,
      ← baseChangeOverInterSnd_comp_baseChangeOverRestrict, baseChangeOverEdsInterIso_hom_hom_fst,
      baseChangeOverEdsEtaleIso_hom_hom_fst]
    exact pullback.condition
  · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, Category.assoc,
      baseChangeOverInterSnd_snd,
      reassoc_of% (baseChangeOverEdsInterIso_hom_hom_snd B S hS hsq p hWp hPp),
      baseChangeOverEdsEtaleIso_hom_hom_snd]
    exact pullback.lift_snd _ _ _

end Pieces

section Homs

variable {X₀ W₀ V₀ T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : W₀ ⟶ X₀) (U : Subfunctor W₀)
  (f : V₀ ⟶ W₀)

/-- `T ×_{X₀} U ⟶ T ×_{X₀} W₀`, as a morphism of algebraic spaces. -/
abbrev baseChangeOverOpenHom (p : T ⟶ X₀) (hUp : IsAlgebraicSpace B S hS (pullback p (U.ι ≫ w)))
    (hWp : IsAlgebraicSpace B S hS (pullback p w)) :
    (⟨pullback p (U.ι ≫ w), hUp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback p w, hWp⟩ :=
  ObjectProperty.homMk (baseChangeOverRestrict B S hS U.ι w p)

/-- `T ×_{X₀} V₀ ⟶ T ×_{X₀} W₀`, as a morphism of algebraic spaces. -/
abbrev baseChangeOverEtaleHom (p : T ⟶ X₀) (hVp : IsAlgebraicSpace B S hS (pullback p (f ≫ w)))
    (hWp : IsAlgebraicSpace B S hS (pullback p w)) :
    (⟨pullback p (f ≫ w), hVp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback p w, hWp⟩ :=
  ObjectProperty.homMk (baseChangeOverRestrict B S hS f w p)

/-- `T ×_{X₀} (U ×_{W₀} V₀) ⟶ T ×_{X₀} U`, as a morphism of algebraic spaces. -/
abbrev baseChangeOverInterFstHom (p : T ⟶ X₀)
    (hPp : IsAlgebraicSpace B S hS (pullback p (pullback.fst U.ι f ≫ U.ι ≫ w)))
    (hUp : IsAlgebraicSpace B S hS (pullback p (U.ι ≫ w))) :
    (⟨pullback p (pullback.fst U.ι f ≫ U.ι ≫ w), hPp⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨pullback p (U.ι ≫ w), hUp⟩ :=
  ObjectProperty.homMk (baseChangeOverRestrict B S hS (pullback.fst U.ι f) (U.ι ≫ w) p)

/-- `T ×_{X₀} (U ×_{W₀} V₀) ⟶ T ×_{X₀} V₀`, as a morphism of algebraic spaces. -/
abbrev baseChangeOverInterSndHom (p : T ⟶ X₀)
    (hPp : IsAlgebraicSpace B S hS (pullback p (pullback.fst U.ι f ≫ U.ι ≫ w)))
    (hVp : IsAlgebraicSpace B S hS (pullback p (f ≫ w))) :
    (⟨pullback p (pullback.fst U.ι f ≫ U.ι ≫ w), hPp⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨pullback p (f ≫ w), hVp⟩ :=
  ObjectProperty.homMk (baseChangeOverInterSnd B S hS w U f p)

/-- The square of algebraic spaces `T ×_{X₀} P₀`, `T ×_{X₀} U`, `T ×_{X₀} V₀`, `T ×_{X₀} W₀`
commutes. -/
theorem baseChangeOverInterFstHom_comp_openHom (p : T ⟶ X₀)
    (hWp : IsAlgebraicSpace B S hS (pullback p w))
    (hUp : IsAlgebraicSpace B S hS (pullback p (U.ι ≫ w)))
    (hVp : IsAlgebraicSpace B S hS (pullback p (f ≫ w)))
    (hPp : IsAlgebraicSpace B S hS (pullback p (pullback.fst U.ι f ≫ U.ι ≫ w))) :
    baseChangeOverInterFstHom B S hS w U f p hPp hUp ≫ baseChangeOverOpenHom B S hS w U p hUp hWp =
      baseChangeOverInterSndHom B S hS w U f p hPp hVp ≫
        baseChangeOverEtaleHom B S hS w f p hVp hWp :=
  ObjectProperty.hom_ext _ (baseChangeOverInterSnd_comp_baseChangeOverRestrict B S hS w U f p)

/-- The base change of a morphism over `X₀`, as a morphism of algebraic spaces. -/
abbrev baseChangeOverMapHom {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : T ⟶ X₀) (p' : T' ⟶ X₀)
    (a : T ⟶ T') (hcomm : a ≫ p' = p) (y : Y₀ ⟶ X₀) (h : IsAlgebraicSpace B S hS (pullback p y))
    (h' : IsAlgebraicSpace B S hS (pullback p' y)) :
    (⟨pullback p y, h⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback p' y, h'⟩ :=
  ObjectProperty.homMk (baseChangeOverMap B S hS p p' a hcomm y)

/-- The base changes of composable morphisms over `X₀` compose. -/
theorem baseChangeOverMapHom_comp {T'' Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : T ⟶ X₀)
    (p' : T' ⟶ X₀) (p'' : T'' ⟶ X₀) (a : T ⟶ T') (a' : T' ⟶ T'') (a'' : T ⟶ T'')
    (ha : a ≫ p' = p) (ha' : a' ≫ p'' = p') (ha'' : a'' ≫ p'' = p) (hcomp : a ≫ a' = a'')
    (y : Y₀ ⟶ X₀) (h : IsAlgebraicSpace B S hS (pullback p y))
    (h' : IsAlgebraicSpace B S hS (pullback p' y))
    (h'' : IsAlgebraicSpace B S hS (pullback p'' y)) :
    baseChangeOverMapHom B S hS p p' a ha y h h' ≫
        baseChangeOverMapHom B S hS p' p'' a' ha' y h' h'' =
      baseChangeOverMapHom B S hS p p'' a'' ha'' y h h'' :=
  ObjectProperty.hom_ext _ (pullback.hom_ext (by simp [← hcomp]) (by simp))

variable (p : T ⟶ X₀) (p' : T' ⟶ X₀) (a : T ⟶ T') (hcomm : a ≫ p' = p)
  (hWp : IsAlgebraicSpace B S hS (pullback p w)) (hWp' : IsAlgebraicSpace B S hS (pullback p' w))
  (hUp : IsAlgebraicSpace B S hS (pullback p (U.ι ≫ w)))
  (hUp' : IsAlgebraicSpace B S hS (pullback p' (U.ι ≫ w)))
  (hVp : IsAlgebraicSpace B S hS (pullback p (f ≫ w)))
  (hVp' : IsAlgebraicSpace B S hS (pullback p' (f ≫ w)))
  (hPp : IsAlgebraicSpace B S hS (pullback p (pullback.fst U.ι f ≫ U.ι ≫ w)))
  (hPp' : IsAlgebraicSpace B S hS (pullback p' (pullback.fst U.ι f ≫ U.ι ≫ w)))

/-- `T ×_{X₀} U ⟶ T ×_{X₀} W₀` commutes with the base changes of a morphism over `X₀`. -/
theorem baseChangeOverMapHom_comp_openHom :
    baseChangeOverMapHom B S hS p p' a hcomm _ hUp hUp' ≫
        baseChangeOverOpenHom B S hS w U p' hUp' hWp' =
      baseChangeOverOpenHom B S hS w U p hUp hWp ≫
        baseChangeOverMapHom B S hS p p' a hcomm w hWp hWp' :=
  ObjectProperty.hom_ext _
    (baseChangeOverRestrict_comp_baseChangeOverMap B S hS U.ι w p p' a hcomm).symm

/-- `T ×_{X₀} V₀ ⟶ T ×_{X₀} W₀` commutes with the base changes of a morphism over `X₀`. -/
theorem baseChangeOverMapHom_comp_etaleHom :
    baseChangeOverMapHom B S hS p p' a hcomm _ hVp hVp' ≫
        baseChangeOverEtaleHom B S hS w f p' hVp' hWp' =
      baseChangeOverEtaleHom B S hS w f p hVp hWp ≫
        baseChangeOverMapHom B S hS p p' a hcomm w hWp hWp' :=
  ObjectProperty.hom_ext _
    (baseChangeOverRestrict_comp_baseChangeOverMap B S hS f w p p' a hcomm).symm

/-- `T ×_{X₀} P₀ ⟶ T ×_{X₀} U` commutes with the base changes of a morphism over `X₀`. -/
theorem baseChangeOverMapHom_comp_interFstHom :
    baseChangeOverMapHom B S hS p p' a hcomm _ hPp hPp' ≫
        baseChangeOverInterFstHom B S hS w U f p' hPp' hUp' =
      baseChangeOverInterFstHom B S hS w U f p hPp hUp ≫
        baseChangeOverMapHom B S hS p p' a hcomm _ hUp hUp' :=
  ObjectProperty.hom_ext _
    (baseChangeOverRestrict_comp_baseChangeOverMap B S hS (pullback.fst U.ι f)
      (U.ι ≫ w) p p' a hcomm).symm

/-- `T ×_{X₀} P₀ ⟶ T ×_{X₀} V₀` commutes with the base changes of a morphism over `X₀`. -/
theorem baseChangeOverMapHom_comp_interSndHom :
    baseChangeOverMapHom B S hS p p' a hcomm _ hPp hPp' ≫
        baseChangeOverInterSndHom B S hS w U f p' hPp' hVp' =
      baseChangeOverInterSndHom B S hS w U f p hPp hVp ≫
        baseChangeOverMapHom B S hS p p' a hcomm _ hVp hVp' :=
  ObjectProperty.hom_ext _
    (baseChangeOverInterSnd_comp_baseChangeOverMap B S hS w U f p p' a hcomm).symm

end Homs

end AlgebraicGeometry.Space

end
