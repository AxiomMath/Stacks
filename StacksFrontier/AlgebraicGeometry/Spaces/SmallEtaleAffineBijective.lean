module

public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison

/-!
# Bijectivity over affine charts is bijectivity

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  A morphism of
sheaves of modules on the small étale site of `F` whose map on sections is bijective over every
étale chart with affine underlying scheme is an isomorphism, hence bijective on the sections
over every étale chart.

The affine étale charts form a dense subsite of the small étale site (Stacks 04JS), so
bijectivity over the affine charts is local bijectivity, and a locally bijective morphism of
sheaves of modules is an isomorphism.  This is the statement of
`AlgebraicGeometry.Space.SmallEtale.isIso_of_bijective_app_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/Spaces/SliceAffineComparison.lean` for the small étale site
itself rather than for a slice of it.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isIso_of_bijective_app_of_isAffineChart`: a morphism of
  sheaves of modules on the small étale site which is bijective on the sections over the affine
  charts is an isomorphism.
* `AlgebraicGeometry.Space.SmallEtale.bijective_app_of_bijective_app_of_isAffineChart`: such a
  morphism is bijective on the sections over every chart.
* `AlgebraicGeometry.Space.SmallEtale.isIso_presheafToSheaf_map_of_bijective_app_of_isAffineChart`:
  a morphism of presheaves of abelian groups bijective on the sections over the affine charts
  becomes an isomorphism after sheafification.

## References

* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory Opposite

universe m u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

include hF in
/-- **Surjectivity on sections over affine charts is local surjectivity** on the small étale
site: every section is, on a covering by affine charts, in the image. -/
theorem isLocallySurjective_of_surjective_app_of_isAffineChart
    {M N : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F
        hF).O)}
    (φ : M ⟶ N)
    (h : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) →
      Function.Surjective (φ.val.app (op Z)).hom) :
    PresheafOfModules.IsLocallySurjective (smallEtaleRingedSite B S hS F hF).J φ.val := by
  constructor
  intro Z s
  refine (topology B S hS F).superset_covering ?_
    ((isCoverDense_affineEtaleInclusion B S hS F hF).is_cover Z)
  rintro W g ⟨⟨A, lift, map, fac⟩⟩
  obtain ⟨t, ht⟩ := h ((AffineEtale.inclusion B S hS F).obj A) A.property
    (((PresheafOfModules.toPresheaf _).obj N.val).map map.op s)
  have hm : (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map φ.val) s).arrows map :=
    ⟨t, ht⟩
  have hgl := (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map φ.val)
    s).downward_closed hm lift
  rw [← fac]
  exact hgl

include hF in
/-- **Injectivity on sections over affine charts is local injectivity** on the small étale
site: two sections with the same image agree on a covering by affine charts. -/
theorem isLocallyInjective_of_injective_app_of_isAffineChart
    {M N : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F
        hF).O)}
    (φ : M ⟶ N)
    (h : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) →
      Function.Injective (φ.val.app (op Z)).hom) :
    PresheafOfModules.IsLocallyInjective (smallEtaleRingedSite B S hS F hF).J φ.val := by
  constructor
  intro Z x y hxy
  refine (topology B S hS F).superset_covering ?_
    ((isCoverDense_affineEtaleInclusion B S hS F hF).is_cover Z.unop)
  rintro W g ⟨⟨A, lift, map, fac⟩⟩
  have hm : (Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf _).obj M.val) x y).arrows map := by
    refine h ((AffineEtale.inclusion B S hS F).obj A) A.property ?_
    have hx := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) map.op x
    have hy := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) map.op y
    exact hx.trans ((congrArg (fun z => ((PresheafOfModules.toPresheaf _).obj N.val).map map.op z)
      hxy).trans hy.symm)
  have hgl := (Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf _).obj M.val) x y).downward_closed hm lift
  rw [← fac]
  exact hgl

include hF in
/-- **A morphism of sheaves of modules on the small étale site of an algebraic space which is
bijective on the sections over the affine charts is an isomorphism.**  Nothing is assumed over a
non-affine chart: the affine charts cover, so the morphism is locally bijective. -/
theorem isIso_of_bijective_app_of_isAffineChart
    {M N : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F
        hF).O)}
    (φ : M ⟶ N)
    (h : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) →
      Function.Bijective (φ.val.app (op Z)).hom) :
    IsIso φ :=
  have := isLocallyInjective_of_injective_app_of_isAffineChart B S hS F hF φ
    fun Z hZ => (h Z hZ).1
  have := isLocallySurjective_of_surjective_app_of_isAffineChart B S hS F hF φ
    fun Z hZ => (h Z hZ).2
  Stacks.SheafOfModules.isIso_of_isLocallyBijective φ

include hF in
/-- **Bijectivity on the sections over the affine charts is bijectivity on the sections over
every chart**, for a morphism of sheaves of modules on the small étale site of an algebraic
space. -/
theorem bijective_app_of_bijective_app_of_isAffineChart
    {M N : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F
        hF).O)}
    (φ : M ⟶ N)
    (h : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) →
      Function.Bijective (φ.val.app (op Z)).hom)
    (Z : SmallEtale B S hS F) :
    Function.Bijective (φ.val.app (op Z)).hom := by
  have := isIso_of_bijective_app_of_isAffineChart B S hS F hF φ h
  exact Function.bijective_iff_has_inverse.2 ⟨((inv φ).val.app (op Z)).hom,
    fun x => congrArg (fun k : M ⟶ M => (k.val.app (op Z)).hom x) (IsIso.hom_inv_id φ),
    fun x => congrArg (fun k : N ⟶ N => (k.val.app (op Z)).hom x) (IsIso.inv_hom_id φ)⟩

/-! ### Presheaves of abelian groups -/

section Presheaf

variable {P Q : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{m}} (α : P ⟶ Q)

include hF in
/-- **Surjectivity on sections over affine charts is local surjectivity**, for a morphism of
presheaves of abelian groups on the small étale site. -/
theorem isLocallySurjective_presheaf_of_surjective_app_of_isAffineChart
    (h : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) →
      Function.Surjective (α.app (op Z))) :
    Presheaf.IsLocallySurjective (topology B S hS F) α := by
  constructor
  intro Z s
  refine (topology B S hS F).superset_covering ?_
    ((isCoverDense_affineEtaleInclusion B S hS F hF).is_cover Z)
  rintro W g ⟨⟨A, lift, map, fac⟩⟩
  obtain ⟨t, ht⟩ := h ((AffineEtale.inclusion B S hS F).obj A) A.property (Q.map map.op s)
  rw [← fac]
  exact (Presheaf.imageSieve α s).downward_closed (f := map) ⟨t, ht⟩ lift

include hF in
/-- **Injectivity on sections over affine charts is local injectivity**, for a morphism of
presheaves of abelian groups on the small étale site. -/
theorem isLocallyInjective_presheaf_of_injective_app_of_isAffineChart
    (h : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) →
      Function.Injective (α.app (op Z))) :
    Presheaf.IsLocallyInjective (topology B S hS F) α := by
  constructor
  intro Z x y hxy
  refine (topology B S hS F).superset_covering ?_
    ((isCoverDense_affineEtaleInclusion B S hS F hF).is_cover Z.unop)
  rintro W g ⟨⟨A, lift, map, fac⟩⟩
  have hm : (Presheaf.equalizerSieve (F := P) x y).arrows map :=
    h ((AffineEtale.inclusion B S hS F).obj A) A.property <|
      (NatTrans.naturality_apply α map.op x).trans
        ((congrArg (fun z => Q.map map.op z) hxy).trans (NatTrans.naturality_apply α map.op y).symm)
  rw [← fac]
  exact (Presheaf.equalizerSieve (F := P) x y).downward_closed hm lift

include hF in
/-- **A morphism of presheaves of abelian groups on the small étale site which is bijective on
the sections over the affine charts becomes an isomorphism after sheafification.** -/
theorem isIso_presheafToSheaf_map_of_bijective_app_of_isAffineChart
    [HasSheafify (topology B S hS F) AddCommGrpCat.{m}]
    [(topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{m}]
    (h : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) →
      Function.Bijective (α.app (op Z))) :
    IsIso ((presheafToSheaf (topology B S hS F) AddCommGrpCat.{m}).map α) := by
  have := isLocallyInjective_presheaf_of_injective_app_of_isAffineChart B S hS F hF α
    fun Z hZ => (h Z hZ).1
  have := isLocallySurjective_presheaf_of_surjective_app_of_isAffineChart B S hS F hF α
    fun Z hZ => (h Z hZ).2
  exact (GrothendieckTopology.W_iff _ α).1
    ((GrothendieckTopology.W_iff_isLocallyBijective _ α).2 ⟨inferInstance, inferInstance⟩)

end Presheaf

end AlgebraicGeometry.Space.SmallEtale

end
