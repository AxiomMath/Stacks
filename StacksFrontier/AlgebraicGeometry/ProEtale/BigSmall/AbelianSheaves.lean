module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Abelian sheaves on the big and small pro-étale sites

Abbreviations for the categories of abelian sheaves on the big pro-étale site over a scheme of a
chosen big pro-étale site and on its small pro-étale site, together with the sheafification and
abelianness instances they are used through.

Restriction of abelian sheaves from the big pro-étale site over an object to its small
pro-étale site is the abelian inverse image of the small-to-big morphism of topoi at the
identity. It is also the direct image along the inclusion of sites, and `restrictionIso`
identifies the two.

## Main definitions

* `AlgebraicGeometry.ProEtale.BigAb`: abelian sheaves on the big pro-étale site over an object.
* `AlgebraicGeometry.ProEtale.SmallAb`: abelian sheaves on its small pro-étale site.
* `AlgebraicGeometry.ProEtale.restriction`: abelian inverse image along the small-to-big
  morphism of topoi attached to a morphism of schemes.

## Main results

* `AlgebraicGeometry.ProEtale.restrictionIso`: the abelian inverse image is the direct image
  along the small-to-big functor of sites.

## Implementation notes

Both sites are only essentially small relative to the scheme universe, so sheafification of
abelian sheaves is obtained from the essentially small comparison rather than from the
small-site instance.

A natural isomorphism of functors into abelian sheaves is built from one between the underlying
sheaves of sets: `liftSheafNatIso` checks that the component maps are additive, using that
additivity of a natural family of maps of sections follows from naturality for the two
biproduct projections.

## References

* [Stacks Project, Tag 0F68](https://stacks.math.columbia.edu/tag/0F68)
* [Stacks Project, Tag 0F69](https://stacks.math.columbia.edu/tag/0F69)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})

/-- Abelian sheaves on the big pro-étale site over an object of a big pro-étale site. -/
public abbrev BigAb (X : B.Scheme) :=
  Sheaf (BigProetaleOver.topology B X.obj X.property) AddCommGrpCat.{u + 1}

/-- Abelian sheaves on the small pro-étale site of an object of a big pro-étale site. -/
public abbrev SmallAb (X : B.Scheme) :=
  Sheaf (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1}

/-- Abelian presheaves on the big pro-étale site over an object admit sheafification. -/
public noncomputable instance bigProetaleOver_hasSheafify (X : B.Scheme) :
    HasSheafify (BigProetaleOver.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0}

/-- Abelian presheaves on the small pro-étale site of an object admit sheafification. -/
public noncomputable instance smallProetale_hasSheafify (X : B.Scheme) :
    HasSheafify (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0}

/-- The category of abelian sheaves on the big pro-étale site over an object is abelian. -/
public noncomputable instance bigAb_abelian (X : B.Scheme) : Abelian (BigAb B X) :=
  CategoryTheory.sheafIsAbelian

/-- The category of abelian sheaves on the small pro-étale site of an object is abelian. -/
public noncomputable instance smallAb_abelian (X : B.Scheme) : Abelian (SmallAb B X) :=
  CategoryTheory.sheafIsAbelian

/-- A natural family of maps of underlying sets between additive functors is additive, by
naturality for the two projections out of a binary biproduct. -/
public lemma natural_map_add {C : Type*} [Category* C] [Preadditive C]
    [Limits.HasBinaryBiproducts C] (F G : C ⥤ AddCommGrpCat.{u}) [F.Additive] [G.Additive]
    (a : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat)
    (X : C) (x y : F.obj X) : a.app X (x + y) = a.app X x + a.app X y := by
  let z : F.obj (X ⊞ X) := F.map Limits.biprod.inl x + F.map Limits.biprod.inr y
  have hn (f : X ⊞ X ⟶ X) : a.app X (F.map f z) = G.map f (a.app (X ⊞ X) z) :=
    ConcreteCategory.congr_hom (a.naturality f) z
  have ⟨hfst, hsnd⟩ : F.map (Limits.biprod.fst : X ⊞ X ⟶ X) z = x ∧
      F.map (Limits.biprod.snd : X ⊞ X ⟶ X) z = y := by
    dsimp [z]
    constructor <;> simp [← ConcreteCategory.comp_apply, ← F.map_comp]
  calc
    a.app X (x + y) = a.app X (F.map (Limits.biprod.fst + Limits.biprod.snd) z) := by
      rw [F.map_add]
      change _ = a.app X (_ + _)
      rw [hfst, hsnd]
      rfl
    _ = G.map (Limits.biprod.fst + Limits.biprod.snd) (a.app (X ⊞ X) z) := hn _
    _ = a.app X x + a.app X y := by
      rw [G.map_add]
      change G.map Limits.biprod.fst (a.app (X ⊞ X) z) +
        G.map Limits.biprod.snd (a.app (X ⊞ X) z) = _
      rw [← hn Limits.biprod.fst, ← hn Limits.biprod.snd, hfst, hsnd]
      rfl

/-- Lift a natural transformation of the underlying sheaves of sets of two additive functors
into abelian sheaves to a natural transformation of the functors themselves. -/
public noncomputable def liftSheafNatTrans
    {C : Type*} [Category* C] [Preadditive C] [Limits.HasBinaryBiproducts C]
    {D : Type*} [Category* D] (J : GrothendieckTopology D)
    (F G : C ⥤ Sheaf J AddCommGrpCat.{u}) [F.Additive] [G.Additive]
    (a : F ⋙ sheafCompose J (forget AddCommGrpCat) ⟶
      G ⋙ sheafCompose J (forget AddCommGrpCat)) : F ⟶ G where
  app X := ⟨{
    app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' ((a.app X).hom.app U) <|
      natural_map_add
        (F ⋙ sheafToPresheaf J AddCommGrpCat ⋙ (evaluation _ _).obj U)
        (G ⋙ sheafToPresheaf J AddCommGrpCat ⋙ (evaluation _ _).obj U)
        (Functor.whiskerRight a (sheafToPresheaf J (Type u) ⋙ (evaluation _ _).obj U)) X
    naturality U V f := by
      ext x
      exact ConcreteCategory.congr_hom ((a.app X).hom.naturality f) x }⟩
  naturality X Y f := by
    ext U x
    exact ConcreteCategory.congr_hom (CC := fun X : Type u => X)
      (congrArg (fun t => t.hom.app U) (a.naturality f)) x

/-- Lift a natural isomorphism of the underlying sheaves of sets of two additive functors into
abelian sheaves to a natural isomorphism of the functors themselves. -/
public noncomputable def liftSheafNatIso
    {C : Type*} [Category* C] [Preadditive C] [Limits.HasBinaryBiproducts C]
    {D : Type*} [Category* D] (J : GrothendieckTopology D)
    (F G : C ⥤ Sheaf J AddCommGrpCat.{u}) [F.Additive] [G.Additive]
    (e : F ⋙ sheafCompose J (forget AddCommGrpCat) ≅
      G ⋙ sheafCompose J (forget AddCommGrpCat)) : F ≅ G where
  hom := liftSheafNatTrans J F G e.hom
  inv := liftSheafNatTrans J G F e.inv
  hom_inv_id := by
    ext X U x
    exact ConcreteCategory.congr_hom (CC := fun X : Type u => X)
      (congrArg (fun t => t.hom.app U) (e.hom_inv_id_app X)) x
  inv_hom_id := by
    ext X U x
    exact ConcreteCategory.congr_hom (CC := fun X : Type u => X)
      (congrArg (fun t => t.hom.app U) (e.inv_hom_id_app X)) x

variable {B}

/-- The abelian inverse image along the small-to-big morphism of topoi attached to a morphism
`a : X ⟶ Y` of schemes of a big pro-étale site. -/
public noncomputable abbrev restriction {X Y : B.Scheme} (a : X ⟶ Y) :=
  CategoryTheory.Sites.abelianInverseImage (smallProetaleToBigProetaleMorphism B X Y a)

attribute [local instance] Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

/-- The abelian inverse image along a small-to-big morphism of pro-étale topoi is additive. -/
public noncomputable instance restriction_additive {X Y : B.Scheme} (a : X ⟶ Y) :
    (CategoryTheory.Sites.abelianInverseImage
      (smallProetaleToBigProetaleMorphism B X Y a)).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- The abelian inverse image along the small-to-big morphism of topoi is the direct image
along the small-to-big functor of sites. -/
public noncomputable def restrictionIso {X Y : B.Scheme} (a : X ⟶ Y) :
    restriction a ≅
      (smallProetaleToBigProetaleFunctor B X Y a).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallProetale.topology B X.obj X.property)
        (BigProetaleOver.topology B Y.obj Y.property) := by
  let F := smallProetaleToBigProetaleFunctor B X Y a
  let G := F.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallProetale.topology B X.obj X.property)
    (BigProetaleOver.topology B Y.obj Y.property)
  have : G.Additive := ⟨by intros; rfl⟩
  exact liftSheafNatIso (SmallProetale.topology B X.obj X.property) _ G
    (Functor.isoWhiskerLeft
      (sheafCompose (BigProetaleOver.topology B Y.obj Y.property)
        (forget AddCommGrpCat.{u + 1}))
      (F.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1)) _ _))

end AlgebraicGeometry.ProEtale

end
