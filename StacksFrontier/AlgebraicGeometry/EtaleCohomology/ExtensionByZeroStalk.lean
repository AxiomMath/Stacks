module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Category.Grp.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of extension by zero on the small étale site

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`, and
let `x` be a geometric point of `X`. The stalk at `x` of the extension by zero `j_!F` of an
abelian étale sheaf `F` on `U` is the direct sum of the stalks of `F` at the lifts of `x`
to `U`:

```
(j_!F)_x = ⨁_{x̄ ↦ U} F_{x̄}.
```

The proof identifies both sides as left adjoints of one and the same functor. Taking the
stalk at `x` of the extension by zero is left adjoint to restricting the skyscraper sheaf at
`x`, since it is a composite of two left adjoints; and the direct sum of the stalks at the
lifts is left adjoint to the same functor, because a map out of the direct sum is a family of
maps out of the individual stalks, which is exactly a map into the restricted skyscraper. The
two left adjoints are therefore canonically isomorphic, and the germ formula below pins the
isomorphism down.

Exactness of extension by zero is proved separately, by transporting the exactness of lower
shriek along the slice site: the small étale site of `U` is equivalent to the localization of
the small étale site of `X` at `U`, and under that equivalence extension by zero becomes
lower shriek along `Over.forget U`, which is exact.

## Main definitions

* `AlgebraicGeometry.geometricPointLifts` — the lifts of a geometric point of `X` through an
  étale `U ⟶ X`.
* `AlgebraicGeometry.geometricPointOfLift` — the geometric point of `U` attached to a lift.
* `AlgebraicGeometry.liftedStalk` — the stalk of a sheaf on `U` at a lift.

## Main results

* `AlgebraicGeometry.stalkExtensionByZeroIso` — the stalk of `j_!F` is the direct sum of the
  stalks of `F` at the lifts.
* `AlgebraicGeometry.stalkExtensionByZeroIso_germ` — its value on a germ, which characterises
  it.
* `AlgebraicGeometry.stalkExtensionByZeroIso_naturality` — naturality in the sheaf.
* `AlgebraicGeometry.abelianExtensionByZero_exact` — extension by zero is exact.
* `AlgebraicGeometry.abelianExtensionByZero_stalk_isZero_of_not_mem_range` — the stalk of an
  extension by zero vanishes at a geometric point outside the image of `U`.

## Implementation notes

A lift of `x` to `U` is an element of `AlgebraicGeometry.geometricPointFiber` at `U`; it keeps
the residue field of `x`, so distinct lifts are not identified. The point of the small étale
site attached to a geometric point is `AlgebraicGeometry.geometricPointSitePoint`, and the
stalk of Tag 040R is its presheaf fibre, so Mathlib's skyscraper adjunction for a point of a
site applies directly.

## References

* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

/-- Lower shriek along the forgetful functor of a slice site is exact: it preserves finite
limits because the slice has the finite limits the criterion of Tag 04BH needs, and finite
colimits because it is a left adjoint. -/
public theorem sliceLowerShriek_exactFunctor
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasPullbacks (Over U)]
    [HasEqualizers (Over U)]
    [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.forget U).op.HasPointwiseLeftKanExtension F] :
    exactFunctor _ _ (Functor.sheafPullbackConstruction.sheafPullback
      (Over.forget U) AddCommGrpCat.{w} (J.over U) J) := by
  rw [exactFunctor_iff]
  exact ⟨Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits
      (Over.forget U) (J.over U) J,
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits
      AddCommGrpCat.{w} (Over.forget U) (J.over U) J⟩

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX) (x : GeometricPoint X)

/-- The lifts of a geometric point of `X` to an étale object `U` over `X`: the morphisms from
the source of `x` to `U` commuting with the structure morphism. -/
public abbrev geometricPointLifts : Type u := (geometricPointFiber B X hX x).obj U

/-- The geometric point of `U` determined by a lift of a geometric point of `X`. It keeps the
residue field of `x`, so distinct lifts give distinct geometric points. -/
public def geometricPointOfLift (p : geometricPointLifts B X hX U x) :
    GeometricPoint U.obj.left.1 where
  residueField := x.residueField
  hom := p.1

/-- The stalk at the geometric point of `U` determined by a lift of `x`. -/
public abbrev liftedStalk
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (p : geometricPointLifts B X hX U x) : AddCommGrpCat.{u + 1} :=
  etaleStalk B U.obj.left.1 U.obj.left.property (geometricPointOfLift B X hX U x p) F.obj

/-- The point of the small étale site of `U` determined by a lift of `x`. -/
public abbrev liftedSitePoint (p : geometricPointLifts B X hX U x) :
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property).Point :=
  geometricPointSitePoint B U.obj.left.1 U.obj.left.property (geometricPointOfLift B X hX U x p)

/-- The germ map from the sections over an étale neighbourhood `W ⟶ U` of a lift to the stalk
there, with the stalk read as the fibre of the sheaf at the corresponding point of the
site. -/
public abbrev liftedGerm
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (p : geometricPointLifts B X hX U x)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) :
    F.obj.obj (op W) ⟶ (liftedSitePoint B X hX U x p).sheafFiber.obj F :=
  (liftedSitePoint B X hX U x p).toPresheafFiber W w F.obj

/-- The family of stalks of an abelian sheaf on `U` at all the lifts of `x`, as a functor of
the sheaf. -/
public def stalkFamily :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1} ⥤
      (geometricPointLifts B X hX U x → AddCommGrpCat.{u + 1}) where
  obj F p := (liftedSitePoint B X hX U x p).sheafFiber.obj F
  map f p := (liftedSitePoint B X hX U x p).sheafFiber.map f
  map_id _ := by ext p; simp
  map_comp _ _ := by ext p; simp

/-- Sections of the skyscraper sheaf at `x` over `W` form the product of copies of `M` indexed
by the lifts of `x` to `W`. This is the projection to the copy indexed by one such lift. -/
public def skyscraperπ (M : AddCommGrpCat.{u + 1}) (W : SmallEtale B X hX)
    (q : (geometricPointSitePoint B X hX x).fiber.obj W) :
    ((geometricPointSitePoint B X hX x).skyscraperSheafFunctor.obj M).obj.obj (op W) ⟶ M :=
  Pi.π (fun _ => M) q

/-- The adjunction bijection between maps out of the stalk at `x` and maps into the
skyscraper sheaf at `x`, read componentwise: the component at a lift `q` of a section over `W`
is the germ of that section followed by the given map out of the stalk. -/
public lemma skyscraperSheafAdjunction_app_π
    {F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}} {M : AddCommGrpCat.{u + 1}}
    (f : (geometricPointSitePoint B X hX x).sheafFiber.obj F ⟶ M)
    (W : SmallEtale B X hX) (q : (geometricPointSitePoint B X hX x).fiber.obj W) :
    (((geometricPointSitePoint B X hX x).skyscraperSheafAdjunction.homEquiv F M) f).hom.app
        (op W) ≫ skyscraperπ B X hX x M W q =
      (geometricPointSitePoint B X hX x).toPresheafFiber W q F.obj ≫ f :=
  (congrArg (fun k => k.app (op W) ≫ Pi.π (fun _ => M) q)
    (GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_apply_hom
      (Φ := geometricPointSitePoint B X hX x) f)).trans
    ((geometricPointSitePoint B X hX x).skyscraperPresheafHomEquiv_app_π f W q)

/-- The direct sum of the stalks of a sheaf on `U` at all the lifts of `x`. -/
public abbrev liftedStalkSum
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    AddCommGrpCat.{u + 1} :=
  (stalkFamily B X hX U x ⋙ Sigma.functor (geometricPointLifts B X hX U x)).obj F

/-- The inclusion of the stalk at one lift into the direct sum of the stalks at all of
them. -/
public def liftedStalkι
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (p : geometricPointLifts B X hX U x) :
    (liftedSitePoint B X hX U x p).sheafFiber.obj F ⟶ liftedStalkSum B X hX U x F :=
  Sigma.ι (fun p => (liftedSitePoint B X hX U x p).sheafFiber.obj F) p

/-- The direct sum of the stalks is functorial componentwise. -/
public lemma liftedStalkι_map_assoc
    {F G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) (p : geometricPointLifts B X hX U x) {T : AddCommGrpCat.{u + 1}}
    (h : liftedStalkSum B X hX U x G ⟶ T) :
    liftedStalkι B X hX U x F p ≫
        (stalkFamily B X hX U x ⋙ Sigma.functor (geometricPointLifts B X hX U x)).map f ≫ h =
      (liftedSitePoint B X hX U x p).sheafFiber.map f ≫ liftedStalkι B X hX U x G p ≫ h :=
  Sigma.ι_map_assoc _ p h

section StalkComparison

/-- A lift of `x` to `U` together with a lift of the resulting geometric point of `U` to an
étale `W ⟶ U` gives a lift of `x` to `W` viewed as étale over `X`. -/
public def pushLift (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (p : geometricPointLifts B X hX U x)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) :
    (geometricPointSitePoint B X hX x).fiber.obj
      ((smallEtalePostcompose B X hX U).obj W) :=
  ⟨w.1, by
    change w.1 ≫ B.inclusion.map W.obj.hom ≫ B.inclusion.map U.obj.hom = x.hom
    rw [← Category.assoc, w.2]
    exact p.2⟩

/-- Lifting `x` to an étale `W ⟶ U` viewed over `X` is the same as lifting `x` to `U` and then
lifting the resulting geometric point of `U` to `W`. -/
public def liftFiberEquiv (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (Σ p : geometricPointLifts B X hX U x, (liftedSitePoint B X hX U x p).fiber.obj W) ≃
      (geometricPointSitePoint B X hX x).fiber.obj
        ((smallEtalePostcompose B X hX U).obj W) where
  toFun pw := pushLift B X hX U x W pw.1 pw.2
  invFun q := ⟨⟨q.1 ≫ B.inclusion.map W.obj.hom, by
    change (q.1 ≫ B.inclusion.map W.obj.hom) ≫ B.inclusion.map U.obj.hom = x.hom
    exact q.2⟩, ⟨q.1, rfl⟩⟩
  left_inv := by
    rintro ⟨p, w⟩
    apply Sigma.ext (Subtype.ext (by exact w.2))
    apply (Subtype.heq_iff_coe_eq ?_).2
    · rfl
    · intro t
      change (t ≫ B.inclusion.map W.obj.hom = w.1 ≫ B.inclusion.map W.obj.hom) ↔
        (t ≫ B.inclusion.map W.obj.hom = p.1)
      rw [show w.1 ≫ B.inclusion.map W.obj.hom = p.1 from w.2]
  right_inv q := by apply Subtype.ext; rfl

/-- The bijection of lifts is given by pushing a pair of lifts forward. -/
@[simp]
public lemma liftFiberEquiv_apply (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (p : geometricPointLifts B X hX U x)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) :
    liftFiberEquiv B X hX U x W ⟨p, w⟩ = pushLift B X hX U x W p w :=
  rfl

/-- Pushing a lift forward commutes with restriction along a morphism of the small étale site
of `U`. -/
public lemma pushLift_map
    {W V : SmallEtale B U.obj.left.1 U.obj.left.property} (f : W ⟶ V)
    (p : geometricPointLifts B X hX U x)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) :
    (geometricPointSitePoint B X hX x).fiber.map ((smallEtalePostcompose B X hX U).map f)
      (pushLift B X hX U x W p w) =
      pushLift B X hX U x V p ((liftedSitePoint B X hX U x p).fiber.map f w) := by
  apply Subtype.ext
  rfl

/-- The restriction to `U` of the skyscraper sheaf at `x`. It is the right adjoint shared by
the stalk of the extension by zero and by the direct sum of the stalks at the lifts. -/
public abbrev restrictedSkyscraper :
    AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1} :=
  (geometricPointSitePoint B X hX x).skyscraperSheafFunctor (A := AddCommGrpCat.{u + 1}) ⋙
    abelianRestriction B X hX U

/-- Sections of the restricted skyscraper sheaf over `W` form the product of copies of `M`
indexed by the lifts of `x` to `W` seen as étale over `X`. This is the projection to the copy
indexed by one such lift. -/
public def restrictedSkyscraperπ (M : AddCommGrpCat.{u + 1})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointSitePoint B X hX x).fiber.obj
      ((smallEtalePostcompose B X hX U).obj W)) :
    ((restrictedSkyscraper B X hX U x).obj M).obj.obj (op W) ⟶ M :=
  Pi.π (fun _ => M) q

/-- Two maps into the sections of the restricted skyscraper sheaf over `W` agree as soon as
all their components agree. -/
public lemma restrictedSkyscraper_hom_ext {M : AddCommGrpCat.{u + 1}}
    {W : SmallEtale B U.obj.left.1 U.obj.left.property} {Y : AddCommGrpCat.{u + 1}}
    {a b : Y ⟶ ((restrictedSkyscraper B X hX U x).obj M).obj.obj (op W)}
    (h : ∀ q, a ≫ restrictedSkyscraperπ B X hX U x M W q =
      b ≫ restrictedSkyscraperπ B X hX U x M W q) : a = b :=
  Pi.hom_ext _ _ h

/-- The restriction maps of the restricted skyscraper sheaf are the reindexings of the
product along the action of the lifts. -/
public lemma restrictedSkyscraper_obj_map_π (M : AddCommGrpCat.{u + 1})
    {W V : SmallEtale B U.obj.left.1 U.obj.left.property} (f : W ⟶ V)
    (q : (geometricPointSitePoint B X hX x).fiber.obj
      ((smallEtalePostcompose B X hX U).obj W)) :
    ((restrictedSkyscraper B X hX U x).obj M).obj.map f.op ≫
        restrictedSkyscraperπ B X hX U x M W q =
      restrictedSkyscraperπ B X hX U x M V ((geometricPointSitePoint B X hX x).fiber.map
        ((smallEtalePostcompose B X hX U).map f) q) :=
  (Limits.Pi.map'_comp_π
    (f := fun _ : (geometricPointSitePoint B X hX x).fiber.obj
      ((smallEtalePostcompose B X hX U).obj V) => M)
    (g := fun _ : (geometricPointSitePoint B X hX x).fiber.obj
      ((smallEtalePostcompose B X hX U).obj W) => M)
    ((geometricPointSitePoint B X hX x).fiber.map
      ((smallEtalePostcompose B X hX U).map f)) (fun _ => 𝟙 M) q).trans
    (Category.comp_id _)

/-- Post-composition with a map of abelian groups acts componentwise on the restricted
skyscraper sheaf. -/
public lemma restrictedSkyscraperπ_naturality {M N : AddCommGrpCat.{u + 1}} (g : M ⟶ N)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointSitePoint B X hX x).fiber.obj
      ((smallEtalePostcompose B X hX U).obj W)) :
    ((restrictedSkyscraper B X hX U x).map g).hom.app (op W) ≫
        restrictedSkyscraperπ B X hX U x N W q =
      restrictedSkyscraperπ B X hX U x M W q ≫ g :=
  Pi.map_π (fun _ => g) q

variable {B X hX U x}
variable (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    AddCommGrpCat.{u + 1}) (M : AddCommGrpCat.{u + 1})

/-- The component at `W` of the map to the restricted skyscraper sheaf determined by a family
of maps out of the stalks at the lifts. -/
public def stalkFamilyToSkyscraperApp
    (f : ∀ p, (liftedSitePoint B X hX U x p).sheafFiber.obj F ⟶ M)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    F.obj.obj (op W) ⟶ ((restrictedSkyscraper B X hX U x).obj M).obj.obj (op W) :=
  Pi.lift fun q =>
    let pw := (liftFiberEquiv B X hX U x W).symm q
    liftedGerm B X hX U x F pw.1 W pw.2 ≫ f pw.1

/-- The defining formula for the components of `stalkFamilyToSkyscraperApp`. -/
public lemma stalkFamilyToSkyscraperApp_π
    (f : ∀ p, (liftedSitePoint B X hX U x p).sheafFiber.obj F ⟶ M)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (p : geometricPointLifts B X hX U x)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) :
    stalkFamilyToSkyscraperApp F M f W ≫
        restrictedSkyscraperπ B X hX U x M W (pushLift B X hX U x W p w) =
      liftedGerm B X hX U x F p W w ≫ f p := by
  show Pi.lift _ ≫ Pi.π _ ((liftFiberEquiv B X hX U x W) ⟨p, w⟩) = _
  rw [Pi.lift_π, Equiv.symm_apply_apply]

/-- A family of maps out of the stalks at the lifts assembles into a map to the restricted
skyscraper sheaf. -/
public def stalkFamilyToSkyscraper
    (f : ∀ p, (liftedSitePoint B X hX U x p).sheafFiber.obj F ⟶ M) :
    F ⟶ (restrictedSkyscraper B X hX U x).obj M where
  hom :=
    { app W := stalkFamilyToSkyscraperApp F M f W.unop
      naturality {W V} g := by
        apply restrictedSkyscraper_hom_ext
        intro q
        obtain ⟨⟨p, w⟩, rfl⟩ := (liftFiberEquiv B X hX U x V.unop).surjective q
        rw [← Quiver.Hom.op_unop g, liftFiberEquiv_apply, Category.assoc,
          stalkFamilyToSkyscraperApp_π, Category.assoc,
          restrictedSkyscraper_obj_map_π, pushLift_map, stalkFamilyToSkyscraperApp_π]
        exact (liftedSitePoint B X hX U x p).toPresheafFiber_w_assoc g.unop w F.obj (f p) }

/-- A map to the restricted skyscraper sheaf restricts to a map out of the stalk at each
lift. -/
public def skyscraperToStalkFamily (g : F ⟶ (restrictedSkyscraper B X hX U x).obj M)
    (p : geometricPointLifts B X hX U x) :
    (liftedSitePoint B X hX U x p).sheafFiber.obj F ⟶ M :=
  (liftedSitePoint B X hX U x p).presheafFiberDesc
    (fun W w => g.hom.app (op W) ≫
      restrictedSkyscraperπ B X hX U x M W (pushLift B X hX U x W p w)) (by
      intro W V f w
      change F.obj.map f.op ≫ (g.hom.app (op W) ≫
        restrictedSkyscraperπ B X hX U x M W (pushLift B X hX U x W p w)) = _
      rw [← Category.assoc, g.hom.naturality f.op, Category.assoc,
        restrictedSkyscraper_obj_map_π, pushLift_map])

/-- Families of maps out of the stalks at the lifts correspond to maps into the restricted
skyscraper sheaf. -/
public def stalkFamilySkyscraperEquiv :
    (∀ p, (liftedSitePoint B X hX U x p).sheafFiber.obj F ⟶ M) ≃
      (F ⟶ (restrictedSkyscraper B X hX U x).obj M) where
  toFun := stalkFamilyToSkyscraper F M
  invFun := skyscraperToStalkFamily F M
  left_inv f := by
    funext p
    apply (liftedSitePoint B X hX U x p).presheafFiber_hom_ext
    intro W w
    simp only [skyscraperToStalkFamily,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
    exact stalkFamilyToSkyscraperApp_π F M f W p w
  right_inv g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    obtain ⟨W⟩ := W
    apply restrictedSkyscraper_hom_ext
    intro q
    obtain ⟨⟨p, w⟩, rfl⟩ := (liftFiberEquiv B X hX U x W).surjective q
    change stalkFamilyToSkyscraperApp F M _ W ≫
      restrictedSkyscraperπ B X hX U x M W (pushLift B X hX U x W p w) = _
    rw [stalkFamilyToSkyscraperApp_π]
    exact (liftedSitePoint B X hX U x p).toPresheafFiber_presheafFiberDesc _ _ W w

/-- Maps out of the direct sum of the stalks at the lifts correspond to maps into the
restricted skyscraper sheaf. -/
public def directSumHomEquiv :
    ((stalkFamily B X hX U x ⋙ Sigma.functor (geometricPointLifts B X hX U x)).obj F ⟶ M) ≃
      (F ⟶ (restrictedSkyscraper B X hX U x).obj M) :=
  (show (∐ (fun p => (liftedSitePoint B X hX U x p).sheafFiber.obj F) ⟶ M) ≃
    (∀ p, (liftedSitePoint B X hX U x p).sheafFiber.obj F ⟶ M) from
    { toFun := fun f p =>
        Sigma.ι (fun p => (liftedSitePoint B X hX U x p).sheafFiber.obj F) p ≫ f
      invFun := fun f => Sigma.desc f
      left_inv f := Sigma.hom_ext _ _ fun p => by simp
      right_inv f := funext fun p => by simp }).trans (stalkFamilySkyscraperEquiv F M)

/-- The defining formula for the components of `directSumHomEquiv`. -/
public lemma directSumHomEquiv_π (f : liftedStalkSum B X hX U x F ⟶ M)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (p : geometricPointLifts B X hX U x)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) :
    (directSumHomEquiv F M f).hom.app (op W) ≫
        restrictedSkyscraperπ B X hX U x M W (pushLift B X hX U x W p w) =
      liftedGerm B X hX U x F p W w ≫ liftedStalkι B X hX U x F p ≫ f :=
  stalkFamilyToSkyscraperApp_π F M _ W p w

/-- The germ map into the stalk at a lift is natural in the sheaf. -/
public lemma liftedGerm_naturality_assoc
    {F G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) (p : geometricPointLifts B X hX U x)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) {T : AddCommGrpCat.{u + 1}}
    (h : (liftedSitePoint B X hX U x p).sheafFiber.obj G ⟶ T) :
    liftedGerm B X hX U x F p W w ≫ (liftedSitePoint B X hX U x p).sheafFiber.map f ≫ h =
      f.hom.app (op W) ≫ liftedGerm B X hX U x G p W w ≫ h :=
  (liftedSitePoint B X hX U x p).toPresheafFiber_naturality_assoc f.hom W w h

/-- The germ into a summand of the direct sum of the stalks is natural in the sheaf. -/
public lemma liftedGerm_ι_map_assoc
    {F G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) (p : geometricPointLifts B X hX U x)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (w : (liftedSitePoint B X hX U x p).fiber.obj W) {T : AddCommGrpCat.{u + 1}}
    (h : liftedStalkSum B X hX U x G ⟶ T) :
    liftedGerm B X hX U x F p W w ≫ liftedStalkι B X hX U x F p ≫
        (stalkFamily B X hX U x ⋙ Sigma.functor (geometricPointLifts B X hX U x)).map f ≫ h =
      f.hom.app (op W) ≫ liftedGerm B X hX U x G p W w ≫
        liftedStalkι B X hX U x G p ≫ h := by
  rw [liftedStalkι_map_assoc, liftedGerm_naturality_assoc]

variable (B X hX U x)

/-- The direct sum of the stalks at the lifts of `x` is left adjoint to the restricted
skyscraper sheaf at `x`. -/
public def directSumAdjunction :
    (stalkFamily B X hX U x ⋙ Sigma.functor (geometricPointLifts B X hX U x)) ⊣
      restrictedSkyscraper B X hX U x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := directSumHomEquiv
      homEquiv_naturality_left_symm := by
        intro F G M f g
        apply (directSumHomEquiv F M).injective
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext W
        obtain ⟨W⟩ := W
        apply restrictedSkyscraper_hom_ext
        intro q
        obtain ⟨⟨p, w⟩, rfl⟩ := (liftFiberEquiv B X hX U x W).surjective q
        rw [liftFiberEquiv_apply, Equiv.apply_symm_apply]
        change (f.hom.app (op W) ≫ g.hom.app (op W)) ≫
          restrictedSkyscraperπ B X hX U x M W (pushLift B X hX U x W p w) = _
        rw [directSumHomEquiv_π]
        change _ = liftedGerm B X hX U x F p W w ≫ liftedStalkι B X hX U x F p ≫
          (stalkFamily B X hX U x ⋙ Sigma.functor (geometricPointLifts B X hX U x)).map f ≫
            (directSumHomEquiv G M).symm g
        rw [liftedGerm_ι_map_assoc]
        have h := directSumHomEquiv_π G M ((directSumHomEquiv G M).symm g) W p w
        rw [Equiv.apply_symm_apply] at h
        exact congrArg (fun k => f.hom.app (op W) ≫ k) h
      homEquiv_naturality_right := by
        intro F M N f g
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext W
        obtain ⟨W⟩ := W
        apply restrictedSkyscraper_hom_ext
        intro q
        obtain ⟨⟨p, w⟩, rfl⟩ := (liftFiberEquiv B X hX U x W).surjective q
        rw [liftFiberEquiv_apply, directSumHomEquiv_π]
        change _ = (directSumHomEquiv F M f).hom.app (op W) ≫
          ((restrictedSkyscraper B X hX U x).map g).hom.app (op W) ≫
            restrictedSkyscraperπ B X hX U x N W (pushLift B X hX U x W p w)
        rw [restrictedSkyscraperπ_naturality]
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ g) (directSumHomEquiv_π F M f W p w).symm }

/-- The component at an étale neighbourhood `W ⟶ U` of the unit of the extension-by-zero
adjunction: it sends a section over `W` to its image in the extension by zero, over `W` seen
as étale over `X`. -/
public def extensionByZeroUnitApp
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    F.obj.obj (op W) ⟶
      ((abelianExtensionByZero B X hX U).obj F).obj.obj
        (op ((smallEtalePostcompose B X hX U).obj W)) :=
  ((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (op W)

/-- Taking the stalk at `x` of the extension by zero is left adjoint to the restricted
skyscraper sheaf at `x`, being the composite of two left adjoints. -/
public def extensionStalkAdjunction :
    (abelianExtensionByZero B X hX U ⋙ (geometricPointSitePoint B X hX x).sheafFiber) ⊣
      restrictedSkyscraper B X hX U x :=
  (abelianExtensionByZeroAdjunction B X hX U).comp
    (geometricPointSitePoint B X hX x).skyscraperSheafAdjunction

/-- The defining formula for the components of the adjunction bijection of
`extensionStalkAdjunction`. -/
public lemma extensionStalkHomEquiv_π
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (M : AddCommGrpCat.{u + 1})
    (f : (geometricPointSitePoint B X hX x).sheafFiber.obj
      ((abelianExtensionByZero B X hX U).obj F) ⟶ M)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointSitePoint B X hX x).fiber.obj
      ((smallEtalePostcompose B X hX U).obj W)) :
    ((extensionStalkAdjunction B X hX U x).homEquiv F M f).hom.app (op W) ≫
        restrictedSkyscraperπ B X hX U x M W q =
      extensionByZeroUnitApp B X hX U F W ≫
        (geometricPointSitePoint B X hX x).toPresheafFiber
          ((smallEtalePostcompose B X hX U).obj W) q
          ((abelianExtensionByZero B X hX U).obj F).obj ≫ f := by
  rw [extensionStalkAdjunction, Adjunction.comp_homEquiv]
  show (((abelianExtensionByZeroAdjunction B X hX U).homEquiv F _
      ((geometricPointSitePoint B X hX x).skyscraperSheafAdjunction.homEquiv _ M f)).hom.app
        (op W)) ≫
    skyscraperπ B X hX x M ((smallEtalePostcompose B X hX U).obj W) q = _
  rw [Adjunction.homEquiv_apply]
  show (extensionByZeroUnitApp B X hX U F W ≫
      (((geometricPointSitePoint B X hX x).skyscraperSheafAdjunction.homEquiv _ M f).hom.app
        (op ((smallEtalePostcompose B X hX U).obj W)))) ≫
    skyscraperπ B X hX x M ((smallEtalePostcompose B X hX U).obj W) q = _
  rw [Category.assoc, skyscraperSheafAdjunction_app_π]

/-- The two left adjoints of the restricted skyscraper sheaf agree. -/
public def extensionStalkIso :
    (abelianExtensionByZero B X hX U ⋙ (geometricPointSitePoint B X hX x).sheafFiber) ≅
      (stalkFamily B X hX U x ⋙ Sigma.functor (geometricPointLifts B X hX U x)) :=
  (extensionStalkAdjunction B X hX U x).leftAdjointUniq (directSumAdjunction B X hX U x)

end StalkComparison

/-- **Stacks 03S5.** The stalk at a geometric point `x` of `X` of the extension by zero of an
abelian étale sheaf on `U` is the direct sum of its stalks at the lifts of `x` to `U`. -/
@[stacks 03S5 "stalk formula"]
public def stalkExtensionByZeroIso
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    etaleStalk B X hX x ((abelianExtensionByZero B X hX U).obj F).obj ≅
      (∐ fun p : geometricPointLifts B X hX U x => liftedStalk B X hX U x F p) :=
  (extensionStalkIso B X hX U x).app F

/-- **Stacks 03S5.** The stalk isomorphism sends the germ of a section over an étale
neighbourhood `W ⟶ U`, viewed in the extension by zero through the adjunction unit, to its
germ at the induced lift, in the corresponding summand of the direct sum. This formula
characterises the isomorphism. -/
@[stacks 03S5 "germ computation"]
public theorem stalkExtensionByZeroIso_germ
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (p : geometricPointLifts B X hX U x)
    (w : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (geometricPointOfLift B X hX U x p)).obj W)
    (q : (geometricPointFiber B X hX x).obj ((smallEtalePostcompose B X hX U).obj W))
    (hq : q.1 = w.1) (s : F.obj.obj (op W)) :
    (stalkExtensionByZeroIso B X hX U x F).hom
      ((colimit.ι ((CategoryOfElements.π (geometricPointFiber B X hX x)).op ⋙
          ((abelianExtensionByZero B X hX U).obj F).obj)
          (op ⟨(smallEtalePostcompose B X hX U).obj W, q⟩))
        (((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (op W) s)) =
      (Sigma.ι (fun p : geometricPointLifts B X hX U x => liftedStalk B X hX U x F p) p)
        ((colimit.ι ((CategoryOfElements.π (geometricPointFiber B U.obj.left.1
            U.obj.left.property (geometricPointOfLift B X hX U x p))).op ⋙ F.obj)
          (op ⟨W, w⟩)) s) := by
  obtain rfl : q = pushLift B X hX U x W p w := Subtype.ext hq
  have h := (extensionStalkAdjunction B X hX U x).homEquiv_leftAdjointUniq_hom_app
    (directSumAdjunction B X hX U x) F
  have hu : (directSumAdjunction B X hX U x).unit.app F = directSumHomEquiv F _ (𝟙 _) := by
    rw [← Adjunction.homEquiv_id, directSumAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rw [hu] at h
  have he := congrArg (fun k => k.hom.app (op W) ≫
    restrictedSkyscraperπ B X hX U x _ W (pushLift B X hX U x W p w)) h
  rw [extensionStalkHomEquiv_π, directSumHomEquiv_π F _ (𝟙 _) W p w, Category.comp_id] at he
  exact ConcreteCategory.congr_hom he s

/-- **Stacks 03S5.** The stalk decomposition of extension by zero is natural in the abelian
sheaf. -/
@[stacks 03S5 "naturality"]
public theorem stalkExtensionByZeroIso_naturality
    {F G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) :
    colimMap (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B X hX x)).op
        ((abelianExtensionByZero B X hX U).map f).hom) ≫
        (stalkExtensionByZeroIso B X hX U x G).hom =
      (stalkExtensionByZeroIso B X hX U x F).hom ≫
        Limits.Sigma.map (fun p : geometricPointLifts B X hX U x =>
          colimMap (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber
            B U.obj.left.1 U.obj.left.property (geometricPointOfLift B X hX U x p))).op f.hom)) :=
  (extensionStalkIso B X hX U x).hom.naturality f

/-- **Stacks 03S5.** Extension by zero of abelian sheaves along an étale morphism is exact.
Under the equivalence of the small étale site of `U` with the localization of the small étale
site of `X` at `U`, extension by zero becomes lower shriek along `Over.forget U`, which is
exact. -/
@[stacks 03S5 "exactness"]
public theorem abelianExtensionByZero_exact :
    exactFunctor _ _ (abelianExtensionByZero B X hX U) := by
  let J := SmallEtale.topology B X hX
  let K := J.over U
  let e := smallEtaleEquivalenceOver B X hX U
  let : HasTerminal (Over U) := CategoryTheory.Over.over_hasTerminal U
  let : HasBinaryProducts (Over U) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks (C := Over U)
  let : HasEqualizers (Over U) := hasEqualizers_of_hasPullbacks_and_binary_products
  have htop := smallEtaleEquivalenceOver_topology B X hX U
  have hDense : e.inverse.IsDenseSubsite K (e.functor.inducedTopology K) := by
    let e' := e.symm
    show e'.functor.IsDenseSubsite K (e'.inverse.inducedTopology K)
    infer_instance
  let : e.inverse.IsDenseSubsite K
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property) := by
    rw [← htop]
    exact hDense
  let E := e.sheafCongr (SmallEtale.topology B U.obj.left.1 U.obj.left.property) K
    AddCommGrpCat.{u + 1}
  let : e.functor.IsContinuous
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property) K := by
    rw [← htop]
    infer_instance
  let : (e.functor ⋙ Over.forget U).IsContinuous
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property) J :=
    Functor.isContinuous_comp e.functor (Over.forget U)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property) K J
  let : HasWeakSheafify J AddCommGrpCat.{u + 1} := by
    dsimp [J]
    infer_instance
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
    dsimp [J]
    infer_instance
  have hSheafify : HasSheafify J AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify J AddCommGrpCat.{u + 1} := hSheafify
  let L := Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget U) AddCommGrpCat.{u + 1} K J
  obtain ⟨_, _⟩ := (exactFunctor_iff L).1
    (@sliceLowerShriek_exactFunctor _ _ J U hSheafify inferInstance inferInstance inferInstance)
  have hComp : exactFunctor _ _ (E.functor ⋙ L) :=
    (exactFunctor_iff _).2 ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩
  have hPush : abelianRestriction B X hX U ≅
      (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u + 1} K J ⋙ E.inverse := by
    show (smallEtalePostcompose B X hX U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) J ≅
      (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u + 1} K J ⋙
        e.functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B U.obj.left.1 U.obj.left.property) K
    exact (Functor.sheafPushforwardContinuousComp e.functor (Over.forget U)
        AddCommGrpCat.{u + 1} (SmallEtale.topology B U.obj.left.1 U.obj.left.property) K J ≪≫
      Functor.sheafPushforwardContinuousIso
        (eqToIso (smallEtaleEquivalenceOver_restriction B X hX U)) AddCommGrpCat.{u + 1}
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) J).symm
  refine (exactFunctor _ _).prop_of_iso (Adjunction.leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtalePostcompose B X hX U) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property) J)
    ((E.toAdjunction.comp (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.forget U) AddCommGrpCat.{u + 1} K J)).ofNatIsoRight hPush.symm)).symm hComp

/-- A geometric point of `X` outside the image of `U` has no lifts to `U`: a lift would send
the point of its source to a preimage. -/
private theorem geometricPointLifts_eq_empty
    (hx : x.hom default ∉ Set.range (B.inclusion.map U.obj.hom).base) :
    IsEmpty (geometricPointLifts B X hX U x) :=
  ⟨fun p => hx ⟨p.1 default, by simpa using congrArg (fun f => f default) p.2⟩⟩

/-- A coproduct of abelian groups indexed by an empty type is a zero object: it receives no
summand inclusions, so there is exactly one map out of it to any group. -/
public theorem isZero_sigma_of_isEmpty {I : Type u} [IsEmpty I]
    (K : I → AddCommGrpCat.{u + 1}) : IsZero (∐ K) := by
  have : ∀ Y : AddCommGrpCat.{u + 1}, Unique (∐ K ⟶ Y) := fun Y =>
    ⟨⟨0⟩, fun f => Sigma.hom_ext _ _ isEmptyElim⟩
  exact IsZero.of_iso (isZero_zero _)
    (IsInitial.uniqueUpToIso (IsInitial.ofUnique _) (isZero_zero _).isInitial)

/-- **Stacks 0F70.** The extension by zero of an abelian étale sheaf on `U` has zero stalk at
every geometric point of `X` outside the image of `U`: by the stalk formula the stalk is the
direct sum over the lifts of that point, and there are none. -/
@[stacks 0F70 "extension_by_zero_characterization: zero stalks",
  stacks 0F70 "extension_by_zero_characterization"]
public theorem abelianExtensionByZero_stalk_isZero_of_not_mem_range
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (hx : x.hom default ∉ Set.range (B.inclusion.map U.obj.hom).base) :
    IsZero (etaleStalk B X hX x ((abelianExtensionByZero B X hX U).obj F).obj) := by
  classical
  have := geometricPointLifts_eq_empty B X hX U x hx
  exact IsZero.of_iso (isZero_sigma_of_isEmpty _) (stalkExtensionByZeroIso B X hX U x F)

end AlgebraicGeometry

end
