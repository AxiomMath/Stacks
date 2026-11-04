module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The category of polarized proper schemes (Stacks 0D1M)

A *polarized family* is a morphism of schemes `X ⟶ S` which is proper, flat and of finite
presentation, together with an invertible `𝒪_X`-module which is relatively ample on `X/S`. A
morphism of polarized families is a cartesian square of structure morphisms together with an
isomorphism identifying the pullback of the polarization of the target with the polarization of
the source, and forgetting a polarized family to its base scheme exhibits the resulting category
as a category over the big fppf site of schemes.

## Main definitions

* `AlgebraicGeometry.PolarizedFamily`: **Stacks 0D1M**, the objects.
* `AlgebraicGeometry.PolarizedFamily.Hom`: **Stacks 0D1M**, the morphisms.
* `AlgebraicGeometry.PolarizedFamily.instCategory`: **Stacks 0D1M**, the category.
* `AlgebraicGeometry.polarizedProjection`: **Stacks 0D1M**, the forgetful functor to the big fppf
  site.

## Implementation notes

The big fppf site of the source is absolute, while this library's big fppf site is a size-bounded
category of schemes. Only the *base* of a polarized family is asked to lie in the site; the total
space is an arbitrary scheme of the same universe, so no size hypothesis is imposed on the family
itself. The cartesian condition on a morphism is a `CategoryTheory.IsPullback` in `Scheme`, which
is the square of the site read through `AlgebraicGeometry.BigFppfSite.inclusion`.

Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple` of Stacks 01VH, whose
statement keys on an *instance* of the Stacks 01CS invertibility predicate
`AlgebraicGeometry.SheafOfModules.IsInvertible`; invertibility is therefore carried as its own
field and supplied to the ampleness field with `letI`. Since invertibility is `Prop`-valued,
proof irrelevance makes relative ampleness independent of that witness.

Composition of morphisms multiplies the comparisons of polarizations using the pullback
pseudofunctor `AlgebraicGeometry.Scheme.Modules.pullback` of Mathlib, so the three category laws
are its pseudofunctor coherences
(`AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality`, `pseudofunctor_right_unitality`
and `pseudofunctor_associativity`) together with the identity and pasting lemmas for pullback
squares. The comparison of a morphism is typed through its morphism of total spaces, so an
equality of morphisms of polarized families is an equality of the two underlying morphisms *and* a
heterogeneous equality of the comparisons; that is `AlgebraicGeometry.PolarizedFamily.Hom.ext`,
and the three coherences are proved in exactly that shape, the transport along the equality of
total maps being `CategoryTheory.eqToIso` because
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is.

## References

* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u})

/-- **Stacks 0D1M.** A *polarized family*: a proper, flat, finitely presented morphism from a
scheme to a scheme of the big fppf site, together with an invertible module on the total space
which is relatively ample for that morphism. -/
@[stacks 0D1M "objects"]
structure PolarizedFamily where
  /-- The base scheme of the family, an object of the big fppf site. -/
  base : B.Schemes
  /-- The total space of the family. -/
  total : Scheme.{u}
  /-- The structure morphism of the family. -/
  toBase : total ⟶ B.inclusion.obj base
  /-- The structure morphism is proper. -/
  proper : IsProper toBase
  /-- The structure morphism is flat (Stacks 01U3). -/
  flat : Flat toBase
  /-- The structure morphism is of finite presentation (Stacks 01TP). -/
  finitePresentation : FinitePresentation toBase
  /-- The polarization, a module on the total space. -/
  lineBundle : total.Modules
  /-- The polarization is invertible (Stacks 01CS). -/
  invertible : SheafOfModules.IsInvertible total.presheaf total.ringCatSheaf.2 lineBundle
  /-- The polarization is relatively ample for the structure morphism (Stacks 01VH). -/
  relativelyAmple :
    letI := invertible
    Stacks.RelativeAmple.IsRelativelyAmple toBase lineBundle

namespace PolarizedFamily

variable {B}

/-- **Stacks 0D1M.** A morphism of polarized families: a morphism of total spaces over a morphism
of base schemes whose square is cartesian, together with an isomorphism from the pullback of the
polarization of the target to the polarization of the source. -/
@[stacks 0D1M "morphisms"]
structure Hom (X Y : PolarizedFamily B) where
  /-- The morphism of base schemes. -/
  baseMap : X.base ⟶ Y.base
  /-- The morphism of total spaces. -/
  totalMap : X.total ⟶ Y.total
  /-- The square of structure morphisms is cartesian. -/
  cartesian : IsPullback totalMap X.toBase Y.toBase (B.inclusion.map baseMap)
  /-- The comparison of polarizations. -/
  lineBundleIso : (Scheme.Modules.pullback totalMap).obj Y.lineBundle ≅ X.lineBundle

/-- Two morphisms of polarized families agree as soon as their base maps and their maps of total
spaces agree and their comparisons of polarizations agree over the latter. The comparison is typed
through the map of total spaces, so its equality is heterogeneous. -/
theorem Hom.ext {X Y : PolarizedFamily B} {f g : Hom X Y} (hbase : f.baseMap = g.baseMap)
    (htotal : f.totalMap = g.totalMap) (hline : f.lineBundleIso ≍ g.lineBundleIso) : f = g := by
  obtain ⟨fb, ft, fc, fi⟩ := f
  obtain ⟨gb, gt, gc, gi⟩ := g
  subst hbase
  subst htotal
  obtain rfl : fi = gi := eq_of_heq hline
  rfl

/-- A composite of an `eqToIso` with an isomorphism is heterogeneously that isomorphism; this is
how a transported comparison of polarizations is recognised. -/
theorem eqToIso_trans_heq {C : Type*} [Category C] {A A' D : C} (h : A = A')
    (e : A' ≅ D) : eqToIso h ≪≫ e ≍ e := by
  cases h
  simpa only [eqToIso_refl, Iso.refl_trans] using (HEq.rfl : e ≍ e)

/-- An isomorphism whose forward map is an `eqToHom` followed by that of `e` is heterogeneously
equal to `e`. -/
private theorem iso_heq_of_hom_eq {C : Type*} [Category C] {A A' D : C} (h : A = A')
    (i : A ≅ D) (e : A' ≅ D) (hi : i.hom = eqToHom h ≫ e.hom) : i ≍ e :=
  (heq_of_eq (Iso.ext hi : i = eqToIso h ≪≫ e)).trans (eqToIso_trans_heq h e)

/-- The identity morphism of a polarized family: the identity square, with the canonical
identification of the pullback of the polarization along the identity. -/
protected def id (X : PolarizedFamily B) : Hom X X where
  baseMap := 𝟙 X.base
  totalMap := 𝟙 X.total
  cartesian := by
    rw [B.inclusion.map_id X.base]
    exact IsPullback.id_horiz X.toBase
  lineBundleIso := (Scheme.Modules.pullbackId X.total).app X.lineBundle

/-- The composite of two morphisms of polarized families: the pasted square, with the comparison
of polarizations obtained from the pullback pseudofunctor. -/
protected def comp {X Y Z : PolarizedFamily B} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  baseMap := f.baseMap ≫ g.baseMap
  totalMap := f.totalMap ≫ g.totalMap
  cartesian := by
    rw [B.inclusion.map_comp f.baseMap g.baseMap]
    exact f.cartesian.paste_horiz g.cartesian
  lineBundleIso :=
    (Scheme.Modules.pullbackComp f.totalMap g.totalMap).symm.app Z.lineBundle ≪≫
      (Scheme.Modules.pullback f.totalMap).mapIso g.lineBundleIso ≪≫ f.lineBundleIso

/-- The identity is a left unit for composition of morphisms of polarized families; on the
comparisons of polarizations this is the right unitality of the pullback pseudofunctor. -/
protected theorem id_comp {X Y : PolarizedFamily B} (f : Hom X Y) :
    PolarizedFamily.comp (PolarizedFamily.id X) f = f := by
  refine Hom.ext (by simp [PolarizedFamily.id, PolarizedFamily.comp])
    (by simp [PolarizedFamily.id, PolarizedFamily.comp]) ?_
  have hobj : (Scheme.Modules.pullback (𝟙 X.total ≫ f.totalMap)).obj Y.lineBundle =
      (Scheme.Modules.pullback f.totalMap).obj Y.lineBundle := by simp
  have h := congrArg (fun α => α.app Y.lineBundle)
    (Scheme.Modules.pseudofunctor_right_unitality f.totalMap)
  have h' : (Scheme.Modules.pullbackComp (𝟙 X.total) f.totalMap).inv.app Y.lineBundle ≫
      (Scheme.Modules.pullbackId X.total).hom.app
        ((Scheme.Modules.pullback f.totalMap).obj Y.lineBundle) ≫ f.lineBundleIso.hom =
      eqToHom hobj ≫ f.lineBundleIso.hom := by
    simpa [Functor.whiskerLeft_app, Category.assoc] using
      congrArg (fun k => k ≫ f.lineBundleIso.hom) h
  exact iso_heq_of_hom_eq hobj _ _
    (by simpa [PolarizedFamily.id, PolarizedFamily.comp, Category.assoc] using h')

/-- The identity is a right unit for composition of morphisms of polarized families; on the
comparisons of polarizations this is the left unitality of the pullback pseudofunctor. -/
protected theorem comp_id {X Y : PolarizedFamily B} (f : Hom X Y) :
    PolarizedFamily.comp f (PolarizedFamily.id Y) = f := by
  refine Hom.ext (by simp [PolarizedFamily.id, PolarizedFamily.comp])
    (by simp [PolarizedFamily.id, PolarizedFamily.comp]) ?_
  have hobj : (Scheme.Modules.pullback (f.totalMap ≫ 𝟙 Y.total)).obj Y.lineBundle =
      (Scheme.Modules.pullback f.totalMap).obj Y.lineBundle := by simp
  have h := congrArg (fun α => α.app Y.lineBundle)
    (Scheme.Modules.pseudofunctor_left_unitality f.totalMap)
  have h' : (Scheme.Modules.pullbackComp f.totalMap (𝟙 Y.total)).inv.app Y.lineBundle ≫
      (Scheme.Modules.pullback f.totalMap).map
        ((Scheme.Modules.pullbackId Y.total).hom.app Y.lineBundle) ≫ f.lineBundleIso.hom =
      eqToHom hobj ≫ f.lineBundleIso.hom := by
    simpa [Functor.whiskerRight_app, Category.assoc] using
      congrArg (fun k => k ≫ f.lineBundleIso.hom) h
  exact iso_heq_of_hom_eq hobj _ _
    (by simpa [PolarizedFamily.id, PolarizedFamily.comp, Category.assoc] using h')

/-- Composition of morphisms of polarized families is associative; on the comparisons of
polarizations this is the associativity coherence of the pullback pseudofunctor. -/
protected theorem assoc {W X Y Z : PolarizedFamily B} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    PolarizedFamily.comp (PolarizedFamily.comp f g) h =
      PolarizedFamily.comp f (PolarizedFamily.comp g h) := by
  refine Hom.ext (by simp [PolarizedFamily.comp]) (by simp [PolarizedFamily.comp]) ?_
  have hobj : (Scheme.Modules.pullback ((f.totalMap ≫ g.totalMap) ≫ h.totalMap)).obj
      Z.lineBundle =
      (Scheme.Modules.pullback (f.totalMap ≫ g.totalMap ≫ h.totalMap)).obj Z.lineBundle := by
    simp
  set a := (Scheme.Modules.pullbackComp f.totalMap (g.totalMap ≫ h.totalMap)).inv.app
    Z.lineBundle with ha
  set b := (Scheme.Modules.pullback f.totalMap).map
    ((Scheme.Modules.pullbackComp g.totalMap h.totalMap).inv.app Z.lineBundle) with hb
  set c := (Scheme.Modules.pullbackComp f.totalMap g.totalMap).hom.app
    ((Scheme.Modules.pullback h.totalMap).obj Z.lineBundle) with hc
  set d := (Scheme.Modules.pullbackComp (f.totalMap ≫ g.totalMap) h.totalMap).hom.app
    Z.lineBundle with hd
  have hcoh := congrArg (fun α => α.app Z.lineBundle)
    (Scheme.Modules.pseudofunctor_associativity f.totalMap g.totalMap h.totalMap)
  have hcoh' : a ≫ b ≫ c ≫ d = eqToHom hobj.symm := by
    simpa [ha, hb, hc, hd, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.assoc] using hcoh
  have hprefix :
      (Scheme.Modules.pullbackComp (f.totalMap ≫ g.totalMap) h.totalMap).inv.app Z.lineBundle ≫
        (Scheme.Modules.pullbackComp f.totalMap g.totalMap).inv.app
          ((Scheme.Modules.pullback h.totalMap).obj Z.lineBundle) =
      eqToHom hobj ≫ a ≫ b := by
    apply (cancel_mono (c ≫ d)).1
    have hleft : ((Scheme.Modules.pullbackComp (f.totalMap ≫ g.totalMap) h.totalMap).inv.app
          Z.lineBundle ≫
        (Scheme.Modules.pullbackComp f.totalMap g.totalMap).inv.app
          ((Scheme.Modules.pullback h.totalMap).obj Z.lineBundle)) ≫ c ≫ d = 𝟙 _ := by
      simp [hc, hd]
    have hright : (eqToHom hobj ≫ a ≫ b) ≫ c ≫ d = 𝟙 _ :=
      (Category.assoc (eqToHom hobj) (a ≫ b) (c ≫ d)).trans
        ((congrArg (fun k => eqToHom hobj ≫ k) (Category.assoc a b (c ≫ d))).trans
          ((congrArg (fun k => eqToHom hobj ≫ k) hcoh').trans (by simp)))
    rw [hleft, hright]
  refine iso_heq_of_hom_eq hobj _ _ ?_
  have := congrArg (fun k => k ≫ (Scheme.Modules.pullback f.totalMap).map
    ((Scheme.Modules.pullback g.totalMap).map h.lineBundleIso.hom) ≫
      (Scheme.Modules.pullback f.totalMap).map g.lineBundleIso.hom ≫ f.lineBundleIso.hom) hprefix
  simpa [PolarizedFamily.comp, ha, hb, Category.assoc] using this

/-- **Stacks 0D1M.** Polarized families, cartesian squares between them and comparisons of
polarizations form a category: the two underlying morphisms compose componentwise and the
comparisons compose through the pullback pseudofunctor. -/
@[stacks 0D1M "category"]
instance instCategory : Category.{u} (PolarizedFamily B) where
  Hom X Y := Hom X Y
  id X := PolarizedFamily.id X
  comp f g := PolarizedFamily.comp f g
  id_comp f := PolarizedFamily.id_comp f
  comp_id f := PolarizedFamily.comp_id f
  assoc f g h := PolarizedFamily.assoc f g h

/-- The base map of an identity morphism is the identity. -/
@[simp]
theorem id_baseMap (X : PolarizedFamily B) : Hom.baseMap (𝟙 X) = 𝟙 X.base := rfl

/-- The map of total spaces of an identity morphism is the identity. -/
@[simp]
theorem id_totalMap (X : PolarizedFamily B) : Hom.totalMap (𝟙 X) = 𝟙 X.total := rfl

/-- The base map of a composite is the composite of the base maps. -/
@[simp]
theorem comp_baseMap {X Y Z : PolarizedFamily B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.baseMap (f ≫ g) = f.baseMap ≫ g.baseMap := rfl

/-- The map of total spaces of a composite is the composite of the maps of total spaces. -/
@[simp]
theorem comp_totalMap {X Y Z : PolarizedFamily B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.totalMap (f ≫ g) = f.totalMap ≫ g.totalMap := rfl

end PolarizedFamily

/-- **Stacks 0D1M.** The forgetful functor taking a polarized family to its base scheme, which is
how the category of polarized families is viewed as a category over the big fppf site. -/
@[stacks 0D1M "projection"]
def polarizedProjection : PolarizedFamily B ⥤ B.Schemes where
  obj X := X.base
  map f := f.baseMap
  map_id := by intro; rfl
  map_comp := by intros; rfl

/-- The projection takes a polarized family to its base scheme. -/
@[simp]
theorem polarizedProjection_obj (X : PolarizedFamily B) :
    (polarizedProjection B).obj X = X.base := rfl

/-- The projection takes a morphism of polarized families to its base map. -/
@[simp]
theorem polarizedProjection_map {X Y : PolarizedFamily B} (f : X ⟶ Y) :
    (polarizedProjection B).map f = f.baseMap := rfl

end AlgebraicGeometry

end
