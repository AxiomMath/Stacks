module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SheafTorsorsEffectiveDescent
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproductSheaf
import all StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SheafTorsorsEffectiveDescent
import all StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves

/-!
# Glueing the sheaves underlying a descent datum of algebraic spaces over varying bases

Let `S` be a scheme contained in a big fppf site and let `p = spacesProjection` be the projection
from algebraic spaces over varying base schemes (Stacks 04U8) to the big fppf site of `S`. A
descent datum for `p` relative to a covering sieve `R` of an object `U` (Stacks 026B,
sieve-indexed) is a family of algebraic spaces `X_f` over the sources `V` of the arrows `f : V ⟶ U`
of `R`, glued by isomorphisms between their chosen pullbacks. This file shows that the underlying
sheaves always glue: there is an fppf sheaf `F` with a morphism `F ⟶ h_U` of which every `X_f` is
the base change along `f`, compatibly with the glueing isomorphisms
(`AlgebraicGeometry.SpacesDescent.nonempty_sheafGlueing`).

This is the first half of the source's proof of condition (3) of Stacks 04UD, and of Stacks 0ADV:
"by Sites, Lemma 04TR there exists a sheaf `X` on `(Sch/U)_{fppf}` recovering the `X_i` and the
`φ_ij`". Whether `F` is an algebraic space is a separate question, answered by Stacks 04S6 under a
finiteness hypothesis, and is not addressed here.

## Main definitions

* `AlgebraicGeometry.SpacesDescent.fiberSheaf`: an algebraic space over `V`, as a sheaf on the
  localized site `C/V`.
* `AlgebraicGeometry.SpacesDescent.pullbackFiberSheafIso`: the sheaf of a chosen pullback is the
  restriction of the sheaf.
* `AlgebraicGeometry.SpacesDescent.sheafDescentData`: the descent datum of sheaves underlying a
  descent datum for `spacesProjection`, in the form `CategoryTheory.Pseudofunctor.DescentData` of
  the pseudofunctor of sheaves on the localized sites.
* `AlgebraicGeometry.SpacesDescent.SheafGlueing`: a glueing of the datum as sheaves.

## Main results

* `AlgebraicGeometry.SpacesDescent.nonempty_sheafGlueing`: every descent datum for
  `spacesProjection` relative to a covering sieve has a glueing as sheaves.

## Implementation notes

The glueing is Stacks 04TR in the universe of the site's morphisms, applied to the tautological
family of the sieve; the big fppf site supplies the covering subfamily indexed in that universe
which it needs. The glued sheaf `H` lives on `C/U`, and the sheaf over `h_U` is
`OverShriek.presheaf H`, whose charts are the morphisms from the objects of the datum. The small
glueing, the covering subfamily and the charts are the private auxiliaries of the proof of
Stacks 04UM condition (3) in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SheafTorsorsEffectiveDescent`,
reached by `import all` rather than restated.

The one non-formal verification is that the glueing morphisms are compatible with base change
(`AlgebraicGeometry.SpacesDescent.sheafDescentHom_pullHom`), which is the base-change axiom of the
datum read on sections through the chosen cartesian lifts.

## References

* [Stacks Project, Tag 04UD](https://stacks.math.columbia.edu/tag/04UD)
* [Stacks Project, Tag 04TR](https://stacks.math.columbia.edu/tag/04TR)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SpacesDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure morphism of an object of the fibre of `spacesProjection` over `V`, read as a
morphism to the presheaf represented by `V`. -/
abbrev fiberHom {V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber V) :
    X.1.left.obj ⟶ yoneda.obj V :=
  X.1.hom ≫ yoneda.map (eqToHom X.2)

/-- An object of the fibre of `spacesProjection` over `V`, as a presheaf over `h_V`. -/
abbrev fiberOver {V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber V) :
    Over (yoneda.obj V) :=
  Over.mk (fiberHom X)

/-- A morphism of the fibre of `spacesProjection` over `V`, as a morphism of presheaves over
`h_V`. -/
def fiberOverHom {V : BigFppfOver B S hS} {X Y : (spacesProjection B S hS).Fiber V}
    (m : X ⟶ Y) : fiberOver X ⟶ fiberOver Y := by
  refine Over.homMk m.1.left.hom ?_
  let : (spacesProjection B S hS).IsHomLift (𝟙 V) m.1 := m.2
  have hm := IsHomLift.fac' (spacesProjection B S hS) (𝟙 V) m.1
  change m.1.right = eqToHom X.2 ≫ (𝟙 V) ≫ eqToHom Y.2.symm at hm
  have hm' : m.1.right = eqToHom X.2 ≫ eqToHom Y.2.symm := by
    simpa only [Category.comp_id, Category.id_comp] using hm
  have hcomma := m.1.w
  change m.1.left.hom ≫ Y.1.hom = X.1.hom ≫ yoneda.map m.1.right at hcomma
  change m.1.left.hom ≫ Y.1.hom ≫ yoneda.map (eqToHom Y.2) =
    X.1.hom ≫ yoneda.map (eqToHom X.2)
  calc
    m.1.left.hom ≫ Y.1.hom ≫ yoneda.map (eqToHom Y.2) =
        X.1.hom ≫ yoneda.map m.1.right ≫ yoneda.map (eqToHom Y.2) :=
          congrArg (fun k => k ≫ yoneda.map (eqToHom Y.2)) hcomma
    _ = X.1.hom ≫ yoneda.map (m.1.right ≫ eqToHom Y.2) := by
          rw [← Functor.map_comp]
    _ = X.1.hom ≫ yoneda.map (eqToHom X.2) := by rw [hm']; simp

/-- The sheaf on the localized site `C/V` attached to an object of the fibre of
`spacesProjection` over `V`: its sections over `T ⟶ V` are the sections of the algebraic space
over `T` lying over `T ⟶ V`. -/
def fiberSheaf {V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber V) :
    Sheaf ((BigFppfOver.topology B S hS).over V) (Type u) :=
  ⟨OverShriek.fiber (𝟙 (yoneda.obj V)) (fiberHom X), by
    let J := BigFppfOver.topology B S hS
    have hX' : Presheaf.IsSheaf (J.over V) ((Over.forget V).op ⋙ X.1.left.obj) :=
      (Over.forget V).op_comp_isSheaf_of_isSheaf (J.over V) J X.1.left.obj
        X.1.left.property.isSheaf
    have hU' : Presheaf.IsSheaf (J.over V) ((Over.forget V).op ⋙ yoneda.obj V) :=
      (Over.forget V).op_comp_isSheaf_of_isSheaf (J.over V) J (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V).isSheaf
    rw [isSheaf_iff_isSheaf_of_type]
    exact OverShriek.isSheaf_fiber (K := J.over V) (𝟙 (yoneda.obj V)) (fiberHom X)
      ((isSheaf_iff_isSheaf_of_type (J.over V) _).1 hX')
      (((isSheaf_iff_isSheaf_of_type (J.over V) _).1 hU').isSeparated)⟩

/-- The morphism of sheaves on `C/V` induced by a morphism of the fibre over `V`. -/
def fiberSheafMap {V : BigFppfOver B S hS} {X Y : (spacesProjection B S hS).Fiber V}
    (m : X ⟶ Y) : fiberSheaf X ⟶ fiberSheaf Y :=
  ⟨OverShriek.fiberMap (𝟙 (yoneda.obj V)) (fiberOverHom m)⟩

/-- The morphism of sheaves of a morphism of the fibre, read on sections. -/
@[simp]
theorem fiberSheafMap_app_val {V : BigFppfOver B S hS} {X Y : (spacesProjection B S hS).Fiber V}
    (m : X ⟶ Y) (T : (Over V)ᵒᵖ) (s : (fiberSheaf X).obj.obj T) :
    ((fiberSheafMap m).hom.app T s).1 = m.1.left.hom.app (op T.unop.left) s.1 := rfl

/-- `fiberSheafMap` preserves composition. -/
@[reassoc]
theorem fiberSheafMap_comp {V : BigFppfOver B S hS} {X Y Z : (spacesProjection B S hS).Fiber V}
    (m : X ⟶ Y) (m' : Y ⟶ Z) : fiberSheafMap (m ≫ m') = fiberSheafMap m ≫ fiberSheafMap m' :=
  rfl

/-- `fiberSheafMap` preserves identities. -/
theorem fiberSheafMap_id {V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber V) :
    fiberSheafMap (𝟙 X) = 𝟙 _ :=
  rfl

/-- A strongly cartesian morphism of `spacesProjection` over `f : V ⟶ U` gives a cartesian square
of presheaves over `yoneda.map f`, with the structure morphisms normalized to `h_V` and `h_U`. -/
theorem isPullback_of_isStronglyCartesian {U V : BigFppfOver B S hS} (f : V ⟶ U)
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (m : A ⟶ C) [(spacesProjection B S hS).IsStronglyCartesian f m]
    (hA : A.right = V) (hC : C.right = U) :
    IsPullback m.left.hom (A.hom ≫ yoneda.map (eqToHom hA))
      (C.hom ≫ yoneda.map (eqToHom hC)) (yoneda.map f) := by
  subst hA hC
  have hg : m.right = f := by
    simpa using IsHomLift.fac' (spacesProjection B S hS) f m
  subst hg
  simpa using (isPullback_hom_of_isStronglyCartesian B S hS m inferInstance).flip

/-- The chosen pullback of an object of the fibre of `spacesProjection` sits in a cartesian square
of presheaves over the representables. -/
theorem isPullback_pullbackMap [(spacesProjection B S hS).IsFibered] {U V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U) :
    IsPullback (Functor.IsPreFibered.pullbackMap X.2 f).left.hom
      (fiberHom (Functor.pullbackFiber (spacesProjection B S hS) X f)) (fiberHom X)
      (yoneda.map f) := by
  have : (spacesProjection B S hS).IsCartesian f (Functor.IsPreFibered.pullbackMap X.2 f) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian X.2 f
  have : (spacesProjection B S hS).IsStronglyCartesian f
      (Functor.IsPreFibered.pullbackMap X.2 f) :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian _ f _
  exact isPullback_of_isStronglyCartesian f _ _ X.2

/-- The sheaf on `C/V` of the chosen pullback of `X` along `f : V ⟶ U` is the restriction along
`f` of the sheaf on `C/U` of `X`. -/
@[no_expose]
def pullbackFiberSheafIso [(spacesProjection B S hS).IsFibered] {U V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U) :
    fiberSheaf (Functor.pullbackFiber (spacesProjection B S hS) X f) ≅
      ((BigFppfOver.topology B S hS).overMapPullback (Type u) f).obj (fiberSheaf X) :=
  let e := Space.SheafTorsors.fiberIsoOfPullback f (fiberOver X)
    (fiberOver (Functor.pullbackFiber (spacesProjection B S hS) X f))
    (Functor.IsPreFibered.pullbackMap X.2 f).left.hom (isPullback_pullbackMap X f)
  ⟨⟨e.hom⟩, ⟨e.inv⟩, Sheaf.hom_ext e.hom_inv_id, Sheaf.hom_ext e.inv_hom_id⟩

/-- `pullbackFiberSheafIso` read on sections. -/
@[simp]
theorem pullbackFiberSheafIso_hom_app_val [(spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U)
    (T : (Over V)ᵒᵖ)
    (s : (fiberSheaf (Functor.pullbackFiber (spacesProjection B S hS) X f)).obj.obj T) :
    ((pullbackFiberSheafIso X f).hom.hom.app T s).1 =
      (Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app (op T.unop.left) s.1 :=
  by exact rfl

/-- The inverse of `pullbackFiberSheafIso`, followed by the chosen pullback map, is the identity on
sections. -/
theorem pullbackMap_pullbackFiberSheafIso_inv_app_val [(spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U)
    (T : (Over V)ᵒᵖ)
    (s : (((BigFppfOver.topology B S hS).overMapPullback (Type u) f).obj
      (fiberSheaf X)).obj.obj T) :
    (Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app (op T.unop.left)
      ((pullbackFiberSheafIso X f).inv.hom.app T s).1 = s.1 :=
  congrArg (fun φ => (φ.hom.app T s).1) (pullbackFiberSheafIso X f).inv_hom_id

/-- An element of the restriction along `f` of the sheaf of `X` is the image of exactly one element
of the sheaf of the chosen pullback: the one lying over the same morphism and mapping to it. -/
theorem pullbackFiberSheafIso_inv_app_val_eq [(spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U)
    (T : (Over V)ᵒᵖ)
    (s : (((BigFppfOver.topology B S hS).overMapPullback (Type u) f).obj
      (fiberSheaf X)).obj.obj T)
    (v : (Functor.pullbackFiber (spacesProjection B S hS) X f).1.left.obj.obj
      (op T.unop.left))
    (hv : (fiberHom (Functor.pullbackFiber (spacesProjection B S hS) X f)).app
      (op T.unop.left) v = T.unop.hom)
    (hvs : (Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app (op T.unop.left) v = s.1) :
    ((pullbackFiberSheafIso X f).inv.hom.app T s).1 = v := by
  have h : (pullbackFiberSheafIso X f).hom.hom.app T ⟨v, hv⟩ = s := Subtype.ext hvs
  have h' := congrArg (fun φ => φ.hom.app T ⟨v, hv⟩) (pullbackFiberSheafIso X f).hom_inv_id
  change (pullbackFiberSheafIso X f).inv.hom.app T
    ((pullbackFiberSheafIso X f).hom.hom.app T ⟨v, hv⟩) = ⟨v, hv⟩ at h'
  rw [h] at h'
  exact congrArg Subtype.val h'

/-- Composition in the comma category of algebraic spaces over varying bases, read on sections. -/
theorem comp_left_app
    {A C E : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (a : A ⟶ C) (b : C ⟶ E) (T : (BigFppfOver B S hS)ᵒᵖ) (x : A.left.obj.obj T) :
    (a ≫ b).left.hom.app T x = b.left.hom.app T (a.left.hom.app T x) :=
  rfl

/-- A morphism of the fibre of `spacesProjection` over `V` preserves the structure morphisms to
`h_V`, read on sections. -/
theorem fiberHom_app_map {V : BigFppfOver B S hS} {X Y : (spacesProjection B S hS).Fiber V}
    (m : X ⟶ Y) (T : (BigFppfOver B S hS)ᵒᵖ) (x : X.1.left.obj.obj T) :
    (fiberHom Y).app T (m.1.left.hom.app T x) = (fiberHom X).app T x :=
  congrArg (fun k => k.app T x) (Over.w (fiberOverHom m))

/-- The chosen pullback map is compatible with the structure morphisms, read on sections. -/
theorem fiberHom_app_pullbackMap [(spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U)
    (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (Functor.pullbackFiber (spacesProjection B S hS) X f).1.left.obj.obj T) :
    (fiberHom X).app T ((Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app T x) =
      (fiberHom (Functor.pullbackFiber (spacesProjection B S hS) X f)).app T x ≫ f :=
  congrArg (fun k => k.app T x) (isPullback_pullbackMap X f).w

open GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj in
/-- Restricting a section of the sheaf of an object of the fibre along an identity of objects of
the site does not change the underlying section of the algebraic space. -/
private theorem rest_fiberSheaf_val {V : BigFppfOver B S hS} (X : (spacesProjection B S hS).Fiber V)
    {W : BigFppfOver B S hS} (g ug : W ⟶ V) (e : 𝟙 W ≫ g = ug)
    (x : (fiberSheaf X).obj.obj (op (Over.mk g))) :
    (ConcreteCategory.hom (rest (fiberSheaf X) (𝟙 W) g ug e) x).1 = x.1 := by
  change X.1.left.obj.map (𝟙 W).op x.1 = x.1
  simp

/-- A morphism of the comma category of algebraic spaces over varying bases, lying over
`f : V ⟶ U`, whose square of presheaves over `yoneda.map f` is cartesian is strongly cartesian:
the converse of `AlgebraicGeometry.SpacesDescent.isPullback_of_isStronglyCartesian`, both being
Stacks 04U9 read on the normalized structure morphisms. -/
theorem isStronglyCartesian_of_isPullback {U V : BigFppfOver B S hS} (f : V ⟶ U)
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (m : A ⟶ C) (hA : A.right = V) (hC : C.right = U)
    (hm : m.right = eqToHom hA ≫ f ≫ eqToHom hC.symm)
    {cA : A.left.obj ⟶ yoneda.obj V} {cC : C.left.obj ⟶ yoneda.obj U}
    (hcA : A.hom ≫ yoneda.map (eqToHom hA) = cA) (hcC : C.hom ≫ yoneda.map (eqToHom hC) = cC)
    (h : IsPullback m.left.hom cA cC (yoneda.map f)) :
    (spacesProjection B S hS).IsStronglyCartesian f m := by
  subst hcA hcC hA hC
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm
  subst hm
  rw [spacesProjection_isStronglyCartesian_iff]
  have h' : IsPullback A.hom m.left.hom (yoneda.map m.right) C.hom := by
    simpa using h.flip
  have e : pullback.lift A.hom m.left.hom m.w.symm = h'.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [h'.isoPullback_hom_fst]
      exact pullback.lift_fst _ _ _
    · rw [h'.isoPullback_hom_snd]
      exact pullback.lift_snd _ _ _
  have : IsIso (pullback.lift A.hom m.left.hom m.w.symm) := by
    rw [e]
    infer_instance
  have : IsIso ((ObjectProperty.ι _).map (ObjectProperty.homMk
      (pullback.lift A.hom m.left.hom m.w.symm) :
        A.left ⟶ AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap m.right)
          (ObjectProperty.homMk C.hom))) :=
    inferInstanceAs (IsIso (pullback.lift A.hom m.left.hom m.w.symm))
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

section DescentData

variable [(spacesProjection B S hS).IsFibered] {U : BigFppfOver B S hS} {R : Sieve U}
  (D : (spacesProjection B S hS).SieveDescentDatum R)

/-- The index type of the tautological family of a sieve: its arrows. -/
abbrev Arrows (R : Sieve U) := Σ V : BigFppfOver B S hS, {f : V ⟶ U // R.arrows f}

/-- The gluing morphisms of the descent datum of sheaves underlying a descent datum of algebraic
spaces over varying bases. -/
def sheafDescentHom {Y : BigFppfOver B S hS} {i₁ i₂ : Arrows R} (f₁ : Y ⟶ i₁.1) (f₂ : Y ⟶ i₂.1)
    (h : f₁ ≫ i₁.2.1 = f₂ ≫ i₂.2.1) :
    ((BigFppfOver.topology B S hS).overMapPullback (Type u) f₁).obj
        (fiberSheaf (D.obj i₁.2.1 i₁.2.2)) ⟶
      ((BigFppfOver.topology B S hS).overMapPullback (Type u) f₂).obj
        (fiberSheaf (D.obj i₂.2.1 i₂.2.2)) :=
  (pullbackFiberSheafIso _ f₁).inv ≫ fiberSheafMap (D.iso i₁.2.2 i₂.2.2 f₁ f₂ h).hom ≫
    (pullbackFiberSheafIso _ f₂).hom

/-- The glueing morphisms read on sections: transport by the glueing isomorphism of the datum,
between the chosen pullbacks. -/
theorem sheafDescentHom_app_val {Y : BigFppfOver B S hS} {i₁ i₂ : Arrows R} (f₁ : Y ⟶ i₁.1)
    (f₂ : Y ⟶ i₂.1) (h : f₁ ≫ i₁.2.1 = f₂ ≫ i₂.2.1) (T : (Over Y)ᵒᵖ)
    (s : (((BigFppfOver.topology B S hS).overMapPullback (Type u) f₁).obj
      (fiberSheaf (D.obj i₁.2.1 i₁.2.2))).obj.obj T) :
    ((sheafDescentHom D f₁ f₂ h).hom.app T s).1 =
      (Functor.IsPreFibered.pullbackMap (D.obj i₂.2.1 i₂.2.2).2 f₂).left.hom.app
        (op T.unop.left)
        ((D.iso i₁.2.2 i₂.2.2 f₁ f₂ h).hom.1.left.hom.app (op T.unop.left)
          ((pullbackFiberSheafIso _ f₁).inv.hom.app T s).1) :=
  by exact rfl

/-- The glueing morphism of an arrow with itself along one morphism is the identity. -/
theorem sheafDescentHom_self {Y : BigFppfOver B S hS} {i : Arrows R} (f₁ : Y ⟶ i.1)
    (h : f₁ ≫ i.2.1 = f₁ ≫ i.2.1) : sheafDescentHom D f₁ f₁ h = 𝟙 _ := by
  rw [sheafDescentHom, D.iso_self, fiberSheafMap_id, Category.id_comp, Iso.inv_hom_id]

/-- The cocycle condition for the glueing morphisms. -/
theorem sheafDescentHom_comp {Y : BigFppfOver B S hS} {i₁ i₂ i₃ : Arrows R} (f₁ : Y ⟶ i₁.1)
    (f₂ : Y ⟶ i₂.1) (f₃ : Y ⟶ i₃.1) (h₁₂ : f₁ ≫ i₁.2.1 = f₂ ≫ i₂.2.1)
    (h₂₃ : f₂ ≫ i₂.2.1 = f₃ ≫ i₃.2.1) (h₁₃ : f₁ ≫ i₁.2.1 = f₃ ≫ i₃.2.1) :
    sheafDescentHom D f₁ f₂ h₁₂ ≫ sheafDescentHom D f₂ f₃ h₂₃ = sheafDescentHom D f₁ f₃ h₁₃ := by
  simp only [sheafDescentHom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← fiberSheafMap_comp_assoc, D.cocycle i₁.2.2 i₂.2.2 i₃.2.2 f₁ f₂ f₃ h₁₂ h₂₃ h₁₃]

omit [(spacesProjection B S hS).IsFibered] in
/-- A morphism of the fibre read on sections: the underlying morphism of a composite. -/
theorem fiber_comp_app {V : BigFppfOver B S hS} {X Y Z : (spacesProjection B S hS).Fiber V}
    (a : X ⟶ Y) (b : Y ⟶ Z) (T : (BigFppfOver B S hS)ᵒᵖ) (x : X.1.left.obj.obj T) :
    (a ≫ b).1.left.hom.app T x = b.1.left.hom.app T (a.1.left.hom.app T x) :=
  rfl

omit [(spacesProjection B S hS).IsFibered] in
/-- An isomorphism of the fibre read on sections: `hom` after `inv` is the identity. -/
theorem fiber_inv_hom_app {V : BigFppfOver B S hS} {X Y : (spacesProjection B S hS).Fiber V}
    (e : X ≅ Y) (T : (BigFppfOver B S hS)ᵒᵖ) (y : Y.1.left.obj.obj T) :
    e.hom.1.left.hom.app T (e.inv.1.left.hom.app T y) = y := by
  rw [← fiber_comp_app, e.inv_hom_id]
  rfl

/-- The section-level heart of the compatibility of the glueing morphisms with base change. -/
theorem pullbackMap_app_iso_base_change {Y Y' Z : BigFppfOver B S hS}
    {V₁ V₂ : BigFppfOver B S hS}
    (Xi : (spacesProjection B S hS).Fiber V₁) (Xj : (spacesProjection B S hS).Fiber V₂)
    (f₁ : Y ⟶ V₁) (f₂ : Y ⟶ V₂) (g : Y' ⟶ Y)
    (α : Functor.pullbackFiber (spacesProjection B S hS) Xi f₁ ≅
      Functor.pullbackFiber (spacesProjection B S hS) Xj f₂)
    (α' : Functor.pullbackFiber (spacesProjection B S hS) Xi (g ≫ f₁) ⟶
      Functor.pullbackFiber (spacesProjection B S hS) Xj (g ≫ f₂))
    (hα' : α' = (Functor.pullbackFiberCompIso Xi f₁ g).inv ≫
      (Functor.pullbackFiberIso α g).hom ≫ (Functor.pullbackFiberCompIso Xj f₂ g).hom)
    (z : Z ⟶ Y')
    (x : (((BigFppfOver.topology B S hS).overMapPullback (Type u) f₁).obj
      (fiberSheaf Xi)).obj.obj (op (Over.mk (z ≫ g))))
    (s : (((BigFppfOver.topology B S hS).overMapPullback (Type u) (g ≫ f₁)).obj
      (fiberSheaf Xi)).obj.obj (op (Over.mk z)))
    (hxs : x.1 = s.1) :
    (Functor.IsPreFibered.pullbackMap Xj.2 f₂).left.hom.app (op Z)
        (α.hom.1.left.hom.app (op Z) ((pullbackFiberSheafIso Xi f₁).inv.hom.app _ x).1) =
      (Functor.IsPreFibered.pullbackMap Xj.2 (g ≫ f₂)).left.hom.app (op Z)
        (α'.1.left.hom.app (op Z) ((pullbackFiberSheafIso Xi (g ≫ f₁)).inv.hom.app _ s).1) := by
  set ci := Functor.pullbackFiberCompIso Xi f₁ g
  set cj := Functor.pullbackFiberCompIso Xj f₂ g
  set u := ((pullbackFiberSheafIso Xi (g ≫ f₁)).inv.hom.app _ s).1 with hu
  have hu1 : (Functor.IsPreFibered.pullbackMap Xi.2 (g ≫ f₁)).left.hom.app (op Z) u = s.1 :=
    pullbackMap_pullbackFiberSheafIso_inv_app_val Xi (g ≫ f₁) _ s
  have hu2 : (fiberHom (Functor.pullbackFiber (spacesProjection B S hS) Xi (g ≫ f₁))).app
      (op Z) u = z :=
    ((pullbackFiberSheafIso Xi (g ≫ f₁)).inv.hom.app _ s).2
  set w := ci.inv.1.left.hom.app (op Z) u with hw
  set v := (Functor.IsPreFibered.pullbackMap
    (Functor.pullbackFiber (spacesProjection B S hS) Xi f₁).2 g).left.hom.app (op Z) w with hv
  have hci := Functor.pullbackFiberCompIso_hom_fac Xi f₁ g
  have hcj := Functor.pullbackFiberCompIso_hom_fac Xj f₂ g
  have hxv : ((pullbackFiberSheafIso Xi f₁).inv.hom.app _ x).1 = v := by
    refine pullbackFiberSheafIso_inv_app_val_eq Xi f₁ _ x v ?_ ?_
    · exact (fiberHom_app_pullbackMap _ g (op Z) w).trans
        (congrArg (· ≫ g) ((fiberHom_app_map ci.inv (op Z) u).trans hu2))
    · exact (((congrArg (fun k => k.left.hom.app (op Z) w) hci).symm.trans
        (congrArg (fun y => (Functor.IsPreFibered.pullbackMap Xi.2 (g ≫ f₁)).left.hom.app
          (op Z) y) (fiber_inv_hom_app ci (op Z) u))).trans hu1).trans hxs.symm
  set πj := fun y => (Functor.IsPreFibered.pullbackMap Xj.2 f₂).left.hom.app (op Z) y
  set πj' := fun y => (Functor.IsPreFibered.pullbackMap Xj.2 (g ≫ f₂)).left.hom.app (op Z) y
  set pα := Functor.pullbackFiberHom α.hom g
  calc πj (α.hom.1.left.hom.app (op Z) ((pullbackFiberSheafIso Xi f₁).inv.hom.app _ x).1)
      = πj (α.hom.1.left.hom.app (op Z) v) :=
        congrArg (fun y => πj (α.hom.1.left.hom.app (op Z) y)) hxv
    _ = πj ((Functor.IsPreFibered.pullbackMap
          (Functor.pullbackFiber (spacesProjection B S hS) Xj f₂).2 g).left.hom.app (op Z)
          (pα.1.left.hom.app (op Z) w)) :=
        congrArg πj (congrArg (fun k => k.left.hom.app (op Z) w)
          (Functor.pullbackFiberHom_fac α.hom g)).symm
    _ = πj' (cj.hom.1.left.hom.app (op Z) (pα.1.left.hom.app (op Z) w)) :=
        (congrArg (fun k => k.left.hom.app (op Z) (pα.1.left.hom.app (op Z) w)) hcj).symm
    _ = πj' (α'.1.left.hom.app (op Z) u) :=
        congrArg πj' (congrArg (fun k => k.1.left.hom.app (op Z) u) hα').symm

open GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj in
/-- The glueing morphisms are compatible with base change. -/
theorem sheafDescentHom_pullHom {Y Y' : BigFppfOver B S hS} {i₁ i₂ : Arrows R} (f₁ : Y ⟶ i₁.1)
    (f₂ : Y ⟶ i₂.1) (h : f₁ ≫ i₁.2.1 = f₂ ≫ i₂.2.1) (g : Y' ⟶ Y)
    (h' : (g ≫ f₁) ≫ i₁.2.1 = (g ≫ f₂) ≫ i₂.2.1) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := (BigFppfOver.topology B S hS).pseudofunctorOver (Type u))
      (M₁ := fiberSheaf (D.obj i₁.2.1 i₁.2.2)) (M₂ := fiberSheaf (D.obj i₂.2.1 i₂.2.2))
      (sheafDescentHom D f₁ f₂ h) g (g ≫ f₁) (g ≫ f₂) rfl rfl =
      sheafDescentHom D (g ≫ f₁) (g ≫ f₂) h' := by
  apply Sheaf.hom_ext
  ext T s
  obtain ⟨T⟩ := T
  obtain ⟨Z, z, rfl⟩ := Over.mk_surjective T
  refine (congrArg (fun φ => φ s) (appS_pullHom (fiberSheaf (D.obj i₁.2.1 i₁.2.2))
    (fiberSheaf (D.obj i₂.2.1 i₂.2.2)) (sheafDescentHom D f₁ f₂ h) g (g ≫ f₁) (g ≫ f₂)
    rfl rfl z)).trans ?_
  apply Subtype.ext
  refine (rest_fiberSheaf_val (D.obj i₂.2.1 i₂.2.2) ((z ≫ g) ≫ f₂) (z ≫ g ≫ f₂)
    (by simp) _).trans ?_
  refine Eq.trans ?_ (sheafDescentHom_app_val D (g ≫ f₁) (g ≫ f₂) h' _ s).symm
  refine (sheafDescentHom_app_val D f₁ f₂ h _ _).trans ?_
  exact pullbackMap_app_iso_base_change _ _ f₁ f₂ g _ _
    (D.iso_pullback i₁.2.2 i₂.2.2 f₁ f₂ h g).symm z _ s
    (rest_fiberSheaf_val (D.obj i₁.2.1 i₁.2.2) _ _ _ s)

/-- **The descent datum of sheaves underlying a descent datum of algebraic spaces over varying
bases**, relative to the tautological family of the sieve. -/
def sheafDescentData :
    ((BigFppfOver.topology B S hS).pseudofunctorOver (Type u)).DescentData
      (fun i : Arrows R => i.2.1) where
  obj i := fiberSheaf (D.obj i.2.1 i.2.2)
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := sheafDescentHom D f₁ f₂ (hf₁.trans hf₂.symm)
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    subst hgf₁ hgf₂ hq
    exact sheafDescentHom_pullHom D f₁ f₂ _ g _
  hom_self _ _ _ g _ := sheafDescentHom_self D g _
  hom_comp _ _ _ _ _ f₁ f₂ f₃ _ _ _ := sheafDescentHom_comp D f₁ f₂ f₃ _ _ _

/-- **A glueing of a descent datum of algebraic spaces over varying bases, as sheaves.** A sheaf
`obj` with a morphism `π` to the presheaf represented by `U`, and for every arrow `f : V ⟶ U` of
the sieve a morphism from the object of the datum attached to `f`, exhibiting it as the base change
of `obj` along `f` and compatible with the glueing isomorphisms of the datum. -/
structure SheafGlueing where
  /-- The glued sheaf. -/
  obj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- It is a sheaf. -/
  isSheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) obj
  /-- Its structure morphism to `h_U`. -/
  π : obj ⟶ yoneda.obj U
  /-- The morphisms from the objects of the datum. -/
  ι : ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1.left.obj ⟶ obj
  /-- They exhibit the objects of the datum as the base changes of `obj`. -/
  isPullback : ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ U) (hf : R.arrows f),
    IsPullback (ι f hf) (fiberHom (D.obj f hf)) π (yoneda.map f)
  /-- They are compatible with the glueing isomorphisms of the datum. -/
  comp_ι : ∀ ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R.arrows f) ⦃g : W ⟶ U⦄
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
    (D.iso hf hg ε ε' heq).hom.1.left.hom ≫
        (Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε').left.hom ≫ ι g hg =
      (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε).left.hom ≫ ι f hf

open Space.SheafTorsors in
/-- **Every descent datum of algebraic spaces over varying bases, relative to a covering sieve,
glues as a sheaf.** The sheaves on the localized sites underlying the objects of the datum glue,
by Stacks 04TR in the universe of the site's morphisms, to a sheaf `H` on `C/U`; the glued sheaf
over `h_U` is the presheaf `OverShriek.presheaf H`, and its charts are the morphisms from the
objects of the datum. -/
theorem nonempty_sheafGlueing (hR : R ∈ BigFppfOver.topology B S hS U) :
    Nonempty (SheafGlueing D) := by
  classical
  obtain ⟨A, a, ha⟩ := bigFppfOver_small_subcover
    (fun i : Arrows R => i.2.1) (Functor.mem_of_generate_ofArrows_arrows _ hR)
  obtain ⟨H, ⟨e⟩⟩ := small_sheaf_descent
    (BigFppfOver.topology B S hS) (fun i : Arrows R => i.2.1)
    (Functor.mem_of_generate_ofArrows_arrows _ hR) A a ha
    (sheafDescentData D)
  let ei : ∀ i : Arrows R, OverShriek.fiber (𝟙 (yoneda.obj i.1)) (fiberHom (D.obj i.2.1 i.2.2)) ≅
      (Over.map i.2.1).op ⋙ H.obj := fun i =>
    ((sheafToPresheaf _ _).mapIso (descentComponentIso _ H
      (sheafDescentData D) e i)).symm
  refine ⟨{ obj := OverShriek.presheaf H.obj
            isSheaf := (isSheaf_iff_isSheaf_of_type _ _).2 (OverShriek.isSheaf_presheaf _ H.obj
              ((isSheaf_iff_isSheaf_of_type _ _).1 (isAlgebraicSpace_yoneda B S hS U).isSheaf)
              ((isSheaf_iff_isSheaf_of_type _ _).1 H.property))
            π := OverShriek.presheafToYoneda H.obj
            ι := fun V f hf => sheafChart f H.obj (fiberOver (D.obj f hf)) (ei ⟨V, f, hf⟩)
            isPullback := fun V f hf => sheafChart_isPullback _ _ _ _
            comp_ι := ?_ }⟩
  intro V W Z f hf g hg ε ε' heq
  ext ⟨T⟩ y
  set z : T ⟶ Z := (fiberHom (Functor.pullbackFiber (spacesProjection B S hS)
    (D.obj f hf) ε)).app (op T) y
  set xv := (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε).left.hom.app (op T) y
  have hxv : (fiberHom (D.obj f hf)).app (op T) xv = z ≫ ε :=
    fiberHom_app_pullbackMap (D.obj f hf) ε (op T) y
  set yv := (Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε').left.hom.app (op T)
    ((D.iso hf hg ε ε' heq).hom.1.left.hom.app (op T) y)
  have hyv : (fiberHom (D.obj g hg)).app (op T) yv = z ≫ ε' :=
    (fiberHom_app_pullbackMap (D.obj g hg) ε' (op T) _).trans
      (congrArg (· ≫ ε') (fiberHom_app_map (D.iso hf hg ε ε' heq).hom (op T) y))
  let x : (fiberSheaf (D.obj f hf)).obj.obj (op (Over.mk (z ≫ ε))) := ⟨xv, hxv⟩
  have hD : (sheafDescentHom D (i₁ := ⟨V, f, hf⟩) (i₂ := ⟨W, g, hg⟩) ε ε' heq).hom.app
      (op (Over.mk z)) x = ⟨yv, hyv⟩ :=
    Subtype.ext ((sheafDescentHom_app_val D (i₁ := ⟨V, f, hf⟩) (i₂ := ⟨W, g, hg⟩) ε ε' heq
      (op (Over.mk z)) x).trans (congrArg (fun w =>
        (Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε').left.hom.app (op T)
          ((D.iso hf hg ε ε' heq).hom.1.left.hom.app (op T) w))
        (pullbackFiberSheafIso_inv_app_val_eq (D.obj f hf) ε (op (Over.mk z)) x y rfl rfl)))
  have key := sigma_descent_inv (BigFppfOver.topology B S hS) H
    (sheafDescentData D) e (ε ≫ f) (i := ⟨V, f, hf⟩) (j := ⟨W, g, hg⟩) ε ε' rfl heq.symm z x
  change (sheafChart g H.obj (fiberOver (D.obj g hg)) (ei ⟨W, g, hg⟩)).app (op T) yv =
    (sheafChart f H.obj (fiberOver (D.obj f hf)) (ei ⟨V, f, hf⟩)).app (op T) xv
  refine (sheafChart_apply g H.obj (fiberOver (D.obj g hg)) (ei ⟨W, g, hg⟩)
    (Over.mk (z ≫ ε')) ⟨yv, hyv⟩).trans (Eq.trans ?_ (sheafChart_apply f H.obj
      (fiberOver (D.obj f hf)) (ei ⟨V, f, hf⟩) (Over.mk (z ≫ ε)) x).symm)
  refine Eq.trans ?_ key
  exact congrArg (fun w => (⟨(z ≫ ε') ≫ g, (e.inv.hom ⟨W, g, hg⟩).hom.app
    (op (Over.mk (z ≫ ε'))) w⟩ : (OverShriek.presheaf H.obj).obj (op T))) hD.symm

/-- **A glueing as sheaves whose glued sheaf is an algebraic space makes the datum effective.**
The glued sheaf with its structure morphism to `h_U` is an object of the fibre of
`spacesProjection` over `U`, and the charts of the glueing are strongly cartesian morphisms to it
by Stacks 04U9, because they exhibit the objects of the datum as base changes. -/
theorem SheafGlueing.isEffective (G : SheafGlueing D) (halg : IsAlgebraicSpace B S hS G.obj) :
    D.IsEffective := by
  let x : (spacesProjection B S hS).Fiber U := ⟨⟨⟨G.obj, halg⟩, U, G.π⟩, rfl⟩
  let ζ : ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ x.1 :=
    fun V f hf =>
      { left := ObjectProperty.homMk (G.ι f hf)
        right := eqToHom (D.obj f hf).2 ≫ f
        w := by
          change G.ι f hf ≫ G.π = (D.obj f hf).1.hom ≫ yoneda.map (eqToHom (D.obj f hf).2 ≫ f)
          simpa [Functor.map_comp] using (G.isPullback f hf).w }
  have hζ : ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ U) (hf : R.arrows f),
      (spacesProjection B S hS).IsStronglyCartesian f (ζ f hf) := fun V f hf =>
    isStronglyCartesian_of_isPullback f (ζ f hf) (D.obj f hf).2 rfl
      (by rw [eqToHom_refl, Category.comp_id]) rfl
      (by exact (congrArg (fun k => G.π ≫ k) (yoneda.map_id U)).trans (Category.comp_id _))
      (G.isPullback f hf)
  refine ⟨x, ζ, fun V f hf => ?_, ?_⟩
  · have := hζ f hf
    infer_instance
  · intro V W Z f hf g hg ε ε' heq
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      exact G.comp_ι hf hg ε ε' heq
    · have hl : ∀ {V : BigFppfOver B S hS} {f : V ⟶ U} (hf : R.arrows f) (ε : Z ⟶ V),
          (spacesProjection B S hS).IsHomLift (ε ≫ f)
            (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫ ζ f hf) :=
        fun hf ε => @IsHomLift.comp _ _ _ _ (spacesProjection B S hS) _ _ _ _ _ _ ε _ _ _
          (Functor.IsPreFibered.pullbackMap.IsCartesian (D.obj _ hf).2 ε).toIsHomLift
          (hζ _ hf).toIsHomLift
      have : (spacesProjection B S hS).IsHomLift (𝟙 Z)
          (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) :=
        (D.iso hf hg ε ε' heq).hom.2
      have h₁ : (spacesProjection B S hS).IsHomLift (ε ≫ f)
          (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
            Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ ζ g hg) := by
        rw [heq, ← Category.id_comp (ε' ≫ g)]
        exact @IsHomLift.comp _ _ _ _ (spacesProjection B S hS) _ _ _ _ _ _ (𝟙 Z) (ε' ≫ g) _ _
          (D.iso hf hg ε ε' heq).hom.2 (hl hg ε')
      have := hl hf ε
      exact (IsHomLift.fac' (spacesProjection B S hS) (ε ≫ f)
        (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
          Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ ζ g hg)).trans
        (IsHomLift.fac' (spacesProjection B S hS) (ε ≫ f)
          (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫ ζ f hf)).symm

end DescentData

end AlgebraicGeometry.SpacesDescent

end
