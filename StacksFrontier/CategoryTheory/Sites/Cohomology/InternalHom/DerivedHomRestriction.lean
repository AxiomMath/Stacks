module

public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Localization.Prod
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Derived internal Hom commutes with restriction to a slice site

Let `(C, O)` be a ringed site and `U` an object of `C`. **Stacks 08JB** asserts that for objects
`K`, `L` of `D(O)`

```
RSheafHom(K|_U, L|_U) = RSheafHom(K, L)|_U,
```

the restriction `(-)|_U` being the functor induced on derived categories by restriction of sheaves
of modules to the slice site `C/U`. This file proves it, as an isomorphism natural in both
variables, and pins the isomorphism down on representatives: on the class of a complex `A` and of a
K-injective complex `B` it is the class of the map of internal Hom complexes

```
SheafHom(A, B)|_U ⟶ SheafHom(A|_U, B|_U)
```

whose every local homogeneous component is the canonical restriction isomorphism of Stacks 0E8H.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsInternalHomRestrictionMap`: the property of a map of internal
  Hom complexes of being, on every local homogeneous component, the canonical restriction of
  Stacks 0E8H.
* `AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso`: that map, which is in fact an
  isomorphism of complexes.
* `AlgebraicGeometry.RingedSite.DerivedHomRestriction`: the comparison on the derived category,
  its naturality in both variables, and its characterization on representatives.
* `AlgebraicGeometry.RingedSite.derivedHomRestriction`: the canonical such comparison.

## Main results

* `AlgebraicGeometry.RingedSite.derivedHom_restriction_exists`: Stacks 08JB, the comparison exists.
* `AlgebraicGeometry.RingedSite.DerivedHomRestriction.complexMap_apply`: the restriction formula
  for local homogeneous cochains along the iterated slice.
* `AlgebraicGeometry.RingedSite.derivedHomRestriction_complexMap_isRestriction`: the chain-level
  comparison is restriction of internal Hom.
* `AlgebraicGeometry.RingedSite.derivedHomRestriction_model`: the derived comparison is the class
  of that chain-level comparison.

## Implementation notes

Restriction of modules to a slice site is exact, so the induced functor on derived categories
takes the class of a complex to the class of its degreewise restriction; that identification is
`CategoryTheory.Functor.mapDerivedCategoryFactors` and is used here instead of inverting the unit
of a right-derived functor. At a K-injective target the derived internal Hom is the class of the
ordinary internal Hom complex (`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`), and the
restricted target stays K-injective by Stacks 08FI, so both sides are the class of a complex and
the comparison is the class of `sheafHomRestrictionComplexIso`.

To extend from K-injective targets to all of `D(O)` the comparison is descended through the
localization in two variables at once: `extendIsoFromResolution` turns a family of
isomorphisms, defined on the classes of pairs whose target is K-injective and natural for
morphisms of such pairs, into an isomorphism of bifunctors, using the functorial K-injective
resolution of Stacks 079P and the full faithfulness of whiskering by a localization functor.

The statement is given as a structure asserted to be nonempty, rather than as a bare
isomorphism, because the two naturality squares and the model identification are what make the
comparison canonical; `derivedHomRestriction` is the chosen one.

Sheaves of modules on the slice site are indexed by `ringSheaf (X.over U).O` here and by
`(ringSheaf X.O).over U` in `AlgebraicGeometry.RingedSite.restrictComplex`; the sections of a
restricted complex are read both as a module and, through `sectionComplex`, as an abelian group.
Each of those pairs is the same object, but only after `Stacks.SheafOfModules.Tensor.ringSheaf` is
commuted past restriction along `Over.forget U`, respectively after the pushforward of presheaves
of modules and its restriction of scalars are unfolded. Both identifications are therefore
invisible at the transparency a rewrite uses, which makes every goal below ill-typed there and
every `rw` fail; the functors involved are made `implicit_reducible` locally to restore them.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  CochainComplex.HomComplex
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- The chain-level restriction map is induced, in every degree and on every
local homogeneous component, by restriction of the internal Hom of modules. -/
def IsInternalHomRestrictionMap
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ)
    (f : restrictComplex X (sheafHomComplex X A B).obj U ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).obj) : Prop :=
  ∀ (V : (Over U)ᵒᵖ) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op V.unop.left)),
    (((AddCommGrpCat.Hom.hom
      (((sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).sectionsIso V.unop).hom.f n)
      ((f.f n).val.app V s)).v p q hpq).val) =
    ((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).hom.app V).hom
      (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X A B).sectionsIso V.unop.left).hom.f n) s).v
          p q hpq).val)

section


private theorem restrictionPreservesZero :
    (SheafOfModules.overFunctor (ringSheaf X.O) U).PreservesZeroMorphisms :=
  { map_zero := by intros; ext V x; rfl }

attribute [local instance] restrictionPreservesZero

/-- The degreewise restriction of a K-injective complex of sheaves of modules to the slice site
over `U` is K-injective. -/
theorem restriction_isKInjective
    (B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) [B.IsKInjective] :
    (show CochainComplex (SheafOfModules.{u} (ringSheaf (X.over U).O)) ℤ from
      restrictComplex X B U).IsKInjective :=
  Stacks.Cohomology.Localization.isKInjective_over X.J (ringSheaf X.O) U B

private def restrictCochain
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (V : Over U) (n : ℤ)
    (z : (restrictComplex X A V.left).HomComplex (restrictComplex X B V.left) |>.X n) :
    (restrictComplex (X.over U) (restrictComplex X A U) V).HomComplex
      (restrictComplex (X.over U) (restrictComplex X B U) V) |>.X n :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
    ⟨((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).hom.app (op V)).hom
      (z.v p q hpq).val⟩

private lemma restrictCochain_apply
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (V : Over U) (n p q : ℤ)
    (hpq : p + n = q)
    (z : (restrictComplex X A V.left).HomComplex (restrictComplex X B V.left) |>.X n)
    (W : (Over V)ᵒᵖ)
    (x : ((restrictComplex (X.over U) (restrictComplex X A U) V).X p).val.obj W) :
    (((restrictCochain X U A B V n z).v p q hpq).val.app W) x =
      ((z.v p q hpq).val.app (op (Over.mk W.unop.hom.left))) x :=
  Stacks.SheafOfModules.InternalHom.internalHomOverIso_hom_app X U (A.X p) (B.X q) (op V)
    (z.v p q hpq).val W x

private def restrictCochainEquiv
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (V : Over U) (n : ℤ) :
    ((restrictComplex X A V.left).HomComplex (restrictComplex X B V.left)).X n ≃+
      ((restrictComplex (X.over U) (restrictComplex X A U) V).HomComplex
        (restrictComplex (X.over U) (restrictComplex X B U) V)).X n where
  toFun := restrictCochain X U A B V n
  invFun z := CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
    ⟨((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).inv.app (op V)).hom
      (z.v p q hpq).val⟩
  left_inv z := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply SheafOfModules.hom_ext
    exact congrArg (fun f => (f.app (op V)).hom (z.v p q hpq).val)
      (Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).hom_inv_id
  right_inv z := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply SheafOfModules.hom_ext
    exact congrArg (fun f => (f.app (op V)).hom (z.v p q hpq).val)
      (Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).inv_hom_id
  map_add' z w := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply SheafOfModules.hom_ext
    exact map_add _ _ _

private lemma sheafHom_smul_apply
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {F G : SheafOfModules.{u} R}
    (r : ℤˣ) (f : F ⟶ G) (V : Cᵒᵖ) (x : F.val.obj V) :
    ((r • f).val.app V) x = r • (f.val.app V x) := by
  have : (SheafOfModules.evaluation R V).Additive := { map_add := rfl }
  show ((SheafOfModules.evaluation R V).map ((r : ℤ) • f)) x = _
  rw [Functor.map_zsmul]
  rfl

private lemma restrictCochain_d
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (V : Over U) (i j : ℤ)
    (z : ((restrictComplex X A V.left).HomComplex (restrictComplex X B V.left)).X i) :
    CochainComplex.HomComplex.δ i j (restrictCochain X U A B V i z) =
      restrictCochain X U A B V j (CochainComplex.HomComplex.δ i j z) := by
  by_cases h : i + 1 = j
  · apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    ext W x
    rw [CochainComplex.HomComplex.δ_v i j h _ p q hpq _ _ rfl rfl, restrictCochain_apply,
      CochainComplex.HomComplex.δ_v i j h _ p q hpq _ _ rfl rfl]
    simp only [SheafOfModules.add_val, SheafOfModules.comp_val]
    show (_ : (B.X q).val.obj (op W.unop.left.left)) + _ = _ + _
    congr 1
    · rw [sheafHom_smul_apply, sheafHom_smul_apply]
      apply congrArg (fun y : (B.X q).val.obj (op W.unop.left.left) => j.negOnePow • y)
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
      rw [restrictCochain_apply]
      rfl
  · rw [CochainComplex.HomComplex.δ_shape i j h,
      CochainComplex.HomComplex.δ_shape i j h]
    exact (restrictCochainEquiv X U A B V j).map_zero.symm

private def sheafHomRestrictionSectionIso
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (V : Over U) :
    sectionComplex X (sheafHomComplex X A B).obj V.left ≅
      sectionComplex (X.over U)
        (sheafHomComplex (X.over U)
          (restrictComplex X A U) (restrictComplex X B U)).obj V :=
  (sheafHomComplex X A B).sectionsIso V.left ≪≫
    HomologicalComplex.Hom.isoOfComponents
      (fun n => AddEquiv.toAddCommGrpIso (restrictCochainEquiv X U A B V n))
      (by
        intro i j hij
        ext z
        exact restrictCochain_d X U A B V i j z) ≪≫
    ((sheafHomComplex (X.over U)
      (restrictComplex X A U) (restrictComplex X B U)).sectionsIso V).symm

/-- The extensionality principle of
`AlgebraicGeometry.RingedSite.homSection_ext` in the form the restriction arguments of this file
use it: the hypothesis quantifies over an object of the slice rather than over an object of the
site together with an arrow to `V`. The two are the same quantifier, through `Over.mk`. -/
private lemma homSection_ext_over
    {Y : RingedSite.{u, u, u}} {A B : CochainComplex (SheafOfModules.{u} (ringSheaf Y.O)) ℤ}
    (H : SheafHomComplex Y A B) (V : Y.C) (n : ℤ)
    {s t : (H.obj.X n).val.obj (op V)}
    (h : ∀ p q (hpq : p + n = q) (W : (Over V)ᵒᵖ)
      (x : ((restrictComplex Y A V).X p).val.obj W),
      (((H.sectionsIso V).hom.f n s).v p q hpq).val.app W x =
        (((H.sectionsIso V).hom.f n t).v p q hpq).val.app W x) : s = t :=
  AlgebraicGeometry.RingedSite.homSection_ext Y H V n
    (fun p q hpq _ i x => h p q hpq (op (Over.mk i)) x)

private lemma sheafHomRestrictionSectionIso_apply
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (V : Over U) (n p q : ℤ)
    (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op V.left))
    (W : (Over V)ᵒᵖ)
    (x : ((restrictComplex (X.over U) (restrictComplex X A U) V).X p).val.obj W) :
    ((((sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)).sectionsIso V).hom.f n
      ((sheafHomRestrictionSectionIso X U A B V).hom.f n s)).v p q hpq).val.app W x =
        ((((sheafHomComplex X A B).sectionsIso V.left).hom.f n s).v p q hpq).val.app
          (op (Over.mk W.unop.hom.left)) x := by
  have h := Iso.inv_hom_id_apply
    ((HomologicalComplex.eval _ _ n).mapIso ((sheafHomComplex (X.over U)
      (restrictComplex X A U) (restrictComplex X B U)).sectionsIso V))
    (restrictCochain X U A B V n (((sheafHomComplex X A B).sectionsIso V.left).hom.f n s))
  exact (congrArg (fun z => (z.v p q hpq).val.app W x) h).trans
    (restrictCochain_apply X U A B V n p q hpq _ W x)

/-- The section identification of `sheafHomRestrictionSectionIso`, as an isomorphism of modules:
it is compatible with the scalar actions. -/
private def restrictionSectionIso
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (V : Over U) (n : ℤ) :
    ((sheafHomComplex X A B).obj.X n).val.obj (op V.left) ≅
      ((sheafHomComplex (X.over U) (restrictComplex X A U)
        (restrictComplex X B U)).obj.X n).val.obj (op V) :=
  ModuleCat.isoMk ((HomologicalComplex.eval _ _ n).mapIso (sheafHomRestrictionSectionIso X U A B V))
    (fun r => by
      ext s
      apply homSection_ext_over
        (sheafHomComplex (X.over U) (restrictComplex X A U)
          (restrictComplex X B U)) V n
      intro p q hpq W x
      refine ((sheafHomComplex (X.over U) (restrictComplex X A U)
          (restrictComplex X B U)).smul_natural_app V r n p q hpq
          ((sheafHomRestrictionSectionIso X U A B V).hom.f n s) W x).trans ?_
      rw [sheafHomRestrictionSectionIso_apply]
      refine Eq.trans ?_ (sheafHomRestrictionSectionIso_apply X U A B V n p q hpq _ W x).symm
      exact ((sheafHomComplex X A B).smul_natural V.left r n p q hpq s W.unop.hom.left x).symm)

private lemma restrictionSectionIso_natural
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ)
    {V W : Over U} (f : W ⟶ V)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op V.left)) :
    (sheafHomRestrictionSectionIso X U A B W).hom.f n
      (((sheafHomComplex X A B).obj.X n).val.map f.left.op s) =
    ((sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)).obj.X n).val.map f.op
        ((sheafHomRestrictionSectionIso X U A B V).hom.f n s) := by
  apply homSection_ext_over
    (sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)) W n
  intro p q hpq Z x
  rw [sheafHomRestrictionSectionIso_apply,
    ← (sheafHomComplex X A B).restrict_natural f.left n p q hpq s Z.unop.hom.left x,
    ← (sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)).restrict_natural_app f n p q hpq _ Z x,
    sheafHomRestrictionSectionIso_apply]
  rfl

/-- **Restriction of the internal Hom complex to a slice.** The degreewise restriction of
`SheafHom(A, B)` to the site over `U` is the internal Hom complex of the restrictions, by the
canonical restriction isomorphism of Stacks 0E8H on every local homogeneous component. This is
the chain-level form of Stacks 08JB; `sheafHomRestrictionComplexIso_isRestriction` records that
it is the restriction map, and `sheafHomRestrictionComplexIso_natural` its naturality.

This is `@[no_expose]`: its construction goes through the private section isomorphisms of this
file, and a public definition whose body is exposed may not mention them. Nothing downstream
unfolds it; it is used only through its naturality. -/
@[no_expose]
def sheafHomRestrictionComplexIso
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    restrictComplex X (sheafHomComplex X A B).obj U ≅
      (sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).obj := by
  let e (n : ℤ) :
      ((restrictComplex X (sheafHomComplex X A B).obj U).X n).val ≅
        ((sheafHomComplex (X.over U)
          (restrictComplex X A U) (restrictComplex X B U)).obj.X n).val :=
    PresheafOfModules.isoMk
      (fun V => restrictionSectionIso X U A B V.unop n)
      (fun _ _ f => by
        ext s
        exact restrictionSectionIso_natural X U A B n f.unop s)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (SheafOfModules.fullyFaithfulForget _).preimageIso (e n)) ?_
  intro i j hij
  ext V s
  exact ConcreteCategory.congr_hom
    ((sheafHomRestrictionSectionIso X U A B V.unop).hom.comm i j) s

/-- **The chain-level restriction isomorphism is the restriction map.** Every local homogeneous
component of `sheafHomRestrictionComplexIso` is the canonical restriction isomorphism of
Stacks 0E8H, which is the defining property `IsInternalHomRestrictionMap`. -/
lemma sheafHomRestrictionComplexIso_isRestriction
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    IsInternalHomRestrictionMap X U A B (sheafHomRestrictionComplexIso X U A B).hom := by
  intro V n p q hpq s
  ext W x
  show ((((sheafHomComplex (X.over U) (restrictComplex X A U)
    (restrictComplex X B U)).sectionsIso V.unop).hom.f n
      ((sheafHomRestrictionSectionIso X U A B V.unop).hom.f n s)).v p q hpq).val.app W x = _
  rw [sheafHomRestrictionSectionIso_apply]
  exact (Stacks.SheafOfModules.InternalHom.internalHomOverIso_hom_app X U (A.X p) (B.X q) V
    ((((sheafHomComplex X A B).sectionsIso V.unop.left).hom.f n s).v p q hpq).val W x).symm

/-- **The chain-level restriction isomorphism is natural in both variables.** Restricting the
map of internal Hom complexes induced by `f : A' ⟶ A` and `g : B ⟶ B'` to the site over `U` is,
through `sheafHomRestrictionComplexIso`, the map of internal Hom complexes over `U` induced by
the restrictions of `f` and `g`. -/
lemma sheafHomRestrictionComplexIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ} (f : A' ⟶ A) (g : B ⟶ B') :
    ((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (homMap X f g) ≫
      (sheafHomRestrictionComplexIso X U A' B').hom =
    (sheafHomRestrictionComplexIso X U A B).hom ≫
      homMap (X.over U)
        (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)
        (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) := by
  ext n V s
  apply homSection_ext_over
    (sheafHomComplex (X.over U) (restrictComplex X A' U)
      (restrictComplex X B' U)) V.unop n
  intro p q hpq W x
  show ((((sheafHomComplex (X.over U) (restrictComplex X A' U)
    (restrictComplex X B' U)).sectionsIso V.unop).hom.f n
      ((sheafHomRestrictionSectionIso X U A' B' V.unop).hom.f n
        (((homMap X f g).f n).val.app (op V.unop.left) s))).v p q hpq).val.app W x =
    ((((sheafHomComplex (X.over U) (restrictComplex X A' U)
      (restrictComplex X B' U)).sectionsIso V.unop).hom.f n
        (((homMap (X.over U) (restrictComplexMap X U f) (restrictComplexMap X U g)).f n).val.app
          (op V.unop) ((sheafHomRestrictionSectionIso X U A B V.unop).hom.f n s))).v
            p q hpq).val.app W x
  rw [sheafHomRestrictionSectionIso_apply X U A' B' V.unop n p q hpq
    (((homMap X f g).f n).val.app (op V.unop.left) s) W,
    sectionsIso_homMap_v X f g V.unop.left n p q hpq s,
    sectionsIso_homMap_v (X.over U) (restrictComplexMap X U f) (restrictComplexMap X U g)
    V.unop n p q hpq ((sheafHomRestrictionSectionIso X U A B V.unop).hom.f n s)]
  show _ = (g.f q).val.app (op W.unop.left.left)
    (((((sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)).sectionsIso V.unop).hom.f n
        ((sheafHomRestrictionSectionIso X U A B V.unop).hom.f n s)).v p q hpq).val.app W
          ((f.f p).val.app (op W.unop.left.left) x))
  rw [sheafHomRestrictionSectionIso_apply]
  rfl

end

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [HasSheafify (X.over U).J AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U)]

/-- The restriction to the slice over `U` of the class of a complex is the class of its
degreewise restriction. This is `CategoryTheory.Functor.mapDerivedCategoryFactors` for the
restriction functor, which is exact. -/
abbrev restrictionComparison (A : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj (restrictComplex X A U) :=
  (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategoryFactors.app A

/-- The source model comparison, obtained from the fixed K-injective model
and the exact-restriction comparison. -/
noncomputable def restrictionSourceComparison
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) [B.IsKInjective] :
    ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj
      (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
        (DerivedCategory.Q.obj B)) ≅
      DerivedCategory.Q.obj (restrictComplex X (sheafHomComplex X A B).obj U) :=
  ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).mapIso
    (derivedSheafHomComparison X A B) ≪≫
    restrictionComparison X U (sheafHomComplex X A B).obj

/-- The target model comparison, using exact restriction in both arguments
and the K-injectivity of the restricted target supplied by Tag 08FI. -/
noncomputable def restrictionTargetComparison
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) [B.IsKInjective] :
    ((derivedSheafHomBifunctor (X.over U)).obj
      (op (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj
        (DerivedCategory.Q.obj A)))).obj
        (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj
          (DerivedCategory.Q.obj B)) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex (X.over U)
          (restrictComplex X A U) (restrictComplex X B U)).obj := by
  have : CochainComplex.IsKInjective
      (show CochainComplex (SheafOfModules.{u} (ringSheaf (X.over U).O)) ℤ from
        restrictComplex X B U) :=
    Stacks.Cohomology.Localization.isKInjective_over X.J (ringSheaf X.O) U B
  exact ((derivedSheafHomBifunctor (X.over U)).mapIso
      (restrictionComparison X U A).symm.op).app _ ≪≫
    ((derivedSheafHomBifunctor (X.over U)).obj
      (op (DerivedCategory.Q.obj (restrictComplex X A U)))).mapIso
        (restrictionComparison X U B) ≪≫
    derivedSheafHomComparison (X.over U)
      (restrictComplex X A U) (restrictComplex X B U)

section

omit [HasSheafify (X.over U).J AddCommGrpCat.{u}] in
private lemma restrictionComparison_natural
    {A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ} (f : A ⟶ B) :
    (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory.map
        (DerivedCategory.Q.map f) ≫ (restrictionComparison X U B).hom =
      (restrictionComparison X U A).hom ≫ DerivedCategory.Q.map
        (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) :=
  (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategoryFactors.hom.naturality f

private def restrictionArgumentsComparison :
    ((DerivedCategory.Q ⋙
        (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).op.prod
      (DerivedCategory.Q ⋙ (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory)) ⋙
        Functor.uncurry.obj (derivedSheafHomBifunctor (X.over U)) ≅
    (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).op.prod
      ((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)) ⋙
        Functor.uncurry.obj (derivedSheafHomBifunctor (X.over U)) :=
  Functor.isoWhiskerRight (NatIso.prod (NatIso.op ((SheafOfModules.overFunctor.{u} (ringSheaf X.O)
    U).mapDerivedCategoryFactors).symm)
    ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategoryFactors)) _

private abbrev restrictionSourceFunctor :
    (DerivedCategory (SheafOfModules.{u} (ringSheaf X.O)))ᵒᵖ × DerivedCategory (SheafOfModules.{u}
      (ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf (X.over U).O)) :=
  Functor.uncurry.obj (derivedSheafHomBifunctor X) ⋙ (SheafOfModules.overFunctor.{u} (ringSheaf X.O)
    U).mapDerivedCategory

private abbrev restrictionTargetFunctor :
    (DerivedCategory (SheafOfModules.{u} (ringSheaf X.O)))ᵒᵖ × DerivedCategory (SheafOfModules.{u}
      (ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf (X.over U).O)) :=
  (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).op.prod
    ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory)) ⋙
    Functor.uncurry.obj (derivedSheafHomBifunctor (X.over U))

/-- Postcomposition with the image of an identity is the identity. -/
private lemma comp_functor_map_id {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {Y : E} {d : D} (φ : Y ⟶ F.obj d) : φ ≫ F.map (𝟙 d) = φ := by
  rw [F.map_id, Category.comp_id]

/-- Postcomposition with the image of an identity under two successive functors. -/
private lemma comp_map_map_id {D E F : Type*} [Category D] [Category E] [Category F]
    (G : D ⥤ E) (H : E ⥤ F) {Y : F} {d : D} (φ : Y ⟶ H.obj (G.obj d)) :
    φ ≫ H.map (G.map (𝟙 d)) = φ := by
  rw [G.map_id, H.map_id, Category.comp_id]

/-- Precomposition with a component of the image of an identity is the identity. -/
private lemma map_id_app_comp {D E J : Type*} [Category D] [Category E] [Category J]
    (B : J ⥤ D ⥤ E) {j : J} {d : D} {Y : E} (ψ : (B.obj j).obj d ⟶ Y) :
    (B.map (𝟙 j)).app d ≫ ψ = ψ := by
  rw [B.map_id, NatTrans.id_app, Category.id_comp]

/-- Precomposition with a component of the image, under a contravariant argument, of the
image of an identity. -/
private lemma map_op_map_id_app_comp {D E J : Type*} [Category D] [Category E] [Category J]
    (G : J ⥤ D) (B : Dᵒᵖ ⥤ D ⥤ E) {j : J} {d : D} {Y : E}
    (ψ : (B.obj (op (G.obj j))).obj d ⟶ Y) :
    (B.map (G.map (𝟙 j)).op).app d ≫ ψ = ψ := by
  rw [G.map_id, op_id, B.map_id, NatTrans.id_app, Category.id_comp]

/-- The action of the source functor on a pair of morphisms, with the composite functor
evaluated away. The two sides are definitionally equal, but a composite functor does not
reduce at the transparency a rewrite uses, so only this form is usable in a rewrite. -/
private lemma restrictionSourceFunctor_map
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))}
    (a : op K ⟶ op K') (b : L ⟶ L') :
    (restrictionSourceFunctor X U).map (Prod.mkHom a b) =
      ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
        (((derivedSheafHomBifunctor X).map a).app L ≫
          ((derivedSheafHomBifunctor X).obj (op K')).map b) := rfl

/-- The action of the target functor on a pair of morphisms, with the composite functor
evaluated away. See `restrictionSourceFunctor_map`. -/
private lemma restrictionTargetFunctor_map
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))}
    (a : op K ⟶ op K') (b : L ⟶ L') :
    (restrictionTargetFunctor X U).map (Prod.mkHom a b) =
      ((derivedSheafHomBifunctor (X.over U)).map
          (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
            a.unop).op).app
            (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj L) ≫
        ((derivedSheafHomBifunctor (X.over U)).obj
          (op (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj K'))).map
            (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map b) := rfl

/-- The source functor on a pair whose second component is an identity. -/
private lemma restrictionSourceFunctor_map_fst
    {K K' L : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))} (a : K' ⟶ K) :
    (restrictionSourceFunctor X U).map (Prod.mkHom a.op (𝟙 L)) =
      ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
        (((derivedSheafHomBifunctor X).map a.op).app L) := by
  rw [restrictionSourceFunctor_map, comp_functor_map_id]

/-- The target functor on a pair whose second component is an identity. -/
private lemma restrictionTargetFunctor_map_fst
    {K K' L : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))} (a : K' ⟶ K) :
    (restrictionTargetFunctor X U).map (Prod.mkHom a.op (𝟙 L)) =
      ((derivedSheafHomBifunctor (X.over U)).map
          (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map a).op).app
            (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj L) :=
  (restrictionTargetFunctor_map X U a.op (𝟙 L)).trans (comp_map_map_id _ _ _)

/-- The source functor on a pair whose first component is an identity. -/
private lemma restrictionSourceFunctor_map_snd
    {K L L' : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))} (b : L ⟶ L') :
    (restrictionSourceFunctor X U).map (Prod.mkHom (𝟙 (op K)) b) =
      ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
        (((derivedSheafHomBifunctor X).obj (op K)).map b) := by
  rw [restrictionSourceFunctor_map, map_id_app_comp]

/-- The target functor on a pair whose first component is an identity. -/
private lemma restrictionTargetFunctor_map_snd
    {K L L' : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))} (b : L ⟶ L') :
    (restrictionTargetFunctor X U).map (Prod.mkHom (𝟙 (op K)) b) =
      ((derivedSheafHomBifunctor (X.over U)).obj
        (op (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj K))).map
          (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map b) :=
  (restrictionTargetFunctor_map X U (𝟙 (op K)) b).trans
    (map_op_map_id_app_comp (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory
      (derivedSheafHomBifunctor (X.over U)) _)

private lemma restrictionSourceComparison_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ} [B.IsKInjective]
      [B'.IsKInjective]
    (f : A' ⟶ A) (g : B ⟶ B') :
    (restrictionSourceFunctor X U).map
      (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (restrictionSourceComparison X U A' B').hom =
    (restrictionSourceComparison X U A B).hom ≫ DerivedCategory.Q.map
      (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (homMap X f g)) := by
  show ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
    (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app (DerivedCategory.Q.obj B) ≫
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
        (DerivedCategory.Q.map g)) ≫
      (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
        (derivedSheafHomComparison X A' B').hom ≫ _) =
    (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
      (derivedSheafHomComparison X A B).hom ≫ _) ≫ _
  rw [← Functor.map_comp_assoc, Category.assoc,
    derivedSheafHomComparison_naturality X f g,
    Functor.map_comp, Category.assoc, restrictionComparison_natural]
  simp only [Category.assoc]

attribute [local instance] restriction_isKInjective

private lemma restrictionTargetComparison_eq
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) [B.IsKInjective] :
    (restrictionTargetComparison X U A B).hom =
      (restrictionArgumentsComparison X U).hom.app (op A, B) ≫
        (derivedSheafHomComparison (X.over U)
          (restrictComplex X A U) (restrictComplex X B U)).hom :=
  (Category.assoc _ _ _).symm

private lemma restrictionTargetComparison_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ} [B.IsKInjective]
      [B'.IsKInjective]
    (f : A' ⟶ A) (g : B ⟶ B') :
    (restrictionTargetFunctor X U).map
      (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (restrictionTargetComparison X U A' B').hom =
    (restrictionTargetComparison X U A B).hom ≫ DerivedCategory.Q.map
      (homMap (X.over U)
        (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)
        (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g)) := by
  rw [restrictionTargetComparison_eq, restrictionTargetComparison_eq]
  have h : (restrictionTargetFunctor X U).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (restrictionArgumentsComparison X U).hom.app (op A', B') = _ :=
    (restrictionArgumentsComparison X U).hom.naturality (Prod.mkHom f.op g)
  exact (CommSq.vert_comp ⟨h⟩ ⟨(Category.assoc _ _ _).trans
    (derivedSheafHomComparison_naturality (X.over U)
      (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)
      (((SheafOfModules.overFunctor (ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g))⟩).w

private def restrictionModelIso
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) [B.IsKInjective] :
    (restrictionSourceFunctor X U).obj (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      (restrictionTargetFunctor X U).obj (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) :=
  restrictionSourceComparison X U A B ≪≫
    DerivedCategory.Q.mapIso (sheafHomRestrictionComplexIso X U A B) ≪≫
    (restrictionTargetComparison X U A B).symm

private lemma restrictionModelIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ} [B.IsKInjective]
      [B'.IsKInjective]
    (f : A' ⟶ A) (g : B ⟶ B') :
    (restrictionSourceFunctor X U).map
      (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (restrictionModelIso X U A' B').hom =
    (restrictionModelIso X U A B).hom ≫
      (restrictionTargetFunctor X U).map
      (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) := by
  have hI := (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map (sheafHomRestrictionComplexIso_natural X U f g)).trans
      (DerivedCategory.Q.map_comp _ _))
  exact (CommSq.vert_comp ⟨restrictionSourceComparison_natural X U f g⟩
    (CommSq.vert_comp ⟨hI⟩
      (CommSq.vert_inv ⟨restrictionTargetComparison_natural X U f g⟩))).w

end

/-- The comparison induced by restriction of internal-Hom complexes, natural
in both derived arguments and characterized on K-injective models. -/
structure DerivedHomRestriction where
  /-- Restriction of the internal-Hom complex on representatives. -/
  complexMap (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    restrictComplex X (sheafHomComplex X A B).obj U ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).obj
  /-- Each homogeneous component is the canonical restriction of Tag 0E8H. -/
  complexMap_isRestriction (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    IsInternalHomRestrictionMap X U A B (complexMap A B)
  /-- The comparison itself: restricting the derived internal Hom to the slice over `U` is the
  derived internal Hom of the restrictions. -/
  iso (K L : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))) :
    ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj
      (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor (X.over U)).obj
        (op (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj K))).obj
          (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj L)
  /-- The comparison is natural in the first, contravariant argument. -/
  natural_left {K K' L : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))} (f : K' ⟶ K) :
    ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
      (((derivedSheafHomBifunctor X).map f.op).app L) ≫
      (iso K' L).hom =
        (iso K L).hom ≫
          ((derivedSheafHomBifunctor (X.over U)).map
            (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map f).op).app
              (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj L)
  /-- The comparison is natural in the second, covariant argument. -/
  natural_right {K L L' : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))} (g : L ⟶ L') :
    ((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map
      (((derivedSheafHomBifunctor X).obj (op K)).map g) ≫
      (iso K L').hom =
        (iso K L).hom ≫
          ((derivedSheafHomBifunctor (X.over U)).obj
            (op (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).obj
              K))).map
              (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapDerivedCategory).map g)
  /-- On a K-injective representative, the derived comparison is the
  localization of the canonical restriction map of Hom complexes. -/
  model (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) [B.IsKInjective] :
    (iso (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
        (restrictionTargetComparison X U A B).hom =
      (restrictionSourceComparison X U A B).hom ≫
        DerivedCategory.Q.map (complexMap A B)

/-- The component of the complex map restricts each local homogeneous map
along the iterated slice, as in the canonical comparison of Tag 0E8H. -/
@[stacks 08JB "restriction on local homogeneous cochains"]
theorem DerivedHomRestriction.complexMap_apply
    (r : DerivedHomRestriction X U)
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ)
    (V : (Over U)ᵒᵖ) (W : (Over V.unop)ᵒᵖ)
    (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op V.unop.left))
    (x : ((restrictComplex (X.over U)
      (restrictComplex X A U) V.unop).X p).val.obj W) :
    (((AddCommGrpCat.Hom.hom
      (((sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).sectionsIso V.unop).hom.f n)
      (((r.complexMap A B).f n).val.app V s)).v p q hpq).val.app W x) =
      (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X A B).sectionsIso V.unop.left).hom.f n) s).v p q hpq).val.app
          (op (Over.mk W.unop.hom.left)) x) := by
  have h' := congrArg (fun y => y.app W x) (r.complexMap_isRestriction A B V n p q hpq s)
  have hCan := Stacks.SheafOfModules.InternalHom.internalHomOverIso_hom_app X U (A.X p) (B.X q) V
    (((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso V.unop.left).hom.f n) s).v
        p q hpq).val) W x
  exact h'.trans hCan

/-- Composing out the inverse half of an iterated isomorphism. -/
private lemma iso_trans_symm_hom_comp {D : Type*} [Category D] {W Y Z T : D}
    (α : Y ≅ Z) (β : Z ≅ T) (γ : W ≅ T) :
    (α ≪≫ β ≪≫ γ.symm).hom ≫ γ.hom = α.hom ≫ β.hom := by
  simp

/-- **Extension of an isomorphism along a resolution.** Let `Q : C ⥤ D` be a localization
functor for `W`, let `R : C ⥤ C` be an endofunctor whose augmentation `η : 𝟭 C ⟶ R` becomes
invertible in `D`, and let `P` be a property of objects of `C` holding on the image of `R`. Then
a family of isomorphisms `F.obj (Q.obj c) ≅ G.obj (Q.obj c)`, given only for the objects `c`
satisfying `P` and natural for the morphisms between such objects, extends to an isomorphism of
functors `F ≅ G`, and the extension still has the given components at the objects satisfying
`P`.

The extension is the preimage, under the fully faithful whiskering by `Q`, of the isomorphism
`Q ⋙ F ≅ Q ⋙ G` obtained by conjugating the given family at `R c` with the isomorphism
`Q.map (η.app c)`.

With `P` the property of being K-injective and `R` a functorial K-injective resolution, this is
how a comparison of derived functors defined on K-injective representatives is extended to the
whole derived category. -/
lemma extendIsoFromResolution
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (R : C ⥤ C) (η : 𝟭 C ⟶ R) [∀ c, IsIso (Q.map (η.app c))]
    (P : C → Prop) (hR : ∀ c, P (R.obj c))
    (F G : D ⥤ E) (e : ∀ c, P c → (F.obj (Q.obj c) ≅ G.obj (Q.obj c)))
    (he : ∀ {c c'} (hc : P c) (hc' : P c') (f : c ⟶ c'),
      F.map (Q.map f) ≫ (e c' hc').hom = (e c hc).hom ≫ G.map (Q.map f)) :
    ∃ e' : F ≅ G, ∀ c (hc : P c), e'.hom.app (Q.obj c) = (e c hc).hom := by
  let t : Q ⋙ F ≅ Q ⋙ G := NatIso.ofComponents
    (fun c => F.mapIso (asIso (Q.map (η.app c))) ≪≫ e (R.obj c) (hR c) ≪≫
      (G.mapIso (asIso (Q.map (η.app c)))).symm)
    (by
      intro c c' f
      dsimp
      have hn := congrArg (fun k => Q.map k) (η.naturality f)
      dsimp at hn
      simp only [Functor.map_comp] at hn
      have hF := congrArg (fun k => F.map k) hn
      simp only [Functor.map_comp] at hF
      simp only [Category.assoc]
      rw [reassoc_of% hF, reassoc_of% (he (hR c) (hR c') (R.map f))]
      congr 2
      apply (cancel_mono (G.map (Q.map (η.app c')))).mp
      simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
      rw [Q.map_comp, hn]
      simp)
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  refine ⟨ff.preimageIso t, fun c hc => ?_⟩
  have ht := congrArg (fun k => k.app c) (ff.map_preimage t.hom)
  change (ff.preimageIso t).hom.app (Q.obj c) = _ at ht
  rw [ht]
  dsimp [t]
  rw [reassoc_of% (he hc (hR c) (η.app c))]
  simp

/-- Derived internal Hom commutes, naturally in both arguments, with
restriction to the slice site over any object. -/
@[stacks 08JB]
theorem derivedHom_restriction_exists :
    Nonempty (DerivedHomRestriction X U) := by
  let C := CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ
  let Q : C ⥤ DerivedCategory (SheafOfModules.{u} (ringSheaf X.O)) := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf X.O)) (ComplexShape.up ℤ)
  let R := (𝟭 Cᵒᵖ).prod (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u}
    (ringSheaf X.O)))
  let η : 𝟭 (Cᵒᵖ × C) ⟶ R :=
    { app := fun c => Prod.mkHom (𝟙 c.1)
        ((Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u}
          (ringSheaf X.O))).app c.2)
      naturality _ _ f := Prod.ext (by simp [R])
        ((Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u}
          (ringSheaf X.O))).naturality f.2) }
  have (c : Cᵒᵖ × C) : IsIso ((Q.op.prod Q).map (η.app c)) := by
    dsimp [Q, η]
    exact (isIso_prod_iff _ _).2 ⟨(Q.mapIso (Iso.refl c.1.unop)).op.isIso_hom, inferInstance⟩
  obtain ⟨e, he⟩ := extendIsoFromResolution (Q.op.prod Q) (W.op.prod W) R η
    (fun c : Cᵒᵖ × C => c.2.IsKInjective)
    (fun c => Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective (SheafOfModules.{u}
      (ringSheaf X.O)) c.2)
    (restrictionSourceFunctor X U) (restrictionTargetFunctor X U)
    (fun c hc => by
      have := hc
      exact restrictionModelIso X U c.1.unop c.2)
    (fun hc hc' f => by
      have := hc
      have := hc'
      exact restrictionModelIso_natural X U f.1.unop f.2)
  refine ⟨{ complexMap := fun A B => (sheafHomRestrictionComplexIso X U A B).hom
            complexMap_isRestriction := sheafHomRestrictionComplexIso_isRestriction X U
            iso := fun K L => e.app (op K, L)
            natural_left := ?_
            natural_right := ?_
            model := ?_ }⟩
  · intro K K' L f
    have h := e.hom.naturality (Prod.mkHom f.op (𝟙 L))
    rwa [restrictionSourceFunctor_map_fst, restrictionTargetFunctor_map_fst] at h
  · intro K L L' g
    have h := e.hom.naturality (Prod.mkHom (𝟙 (op K)) g)
    rwa [restrictionSourceFunctor_map_snd, restrictionTargetFunctor_map_snd] at h
  · intro A B hB
    rw [show (e.app (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B)).hom =
      (restrictionModelIso X U A B).hom from he (op A, B) hB]
    exact iso_trans_symm_hom_comp (restrictionSourceComparison X U A B)
      (DerivedCategory.Q.mapIso (sheafHomRestrictionComplexIso X U A B))
      (restrictionTargetComparison X U A B)

/-- The natural restriction isomorphism for derived internal Hom. -/
noncomputable def derivedHomRestriction : DerivedHomRestriction X U :=
  Classical.choice (derivedHom_restriction_exists X U)

/-- Restriction of internal-Hom complexes is induced on every homogeneous
component by the canonical internal-Hom restriction isomorphism of Tag 0E8H. -/
@[stacks 08JB "restriction of internal-Hom complexes"]
theorem derivedHomRestriction_complexMap_isRestriction
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    IsInternalHomRestrictionMap X U A B
      ((derivedHomRestriction X U).complexMap A B) :=
  (derivedHomRestriction X U).complexMap_isRestriction A B

/-- Under the fixed K-injective and exact-restriction comparisons, the full
derived comparison is the localization of the restriction map of internal-Hom
complexes induced by `Stacks.SheafOfModules.InternalHom.internalHomOverIso`. -/
@[stacks 08JB "canonical model characterization"]
theorem derivedHomRestriction_model
    (A B : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) [B.IsKInjective] :
    ((derivedHomRestriction X U).iso
      (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
        (restrictionTargetComparison X U A B).hom =
      (restrictionSourceComparison X U A B).hom ≫
        DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap A B) :=
  (derivedHomRestriction X U).model A B

end AlgebraicGeometry.RingedSite

end
