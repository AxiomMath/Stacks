module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# The internal Hom complex commutes with restriction to a slice, at unequal universes

Let `(C, O)` be a ringed site whose objects, morphisms and structure rings lie in three
independent universes, `U` an object of `C`, and `A`, `B` complexes of `O`-modules. The degreewise
restriction of the internal Hom complex `SheafHom(A, B)` of Stacks 0A8Z to the slice site over
`U` is the internal Hom complex of the restrictions:

`SheafHom(A, B)|_U ≅ SheafHom(A|_U, B|_U)`.

This is the chain-level form of Stacks 08JB. It is
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction` with the ringed
site freed from `RingedSite.{u, u, u}`; the construction is the same, through the
identification of sections with ordinary Hom complexes and the restriction isomorphism of
Stacks 0E8H (`Stacks.SheafOfModules.InternalHom.internalHomOverIso`), both of which are stated at
independent universes.

## Main definitions

* `AlgebraicGeometry.RingedSite.Raised.sheafHomRestrictionComplexIso`: the comparison.

## Main results

* `AlgebraicGeometry.RingedSite.Raised.homSection_ext`: a section of an internal Hom complex is
  determined by its evaluations.
* `AlgebraicGeometry.RingedSite.Raised.sheafHomRestrictionComplexIso_natural`: the comparison is
  natural in both variables.

## Implementation notes

Sheaves of modules on the slice site are indexed by `ringSheaf (X.over U).O` on one side and by
`(ringSheaf X.O).over U` in `restrictComplex`; the two agree only after unfolding, so the functors
involved are made `implicit_reducible` locally.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

namespace AlgebraicGeometry.RingedSite.Raised

universe m u v w

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
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



/-- **A section of an internal Hom complex is determined by its evaluations**, over a ringed
site at unequal universes. -/
lemma homSection_ext (X : RingedSite.{u, v, w})
    {K L : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n : ℤ) {f g : (H.obj.X n).val.obj (op U)}
    (h : ∀ (p q : ℤ) (hpq : p + n = q) (V : X.C) (i : V ⟶ U) (x : (K.X p).val.obj (op V)),
      ((H.sectionsEquiv U n f).v p q hpq).val.app (op (Over.mk i)) x =
        ((H.sectionsEquiv U n g).v p q hpq).val.app (op (Over.mk i)) x) : f = g := by
  refine (H.sectionsEquiv U n).injective (CochainComplex.HomComplex.Cochain.ext _ _
    fun p q hpq ↦ ?_)
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext
    (LinearMap.ext fun x ↦ h p q hpq W.unop.left W.unop.hom x))

variable (X : RingedSite.{u, v, w}) (U : X.C)

private def restrictCochain
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (V : Over U) (n : ℤ)
    (z : (restrictComplex X A V.left).HomComplex (restrictComplex X B V.left) |>.X n) :
    (restrictComplex (X.over U) (restrictComplex X A U) V).HomComplex
      (restrictComplex (X.over U) (restrictComplex X B U) V) |>.X n :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
    ⟨((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).hom.app (op V)).hom
      (z.v p q hpq).val⟩

private lemma restrictCochain_apply
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (V : Over U) (n p q : ℤ)
    (hpq : p + n = q)
    (z : (restrictComplex X A V.left).HomComplex (restrictComplex X B V.left) |>.X n)
    (W : (Over V)ᵒᵖ)
    (x : ((restrictComplex (X.over U) (restrictComplex X A U) V).X p).val.obj W) :
    (((restrictCochain X U A B V n z).v p q hpq).val.app W) x =
      ((z.v p q hpq).val.app (op (Over.mk W.unop.hom.left))) x :=
  Stacks.SheafOfModules.InternalHom.internalHomOverIso_hom_app X U (A.X p) (B.X q) (op V)
    (z.v p q hpq).val W x

private def restrictCochainEquiv
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (V : Over U) (n : ℤ) :
    ((restrictComplex X A V.left).HomComplex (restrictComplex X B V.left)).X n ≃+
      ((restrictComplex (X.over U) (restrictComplex X A U) V).HomComplex
        (restrictComplex (X.over U) (restrictComplex X B U) V)).X n where
  toFun := restrictCochain X U A B V n
  invFun z := CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
    ⟨((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).inv.app (op V)).hom
      (z.v p q hpq).val⟩
  left_inv z := CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq ↦
    SheafOfModules.hom_ext (congrArg (fun f => (f.app (op V)).hom (z.v p q hpq).val)
      (Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).hom_inv_id)
  right_inv z := CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq ↦
    SheafOfModules.hom_ext (congrArg (fun f => (f.app (op V)).hom (z.v p q hpq).val)
      (Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q)).inv_hom_id)
  map_add' _ _ := CochainComplex.HomComplex.Cochain.ext _ _ fun _ _ _ ↦
    SheafOfModules.hom_ext (map_add _ _ _)

private lemma sheafHom_smul_apply
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {F G : SheafOfModules.{m} R}
    (r : ℤˣ) (f : F ⟶ G) (V : Cᵒᵖ) (x : F.val.obj V) :
    ((r • f).val.app V) x = r • (f.val.app V x) := by
  have : (SheafOfModules.evaluation R V).Additive := { map_add := rfl }
  change ((SheafOfModules.evaluation R V).map ((r : ℤ) • f)) x = _
  rw [Functor.map_zsmul]
  rfl

private lemma restrictCochain_d
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (V : Over U) (i j : ℤ)
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
    change (_ : (B.X q).val.obj (op W.unop.left.left)) + _ = _ + _
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
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (V : Over U) :
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

/-- A section of an internal Hom complex over `V` is determined by its evaluations at the objects
of the slice over `V`. -/
private lemma homSection_ext_over
    {Y : RingedSite.{u, v, w}} {A B : CochainComplex (SheafOfModules.{m} (ringSheaf Y.O)) ℤ}
    (H : SheafHomComplex Y A B) (V : Y.C) (n : ℤ)
    {s t : (H.obj.X n).val.obj (op V)}
    (h : ∀ p q (hpq : p + n = q) (W : (Over V)ᵒᵖ)
      (x : ((restrictComplex Y A V).X p).val.obj W),
      (((H.sectionsIso V).hom.f n s).v p q hpq).val.app W x =
        (((H.sectionsIso V).hom.f n t).v p q hpq).val.app W x) : s = t :=
  homSection_ext Y H V n
    (fun p q hpq _ i x => h p q hpq (op (Over.mk i)) x)

private lemma sheafHomRestrictionSectionIso_apply
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (V : Over U) (n p q : ℤ)
    (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op V.left))
    (W : (Over V)ᵒᵖ)
    (x : ((restrictComplex (X.over U) (restrictComplex X A U) V).X p).val.obj W) :
    ((((sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)).sectionsIso V).hom.f n
      ((sheafHomRestrictionSectionIso X U A B V).hom.f n s)).v p q hpq).val.app W x =
        ((((sheafHomComplex X A B).sectionsIso V.left).hom.f n s).v p q hpq).val.app
          (op (Over.mk W.unop.hom.left)) x := by
  let H := sheafHomComplex (X.over U)
    (restrictComplex X A U) (restrictComplex X B U)
  have h := Iso.inv_hom_id_apply
    ((HomologicalComplex.eval _ _ n).mapIso (H.sectionsIso V))
    (restrictCochain X U A B V n (((sheafHomComplex X A B).sectionsIso V.left).hom.f n s))
  exact (congrArg (fun z => (z.v p q hpq).val.app W x) h).trans
    (restrictCochain_apply X U A B V n p q hpq _ W x)

/-- The section identification of `sheafHomRestrictionSectionIso`, as an isomorphism of modules:
it is compatible with the scalar actions. -/
private def restrictionSectionIso
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (V : Over U) (n : ℤ) :
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
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) (n : ℤ)
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
  change ((((sheafHomComplex (X.over U) (restrictComplex X A U)
    (restrictComplex X B U)).sectionsIso W).hom.f n
      ((sheafHomRestrictionSectionIso X U A B W).hom.f n _)).v p q hpq).val.app Z x = _
  rw [sheafHomRestrictionSectionIso_apply,
    ← (sheafHomComplex X A B).restrict_natural f.left n p q hpq s Z.unop.hom.left x,
    ← (sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)).restrict_natural_app f n p q hpq _ Z x,
    sheafHomRestrictionSectionIso_apply]
  rfl

/-- **Restriction of the internal Hom complex to a slice, at unequal universes.** The degreewise
restriction of `SheafHom(A, B)` to the site over `U` is the internal Hom complex of the
restrictions, by the canonical restriction isomorphism of Stacks 0E8H on every local homogeneous
component. This is `AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` with the ringed
site freed from `RingedSite.{u, u, u}`. -/
@[no_expose]
def sheafHomRestrictionComplexIso
    (A B : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ) :
    restrictComplex X (sheafHomComplex X A B).obj U ≅
      (sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).obj := by
  let e (n : ℤ) :
      ((restrictComplex X (sheafHomComplex X A B).obj U).X n).val ≅
        ((sheafHomComplex (X.over U)
          (restrictComplex X A U) (restrictComplex X B U)).obj.X n).val :=
    PresheafOfModules.isoMk
      (fun V => restrictionSectionIso X U A B V.unop n)
      (by intro V W f; ext s; exact restrictionSectionIso_natural X U A B n f.unop s)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (SheafOfModules.fullyFaithfulForget _).preimageIso (e n)) ?_
  intro i j hij
  ext V s
  exact ConcreteCategory.congr_hom
    ((sheafHomRestrictionSectionIso X U A B V.unop).hom.comm i j) s

/-- **The chain-level restriction isomorphism is natural in both variables.** Restricting the
map of internal Hom complexes induced by `f : A' ⟶ A` and `g : B ⟶ B'` to the site over `U` is,
through `sheafHomRestrictionComplexIso`, the map of internal Hom complexes over `U` induced by
the restrictions of `f` and `g`. -/
lemma sheafHomRestrictionComplexIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{m} (ringSheaf X.O)) ℤ} (f : A' ⟶ A) (g : B ⟶ B') :
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
  change ((((sheafHomComplex (X.over U) (restrictComplex X A' U)
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
  change _ = (g.f q).val.app (op W.unop.left.left)
    (((((sheafHomComplex (X.over U) (restrictComplex X A U)
      (restrictComplex X B U)).sectionsIso V.unop).hom.f n
        ((sheafHomRestrictionSectionIso X U A B V.unop).hom.f n s)).v p q hpq).val.app W
          ((f.f p).val.app (op W.unop.left.left) x))
  rw [sheafHomRestrictionSectionIso_apply]
  rfl

end AlgebraicGeometry.RingedSite.Raised

end
