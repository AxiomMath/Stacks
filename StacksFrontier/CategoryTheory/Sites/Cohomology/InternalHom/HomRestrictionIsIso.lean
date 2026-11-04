module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction

/-!
# The restriction comparison of internal Hom complexes is an isomorphism

Let `X` be a ringed site, `U` an object of its underlying category and `A`, `B` complexes of
`O`-modules. A morphism

`SheafHom(A, B)|_U ⟶ SheafHom(A|_U, B|_U)`

which is, in every degree and on every local homogeneous component, the canonical restriction of
the internal Hom of modules — the property
`AlgebraicGeometry.RingedSite.IsInternalHomRestrictionMap` — is an isomorphism.

The point is that this is available for **arbitrary** `B`. The comparison
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` is an isomorphism by construction,
but what it does on local sections is not part of its public interface, and the comparison whose
behaviour on sections *is* public —
`AlgebraicGeometry.RingedSite.DerivedHomRestriction.complexMap`, described by
`DerivedHomRestriction.complexMap_apply` of Stacks 08JB — is only known to be invertible in the
derived category when `B` is K-injective, through the `model` field of that structure. A
computation which has to pass through the comparison at a `B` that is not K-injective, such as
`Tot(A ⊗_O I)`, needs both at once: the public description on sections and the invertibility.
This supplies the second from the first.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_of_isInternalHomRestrictionMap`: a morphism with the
  property above is an isomorphism.
* `AlgebraicGeometry.RingedSite.complexMap_naturality_right`: the comparison
  `DerivedHomRestriction.complexMap` is natural in the target variable. The corresponding
  statement for the *isomorphism* is `sheafHomRestrictionComplexIso_natural`; this is the one for
  the comparison whose behaviour on local sections is public, which is the one a computation can
  use.

## Implementation notes

Nothing here is deep, and nothing new is constructed: the proof assembles public pieces.

A morphism of complexes of sheaves of modules is an isomorphism as soon as each of its degrees
is, and a morphism of sheaves of modules is an isomorphism as soon as it is injective and
surjective on every group of sections — `Stacks.SheafOfModules.isIso_of_bijective_app`. On
sections the comparison is conjugated by the two descriptions
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsIso` of the sections of an internal Hom
complex as a complex of cochains, both isomorphisms, into a map of cochains; and the property
says that map is, on each homogeneous component, the comparison
`Stacks.SheafOfModules.InternalHom.internalHomOverIso` of Stacks 0E8H, which is an isomorphism.

The half that might have been hard is not: `CochainComplex.HomComplex.Cochain F G n` is a plain
dependent function on triplets `(p, q, p + n = q)`, with no cocycle condition, so *any* family of
components is a cochain. Surjectivity therefore needs only the componentwise inverse, with no
coherence to check, and the components themselves lift from morphisms of presheaves of modules to
morphisms of sheaves of modules for free, a morphism of sheaves of modules being a morphism of
the underlying presheaves and nothing more.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

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

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- The image of an isomorphism under a functor into a concrete category is bijective. -/
private theorem bijective_map_hom_of_iso {C D : Type*} [Category C] [Category D]
    {FD : D → D → Type*} {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] (F : C ⥤ D) {X Y : C} (e : X ≅ Y) :
    Function.Bijective (ConcreteCategory.hom (F.map e.hom)) :=
  ConcreteCategory.bijective_of_isIso _

/-- **A morphism of internal Hom complexes which restricts the internal Hom of modules in every
degree and on every local homogeneous component is an isomorphism.** The hypothesis is
`AlgebraicGeometry.RingedSite.IsInternalHomRestrictionMap`, and `B` is arbitrary: no
K-injectivity is needed.

Degreewise and on sections the comparison becomes, after the two descriptions of the sections of
an internal Hom complex as cochains, a map of cochains which on each homogeneous component is the
comparison of Stacks 0E8H, an isomorphism. Injectivity follows by reading that off componentwise;
surjectivity because a cochain is an arbitrary family of components, so the componentwise inverse
assembles into one with nothing to check. -/
theorem isIso_of_isInternalHomRestrictionMap
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : restrictComplex X (sheafHomComplex X A B).obj U ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).obj)
    (hf : IsInternalHomRestrictionMap X U A B f) :
    IsIso f := by
  have hn : ∀ n, IsIso (f.f n) := by
    intro n
    refine Stacks.SheafOfModules.isIso_of_bijective_app _ (fun V => ⟨?_, ?_⟩)
    · intro s s' hss
      have hinj₁ := (bijective_map_hom_of_iso (HomologicalComplex.eval _ _ n)
        ((sheafHomComplex X A B).sectionsIso V.unop.left)).1
      refine hinj₁ (CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq => ?_)
      refine SheafOfModules.hom_ext ?_
      have hinjH := (bijective_map_hom_of_iso (PresheafOfModules.evaluation _ V)
        (Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q))).1
      refine hinjH (((hf V n p q hpq s).symm.trans ?_))
      rw [hss]
      exact hf V n p q hpq s'
    · intro t
      have hisoH : ∀ p q : ℤ, IsIso ((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U
          (A.X p) (B.X q)).hom.app V) := fun p q =>
        ((PresheafOfModules.evaluation _ V).mapIso
          (Stacks.SheafOfModules.InternalHom.internalHomOverIso X U (A.X p) (B.X q))).isIso_hom
      have hinj₂ := (bijective_map_hom_of_iso (HomologicalComplex.eval _ _ n)
        ((sheafHomComplex (X.over U) (restrictComplex X A U)
          (restrictComplex X B U)).sectionsIso V.unop)).1
      set c' := AddCommGrpCat.Hom.hom
        (((sheafHomComplex (X.over U) (restrictComplex X A U)
          (restrictComplex X B U)).sectionsIso V.unop).hom.f n) t with hc'
      refine ⟨AddCommGrpCat.Hom.hom
        (((sheafHomComplex X A B).sectionsIso V.unop.left).inv.f n)
        (CochainComplex.HomComplex.Cochain.mk (fun p q hpq =>
          ⟨(inv ((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U
            (A.X p) (B.X q)).hom.app V)).hom ((c'.v p q hpq).val)⟩)), ?_⟩
      refine hinj₂ (CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq => ?_)
      refine SheafOfModules.hom_ext ?_
      have hinvhom : ∀ x, AddCommGrpCat.Hom.hom
          (((sheafHomComplex X A B).sectionsIso V.unop.left).hom.f n)
          (AddCommGrpCat.Hom.hom
            (((sheafHomComplex X A B).sectionsIso V.unop.left).inv.f n) x) = x := fun x =>
        congrArg (fun z => AddCommGrpCat.Hom.hom (HomologicalComplex.Hom.f z n) x)
          ((sheafHomComplex X A B).sectionsIso V.unop.left).inv_hom_id
      refine Eq.trans (hf V n p q hpq _) ?_
      refine Eq.trans (congrArg (fun z : CochainComplex.HomComplex.Cochain
          (restrictComplex X A V.unop.left) (restrictComplex X B V.unop.left) n =>
        (ModuleCat.Hom.hom
        ((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U
          (A.X p) (B.X q)).hom.app V))
            (SheafOfModules.Hom.val
              (CochainComplex.HomComplex.Cochain.v z p q hpq))) (hinvhom _)) ?_
      exact congrArg (fun z => (ModuleCat.Hom.hom z) ((c'.v p q hpq).val))
        (IsIso.inv_hom_id ((Stacks.SheafOfModules.InternalHom.internalHomOverIso X U
          (A.X p) (B.X q)).hom.app V))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The restriction comparison of internal Hom complexes is natural in the target.**
Restricting the map of internal Hom complexes induced by `g : B ⟶ B'` and then comparing is the
same as comparing and then applying the map induced by the restriction of `g`.

`sheafHomRestrictionComplexIso_natural` is this statement for the *isomorphism*, in both
variables at once; this is it for `AlgebraicGeometry.RingedSite.DerivedHomRestriction.complexMap`,
which is the comparison a computation on local sections can use, its behaviour there being public
by Stacks 08JB. The proof is that behaviour on both sides, against
`AlgebraicGeometry.RingedSite.homSection_ext`. -/
theorem complexMap_naturality_right
    (A B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (g : B ⟶ B') :
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (homMap X (𝟙 A) g) ≫
        (derivedHomRestriction X U).complexMap A B' =
      (derivedHomRestriction X U).complexMap A B ≫
        homMap (X.over U) (𝟙 (restrictComplex X A U))
          (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
               U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  obtain ⟨V⟩ := V
  ext s
  refine homSection_ext (X.over U) _ V n (fun p q hpq W i x => ?_)
  refine Eq.trans ?_ (applyHomSectionOver_homMap (X.over U) (𝟙 (restrictComplex X A U))
    (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
         U).mapHomologicalComplex (ComplexShape.up ℤ)).map g) V W i n p q hpq
    ((((derivedHomRestriction X U).complexMap A B).f n).val.app (op V) s) x).symm
  refine Eq.trans (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U) A B'
    (op V) (op (Over.mk i)) n p q hpq _ x) ?_
  refine Eq.trans (applyHomSectionOver_homMap X (𝟙 A) g (Over.left V) (Over.left W)
    (Over.Hom.left i) n p q hpq s x) ?_
  exact (congrArg (fun y => (ModuleCat.Hom.hom
      (((((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
             U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g).f q).val.app (op W))) y)
    (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U) A B
      (op V) (op (Over.mk i)) n p q hpq s _)).symm

end AlgebraicGeometry.RingedSite

end
