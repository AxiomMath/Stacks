module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent

/-!
# Sections of the direct image of fppf modules along a 1-morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `f_* : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒴)` the direct
image of **Stacks 06WE** on fppf modules at module universe `u + 1`. For an object `y` of `𝒴`,
the abelian group of sections over `y` of `f_*M` is the value at `y` of the right Kan extension
along `f` of the underlying abelian presheaf of `M`:

`Γ(y, f_*M) ≅ (Ran_f M_ab)(y)`,

naturally in `M`. This is the defining property of the direct image of presheaves of modules of
**Stacks 06WD** (`AlgebraicGeometry.Stack.ModuleFunctoriality.pushforward_iso`), read at `y`.

## Main definitions

* `AlgebraicGeometry.Stack.fppfModuleSheafPushforwardOfStacksSectionsIso`: the identification.

## References

* [Stacks Project, Tag 06WD](https://stacks.math.columbia.edu/tag/06WD)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Sections over `y` of the direct image are the value at `y` of the right Kan extension of the
underlying abelian presheaf.** -/
def fppfModuleSheafPushforwardOfStacksSectionsIso (f : 𝒳 ⟶ 𝒴) (y : 𝒴.val.val.obj) :
    fppfModuleSheafPushforwardOfStacks B S hS f ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y) ⋙ forget₂ (ModuleCat _) AddCommGrpCat.{u + 1} ≅
      SheafOfModules.toSheaf _ ⋙
        sheafToPresheaf (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf))
          AddCommGrpCat.{u + 1} ⋙
        (CatFiberedInGroupoids.homFunctor f.hom).op.ran ⋙
          (evaluation _ AddCommGrpCat.{u + 1}).obj (op y) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (SheafOfModules.forget _)
      (moduleFunctoriality.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).pushforward_iso)
    ((evaluation _ AddCommGrpCat.{u + 1}).obj (op y))

end AlgebraicGeometry.Stack

end
