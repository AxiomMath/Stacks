module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction

/-!
# [Stacks, Tag 03FD] at the universes of the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` at level `u`.  This file proves
[Stacks, Tag 03FD] for the small crystalline site `Cris(X/S)`: deriving the global sections of a
sheaf of `𝒪_{X/S}`-modules *after* forgetting it to its underlying abelian sheaf is the same as
forgetting after deriving, in every degree.

The two forms `ModuleSheafCohomology.globalSectionsComparisonIso` and
`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying` of [Stacks, Tag 03FD] do not apply
here: both carry `[SmallCategory C]` and tie the universes of the site, the structure sheaf, the
modules and the coefficients to a single `u`, whereas `Cris(X/S)` has its objects in
`Type (u + 1)`, its morphisms in `Type u`, its structure sheaf in `RingCat.{u}` and its modules
with sections in `Type (u + 1)`.  What is used instead is the general `δ`-functor construction
behind them, `ModuleSheafCohomology.comparisonIso`, which carries no smallness hypothesis,
instantiated at these universes.

## The three inputs

`ModuleSheafCohomology.comparisonIso` asks for an exact functor `F`, a left exact functor `G`
corepresented by an object `X`, a corepresentation of `F ⋙ G`, and `Ext`-acyclicity of `F` on
injectives against `X`.  Here `F` is `toAbelianSheaf S` and `G` is `globalSections S`, and the
three inputs are:

1. `Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation`, which corepresents
   `Γ(Cris(X/S), -)` on abelian sheaves by the constant sheaf on `ULift ℤ` with the universe of
   the objects of the site free of the universe of its morphisms;
2. `Stacks.SheafOfModules.tensorSheafHomIso`, which corepresents the composite by
   `abelianCorepresentingModule`, the sheafified extension of scalars `𝒪_{X/S} ⊗_ℤ ℤ` — this is
   where the structure sheaf being one universe below the modules matters, and it is why the
   extension of scalars has to be the one with the two universes independent;
3. `Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`, the acyclicity, which applies because
   the constant presheaf on `ULift ℤ` is sectionwise torsion free.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `abelianCorepresentingSheaf` — the constant abelian sheaf on `ULift ℤ`, which corepresents
  `Γ(Cris(X/S), -)`.
* `abelianCorepresentingModule` — the sheaf of `𝒪_{X/S}`-modules `𝒪_{X/S} ⊗_ℤ ℤ` corepresenting
  the global sections of the underlying abelian sheaf.

## Main results

* `ext_eq_zero_of_injective_toAbelianSheaf` — the acyclicity of `toAbelianSheaf` on injectives
  against `abelianCorepresentingSheaf`.
* `abelianComparisonIso` — **[Stacks, Tag 03FD] at the small crystalline site**: the comparison
  `(toAbelianSheaf S ⋙ Γ).rightDerived n ≅ toAbelianSheaf S ⋙ Γ.rightDerived n`, in every
  degree, together with `toRightDerivedZero_comp_abelianComparisonIso`, its degree-zero
  normalization.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The corepresenting objects -/

/-- The constant abelian presheaf on `ULift ℤ` on the small crystalline site.  Its sheafification
corepresents `Γ(Cris(X/S), -)`, and its extension of scalars corepresents the global sections of
the underlying abelian sheaf of a module. -/
abbrev constantIntegerPresheaf : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const (CrystallineThickening S)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **The abelian sheaf corepresenting `Γ(Cris(X/S), -)`**: the constant sheaf on `ULift ℤ`, at
the coefficient universe `u + 1` of the chapter's abelian-valued cohomology. -/
abbrev abelianCorepresentingSheaf : Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (constantSheaf (smallTopology S) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **`Γ(Cris(X/S), -)` is corepresented by the constant abelian sheaf on `ℤ`.**  This is
`Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation`, whose statement leaves the
universe of the objects of the site free of the universe of its morphisms — which is what the
small crystalline site needs, its objects forming a `Type (u + 1)` and its morphisms a
`Type u`. -/
def globalSectionsCorepresentation :
    globalSections S ≅ preadditiveCoyoneda.obj (op (abelianCorepresentingSheaf S)) :=
  Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{u + 1, u, u + 1}
    (smallTopology S)

/-- **The sheaf of `𝒪_{X/S}`-modules corepresenting the global sections of the underlying abelian
sheaf**: the sheafification of the extension of scalars `𝒪_{X/S} ⊗_ℤ ℤ` of the constant abelian
presheaf on `ULift ℤ`.

The extension of scalars is `Stacks.SheafOfModules.tensorPresheaf`, whose ring universe and
coefficient universe are independent: here the structure sheaf is valued in `RingCat.{u}` while
the coefficients lie in `AddCommGrpCat.{u + 1}`, and the resulting presheaf of modules has
sections in `Type (u + 1)`, which is the module universe of `ModuleSheaf S`. -/
abbrev abelianCorepresentingModule : ModuleSheaf S :=
  (PresheafOfModules.sheafification (𝟙 (structureSheaf S).obj)).obj
    (Stacks.SheafOfModules.tensorPresheaf.{u + 1, u, u + 1, u} (structureSheaf S).obj
      (constantIntegerPresheaf S))

/-- **The global sections of the underlying abelian sheaf of a module are corepresented by
`abelianCorepresentingModule`.**  This is `Stacks.SheafOfModules.tensorSheafHomIso` at the
universes of the small crystalline site, composed with the corepresentation of
`Γ(Cris(X/S), -)`. -/
def moduleCorepresentation :
    preadditiveCoyoneda.obj (op (abelianCorepresentingModule S)) ≅
      toAbelianSheaf S ⋙ preadditiveCoyoneda.obj (op (abelianCorepresentingSheaf S)) :=
  Stacks.SheafOfModules.tensorSheafHomIso.{u + 1, u, u, u + 1} (smallTopology S)
    (structureSheaf S) (constantIntegerPresheaf S)

/-! ### The acyclicity -/

/-- The constant abelian presheaf on `ULift ℤ` is sectionwise torsion free: `ℤ` is flat over
itself, and `ULift` does not change that. -/
theorem isTorsionFree_constantIntegerPresheaf (A : (CrystallineThickening S)ᵒᵖ) :
    Module.IsTorsionFree ℤ ((constantIntegerPresheaf S).obj A) :=
  (Module.Flat.isTorsionFree : Module.IsTorsionFree ℤ (ULift.{u + 1} ℤ))

/-- **The acyclicity input of [Stacks, Tag 03FD] at the small crystalline site**: the underlying
abelian sheaf of an injective sheaf of `𝒪_{X/S}`-modules has vanishing positive-degree `Ext`
against the constant sheaf on `ℤ`.

The underlying abelian sheaf of an injective module is not injective; what holds is acyclicity
against sheafifications of sectionwise torsion-free presheaves, which is
`Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`, and the constant presheaf on `ULift ℤ` is
one of those. -/
theorem ext_eq_zero_of_injective_toAbelianSheaf (M : ModuleSheaf S) [Injective M] (n : ℕ)
    (e : Ext.{u + 1} (abelianCorepresentingSheaf S) ((toAbelianSheaf S).obj M) (n + 1)) :
    e = 0 :=
  Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{u + 1, u + 1, u, u, u + 1}
    (smallTopology S) (structureSheaf S) M _
    (ModuleSheafCohomology.isTorsionFree_sheafify (smallTopology S)
      (constantIntegerPresheaf S) (isTorsionFree_constantIntegerPresheaf S)) n e

/-! ### The comparison -/

/-- **[Stacks, Tag 03FD] at the small crystalline site.**  Deriving the composite of forgetting a
sheaf of `𝒪_{X/S}`-modules to its underlying abelian sheaf with `Γ(Cris(X/S), -)` agrees, in
every degree, with forgetting and then deriving `Γ(Cris(X/S), -)`.

This is `ModuleSheafCohomology.comparisonIso`, the general `δ`-functor comparison, instantiated
at the universes of the small crystalline site; the three inputs it asks for are
`globalSectionsCorepresentation`, `moduleCorepresentation` and
`ext_eq_zero_of_injective_toAbelianSheaf`.  It is a named isomorphism, not a choice: it is the
degreewise component of an isomorphism of `δ`-functors normalized in degree zero. -/
def abelianComparisonIso (n : ℕ) :
    (toAbelianSheaf S ⋙ globalSections S).rightDerived n ≅
      toAbelianSheaf S ⋙ (globalSections S).rightDerived n :=
  ModuleSheafCohomology.comparisonIso (toAbelianSheaf S) (globalSections S)
    (abelianCorepresentingSheaf S) (globalSectionsCorepresentation S)
    (abelianCorepresentingModule S) (moduleCorepresentation S)
    (fun M _ n e => ext_eq_zero_of_injective_toAbelianSheaf S M n e) n

/-- **The degree-zero normalization of the comparison.**  It intertwines the two canonical maps
to the zeroth right-derived functors, which is what makes the comparison the one extending the
identity in degree zero rather than an arbitrary isomorphism. -/
theorem toRightDerivedZero_comp_abelianComparisonIso :
    (toAbelianSheaf S ⋙ globalSections S).toRightDerivedZero ≫
        (abelianComparisonIso S 0).hom =
      Functor.whiskerLeft (toAbelianSheaf S) (globalSections S).toRightDerivedZero :=
  ModuleSheafCohomology.toRightDerivedZero_comp_comparisonIso _ _ _ _ _ _ _

end Crystalline.GlobalCrystallineSituation.SmallSite

end
