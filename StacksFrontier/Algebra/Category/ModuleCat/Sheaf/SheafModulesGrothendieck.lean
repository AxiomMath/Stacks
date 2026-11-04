module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksCore.Tactic.StacksAttribute

/-!
# Graded modules over a sheaf of graded algebras form a Grothendieck abelian category

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of `ℤ`-graded
`R`-algebras. [Stacks, Tag 0FRD](https://stacks.math.columbia.edu/tag/0FRD) says that the
category `Mod(A)` of right graded `A`-modules is a Grothendieck abelian category.

Mathlib's `CategoryTheory.IsGrothendieckAbelian.{s} C` for an abelian `C` asks for four things:
that `C` be locally small relative to `s`, that it have filtered colimits of size `s`, that
those be exact (AB5), and that it have a separator. The abelian structure and the filtered
colimits are Tag 0FR0 and are already available from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`; what this file adds is
AB5 and the separator, and then assembles the four.

The separator is the content of the tag: Stacks exhibits
`⨁_{k, U} j_{U!} A_U[k]` and computes
`Hom(j_{U!} A_U[k], M) = Γ(U, M^k)`, so a graded module admitting no nonzero map from the sum
has no nonzero homogeneous local section at all. The objects `j_{U!} A_U[k]` and that
corepresentation formula are
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtensionByZero.lean`; here they are assembled
into a single separating object.

## Main definitions

* `SheafOfModules.GradedModule.pieceFunctors A` takes a graded module to the whole family of its
  homogeneous components, as a functor into `Discrete ℤ ⥤ SheafOfModules R`, and
  `SheafOfModules.GradedModule.pieceFunctorsCompEval` identifies its composite with evaluation
  at `n` with `GradedModule.pieceFunctor A n`.
* `SheafOfModules.GradedModule.separatorFamily A` is the family `j_{U!} A_U[k]` indexed by pairs
  `(U, k)`, whose coproduct is the separator.

## Main results

* `SheafOfModules.sheafOfModules_hasExactColimitsOfShape`: filtered colimits of sheaves of
  modules are exact, at a module universe independent of the site. Mathlib has this only when
  the module universe, the ring universe and the (small) site universe all coincide.
* `SheafOfModules.GradedModule.gradedModule_hasExactColimitsOfShape` and
  `SheafOfModules.GradedModule.gradedModule_ab5`: **AB5 for graded modules**.
* `SheafOfModules.GradedModule.isSeparating_separatorFamily` and
  `SheafOfModules.GradedModule.hasSeparator`: **the separator**.
* `SheafOfModules.GradedModule.isGrothendieckAbelian` is **Tag 0FRD**.

## Implementation notes

**AB5 is proved degreewise, and the route is the dual of the one already used for colimits.**
Exactness of filtered colimits means that `colim` preserves finite limits. Both kinds of limit
in `Mod(A)` are computed degreewise, so the single functor `pieceFunctors A` into the functor
category `Discrete ℤ ⥤ SheafOfModules R` preserves finite limits and filtered colimits, and
reflects finite limits — it reflects isomorphisms by `GradedModule.isIso_of_componentwise`, and
a functor which reflects isomorphisms and preserves finite limits out of a category which has
them reflects them. `HasExactColimitsOfShape.domain_of_functor` then transports AB5 from the
functor category, where it holds pointwise. That each `pieceFunctor A n` preserves *finite
limits* is `Functor.preservesFiniteLimits_of_preservesKernels` applied to the degreewise kernels
of Tag 0FR0 — the exact dual of the `preservesCoequalizers_of_preservesCokernels` step already
used in `GradedDegreeColimits`.

**AB5 for sheaves of modules.** The functor-category step needs filtered colimits of
`SheafOfModules.{s} R` to be exact. Mathlib proves this (`SheafOfModules.instIsGrothendieck…`)
only for a `SmallCategory` site `C : Type s` and `R : Sheaf J RingCat.{s}`, i.e. with the
module universe equal to the site and ring universes, which the universes here are not. The
argument is universe-generic, and it is redone here in that generality: presheaves of modules
inherit exactness of filtered colimits from `Cᵒᵖ ⥤ AddCommGrpCat`, where colimits are pointwise
and `AddCommGrpCat` has AB5, and `Adjunction.hasExactColimitsOfShape` carries it across the
sheafification adjunction, which is left exact.

**Universes.** The statement of Tag 0FRD below is at module universe `max u v a w`, for a site
`C : Type u` with `Category.{v} C` and algebra pieces in `SheafOfModules.{a} R`; `w` is free.
Three of the four conditions force this shape and none of it is a choice:
`LocallySmall.{s}` needs the hom types of `Mod(A)` — which are indexed by the objects of `C`
and valued in the module universe — to be `s`-small, so `u ≤ s` and `v ≤ s`; a direct sum
indexed by a type in `Type s` exists only for `s` the module universe, and the separator is
indexed by pairs `(U, k)` with `U` an object of `C`, so again `u ≤ s`; and the free graded
module on a sheaf of graded sets with values in `Type s` has pieces in `Type (max s a)`, so
`a ≤ s`. Nothing is narrowed: `RingedSite.{u, u, u}` with module universe
`max u v w` is the instance `v := u`, `t := u`, `a := v`, and `AB5` and the separator are stated
and proved before that instantiation, AB5 with the module universe entirely free.

**Why the separator is a coproduct of objects and not an assumption.** `HasSeparator` is the
one field of `IsGrothendieckAbelian` with mathematical content here, and it is what Tag 0FRD's
proof is. It is obtained from `ObjectProperty.IsSeparating.isSeparator_coproduct` applied to the
family `separatorFamily`, so the separating object really is `⨁_{k, U} j_{U!} A_U[k]` and the
tag's proof is the proof below.

## References

* [Stacks Project, Tag 0FRD](https://stacks.math.columbia.edu/tag/0FRD)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe m w a t v u

namespace SheafOfModules

/-! ### Exactness of filtered colimits of sheaves of modules -/

section AB5Sheaves

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Filtered colimits of presheaves of modules are exact**, at a module universe independent
of the site: a colimit of presheaves of modules is computed in presheaves of abelian groups,
where filtered colimits are pointwise and `AddCommGrpCat` satisfies AB5. -/
noncomputable instance presheafOfModules_hasExactColimitsOfShape
    (K : Type m) [SmallCategory K] [IsFiltered K] :
    HasExactColimitsOfShape K (PresheafOfModules.{m} R.obj) where
  preservesFiniteLimits := ⟨fun _ _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := K) ⋙ PresheafOfModules.toPresheaf R.obj) :=
      preservesLimit_of_natIso _
        (preservesColimitNatIso (PresheafOfModules.toPresheaf R.obj)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R.obj)⟩⟩

/-- **Filtered colimits of sheaves of modules are exact**, at a module universe independent of
the site: sheafification is a left exact left adjoint, so it carries the exactness of filtered
colimits of presheaves of modules over to sheaves. -/
noncomputable instance sheafOfModules_hasExactColimitsOfShape
    (K : Type m) [SmallCategory K] [IsFiltered K] :
    HasExactColimitsOfShape K (SheafOfModules.{m} R) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

end AB5Sheaves

namespace GradedModule

/-! ### The family of all homogeneous components, and AB5 -/

section AB5

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- All the homogeneous components of a graded module at once, as a functor into the category of
`ℤ`-indexed families of sheaves of modules. -/
@[simps, sga "6 VI 2.7" "partial"]
noncomputable def pieceFunctors (A : GradedAlgebra.{t, a} R) :
    GradedModule.{t, a, m} A ⥤ Discrete ℤ ⥤ SheafOfModules.{m} R where
  obj M := Discrete.functor M.piece
  map f := Discrete.natTrans fun n ↦ f.app n.as
  map_id _ := by ext ⟨n⟩; rfl
  map_comp _ _ := by ext ⟨n⟩; rfl

/-- Evaluating the family of all homogeneous components at `n` is taking the degree-`n`
component. -/
noncomputable def pieceFunctorsCompEval (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    pieceFunctors.{m} A ⋙
        (CategoryTheory.evaluation (Discrete ℤ) (SheafOfModules.{m} R)).obj (Discrete.mk n) ≅
      pieceFunctor.{t, a, m} A n :=
  Iso.refl _

/-- Taking a fixed homogeneous component preserves finite limits: it preserves kernels, and a
functor between preadditive categories which preserves kernels preserves all finite limits. -/
instance pieceFunctor_preservesFiniteLimits (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    PreservesFiniteLimits (pieceFunctor.{t, a, m} A n) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

instance pieceFunctors_preservesFiniteLimits (A : GradedAlgebra.{t, a} R) :
    PreservesFiniteLimits (pieceFunctors.{m} A) where
  preservesFiniteLimits I _ _ :=
    preservesLimitsOfShape_of_evaluation _ I fun n ↦
      preservesLimitsOfShape_of_natIso (pieceFunctorsCompEval.{m} A n.as).symm

/-- The family of all homogeneous components reflects isomorphisms: a homomorphism of graded
modules which is an isomorphism in every degree is an isomorphism. -/
instance pieceFunctors_reflectsIsomorphisms (A : GradedAlgebra.{t, a} R) :
    (pieceFunctors.{m} A).ReflectsIsomorphisms where
  reflects f _ := isIso_of_componentwise f fun n ↦
    inferInstanceAs (IsIso (((pieceFunctors.{m} A).map f).app (Discrete.mk n)))

/-- **Filtered colimits of graded modules are exact.** Both filtered colimits and finite limits
of graded modules are computed degreewise, so the statement is transported from the category of
`ℤ`-indexed families of sheaves of modules, where it holds pointwise. -/
noncomputable instance gradedModule_hasExactColimitsOfShape (A : GradedAlgebra.{t, a} R)
    (K : Type m) [SmallCategory K] [IsFiltered K] :
    HasExactColimitsOfShape K (GradedModule.{t, a, m} A) :=
  haveI : PreservesColimitsOfShape K (pieceFunctors.{m} A) :=
    preservesColimitsOfShape_of_evaluation _ K fun n ↦
      haveI : PreservesColimitsOfShape K (pieceFunctor.{t, a, m} A n.as) :=
        (pieceFunctor_preservesColimitsOfSize' (A := A) n.as).preservesColimitsOfShape
      preservesColimitsOfShape_of_natIso (pieceFunctorsCompEval.{m} A n.as).symm
  HasExactColimitsOfShape.domain_of_functor K (pieceFunctors.{m} A)

/-- **Graded modules over a sheaf of graded algebras satisfy AB5**, at a module universe
independent of the site. -/
noncomputable instance gradedModule_ab5 (A : GradedAlgebra.{t, a} R) :
    AB5OfSize.{m, m} (GradedModule.{t, a, m} A) where
  ofShape _ _ _ := inferInstance

end AB5

/-! ### The separator, and Tag 0FRD -/

section Separator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasWeakSheafify J (Type max u v a w)]
  [HasSheafify J AddCommGrpCat.{max u v a w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v a w}]

/-- Stacks' separating family `j_{U!} A_U[k]`, indexed by pairs of an object `U` of the site and
an integer `k`. -/
noncomputable def separatorFamily (A : GradedAlgebra.{t, a} R) :
    ULift.{max v a w, u} (C × ℤ) → GradedModule.{t, a, max u v a w} A :=
  fun b ↦ extByZero.{w} A b.down.1 b.down.2

/-- **The family `j_{U!} A_U[k]` is separating.** -/
theorem isSeparating_separatorFamily (A : GradedAlgebra.{t, a} R) :
    ObjectProperty.IsSeparating (.ofObj (separatorFamily.{w} A)) := by
  intro M N f g h
  exact gradedModule_hom_ext_of_extByZero A fun U k φ ↦
    h _ (ObjectProperty.ofObj_apply _ (ULift.up (U, k))) φ

/-- **Graded modules over a sheaf of graded algebras have a separator**, namely the direct sum
`⨁_{k, U} j_{U!} A_U[k]`. This is the content of Tag 0FRD. -/
noncomputable instance hasSeparator (A : GradedAlgebra.{t, a} R) :
    HasSeparator (GradedModule.{t, a, max u v a w} A) :=
  ⟨_, (isSeparating_separatorFamily.{w} A).isSeparator_coproduct⟩

/-- **The category of right graded modules over a sheaf of graded algebras on a site is a
Grothendieck abelian category.**

It is abelian and has filtered colimits by Tag 0FR0, those colimits are exact by
`gradedModule_ab5`, it is locally small, and it has the separator
`⨁_{k, U} j_{U!} A_U[k]`. -/
@[stacks 0FRD]
noncomputable instance isGrothendieckAbelian (A : GradedAlgebra.{t, a} R) :
    IsGrothendieckAbelian.{max u v a w} (GradedModule.{t, a, max u v a w} A) where

end Separator

end GradedModule

end SheafOfModules
