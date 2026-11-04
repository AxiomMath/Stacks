module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of lower shriek of modules from a simplicial component

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
Lower shriek `g_{n!} : Mod(O_n) ⥤ Mod(O)` of sheaves of modules from the degree-`n` component is
exact as soon as the structure-sheaf transitions `f_φ⁻¹O_n ⟶ O_m` out of degree `n` are flat.
Restriction `g_n^*` to that component, being right adjoint to an exact functor, then carries
injective sheaves of `O`-modules to injective sheaves of `O_n`-modules.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`: the pullback
  `f_φ^* : Mod(O_n) ⥤ Mod(O_m)` of sheaves of modules along the transition morphism of ringed
  topoi of a simplex map `φ : [n] ⟶ [m]`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_of_componentModuleRestriction`:
  a functor into sheaves of modules on the total site is left exact as soon as its composite
  with restriction to every simplicial degree is.
* `CategoryTheory.SimplicialSiteSituation.preservesFiniteColimits_componentModuleLowerShriek`:
  `g_{n!}` is right exact, being a left adjoint.
* `CategoryTheory.SimplicialSiteSituation.exactFunctor_transitionPullbackModules`: pullback of
  sheaves of modules along the transition morphism of a simplex map is exact when that morphism
  is flat.
* `CategoryTheory.SimplicialSiteSituation.exactFunctor_componentModuleLowerShriek`: exactness of
  `g_{n!}` under flatness of the transitions out of degree `n`, granted the componentwise
  direct-sum formula for `g_{n!}`.
* `CategoryTheory.SimplicialSiteSituation.preservesInjectiveObjects_componentModuleRestriction`:
  restriction of sheaves of modules to the degree-`n` component preserves injective objects
  under the same hypotheses.
* `CategoryTheory.SimplicialSiteSituation.injective_componentModuleRestriction`:
  **Stacks 0D75**, an injective sheaf of `O`-modules on the total site restricts to an injective
  sheaf of `O_n`-modules on the degree-`n` component.

## Implementation notes

The reduction is the one the source performs. Every object of the total category lies in a
component, so left exactness of a functor into sheaves of modules on the total site is decided by
the restrictions to the components; by the direct-sum formula the restriction of `g_{n!}` to
degree `m` is the sum over the finitely many simplex maps `[n] ⟶ [m]` of the transition
pullbacks, so a finite *product* of them; and a functor exhibited as a product of functors
preserving limits of a shape preserves limits of that shape. Right exactness is formal.

The detection step is the module-coefficient counterpart of
`CategoryTheory.SimplicialSiteSituation.preservesLimitsOfShape_of_componentRestriction`, and it
is deduced from it rather than reproved: restriction of sheaves of modules to a component is, on
underlying sheaves of abelian groups, restriction of abelian sheaves on the nose, and the
underlying-abelian-sheaf functor of `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` preserves
finite limits and reflects isomorphisms, hence reflects them.

Flatness is `AlgebraicGeometry.RingedToposHom.IsFlat` of the transition morphism of ringed topoi,
which is flatness of its inverse-image structure map `f_φ⁻¹O_n ⟶ O_m`, the form the source uses.
Exactness of the transition pullback is Stacks 04JC and is not reproved.

`transitionPullbackModules` is the pullback of the four-field morphism of ringed topoi obtained
by `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, which is the reading the library's
Stacks 04JC is stated for. The development also carries a second reading of a morphism of ringed
topoi as that four-field datum, `AlgebraicGeometry.RingedToposHom.toModulesHom`, whose
inverse-image structure map is the adjunct of the same direct-image structure map and therefore
differs from this one by an application of the adjunction bijection to its own inverse; the two
pullbacks agree, but not by `rfl`.

The injectivity statement is the Homology 015Z step applied to the adjunction `g_{n!} ⊣ g_n^*`,
in the form `preservesInjectiveObjects_of_isExact`. That form asks both adjoints to be additive.
Restriction is additive because it reindexes components and restricts scalars along the identity,
neither of which changes the underlying additive maps; this is
`SheafOfModules.instAdditivePushforward`, stated again locally below because
`componentModuleRestriction` is a `def`, which instance search does not unfold. Lower shriek is
then additive as the left adjoint of an additive functor.

Giving the transition pullback a name is not cosmetic. Its own type spells the two module
categories over the structure sheaves of the component ringed topoi, whereas lower shriek spells
them over the restrictions of the total sheaf of rings; the two are equal, but instance search
matches syntactically, so a direct sum of the unnamed functors sends it looking for the limits
and colimits of a category it does not recognise. The definition above ascribes the second
spelling once, and every later product and biproduct instance is then found immediately.

Coefficients sit at the universe of the situation, because that is where
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriek` is constructed: at a
coefficient universe independent of the site universe the total site has no sheafification of
abelian sheaves available from the data of a situation, so the left adjoint has no input. See the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriek.lean`.

## The direct-sum formula

The componentwise direct-sum formula

`g_m^*(g_{n!}G) = ⨁_{φ : [n] ⟶ [m]} f_φ^*G`

of Tag 0D72 is stated here as the types `ModuleSumFormula` and `ModuleSumFormula'`, and proved,
for an arbitrary situation, as `CategoryTheory.SimplicialSiteSituation.moduleSumFormula` in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaSituation.lean`,
which builds on this file. Stacks 0D74 and Stacks 0D75 are proved from it there and restated in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriekExact.lean`.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
* [Stacks Project, Tag 0D75](https://stacks.math.columbia.edu/tag/0D75)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe v₂ u₂ u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

section Detection

variable (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)

/-- A functor into sheaves of `O`-modules on the total site preserves finite limits as soon as
its composite with restriction to each simplicial degree does: every object of the total category
lies in a component, and the underlying-abelian-sheaf functor reflects finite limits. -/
lemma preservesFiniteLimits_of_forall_componentModuleRestriction {B : Type u₂} [Category.{v₂} B]
    (H : B ⥤ SheafOfModules.{u} O)
    (h : ∀ m : SimplexCategory,
      PreservesFiniteLimits (H ⋙ S.componentModuleRestriction O m)) :
    PreservesFiniteLimits H := by
  have key : PreservesFiniteLimits (H ⋙ SheafOfModules.toSheaf.{u} O) := by
    constructor
    intro K _ _
    refine S.preservesLimitsOfShape_of_componentRestriction K _ fun m => ?_
    have h1 : PreservesLimitsOfShape K (H ⋙ S.componentModuleRestriction O m) :=
      (h m).preservesFiniteLimits K
    have h2 : PreservesLimitsOfShape K
        (SheafOfModules.toSheaf.{u} (S.componentRingSheaf O m)) := by
      have hfin : PreservesFiniteLimits
        (SheafOfModules.toSheaf.{u} (S.componentRingSheaf O m)) := inferInstance
      exact hfin.preservesFiniteLimits K
    exact comp_preservesLimitsOfShape (H ⋙ S.componentModuleRestriction O m)
      (SheafOfModules.toSheaf.{u} (S.componentRingSheaf O m))
  exact preservesFiniteLimits_of_reflects_of_preserves H (SheafOfModules.toSheaf.{u} O)

/-- Lower shriek of modules from a simplicial component is right exact: it is a left adjoint. -/
instance componentModuleLowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits (S.componentModuleLowerShriek O n) :=
  letI : PreservesColimitsOfSize.{u, u} (S.componentModuleLowerShriek O n) :=
    (S.componentModuleLowerShriekAdjunction O n).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

end Detection

variable (P : Sheaf S.totalTopology CommRingCat.{u})

-- Sheafifiability of abelian sheaves on a component, which is what makes the direct sum of
-- sheaves of modules on a component available.
attribute [local instance] hasWeakSheafifyComponent

/-- Pullback of sheaves of modules along the transition morphism of ringed topoi of a simplex
map `φ : [n] ⟶ [m]`: the functor `f_φ^* : Mod(O_n) ⥤ Mod(O_m)` between the module categories of
the two simplicial components. -/
def transitionRingedToposModulesPullback {n m : SimplexCategory} (φ : n ⟶ m) :
    SheafOfModules.{u} (S.componentRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf P) n) ⥤
      SheafOfModules.{u} (S.componentRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf P) m) :=
  (S.transitionRingedToposHom P φ).toRingedToposModulesHom.pullbackModules

/-- `transitionRingedToposModulesPullback` read through `AlgebraicGeometry.RingedToposHom.toModulesHom`
rather than `toRingedToposModulesHom`: the spelling in which the module transitions of Stacks
09WF (`CategoryTheory.SimplicialSiteSituation.componentModuleTransition`) are stated, so that
the direct-sum formula of Stacks 0D72 can be compared with them definitionally. The two readings
are equal, by `AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`. -/
def transitionPullbackModules' {n m : SimplexCategory} (φ : n ⟶ m) :
    SheafOfModules.{u} (S.componentRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf P) n) ⥤
      SheafOfModules.{u} (S.componentRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf P) m) :=
  (S.transitionRingedToposHom P φ).toModulesHom.pullbackModules

/-- **Stacks 04JC for a simplicial transition**, at the `toModulesHom` reading of the
transition pullback. -/
theorem exactFunctor_transitionPullbackModules' {n m : SimplexCategory} (φ : n ⟶ m)
    (hφ : (S.transitionRingedToposHom P φ).IsFlat) :
    exactFunctor
      (SheafOfModules.{u} (S.componentRingSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) P) n))
      (SheafOfModules.{u} (S.componentRingSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) P) m))
      (S.transitionPullbackModules' P φ) := by
  unfold transitionPullbackModules'
  rw [(S.transitionRingedToposHom P φ).toModulesHom_eq_toRingedToposModulesHom]
  exact pullbackModules_exact_of_isFlatMap (S.transitionRingedToposHom P φ) hφ

variable (n : SimplexCategory)

/-- Restriction of sheaves of modules to a simplicial component is additive: it reindexes
components and restricts scalars along the identity, neither of which changes the underlying
additive maps. -/
local instance additive_componentModuleRestriction_ringSheaf (m : SimplexCategory) :
    (S.componentModuleRestriction ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) P) m).Additive where
  map_add := rfl

/-- The componentwise direct-sum formula of Stacks 0D72 (6): the summand at `φ` is the pullback
along the transition morphism of ringed topoi. -/
def ModuleSumFormula (n : SimplexCategory) : Type _ :=
  ∀ m : SimplexCategory,
    S.componentModuleLowerShriek
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) n ⋙
        S.componentModuleRestriction
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) m ≅
      ∐ fun φ : n ⟶ m => S.transitionRingedToposModulesPullback P φ

/-- The componentwise direct-sum formula of Stacks 0D72 (6), with the transition pullback taken
via `toModulesHom`: the summand at `φ` is the pullback along the transition morphism of ringed
topoi. -/
def ModuleSumFormula' (n : SimplexCategory) : Type _ :=
  ∀ m : SimplexCategory,
    S.componentModuleLowerShriek
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) n ⋙
        S.componentModuleRestriction
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) m ≅
      ∐ fun φ : n ⟶ m => S.transitionPullbackModules' P φ

end CategoryTheory.SimplicialSiteSituation

end
