module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaTransitionA
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaTransitionB

/-!
# The componentwise direct sum for modules, in either case of the situation

Let `S` be a simplicial-site situation (Stacks 09WE) and `P` a sheaf of commutative rings on its
total site. The componentwise direct-sum formula of Stacks 0D72 (6) for sheaves of modules,

`g_m^*(g_{n!}G) = ⨁_{φ : [n] ⟶ [m]} f_φ^*G`

in the summand spelling Stacks 0D74 and Stacks 0D75 consume — the pullback along the transition
morphism of ringed topoi — is available in each of the two cases of the situation separately:
`CategoryTheory.SimplicialSite.moduleSumFormulaA` in case (A) and
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaB` in case (B). A situation *is* one of
the two cases, so a case split produces it for an arbitrary situation, and Stacks 0D74 and
Stacks 0D75 then hold with no hypothesis beyond flatness of the transitions out of degree `n`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.moduleSumFormula`: **the componentwise direct-sum
  formula of Stacks 0D72 (6) for sheaves of modules, for an arbitrary simplicial-site
  situation.**

## Main results

* `CategoryTheory.SimplicialSiteSituation.exactFunctor_componentModuleLowerShriek'`:
  **Stacks 0D74.** Lower shriek `g_{n!}` of sheaves of modules from the degree-`n` simplicial
  component is exact as soon as every structure-sheaf transition `f_φ⁻¹O_n ⟶ O_m` out of degree
  `n` is flat.
* `CategoryTheory.SimplicialSiteSituation.preservesInjectiveObjects_componentModuleRestriction'`:
  restriction of sheaves of modules to the degree-`n` component preserves injective objects
  under the same hypothesis.
* `CategoryTheory.SimplicialSiteSituation.injective_componentModuleRestriction'`:
  **Stacks 0D75.** An injective sheaf of `O`-modules on the total site restricts to an injective
  sheaf of `O_n`-modules on the degree-`n` simplicial component.

## Implementation notes

The reduction is the one the source performs, and it is carried out here rather than upstream
because it is the step that consumes the formula. Every object of the total category lies in a
component, so left exactness of a functor into sheaves of modules on the total site is decided by
the restrictions to the components
(`CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_of_forall_componentModuleRestriction`);
by the formula the restriction of `g_{n!}` to degree `m` is the sum over the finitely many simplex
maps `[n] ⟶ [m]` of the transition pullbacks, so a finite *product* of them; and a functor
exhibited as a product of functors preserving limits of a shape preserves limits of that shape.
Right exactness is formal, `g_{n!}` being a left adjoint. Exactness of a transition pullback is
Stacks 04JC, as `…exactFunctor_transitionPullbackModules'`.

The injectivity statement is the Homology 015Z step applied to the adjunction `g_{n!} ⊣ g_n^*`,
in the form `preservesInjectiveObjects_of_isExact`. That form asks both adjoints to be additive.
Restriction is additive because it reindexes components and restricts scalars along the identity,
neither of which changes the underlying additive maps; this is
`SheafOfModules.instAdditivePushforward`, stated again locally below because
`componentModuleRestriction` is a `def`, which instance search does not unfold. Lower shriek is
then additive as the left adjoint of an additive functor.

The case split is written as a `match` on the situation taken before the sheaf of rings, whose
type depends on it. In each branch the situation is literally `⟨Sum.inl C⟩` or `⟨Sum.inr C⟩`,
which is what `CategoryTheory.SimplicialSite.situation` and
`CategoryTheory.CocontinuousSimplicialSite.situation` abbreviate, so each case's formula applies
on the nose.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
* [Stacks Project, Tag 0D75](https://stacks.math.columbia.edu/tag/0D75)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

-- Sheafifiability of abelian sheaves on a component, which is what makes the direct sum of
-- sheaves of modules on a component available.
attribute [local instance] hasWeakSheafifyComponent

/-- **The componentwise direct-sum formula of Stacks 0D72 (6) for sheaves of modules**, for an
arbitrary simplicial-site situation and in the summand spelling Stacks 0D74 consumes: the
restriction to degree `m` of lower shriek from degree `n` is the direct sum, over the simplex maps
`φ : [n] ⟶ [m]`, of the pullbacks of sheaves of modules along the transition morphisms of ringed
topoi.

A situation is one of the two cases of Stacks 09WE, and the formula is proved in each:
`CategoryTheory.SimplicialSite.moduleSumFormulaA` in case (A), where the transitions are
morphisms of sites, and `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaB` in case
(B), where they are cocontinuous functors. -/
@[stacks 0D72 "direct-sum formula on sheaves of modules, in Situation 09WE (both cases)"]
def moduleSumFormula : ∀ (S : SimplicialSiteSituation.{u})
    (P : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory), S.ModuleSumFormula' P n
  | ⟨Sum.inl C⟩, P, n => SimplicialSite.moduleSumFormulaA C P n
  | ⟨Sum.inr C⟩, P, n => CocontinuousSimplicialSite.moduleSumFormulaB C P n

variable (S : SimplicialSiteSituation.{u}) (P : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **Stacks 0D74.** Lower shriek `g_{n!}` of sheaves of modules from the degree-`n` simplicial
component is exact as soon as every structure-sheaf transition `f_φ⁻¹O_n ⟶ O_m` out of degree `n`
is flat.

Right exactness is formal. For left exactness: the restrictions to the components detect finite
limits, the componentwise direct-sum formula of Stacks 0D72 presents the restriction of `g_{n!}`
to degree `m` as the direct sum over the finitely many simplex maps `[n] ⟶ [m]` of the transition
pullbacks, hence as their product, and each of those is left exact by Stacks 04JC. -/
@[stacks 0D74]
theorem exactFunctor_componentModuleLowerShriek'
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom P φ).IsFlat) :
    exactFunctor
      (SheafOfModules.{u} (S.componentRingSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) n))
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)))
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) n) := by
  refine (exactFunctor_iff _).2 ⟨?_, inferInstance⟩
  refine S.preservesFiniteLimits_of_forall_componentModuleRestriction _ _ fun m => ?_
  constructor
  intro K _ _
  have hsum : ∀ φ : n ⟶ m, PreservesLimitsOfShape K (S.transitionPullbackModules' P φ) :=
    fun φ => ((exactFunctor_iff _).1
      (S.exactFunctor_transitionPullbackModules' P φ (hflat m φ))).1.preservesFiniteLimits K
  have : HasFiniteBiproducts
      (SheafOfModules.{u} (S.componentRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P) n) ⥤
        SheafOfModules.{u} (S.componentRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P) m)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let e := S.moduleSumFormula P n m ≪≫
    (biproduct.isoCoproduct fun φ : n ⟶ m => S.transitionPullbackModules' P φ).symm ≪≫
    biproduct.isoProduct fun φ : n ⟶ m => S.transitionPullbackModules' P φ
  refine preservesLimitsOfShape_of_isLimitFan (fun φ => e.hom ≫ Pi.π _ φ) ?_
  refine IsLimit.ofIsoLimit (productIsProduct _) (Cone.ext e.symm ?_)
  rintro ⟨φ⟩
  simp

/-- Restriction of sheaves of modules to a simplicial component is additive: it reindexes
components and restricts scalars along the identity, neither of which changes the underlying
additive maps. -/
local instance additive_componentModuleRestriction' (m : SimplexCategory) :
    (S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) m).Additive where
  map_add := rfl

/-- Restriction `g_n^*` of sheaves of modules to the degree-`n` simplicial component preserves
injective objects when every structure-sheaf transition `f_φ⁻¹O_n ⟶ O_m` out of degree `n` is
flat: it is right adjoint to `g_{n!}`, which is exact by Stacks 0D74, and Homology 015Z
applies. -/
theorem preservesInjectiveObjects_componentModuleRestriction'
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom P φ).IsFlat) :
    (S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P))
        n).PreservesInjectiveObjects := by
  have adj := S.componentModuleLowerShriekAdjunction
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P) n
  have := adj.left_adjoint_additive
  exact preservesInjectiveObjects_of_isExact _ _ adj
    ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriek' P n hflat))

/-- **Stacks 0D75.** Let `O` be a sheaf of rings on the total site whose structure-sheaf
transitions `f_φ⁻¹O_n ⟶ O_m` out of degree `n` are flat. An injective sheaf of `O`-modules
restricts to an injective sheaf of `O_n`-modules on the degree-`n` simplicial component.

Restriction is right adjoint to `g_{n!}`, which is exact by Stacks 0D74, so Homology 015Z
applies. -/
@[stacks 0D75]
theorem injective_componentModuleRestriction'
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom P φ).IsFlat)
    (I : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P))) [Injective I] :
    Injective ((S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) P)) n).obj I) :=
  have := S.preservesInjectiveObjects_componentModuleRestriction' P n hflat
  Functor.injective_obj _ _

end CategoryTheory.SimplicialSiteSituation

end
