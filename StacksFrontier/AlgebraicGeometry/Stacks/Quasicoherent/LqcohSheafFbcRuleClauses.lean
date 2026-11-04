module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeSmoothLocal

/-!
# Clauses (2) and (3) of Stacks 076Z for the rule `LQCoh^fbc`

The rule `AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule` assigns to an algebraic stack the étale
sheaves of modules which are locally quasi-coherent (**Stacks 06WJ**) and have the flat base
change property of **Stacks 0762**, read on sheaves. Clause (2) of **Stacks 076Z** asks that the
rule be stable under inverse image along smooth 1-morphisms. For this rule no smoothness is
needed: the inverse image along any 1-morphism of algebraic stacks preserves local
quasi-coherence (**Stacks 06WL**) and the flat base change property (**Stacks 0764** part (1)),
which together are **Stacks 0771** part (3). Clause (3) asks that membership be local for a
jointly surjective family of smooth 1-morphisms; its converse half is **Stacks 075Y** for local
quasi-coherence and **Stacks 0764** part (3) for the flat base change property.

## Main results

* `AlgebraicGeometry.Stack.isStableUnderSmoothPullback_lqcohSheafFbcModuleRule`: clause (2) of
  **Stacks 076Z** for `LQCoh^fbc`.
* `AlgebraicGeometry.Stack.isSmoothLocalConverse_lqcohSheafFbcModuleRule` and
  `AlgebraicGeometry.Stack.isSmoothLocal_lqcohSheafFbcModuleRule`: clause (3).

## References

* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open CategoryTheory

universe u t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Clause (2) of Stacks 076Z for `LQCoh^fbc`**: the inverse image of a member of the rule
along a smooth 1-morphism of algebraic stacks is a member. This is **Stacks 0771** part (3),
`AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules_stackModuleInverseImage`, which holds for
every 1-morphism. -/
theorem isStableUnderSmoothPullback_lqcohSheafFbcModuleRule :
    StackModuleRule.IsStableUnderSmoothPullback .etale
      (lqcohSheafFbcModuleRule.{u, t} B E h S hS) :=
  fun g _ F hF => lqcohSheafFbcEtaleModules_stackModuleInverseImage B E h S hS g F hF

/-- The flat base change property of the inverse image of sheaves of modules
`Stacks.RelativeCech.moduleInverseImage`, presented over an arbitrary functor `p` equal to
`F ⋙ q`, is that of the inverse image of presheaves of modules over the strict presentation. -/
theorem hasSheafFlatBaseChangeProperty_moduleInverseImage_iff {𝒵 𝒳 : Type (u + 1)}
    [Category.{u} 𝒵] [Category.{u} 𝒳] (p : 𝒵 ⥤ BigFppfOver B S hS)
    (q : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : 𝒵 ⥤ 𝒳) (hF : F ⋙ q = p) (hFq : (F ⋙ q).IsFiberedInGroupoids)
    (G : SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS q hq .etale)) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)
        ((Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u} B S hS p q hp hq F hF
          .etale).obj G).val ↔
      HasSheafFlatBaseChangeProperty B E h S hS (F ⋙ q) hFq (etaleTopology B)
        (etaleTopology_le_topology B)
        ((modulePresheafPullback.{u, u + 1, u, u + 1, u, u} B S hS q hq F hFq).obj G.val) := by
  subst hF
  rfl

/-- **The converse half of clause (3) of Stacks 076Z for `LQCoh^fbc`**: a module on `𝒳_ét`
whose inverse images along a jointly surjective family of smooth 1-morphisms are members of the
rule is a member. This is **Stacks 075Y** for local quasi-coherence and **Stacks 0764** part (3)
for the flat base change property. -/
theorem isSmoothLocalConverse_lqcohSheafFbcModuleRule :
    StackModuleRule.IsSmoothLocalConverse.{u, t, s} .etale
      (lqcohSheafFbcModuleRule.{u, t} B E h S hS) := by
  intro J 𝒲 𝒳 f hsmooth hjs F hF
  exact ⟨isSmoothLocalConverse_locallyQuasicoherentModuleRule.{u, t, s} B S hS E h f hsmooth hjs F
      fun j => (hF j).1,
    hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs
      F.val F.isSheaf fun j => (hasSheafFlatBaseChangeProperty_moduleInverseImage_iff B E h S hS
        _ _ _ _ _ _ (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) F).1 (hF j).2⟩

/-- **Clause (3) of Stacks 076Z for `LQCoh^fbc`**: for a jointly surjective family of smooth
1-morphisms, a module on `𝒳_ét` is a member of the rule if and only if all its inverse images
along the family are. -/
theorem isSmoothLocal_lqcohSheafFbcModuleRule :
    StackModuleRule.IsSmoothLocal.{u, t, s} .etale (lqcohSheafFbcModuleRule.{u, t} B E h S hS) :=
  StackModuleRule.isSmoothLocal_of_isSmoothLocalConverse
    (isStableUnderSmoothPullback_lqcohSheafFbcModuleRule B E h S hS)
    (isSmoothLocalConverse_lqcohSheafFbcModuleRule B E h S hS)

end AlgebraicGeometry.Stack

end
