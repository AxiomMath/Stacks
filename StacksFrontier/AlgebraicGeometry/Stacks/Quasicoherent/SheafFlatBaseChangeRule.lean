module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule

/-!
# The rule `LQCoh^fbc` at the universe of the schemes (Stacks 0765, 0771 (4))

The proof of **Stacks 0765** applies the criterion of **Stacks 076Z** to the rule assigning to
an algebraic stack `𝒳` the full subcategory `LQCoh^fbc(𝒪_𝒳)` of `Mod(𝒳_étale, 𝒪_𝒳)`: the
locally quasi-coherent modules (**Stacks 06WJ**) with the flat base change property
(**Stacks 0762**). Here this rule is a `AlgebraicGeometry.Stack.StackModuleRule`, whose modules
have their sections in the universe `u` of the schemes, with the flat base change property read on
sheaves (`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`).

## Main definitions

* `AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule`: the rule `LQCoh^fbc`, in the étale topology.

## Main results

* `AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule_le_locallyQuasicoherentModuleRule`: its
  members are members of the rule of local quasi-coherence of **Stacks 075Z**.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isZero` and
  `AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule_of_isZero`: a zero module has the flat base
  change property and is in `LQCoh^fbc`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rule `LQCoh^fbc`** in the sense of **Stacks 076Z**, at the universe of the schemes: to an
algebraic stack `𝒳` it assigns the étale sheaves of `𝒪_𝒳`-modules which are locally
quasi-coherent (**Stacks 06WJ**) and have the flat base change property of **Stacks 0762**. -/
abbrev lqcohSheafFbcModuleRule : StackModuleRule.{u, t} B S hS .etale :=
  fun 𝒳 F => IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F.val

/-- The members of `LQCoh^fbc` are locally quasi-coherent. -/
theorem lqcohSheafFbcModuleRule_le_locallyQuasicoherentModuleRule
    (𝒳 : AlgebraicStacks.{u, t} B S hS) :
    lqcohSheafFbcModuleRule B E h S hS 𝒳 ≤ locallyQuasicoherentModuleRule B S hS E h 𝒳 :=
  fun _ hF => hF.1

/-- A zero module has the flat base change property of **Stacks 0762**. -/
theorem hasSheafFlatBaseChangeProperty_of_isZero {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj}
    (hF : Limits.IsZero F) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F := by
  intro x y φ _
  have hx : Limits.IsZero ((restrictModuleToSmallEtaleFunctor.{u, u + 1, u, u} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) x).obj F) :=
    Functor.map_isZero _ hF
  have : IsIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F) :=
    ⟨⟨hx.to_ _, (Functor.map_isZero _ (Functor.map_isZero _ hF)).eq_of_src _ _, hx.eq_of_src _ _⟩⟩
  exact ⟨inferInstance, inferInstance⟩

/-- A zero module is in `LQCoh^fbc`. -/
theorem lqcohSheafFbcModuleRule_of_isZero (𝒳 : AlgebraicStacks.{u, t} B S hS)
    {F : StackModules B S hS .etale 𝒳} (hF : Limits.IsZero F) :
    lqcohSheafFbcModuleRule B E h S hS 𝒳 F :=
  have := isWeakSerre_locallyQuasicoherentModuleRule B S hS E h 𝒳
  ⟨(locallyQuasicoherentModuleRule B S hS E h 𝒳).prop_of_isZero hF,
    hasSheafFlatBaseChangeProperty_of_isZero B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (Functor.map_isZero (SheafOfModules.forget _) hF)⟩

end AlgebraicGeometry.Stack
