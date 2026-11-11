module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcFbcDerivedLimitOfTruncations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineVanishing

/-!
# A complex with cohomology in `LQCoh^fbc` is the derived limit of its truncations (Stacks 08IY)

Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒪_𝒳)` whose cohomology sheaves are
locally quasi-coherent (**Stacks 06WJ**) and have the flat base change property of
**Stacks 0762**.  **Stacks 08IY** says that there is a distinguished triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`

in `D(𝒪_𝒳)`, that is, `K` is the derived limit of the tower of its canonical truncations from
below.

The flat base change property is read here as in the source, with the inverse image of *sheaves*
of modules: `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange`.  The
presheaf-level reading `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` used by
`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc_algebraicStack` is strictly
stronger and fails for some quasi-coherent modules (see
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafFlatBaseChangeProperty.lean`), so the
statement below implies that one.

The proof is the source's.

* The vanishing `H^p(x, ℱ) = 0` for `p > 0`, `ℱ` in `LQCoh^fbc(𝒪_𝒳)` and `x` lying over an affine
  scheme is
  `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`.
* The objects lying over an affine scheme cover `𝒳_fppf`:
  `AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall`.
* The convergence criterion of **Stacks 0D6P** with `d = 0` is
  `Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic`, and the
  triangle is produced from it by `Stacks.InverseSystem.exists_distTriang_milnor_of_isIso`.

## Main results

* `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcohSheafFbc_algebraicStack`:
  **Stacks 08IY**.

## References

* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

namespace AlgebraicGeometry.Stack

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  Stacks.Cohomology.AcyclicCover.evaluation_additive

/-- **Stacks 08IY.** Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒪_𝒳)`, the
derived category of the sheaves of `𝒪_𝒳`-modules on the fppf site of `𝒳`, whose cohomology
sheaves are locally quasi-coherent (**Stacks 06WJ**) and have the flat base change property of
**Stacks 0762**, read with the inverse image of sheaves of modules.  Then there is a distinguished
triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`

in `D(𝒪_𝒳)`: the product of the tower `n ↦ τ_{≥ -n}K` exists and `K` is its derived limit
(`CategoryTheory.Pretriangulated.IsDerivedLimit`, **Stacks 08TC**), the second arrow being
`1 - shift`.

As in the source: the higher cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` vanishes over the
objects lying over an affine scheme
(`AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`),
those objects cover `𝒳_fppf`
(`AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall`), and the
convergence criterion of **Stacks 0D6P** with `d = 0` applies
(`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic`). -/
@[stacks 08IY "K is the derived limit of its canonical truncations from below: the distinguished \
triangle K → ∏ τ_{≥ -n}K → ∏ τ_{≥ -n}K → K[1] in D(𝒪_𝒳), for an algebraic stack 𝒳 and a complex \
of fppf 𝒪_𝒳-modules whose cohomology sheaves are locally quasi-coherent with the flat base \
change property of 0762, read with the inverse image of sheaves of modules"]
theorem exists_isDerivedLimit_truncGETower_of_lqcohSheafFbc_algebraicStack
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (K : DerivedCategory (fppfSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
    (hK : ∀ i : ℤ, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor
        (fppfSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) i).obj K).val) :
    ∃ _ : HasProduct fun n : ℕ ↦
        (fppfTruncGETower B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids K).obj ⟨n⟩,
      IsDerivedLimit (fppfTruncGETower B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids K) K := by
  have hprod := Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower
    (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) K
  refine ⟨hprod, ?_⟩
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (fppfTruncGETower B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids K)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
    (fun n ↦ Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map K
      (homOfLE (Nat.le_succ n)).op)
    fun L c pr d hT hcn ↦
      Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
        (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) K
        (fun x => IsAffineOver B S hS (𝒳.val.val.p.obj x))
        (hasEnoughObjects_isAffineOver_of_essentiallySmall B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids)
        (fun x hx i hi m =>
          isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack B E h S hS 𝒳 _
            (hK m) x hx i hi)
        L c pr d hT hcn
  exact ⟨_, δ, hδ⟩

end AlgebraicGeometry.Stack

end
