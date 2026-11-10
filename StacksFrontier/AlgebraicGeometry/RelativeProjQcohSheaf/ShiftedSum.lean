module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeZero

/-!
# The canonical map from a graded module to the sum of the sheaves of its shifts

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra and `ℳ` a graded `𝒜`-module (Situation 01NN), and
let `(d, f : T → S, L, ψ)` be a quadruple over a test scheme `T` as in Section 01NS. Tag 01O6
attaches to these data the `𝒪_T`-module

`ℳ̃_T = (f^*ℳ^{(d)} ⊗_{f^*𝒜^{(d)}} (⨁_{n ∈ ℤ} L^{⊗ n}))₀`,

and `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.degreeZeroMap` is the canonical map
`f^*ℳ_0 ⟶ ℳ̃_T`, which carries a local section `x` to the pure tensor `x ⊗ 1` of degree zero.

The shift `ℳ(n)` has `ℳ(n)_m = ℳ_{m + n}`, so its degree-zero piece is `ℳ_n`. Applying the
degree-zero map to `ℳ(n)` therefore gives a map `f^*ℳ_n ⟶ (ℳ(n))~_T` for every `n`, and the
underlying `𝒪_S`-module of `ℳ` is the direct sum `⨁_{n ∈ ℤ} ℳ_n`. Since the pullback of sheaves of
modules preserves direct sums, those maps assemble into one map

`f^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~_T`,

which is property (7) of Tag 01O7 read on the chart of a quadruple: the maps
`π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~` of that property pull back along the morphism `h : T → Proj_S(𝒜)`
classified by the quadruple to maps `f^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~_T`, because `π ∘ h = f` and
`h^*(ℳ(n))~ = (ℳ(n))~_T`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.shiftDegreeZeroIso`: the identification
  `f^*ℳ_n ≅ f^*(ℳ(n)_0)` of the pullback of the degree-`n` piece with the pullback of the
  degree-zero piece of the shift.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.shiftedDegreeMap`: the canonical map
  `f^*ℳ_n ⟶ (ℳ(n))~_T`, the degree-zero map of the shift read on `ℳ_n`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.shiftedSumMap`: **the canonical map
  `f^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~_T`**.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.shiftedSumMap_ι`: on the summand
  `f^*ℳ_n` of `f^*ℳ` the map is the canonical map `f^*ℳ_n ⟶ (ℳ(n))~_T` followed by the inclusion of
  the `n`-th summand. Since the summands generate, this determines the map.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.shiftedDegreeMap_comp`: the degree-`n`
  map is determined by the degree-zero pure tensors of `ℳ(n)`.

## Implementation notes

The degree-zero piece of `ℳ(n)` is `ℳ_{0 + n}`, which is only propositionally `ℳ_n`, so the
degree-`n` map is the pullback of a transport followed by the degree-zero map of the shift. The
transport is given as an isomorphism `shiftDegreeZeroIso` rather than inlined as an `eqToHom`, and
its type is written with `(ℳ(n)).piece 0` on the right so that the composite defining
`shiftedDegreeMap` has that object as its middle term on the nose; the pullback functor's image of
an `eqToHom` is an isomorphism because the functor carries the inverse transport to its inverse,
and no `IsIso` instance is needed.

The direct sum of the shifted sheaves and the direct sum underlying `ℳ` are both the categorical
coproduct `∐`, which is the only arbitrary-index direct sum of sheaves of modules available; the
index `ℤ` lies in the lowest universe, which is where `modulesHasCoproducts` provides the
coproducts. The comparison `f^*(⨁_n ℳ_n) ≅ ⨁_n f^*ℳ_n` is `Limits.PreservesCoproduct.iso` of the
pullback functor, available because the pullback is a left adjoint
(`Stacks.PullbackAlgebra.preservesColimitsOfShape_pullbackFunctor`).

The shift used is the unsigned reindexing `SheafOfModules.GradedModule.shift`. No Koszul sign
enters: the summands of `ℳ̃_T` are built from the pieces and the action of the graded module, and
both are transported by the shift without a sign, as Situation 01NN's commutative graded algebras
call for.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Equation 27.10.0.6, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesAbelian
  Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesHasCoproducts

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f A d L)

/-- **The degree-zero piece of the shift `ℳ(n)` is `ℳ_n`**, after pullback: the transport of the
degree-`n` piece along `n = 0 + n`, pulled back along `f`. -/
def shiftDegreeZeroIso (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (M.piece n) ≅
      (pullbackFunctor (ringedSpaceHom f)).obj ((M.shift n).piece 0) :=
  (pullbackFunctor (ringedSpaceHom f)).mapIso
    (eqToIso (congrArg M.piece (zero_add n).symm))

/-- **The canonical map `f^*ℳ_n ⟶ (ℳ(n))~_T`**: the degree-zero map of the shift `ℳ(n)`, whose
degree-zero piece is `ℳ_n`. It carries a local section `x` of `f^*ℳ_n` to the pure tensor `x ⊗ 1`
of degree zero in `(ℳ(n))~_T`. -/
def shiftedDegreeMap (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (M.piece n) ⟶ associatedSheaf (M.shift n) ψ :=
  (shiftDegreeZeroIso M n).hom ≫ degreeZeroMap (M.shift n) ψ

/-- **The degree-`n` map is determined by the degree-zero pure tensors of `ℳ(n)`.** Composing it
with the morphism out of `(ℳ(n))~_T` induced by a balanced family `b` of degreewise maps gives the
degree-zero member `b 0` of the family, read through the identification of `f^*ℳ_n` with the
degree-zero summand of the pure tensors of `ℳ(n)`. -/
theorem shiftedDegreeMap_comp (n : ℤ)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ k : ℤ, summand f (M.shift n) d L k ⟶ N) (h : associatedSheaf (M.shift n) ψ ⟶ N)
    (hh : ∀ k : ℤ, pureTensor (M.shift n) ψ k ≫ h = b k) :
    shiftedDegreeMap M ψ n ≫ h =
      (shiftDegreeZeroIso M n).hom ≫
        (ρ_ ((pullbackFunctor (ringedSpaceHom f)).obj ((M.shift n).piece 0))).inv ≫
          unitSummand (M.shift n) (L := L) ≫ b 0 := by
  rw [shiftedDegreeMap, Category.assoc, degreeZeroMap_comp (M.shift n) ψ b h hh]

/-- The canonical map

`f^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~_T`

of property (7) of Tag 01O7 on the chart of a quadruple, out of the pullback of the `𝒪_S`-module
`ℳ = ⨁_{n ∈ ℤ} ℳ_n` underlying a graded `𝒜`-module. On the summand `f^*ℳ_n` it is the canonical map
`f^*ℳ_n ⟶ (ℳ(n))~_T`, which carries a local section `x` to the pure tensor `x ⊗ 1` of degree zero
in `(ℳ(n))~_T`; this generalizes the map `M ⟶ ⨁_{n ∈ ℤ} Γ(Proj 𝒮, M(n)~)` of Equation 27.10.0.6 of
Tag 01MR.

Property (7) of Tag 01O7 provides maps `π^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~` on `Proj_S(𝒜)`; their pullback
along the morphism `h : T → Proj_S(𝒜)` classified by the quadruple is this map, since `π ∘ h = f`
and `h^*(ℳ(n))~ = (ℳ(n))~_T`. The map on `Proj_S(𝒜)` itself is
`Stacks.RelativeProj.Situation.shiftedSumSheafMap`. -/
def shiftedSumMap :
    (pullbackFunctor (ringedSpaceHom f)).obj (∐ fun n : ℤ => M.piece n) ⟶
      ∐ fun n : ℤ => associatedSheaf (M.shift n) ψ :=
  (PreservesCoproduct.iso (pullbackFunctor (ringedSpaceHom f)) (fun n : ℤ => M.piece n)).hom ≫
    Sigma.desc fun n => shiftedDegreeMap M ψ n ≫
      Sigma.ι (fun k : ℤ => associatedSheaf (M.shift k) ψ) n

/-- **The map `f^*ℳ ⟶ ⨁_{n ∈ ℤ} (ℳ(n))~_T` restricted to the summand `f^*ℳ_n`** is the canonical
map `f^*ℳ_n ⟶ (ℳ(n))~_T` followed by the inclusion of the `n`-th summand. The summands generate
`f^*ℳ`, so this determines the map. -/
theorem shiftedSumMap_ι (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).map (Sigma.ι (fun k : ℤ => M.piece k) n) ≫
        shiftedSumMap M ψ =
      shiftedDegreeMap M ψ n ≫ Sigma.ι (fun k : ℤ => associatedSheaf (M.shift k) ψ) n := by
  have h : (pullbackFunctor (ringedSpaceHom f)).map (Sigma.ι (fun k : ℤ => M.piece k) n) ≫
        (PreservesCoproduct.iso (pullbackFunctor (ringedSpaceHom f))
          fun k : ℤ => M.piece k).hom =
      Sigma.ι (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (M.piece k)) n :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit (pullbackFunctor (ringedSpaceHom f))
        fun k : ℤ => M.piece k)
      (colimit.isColimit _) (Discrete.mk n)
  rw [shiftedSumMap, ← Category.assoc, h, Sigma.ι_comp_desc]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

end
