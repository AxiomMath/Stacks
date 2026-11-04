module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.DerivedProducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact

/-!
# Milnor sequences on a site with enough weakly contractible objects

On a ringed site carrying a covering collection of weakly contractible objects, every inverse
system `(Kₙ)` in the derived category of sheaves of modules has Milnor short exact sequences

`0 ⟶ R¹lim Hᵖ⁻¹(Kₙ) ⟶ Hᵖ(R lim Kₙ) ⟶ lim Hᵖ(Kₙ) ⟶ 0`

in every degree `p`.

## Main results

* `Stacks.WeaklyContractible.exists_milnor_shortExact_of_weaklyContractibleObjectsSituation`:
  the Milnor short exact sequences of an inverse system in the derived category of sheaves of
  modules.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947), part (7)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u t

namespace Stacks.WeaklyContractible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

attribute [local instance] hasProductsOfShape_nat_derivedCategory

/-- **Milnor sequences.** On a ringed site with a covering collection of weakly contractible
objects, an inverse system `K` in the derived category of sheaves of modules and a derived limit
`L` of it fit, in every degree `r`, into a short exact sequence

`0 ⟶ R¹lim Hʳ⁻¹(Kₙ) ⟶ Hʳ(L) ⟶ lim Hʳ(Kₙ) ⟶ 0`,

where `R¹lim` of an inverse system of sheaves of modules is the cokernel of the difference map
`1 - shift` on the product of its terms. The first map is induced by the connecting morphism of
the triangle `L ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ L[1]` through the comparison `Hʳ⁻¹(∏ Kₙ) ≅ ∏ Hʳ⁻¹(Kₙ)`, and the
second is the map whose components are `Hʳ` of the composites `L ⟶ ∏ Kₙ ⟶ Kₙ`. -/
@[stacks 0947 "(7)"]
theorem exists_milnor_shortExact_of_weaklyContractibleObjectsSituation
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    [HasDerivedCategory (SheafOfModules.{t} S.O)]
    (F : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{t} S.O))
    (L : DerivedCategory (SheafOfModules.{t} S.O)) (hL : IsDerivedLimit F L) :
    let X : ℕ → DerivedCategory (SheafOfModules.{t} S.O) := fun n ↦ F.obj (Opposite.op n)
    let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦
      Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : L ⟶ ∏ᶜ X) (b : (∏ᶜ X) ⟶ L⟦(1 : ℤ)⟧),
      let T := Triangle.mk a d b
      T ∈ distTriang (DerivedCategory (SheafOfModules.{t} S.O)) ∧
        ∀ r : ℤ,
          let H := DerivedCategory.homologyFunctor (SheafOfModules.{t} S.O) r
          let H₁ := DerivedCategory.homologyFunctor (SheafOfModules.{t} S.O) (r - 1)
          let homologySystem : ℕᵒᵖ ⥤ SheafOfModules.{t} S.O := F ⋙ H
          let shiftedHomologySystem : ℕᵒᵖ ⥤ SheafOfModules.{t} S.O := F ⋙ H₁
          let P : SheafOfModules.{t} S.O :=
            ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)
          let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) n -
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) (n + 1) ≫
                shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
          ∃ (e : H₁.obj (∏ᶜ X) ≅ P)
            (i : cokernel δ ⟶ H.obj L) (q : H.obj L ⟶ limit homologySystem)
            (w : i ≫ q = 0),
            e.hom = piComparison H₁ X ∧
              cokernel.π δ ≫ i = e.inv ≫
                DerivedCategory.HomologySequence.δ T (r - 1) r ∧
              (∀ n : ℕ, q ≫ limit.π homologySystem (Opposite.op n) =
                H.map a ≫ H.map (Pi.π X n)) ∧
              (ShortComplex.mk i q w).ShortExact :=
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{t} S.O) :=
    Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat
      S.B S.hasEnoughObjects S.isWeaklyContractible
  DerivedCategory.isDerivedLimit_homology_shortExact F L hL

end Stacks.WeaklyContractible

end
