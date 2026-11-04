module

public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.Deformation.Artin.Versality.OpennessTransfer

/-!
# Openness of versality for a base change of the diagonal

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, `V` an object of the
site and `y : (Sch/V)_{fppf} ⥤ 𝒳 × 𝒳` a 1-morphism over the site. Openness of versality for the
diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` (part of axiom `[5]` of Section 07XJ, in the sense of Stacks 07XQ,
part (2)) says that the 2-fibre product

`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`,

regarded over `(Sch/V)_{fppf}` through its first projection, has openness of versality. This file
proves the step "Axiom [5] for `Y` follows directly from openness of versality for `Δ_𝒳`" of the
proof of Stacks 07Y5: `𝒴` regarded over `(Sch/S)_{fppf}` has openness of versality, and so has
every category equivalent to it over the site — in particular the category fibred in sets of its
functor of isomorphism classes.

Openness of versality is stated with `Deformation.Artin.HasOpenVersality`, the body of
`Deformation.Artin.IsOpenVersality` and `Deformation.Artin.IsOpenVersalityMorphism`: those two
predicates take a proof that the structure functor composed with `Over.post B.inclusion` is
fibred in groupoids over all schemes over the base, which is unsatisfiable over a bounded big
fppf site as soon as the category is nonempty (no object lies over a scheme of size at least the
cutoff), so they cannot serve as hypotheses here.

## Main results

* `Deformation.Artin.hasOpenVersality_diagonalBaseChange`: openness of versality over `V`
  gives openness of versality over `S`.
* `Deformation.Artin.hasOpenVersality_of_equivalenceOver_diagonalBaseChange`: the same for any
  category equivalent over the site to `𝒴`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u v w v₂ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Relocalizing the big fppf site and passing to all schemes commute: regarding a scheme over
`V` as one over `S` and then as a scheme over `S`, or first as a scheme over `V` and then over
`S`, is the same. -/
theorem overMap_comp_overPost (V : BigFppfOver B S hS) :
    Over.map V.hom ⋙ Over.post B.inclusion =
      Over.post B.inclusion ⋙ Over.map (B.inclusion.map V.hom) :=
  rfl

/-- **Axiom `[5]` for `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` over `S`** (the step "Axiom [5] for
`Y` follows directly from openness of versality for `Δ_𝒳`" of the proof of Stacks 07Y5). If the
2-fibre product of `y` and the diagonal, regarded over `V` through its first projection, has
openness of versality, then it has openness of versality regarded over `S`. -/
theorem hasOpenVersality_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hopen : HasOpenVersality
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙ Over.post B.inclusion)) :
    HasOpenVersality
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙ Over.post B.inclusion) := by
  have h := hasOpenVersality_comp_overMap (B.inclusion.map V.hom) _ hopen
  rwa [Functor.assoc, ← overMap_comp_overPost, ← Functor.assoc,
    TwoFibreProductOver.fst_comp_eq] at h

/-- **Axiom `[5]` for a category equivalent to `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`.** If the
2-fibre product of `y` and the diagonal has openness of versality over `V` and `Q` is equivalent
to it over the big fppf site of `S` — for instance the category fibred in sets of its functor of
isomorphism classes — then `Q` has openness of versality over `S`. This is axiom `[5]` for the
functor `Y` in the proof of Stacks 07Y5. -/
theorem hasOpenVersality_of_equivalenceOver_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hopen : HasOpenVersality
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙ Over.post B.inclusion))
    {𝒬 : Type v₂} [Category.{w₂} 𝒬] {Q : 𝒬 ⥤ BigFppfOver B S hS}
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS)
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor) Q) :
    HasOpenVersality (Q ⋙ Over.post B.inclusion) :=
  hasOpenVersality_of_equivalenceOver e
    (hasOpenVersality_diagonalBaseChange B S hS 𝒳 V y hopen)

end Deformation.Artin

end
