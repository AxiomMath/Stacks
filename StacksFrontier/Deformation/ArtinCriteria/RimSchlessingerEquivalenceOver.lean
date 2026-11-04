module

public import StacksFrontier.Deformation.ArtinCriteria.DiagonalBaseChangeTangent
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger
import all StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger

/-!
# Condition (RS) transports along an equivalence over the site

Let `P` and `Q` be categories fibred in groupoids over the big fppf site of a scheme `S` and
`e : P ≃ Q` an equivalence over the site. If `P` satisfies condition (RS) (Stacks 07WP), so does
`Q`. The forward functor of `e` restricts to an equivalence on every fibre, and it intertwines the
canonical functors of the two categories from the fibre over the fourth corner of a square to the
2-fibre product of the fibres over the other three (the identification used for Stacks 07WR); the
functor it induces on those 2-fibre products is an equivalence by Stacks 02XB (3).

Applied to `𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`, which satisfies (RS) by Stacks 07WR, this is
Artin's axiom `[2]` for any category equivalent to `𝒴` over the site — for instance the category
fibred in sets of its functor of isomorphism classes — as the proof of Stacks 07Y5 uses it.

## Main results

* `Deformation.Artin.isEquivalence_fiberMap_of_equivalenceOver`: an equivalence over a base
  category restricts to an equivalence on every fibre.
* `Deformation.Artin.satisfiesRS_of_equivalenceOver`: condition (RS) transports along an
  equivalence over the site.
* `Deformation.Artin.satisfiesRS_of_equivalenceOver_diagonalBaseChange`: axiom `[2]` for a
  category equivalent to `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` over the site.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WR](https://stacks.math.columbia.edu/tag/07WR)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u v w v₁ w₁ v₂ w₂ v₃ w₃

/-- **An equivalence over a base category restricts to an equivalence on every fibre.** For an
equivalence `e` over `𝒞` between `p` and `q`, the functor induced by its forward functor on the
fibres over any object `Z` of `𝒞` is an equivalence: it is faithful and full because the forward
functor is, the preimage of a morphism over `𝟙 Z` lying over `𝟙 Z` since the forward functor is
strictly over `𝒞`, and every object of the fibre of `q` is the image of its image under the
backward functor, through the counit, which lies over identities. -/
theorem isEquivalence_fiberMap_of_equivalenceOver {𝒞 : Type w₃} [Category.{v₃} 𝒞]
    {X₁ : Type v₁} [Category.{w₁} X₁] {X₂ : Type v₂} [Category.{w₂} X₂]
    {p : X₁ ⥤ 𝒞} {q : X₂ ⥤ 𝒞} (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := 𝒞) p q)
    (Z : 𝒞) : (Functor.fiberMap p q e.hom.functor e.hom.w Z).IsEquivalence := by
  have : e.hom.functor.IsEquivalence := e.toEquivalence.isEquivalence_functor
  exact
    { faithful := ⟨fun h =>
        Subtype.ext (e.hom.functor.map_injective (congrArg Subtype.val h))⟩
      full := ⟨fun φ => by
        obtain ⟨ψ, hψ⟩ := e.hom.functor.map_surjective φ.1
        have hlift : (e.hom.functor ⋙ q).IsHomLift (𝟙 Z) ψ := by
          have : q.IsHomLift (𝟙 Z) (e.hom.functor.map ψ) := hψ ▸ φ.2
          exact IsHomLift.of_fac' (e.hom.functor ⋙ q) (𝟙 Z) ψ
            (IsHomLift.domain_eq q (𝟙 Z) (e.hom.functor.map ψ))
            (IsHomLift.codomain_eq q (𝟙 Z) (e.hom.functor.map ψ))
            (IsHomLift.fac' q (𝟙 Z) (e.hom.functor.map ψ))
        rw [e.hom.w] at hlift
        exact ⟨⟨ψ, hlift⟩, Subtype.ext hψ⟩⟩
      essSurj := ⟨fun b => by
        obtain ⟨b, rfl⟩ := b
        exact ⟨(Functor.fiberMap q p e.inv.functor e.inv.w (q.obj b)).obj ⟨b, rfl⟩,
          ⟨Functor.fiberIsoOfLift q (e.counitIso.app b) (e.isHomLift_counitIso_hom_app b)⟩⟩⟩ }

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (RS) transports along an equivalence over the site.** If `P` and `Q` are fibred in
groupoids over the big fppf site of `S`, `P` satisfies (RS) and `e` is an equivalence over the site
between `P` and `Q`, then `Q` satisfies (RS). At each square of the condition, the forward functor
of `e` intertwines the two canonical functors to 2-fibre products of fibres; it is an equivalence
on each fibre (`Deformation.Artin.isEquivalence_fiberMap_of_equivalenceOver`), so the functor it
induces on the 2-fibre products of fibres is an equivalence (Stacks 02XB (3)), and the canonical
functor of `Q` is one because that of `P` is. -/
theorem satisfiesRS_of_equivalenceOver
    {X₁ : Type v₁} [Category.{w₁} X₁] {X₂ : Type v₂} [Category.{w₂} X₂]
    {P : X₁ ⥤ BigFppfOver B S hS} {Q : X₂ ⥤ BigFppfOver B S hS}
    (hP : P.IsFiberedInGroupoids) (hQ : Q.IsFiberedInGroupoids)
    (hRS : SatisfiesRS B S hS P hP)
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS) P Q) :
    SatisfiesRS B S hS Q hQ := by
  let : P.IsFibered := hP.isFibered
  let : Q.IsFibered := hQ.isFibered
  dsimp only [SatisfiesRS]
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hFTX hFTX' hFTY hFTY' hClosed hPush
  have hx := hRS (i := i) (j := j) (i' := i') (j' := j') w hX hX' hY hY'
    hFTX hFTX' hFTY hFTY' hClosed hPush
  have hF : Functor.IsFibredOneMorphism P Q e.hom.functor :=
    hQ.isFibredOneMorphism e.hom.w
  have := isEquivalence_fiberMap_of_equivalenceOver e
  have : (fiberSquareTargetMap hF j i).IsEquivalence := by
    unfold fiberSquareTargetMap
    exact CategoryTheory.induced_isEquivalence_of_isEquivalence _ _ _ _ _
  have : (Functor.fiberMap P Q e.hom.functor hF.comp_eq Y' ⋙
      fiberSquareComparison Q (Functor.chosenPullbacks Q) j i j' i' w.symm).IsEquivalence :=
    Functor.isEquivalence_of_iso (fiberSquareComparison_map hF j i j' i' w.symm)
  exact Functor.isEquivalence_of_comp_left (Functor.fiberMap P Q e.hom.functor hF.comp_eq Y') _

/-- **Axiom `[2]` for a category equivalent to `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`** over the
site — for instance the category fibred in sets of its functor of isomorphism classes. The 2-fibre
product satisfies (RS) by Stacks 07WR (`Deformation.Artin.satisfiesRS_diagonalBaseChange`), and
(RS) transports along the equivalence. This is axiom `[2]` for the functor `Y` in the proof of
Stacks 07Y5. -/
theorem satisfiesRS_of_equivalenceOver_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)
    {X₂ : Type v₂} [Category.{w₂} X₂] {Q : X₂ ⥤ BigFppfOver B S hS}
    (hQ : Q.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS)
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor) Q) :
    SatisfiesRS B S hS Q hQ :=
  satisfiesRS_of_equivalenceOver B S hS
    (TwoFibreProductOver.isFiberedInGroupoids (Over.map V.hom) 𝒳.val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
      (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
      (Functor.IsFiberedInGroupoids.over_map V.hom) 𝒳.isFiberedInGroupoids
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
      (Stack.diagonalBasedFunctor B S hS 𝒳).w) hQ
    (satisfiesRS_diagonalBaseChange B S hS 𝒳 hRS V y hy) e

end Deformation.Artin

end
