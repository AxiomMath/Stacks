module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SystemMorphismOfAlgebraicLimit

/-!
# Two limit descriptions of the same space are eventually isomorphic

In Situation 0CP6, let `X ⟶ B` be quasi-separated and let `G`, `G'` be two diagrams for `X` as
in Stacks 0CP8. Applying Stacks 0CPA to `𝟙 X` in both directions gives morphisms between the
two image systems of Stacks 0CP9 on a common tail, and the eventual uniqueness of Stacks 0CPA
shows that their composites are eventually the identities. This is the example of Stacks 0CPB.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_systemMorphism_inv_of_algebraicLimit`:
  the two limit descriptions are eventually isomorphic, with no bound on the size of the index
  set.

## References

* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace GoodDiagram

namespace SystemMorphism

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}

/-- **The limit descriptions attached to two good diagrams of the same space are eventually
isomorphic** (the example of Stacks 0CPB), for an index set of any size. On a common tail there
are morphisms of image systems in both directions inducing the identity of `X`, and at every
sufficiently late stage their components are mutually inverse. -/
theorem exists_systemMorphism_inv_of_algebraicLimit (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (G G' : GoodDiagram B S hS hZ D pX) :
    ∃ (i₀ : I) (h : G.index ≤ i₀) (h' : G'.index ≤ i₀)
      (E : SystemMorphism G G' (𝟙 X) i₀ h h') (E' : SystemMorphism G' G (𝟙 X) i₀ h' h)
      (i₁ : I) (h₁ : i₀ ≤ i₁), ∀ (i : I) (hi : i₁ ≤ i),
        E.app i (h₁.trans hi) ≫ E'.app i (h₁.trans hi) = 𝟙 _ ∧
          E'.app i (h₁.trans hi) ≫ E.app i (h₁.trans hi) = 𝟙 _ := by
  have ex := exists_systemMorphism_of_algebraicLimit hX hXqs (𝟙 X) (Category.id_comp pX)
  obtain ⟨a, ha, ha', ⟨E₀⟩⟩ := ex G G'
  obtain ⟨b, hb', hb, ⟨E₀'⟩⟩ := ex G' G
  obtain ⟨m, ham, hbm⟩ := exists_ge_ge a b
  let E := E₀.restrict ham
  let E' := E₀'.restrict hbm
  obtain ⟨c, hc, hc'⟩ := eventually_eq_systemMorphism_of_algebraicLimit hX hXqs
    (E.comp E' (Category.id_comp _)) (id G m (ha.trans ham))
  obtain ⟨d, hd, hd'⟩ := eventually_eq_systemMorphism_of_algebraicLimit hX hXqs
    (E'.comp E (Category.id_comp _)) (id G' m (hb'.trans hbm))
  obtain ⟨i₁, hci, hdi⟩ := exists_ge_ge c d
  refine ⟨m, ha.trans ham, hb'.trans hbm, E, E', i₁, hc.trans hci, fun i hi => ?_⟩
  let j := Over.mk (homOfLE ((hc.trans hci).trans hi)).op
  exact ⟨hc' j (hci.trans hi), hd' j (hdi.trans hi)⟩

end SystemMorphism

end GoodDiagram

end AlgebraicGeometry.Space

end
