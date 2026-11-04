module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilCohomologyTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassData

/-!
# Axiom (A8) of Section 45.14

Let `X` be a smooth projective scheme over a field `k` and `k' = Γ(X, 𝒪_X)`. Then `k'` is a
finite separable `k`-algebra (Varieties, Tag 0BUG), that is, a finite étale `k`-algebra, so that
`Spec(k')` is a smooth projective scheme over `k`, and the canonical morphism
`X ⟶ Spec(Γ(X, 𝒪_X))` is a morphism of smooth projective `k`-schemes. Axiom (A8) of Section 45.14
asks that the induced map `H^0(Spec(k')) ⟶ H^0(X)` be an isomorphism.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.GlobalSectionsAxiom`: **axiom (A8)**, stated with the
  morphism `Stacks.WeilCohomology.SmoothProjectiveScheme.toSpecGlobalSections` and the finite
  étale structure of `Γ(X, 𝒪_X)` of `...Concrete.WeilCohomologyTheory` (where the same condition
  is recorded for data (D0)–(D3), `Stacks.WeilCohomology.WeilData.GlobalSectionsCondition`).

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

open SmoothProjectiveScheme in
/-- **Axiom (A8)**: for a smooth projective scheme `X` over `k` and `k' = Γ(X, 𝒪_X)`, the map
`H^0(Spec(k')) ⟶ H^0(X)` induced by the canonical morphism `X ⟶ Spec(k')` is an isomorphism. -/
def GlobalSectionsAxiom : Prop :=
  ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    Function.Bijective fun a : 𝔇.grade (spec k (globalSections X)) 0 =>
      (⟨𝔇.pull (toSpecGlobalSections X) a, 𝔇.pull_grade (toSpecGlobalSections X) 0 a.1 a.2⟩ :
        𝔇.grade X 0)

end FirstChernClassData

end Stacks.WeilCohomology

end
