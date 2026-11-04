module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# The criterion of Stacks 0EZU in terms of strict henselizations

Stacks, Lemma 0EZU: in a cartesian square of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `g` quasi-compact and quasi-separated, an abelian sheaf `F` on `T_étale` and `q ≥ 0`, the base
change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism exactly when for every geometric
point `x̄` of `X` with image `s̄`

`H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S T, F) = H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S T, F)`.

The equality of cohomology groups is read as the canonical map being an isomorphism: the degree-`q`
cohomology of the restriction of derived sections along the morphism
`Spec(𝒪^{sh}_{X,x̄}) ×_S T ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S T` induced by the canonical morphism of strict
henselizations, of the inverse image of `F`. The strict henselizations are those of a big étale
site `B` containing `X` and `S`.

## Main definitions

* `Stacks.EtaleCohomology.SmoothBaseChange.StrictHenselizationBaseChangeCriterion` — the
  statement of Stacks 0EZU.

## References

* [Stacks Project, Tag 0EZU](https://stacks.math.columbia.edu/tag/0EZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- The morphism `Spec(𝒪^{sh}_{X,x̄}) ×_S T ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S T` induced by the canonical
morphism of strict henselizations, for `f : X ⟶ S`, `g : T ⟶ S` and a geometric point `x̄` of `X`
with image `s̄`. -/
def strictHenselizationBaseChangeMap (B : BigEtaleSite.{u}) {X S T : Scheme.{u}}
    (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) (g : T ⟶ S) (x : GeometricPoint X) :
    pullback (strictHenselizationToBase B X hX x ≫ f) g ⟶
      pullback (strictHenselizationToBase B S hS (x.map f)) g :=
  pullback.map _ _ _ _ (strictHenselizationSquareMap B hX hS f x) (𝟙 T) (𝟙 S)
    (by rw [Category.comp_id, strictHenselizationSquareMap_comp]) (by simp)

/-- **The statement of Stacks 0EZU.** For a cartesian square of schemes with `g` quasi-compact and
quasi-separated, an abelian sheaf `F` on `T_étale` and `q : ℕ`, the base change map
`f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism if and only if, for every geometric point `x̄`
of `X` with image `s̄`, the canonical map
`H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S T, F) ⟶ H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S T, F)` is an isomorphism. -/
def StrictHenselizationBaseChangeCriterion (B : BigEtaleSite.{u}) : Prop :=
  ∀ ⦃X Y S T : Scheme.{u}⦄ (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ),
    (∀ x : GeometricPoint X,
      letI := smallEtaleGlobalSectionsAb_hasRightDerivedFunctor
        (pullback (strictHenselizationToBase B S hS (x.map f)) g)
      letI := smallEtaleGlobalSectionsAb_hasRightDerivedFunctor
        (pullback (strictHenselizationToBase B X hX x ≫ f) g)
      IsIso ((DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).map
        ((smallEtaleDerivedGlobalSectionsRestriction
          (strictHenselizationBaseChangeMap B hX hS f g x)).app
          ((smallEtaleDerivedPullbackAb
            (pullback.snd (strictHenselizationToBase B S hS (x.map f)) g)).obj
            ((DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj
              F))))) ↔
      IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F)

end Stacks.EtaleCohomology.SmoothBaseChange

end
