module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelEtaleSquareCoherence
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyMapIsTheEdgeMorphism

/-!
# The base-change square of Stacks 0EYL's levels, on cohomology

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelEtaleSquareCoherence.lean` builds the
pasted base-change square `levelEtaleSquare` of the levels of Stacks 0EYL: restriction to the level
`i` followed by direct image along the transition of `a : i ⟶ j` is direct image along base change
in the small étale site followed by restriction to the level `j`, with its identity and composition
laws.

This file reads that square on **cohomology**, which is the index-naturality clause of Stacks
03Q6. Both the transition map of the cohomology of the levels and the transition map of the
cohomology of the small étale sites of the stages are Leray edge morphisms
(`Stacks.Cohomology.RightDerivedEdge.edge`), and the square relating them is an instance of the
calculus of `StacksFrontier/Algebra/Homology/RightDerivedEdgeCalculus.lean`:

* composition in the first variable (`edge_app_comp`) splits each side of the square into the
  comparison with the stage and the transition along it;
* naturality in the first variable (`map_comp_edge_app`) is where `levelEtaleSquare` enters;
* the naturality of `edge` itself in the sheaf absorbs the transition map `ψ` of the system.

Nothing else is used; in particular no new geometry.

## Main results

* `Stacks.EtaleCohomology.TransitionBaseChange.edge_levelEtaleSquare` — **the cohomological
  base-change square of the levels.** The transition map of the derived sections of the levels,
  followed by the comparison with the small étale site of the stage, equals the comparison at the
  other end followed by the transition map of the derived sections of the stages, read across the
  square.
* `Stacks.EtaleCohomology.TransitionBaseChange.isIso_edge_levelEtaleRestrict` — **the comparison
  between the cohomology of a level and the cohomology of the small étale site of its stage is an
  isomorphism**, because restriction to the level is an equivalence of abelian sheaf categories.

## Implementation notes

The sections functor is taken over an arbitrary object `V` of the level `j`, not over a terminal
one: the objects the cohomology diagram of Stacks 09YQ is taken over are transition images of a
chart and are not canonical choices. Terminality is only needed to *name* the resulting groups as
the cohomology of a site, which is
`Stacks.EtaleCohomology.TransitionBaseChange.sectionsRightDerivedIsoEtaleCohomology` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelEtaleSquareEtaleCohomology.lean`;
the square read in that spelling is `...TransitionBaseChange.levelEtaleCohomologyIso_naturality`
there.

The abelian machinery of the four sheaf categories involved, and the preservation of injective
objects by the three direct images, are instance arguments rather than derived — except that
`[(stagePush E Ab a).PreservesInjectiveObjects]` is a theorem,
`Stacks.EtaleCohomology.TransitionBaseChange.preservesInjectiveObjects_stagePush`, with no
hypothesis at all. At the canonical system of Stacks 0EYL the others come from
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.hasSheafifyAb`,
`...enoughInjectives` and `...injective_abelianSheafPushforward`, and for the restriction to a
level from its being an equivalence.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.RightDerivedEdge

namespace Stacks.EtaleCohomology.TransitionBaseChange

universe v u

open AlgebraicGeometry

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX)
  [hcont : ∀ i : E.system.I,
    (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]

attribute [local instance] isContinuous_transition isContinuous_stageBaseChange
  isContinuous_transition_comp_levelEtale isContinuous_levelEtale_comp_stageBaseChange
  isContinuous_transition_comp isContinuous_stageBaseChange_comp

section Square

variable {i j : E.system.I} (a : i ⟶ j)
  [HasSheafify (E.system.J i) Ab.{max u v + 1}] [HasSheafify (E.system.J j) Ab.{max u v + 1}]
  [HasSheafify (stageTopology E i) Ab.{max u v + 1}]
  [HasSheafify (stageTopology E j) Ab.{max u v + 1}]
  [HasInjectiveResolutions (Sheaf (E.system.J i) Ab.{max u v + 1})]
  [HasInjectiveResolutions (Sheaf (E.system.J j) Ab.{max u v + 1})]
  [HasInjectiveResolutions (Sheaf (stageTopology E i) Ab.{max u v + 1})]
  [HasInjectiveResolutions (Sheaf (stageTopology E j) Ab.{max u v + 1})]
  [(levelPush E Ab.{max u v + 1} a).PreservesInjectiveObjects]
  [(stagePush E Ab.{max u v + 1} a).PreservesInjectiveObjects]
  [(levelEtaleRestrict E Ab.{max u v + 1} i).PreservesInjectiveObjects]
  [(levelEtaleRestrict E Ab.{max u v + 1} j).PreservesInjectiveObjects]

/-- **The cohomological base-change square of the levels of Stacks 0EYL.** Let `a : i ⟶ j` be an
arrow of the index category, `𝒢ᵢ` and `𝒢ⱼ` abelian sheaves on the small étale sites of the two
stages and `ψ : 𝒢ⱼ ⟶ (Xᵢ ⟶ Xⱼ)_* 𝒢ᵢ` a transition map between them, and let `V` be an object of the
level `j`. Then the square

```
Rᵖ Γ_V(level j, 𝒢ⱼ|)  ──transition──▶  Rᵖ Γ_{u_a V}(level i, 𝒢ᵢ|)
        │                                      │
   comparison                              comparison
        ▼                                      ▼
Rᵖ Γ(small étale Xⱼ, 𝒢ⱼ)  ──transition──▶  Rᵖ Γ(small étale Xᵢ, 𝒢ᵢ)
```

commutes, where every map is a Leray edge morphism and the right-hand column is read across the
pasted base-change square `levelEtaleSquare`.

This is the index-naturality of the comparison between the cohomology of the levels of Stacks
0EYL and the cohomology of the small étale sites of the stages. Its three ingredients are
`Stacks.Cohomology.RightDerivedEdge.edge_app_comp`,
`Stacks.Cohomology.RightDerivedEdge.map_comp_edge_app` — which is where `levelEtaleSquare`
enters — and the naturality of the edge morphism in the abelian sheaf. -/
theorem edge_levelEtaleSquare
    (𝒢i : Sheaf (stageTopology E i) Ab.{max u v + 1})
    (𝒢j : Sheaf (stageTopology E j) Ab.{max u v + 1})
    (ψ : 𝒢j ⟶ (stagePush E Ab.{max u v + 1} a).obj 𝒢i)
    (V : E.system.C j) (p : ℕ) :
    ((((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p).map
          ((levelEtaleRestrict E Ab.{max u v + 1} j).map ψ ≫
            (levelEtaleSquare E Ab.{max u v + 1} a).inv.app 𝒢i)) ≫
        (edge (levelPush E Ab.{max u v + 1} a)
            ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app
          ((levelEtaleRestrict E Ab.{max u v + 1} i).obj 𝒢i) ≫
          (edge (levelEtaleRestrict E Ab.{max u v + 1} i)
            (levelPush E Ab.{max u v + 1} a ⋙
              (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app 𝒢i =
      (edge (levelEtaleRestrict E Ab.{max u v + 1} j)
            ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app 𝒢j ≫
        (((levelEtaleRestrict E Ab.{max u v + 1} j ⋙
            (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p).map ψ) ≫
          (edge (stagePush E Ab.{max u v + 1} a)
              (levelEtaleRestrict E Ab.{max u v + 1} j ⋙
                (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app 𝒢i ≫
            (NatTrans.rightDerived (Functor.whiskerRight
              (levelEtaleSquare E Ab.{max u v + 1} a).inv
              ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V))) p).app 𝒢i := by
  have hnat : (((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p).map
          ((levelEtaleRestrict E Ab.{max u v + 1} j).map ψ) ≫
        (edge (levelEtaleRestrict E Ab.{max u v + 1} j)
            ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app
          ((stagePush E Ab.{max u v + 1} a).obj 𝒢i) =
      (edge (levelEtaleRestrict E Ab.{max u v + 1} j)
            ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).app 𝒢j ≫
        ((levelEtaleRestrict E Ab.{max u v + 1} j ⋙
          (sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p).map ψ :=
    (edge (levelEtaleRestrict E Ab.{max u v + 1} j)
      ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p).naturality ψ
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← edge_app_comp (levelEtaleRestrict E Ab.{max u v + 1} i) (levelPush E Ab.{max u v + 1} a)
      ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p 𝒢i,
    map_comp_edge_app ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V))
      (levelEtaleSquare E Ab.{max u v + 1} a).inv p 𝒢i,
    edge_app_comp (stagePush E Ab.{max u v + 1} a) (levelEtaleRestrict E Ab.{max u v + 1} j)
      ((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)) p 𝒢i]
  simp only [Category.assoc]
  rw [← Category.assoc, hnat]
  simp only [Category.assoc]

end Square

/-! ### The comparison with the stage is an isomorphism -/

section Comparison

variable (i : E.system.I)
  [HasSheafify (E.system.J i) Ab.{max u v + 1}]
  [HasSheafify (stageTopology E i) Ab.{max u v + 1}]
  [HasInjectiveResolutions (Sheaf (E.system.J i) Ab.{max u v + 1})]
  [HasInjectiveResolutions (Sheaf (stageTopology E i) Ab.{max u v + 1})]
  [(levelEtaleRestrict E Ab.{max u v + 1} i).IsEquivalence]

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The comparison between the cohomology of a level and the cohomology of the small étale site
of its stage is an isomorphism.** Restriction to the level is an equivalence of abelian sheaf
categories — the level equivalence of Stacks 0EYL followed by the affine inclusion of Stacks 04HR,
both dense subsite inclusions — hence exact and injective-preserving, so it carries an injective
resolution to an injective resolution and the edge morphism of
`Stacks.Cohomology.RightDerivedEdge.isIso_edge_app` is invertible. -/
theorem isIso_edge_levelEtaleRestrict {ℰ : Type*} [Category* ℰ] [Abelian ℰ]
    (S : Sheaf (E.system.J i) Ab.{max u v + 1} ⥤ ℰ) [S.Additive] (p : ℕ)
    (M : Sheaf (stageTopology E i) Ab.{max u v + 1}) :
    IsIso ((edge (levelEtaleRestrict E Ab.{max u v + 1} i) S p).app M) :=
  have hadj : (levelEtaleRestrict E Ab.{max u v + 1} i).inv ⊣
      levelEtaleRestrict E Ab.{max u v + 1} i :=
    (levelEtaleRestrict E Ab.{max u v + 1} i).asEquivalence.symm.toAdjunction
  have : (levelEtaleRestrict E Ab.{max u v + 1} i).inv.PreservesMonomorphisms := inferInstance
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms hadj
  isIso_edge_app (levelEtaleRestrict E Ab.{max u v + 1} i) S p M

end Comparison

end Stacks.EtaleCohomology.TransitionBaseChange

end
