module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic

/-!
# The morphism `φ_{(L, (s₀, …, sₙ))}` is natural in the source, and is stable under base change

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s₀, …, sₙ` global sections of `L`
generating it. Section 27.13 attaches to this datum the morphism
`φ_{(L, (s₀, …, sₙ))} : X ⟶ ℙⁿ_S` over a base `S`
(`Stacks.ProjectiveFromSections.toProjectiveSpaceOver`). This file proves the two statements that
identify that morphism after a base change of the whole situation.

The first is naturality in the source scheme: for `h : Y ⟶ X` the composite
`h ≫ φ_{(L, (s₀, …, sₙ))}` is the morphism attached to the pulled back module `h^* L` with the
pulled back sections `h^* s₀, …, h^* sₙ`, read on the integral model `ℙⁿ_ℤ` where no base
intervenes. The second is the geometric consequence over a base: if `X' = X ×_S S'` is the base
change of `X` along `S' ⟶ S`, then the square

```
X'  --φ'-->  ℙⁿ_{S'}
|               |
v               v
X   --φ-->   ℙⁿ_S
```

whose right vertical arrow is `AlgebraicGeometry.projectiveSpaceOverMap` is cartesian — `φ'` is
the base change of `φ`. Every property of morphisms stable under base change therefore passes
from `φ` to `φ'`; this is what lets hypothesis (3) of [Stacks, Tag 0FD6] — that `φ` is an
immersion — be transported to a base-changed situation.

## Main results

* `Stacks.ProjectiveFromSections.comp_toProjectiveSpaceAtUniverse`: naturality in the source
  scheme, on the integral model.
* `Stacks.ProjectiveFromSections.comp_toProjectiveSpaceOver`: the same over a base, as the
  commuting square above.
* `Stacks.ProjectiveFromSections.isPullback_toProjectiveSpaceOver`: that square is cartesian.
* `Stacks.ProjectiveFromSections.isImmersion_toProjectiveSpaceOver_of_isPullback`: an immersion
  stays an immersion after base change of the situation.

## Implementation notes

Naturality is not proved by comparing the glueings. It is read off the representability of
[Stacks, Tag 01NE], which is formalized as `Stacks.ProjectiveSpaceModuli.pointsEquiv` together with
its naturality `Stacks.ProjectiveSpaceModuli.pointsOfHom_comp`: a morphism to `ℙⁿ_ℤ` is
determined by the pair `(L, (s₀, …, sₙ))` it pulls the tautological pair back to, the glued
morphism of `Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse` is *pinned* by its own
pair (that is exactly `Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse`), and the
pullback of the pair along `h` is the pair of the pulled back sections by construction
(`Stacks.ProjectiveSpaceModuli.pullbackTuple`). So both sides of the naturality statement
classify the same pair, and the injectivity half of Tag 01NE identifies them. No statement about
ratios of sections, and no comparison of charts, is needed.

The invertibility of the pulled back module is needed to state the right hand side at all, and
[Stacks, Tag 0B8L] supplies it; the instance is reached from the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling through
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.isInvertibleModule_schemeModulesPullback`,
which is why that module is imported.

Over a base nothing more happens: `ℙⁿ_S` is a fibre product over the terminal scheme, so a
morphism into it is a pair of a morphism to `S` and a morphism to `ℙⁿ_ℤ`
(`Stacks.AmpleProjectiveImmersion.liftOver`), the first components agree because `X'` lies over
`S'`, and the second components agree by naturality. Cartesianness is then pullback cancellation
against the cartesian square of `AlgebraicGeometry.isPullback_projectiveSpaceOverMap`.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveFromSections

variable {X Y : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}
  (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)

/-- The class of the pair `(L, (s₀, …, sₙ))` is the point classified by its glued morphism. -/
private theorem pointsOfHom_toProjectiveSpaceAtUniverse
    (t : Stacks.ProjectiveSpaceModuli.GeneratingTuple X n) :
    Stacks.ProjectiveSpaceModuli.pointsOfHom (toProjectiveSpaceAtUniverse t.coord t.generates) =
      ⟦t⟧ :=
  Quotient.sound (Stacks.ProjectiveSpaceModuli.isomorphic_tautological_of_isPinned
    (t := t) fun i => ι_toProjectiveSpaceAtUniverse t.coord t.generates i)

/-- **The morphism to the integral model is natural in the source scheme.** For `h : Y ⟶ X` the
composite `h ≫ φ_{(L, (s₀, …, sₙ))}` is the morphism attached to the pulled back module with the
pulled back sections.

Both sides classify the same pair of [Stacks, Tag 01NE]: the left one because the pair of a
composite is the pullback of the pair (`Stacks.ProjectiveSpaceModuli.pointsOfHom_comp`), the
right one because the glued morphism is pinned by the pair it is built from. -/
theorem comp_toProjectiveSpaceAtUniverse (h : Y ⟶ X)
    (hs' : GeneratesStalks fun i => pullbackGlobalSections h L (s i)) :
    h ≫ toProjectiveSpaceAtUniverse s hs =
      toProjectiveSpaceAtUniverse (fun i => pullbackGlobalSections h L (s i)) hs' := by
  let t : Stacks.ProjectiveSpaceModuli.GeneratingTuple X n := ⟨L, ‹_›, s, hs⟩
  refine Stacks.ProjectiveSpaceModuli.pointsOfHom_injective ?_
  rw [Stacks.ProjectiveSpaceModuli.pointsOfHom_comp,
    pointsOfHom_toProjectiveSpaceAtUniverse t,
    Stacks.ProjectiveSpaceModuli.pullbackPoints_mk]
  exact (pointsOfHom_toProjectiveSpaceAtUniverse
    (Stacks.ProjectiveSpaceModuli.pullbackTuple h t)).symm

variable {S S' : Scheme.{u}} (f : X ⟶ S) {u : S' ⟶ S} {g : Y ⟶ X} {f' : Y ⟶ S'}

/-- **The base change of the situation commutes with `φ_{(L, (s₀, …, sₙ))}`.** If `Y` lies over
`S'` and `g : Y ⟶ X` lies over `u : S' ⟶ S`, the morphism attached to the pulled back sections
followed by `ℙⁿ_{S'} ⟶ ℙⁿ_S` is `g` followed by the morphism attached to the original ones.

Both sides are morphisms into a fibre product over the terminal scheme; the components over the
base agree because the square `(g, f', f, u)` commutes, and the components on the integral model
agree by `Stacks.ProjectiveFromSections.comp_toProjectiveSpaceAtUniverse`. -/
theorem comp_toProjectiveSpaceOver (hsq : g ≫ f = f' ≫ u)
    (hs' : GeneratesStalks fun i => pullbackGlobalSections g L (s i)) :
    toProjectiveSpaceOver (fun i => pullbackGlobalSections g L (s i)) hs' f' ≫
        projectiveSpaceOverMap n u =
      g ≫ toProjectiveSpaceOver s hs f := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc,
      toProjectiveSpaceOver_fst, Category.assoc, toProjectiveSpaceOver_fst, hsq]
  · rw [Category.assoc,
      show projectiveSpaceOverMap n u ≫ pullback.snd (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        projectiveSpaceOver.toIntegralAtUniverse n S' from projectiveSpaceOverMap_snd n u,
      toProjectiveSpaceOver_snd, Category.assoc,
      show toProjectiveSpaceOver s hs f ≫ pullback.snd (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        toProjectiveSpaceAtUniverse s hs from toProjectiveSpaceOver_snd s hs f,
      comp_toProjectiveSpaceAtUniverse s hs g hs']

/-- **`φ_{(L, (s₀, …, sₙ))}` is stable under base change of the situation.** If `Y = X ×_S S'`,
then the morphism `Y ⟶ ℙⁿ_{S'}` attached to the pulled back sections is the base change of
`φ_{(L, (s₀, …, sₙ))} : X ⟶ ℙⁿ_S` along `ℙⁿ_{S'} ⟶ ℙⁿ_S`.

Pasted onto the cartesian square of `AlgebraicGeometry.isPullback_projectiveSpaceOverMap` the
square below is the cartesian square of `Y`, because both morphisms to projective space lie over
the respective bases. -/
theorem isPullback_toProjectiveSpaceOver (hpb : IsPullback g f' f u)
    (hs' : GeneratesStalks fun i => pullbackGlobalSections g L (s i)) :
    IsPullback (toProjectiveSpaceOver (fun i => pullbackGlobalSections g L (s i)) hs' f') g
      (projectiveSpaceOverMap n u) (toProjectiveSpaceOver s hs f) := by
  refine IsPullback.of_right ?_ (comp_toProjectiveSpaceOver s hs f hpb.w hs')
    (isPullback_projectiveSpaceOverMap n u).flip
  rw [toProjectiveSpaceOver_fst, toProjectiveSpaceOver_fst]
  exact hpb.flip

/-- **An immersion stays an immersion after base change of the situation.** Hypothesis (3) of
[Stacks, Tag 0FD6] for a base-changed situation, granted it for the original one: the two
morphisms to projective space sit in a cartesian square, and
`AlgebraicGeometry.IsImmersion` is stable under base change. -/
theorem isImmersion_toProjectiveSpaceOver_of_isPullback (hpb : IsPullback g f' f u)
    (hs' : GeneratesStalks fun i => pullbackGlobalSections g L (s i))
    [IsImmersion (toProjectiveSpaceOver s hs f)] :
    IsImmersion (toProjectiveSpaceOver (fun i => pullbackGlobalSections g L (s i)) hs' f') :=
  MorphismProperty.of_isPullback
    (isPullback_toProjectiveSpaceOver s hs f hpb hs').flip inferInstance

end Stacks.ProjectiveFromSections

end
