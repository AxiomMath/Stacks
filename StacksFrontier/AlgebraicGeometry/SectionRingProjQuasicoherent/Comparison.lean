module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Basic

/-!
# Functoriality of the comparison with a quasi-coherent module on `Proj` of the section ring

In the situation of Stacks Tag 01QH — `X` a scheme, `L` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, L)` and `f : X ⟶ Proj S` the canonical morphism of Stacks Tag 01PZ — Stacks Tag
0B5I provides, for a module `ℱ` on `X` with graded module `M = Γ_*(X, L, ℱ)`, a comparison
morphism `M̃ ⟶ f_* ℱ` on `Proj S`, functorial in `ℱ`. Stacks Tag 01QJ asserts that the
transposed morphism `f^* M̃ ⟶ ℱ` is an isomorphism, functorially in `ℱ`.

**Clause (b) of Tag 01QJ — the functoriality — is what this file proves**: transposition along
the adjunction `f^* ⊣ f_*` carries a natural family `M̃ ⟶ f_* ℱ` to a natural family
`f^* M̃ ⟶ ℱ`. Since `f` is an open immersion (Stacks Tag 01Q1), the transposition can be run
through `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, whose adjunction has an explicit
counit, and transported to `f^*` along Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.restrictComparison`: the transposition through
  restriction along the open immersion `f`.
* `Stacks.SectionRingProjQuasicoherent.pullbackComparison`: **clause (b) of Stacks Tag 01QJ**,
  the comparison `f^* M̃ ⟶ ℱ` as a natural transformation in `ℱ`.

## Implementation notes

The sheaf-of-modules adjunctions are elaborated here rather than in the sibling file because
that file makes `TopCat.Sheaf`, `sheafCompose` and `ProjectiveSpectrum.top` reducible in order
to state the associated-sheaf functor on the scheme `Proj S`; with those reducibility settings
in force the definitional unfolding inside `restrictAdjunction` exhausts memory.

## References

* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Ample
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)

universe u

namespace Stacks.SectionRingProjQuasicoherent

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : IsAmple X L)

section Restrict

variable [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- **Tag 0B5I's comparison `M̃ ⟶ f_* ℱ`, transposed across the restriction adjunction.** For `f`
an open immersion, `AlgebraicGeometry.Scheme.Modules.restrictFunctor f` is left adjoint to `f_*`
with an explicit counit, so a morphism `M̃ ⟶ f_* ℱ` transposes to `M̃|_X ⟶ ℱ`; transposition
along an adjunction is natural, which is the naturality proved here. -/
def restrictComparison
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL)) :
    tildeFunctor L ⋙ Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL) ⟶ 𝟭 X.Modules where
  app A := (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map (c.app A) ≫
    (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).counit.app A
  naturality A B φ := by
    have hc : (tildeFunctor L).map φ ≫ c.app B =
        c.app A ≫ (Scheme.Modules.pushforward (projHomOfIsAmple L hL)).map φ := c.naturality φ
    have hu := (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).counit.naturality φ
    dsimp only [Functor.comp_map, Functor.id_map] at hu ⊢
    rw [← Category.assoc, ← Functor.map_comp, hc, Functor.map_comp, Category.assoc, hu,
      ← Category.assoc]

end Restrict

/-- **Clause (b) of Stacks Tag 01QJ: the comparison `f^* M̃ ⟶ ℱ` is functorial in `ℱ`.**

Stacks Tag 0B5I supplies, for each `ℱ`, a morphism `M̃ ⟶ f_* ℱ` on `Proj Γ_*(X, L)` functorial
in `ℱ`, where `M = Γ_*(X, L, ℱ)`; that family is the hypothesis `c`. Transposing it along the
adjunction `f^* ⊣ f_*` gives a morphism `f^* M̃ ⟶ ℱ` for each `ℱ`, and transposition is natural,
so the transposed family is again functorial in `ℱ`. -/
@[stacks 01QJ "clause (b): the comparison `f^*M̃ ⟶ ℱ` is functorial in `ℱ`, carrying Tag 0B5I's
morphism `M̃ ⟶ f_*ℱ` for the twisted-section module as the hypothesis `c`"]
def pullbackComparison
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL)) :
    pullbackTildeFunctor L hL ⟶ 𝟭 X.Modules :=
  haveI : IsOpenImmersion (projHomOfIsAmple L hL) :=
    Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  (Functor.isoWhiskerLeft (tildeFunctor L)
      (Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL))).inv ≫
    restrictComparison L hL c

end Stacks.SectionRingProjQuasicoherent

end
