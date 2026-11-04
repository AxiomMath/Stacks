module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistSquare

/-!
# The twist square of Stacks Tag 01QK is equivalent to the multiplication-compatibility of `c`

In the situation of Stacks Tag 01QH — `X` a scheme, `𝓛` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, 𝓛)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism of Stacks Tag 01PZ —
Stacks Tag 01QJ produces for each `𝓕` a comparison `θ_𝓕 : f^* M̃ ⟶ 𝓕`, and the second assertion
of the Remark Tag 01QK is that the square

```
      f^*M̃ ⊗_{𝒪_X} f^*𝒪_Y(n)  ────▶  f^*(M(n)~)
               │                            │
     θ_𝓕 ⊗ θ_{𝓛^{⊗n}}              θ_{𝓕 ⊗ 𝓛^{⊗n}}
               ▼                            ▼
         𝓕 ⊗ 𝓛^{⊗n}  ──── id ────▶   𝓕 ⊗ 𝓛^{⊗n}
```

commutes. `StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistSquare.lean` derives the
square, at the Tag 01QJ comparison
`Stacks.SectionRingProjQuasicoherent.pullbackComparison L hL c`, from the hypothesis

```
    hmul : mult ≫ c.app (𝓕 ⊗ 𝓖) = (c.app 𝓕 ⊗ₘ c.app 𝓖) ≫ μ (f_*) 𝓕 𝓖
```

on Tag 0B5I's family `c`, as `Stacks.SectionRingProjTheta.pullbackComparison_tensorHom`.

This file proves the converse, so that `hmul` and the square are one statement read on the two
sides of the adjunction `f^{-1} ⊣ f_*`: the Remark's square is a multiplication-compatibility of
`c` on `Proj Γ_*(X, L)`.

## Main results

* `Stacks.SectionRingProjTheta.conjugated_square_iff`: conjugating the square by isomorphisms
  of its three upper corners loses nothing; the converse of `conjugated_square`.
* `Stacks.SectionRingProjTheta.restrictComparison_tensorHom_iff`: the equivalence at
  `Stacks.SectionRingProjQuasicoherent.restrictComparison`, the family the Tag 01QJ comparison is
  defined from. It is `tensorHom_eq_of_mulComm` paired with its converse
  `mulComm_of_tensorHom_eq`.
* `Stacks.SectionRingProjTheta.pullbackComparison_tensorHom_iff_mulComm`: the equivalence at
  the Tag 01QJ comparison `pullbackComparison`, with the top arrow `pullbackTwistTop` built from
  `mult`.

## Implementation notes

The proof of `pullbackComparison_tensorHom_iff_mulComm` follows that of
`pullbackComparison_tensorHom` exactly: the two `rfl` lemmas `pullbackComparison_app` and
`pullbackTwistTop_eq` are rewritten into the goal first, so that the kernel is never asked to
unfold `Stacks.SectionRingProjQuasicoherent.pullbackTildeFunctor` at three corners at once.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

open Stacks.Ample
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (tildeFunctor pullbackTildeFunctor restrictComparison
  pullbackComparison)

universe v₁ u₁ u

namespace Stacks.SectionRingProjTheta

section Conjugate

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- **The conjugation of `conjugated_square` loses nothing**: the conjugated square holds exactly
when the original one does. The converse direction composes with `wA.inv ⊗ₘ wB.inv` on the left,
which is possible because the three comparisons are isomorphisms. -/
theorem conjugated_square_iff {A A' B B' R R' P Q : C} (wA : A ≅ A') (wB : B ≅ B') (wR : R ≅ R')
    (m : A' ⊗ B' ⟶ R') (θA : A' ⟶ P) (θB : B' ⟶ Q) (θR : R' ⟶ P ⊗ Q) :
    ((wA.hom ≫ θA) ⊗ₘ (wB.hom ≫ θB)
        = ((wA.hom ⊗ₘ wB.hom) ≫ m ≫ wR.inv) ≫ (wR.hom ≫ θR))
      ↔ θA ⊗ₘ θB = m ≫ θR := by
  refine ⟨fun h => ?_, conjugated_square wA wB wR m θA θB θR⟩
  simp only [← tensorHom_comp_tensorHom, Category.assoc, Iso.inv_hom_id_assoc] at h
  exact (cancel_epi (wA.hom ⊗ₘ wB.hom)).1 h

end Conjugate

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : IsAmple X L)

section Restrict

variable [IsOpenImmersion (projHomOfIsAmple L hL)]
  [(Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).Monoidal]
  [(Scheme.Modules.pushforward (projHomOfIsAmple L hL)).LaxMonoidal]
  [(Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).IsMonoidal]

/-- **The square at the restriction spelling of `θ` is equivalent to the
multiplication-compatibility of `c`.**

`Stacks.SectionRingProjQuasicoherent.restrictComparison L hL c |>.app 𝓕` is by definition the
transpose of `c.app 𝓕` across `Scheme.Modules.restrictAdjunction`, so this is
`tensorHom_eq_of_mulComm` paired with its converse `mulComm_of_tensorHom_eq`, with no transport
at all. Its `mpr` half is `restrictComparison_tensorHom`. -/
theorem restrictComparison_tensorHom_iff
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F G : X.Modules)
    (mult : (tildeFunctor L).obj F ⊗ (tildeFunctor L).obj G ⟶ (tildeFunctor L).obj (F ⊗ G)) :
    ((restrictComparison L hL c).app F ⊗ₘ (restrictComparison L hL c).app G
        = μ (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL))
              ((tildeFunctor L).obj F) ((tildeFunctor L).obj G) ≫
            (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map mult ≫
              (restrictComparison L hL c).app (F ⊗ G))
      ↔ mult ≫ c.app (F ⊗ G) = (c.app F ⊗ₘ c.app G) ≫
          μ (Scheme.Modules.pushforward (projHomOfIsAmple L hL)) F G :=
  ⟨mulComm_of_tensorHom_eq (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL))
      mult (c.app F) (c.app G) (c.app (F ⊗ G)),
    tensorHom_eq_of_mulComm (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL))
      mult (c.app F) (c.app G) (c.app (F ⊗ G))⟩

/-- **The square at the Tag 01QJ comparison is equivalent to the
multiplication-compatibility of Tag 0B5I's family.**

This is `restrictComparison_tensorHom_iff` conjugated by the crossing isomorphism at each of the
three upper corners, which `conjugated_square_iff` shows loses nothing. Its `mpr` half is
`pullbackComparison_tensorHom`: the hypothesis `hmul` of that declaration and its conclusion are
one statement, read on the two sides of the adjunction. -/
theorem pullbackComparison_tensorHom_iff_mulComm
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F G : X.Modules)
    (mult : (tildeFunctor L).obj F ⊗ (tildeFunctor L).obj G ⟶ (tildeFunctor L).obj (F ⊗ G)) :
    ((pullbackComparison L hL c).app F ⊗ₘ (pullbackComparison L hL c).app G
        = pullbackTwistTop L hL F G mult ≫ (pullbackComparison L hL c).app (F ⊗ G))
      ↔ mult ≫ c.app (F ⊗ G) = (c.app F ⊗ₘ c.app G) ≫
          μ (Scheme.Modules.pushforward (projHomOfIsAmple L hL)) F G := by
  rw [pullbackComparison_app L hL c F, pullbackComparison_app L hL c G,
    pullbackComparison_app L hL c (F ⊗ G), pullbackTwistTop_eq]
  refine Iff.trans (conjugated_square_iff (pullbackTildeCrossIso L hL F)
    (pullbackTildeCrossIso L hL G) (pullbackTildeCrossIso L hL (F ⊗ G))
    (μ (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)) ((tildeFunctor L).obj F)
        ((tildeFunctor L).obj G) ≫
      (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map mult)
    ((restrictComparison L hL c).app F) ((restrictComparison L hL c).app G)
    ((restrictComparison L hL c).app (F ⊗ G))) ?_
  rw [Category.assoc]
  exact restrictComparison_tensorHom_iff L hL c F G mult

end Restrict

end Scheme

end Stacks.SectionRingProjTheta

end
