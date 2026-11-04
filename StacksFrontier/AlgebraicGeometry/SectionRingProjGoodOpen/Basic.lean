module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Reverse
public import StacksFrontier.AlgebraicGeometry.ProjShared.InvertibleLocus
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.FromAmple
public import StacksFrontier.Algebra.DirectSum.ExternalGrading

/-!
# The canonical morphism lands in the good open: Stacks Tag 01QI

Situation Stacks Tag 01QH: `X` is a scheme, `L` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, L)` the graded section ring of Stacks Tag 01CV, `Y = Proj S`, and
`f : X ⟶ Y` the canonical morphism of Stacks Tag 01PZ
(`Stacks.SectionRingProjMorphism.projHomOfIsAmple`).

Stacks Tag 01QI's first claim is that `f` maps `X` into the open `W = W_1 ⊆ Y` of Stacks Tag
01MU, the largest open on which `𝒪_Y(1)` is invertible and all multiplication maps
`𝒪_Y(n) ⊗ 𝒪_Y(m) → 𝒪_Y(n + m)` are isomorphisms. That open is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible (grading L) 1`, and this file
proves `f ⁻¹ᵁ W_1 = ⊤`.

## Main results

* `Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible`: **the canonical
  morphism of Stacks Tag 01PZ factors through `W_1`.**

## Implementation notes

Stacks Tag 01MU identifies `W_1` with the union of the standard opens `D₊(a b)` for `a`, `b`
homogeneous with `deg a = deg b + 1` (`Stacks.AlgebraicGeometry.ProjShared.ratioLocus`), and that
identification (`Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_ratioLocus`) is what
makes the claim checkable pointwise: it is enough to produce, at every point `x` of `X`, *two
homogeneous sections of consecutive degrees* neither of which vanishes at `x`. The preimage of
`D₊(a b)` is then the nonvanishing open `X_{ab} = X_a ∩ X_b` by clause (1) of Stacks Tag 01PZ
(`Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen`), and `x` lies in it.

**Consecutive degrees are the whole difficulty, and ampleness supplies them in the form of
eventual finite generation.** A single degree would not do: `W_1` asks for a pair with
`deg a = deg b + 1`. What is used is
`Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple` — the first half of clause (7)
of Stacks Tag 01Q3 — which gives an `n₀` beyond which *every* tensor power `L ^⊗ n` is generated
by global sections; applying it at two consecutive degrees `e` and `e + 1` above `n₀`, and then
picking from each generating family a member not vanishing at `x`
(`Stacks.SheafOfModules.exists_generatingSection_nonvanishing`), produces the pair. The
finiteness of the generating families is not needed anywhere here.

Three vocabularies for "does not vanish at `x`" meet in this file and are crossed in
`Stacks.SectionRingProjGoodOpen.exists_powSections_mem_nvLocus_of_isFinGen`:
`Stacks.SheafOfModules.nonvanishingOpen` of a restriction-compatible family, which is what
generating sections come as; `Stacks.Ample.nonvanishingLocus` of a global section, which the two
are joined by in `Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval`; and
`Stacks.AmpleFiniteAvoidance.nvLocus` of a homogeneous element of the section ring, reached by
`Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`. The last is the vocabulary clause
(1) of Stacks Tag 01PZ speaks.

No degree transport is needed: `W_1`'s index shape is `𝒮 (e + 1)` against `𝒮 e`, which is
literally the pair of degrees produced, and the product has degree `(e + 1) + e`.

## References

* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)

## What is not done

**The second claim of Stacks Tag 01QI is not addressed.** That claim is that the pullbacks
`f^* 𝒪_Y(n) → L ^⊗ n` are isomorphisms; the comparison map it speaks of does not exist in this
repository, so neither the map nor the claim is stated here, and the attribute written below is
scoped by its clause string to the first claim alone.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.GradedSections (powSections)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)

universe u

namespace Stacks.SectionRingProjGoodOpen

section Monoidal

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

/-! ### From generation in a degree to a homogeneous section of that degree -/

/-- **Where `L ^⊗ n` is generated by global sections, every point has a homogeneous element of
the section ring of degree `n` not vanishing there.** Only the existence of a generating family
is used, not its finiteness.

This crosses the three nonvanishing vocabularies at once: the generating section is a
restriction-compatible family, `Stacks.SheafOfModules.exists_generatingSection_nonvanishing`
places `x` in its bundled nonvanishing open,
`Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval` reads that open as the nonvanishing locus
of the corresponding global section, and
`Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq` replaces the global section by a
homogeneous element of `Γ_*(X, L)` with the same locus. -/
public theorem exists_powSections_mem_nvLocus_of_isFinGen {n : ℕ}
    (h : Stacks.AmpleEventualGeneration.IsFinGen (Stacks.Ample.tensorPowModule X L (n : ℤ)))
    (x : X) : ∃ a : powSections L n, x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L a := by
  obtain ⟨σ, -⟩ := h
  obtain ⟨i, hi⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing
    (Stacks.Ample.tensorPowModule X L (n : ℤ)) σ x
  obtain ⟨a, ha⟩ := Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq L n
    ((σ.s i).eval (op ⊤))
  refine ⟨a, ?_⟩
  rw [ha, ← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X
    (Stacks.Ample.tensorPowModule X L (n : ℤ)) (σ.s i)]
  exact hi

/-- **For `L` ample every point has a pair of homogeneous elements of the section ring of
consecutive degrees, neither vanishing there.** This is the input `W_1` needs, and it is where
ampleness is spent, through eventual finite generation of the tensor powers
(`Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple`, the first half of clause (7)
of Stacks Tag 01Q3): generation holds in all degrees above some `n₀`, so in particular in the two
consecutive degrees `e` and `e + 1` for any natural `e` with `n₀ ≤ e`. -/
private theorem exists_consecutive_mem_nvLocus (hL : Stacks.Ample.IsAmple X L) (x : X) :
    ∃ (e : ℕ) (a : powSections L (e + 1)) (b : powSections L e),
      x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L a ∧
        x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L b := by
  obtain ⟨n₀, hgen⟩ := Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple L hL
  obtain ⟨e, he⟩ : ∃ e : ℕ, n₀ ≤ (e : ℤ) := ⟨n₀.toNat, Int.self_le_toNat n₀⟩
  obtain ⟨a, ha⟩ := exists_powSections_mem_nvLocus_of_isFinGen L (n := e + 1)
    (hgen ((e + 1 : ℕ) : ℤ) (by push_cast; omega)) x
  obtain ⟨b, hb⟩ := exists_powSections_mem_nvLocus_of_isFinGen L (n := e) (hgen (e : ℤ) he) x
  exact ⟨e, a, b, ha, hb⟩

/-! ### Tag 01QI's first claim -/

/-- **Stacks Tag 01QI, first claim: the canonical morphism of Stacks Tag 01PZ maps `X` into the
good open `W_1`.** In the situation of Stacks Tag 01QH — `L` ample on `X`, `S = Γ_*(X, L)`,
`Y = Proj S` — the morphism `f : X ⟶ Y` of Stacks Tag 01PZ pulls the open `W_1 ⊆ Y` of Stacks
Tag 01MU back to all of `X`.

The proof is pointwise. Stacks Tag 01MU's identity
`Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_ratioLocus` turns `W_1` into the union
of the standard opens `D₊(a b)` with `deg a = deg b + 1`; ampleness provides at each point a pair
of homogeneous sections of consecutive degrees `e + 1` and `e` not vanishing there
(`Stacks.SectionRingProjGoodOpen.exists_consecutive_mem_nvLocus`); their product is a homogeneous
element of degree `(e + 1) + e` not vanishing there
(`Stacks.AmpleFiniteAvoidance.nvLocus_mul`); and clause (1) of Stacks Tag 01PZ
(`Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen`) identifies the
preimage of `D₊` of that product with the nonvanishing open, which therefore contains the
point. -/
@[stacks 01QI "the canonical morphism lands in the good open W₁"]
public theorem projHomOfIsAmple_preimage_whereInvertible (hL : Stacks.Ample.IsAmple X L) :
    Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL ⁻¹ᵁ
        Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible (grading L) 1 = ⊤ := by
  rw [Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_ratioLocus]
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨e, a, b, ha, hb⟩ := exists_consecutive_mem_nvLocus L hL x
  have hd : 0 < e + 1 + e := by omega
  have hprod : x ∈ nvOpen L (Stacks.GradedSections.mul a b) := by
    have hset : x ∈ (nvOpen L (Stacks.GradedSections.mul a b) : Set X) := by
      rw [Stacks.AmpleFiniteAvoidance.coe_nvOpen, Stacks.AmpleFiniteAvoidance.nvLocus_mul]
      exact ⟨ha, hb⟩
    exact hset
  have hmul : DirectSum.of (powSections L) (e + 1) a * DirectSum.of (powSections L) e b
      = DirectSum.of (powSections L) (e + 1 + e) (Stacks.GradedSections.mul a b) := by
    rw [DirectSum.of_mul_of, Stacks.GradedSections.gMul_def]
  have hbasic : Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL x ∈
      Proj.basicOpen (grading L)
        (DirectSum.of (powSections L) (e + 1) a * DirectSum.of (powSections L) e b) := by
    have hpre : x ∈ Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL ⁻¹ᵁ
        Proj.basicOpen (grading L)
          (DirectSum.of (powSections L) (e + 1 + e) (Stacks.GradedSections.mul a b)) := by
      rw [Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL _ hd]
      exact hprod
    rw [hmul]
    exact hpre
  exact Stacks.AlgebraicGeometry.ProjShared.basicOpen_mul_le_ratioLocus (grading L) (d := 1)
    (e := e) (Stacks.ExternalGrading.of_mem_summand (e + 1) a)
    (Stacks.ExternalGrading.of_mem_summand e b) hbasic

end Monoidal

end Stacks.SectionRingProjGoodOpen

end
