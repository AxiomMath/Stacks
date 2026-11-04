module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Unramified.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of formal smoothness along a faithfully flat intermediate algebra

Let `R → B → C` be commutative ring maps with `C` faithfully flat over `B`. If `R → C` and
`B → C` are formally smooth, then `R → B` is formally smooth. This file proves the Kähler
differential half of that statement, which is the part the naive cotangent complex in Mathlib
can see.

Write `Ω` for Kähler differentials. Formal smoothness of `B → C` makes the Jacobi–Zariski
sequence of `R → B → C` into a short exact sequence
```
0 → C ⊗[B] Ω[B⁄R] → Ω[C⁄R] → Ω[C⁄B] → 0
```
which is split because `Ω[C⁄B]` is projective. Formal smoothness of `R → C` then makes
`C ⊗[B] Ω[B⁄R]` a direct summand of the projective module `Ω[C⁄R]`, and faithfully flat descent
of flatness turns this into flatness of `Ω[B⁄R]` over `B`.

## Main results

* `injective_mapBaseChange`: `C ⊗[B] Ω[B⁄R] → Ω[C⁄R]` is injective as soon as `H¹(L_{C/B})`
  vanishes, e.g. when `B → C` is formally smooth.
* `exists_splitting_kaehlerDifferential`: the splitting `Ω[C⁄R] ≃ C ⊗[B] Ω[B⁄R] × Ω[C⁄B]`.
* `projective_tensorProduct_kaehlerDifferential`: `C ⊗[B] Ω[B⁄R]` is a projective `C`-module.
* `flat_kaehlerDifferential`: `Ω[B⁄R]` is a flat `B`-module.
* `formallyUnramified_of_faithfullyFlat`: formal unramifiedness of `R → B`, assuming it for
  `R → C` and with no extra hypotheses.
* `formallySmooth_of_subsingleton_tensorProduct_h1Cotangent` and
  `formallySmooth_of_subsingleton_h1Cotangent`: formal smoothness of `R → B`, under the two
  extra hypotheses discussed below.

## Implementation notes

`Algebra.FormallySmooth R B` unfolds (tag 031I, `Algebra.formallySmooth_iff`) to two conditions:
`Ω[B⁄R]` is a projective `B`-module and `H¹(L_{B/R})` vanishes. Neither follows from the
hypotheses with the API currently available, and `formallySmooth_of_subsingleton_h1Cotangent`
therefore carries two extra hypotheses.

* Projectivity. What descends along a faithfully flat ring map in Mathlib is flatness
  (`Module.Flat.of_flat_tensorProduct`), not projectivity; descent of projectivity is the
  theorem of Raynaud and Gruson (tag 058B), which Mathlib does not have — see the TODO in
  `Mathlib/RingTheory/Etale/Descent.lean`. So `Module.FinitePresentation B Ω[B⁄R]` is assumed
  and `Module.Flat.projective_of_finitePresentation` is used, exactly as in that file. For a
  morphism locally of finite presentation the differentials of the stalks are finitely
  presented, so the hypothesis is harmless in the intended scheme-level application.
* Vanishing of `H¹(L_{B/R})`. Mathlib's Jacobi–Zariski sequence stops at `H¹` of the *naive*
  cotangent complex, and `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat` gives exactness
  of `C ⊗[B] H¹(L_{B/R}) → H¹(L_{C/R}) → H¹(L_{C/B})` at the middle term only. Deducing
  `C ⊗[B] H¹(L_{B/R}) = 0` from `H¹(L_{C/R}) = 0` needs injectivity of the left map, i.e. the
  vanishing of `H²(L_{C/B})`, which is where formal smoothness of `B → C` would enter and
  which is not expressible with the naive complex. Mathlib proves the corresponding injectivity
  only when `B → C` is a localization away from an element
  (`Algebra.Generators.liftBaseChange_injective_of_isLocalizationAway`, tag 08JZ). So the
  vanishing of `C ⊗[B] H¹(L_{B/R})`, equivalently of `H¹(L_{B/R})`, is assumed; everything else
  in the descent is proved here.

## References

* [Stacks Project, Tag 02K6](https://stacks.math.columbia.edu/tag/02K6)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 031I](https://stacks.math.columbia.edu/tag/031I)
* [Stacks Project, Tag 058B](https://stacks.math.columbia.edu/tag/058B)
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Stacks.RingTheory.FormallySmoothDescent

variable (R : Type u) (B : Type v) (C : Type w) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]

/-- If `H¹(L_{C/B})` vanishes, the Jacobi–Zariski sequence of `R → B → C` starts with an
injection `C ⊗[B] Ω[B⁄R] → Ω[C⁄R]`: the connecting map into `C ⊗[B] Ω[B⁄R]` has subsingleton
source, so the kernel of `KaehlerDifferential.mapBaseChange` is trivial. -/
theorem injective_mapBaseChange [Subsingleton (Algebra.H1Cotangent B C)] :
    Function.Injective (KaehlerDifferential.mapBaseChange R B C) := by
  have hδ : Algebra.H1Cotangent.δ R B C = 0 := by
    ext x
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  rw [← LinearMap.ker_eq_bot,
    (Algebra.H1Cotangent.exact_δ_mapBaseChange R B C).linearMap_ker_eq, hδ,
    LinearMap.range_zero]

/-- For `B → C` formally smooth, the Jacobi–Zariski sequence of `R → B → C` is a split short
exact sequence `0 → C ⊗[B] Ω[B⁄R] → Ω[C⁄R] → Ω[C⁄B] → 0`: it is exact on the left by
`injective_mapBaseChange`, surjective on the right by `KaehlerDifferential.map_surjective`, and
it splits because `Ω[C⁄B]` is a projective `C`-module. -/
@[ega "0 20.7.2" "special case", sga "6 VIII 2.6" "partial"]
theorem exists_splitting_kaehlerDifferential [Algebra.FormallySmooth B C] :
    ∃ e : Ω[C⁄R] ≃ₗ[C] (C ⊗[B] Ω[B⁄R]) × Ω[C⁄B],
      KaehlerDifferential.mapBaseChange R B C =
          e.symm.toLinearMap ∘ₗ LinearMap.inl C (C ⊗[B] Ω[B⁄R]) Ω[C⁄B] ∧
        KaehlerDifferential.map R B C C =
          LinearMap.snd C (C ⊗[B] Ω[B⁄R]) Ω[C⁄B] ∘ₗ e.toLinearMap := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (KaehlerDifferential.map R B C C)
    (LinearMap.id (R := C) (M := Ω[C⁄B])) (KaehlerDifferential.map_surjective R B C)
  exact ⟨_, ((KaehlerDifferential.exact_mapBaseChange_map R B C).splitSurjectiveEquiv
    (injective_mapBaseChange R B C) ⟨l, hl⟩).2⟩

/-- If `R → C` and `B → C` are formally smooth, then `C ⊗[B] Ω[B⁄R]` is a projective
`C`-module, being a direct summand of the projective module `Ω[C⁄R]`. -/
theorem projective_tensorProduct_kaehlerDifferential [Algebra.FormallySmooth R C]
    [Algebra.FormallySmooth B C] : Module.Projective C (C ⊗[B] Ω[B⁄R]) := by
  obtain ⟨e, he, -⟩ := exists_splitting_kaehlerDifferential R B C
  refine Module.Projective.of_split (KaehlerDifferential.mapBaseChange R B C)
    (LinearMap.fst C (C ⊗[B] Ω[B⁄R]) Ω[C⁄B] ∘ₗ e.toLinearMap) ?_
  rw [he]
  ext x
  simp

/-- If `C` is faithfully flat over `B` and `R → C` and `B → C` are formally smooth, then
`Ω[B⁄R]` is a flat `B`-module: its base change `C ⊗[B] Ω[B⁄R]` is projective, hence flat, and
flatness descends along faithfully flat ring maps. -/
theorem flat_kaehlerDifferential [Module.FaithfullyFlat B C] [Algebra.FormallySmooth R C]
    [Algebra.FormallySmooth B C] : Module.Flat B Ω[B⁄R] :=
  have : Module.Projective C (C ⊗[B] Ω[B⁄R]) := projective_tensorProduct_kaehlerDifferential R B C
  Module.Flat.of_flat_tensorProduct B Ω[B⁄R] C

/-- The projectivity half of formal smoothness of `R → B`, under the extra hypothesis that
`Ω[B⁄R]` is a finitely presented `B`-module. Without it one would need descent of projectivity
along faithfully flat ring maps, i.e. Raynaud–Gruson. -/
theorem projective_kaehlerDifferential [Module.FaithfullyFlat B C] [Algebra.FormallySmooth R C]
    [Algebra.FormallySmooth B C] [Module.FinitePresentation B Ω[B⁄R]] :
    Module.Projective B Ω[B⁄R] :=
  have : Module.Flat B Ω[B⁄R] := flat_kaehlerDifferential R B C
  Module.Flat.projective_of_finitePresentation

/-- **Descent of formal unramifiedness.** If `C` is faithfully flat over `B`, `H¹(L_{C/B})`
vanishes (e.g. `B → C` is formally smooth) and `R → C` is formally unramified, then `R → B` is
formally unramified: `C ⊗[B] Ω[B⁄R]` injects into the trivial module `Ω[C⁄R]`, and faithful
flatness reflects triviality. -/
theorem formallyUnramified_of_faithfullyFlat [Module.FaithfullyFlat B C]
    [Subsingleton (Algebra.H1Cotangent B C)] [Algebra.FormallyUnramified R C] :
    Algebra.FormallyUnramified R B :=
  have : Subsingleton (C ⊗[B] Ω[B⁄R]) := (injective_mapBaseChange R B C).subsingleton
  ⟨Module.FaithfullyFlat.lTensor_reflects_triviality B C Ω[B⁄R]⟩

/-- **Stacks Project, Tags 02K6 and 02KM**, commutative algebra input, with the two gaps
described in the implementation notes left as hypotheses. Let `R → B → C` be ring maps with `C`
faithfully flat over `B` and both `R → C` and `B → C` formally smooth. If moreover `Ω[B⁄R]` is a
finitely presented `B`-module and the base change `C ⊗[B] H¹(L_{B/R})` vanishes, then `R → B` is
formally smooth.

The hypothesis on the base changed first homology is the sharp form of the missing step: the
Jacobi–Zariski sequence maps `C ⊗[B] H¹(L_{B/R})` to `H¹(L_{C/R})`, which vanishes by formal
smoothness of `R → C`, so it is exactly injectivity of that map which is unavailable. -/
theorem formallySmooth_of_subsingleton_tensorProduct_h1Cotangent [Module.FaithfullyFlat B C]
    [Algebra.FormallySmooth R C] [Algebra.FormallySmooth B C]
    [Module.FinitePresentation B Ω[B⁄R]] [Subsingleton (C ⊗[B] Algebra.H1Cotangent R B)] :
    Algebra.FormallySmooth R B :=
  ⟨projective_kaehlerDifferential R B C,
    Module.FaithfullyFlat.lTensor_reflects_triviality B C (Algebra.H1Cotangent R B)⟩

/-- The variant of `formallySmooth_of_subsingleton_tensorProduct_h1Cotangent` that assumes the
vanishing of `H¹(L_{B/R})` itself; over a faithfully flat `B`-algebra the two hypotheses agree. -/
theorem formallySmooth_of_subsingleton_h1Cotangent [Module.FaithfullyFlat B C]
    [Algebra.FormallySmooth R C] [Algebra.FormallySmooth B C]
    [Module.FinitePresentation B Ω[B⁄R]] [Subsingleton (Algebra.H1Cotangent R B)] :
    Algebra.FormallySmooth R B :=
  ⟨projective_kaehlerDifferential R B C, inferInstance⟩

end Stacks.RingTheory.FormallySmoothDescent

end
