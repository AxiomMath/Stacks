module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType

/-!
# Composition of ring maps of finite type and of finite presentation

This file states [Stacks, Tag 00F4] (Lemma 10.6.2) in full, as one conjunction over ring maps
`f : R →+* S'` and `g : S' →+* S`.

## Main results

* `RingHom.finiteType_finitePresentation_comp_and_of_comp`: the four parts of the lemma.

## References

* [Stacks Project, Tag 00F4](https://stacks.math.columbia.edu/tag/00F4)
-/

@[expose] public section

namespace RingHom

universe u v w

/-- **Stacks 00F4 (Lemma 10.6.2).** Let `f : R →+* S'` and `g : S' →+* S` be ring maps.
1. If `f` and `g` are of finite type, so is `g.comp f` (`RingHom.FiniteType.comp`).
2. If `f` and `g` are of finite presentation, so is `g.comp f`
   (`RingHom.FinitePresentation.comp`).
3. If `g.comp f` is of finite type, so is `g` (`RingHom.FiniteType.of_comp_finiteType`).
4. If `g.comp f` is of finite presentation and `f` is of finite type, then `g` is of finite
   presentation (`RingHom.FinitePresentation.of_comp_finiteType`). -/
@[stacks 00F4 "the four parts of the lemma"]
theorem finiteType_finitePresentation_comp_and_of_comp {R : Type u} {S' : Type v} {S : Type w}
    [CommRing R] [CommRing S'] [CommRing S] (f : R →+* S') (g : S' →+* S) :
    (f.FiniteType → g.FiniteType → (g.comp f).FiniteType) ∧
      (f.FinitePresentation → g.FinitePresentation → (g.comp f).FinitePresentation) ∧
      ((g.comp f).FiniteType → g.FiniteType) ∧
      ((g.comp f).FinitePresentation → f.FiniteType → g.FinitePresentation) :=
  ⟨fun hf hg => hg.comp hf, fun hf hg => hg.comp hf, fun h => h.of_comp_finiteType,
    fun h hf => FinitePresentation.of_comp_finiteType f h hf⟩

end RingHom
