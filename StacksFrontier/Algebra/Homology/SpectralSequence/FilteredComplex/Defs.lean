module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksCore.CategoryTheory.Filtration.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered complexes and the induced filtration on cohomology

A filtered complex is a cochain complex `K^•` together with a decreasing filtration of it by
subcomplexes `F^pK^•`, that is a `CategoryTheory.FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ`. The
induced filtration `F^pH^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))` is a filtration of `H^n(K^•)`
indexed by `ℤᵒᵖ`.

## Main definitions

* `CochainComplex.Filtered`: Filtered cochain complexes, as filtered objects of
  `CochainComplex C ℤ` indexed by `ℤᵒᵖ`.
* `CochainComplex.Filtered.inducedFiltration`: The filtration of `H^n(K^•)` induced by a
  filtered complex `K^•`.

## Implementation notes

As in `StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic`, the source defines a
filtered complex as a complex of filtered objects; a complex filtered by subcomplexes is the same
datum ([Stacks, Tag 05TW], [Stacks, Tag 015W]). The induced filtration is built from its antitone
family of image subobjects by `Filtration.ofAntitone`.

## References

* [Stacks Project, Tag 012L](https://stacks.math.columbia.edu/tag/012L)
* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 05TW](https://stacks.math.columbia.edu/tag/05TW)
* [Stacks Project, Tag 015W](https://stacks.math.columbia.edu/tag/015W)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CochainComplex

/-- A filtered complex of `C`: a cochain complex `K^•` together with a decreasing filtration
`F^pK^•` of it by subcomplexes, i.e. a filtered object of `CochainComplex C ℤ` indexed by `ℤᵒᵖ`. -/
@[stacks 012L "as a complex filtered by subcomplexes, the same datum as a complex of `Fil(𝒜)`",
  ega "0 11.2.2"]
abbrev Filtered (C : Type u) [Category.{v} C] [HasZeroMorphisms C] : Type _ :=
  FilteredObject (CochainComplex C ℤ) ℤᵒᵖ

namespace Filtered

variable {C : Type u} [Category.{v} C] [Abelian C] (K : Filtered C) (n : ℤ)

/-- The step `F^pH^n(K^•)` of the induced filtration: the image of `H^n(F^pK^•) ⟶ H^n(K^•)`. -/
noncomputable abbrev inducedFiltrationStep (p : ℤ) : Subobject (K.X.homology n) :=
  imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)

/-- The steps `F^pH^n(K^•)` of the induced filtration are antitone in `p`. -/
lemma inducedFiltrationStep_antitone : Antitone (K.inducedFiltrationStep n) := fun p q h ↦ by
  have e : HomologicalComplex.homologyMap (K.filtration.ι.app (op q)) n =
      HomologicalComplex.homologyMap (K.filtration.diagram.map (opHomOfLE h)) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n := by
    rw [← HomologicalComplex.homologyMap_comp, K.filtration.diagram_map_comp_ι_app]
  simp only [inducedFiltrationStep, e]
  exact imageSubobject_comp_le _ _

/-- The filtration of `H^n(K^•)` induced by a filtered complex `K^•`, with steps
`F^pH^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))`. -/
@[stacks 012P]
noncomputable def inducedFiltration : Filtration (K.X.homology n) ℤᵒᵖ :=
  Filtration.ofAntitone (K.inducedFiltrationStep n) (K.inducedFiltrationStep_antitone n)

/-- The step of `inducedFiltration` at `op p` is the image of `H^n(F^pK^•) ⟶ H^n(K^•)`. -/
@[simp]
lemma inducedFiltration_subobject (p : ℤ) :
    (K.inducedFiltration n).subobject (op p) =
      imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) :=
  Filtration.subobject_ofAntitone _ _ p

end Filtered

end CochainComplex
