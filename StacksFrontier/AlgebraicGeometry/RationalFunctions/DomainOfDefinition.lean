module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# The morphism representing a rational map on its domain of definition

A rational map `φ` from a scheme `X` to a scheme `Y` is an equivalence class of morphisms into
`Y` defined on dense open subschemes of `X`, two of them being identified when they agree on a
smaller dense open subscheme [Stacks, Tag 01RR]. The domain of definition of `φ` is the set of
points admitting a representative defined there, an open subscheme `U ⊆ X`
[Stacks, Tag 0A1X]; in general no single representative is defined on all of `U`.

When `X` is reduced and `Y` is separated that pathology disappears: the representatives glue, and
they glue in only one way, so there is exactly one morphism `f : U ⟶ Y` representing `φ`, that
is, whose partial map `⟨φ.domain, φ.dense_domain, f⟩` lies in the equivalence class `φ`
[Stacks, Tag 0A1Y]. If moreover `X` and `Y` are schemes over a separated scheme `S` and `φ` is an
`S`-rational map, that morphism is a morphism over `S`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.existsUnique_hom_domain`: for `X` reduced and `Y`
  separated, exactly one morphism from the domain of definition of `φ` to `Y` represents `φ`.
* `AlgebraicGeometry.Scheme.RationalMap.isOver_of_toRationalMap_eq`: over a separated base `S`,
  that morphism is a morphism over `S`.

## References

* [Stacks Project, Tag 0A1Y](https://stacks.math.columbia.edu/tag/0A1Y), Lemma 29.50.9.
* [Stacks Project, Tag 0A1X](https://stacks.math.columbia.edu/tag/0A1X), Definition 29.50.8, the
  domain of definition.
* [Stacks Project, Tag 01RR](https://stacks.math.columbia.edu/tag/01RR), Section 29.50, rational
  maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

namespace Scheme.RationalMap

/-- Let `X` and `Y` be schemes with `X` reduced and `Y` separated, and let `φ` be a rational map
from `X` to `Y` with domain of definition `φ.domain`. There is exactly one morphism
`φ.domain ⟶ Y` representing `φ`, that is, exactly one morphism on the domain of definition whose
partial map lies in the equivalence class `φ`. -/
@[stacks 0A1Y "existence and uniqueness of the morphism on the domain of definition",
  ega "I 7.2.2" "special case",
  ega "IV 20.2.4" "special case",
  ega "IV 20.2.8" "special case",
  ega "IV 20.3.2" "special case"]
theorem existsUnique_hom_domain [IsReduced X] [Y.IsSeparated] (φ : X ⤏ Y) :
    ∃! f : φ.domain.toScheme ⟶ Y,
      (PartialMap.mk φ.domain φ.dense_domain f).toRationalMap = φ := by
  refine ⟨φ.toPartialMap.hom, φ.toRationalMap_toPartialMap, fun f hf ↦ ?_⟩
  obtain ⟨e, he⟩ := (PartialMap.ext_iff _ _).mp
    ((PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ Scheme)
      (f := PartialMap.mk φ.domain φ.dense_domain f) (g := φ.toPartialMap) rfl).mp
      (PartialMap.toRationalMap_eq_iff.mp (hf.trans φ.toRationalMap_toPartialMap.symm)))
  have he' : f = X.homOfLE e.le ≫ φ.toPartialMap.hom := he
  have hid : X.homOfLE e.le = 𝟙 φ.domain.toScheme := X.homOfLE_rfl _
  rw [he', hid]
  exact Category.id_comp _

/-- Let `X` and `Y` be schemes over a separated scheme `S`, with `X` reduced and `Y` separated,
and let `φ` be an `S`-rational map from `X` to `Y`. Then the morphism on the domain of definition
of `φ` that represents `φ` is a morphism over `S`. -/
@[stacks 0A1Y "the morphism on the domain of definition is a morphism over a separated base",
  ega "IV 20.2.5" "special case"]
theorem isOver_of_toRationalMap_eq [X.Over S] [Y.Over S] [IsReduced X] [Y.IsSeparated]
    [S.IsSeparated] (φ : X ⤏ Y) [φ.IsOver S] {f : φ.domain.toScheme ⟶ Y}
    (hf : (PartialMap.mk φ.domain φ.dense_domain f).toRationalMap = φ) :
    f.IsOver S := by
  have h : f = φ.toPartialMap.hom :=
    (existsUnique_hom_domain φ).unique hf φ.toRationalMap_toPartialMap
  exact ⟨(congrArg (· ≫ Y ↘ S) h).trans (comp_over φ.toPartialMap.hom S)⟩

end Scheme.RationalMap

end AlgebraicGeometry
