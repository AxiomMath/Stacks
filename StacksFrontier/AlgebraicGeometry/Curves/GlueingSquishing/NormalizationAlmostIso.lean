module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a reduced algebraic scheme is an almost isomorphism

[Stacks, Tag 0C20] factors the normalization `ν : X^ν ⟶ X` of a curve by [Stacks, Tag 0C1L],
whose Lean form `Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain` asks for
`Stacks.GlueSquishFactor.IsAlmostIso ν`. That predicate has seven conjuncts. This file discharges
six of them for the normalization of a reduced scheme locally of finite type over a field, and
reduces `IsAlmostIso ν` to the seventh:

**`∃ U, Set.Finite ((U : Set X)ᶜ) ∧ IsIso (ν ∣_ U)`** — the finiteness of the locus where `ν`
fails to be an isomorphism.

The six discharged clauses are: finite type and quasi-compactness of both structure morphisms,
which for `X^ν` follow from the finiteness of `ν`
(`AlgebraicGeometry.isFinite_normalizationOverField`, [Stacks, Tag 0BXR]); the finiteness of `ν`
itself; and the inclusion `𝒪_X ⊂ ν_*𝒪_{X^ν}`
(`AlgebraicGeometry.mono_hom_pushforwardAlgebra_normalizationOverField`).

## Implementation notes

**The two spellings of `𝒪_X ⊂ ν_*𝒪_{X^ν}`.**
`Stacks.AlgebraicGeometry.Normalization.mono_toRingCatSheafHom_fromNormalization` states the
inclusion as a monomorphism in the sheaves of **`RingCat`**-valued sheaves, whereas
`Stacks.GlueSquishFactor.IsAlmostIso` asks for a monomorphism of
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra`, an object of **`CommRingCat`**-valued
algebra sheaves. The two are the same arrow `𝒪_X ⟶ ν_*𝒪_{X^ν}` in two categories, and nothing
transports `Mono` from one to the other. What does bridge them is the statement both are proved
from, namely injectivity of `ν^♯` on sections over every open:
`Stacks.AlgebraicGeometry.Normalization.injective_fromNormalization_app` supplies it and
`Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_forall_injective_app` consumes it.

## Main results

* `Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_forall_injective_app` — injectivity
  of `f^♯` on sections over every open gives `𝒪_Y ⊂ f_*𝒪_X` in the shape
  `Stacks.GlueSquishFactor.IsAlmostIso` asks for.
* `AlgebraicGeometry.injective_app_normalizationOverField` — `ν^♯` is injective on sections over
  every open, for `X` reduced.
* `AlgebraicGeometry.mono_hom_pushforwardAlgebra_normalizationOverField` — hence
  `𝒪_X ⊂ ν_*𝒪_{X^ν}`.
* `AlgebraicGeometry.isAlmostIso_normalizationOverField_of_exists_isIso` — `IsAlmostIso ν`,
  granted the finiteness of the locus where `ν` is not an isomorphism.

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.GlueSquishFactor

/-- **`𝒪_Y ⊂ f_*𝒪_X` from injectivity on sections over every open.** For an affine morphism
`f : X ⟶ Y` whose map `f^♯` is injective on sections over every open of `Y`, the morphism
`𝒪_Y ⟶ f_*𝒪_X` of `CommRingCat`-valued algebra sheaves is a monomorphism. -/
theorem mono_hom_pushforwardAlgebra_of_forall_injective_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (h : ∀ U : Y.Opens, Function.Injective (f.app U).hom) :
    Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom := by
  refine mono_hom_pushforwardAlgebra_of_injective_app f fun y => ?_
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  exact ⟨U, hU, hyU, h U⟩

end Stacks.GlueSquishFactor

namespace AlgebraicGeometry

/-- **The normalization morphism of a reduced scheme locally of finite type over a field is
injective on sections over every open.** -/
theorem injective_app_normalizationOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens) :
    Function.Injective ((normalizationOverField k p).app U).hom := by
  let f := Scheme.fromGenericPointResidueFields X
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  let : QuasiCompact f := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let : QuasiSeparated f := Scheme.quasiSeparatedFromGenericPointResidueFields X
  exact Stacks.AlgebraicGeometry.Normalization.injective_fromNormalization_app f U

/-- **`𝒪_X ⊂ ν_*𝒪_{X^ν}` for the normalization of a reduced scheme locally of finite type over a
field**, as a monomorphism of `CommRingCat`-valued algebra sheaves: clause (2) of
[Stacks, Tag 0C1R]. -/
theorem mono_hom_pushforwardAlgebra_normalizationOverField (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsReduced X] :
    Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra (normalizationOverField k p)).hom := by
  have := isFinite_normalizationOverField k p
  exact Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_forall_injective_app _
    (injective_app_normalizationOverField k p)

/-- **The normalization of a reduced algebraic scheme over an algebraically closed field is an
almost isomorphism in the sense of [Stacks, Tag 0C1L], granted that it is an isomorphism away
from finitely many points.** -/
@[ega "IV 7.8.6" "(ii), special case"]
theorem isAlmostIso_normalizationOverField_of_exists_isIso (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced X]
    (hU : ∃ U : X.Opens, Set.Finite ((U : Set X)ᶜ) ∧ IsIso (normalizationOverField k p ∣_ U)) :
    Stacks.GlueSquishFactor.IsAlmostIso
      (Over.homMk (normalizationOverField k p) rfl :
        Over.mk (normalizationOverField k p ≫ p) ⟶ Over.mk p) := by
  have := isFinite_normalizationOverField k p
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hU⟩, mono_hom_pushforwardAlgebra_normalizationOverField k p⟩
  · change LocallyOfFiniteType (normalizationOverField k p ≫ p)
    infer_instance
  · change QuasiCompact (normalizationOverField k p ≫ p)
    infer_instance
  · change LocallyOfFiniteType p
    infer_instance
  · change QuasiCompact p
    infer_instance
  · change IsFinite (normalizationOverField k p)
    infer_instance

end AlgebraicGeometry

end
