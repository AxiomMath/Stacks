module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Tactic.TFAE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite morphisms are the proper morphisms with finite fibres

Let `f : X ⟶ S` be a morphism of schemes. The following are equivalent:

1. `f` is finite;
2. `f` is proper with finite fibres;
3. `f` is proper and locally quasi-finite;
4. `f` is universally closed, separated, locally of finite type and has finite fibres.

The fibre of `f` over `s` is recorded by its underlying set `f ⁻¹' {s}`, which is homeomorphic
to the scheme-theoretic fibre `f.fiber s`.

## Main results

* `AlgebraicGeometry.IsFinite.tfae_isProper_locallyQuasiFinite`: the four conditions as a
  `List.TFAE`.

## Implementation notes

The implication (3) ⇒ (1) is Zariski's main theorem in the form
`AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite`. (2) ⇔ (3) is
`AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`, available because a proper
morphism is quasi-compact and locally of finite type, and (2) ⇔ (4) is the definition of a proper
morphism.

## References

* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For a morphism of schemes `f : X ⟶ S` the following are equivalent: `f` is finite; `f` is
proper with finite fibres; `f` is proper and locally quasi-finite; `f` is universally closed,
separated, locally of finite type and has finite fibres. The fibre over `s` is its underlying set
`f ⁻¹' {s}`. -/
@[stacks 02LS, ega "III 4.4.11" "more general", ega "IV 18.12.4"]
theorem IsFinite.tfae_isProper_locallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE
      [IsFinite f,
        IsProper f ∧ ∀ s : S, (f ⁻¹' {s}).Finite,
        IsProper f ∧ LocallyQuasiFinite f,
        UniversallyClosed f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧
          ∀ s : S, (f ⁻¹' {s}).Finite] := by
  tfae_have 1 ↔ 3 := IsFinite.iff_isProper_and_locallyQuasiFinite f
  tfae_have 2 ↔ 3 :=
    ⟨fun ⟨_, h⟩ ↦ ⟨inferInstance, locallyQuasiFinite_iff_finite_preimage_singleton.mpr h⟩,
      fun ⟨_, h⟩ ↦ ⟨inferInstance, locallyQuasiFinite_iff_finite_preimage_singleton.mp h⟩⟩
  tfae_have 2 ↔ 4 :=
    ⟨fun ⟨_, h⟩ ↦ ⟨inferInstance, inferInstance, inferInstance, h⟩, fun ⟨_, _, _, h⟩ ↦ ⟨⟨⟩, h⟩⟩
  tfae_finish

end AlgebraicGeometry

end
