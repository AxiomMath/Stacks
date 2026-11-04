module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Etale.FrobeniusBaseChange

/-!
# Derived global sections of an étale scheme and the Frobenius of the base

Let `p` be a prime number, let `A` be a commutative ring in which `p` vanishes, and let
`F : A → A`, `a ↦ aᵖ`, be its Frobenius endomorphism. For a quasi-compact, quasi-separated,
étale scheme `V` over `Spec A` there is an isomorphism

`RΓ(V, 𝒪_V) ⊗^L_{A, F} A ≅ RΓ(V, 𝒪_V)`

in `D(A)`. This is [Stacks, Tag 0EC9].

## Main results

* `Stacks.EtaleFrobenius.derivedGlobalSectionsBaseChange`: cohomology and base change for the
  structure sheaf of a flat quasi-compact quasi-separated scheme over an affine base, in the shape
  `Stacks.EtaleFrobenius.DerivedGlobalSectionsBaseChange` of
  `StacksFrontier/AlgebraicGeometry/Etale/FrobeniusBaseChange.lean`. It is
  `AlgebraicGeometry.nonempty_extendScalarsDerived_derivedGlobalSectionsOver_iso_of_flat`,
  [Stacks, Tag 08IB] at the structure sheaf read on global sections over the affine base.
* `Stacks.EtaleFrobenius.nonempty_extendScalarsDerived_derivedGlobalSections_iso_of_etale`:
  **[Stacks, Tag 0EC9]**, at exactly the hypotheses of the source.

## The proof

The source's proof: the relative Frobenius `V ⟶ V ×_{Spec A, Spec F} Spec A` is an isomorphism
because `V` is étale over `A` ([Stacks, Tag 0EBS]), so the absolute Frobenius of `V` exhibits `V`
as its own base change along `Spec F`
(`Stacks.EtaleFrobenius.isPullback_absoluteFrobenius`); and `V` is flat over `A`, so cohomology
and base change ([Stacks, Tag 08IB]) applied to that cartesian square computes
`RΓ(V, 𝒪_V) ⊗^L_{A, F} A` as `RΓ(V, 𝒪_V)`.

## References

* [Stacks Project, Tag 0EC9](https://stacks.math.columbia.edu/tag/0EC9)
* [Stacks Project, Tag 0EBS](https://stacks.math.columbia.edu/tag/0EBS)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleFrobenius

-- Standard model only: `nonempty_extendScalarsDerived_derivedGlobalSections_iso` (base input).
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Cohomology and base change for the structure sheaf over an affine base.** For every ring
map `φ : A ⟶ A'`, every flat, quasi-compact and quasi-separated `h : W ⟶ Spec A` and every
cartesian square exhibiting `h' : W' ⟶ Spec A'` as the base change of `h` along `Spec φ`, the
derived base change `RΓ(W, 𝒪_W) ⊗^L_{A, φ} A'` is `RΓ(W', 𝒪_{W'})`. -/
theorem derivedGlobalSectionsBaseChange (A : Type u) [CommRing A] :
    DerivedGlobalSectionsBaseChange A := by
  intro A' _ φ W W' h h' q hsq hqc hqs hfl
  exact nonempty_extendScalarsDerived_derivedGlobalSectionsOver_iso_of_flat φ h h' q hsq

variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp0 : (p : A) = 0)
  {V : Scheme.{u}} (f : V ⟶ Spec (.of A))

/-- **Stacks Project, Tag 0EC9.** Let `p` be a prime number, let `A` be a commutative ring in
which `p` vanishes and let `F : A → A`, `a ↦ aᵖ`, be its Frobenius endomorphism. If
`V ⟶ Spec A` is quasi-compact, quasi-separated and étale, then there exists an isomorphism

`RΓ(V, 𝒪_V) ⊗^L_{A, F} A ≅ RΓ(V, 𝒪_V)`

in `D(A)`.

The relative Frobenius of `V` is an isomorphism ([Stacks, Tag 0EBS]), so the absolute Frobenius
square of `V` is cartesian, and cohomology and base change for the flat morphism `V ⟶ Spec A`
(`derivedGlobalSectionsBaseChange`, [Stacks, Tag 08IB]) applies to it. -/
@[stacks 0EC9]
theorem nonempty_extendScalarsDerived_derivedGlobalSections_iso_of_etale
    [QuasiCompact f] [QuasiSeparated f] [Etale f] :
    Nonempty ((StacksDraft.PseudoCoherence.extendScalarsDerived
        (Stacks.LocalCohomology.frobeniusOfNatCastEqZero A p Fact.out hp0)).obj
        ((derivedGlobalSectionsOver f).obj (derivedStructureSheaf V)) ≅
      (derivedGlobalSectionsOver f).obj (derivedStructureSheaf V)) :=
  nonempty_extendScalarsDerived_derivedGlobalSections_iso p hp0 f
    (derivedGlobalSectionsBaseChange A)

end Stacks.EtaleFrobenius

end
