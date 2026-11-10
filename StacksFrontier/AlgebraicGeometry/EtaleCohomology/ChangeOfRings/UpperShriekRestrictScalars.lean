module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ChangeOfRings.UpperShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.LowerShriekExtendScalarsHeldInputs
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The derived upper shriek commutes with restriction of coefficients

Let `Λ₁ ⟶ Λ₂` be a homomorphism of torsion rings and let `f : X ⟶ Y` be a separated finite type
morphism of quasi-compact and quasi-separated schemes. [Stacks, Tag 0GLF] asserts that the square

```
D(X_étale, Λ₂) --res--> D(X_étale, Λ₁)
     ↑ Rf^!                  ↑ Rf^!
D(Y_étale, Λ₂) --res--> D(Y_étale, Λ₁)
```

commutes, `res` turning a `Λ₂`-module into a `Λ₁`-module through the ring map.

## Main results

* `Stacks.EtaleCohomology.ChangeOfRings.upperShriek_restrictScalars`: **[Stacks, Tag 0GLF]**.

## Implementation notes

The source's proof is followed. `f` has a compactification `f = fbar ∘ j` by Nagata's theorem
([Stacks, Tag 0F41], `AlgebraicGeometry.hasCompactification_of_compactSpace_quasiSeparatedSpace`),
`Rf_! = R(fbar)_* ∘ j_!` ([Stacks, Tag 0F7H]) is a left adjoint for every compactification and both
coefficient rings ([Stacks, Tag 0G2C],
`Stacks.EtaleCohomology.DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded`), and `Rf^!`
is its right adjoint `CategoryTheory.Functor.rightAdjoint`. The square is obtained by uniqueness
of adjoints (`Stacks.EtaleCohomology.ChangeOfRings.upperShriekRestrictScalarsIsoOfLowerShriek`)
from the second square of [Stacks, Tag 0GL6],
`Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion`, and the
adjunction `- ⊗^L_{Λ₁} Λ₂ ⊣ res` of [Stacks, Tag 07A6] on `X_étale` and on `Y_étale`,
`Stacks.EtaleCohomology.etaleModuleDerivedExtendRestrictAdj`.

The statement holds for *every* compactification `j`, which is stronger than for one chosen
compactification. A ring is torsion exactly when `n = 0` in it for some `n ≥ 1` (then `1` is
torsion); `Λ₂` is then torsion as well, so only the hypothesis on `Λ₁` is needed. The two rings
are commutative rings in `Type`, the universe of [Stacks, Tag 0G2C].
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology.ChangeOfRings

variable {Λ₁ Λ₂ : Type} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **[Stacks, Tag 0GLF].** Let `φ : Λ₁ ⟶ Λ₂` be a homomorphism of torsion rings (`n = 0` in
`Λ₁` for some `n ≥ 1`, hence also in `Λ₂`) and let `f : X ⟶ Y` be a separated morphism of finite
type between quasi-compact and quasi-separated schemes. Then `f` has a compactification
([Stacks, Tag 0F41]), and for every compactification `j`, with `Rf_! = R(fbar)_* ∘ j_!` and `Rf^!`
its right adjoint over `Λ₁` and over `Λ₂` ([Stacks, Tag 0G2C]),

`res ∘ Rf^! ≅ Rf^! ∘ res : D(Y_étale, Λ₂) ⥤ D(X_étale, Λ₁)`,

`res` being restriction of scalars along `φ`. -/
@[stacks 0GLF]
theorem upperShriek_restrictScalars (n : ℕ) (hn : 0 < n) (hΛ₁ : (n : Λ₁) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    Nonempty (CompactificationOf (Over.mk f)) ∧
      ∀ j : CompactificationOf (Over.mk f),
        letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ₁ n hn hΛ₁ f j
        letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ₂ n hn
          (natCast_eq_zero_of_ringHom φ hΛ₁) f j
        Nonempty ((derivedLowerShriekUnbounded.{u, 0} f j Λ₂).rightAdjoint ⋙
            derivedRestrictScalars.{u, 0} φ X ≅
          derivedRestrictScalars.{u, 0} φ Y ⋙
            (derivedLowerShriekUnbounded.{u, 0} f j Λ₁).rightAdjoint) := by
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨j, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
    exact ⟨j⟩
  · have htors : ∀ x : Λ₁, ∃ m : ℕ, 0 < m ∧ (m : Λ₁) * x = 0 :=
      fun x => ⟨n, hn, by rw [hΛ₁, zero_mul]⟩
    have := isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion φ htors f j
    exact ⟨upperShriekRestrictScalarsIsoOfLowerShriek φ n hn hΛ₁ f j
      (etaleModuleDerivedExtendRestrictAdj.{u, 0} φ X)
      (etaleModuleDerivedExtendRestrictAdj.{u, 0} φ Y)
      (asIso (derivedLowerShriekUnboundedExtendScalarsMap.{u, 0} φ f j))⟩

end Stacks.EtaleCohomology.ChangeOfRings

end
