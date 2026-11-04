module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeFiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor base change isomorphism over a field, for schemes of finite type

Let `K` be a field and `n ≥ 1` an integer invertible in `K`. Consider a commutative diagram
```
X <-p-- X' <-h-- Y
|       |f'      |e
v       v        v
Spec K <- S' <-g- T
```
of schemes of finite type over `K` with `X' = X ×_{Spec K} S'` and `Y = X' ×_{S'} T`.
[Stacks, Tag 0F1N] asserts that the canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is an isomorphism for all `E ∈ D(X_étale, ℤ/nℤ)` and `F ∈ D(T_étale, ℤ/nℤ)`.

The source reduces this to [Stacks, Tag 0F1J] using that all the functors involved commute with
direct sums, which is where finite type is used ([Stacks, Tag 0F10], [Stacks, Tag 0F11]). The
reduction is
`Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_finiteType_of_isGE`, and
Tag 0F1J is `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_isUnit`.

## Main results

* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_finiteType` —
  [Stacks, Tag 0F1N].

## References

* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- forced by `Stacks.EtaleCohomology.EtaleCoefficients.
-- isIso_tensorBaseChangeMap_of_finiteType_of_isGE` (Kunneth/TensorBaseChangeFiniteType.lean:130),
-- stated for the standard model of the derived category, through `derivedPullback`.
attribute [local instance] HasDerivedCategory.standard

-- [Stacks, Tag 0F10] imports `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

/-- **[Stacks, Tag 0F1N].** Let `K` be a field and `n ≥ 1` an integer invertible in `K`.
Consider a commutative diagram
```
X <-p-- X' <-h-- Y
|       |f'      |e
v       v        v
Spec K <- S' <-g- T
```
of schemes of finite type over `K` (through `πX`, `πS` and `g ≫ πS`) with `X' = X ×_K S'` and
`Y = X' ×_{S'} T`. Then the canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is an isomorphism for all `E ∈ D(X_étale, ℤ/nℤ)` and `F ∈ D(T_étale, ℤ/nℤ)`.

The reduction to `E ∈ D⁺` of Tor amplitude bounded below and `F ∈ D⁺`, where the functors
commute with direct sums because `cd(g), cd(h) < ∞` ([Stacks, Tag 0F10]), is
`isIso_tensorBaseChangeMap_of_finiteType_of_isGE`; the bounded below case is [Stacks, Tag 0F1J]
(`isIso_tensorBaseChangeMap_of_isUnit`). -/
@[stacks 0F1N]
theorem isIso_tensorBaseChangeMap_of_finiteType (K : Type u) [Field K] (n : ℕ) [NeZero n]
    (hn : IsUnit (n : K)) {X X' Y S' T : Scheme.{u}} (πX : X ⟶ Spec (.of K))
    (πS : S' ⟶ Spec (.of K)) (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (g : T ⟶ S') [LocallyOfFiniteType πX] [QuasiCompact πX] [LocallyOfFiniteType πS]
    [QuasiCompact πS] [LocallyOfFiniteType (g ≫ πS)] [QuasiCompact (g ≫ πS)]
    (hX' : IsPullback p f' πX πS) (hY : IsPullback h e f' g)
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod n)) p).obj E) F) := by
  have : QuasiCompact g := quasiCompact_of_finiteType K (g ≫ πS) πS g
  have : QuasiSeparated g := quasiSeparated_of_finiteType K (g ≫ πS) g
  exact isIso_tensorBaseChangeMap_of_finiteType_of_isGE K n πX πS p f' h e g hX' hY
    (fun E F a b _ hE hEa hF =>
      isIso_tensorBaseChangeMap_of_isUnit K n hn πX πS p f' hX' g h e hY E ⟨b, hE⟩ a hEa F
        ⟨_, hF⟩) E F

end Stacks.EtaleCohomology.EtaleCoefficients

end
