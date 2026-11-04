module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforwardLan

/-!
# The functor `Rf_!` of a compactification

Let `f : X ⟶ Y` be a separated morphism of finite type between Noetherian schemes. A
compactification of `X` over `Y` is an open immersion `j : X ⟶ X̄` with `f̄ : X̄ ⟶ Y` proper, and
[Stacks, Section 0G4Z] attaches to it the functor

`Rf_! = Rf̄_* ∘ Rj_! : D^b_{Coh}(𝒪_X) ⥤ Pro-D^b_{Coh}(𝒪_Y)`.

This file records the data a compactification contributes and the functor it determines.

## Main definitions

* `CategoryTheory.CompactificationData`: the data a compactification contributes to the
  construction.
* `CategoryTheory.CompactificationData.shriekImage`: the functor `Rf_! = Rf̄_* ∘ Rj_!` it
  determines, `Rf̄_*` being applied to pro-objects termwise.

## Implementation notes

A compactification contributes exactly the data the construction uses: the category
`D^b_{Coh}(𝒪_{X̄})`, the restriction `j^*` with a Deligne system assignment (which is how `Rj_!`
exists at all, [Stacks, Tag 0G4N]), and the proper pushforward `Rf̄_*`. The functor `Rf̄_*` is
applied to pro-objects termwise, as the source does: `Rf_! K = Rf̄_* Rj_! K` is the pro-object of
the termwise image `(Rf̄_* K_n)` of an inverse system `(K_n)` giving `Rj_! K`. This is
`CategoryTheory.ProSeq.map`, which needs nothing of `Rf̄_*` (in particular no right adjoint inside
`D^b_{Coh}`, which a proper pushforward need not have). The concrete instance for an open
immersion into a scheme proper over `Y` is `CategoryTheory.CompactificationData.ofOpenImmersion`,
and the resulting `Rf_!` of a morphism of `FTS_S` is `AlgebraicGeometry.lowerShriek`. By [Stacks,
Tag 0G50] it does not depend on the compactification up to isomorphism.

`CategoryTheory.Compactification` (in
`StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.Independence`) is the earlier
form of the same data, which in addition carries a right adjoint `f̄^!` of `Rf̄_*` and pushes
pro-objects forward through it; `CategoryTheory.CompactificationData` drops that adjoint, which a
proper pushforward on `D^b_{Coh}` need not have.

## References

* [Stacks Project, Tag 0G4Z](https://stacks.math.columbia.edu/tag/0G4Z)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃

namespace CategoryTheory

/-- The data one compactification `j : X ⟶ X̄` of `X` over `Y` contributes to the construction of
`Rf_!`: the bounded coherent derived category of `X̄`, the restriction `j^*` to `X` together with a
Deligne system assignment for it — which is what makes `Rj_!` exist, [Stacks, Tag 0G4N] — and the
proper pushforward `Rf̄_*` to `Y`. -/
public structure CompactificationData (𝒞 : Type u₁) [Category.{v} 𝒞] (𝒟 : Type u₂) [Category.{v} 𝒟]
    (ℳ : Type u₃) [Category.{v} ℳ] where
  /-- Restriction `j^* : D^b_{Coh}(𝒪_{X̄}) ⥤ D^b_{Coh}(𝒪_X)` along the open immersion. -/
  restrict : ℳ ⥤ 𝒞
  /-- The Deligne system assignment for `j^*`, which determines `Rj_!`. -/
  assignment : DeligneSystemAssignment restrict
  /-- The proper pushforward `Rf̄_* : D^b_{Coh}(𝒪_{X̄}) ⥤ D^b_{Coh}(𝒪_Y)`. -/
  direct : ℳ ⥤ 𝒟

namespace CompactificationData

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]

/-- The functor `Rf_! = Rf̄_* ∘ Rj_! : D^b_{Coh}(𝒪_X) ⥤ Pro-D^b_{Coh}(𝒪_Y)` attached to a
compactification: `Rj_!` followed by the termwise pushforward of pro-objects along `Rf̄_*`. -/
public def shriekImage {ℳ : Type u₃} [Category.{v} ℳ] (C : CompactificationData 𝒞 𝒟 ℳ)
    [∀ A : ℳ ⥤ Type v, C.direct.HasLeftKanExtension A] : 𝒞 ⥤ ProSeq 𝒟 :=
  extensionByZero C.restrict C.assignment ⋙ ProSeq.map C.direct

end CompactificationData

end CategoryTheory

end
