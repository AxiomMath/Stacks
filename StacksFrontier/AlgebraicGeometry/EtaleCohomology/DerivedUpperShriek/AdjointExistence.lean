module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.Compactification
public import StacksFrontier.Homology.Injectives.BrownRepresentability
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of derived lower shriek

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes and let `Λ` be a torsion coefficient ring. Then

`Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)`

has a right adjoint `Rf^! : D(Y_étale, Λ) ⟶ D(X_étale, Λ)`, [Stacks, Tag 0G2C].

## Main results

All in the namespace `Stacks.EtaleCohomology.DerivedUpperShriek`.

* `isLeftAdjoint_derivedLowerShriek` — **[Stacks, Tag 0G2C]** for `Rf_!` presented as the
  composite `Rf̄_* ∘ j_!` of a compactification: the functor has a right adjoint.
* `derivedUpperShriek` — the resulting `Rf^!`, with `derivedLowerShriekAdjunction` the
  adjunction `Rf_! ⊣ Rf^!` and `derivedUpperShriek_isTriangulated` its exactness.
* `CompactificationData.isLeftAdjoint_derivedLowerShriek` — the same for the derived lower
  shriek of a `CompactificationData`.

## Implementation notes

*The presentation of `Rf_!`.* `Rf_!` is the composite `Rf̄_* ∘ j_!` of a compactification
`f = f̄ ∘ j`, and its commutation with direct sums, [Stacks, Tag 0G29], is a hypothesis on the
composite.

*`IsLeftAdjoint` rather than an existential.* The conclusion is stated as
`CategoryTheory.Functor.IsLeftAdjoint`, which is Mathlib's spelling of "has a right adjoint". It
makes `CategoryTheory.Functor.rightAdjoint` and `CategoryTheory.Adjunction.ofIsLeftAdjoint`
available, so `Rf^!` below is a functor with an adjunction and hence with a *counit*.

*The coefficient ring.* The torsion hypothesis on `Λ` enters the source's proof only through
[Stacks, Tag 0G29] and through the independence of `Rf_!` of the chosen compactification. Both
are hypotheses or absent here, so no hypothesis on `Λ` appears: the abelian category `A` of
sheaves of `Λ`-modules on `X_étale` enters only through being Grothendieck abelian, which it
is for every coefficient ring
(`Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules`).

## References

* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F5Y](https://stacks.math.columbia.edu/tag/0F5Y)
* [Stacks Project, Tag 0G29](https://stacks.math.columbia.edu/tag/0G29)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
* [Stacks Project, Tag 0GLB](https://stacks.math.columbia.edu/tag/0GLB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.EtaleCohomology.DerivedUpperShriek

universe z w v u u' u''

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{max w u v} A]
  [HasDerivedCategory.{z} A]
  (DX : Type u') [Category.{max u v} DX] [HasZeroObject DX] [HasShift DX ℤ] [Preadditive DX]
  [∀ n : ℤ, (shiftFunctor DX n).Additive] [Pretriangulated DX]
  (DY : Type u'') [Category.{max u v} DY] [HasZeroObject DY] [HasShift DY ℤ] [Preadditive DY]
  [∀ n : ℤ, (shiftFunctor DY n).Additive] [Pretriangulated DY]
  (shriek : DerivedCategory A ⥤ DX) [shriek.CommShift ℤ] [shriek.IsTriangulated]
  (pushforwardFbar : DX ⥤ DY) [pushforwardFbar.CommShift ℤ] [pushforwardFbar.IsTriangulated]
  [∀ J : Type (max w u v),
    PreservesColimitsOfShape (Discrete J) (shriek ⋙ pushforwardFbar)]

/-- Let `Λ` be a coefficient ring, let `A` be the Grothendieck abelian category of sheaves of
`Λ`-modules on `X_étale`, and let `Rf_! = Rf̄_* ∘ j_!` be the derived lower shriek of a
compactification `f = f̄ ∘ j`, with `j_!` and `Rf̄_*` exact. If `Rf_!` commutes with direct sums —
which is [Stacks, Tag 0G29] when `f` is a separated finite-type morphism of quasi-compact
quasi-separated schemes and `Λ` is torsion — then `Rf_!` has a right adjoint
`Rf^! : D(Y_étale, Λ) ⟶ D(X_étale, Λ)`. -/
@[stacks 0G2C "Rf_! = Rf̄_*j_!, with its commutation with direct sums (Tag 0G29) assumed"]
theorem isLeftAdjoint_derivedLowerShriek : (shriek ⋙ pushforwardFbar).IsLeftAdjoint := by
  obtain ⟨G, adj, -⟩ := Stacks.Injectives.exists_exact_rightAdjoint.{z, w, v, u} A DY
    (shriek ⋙ pushforwardFbar)
  exact ⟨G, ⟨adj⟩⟩

/-- `Rf^!`, the right adjoint of the derived lower shriek `Rf_! = Rf̄_* ∘ j_!` provided by
[Stacks, Tag 0G2C]. -/
abbrev derivedUpperShriek : DY ⥤ DerivedCategory A :=
  letI := isLeftAdjoint_derivedLowerShriek.{z, w} A DX DY shriek pushforwardFbar
  (shriek ⋙ pushforwardFbar).rightAdjoint

/-- The adjunction `Rf_! ⊣ Rf^!` of [Stacks, Tag 0G2C]. -/
def derivedLowerShriekAdjunction :
    (shriek ⋙ pushforwardFbar) ⊣ derivedUpperShriek.{z, w} A DX DY shriek pushforwardFbar :=
  letI := isLeftAdjoint_derivedLowerShriek.{z, w} A DX DY shriek pushforwardFbar
  Adjunction.ofIsLeftAdjoint (shriek ⋙ pushforwardFbar)

/-- `Rf^!` is exact: it commutes with the shift and is a triangulated functor. -/
theorem derivedUpperShriek_isTriangulated :
    ∃ commShift : (derivedUpperShriek.{z, w} A DX DY shriek pushforwardFbar).CommShift ℤ,
      letI := commShift
      (derivedUpperShriek.{z, w} A DX DY shriek pushforwardFbar).IsTriangulated := by
  let adj := derivedLowerShriekAdjunction.{z, w} A DX DY shriek pushforwardFbar
  let _ := adj.rightAdjointCommShift ℤ
  let _ : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨inferInstance, adj.isTriangulated_rightAdjoint⟩

namespace CompactificationData

variable {DX DY}

/-- The functor `Rf_! = Rf̄_* ∘ j_!` read off a `CompactificationData` has a right adjoint as soon
as it commutes with direct sums, which is [Stacks, Tag 0G29]. -/
@[stacks 0G2C "for a CompactificationData; the commutation with direct sums (Tag 0G29) assumed"]
theorem isLeftAdjoint_derivedLowerShriek
    (data : CompactificationData (DerivedCategory A) DX DY)
    [data.shriek.CommShift ℤ] [data.shriek.IsTriangulated]
    [data.pushforwardFbar.CommShift ℤ] [data.pushforwardFbar.IsTriangulated]
    [∀ J : Type (max w u v),
      PreservesColimitsOfShape (Discrete J) data.derivedLowerShriek] :
    data.derivedLowerShriek.IsLeftAdjoint :=
  DerivedUpperShriek.isLeftAdjoint_derivedLowerShriek.{z, w} A DX DY data.shriek
    data.pushforwardFbar

end CompactificationData

end Stacks.EtaleCohomology.DerivedUpperShriek

end
