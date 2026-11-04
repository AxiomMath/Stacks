module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.HomSection
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# A nonzero morphism of invertible modules on an integral scheme is a twist by a divisor

Let `X` be an integral scheme and `L`, `L'` invertible `𝒪_X`-modules. A nonzero morphism
`σ : L ⟶ L'` is the same thing as a nonzero global section of `L' ⊗ L^∨`
(`Stacks.SheafOfModules.Scheme.homTensorDualSectionEquiv`), that section is regular because `X`
is integral ([Stacks, Tag 01WY]), so its zero scheme is an effective Cartier divisor `D` with
`𝒪_X(D) ≅ L' ⊗ L^∨` ([Stacks, Tag 01X0]); cancelling the dual factor gives `𝒪_X(D) ⊗ L ≅ L'`.

This is the step "it then suffices to check that `σ`, regarded as a global section of
`L' ⊗ L^{⊗ -1}`, ..." in the proof of [Stacks, Tag 0B3T]: it produces the divisor, and leaves
open which divisor it is. What Tag 0B3T needs beyond this is the identification of that divisor
with a multiple `k D` of the given one and the bound `k ≤ min(s, r)`; neither is proved here.

## Main definitions

* `Stacks.SheafOfModules.tensorDualTwistCancel`: the cancellation `(L' ⊗ L^∨) ⊗ L ≅ L'`.

## Main results

* `AlgebraicGeometry.exists_isEffectiveCartierDivisor_tensorIso_of_ne_zero`: a nonzero morphism
  of invertible modules on an integral scheme exhibits the target as a twist of the source by
  an effective Cartier divisor.

## Implementation notes

The cancellation is the associativity constraint, the evaluation pairing `L^∨ ⊗ L ≅ 𝒪_X` of Tag
040A (2) and the right unit constraint, in the shape
`Stacks.SheafOfModules.Invertible.tensorInverseCancel` of
`StacksFrontier/AlgebraicGeometry/Spaces/InvertibleDivisorDifference.lean` uses for the negative
tensor power. It is stated for the *dual* rather than for `L^{⊗ -1}` because that is the factor
`Stacks.SheafOfModules.Scheme.tensorDualTwist` carries, and in that order no braiding is needed.

Both invertibility classes of the repository occur. The divisor machinery — `zeroScheme`,
`IsRegularSection`, Tag 01X0 — is stated for `AlgebraicGeometry.SheafOfModules.IsInvertible`,
while the dual and the evaluation pairing are stated for `Stacks.SheafOfModules.IsInvertible`.
The hypotheses are taken in the divisor spelling and crossed over once with
`Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible`; the twist's own
invertibility is produced in the second spelling by Tag 01CT (1) and crossed back.

**No `@[stacks]` attribute.** The statement is a step of the proof of Tag 0B3T, not one of its
assertions: the tag asserts that the two determinant line bundles differ by a *bounded multiple
of the given divisor*, and the divisor produced here is only the zero scheme of `σ`. It is also
not an assertion of Tag 01X0, which is about a single invertible module with a regular section
and is applied here rather than restated.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 040A](https://stacks.math.columbia.edu/tag/040A)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite SheafOfModules

universe v u

namespace Stacks.SheafOfModules

/-! ### Cancelling the dual factor -/

section Cancel

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (L L' : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))
  [IsInvertible 𝒪 h𝒪 L]

/-- **Cancelling the dual factor of an invertible module**: `(L' ⊗ L^∨) ⊗ L ≅ L'`, by
associativity, the evaluation pairing `L^∨ ⊗ L ≅ 𝒪` of Tag 040A (2) and the right unit
constraint. -/
def tensorDualTwistCancel :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
            (L')).obj ((dualSheaf 𝒪 h𝒪 L)))))).obj (L)) ≅ L' :=
  Invertible.tensorProductAssociator 𝒪 h𝒪 L' (dualSheaf 𝒪 h𝒪 L) L ≪≫
    Invertible.tensorProductIso 𝒪 h𝒪 (Iso.refl L')
      (@asIso _ _ _ _ (evaluation 𝒪 h𝒪 L) (Invertible.isIso_evaluation 𝒪 h𝒪 L)) ≪≫
    Invertible.tensorProductRightUnitor 𝒪 h𝒪 L'

end Cancel

end Stacks.SheafOfModules

/-! ### The divisor of a nonzero morphism -/

namespace AlgebraicGeometry

open Stacks.SheafOfModules

variable {X : Scheme.{u}} [IsIntegral X] (L L' : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']

omit [IsIntegral X] [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L'] in
/-- The twist `L' ⊗ L^∨` of two invertible modules on a scheme is invertible, in the divisor
machinery's spelling of invertibility. -/
theorem isInvertible_tensorDualTwist
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L'] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.tensorDualTwist L L') :=
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (dualSheaf X.sheaf.obj X.ringCatSheaf.property L) :=
    Invertible.isInvertible_dualSheaf X.sheaf.obj X.ringCatSheaf.property L
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.tensorDualTwist L L') :=
    tensorProduct_isInvertible X.sheaf.obj X.ringCatSheaf.property L'
      (dualSheaf X.sheaf.obj X.ringCatSheaf.property L)
  Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible

/-- **The divisor cut out by a morphism of invertible modules**: the zero scheme of the global
section of `L' ⊗ L^∨` that the morphism corresponds to. For `σ ≠ 0` on an integral scheme this
is the effective Cartier divisor `D` of the proof of [Stacks, Tag 0B3T] with `𝒪_X(D) ⊗ L ≅ L'`,
named rather than left existentially quantified so that a statement can constrain it. -/
def morphismZeroScheme (σ : L ⟶ L') : X.IdealSheafData :=
  letI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  letI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  letI := isInvertible_tensorDualTwist L L'
  zeroScheme X (Scheme.tensorDualTwist L L')
    ((Scheme.homTensorDualSectionEquiv L L') σ)

/-- **The divisor of a nonzero morphism of invertible modules on an integral scheme is an
effective Cartier divisor with `𝒪_X(Z(σ)) ⊗ L ≅ L'`.** The corresponding global section of
`L' ⊗ L^∨` is nonzero because the comparison is additive and injective, hence regular because
`X` is integral, so [Stacks, Tag 01X0] applies and cancelling the dual factor gives the
twist. -/
theorem isEffectiveCartierDivisor_morphismZeroScheme_and_nonempty_tensorIso
    {σ : L ⟶ L'} (hσ : σ ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (morphismZeroScheme L L' σ) ∧
      Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
            ((Stacks.Divisors.invertibleSheaf' (morphismZeroScheme L L' σ)))).obj (L)) ≅ L') := by
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (dualSheaf X.sheaf.obj X.ringCatSheaf.property L) :=
    Invertible.isInvertible_dualSheaf X.sheaf.obj X.ringCatSheaf.property L
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.tensorDualTwist L L') :=
    tensorProduct_isInvertible X.sheaf.obj X.ringCatSheaf.property L'
      (dualSheaf X.sheaf.obj X.ringCatSheaf.property L)
  let := isInvertible_tensorDualTwist L L'
  set s : (Scheme.tensorDualTwist L L').sections :=
    sectionsOfTop (Scheme.tensorDualTwist L L')
      ((Scheme.homTensorDualSectionEquiv L L') σ) with hsdef
  have hs : s.eval (op ⊤) = (Scheme.homTensorDualSectionEquiv L L') σ :=
    sectionsOfTop_eval_top _ _
  have hne : s.eval (op ⊤) ≠ 0 := by
    rw [hs]
    exact fun h => hσ ((Scheme.homTensorDualSectionEquiv L L' (X := X)).map_eq_zero_iff.mp h)
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
    isRegularSection_of_eval_top_ne_zero _ s hne
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme X (Scheme.tensorDualTwist L L') (s.eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X _ s).mpr hreg
  have hiso : Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
        (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
          ((Stacks.Divisors.invertibleSheaf'
            (zeroScheme X (Scheme.tensorDualTwist L L') (s.eval (op ⊤)))))).obj (L)) ≅ L') :=
    ⟨Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property
        (invertibleSheafIsoZeroSchemeOfIsRegularSection _ s hreg).symm (Iso.refl L) ≪≫
      tensorDualTwistCancel X.sheaf.obj X.ringCatSheaf.property L L'⟩
  rw [hs] at hD hiso
  exact ⟨hD, hiso⟩

/-- **The divisor of a nonzero morphism of invertible modules is an effective Cartier
divisor.** -/
theorem isEffectiveCartierDivisor_morphismZeroScheme {σ : L ⟶ L'} (hσ : σ ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (morphismZeroScheme L L' σ) :=
  (isEffectiveCartierDivisor_morphismZeroScheme_and_nonempty_tensorIso L L' hσ).1

/-- **A nonzero morphism of invertible modules on an integral scheme is the twist by its own
divisor**: `𝒪_X(Z(σ)) ⊗ L ≅ L'`. -/
theorem nonempty_tensorIso_morphismZeroScheme {σ : L ⟶ L'} (hσ : σ ≠ 0) :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
        (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
          ((Stacks.Divisors.invertibleSheaf' (morphismZeroScheme L L' σ)))).obj (L)) ≅ L') :=
  (isEffectiveCartierDivisor_morphismZeroScheme_and_nonempty_tensorIso L L' hσ).2

/-- **A nonzero morphism of invertible modules on an integral scheme is a twist by an effective
Cartier divisor.** The morphism is a global section of `L' ⊗ L^∨`, nonzero because the
comparison is additive and injective, hence regular because `X` is integral; its zero scheme
`D` is an effective Cartier divisor with `𝒪_X(D) ≅ L' ⊗ L^∨` by [Stacks, Tag 01X0], and
cancelling the dual factor gives `𝒪_X(D) ⊗ L ≅ L'`.

This is the divisor-producing step of the proof of [Stacks, Tag 0B3T]; which divisor it is, the
tag's `k D`, is not determined here. The divisor itself is `morphismZeroScheme L L' σ`. -/
theorem exists_isEffectiveCartierDivisor_tensorIso_of_ne_zero {σ : L ⟶ L'} (hσ : σ ≠ 0) :
    ∃ D : X.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
            ((Stacks.Divisors.invertibleSheaf' D))).obj (L)) ≅ L') :=
  ⟨morphismZeroScheme L L' σ, isEffectiveCartierDivisor_morphismZeroScheme L L' hσ,
    nonempty_tensorIso_morphismZeroScheme L L' hσ⟩

end AlgebraicGeometry

end
