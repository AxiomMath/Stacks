module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorNumericalCoherent
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackFlatClosed

/-!
# `Hilb^P_{X/B}` (Stacks 0DPG)

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation, let `I` be a
set, `E_i ∈ D(𝒪_X)` perfect for `i ∈ I`, and `P : I → ℤ` — the standing data
`AlgebraicGeometry.Space.NumericalSituation` of Situation 0DNC.  Since
`Hilb_{X/B} = Quot_{𝒪_X/X/B}` (Stacks 0D00), Stacks 0DPG defines

`Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B} = Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`,

the families `Z ⊆ X_T` whose object `(T, 𝒪_Z)` of `Coh_{X/B}` has numerical invariants
`χ_i(t) = χ(X_t, E_{i,t} ⊗^𝐋 𝒪_{Z_t})` equal to `P(i)` at every point `t ∈ |T|`, and asserts that
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion, and an open and closed immersion when `I`
is finite, when `B` is locally Noetherian, or when `I = ℤ` and `E_i = 𝓛^{⊗ i}`.  The source deduces
all of this by base change from the corresponding assertions about `Coh^P_{X/B} ⊆ Coh_{X/B}`.

## Main definitions

* `AlgebraicGeometry.Space.numericalHilbertCondition`: **`Hilb^P_{X/B}`**, the subfunctor of the
  Hilbert presheaf corresponding to `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`.
* `AlgebraicGeometry.Space.numericalHilbertEulerData`: the fibrewise invariants of the families
  classified by `Hilb_{X/B}` given by Situation 0DNC, in the form of
  `AlgebraicGeometry.Space.HilbertEulerData`.

## Main results

* `AlgebraicGeometry.Space.isPrescribed_numericalHilbertEulerData_iff`: the subfunctor
  `AlgebraicGeometry.Space.HilbertEulerData.numericalHilbertFunctor` for those invariants is
  `Hilb^P_{X/B}`.
* In `AlgebraicGeometry.Space`:
  * `relative_closedImmersion_flat_numericalHilbertCondition_of_isLocallyConstant`:
    `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion when the invariants are locally
    constant.
  * `relative_openImmersion_closedImmersion_numericalHilbertCondition_of_isLocallyConstant`:
    it is an open and closed immersion for a finite index set.
  * `relative_closedImmersion_flat_numericalHilbertCondition_of_isFlatClosed`: it is a flat
    closed immersion when `Coh^P_{X/B} ⊆ Coh_{X/B}` is a flat closed substack.
  * `relative_openImmersion_closedImmersion_numericalHilbertCondition_of_isOpenAndClosed`:
    it is an open and closed immersion when `Coh^P_{X/B}` is an open and closed substack.

## Implementation notes

The Hilbert presheaf takes values in `Type (u + 1)`, so representability of
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is taken along `CategoryTheory.uliftYoneda.{u + 1}`, as in
`AlgebraicGeometry.Space.IsClosedImmersionULift`.  "Flat closed immersion" is representability by
morphisms of schemes which are flat closed immersions; for a representable morphism this is
flatness in the sense of Stacks 03ML (`AlgebraicGeometry.Space.isFlat_iff_presheaf`).

The two properties of Situation 0DNC's `AlgebraicGeometry.Space.NumericalSituation.numericalEuler`
that the source deduces from Stacks 0A1P and 0D1Z — compatibility with pullback along the
morphisms of `Coh_{X/B}` and local constancy — are carried here as the explicit hypotheses `hbc`
and `hlc`, and the open-and-closed conditions of Stacks 0DND (`B` locally Noetherian) and 0DNE
(`I = ℤ`, `E_i = 𝓛^{⊗ i}`) as the explicit hypothesis `hQ`.

## References

* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  (N : NumericalSituation.{u, v, u} B S hS (structureSheafQuotSituation f hf).toCoherentSituation)

variable {N}

/-- **Stacks 0DPG, the definition of `Hilb^P_{X/B}`.**  Through the identification
`Hilb_{X/B} = Quot_{𝒪_X/X/B}` of Stacks 0D00, `Hilb^P_{X/B}` is
`Quot^P_{𝒪_X/X/B} = Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`: the subfunctor of the Hilbert
presheaf of the families `Z ⊆ X_T` whose object `(T, 𝒪_Z)` of `Coh_{X/B}` lies in
`Coh^P_{X/B}`, that is, has `χ_i(t) = P(i)` for all `i ∈ I` and all `t ∈ |T|`.  It is a subfunctor
because the numerical invariants are compatible with pullback, `hbc`. -/
def numericalHilbertCondition
    (hbc : ∀ {A' A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation}
      (φ : CoherentHom A' A) (i : N.I) (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t)) :
    Subfunctor (hilbertPresheaf f) :=
  hilbertCondition f hf N.HasNumericalInvariants
    (CoherentSituation.numerical_points_of_hom (χ := N.numericalEuler) N.P hbc)

section Assertions

variable (hbc : ∀ {A' A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation}
      (φ : CoherentHom A' A) (i : N.I) (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))

/-- A family lies in `Hilb^P_{X/B}` exactly when its object `(T, 𝒪_Z)` of `Coh_{X/B}` lies in
`Coh^P_{X/B}`. -/
theorem mem_numericalHilbertCondition_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (hilbertPresheaf f).obj T) :
    x ∈ (numericalHilbertCondition f hf hbc).obj T ↔
      N.HasNumericalInvariants (hilbertCohObject f hf x) :=
  Iff.rfl

/-- `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion as soon as the numerical invariants
`χ_i` are locally constant. -/
theorem relative_closedImmersion_flat_numericalHilbertCondition_of_isLocallyConstant
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (numericalHilbertCondition f hf hbc).ι :=
  relative_closedImmersion_flat_hilbertCondition_of_isLocallyConstant f hf hbc hlc N.P

/-- `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion for a finite index set as soon
as the numerical invariants `χ_i` are locally constant. -/
theorem relative_openImmersion_closedImmersion_numericalHilbertCondition_of_isLocallyConstant
    [Finite N.I] (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (numericalHilbertCondition f hf hbc).ι :=
  relative_openImmersion_closedImmersion_hilbertCondition_of_isLocallyConstant f hf hbc hlc N.P

/-- `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion as soon as `Coh^P_{X/B} ⊆ Coh_{X/B}` is
a flat closed substack. -/
theorem relative_closedImmersion_flat_numericalHilbertCondition_of_isFlatClosed
    (hQ : CoherentSituation.IsFlatClosedCondition
      (structureSheafQuotSituation f hf).toCoherentSituation N.HasNumericalInvariants) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (numericalHilbertCondition f hf hbc).ι :=
  relative_closedImmersion_flat_hilbertCondition_ι f hf
    (CoherentSituation.numerical_points_of_hom (χ := N.numericalEuler) N.P hbc)
    (CoherentSituation.isFlatClosedCondition_iff_isCutOutOnTestSchemes.1 hQ)

/-- `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion as soon as `Coh^P_{X/B}` is an
open and closed substack of `Coh_{X/B}`. -/
theorem relative_openImmersion_closedImmersion_numericalHilbertCondition_of_isOpenAndClosed
    (hQ : CoherentSituation.IsOpenAndClosedCondition
      (structureSheafQuotSituation f hf).toCoherentSituation N.HasNumericalInvariants) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (numericalHilbertCondition f hf hbc).ι :=
  relative_openImmersion_closedImmersion_hilbertCondition_ι f hf
    (CoherentSituation.numerical_points_of_hom (χ := N.numericalEuler) N.P hbc)
    hQ.isCutOutOnTestSchemes

/-- The fibrewise invariants `χ_i(t) = χ(X_t, E_{i,t} ⊗^𝐋 𝒪_{Z_t})` of the families classified by
`Hilb_{X/B}`, read on the points of the test schemes: the invariants of Situation 0DNC of their
objects `(T, 𝒪_Z)` of `Coh_{X/B}`. -/
def numericalHilbertEulerData : HilbertEulerData f N.I :=
  HilbertEulerData.ofCoherent f hf
    (CoherentSituation.schemePointsFunction
      (D := (structureSheafQuotSituation f hf).toCoherentSituation)
      N.numericalEuler)
    (CoherentSituation.schemePointsFunction_hom hbc)

/-- **`HilbertEulerData.numericalHilbertFunctor` is `Quot^P_{𝒪_X/X/B}`.**  For the fibrewise
invariants of Situation 0DNC, a family `Z ⊆ X_T` over a scheme `T` over `B` lies in
`AlgebraicGeometry.Space.HilbertEulerData.numericalHilbertFunctor` exactly when, read over the
scheme of the site underlying `T`, it lies in `Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B}`. -/
theorem isPrescribed_numericalHilbertEulerData_iff {T : SchemesOverPresheaf B S hS Y}
    (z : HilbertFamily f T) :
    (numericalHilbertEulerData f hf hbc).IsPrescribed N.P z ↔
      z.toOver f ∈ (numericalHilbertCondition f hf hbc).obj (Opposite.op T.left) :=
  (isPrescribed_ofCoherent_iff f hf
    (CoherentSituation.schemePointsFunction
      (D := (structureSheafQuotSituation f hf).toCoherentSituation) N.numericalEuler)
    (CoherentSituation.schemePointsFunction_hom hbc) N.P z).trans
    (CoherentSituation.forall_schemePointsFunction_eq_iff N.P _)

end Assertions

end AlgebraicGeometry.Space

end
