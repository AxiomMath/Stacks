module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertNumericalQuotFibreProduct
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImagePerfect
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackNoetherianDescent
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.HilbertPolynomialHilbertQuot
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotConditionTransport
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFiniteProjectiveModel

/-!
# `Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B}` (Stacks 0DPG)

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation, let `I` be a
set, `E_i ∈ D(𝒪_X)` perfect for `i ∈ I`, and `P : I → ℤ`: the standing data
`AlgebraicGeometry.Space.NumericalSituation` of Situation 0DNC.  Since
`Hilb_{X/B} = Quot_{𝒪_X/X/B}` (Stacks 0D00), Stacks 0DPG defines

`Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B} = Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`

with `Quot^P` as in Stacks 0DP6.  A family `Z ⊆ X_T` lies in `Hilb^P_{X/B}` when its object
`(T, 𝒪_Z)` of `Coh_{X/B}` has `χ_i(t) = χ(K_i ⊗^𝐋 κ(t)) = P(i)` for every `i ∈ I` and every
`t ∈ |T|`, where `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝒪_Z)`.  The remark asserts that
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion, and an open and closed immersion when `I`
is finite, when `B` is locally Noetherian, or when `I = ℤ` and `E_i = 𝓛^{⊗ i}` for an invertible
`𝒪_X`-module `𝓛`, in which case it is written `Hilb^{P, 𝓛}_{X/B}`.

All of this follows by base change from the same assertions about
`Coh^P_{X/B} ⊆ Coh_{X/B}` (Stacks 0DND, 0DNE).  The inputs of those are that the functions `χ_i`
are compatible with pullback along the morphisms of `Coh_{X/B}` and locally constant, both
consequences of Stacks 0A1P (`K_i` is perfect and its formation commutes with base change) and
Stacks 0D1Z.

## Main definitions

* `AlgebraicGeometry.Space.numericalHilbertSubfunctor`: **`Hilb^P_{X/B}`**, the subfunctor of
  the Hilbert presheaf corresponding to `Quot^P_{𝒪_X/X/B}`.
* `AlgebraicGeometry.Space.hilbertPolynomialHilbertSubfunctor`: **`Hilb^{P, 𝓛}_{X/B}`**, the case
  `I = ℤ`, `E_n = 𝓛^{⊗ n}`.

## Main results

* `AlgebraicGeometry.Space.mem_numericalHilbertSubfunctor_iff_exists_numericalQuot`: a family
  lies in `Hilb^P_{X/B}` exactly when its quotient `𝒪_{X_T} ⟶ 𝒪_Z` lifts to the fibre product
  `Quot^P_{𝒪_X/X/B}` of Stacks 0DP6.
* `AlgebraicGeometry.Space.relative_closedImmersion_flat_numericalHilbertSubfunctor_ι`:
  `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion.
* `relative_openImmersion_closedImmersion_numericalHilbertSubfunctor_ι_of_finite`:
  `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion when `I` is finite.
* `relative_openImmersion_closedImmersion_numericalHilbertSubfunctor_ι_of_isLocallyNoetherian`:
  `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion when `B` is locally Noetherian.
* `relative_openImmersion_closedImmersion_hilbertPolynomialHilbertSubfunctor_ι`:
  `Hilb^{P, 𝓛}_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion.

## Implementation notes

The Hilbert presheaf takes values in `Type (u + 1)`, so "`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat
closed immersion" is representability of the inclusion of the subfunctor, along
`CategoryTheory.uliftYoneda.{u + 1}`, by morphisms of schemes which are flat closed immersions;
likewise for open and closed immersions.  In the case `I = ℤ`, `E_n = 𝓛^{⊗ n}` the condition is
read, as in Stacks 0DNF, on the Euler characteristics `χ(X_t, 𝒪_{Z_t} ⊗ 𝓛_t^{⊗ n})` of the
fibres (`AlgebraicGeometry.Space.CoherentObject.HasHilbertPolynomial`), so that
`Hilb^{P, 𝓛}_{X/B}` is the inverse image of
`Quot^{P, 𝓛}_{𝒪_X/X/B}` (`AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot`);
by the base change of Stacks 0A1P these are the invariants `χ(K_n ⊗^𝐋 κ(t))` of
Situation 0DNC for `E_n = 𝓛^{⊗ n}`.  An algebraic space is locally Noetherian when every
scheme étale over it is locally Noetherian (Stacks 03E2), which is
`AlgebraicGeometry.Space.IsLocallyNoetherian`.

## References

* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 03E2](https://stacks.math.columbia.edu/tag/03E2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  (N : NumericalSituation.{u, v, u} B S hS (structureSheafQuotSituation f hf).toCoherentSituation)

/-- `Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B}`: the subfunctor of the Hilbert presheaf of the families
`Z ⊆ X_T` whose object `(T, 𝒪_Z)` of `Coh_{X/B}` lies in `Coh^P_{X/B}`: for every `i ∈ I` and
every point `t` of `T`, `χ(K_i ⊗^𝐋 κ(t)) = P(i)` with `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝒪_Z)`.  It is
the subfunctor that the fibre product `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}` of Stacks 0DP6
cuts out of `Hilb_{X/B}` through Stacks 0D00
(`AlgebraicGeometry.Space.mem_numericalHilbertSubfunctor_iff_exists_numericalQuot`), and a
subfunctor because the `χ_i` are compatible with pullback (Stacks 0A1P). -/
@[stacks 0DPG "the definition of `Hilb^P_{X/B}` as the subfunctor of `Hilb_{X/B}` corresponding \
to `Quot^P_{𝒪_X/X/B} = Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`, for the actual invariants \
`χ(K_i ⊗^𝐋 κ(t))` of Situation 0DNC"]
def numericalHilbertSubfunctor : Subfunctor (hilbertPresheaf f) :=
  numericalHilbertCondition f hf (N := N) fun φ i t => N.numericalEuler_eq_of_hom φ i t

/-- A family lies in `Hilb^P_{X/B}` exactly when its object `(T, 𝒪_Z)` of `Coh_{X/B}` lies in
`Coh^P_{X/B}`. -/
theorem mem_numericalHilbertSubfunctor_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (hilbertPresheaf f).obj T) :
    x ∈ (numericalHilbertSubfunctor f hf N).obj T ↔
      N.HasNumericalInvariants (hilbertCohObject f hf x) :=
  Iff.rfl

/-- A family `Z ⊆ X_T` lies in `Hilb^P_{X/B}` exactly when its quotient `𝒪_{X_T} ⟶ 𝒪_Z`, the
section of `Quot_{𝒪_X/X/B}` over `T` it corresponds to under `Hilb_{X/B} = Quot_{𝒪_X/X/B}`
(Stacks 0D00), lifts to the 2-fibre product
`Quot^P_{𝒪_X/X/B} = Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}` of Stacks 0DP6
(`AlgebraicGeometry.Space.QuotSituation.numericalQuot`). -/
@[stacks 0DPG "`Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B}`: a family lies in `Hilb^P_{X/B}` exactly when \
its quotient, through `Hilb_{X/B} = Quot_{𝒪_X/X/B}` (0D00), lifts to the 2-fibre product \
`Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}` of 0DP6"]
theorem mem_numericalHilbertSubfunctor_iff_exists_numericalQuot {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (hilbertPresheaf f).obj T) :
    x ∈ (numericalHilbertSubfunctor f hf N).obj T ↔
      ∃ P : (structureSheafQuotSituation f hf).NumericalQuotObjects N,
        P.x = ((hilbertPresheafIsoQuotSitePresheaf f hf).hom.app T x).toQuotObjects :=
  mem_numericalHilbertCondition_iff_exists_numericalQuot f hf
    N.numericalEuler_eq_of_hom x

/-- `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion: its inclusion is representable
by morphisms of schemes which are flat closed immersions.  This is the base change of
`Coh^P_{X/B} ⟶ Coh_{X/B}`, a flat closed immersion by Stacks 0DND. -/
@[stacks 0DPG "`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is a flat closed immersion"]
theorem relative_closedImmersion_flat_numericalHilbertSubfunctor_ι :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (numericalHilbertSubfunctor f hf N).ι :=
  relative_closedImmersion_flat_numericalHilbertCondition_of_isLocallyConstant f hf
    N.numericalEuler_eq_of_hom
    N.isLocallyConstant_numericalEuler

/-- If `I` is finite, then `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion. -/
@[stacks 0DPG "for `I` finite, `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion"]
theorem relative_openImmersion_closedImmersion_numericalHilbertSubfunctor_ι_of_finite
    [Finite N.I] :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (numericalHilbertSubfunctor f hf N).ι :=
  relative_openImmersion_closedImmersion_numericalHilbertCondition_of_isLocallyConstant f hf
    N.numericalEuler_eq_of_hom
    N.isLocallyConstant_numericalEuler

/-- If every scheme étale over `B` is locally Noetherian (Stacks 03E2), then
`Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed immersion, whatever the index set. -/
@[stacks 0DPG "for `B` locally Noetherian, `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is an open and closed \
immersion"]
theorem relative_openImmersion_closedImmersion_numericalHilbertSubfunctor_ι_of_isLocallyNoetherian
    (hY : IsLocallyNoetherian B S hS Y.1) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (numericalHilbertSubfunctor f hf N).ι :=
  relative_openImmersion_closedImmersion_numericalHilbertCondition_of_isOpenAndClosed f hf
    N.numericalEuler_eq_of_hom
    (N.isOpenAndClosedCondition_hasNumericalInvariants_of_noetherianDescent
      N.numericalEuler_eq_of_hom N.isLocallyConstant_numericalEuler
      fun A t => CoherentSituation.exists_noetherianDescent_of_isLocallyNoetherian _ hY A t)

section HilbertPolynomial

variable (L : Modules.{u, u} B S hS X.1 X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
  (P : ℤ → ℤ)

/-- `Hilb^{P, 𝓛}_{X/B}`: the case `I = ℤ`, `E_n = 𝓛^{⊗ n}` for an invertible `𝒪_X`-module `𝓛`,
the subfunctor of the Hilbert presheaf of the families `Z ⊆ X_T` whose object `(T, 𝒪_Z)` lies in
`Coh^{P, 𝓛}_{X/B}` of Stacks 0DNF: `P(n) = χ(X_t, 𝒪_{Z_t} ⊗ 𝓛_t^{⊗ n})` for every `n ∈ ℤ` and
every point `t` of `T`.  It is the inverse image of `Quot^{P, 𝓛}_{𝒪_X/X/B}` under
`Hilb_{X/B} = Quot_{𝒪_X/X/B}` (Stacks 0D00). -/
@[stacks 0DPG "the notation `Hilb^{P, L}_{X/B}` for the case `I = ℤ`, `E_n = L^{⊗ n}`: the \
families `Z ⊆ X_T` with `P(n) = χ(X_t, 𝒪_{Z_t} ⊗ L_t^{⊗ n})` for all `n` and `t`, the inverse \
image of `Quot^{P, L}_{𝒪_X/X/B}` under `Hilb_{X/B} = Quot_{𝒪_X/X/B}`"]
alias hilbertPolynomialHilbertSubfunctor := AlgebraicGeometry.Space.hilbertPolynomialHilbert

/-- A family lies in `Hilb^{P, 𝓛}_{X/B}` exactly when its quotient `𝒪_{X_T} ⟶ 𝒪_Z` lies in
`Quot^{P, 𝓛}_{𝒪_X/X/B}`, that is, has `P(n) = χ(X_t, 𝒪_{Z_t} ⊗ 𝓛_t^{⊗ n})` for all `n` and `t`
(`AlgebraicGeometry.Space.QuotSituation.mem_hilbertPolynomialQuot_iff`). -/
theorem mem_hilbertPolynomialHilbertSubfunctor_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (hilbertPresheaf f).obj T) :
    x ∈ (hilbertPolynomialHilbertSubfunctor f hf L P).obj T ↔
      (hilbertPresheafIsoQuotSitePresheaf f hf).hom.app T x ∈
        ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P).obj T :=
  Iff.rfl

/-- In the case `I = ℤ`, `E_n = 𝓛^{⊗ n}`, `Hilb^{P, 𝓛}_{X/B} ⟶ Hilb_{X/B}` is an open and
closed immersion, the base change of the open and closed substack `Coh^{P, 𝓛}_{X/B} ⊆ Coh_{X/B}`
of Stacks 0DNF. -/
@[stacks 0DPG "for `I = ℤ` and `E_n = L^{⊗ n}`, `Hilb^{P, L}_{X/B} ⟶ Hilb_{X/B}` is an open and \
closed immersion"]
theorem relative_openImmersion_closedImmersion_hilbertPolynomialHilbertSubfunctor_ι :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (hilbertPolynomialHilbertSubfunctor f hf L P).ι :=
  MorphismProperty.relative_preimage_ι _
    ((structureSheafQuotSituation f hf).relative_openImmersion_closedImmersion_quotCondition_ι
      (fun m h => @CoherentObject.hasHilbertPolynomial_of_coherentHom B S hS _ L hL P _ _ m h)
      (CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial
        (D := (structureSheafQuotSituation f hf).toCoherentSituation) L (hL := hL)
          P).isCutOutOnTestSchemes)

end HilbertPolynomial

end AlgebraicGeometry.Space

end
