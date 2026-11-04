module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Algebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.LocalPowerProduct
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic

/-!
# The open `U(ψ)` attached to an invertible sheaf and a graded map into its powers

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `f : X ⟶ S` a morphism of
schemes, `ℒ` an invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}` a homomorphism of
graded `𝒪_X`-algebras. This file defines the open

  `U(ψ) = ⋃_{(U, V, a)} U_{ψ(a)}`

where `V ⊆ S` runs over the affine opens, `U = f^{-1}(V)`, and `a ∈ 𝒜(V)_+` over the homogeneous
sections of positive degree `d`; the value `ψ(a)` is a section of `ℒ^{⊗ d}` over `U`, and
`U_{ψ(a)} ⊆ X` is the open on which it does not vanish.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`: an invertible module
  `ℒ` on a scheme over the base together with the homogeneous components of `ψ`, written under
  the pullback–pushforward adjunction as maps `𝒜_n ⟶ f_*(ℒ^{⊗ n})`, and multiplicative across
  degrees.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.value`: the section
  `ψ(a) ∈ Γ(f^{-1}(V), ℒ^{⊗ d})` attached to a homogeneous `a ∈ 𝒜_d(V)`.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.nonvanishingOpenAt`:
  the open `U_{ψ(a)} ⊆ X` on which `ψ(a)` does not vanish.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.PositiveSection`: an index triple
  `(V, d, a)`: an affine open of the base, a positive degree, and a homogeneous section of that
  degree over it.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.coveringOpen`: the open
  `U(ψ)`, the supremum of the `U_{ψ(a)}` over those triples.

## Main results

* `…GradedPowerMap.value_mul`: `ψ(a · b) = ψ(a) · ψ(b)` on homogeneous sections.
* `…GradedPowerMap.nonvanishingOpenAt_le_preimage`: `U_{ψ(a)} ⊆ f^{-1}(V)`.
* `…GradedPowerMap.nonvanishingOpenAt_le_coveringOpen`: each member `U_{ψ(a)}` of the family lies
  in `U(ψ)`.
* `…GradedPowerMap.exists_mem_openOfPositiveSection_of_mem_coveringOpen` and
  `…GradedPowerMap.mem_coveringOpen_iff`: a point lies in `U(ψ)` exactly when some member of the
  family contains it.
* `…GradedPowerMap.coveringOpen_congr`: `U(ψ)` depends on `ψ` only through the opens `U_{ψ(a)}`.
* `…GradedPowerMap.coveringOpen_eq_iSup`, `…GradedPowerMap.coveringOpen_le_iff`: `U(ψ)` is the
  union of the opens `U_{ψ(a)}`, and lies in an open exactly when each of them does.

## References

* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0D2Y](https://stacks.math.columbia.edu/tag/0D2Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S)

/-! ### The data -/

/-- An invertible `𝒪_X`-module `ℒ` on a scheme `X` over the base together with the homogeneous
components of a homomorphism of graded `𝒪_X`-algebras `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`, written
under the pullback–pushforward adjunction as maps `𝒜_n ⟶ f_*(ℒ^{⊗ n})` and multiplicative across
degrees. The unit axiom `ψ(1) = 1` is not imposed. -/
public structure GradedPowerMap {T : Scheme.{u}} (f : T ⟶ S) where
  /-- The invertible module `ℒ` on the scheme over the base. -/
  L : T.Modules
  /-- It is invertible. -/
  invertible : Stacks.Ample.IsInvertibleModule T L
  /-- The homogeneous components of `ψ`, in adjoint form. -/
  ψ (n : ℕ) : A.piece (n : ℤ) ⟶ (Scheme.Modules.pushforward f).obj (natTensorPow L n)
  /-- The components of `ψ` are multiplicative across degrees: for homogeneous sections
  `a ∈ 𝒜_n(V)` and `b ∈ 𝒜_m(V)` over an open `V` of the base, the value of `ψ` at their product
  is the product of the values, taken in `ℒ^{⊗ n}` and `ℒ^{⊗ m}` over `f^{-1}(V)`. -/
  map_mul (n m : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V))
      (b : Γ(A.piece (m : ℤ), V)) :
    (ψ (n + m)).val.app (op V) ((A.mul (n : ℤ) (m : ℤ)).app V a b)
      = @Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections T L invertible n m
          (f ⁻¹ᵁ V) ((ψ n).val.app (op V) a) ((ψ m).val.app (op V) b)

attribute [instance] GradedPowerMap.invertible

namespace GradedPowerMap

variable {A} {T : Scheme.{u}} {f : T ⟶ S} (P : GradedPowerMap A f)

/-- The section `ψ(a) ∈ Γ(f^{-1}(V), ℒ^{⊗ n})` attached to a homogeneous section `a ∈ 𝒜_n(V)`:
the component `ψ_n` evaluated on `a`, the sections of `f_*(ℒ^{⊗ n})` over `V` being those of
`ℒ^{⊗ n}` over `f^{-1}(V)`. -/
public def value (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    Γ(natTensorPow P.L n, f ⁻¹ᵁ V) :=
  (P.ψ n).val.app (op V) a

/-- `ψ` is multiplicative across degrees on values: `ψ(a · b) = ψ(a) · ψ(b)` in
`Γ(f^{-1}(V), ℒ^{⊗ (n + m)})`. -/
@[stacks 01O8 "item (6): the components of psi are multiplicative across degrees, the value at a \
product of homogeneous sections over an open of the base being the product of the values in the \
tensor powers of L over the preimage of that open"]
public theorem value_mul (n m : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V))
    (b : Γ(A.piece (m : ℤ), V)) :
    P.value (n + m) V ((A.mul (n : ℤ) (m : ℤ)).app V a b)
      = Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections P.L
          (P.value n V a) (P.value m V b) :=
  P.map_mul n m V a b

/-- The open `U_{ψ(a)} ⊆ X` on which the section `ψ(a)` of `ℒ^{⊗ n}` over `f^{-1}(V)` does not
vanish. -/
public def nonvanishingOpenAt (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) : T.Opens :=
  Stacks.SectionPowerOpen.nonvanishingOpenOn (natTensorPow P.L n) (f ⁻¹ᵁ V) (P.value n V a)

/-- `U_{ψ(a)}` lies in `f^{-1}(V)`. -/
public theorem nonvanishingOpenAt_le_preimage (n : ℕ) (V : S.Opens)
    (a : Γ(A.piece (n : ℤ), V)) : P.nonvanishingOpenAt n V a ≤ f ⁻¹ᵁ V :=
  Stacks.SectionPowerOpen.nonvanishingOpenOn_le (natTensorPow P.L n) (f ⁻¹ᵁ V) (P.value n V a)

/-- Membership in `U_{ψ(a)}`, unfolded to the nonvanishing locus of `ψ(a)` over `f^{-1}(V)`. -/
public theorem mem_nonvanishingOpenAt_iff (n : ℕ) (V : S.Opens)
    (a : Γ(A.piece (n : ℤ), V)) (x : T) :
    x ∈ P.nonvanishingOpenAt n V a ↔
      x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
        (natTensorPow P.L n) (f ⁻¹ᵁ V) (P.value n V a) :=
  Iff.rfl

end GradedPowerMap

/-! ### The index triples -/

/-- An index triple `(V, d, a)`: an affine open `V` of the base, a positive degree `d`, and a
homogeneous section of `𝒜` of degree `d` over `V`. The degree is presented as `deg + 1`. -/
public structure PositiveSection where
  /-- The degree, less one: the degree of the section is `deg + 1 ≥ 1`. -/
  deg : ℕ
  /-- The affine open of the base. -/
  base : S.Opens
  /-- It is affine. -/
  isAffineOpen : IsAffineOpen base
  /-- The homogeneous section of `𝒜` of degree `deg + 1` over it. -/
  val : Γ(A.piece ((deg + 1 : ℕ) : ℤ), base)

namespace GradedPowerMap

variable {A} {T : Scheme.{u}} {f : T ⟶ S} (P : GradedPowerMap A f)

/-- The member `U_{ψ(a)}` of the family indexed by a triple. -/
public def openOfPositiveSection (p : PositiveSection A) : T.Opens :=
  P.nonvanishingOpenAt (p.deg + 1) p.base p.val

/-- The open `U(ψ) = ⋃_{(U, V, a)} U_{ψ(a)}`: the union of the opens on which the values of `ψ`
at the homogeneous sections of positive degree over the affine opens of the base do not
vanish. -/
@[stacks 01O8 "the open U(psi) = union over triples (U, V, a) -- V affine open of the base, \
U = f^{-1}(V), a a homogeneous section of positive degree of A over V -- of the open U_{psi(a)} \
on which the section psi(a) of L^{tensor deg(a)} over U does not vanish"]
public def coveringOpen : T.Opens :=
  ⨆ p : PositiveSection A, P.openOfPositiveSection p

/-- Each `U_{ψ(a)}` of the family lies in `U(ψ)`. -/
public theorem openOfPositiveSection_le_coveringOpen (p : PositiveSection A) :
    P.openOfPositiveSection p ≤ P.coveringOpen :=
  le_iSup P.openOfPositiveSection p

/-- Each `U_{ψ(a)}`, written out on a triple, lies in `U(ψ)`. -/
public theorem nonvanishingOpenAt_le_coveringOpen (n : ℕ) (V : S.Opens) (hV : IsAffineOpen V)
    (a : Γ(A.piece ((n + 1 : ℕ) : ℤ), V)) :
    P.nonvanishingOpenAt (n + 1) V a ≤ P.coveringOpen :=
  P.openOfPositiveSection_le_coveringOpen ⟨n, V, hV, a⟩

/-- A point of `U(ψ)` lies in `U_{ψ(a)}` for some triple. -/
public theorem exists_mem_openOfPositiveSection_of_mem_coveringOpen {x : T}
    (hx : x ∈ P.coveringOpen) : ∃ p : PositiveSection A, x ∈ P.openOfPositiveSection p :=
  Opens.mem_iSup.mp hx

/-- A point lies in `U(ψ)` exactly when the value of `ψ` at some homogeneous section of positive
degree over some affine open of the base does not vanish there. -/
public theorem mem_coveringOpen_iff {x : T} :
    x ∈ P.coveringOpen ↔ ∃ p : PositiveSection A, x ∈ P.openOfPositiveSection p :=
  Opens.mem_iSup

/-- `U(ψ)` depends on `ψ` only through its values on homogeneous sections of positive degree over
the affine opens of the base. -/
public theorem coveringOpen_congr {P' : GradedPowerMap A f}
    (h : ∀ p : PositiveSection A, P.openOfPositiveSection p = P'.openOfPositiveSection p) :
    P.coveringOpen = P'.coveringOpen :=
  iSup_congr h

/-- `U(ψ)` is the union of the opens `U_{ψ(a)}`. -/
public theorem coveringOpen_eq_iSup :
    P.coveringOpen = ⨆ p : PositiveSection A, P.openOfPositiveSection p :=
  rfl

/-- `U(ψ)` lies in an open exactly when every `U_{ψ(a)}` does. -/
public theorem coveringOpen_le_iff {O : T.Opens} :
    P.coveringOpen ≤ O ↔ ∀ p : PositiveSection A, P.openOfPositiveSection p ≤ O :=
  iSup_le_iff

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
