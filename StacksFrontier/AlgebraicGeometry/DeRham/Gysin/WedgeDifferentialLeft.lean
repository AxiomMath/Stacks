module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.LocalizedLeibniz

/-!
# Differentiating a form with an exact one-form on its left

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, let `Ω = Ω_{𝒪_X/A}` be the sheaf of relative
differentials and let `B` also denote a package of the three algebras of Stacks Section 17.21 for
`Ω`. The graded Leibniz rule `AlgebraicGeometry.SheafOfModules.d_formProduct` says

`d (ω ∧ η) = d ω ∧ η + (-1)^p ω ∧ d η`

for arbitrary local sections `ω` of `Ωᵖ` and `η` of `Ωᵠ`. Its specialization to a **closed right**
factor is `AlgebraicGeometry.SheafOfModules.d_formProduct_of_closed_right`. This file records the
specialization to a **closed left** factor,

`d (ω ∧ η) = (-1)^p ω ∧ d η` when `d ω = 0`,

and the case of it the de Rham complex is actually reasoned with: an exact one-form is closed
(`AlgebraicGeometry.SheafOfModules.d_exactOne_eq_zero`), so

`d (d c ∧ ω) = - d c ∧ d ω`.

Together with the Leibniz rule against a scalar
`AlgebraicGeometry.SheafOfModules.d_smul` — `d (a · ω) = d a ∧ ω + a · d ω` — this is what lets a
formula built from `a · ω` and `d c ∧ ω` be differentiated term by term.

## Main results

* `AlgebraicGeometry.SheafOfModules.XIsoOfEq_hom_app_eq_reindexForm`: the reindexing isomorphism
  of the de Rham complex acts on local sections as `reindexForm`.
* `AlgebraicGeometry.SheafOfModules.d_reindexForm`: the commutation of the differential with a
  reindexing of its source.
* `AlgebraicGeometry.SheafOfModules.d_formProduct_of_closed_left`: **the graded Leibniz rule with
  a closed left factor.**
* `AlgebraicGeometry.SheafOfModules.d_formProduct_exactOne_left`: **the differential
  anticommutes with wedging an exact one-form on the left**, `d (d c ∧ ω) = - d c ∧ d ω`. This is
  the sheaf-level form of `KaehlerDifferential.deRhamDifferential_wedgeLeft_D`.

## Implementation notes

The degree of `d c ∧ ω` is `1 + p` as a wedge product and `p + 1` as a term of the de Rham
complex, so a reindexing is part of every statement. The spelling chosen is the one
`AlgebraicGeometry.SheafOfModules.d_smul` uses, namely
`reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω)`, so that the two
rules can be applied to the same term without a bridge. `d_reindexForm` is what moves the
differential across such a reindexing; it holds by `subst`, since a reindexing is a transport
along an equality of natural numbers.

## References

* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### Reindexing -/

/-- Reindexing twice, with the sign `(-1)^1` interposed, is a single reindexing followed by a
negation. This is the whole transport computation
`AlgebraicGeometry.SheafOfModules.d_formProduct_exactOne_left` performs once the Leibniz rule has
been applied, isolated so that both equalities of degrees can be discharged by `subst`. -/
private theorem reindexForm_neg_one_pow_one_reindexForm {m n k : ℕ} (h : m = n) (h' : n = k)
    (U : (Opens X.carrier)ᵒᵖ) (x : (B.exteriorPower m).val.obj U) :
    reindexForm B h' U ((-1 : ℤ) ^ 1 • reindexForm B h U x) =
      -reindexForm B (h.trans h') U x := by
  subst h
  subst h'
  rw [reindexForm_rfl, pow_one, neg_one_zsmul, reindexForm_rfl]

variable (D : DeRhamDifferential B)

/-- The reindexing isomorphism of the de Rham complex acts on local sections as
`AlgebraicGeometry.SheafOfModules.reindexForm`: both are the transport along the equality of
degrees. -/
theorem XIsoOfEq_hom_app_eq_reindexForm {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower m).val.obj U) :
    ((deRhamComplex B D).XIsoOfEq h).hom.val.app U x = reindexForm B h U x := by
  subst h
  rw [HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- **The differential commutes with a reindexing of its source.** Reindexing is a transport
along an equality of natural numbers, and the differential out of degree `n` is the differential
out of degree `m` when `m = n`. -/
theorem d_reindexForm {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower m).val.obj U) :
    ((deRhamComplex B D).d n (n + 1)).val.app U (reindexForm B h U x) =
      reindexForm B (congrArg (· + 1) h) U
        (((deRhamComplex B D).d m (m + 1)).val.app U x) := by
  subst h
  rfl

/-! ### The Leibniz rule with a closed left factor -/

/-- **The graded Leibniz rule with a closed left factor:** `d(ω ∧ η) = (-1)^p ω ∧ d(η)` when
`dω = 0`. The first summand of the Leibniz rule
`d(ω ∧ η) = d(ω) ∧ η + (-1)^p ω ∧ d(η)` vanishes. -/
theorem d_formProduct_of_closed_left (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U)
    (hω : ((deRhamComplex B D).d p (p + 1)).val.app U ω = 0) :
    ((deRhamComplex B D).d (p + q) (p + q + 1)).val.app U (formProduct B p q U ω η) =
      (-1 : ℤ) ^ p •
        ((deRhamComplex B D).XIsoOfEq (show p + (q + 1) = p + q + 1 by omega)).hom.val.app U
          (formProduct B p (q + 1) U ω (((deRhamComplex B D).d q (q + 1)).val.app U η)) := by
  have hz : formProduct B (p + 1) q U (((deRhamComplex B D).d p (p + 1)).val.app U ω) η = 0 := by
    rw [hω]
    exact congrFun (congrArg
      (fun k : (B.exteriorPower q).val.obj U →+ (B.exteriorPower (p + 1 + q)).val.obj U => ⇑k)
      (map_zero ((B.exterior.mul ((p + 1 : ℕ) : ℤ) (q : ℤ)).app U))) η
  rw [d_formProduct B D p q U ω η, hz,
    show ((deRhamComplex B D).XIsoOfEq (show p + 1 + q = p + q + 1 by omega)).hom.val.app U
      (0 : (B.exteriorPower (p + 1 + q)).val.obj U) = 0 from map_zero _, zero_add]

/-- **The de Rham differential anticommutes with wedging an exact one-form on the left:**
`d (d c ∧ ω) = - d c ∧ d ω`, for a local section `c` of the structure sheaf and an arbitrary
local `p`-form `ω`.

This is `AlgebraicGeometry.SheafOfModules.d_formProduct_of_closed_left` in the case `p = 1`,
whose hypothesis is the closedness of the exact one-form `d c`
(`AlgebraicGeometry.SheafOfModules.d_exactOne_eq_zero`), with the sign `(-1)^1` read as a
negation. It is the sheaf-level form of
`KaehlerDifferential.deRhamDifferential_wedgeLeft_D`. -/
theorem d_formProduct_exactOne_left (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (c : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) :
    ((deRhamComplex B D).d (p + 1) (p + 1 + 1)).val.app U
        (reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω)) =
      -reindexForm B (Nat.add_comm 1 (p + 1)) U
        (formProduct B 1 (p + 1) U (exactOne B U c)
          (((deRhamComplex B D).d p (p + 1)).val.app U ω)) := by
  have h : 1 + (p + 1) = 1 + p + 1 := by omega
  rw [d_reindexForm B D (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω),
    d_formProduct_of_closed_left B D 1 p U (exactOne B U c) ω (d_exactOne_eq_zero B D U c),
    XIsoOfEq_hom_app_eq_reindexForm B D h U]
  exact reindexForm_neg_one_pow_one_reindexForm B h (congrArg (· + 1) (Nat.add_comm 1 p)) U _

end AlgebraicGeometry.SheafOfModules
