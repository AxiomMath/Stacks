module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.LogarithmicDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.WedgeDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex

/-!
# The repeated factor on the left of the Gysin wedge

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and write
`u = f₁ ⋯ f_c` for the product of the equations. This file proves the vanishing

`d u ∧ (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = 0`

for an arbitrary local `p`-form `ω`, together with the single-equation case
`d f_j ∧ (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = 0` it is assembled from.

The left-handed form is *not* a consequence of the right-handed vanishing
`(ω ∧ d f_j) ∧ d f₁ ∧ ⋯ ∧ d f_c = 0` for a general graded algebra with a square-zero degree-one
generator — in the algebra `ℤ⟨a, w⟩/(a²)` with `a` and `w` of degree one, `a · w · a ≠ 0` — so
some commutation law is needed; here it is graded commutativity of the exterior algebra,
`AlgebraicGeometry.SheafOfModules.formProduct_comm`.

## Main results

* `AlgebraicGeometry.SheafOfModules.formProduct_exactOne_prodDegOne_eq_zero`: **the left-handed
  vanishing for a single equation**, `d b_j ∧ (ω ∧ d b₁ ∧ ⋯ ∧ d b_c) = 0`.
* `AlgebraicGeometry.SheafOfModules.formProduct_exactOne_finProd_prodDegOne_eq_zero`: the same
  for the differential of an arbitrary finite ordered product of the `b_j`, with repetitions
  allowed.
* `AlgebraicGeometry.SheafOfModules.formProduct_exactOne_prod_prodDegOne_eq_zero`: **the
  vanishing for the product of all the equations**, `d(b₁ ⋯ b_c) ∧ (ω ∧ d b₁ ∧ ⋯ ∧ d b_c) = 0`.
* `AlgebraicGeometry.Scheme.Hom.exactOneForm_prod_equationsWedge_eq_zero`: the same statement for
  a morphism of schemes and global equations, phrased with
  `AlgebraicGeometry.Scheme.Hom.equationsWedge`.

## Implementation notes

Products of forms are taken in the degree-normalized spelling
`AlgebraicGeometry.SheafOfModules.formProduct`, whose target degree is computed in `ℕ`; the two
parenthesizations `(d b ∧ ω) ∧ (d b₁ ∧ ⋯ ∧ d b_c)` and `d b ∧ (ω ∧ d b₁ ∧ ⋯ ∧ d b_c)` therefore
live in the exterior powers of degree `1 + p + c` and `1 + (p + c)`, which are equal but not
syntactically so, and `AlgebraicGeometry.SheafOfModules.reindexForm` transports between them.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### Bookkeeping -/

/-- The exact differential of the unit section vanishes: a derivation kills `1`. -/
private alias exactOne_one' := AlgebraicGeometry.SheafOfModules.exactOne_one

/-- The wedge product of zero with a local section vanishes. -/
private alias formProduct_zero_left' := formProduct_zero_left

/-- The wedge product is additive in its left factor. -/
private theorem formProduct_add_left (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω ω' : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    formProduct B p q U (ω + ω') η = formProduct B p q U ω η + formProduct B p q U ω' η :=
  congrFun (congrArg (fun k : (B.exteriorPower q).val.obj U →+ _ => ⇑k)
    (map_add ((B.exterior.mul (p : ℤ) (q : ℤ)).app U) ω ω')) η

/-- The wedge product commutes with scaling its left factor by a local section of the structure
sheaf. -/
theorem formProduct_smul_left (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (a : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (η : (B.exteriorPower q).val.obj U) :
    formProduct B p q U (a • ω) η = a • formProduct B p q U ω η :=
  (B.exterior.mul (p : ℤ) (q : ℤ)).map_smul_left U a ω η

/-- The wedge product commutes with scaling its left factor by an integer: the integer action is
the action of its image in the structure sheaf. -/
private theorem formProduct_zsmul_left (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ) (k : ℤ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    formProduct B p q U (k • ω) η = k • formProduct B p q U ω η := by
  rw [← Int.cast_smul_eq_zsmul (X.sheaf.obj.obj U) k ω, formProduct_smul_left,
    Int.cast_smul_eq_zsmul]

/-- Reindexing the zero form gives the zero form. -/
theorem reindexForm_zero {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ) :
    reindexForm B h U (0 : (B.exteriorPower m).val.obj U) = 0 := by
  subst h; rfl

/-- A form whose reindexing vanishes vanishes. -/
private theorem eq_zero_of_reindexForm_eq_zero {m n : ℕ} (h : m = n)
    (U : (Opens X.carrier)ᵒᵖ) (x : (B.exteriorPower m).val.obj U)
    (hx : reindexForm B h U x = 0) : x = 0 := by
  subst h; exact hx

/-- Reindexing the left factor of a wedge product reindexes the product. -/
private theorem formProduct_reindexForm_left {m n r : ℕ} (h : m = n)
    (U : (Opens X.carrier)ᵒᵖ) (x : (B.exteriorPower m).val.obj U)
    (z : (B.exteriorPower r).val.obj U) :
    formProduct B n r U (reindexForm B h U x) z =
      reindexForm B (congrArg (fun k : ℕ => k + r) h) U (formProduct B m r U x z) := by
  subst h; rfl

/-! ### The left-handed vanishing -/

/-- **The repeated factor vanishes on the left, for a single equation.** For local sections
`b₁, …, b_c` of the structure sheaf, a local `p`-form `ω` and an index `j`,

`d b_j ∧ (ω ∧ d b₁ ∧ ⋯ ∧ d b_c) = 0`. -/
theorem formProduct_exactOne_prodDegOne_eq_zero (p c : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (b : Fin c → X.sheaf.obj.obj U) (j : Fin c) :
    formProduct B 1 (p + c) U (exactOne B U (b j))
        (formProduct B p c U ω
          (B.exterior.prodDegOne U c fun i => exactOne B U (b i))) = 0 := by
  have hright : formProduct B (p + 1) c U (formProduct B p 1 U ω (exactOne B U (b j)))
      (B.exterior.prodDegOne U c fun i => exactOne B U (b i)) = 0 :=
    _root_.SheafOfModules.GradedAlgebra.mul_generator_mul_prodDegOne_eq_zero
      B.squareZero_exteriorGenerator U (p : ℤ) ω
      (fun i => ((universalDerivation.{u, u, u} φ).app U).d (b i)) j
  refine eq_zero_of_reindexForm_eq_zero B (Nat.add_assoc 1 p c).symm U _ ?_
  rw [← formProduct_assoc B 1 p c U (exactOne B U (b j)) ω _,
    formProduct_comm B 1 p U (exactOne B U (b j)) ω, formProduct_zsmul_left,
    formProduct_reindexForm_left, hright, reindexForm_zero, smul_zero]

/-- **The repeated factor vanishes on the left, for an arbitrary ordered product of the
equations.** For any finite word `s` in the indices `1, …, c`,

`d (b_{s(1)} ⋯ b_{s(n)}) ∧ (ω ∧ d b₁ ∧ ⋯ ∧ d b_c) = 0`. -/
theorem formProduct_exactOne_finProd_prodDegOne_eq_zero (p c : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (b : Fin c → X.sheaf.obj.obj U) :
    ∀ (n : ℕ) (s : Fin n → Fin c),
      formProduct B 1 (p + c) U (exactOne B U (∏ i, b (s i)))
          (formProduct B p c U ω
            (B.exterior.prodDegOne U c fun i => exactOne B U (b i))) = 0 := by
  intro n
  induction n with
  | zero =>
      intro s
      rw [Fin.prod_univ_zero, exactOne_one' B U]
      exact formProduct_zero_left' B 1 (p + c) U _
  | succ n ih =>
      intro s
      rw [Fin.prod_univ_castSucc, exactOne_mul, formProduct_add_left, formProduct_smul_left,
        formProduct_smul_left, formProduct_exactOne_prodDegOne_eq_zero B p c U ω b
          (s (Fin.last n)), ih fun i => s i.castSucc, smul_zero, smul_zero, add_zero]

/-- **The repeated factor vanishes on the left, for the product of all the equations.** For local
sections `b₁, …, b_c` of the structure sheaf and a local `p`-form `ω`,

`d (b₁ ⋯ b_c) ∧ (ω ∧ d b₁ ∧ ⋯ ∧ d b_c) = 0`. -/
theorem formProduct_exactOne_prod_prodDegOne_eq_zero (p c : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (b : Fin c → X.sheaf.obj.obj U) :
    formProduct B 1 (p + c) U (exactOne B U (∏ j, b j))
        (formProduct B p c U ω
          (B.exterior.prodDegOne U c fun i => exactOne B U (b i))) = 0 :=
  formProduct_exactOne_finProd_prodDegOne_eq_zero B p c U ω b c fun i => i

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- **The differential of the product of the equations kills the numerator of the Gysin
fraction.** For a morphism `π : X ⟶ S`, global functions `f₁, …, f_c` on `X`, a local `p`-form
`ω` and `u = f₁ ⋯ f_c`,

`d u ∧ (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = 0`,

the wedge on the right being the numerator of the Gysin formula of [Stacks, Tag 0G83]. -/
theorem exactOneForm_prod_equationsWedge_eq_zero (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (p : ℕ) (U : X.Opensᵒᵖ)
    (ω : ((deRhamAlgebras π).exteriorPower p).val.obj U) :
    AlgebraicGeometry.SheafOfModules.formProduct (deRhamAlgebras π) 1 (p + c) U
        (exactOneForm π U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (∏ j, f j)))
        (AlgebraicGeometry.SheafOfModules.formProduct (deRhamAlgebras π) p c U ω
          ((equationsWedge π f).eval U)) = 0 := by
  have hres : X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (∏ j, f j) =
      ∏ j, X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j) :=
    map_prod (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom f Finset.univ
  rw [hres]
  exact AlgebraicGeometry.SheafOfModules.formProduct_exactOne_prod_prodDegOne_eq_zero
    (deRhamAlgebras π) p c U ω
    fun j => X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j)

end AlgebraicGeometry.Scheme.Hom

end
