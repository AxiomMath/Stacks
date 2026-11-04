module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# Transposing cycles, Chow classes and correspondences

Switching the two factors of a fibre product `X ×_S Y ≅ Y ×_S X` is an isomorphism over the
base, so pushing forward along it carries cycles on `X ×_S Y` to cycles on `Y ×_S X` and Chow
classes to Chow classes. On rational correspondences this is the *transpose* `c ↦ cᵗ`, and it
shifts the degree: for `X` equidimensional of dimension `d` and `Y` equidimensional of
dimension `e` it takes `Corrʳ(X, Y)` to `Corr^{d - e + r}(Y, X)`.

## Main definitions

* `Stacks.WeilCohomology.cycleTranspose`: transposition of cycles.
* `Stacks.WeilCohomology.chowTranspose`: transposition of Chow classes.
* `Stacks.WeilCohomology.Correspondence`: the space `Corrʳ(X, Y)` of rational correspondences
  of degree `r`.
* `Stacks.WeilCohomology.transpose`: transposition of rational correspondences.
* `Stacks.WeilCohomology.cycleTransposeEquiv`, `Stacks.WeilCohomology.chowTransposeEquiv` and
  `Stacks.WeilCohomology.transposeEquiv`: the same three maps read as *isomorphisms*, each with
  inverse the transpose in the other direction.

## Main results

* `Stacks.WeilCohomology.chowTranspose_mk` and `Stacks.WeilCohomology.transpose_tmul`
  evaluate the two induced maps on classes of cycles and on pure tensors.
* `Stacks.WeilCohomology.cycleTranspose_cycleTranspose` and
  `Stacks.WeilCohomology.chowTranspose_chowTranspose`: transposing twice is the identity, on
  cycles and on Chow classes, so that the transpose is an isomorphism (Stacks 0FG4).
* `Stacks.WeilCohomology.transposeEquiv_apply`: the isomorphism
  `Corrʳ(X, Y) ≃ Corr^{d - e + r}(Y, X)` is the transpose `c ↦ cᵗ`, and
  `Stacks.WeilCohomology.transposeEquiv_symm_tmul` identifies its inverse with the transpose
  back.

## Implementation notes

A correspondence of degree `r` from `X` to `Y` is an element of `CH^{d + r}(X × Y) ⊗ ℚ` for `X`
equidimensional of dimension `d`. Since the repository grades Chow groups by dimension and
`X × Y` has dimension `d + e`, this is `A_{e - r}(X × Y) ⊗ ℚ`, which depends on `d` only through
the degree shift; accordingly `Correspondence` records the dimension `e` of the second factor as
an explicit parameter and `transpose` takes the dimension `d` of the first factor as a further
one. Equidimensionality is not imposed: with the dimensions supplied as parameters the
definitions make sense, and are the intended ones, for any pair of schemes locally of finite
type over the base.

No declaration here takes a hypothesis of the form of Stacks 02S2: the factor switch is an
isomorphism, and pushforward along an isomorphism, `Stacks.Chow.chowPushforwardOfIso`, descends
to Chow groups by `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isIso`.

## References

* [Stacks Project, Tag 0FG4](https://stacks.math.columbia.edu/tag/0FG4)
-/

open AlgebraicGeometry

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- The factor switch `X ×_S Y ≅ Y ×_S X` is a morphism over the base. -/
theorem pullbackSymmetry_hom_comp_base {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) :
    (pullbackSymmetry sX sY).hom ≫ (pullback.fst sY sX ≫ sY) = pullback.fst sX sY ≫ sX := by
  rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pullback.condition.symm

/-- The factor switch is an involution: switching `X ×_S Y ≅ Y ×_S X` and then switching back
`Y ×_S X ≅ X ×_S Y` is the identity of `X ×_S Y`. -/
theorem pullbackSymmetry_hom_comp_pullbackSymmetry_hom {S X Y : Scheme.{u}} (sX : X ⟶ S)
    (sY : Y ⟶ S) :
    (pullbackSymmetry sX sY).hom ≫ (pullbackSymmetry sY sX).hom = 𝟙 (pullback sX sY) := by
  apply pullback.hom_ext <;> simp

/-- The inverse of the factor switch `X ×_S Y ≅ Y ×_S X` is the factor switch
`Y ×_S X ≅ X ×_S Y`. -/
theorem inv_pullbackSymmetry_hom {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) :
    inv (pullbackSymmetry sX sY).hom = (pullbackSymmetry sY sX).hom :=
  IsIso.inv_eq_of_hom_inv_id (pullbackSymmetry_hom_comp_pullbackSymmetry_hom sX sY)

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- **Stacks Project, Tag 0FG4.** Transposition of cycles on a fibre product: proper pushforward
along the factor switch `X ×_S Y ≅ Y ×_S X`. -/
@[stacks 0FG4 "transpose"]
def cycleTranspose (n : ℤ) :
    CycleGroup C (pullback.fst sX sY ≫ sX) n →+ CycleGroup C (pullback.fst sY sX ≫ sY) n :=
  properPushforwardHom C _ _ (pullbackSymmetry sX sY).hom
    (pullbackSymmetry_hom_comp_base sX sY) n

/-- **Stacks Project, Tag 0FG4.** Transposition of Chow classes on a fibre product, induced by
transposition of cycles. The factor switch is an isomorphism, so this needs no instance of
Stacks 02S2. -/
@[stacks 0FG4 "transpose"]
def chowTranspose (n : ℤ) :
    chowGroup C (pullback.fst sX sY ≫ sX) n →+ chowGroup C (pullback.fst sY sX ≫ sY) n :=
  chowPushforwardOfIso C _ _ (pullbackSymmetry sX sY).hom
    (pullbackSymmetry_hom_comp_base sX sY) n

/-- Transposing a cycle twice returns it. -/
theorem cycleTranspose_cycleTranspose (n : ℤ)
    (α : CycleGroup C (pullback.fst sX sY ≫ sX) n) :
    cycleTranspose C sY sX n (cycleTranspose C sX sY n α) = α := by
  have hcomp := congrFun (properPushforward_comp C (pullback.fst sX sY ≫ sX)
    (pullback.fst sY sX ≫ sY) (pullback.fst sX sY ≫ sX) (pullbackSymmetry sX sY).hom
    (pullbackSymmetry sY sX).hom (pullbackSymmetry_hom_comp_base sX sY)
    (pullbackSymmetry_hom_comp_base sY sX) n) α
  rw [Function.comp_apply, properPushforward_congr C (pullback.fst sX sY ≫ sX)
      (pullback.fst sX sY ≫ sX) ((pullbackSymmetry sX sY).hom ≫ (pullbackSymmetry sY sX).hom)
      (𝟙 (pullback sX sY)) (pullbackSymmetry_hom_comp_pullbackSymmetry_hom sX sY) _
      (Category.id_comp _) n, properPushforward_id] at hcomp
  exact hcomp

/-- **Stacks Project, Tag 0FG4.** Transposition of cycles on a fibre product is an isomorphism
of groups of `n`-cycles, with inverse the transposition in the other direction. -/
@[stacks 0FG4 "the transpose is an isomorphism, on cycles"]
def cycleTransposeEquiv (n : ℤ) :
    CycleGroup C (pullback.fst sX sY ≫ sX) n ≃+ CycleGroup C (pullback.fst sY sX ≫ sY) n where
  toFun := cycleTranspose C sX sY n
  invFun := cycleTranspose C sY sX n
  left_inv := cycleTranspose_cycleTranspose C sX sY n
  right_inv := cycleTranspose_cycleTranspose C sY sX n
  map_add' := map_add _

/-- `cycleTransposeEquiv` applied to a cycle is its transpose. -/
@[simp]
theorem cycleTransposeEquiv_apply (n : ℤ) (α : CycleGroup C (pullback.fst sX sY ≫ sX) n) :
    cycleTransposeEquiv C sX sY n α = cycleTranspose C sX sY n α :=
  rfl

/-- The inverse of `cycleTransposeEquiv` is the transposition in the other direction. -/
@[simp]
theorem cycleTransposeEquiv_symm_apply (n : ℤ)
    (α : CycleGroup C (pullback.fst sY sX ≫ sY) n) :
    (cycleTransposeEquiv C sX sY n).symm α = cycleTranspose C sY sX n α :=
  rfl

/-- The transpose of the class of a cycle is the class of its transpose. -/
@[simp]
theorem chowTranspose_mk (n : ℤ) (α : CycleGroup C (pullback.fst sX sY ≫ sX) n) :
    chowTranspose C sX sY n
        (QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX sY ≫ sX) n) α) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sY sX ≫ sY) n)
        (cycleTranspose C sX sY n α) :=
  rfl

/-- Transposing a Chow class twice returns it. -/
theorem chowTranspose_chowTranspose (n : ℤ) (α : chowGroup C (pullback.fst sX sY ≫ sX) n) :
    chowTranspose C sY sX n (chowTranspose C sX sY n α) = α := by
  have h := chowPushforwardOfIso_inv_comp C (pullback.fst sX sY ≫ sX)
    (pullback.fst sY sX ≫ sY) (pullbackSymmetry sX sY).hom
    (pullbackSymmetry_hom_comp_base sX sY) n α
  rwa [chowPushforwardOfIso_congr C (pullback.fst sY sX ≫ sY) (pullback.fst sX sY ≫ sX)
    (inv (pullbackSymmetry sX sY).hom) (pullbackSymmetry sY sX).hom
    (inv_pullbackSymmetry_hom sX sY) _ (pullbackSymmetry_hom_comp_base sY sX) n] at h

/-- **Stacks Project, Tag 0FG4.** Transposition of Chow classes on a fibre product is an
isomorphism of Chow groups, with inverse the transposition in the other direction. -/
@[stacks 0FG4 "the transpose is an isomorphism, on cycle classes"]
def chowTransposeEquiv (n : ℤ) :
    chowGroup C (pullback.fst sX sY ≫ sX) n ≃+ chowGroup C (pullback.fst sY sX ≫ sY) n where
  toFun := chowTranspose C sX sY n
  invFun := chowTranspose C sY sX n
  left_inv := chowTranspose_chowTranspose C sX sY n
  right_inv := chowTranspose_chowTranspose C sY sX n
  map_add' := map_add _

/-- `chowTransposeEquiv` applied to a Chow class is its transpose. -/
@[simp]
theorem chowTransposeEquiv_apply (n : ℤ) (α : chowGroup C (pullback.fst sX sY ≫ sX) n) :
    chowTransposeEquiv C sX sY n α = chowTranspose C sX sY n α :=
  rfl

/-- The inverse of `chowTransposeEquiv` is the transposition in the other direction. -/
@[simp]
theorem chowTransposeEquiv_symm_apply (n : ℤ) (α : chowGroup C (pullback.fst sY sX ≫ sY) n) :
    (chowTransposeEquiv C sX sY n).symm α = chowTranspose C sY sX n α :=
  rfl

/-- **Stacks Project, Tag 0FG4.** The `ℚ`-vector space `Corrʳ(X, Y)` of rational correspondences
of degree `r` from `X` to a target equidimensional of dimension `e`: the degree-`(e - r)` Chow
group of `X ×_S Y` with rational coefficients. -/
abbrev Correspondence (e r : ℤ) : Type u :=
  TensorProduct ℤ ℚ (chowGroup C (pullback.fst sX sY ≫ sX) (e - r))

/-- **Stacks Project, Tag 0FG4.** The transpose `c ↦ cᵗ` of a rational correspondence. For `X`
equidimensional of dimension `d` and `Y` equidimensional of dimension `e` it maps
`Corrʳ(X, Y)` to `Corr^{d - e + r}(Y, X)`. -/
@[stacks 0FG4 "transpose"]
def transpose (d e r : ℤ) :
    Correspondence C sX sY e r →ₗ[ℤ] Correspondence C sY sX d (d - e + r) :=
  TensorProduct.map LinearMap.id
    ((((chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY)
          (show e - r = d - (d - e + r) by omega)).toAddMonoidHom).comp
      (chowTranspose C sX sY (e - r))).toIntLinearMap)

/-- The transpose of a pure tensor `q ⊗ α` is `q` tensored with the transpose of `α`, moved to
degree `d - (d - e + r)`. -/
@[simp]
theorem transpose_tmul (d e r : ℤ) (q : ℚ)
    (α : chowGroup C (pullback.fst sX sY ≫ sX) (e - r)) :
    transpose C sX sY d e r (q ⊗ₜ[ℤ] α) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY)
        (show e - r = d - (d - e + r) by omega) (chowTranspose C sX sY (e - r) α) :=
  rfl

/-- **Stacks Project, Tag 0FG4.** For `X` equidimensional of dimension `d` and `Y`
equidimensional of dimension `e`, the factor switch `X ×_S Y ≅ Y ×_S X` determines an
*isomorphism*

  `Corrʳ(X, Y) ≃ Corr^{d - e + r}(Y, X)`, `c ↦ cᵗ`,

the transpose, with inverse the transpose in the other direction. -/
@[stacks 0FG4 "the transpose is an isomorphism Corr^r(X, Y) = Corr^{d - e + r}(Y, X)"]
def transposeEquiv (d e r : ℤ) :
    Correspondence C sX sY e r ≃ₗ[ℚ] Correspondence C sY sX d (d - e + r) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (((chowTransposeEquiv C sX sY (e - r)).trans
      (chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY)
        (show e - r = d - (d - e + r) by omega))).toIntLinearEquiv)

/-- `transposeEquiv` on a pure tensor `q ⊗ α` is `q` tensored with the transpose of `α`, moved to
degree `d - (d - e + r)`. -/
@[simp]
theorem transposeEquiv_tmul (d e r : ℤ) (q : ℚ)
    (α : chowGroup C (pullback.fst sX sY ≫ sX) (e - r)) :
    transposeEquiv C sX sY d e r (q ⊗ₜ[ℤ] α) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY)
        (show e - r = d - (d - e + r) by omega) (chowTranspose C sX sY (e - r) α) :=
  rfl

/-- The isomorphism of Stacks 0FG4 is the transpose `c ↦ cᵗ`. -/
@[simp]
theorem transposeEquiv_apply (d e r : ℤ) (c : Correspondence C sX sY e r) :
    transposeEquiv C sX sY d e r c = transpose C sX sY d e r c :=
  rfl

/-- The inverse of the isomorphism of Stacks 0FG4 is the transpose in the other direction, the
degrees matched up by `e - r = d - (d - e + r)`. -/
theorem transposeEquiv_symm_tmul (d e r : ℤ) (q : ℚ)
    (α : chowGroup C (pullback.fst sY sX ≫ sY) (e - r)) :
    (transposeEquiv C sX sY d e r).symm
        (q ⊗ₜ[ℤ] chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY)
          (show e - r = d - (d - e + r) by omega) α) =
      q ⊗ₜ[ℤ] chowTranspose C sY sX (e - r) α := by
  rw [LinearEquiv.symm_apply_eq, transposeEquiv_tmul, chowTranspose_chowTranspose]

end Stacks.WeilCohomology

end
