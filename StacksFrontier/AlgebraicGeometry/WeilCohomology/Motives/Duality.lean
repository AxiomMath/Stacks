module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.MonoidalStructure
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroups
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import StacksCore.Tactic.StacksAttribute

/-!
# Duality for the motive of a smooth projective scheme

Let `X` be a smooth projective scheme over `k` which is equidimensional of dimension `d`. Then
the `d`-fold Tate twist `h(X)(d)` of the motive of `X` is a left dual of `h(X)` in the category
`M_k` of Chow motives: there are a unit `η : 1 ⟶ h(X) ⊗ h(X)(d)` and a counit
`ε : h(X)(d) ⊗ h(X) ⟶ 1`, both given by the class of the diagonal, for which the two triangle
composites are the identity.

The three groups of correspondences

  `Corr⁰(X, X) = CH^d(X × X) ⊗ ℚ = Corr^d(Spec k, X × X) = Corr^{-d}(X × X, Spec k)`,

that is `Hom(h(X), h(X))`, `Hom(1, h(X) ⊗ h(X)(d))` and `Hom(h(X)(d) ⊗ h(X), 1)`, are identified
with each other, so that one class, the diagonal, is at once the identity of `h(X)`, the unit `η`
and the counit `ε`. Given the two composition formulas for the diagonal, the duality is an
`ExactPairing` in the category of correspondences.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceStructure.motiveOf`: the motive `h(X) = (X, 1, 0)`.
* `Stacks.WeilCohomology.CorrespondenceStructure.tateMotive`: the Tate motive
  `1(n) = 1(1)^{⊗ n}`.
* `Stacks.WeilCohomology.CorrespondenceStructure.motiveTwist`: the Tate twist
  `h(X)(n) = h(X) ⊗ 1(n)`.
* `Stacks.WeilCohomology.DiagonalPairingData`: a unit and a counit whose two composites, in
  either order, are the identity.
* `Stacks.WeilCohomology.graphCorrespondenceStructure`: the tautological correspondence
  structure on a symmetric monoidal category, where every correspondence is a graph.

## Main results

* `Stacks.WeilCohomology.selfCorrespondenceEquivCoevaluation` and
  `Stacks.WeilCohomology.selfCorrespondenceEquivEvaluation`: the degree-zero self
  correspondences of `X` are the degree-`d` correspondences from the base point to `X × X` and
  the degree-`(-d)` correspondences from `X × X` to the base point.
* `Stacks.WeilCohomology.dualityCorrespondenceEquiv`: hence the group of units and the group of
  counits of the duality are canonically the same.
* `Stacks.WeilCohomology.exactPairing_motiveOf_motiveTwist`: given the two composition formulas,
  `h(X)(d)` is a left dual of `h(X)`.
* `Stacks.WeilCohomology.exactPairing_motiveTwist_motiveOf` and
  `Stacks.WeilCohomology.hasRightDual_motiveOf`: the duality is two sided, and `h(X)` is
  dualizable.
* `Stacks.WeilCohomology.motiveOf_tensorRightAdjunction`: the duality as an adjunction,
  `- ⊗ h(X) ⊣ - ⊗ h(X)(d)`.

## Implementation notes

* Following Tag 0FFP, `Y` is a *left dual* of `X` when there are `η : 1 ⟶ X ⊗ Y` and
  `ε : Y ⊗ X ⟶ 1` whose two triangle composites are the identity. That datum is Mathlib's
  `CategoryTheory.ExactPairing X Y`, which Mathlib names `HasRightDual X`; so `h(X)(d)` being a
  left dual of `h(X)` is `ExactPairing (h X) (h X (d))`.
* The objects of `Stacks.WeilCohomology.CorrespondenceStructure.Obj` are the motives `(X, 1, m)`
  with trivial projector. The twist is `M(n) = M ⊗ 1(n)` with `1(n) = 1(1)^{⊗ n}`, `1(1)` being a
  distinguished object `L`; only non-negative twists occur.
* Chow groups are graded by dimension, the dimension of a scheme being a parameter. The
  correspondence groups are taken at the dimension `2 * d` of `X × X`, where the three groups
  above are the single group `A_d(X × X) ⊗ ℚ`, which is `CH^d(X × X) ⊗ ℚ` in the codimension
  grading.
* `Stacks.WeilCohomology.DiagonalPairingData` carries the two identifications of Tag 0FG0 (2) and
  (3), defines the unit and the counit as the images of the identity of `h(X)` under them, and
  carries the two composition formulas: the composite of `[Δ] ⊗ 1 ∈ Corr^d(X, X³)` with
  `1 ⊗ [Δ] ∈ Corr^{-d}(X³, X)`, in either order, is `[Δ] = 1 ∈ Corr⁰(X, X)`. Conversely
  `Stacks.WeilCohomology.DiagonalPairingData.ofExactPairing` builds such data from an exact
  pairing, so this hypothesis is equivalent to the conclusion.

## References

* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

open AlgebraicGeometry

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.Chow

universe v u w

namespace Stacks.WeilCohomology

/-! ### The groups of correspondences in which the duality pairing lives -/

/-- Transport of rational Chow classes along an equality of degrees, as a `ℚ`-linear
isomorphism. -/
def rationalChowGroupDegreeEquiv (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {k l : ℤ} (h : k = l) :
    RationalChowGroup C sX k ≃ₗ[ℚ] RationalChowGroup C sX l :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (chowGroupDegreeEquiv C sX h).toIntLinearEquiv

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (d : ℤ)

/-- For `X` equidimensional of dimension `d`, so that `X × X` is
equidimensional of dimension `2 * d`, the canonical `ℚ`-linear isomorphism

  `Corr⁰(X, X) = CH^d(X × X) ⊗ ℚ = Corr^d(Spec k, X × X)`.

The left-hand group is `Hom(h(X), h(X))`, which contains the identity `[Δ]`; the right-hand one
is `Hom(1, h(X) ⊗ h(X)(d))`, which contains the unit `η` of the duality. The identification is
that of Tag 0FG0 (3), proper pushforward along the collapsing projection
`Spec k × (X × X) ≅ X × X`. -/
@[stacks 0FGI
  "the identification Corr^0(X,X) = Corr^d(Spec k, X x X) = CH^d(X x X) tensor Q, which puts
the identity [D] of h(X) and the unit of the duality in one group"]
def selfCorrespondenceEquivCoevaluation :
    Correspondence C sX sX d 0 ≃ₗ[ℚ]
      Correspondence C (𝟙 C.S) (pullback.fst sX sX ≫ sX) (2 * d) d :=
  (rationalChowGroupDegreeEquiv C (pullback.fst sX sX ≫ sX)
      (show d - 0 = 2 * d - d by ring)).trans
    (correspondenceFromPointEquiv C (pullback.fst sX sX ≫ sX) (2 * d) d)

/-- For `X` equidimensional of dimension `d` the canonical
`ℚ`-linear isomorphism

  `Corr⁰(X, X) = CH_d(X × X) ⊗ ℚ = Corr^{-d}(X × X, Spec k)`.

The right-hand group is `Hom(h(X)(d) ⊗ h(X), 1)`, which contains the counit `ε` of the duality.
The identification is that of Tag 0FG0 (2), proper pushforward along the collapsing projection
`(X × X) × Spec k ≅ X × X`. -/
@[stacks 0FGI
  "the identification Corr^0(X,X) = Corr^{-d}(X x X, Spec k) = CH_d(X x X) tensor Q, which puts
the identity [D] of h(X) and the counit of the duality in one group"]
def selfCorrespondenceEquivEvaluation :
    Correspondence C sX sX d 0 ≃ₗ[ℚ]
      Correspondence C (pullback.fst sX sX ≫ sX) (𝟙 C.S) 0 (-d) :=
  (rationalChowGroupDegreeEquiv C (pullback.fst sX sX ≫ sX)
      (show d - 0 = -(-d) by ring)).trans
    (correspondenceToPointEquiv C (pullback.fst sX sX ≫ sX) (-d))

/-- The group of candidate units of the duality and the group of
candidate counits are canonically the same, both being `CH^d(X × X) ⊗ ℚ = CH_d(X × X) ⊗ ℚ`:

  `Corr^d(Spec k, X × X) = Corr^{-d}(X × X, Spec k)`. -/
@[stacks 0FGI
  "the identification Corr^d(Spec k, X x X) = Corr^{-d}(X x X, Spec k) that makes one class [D]
serve as identity, as unit and as counit"]
def dualityCorrespondenceEquiv :
    Correspondence C (𝟙 C.S) (pullback.fst sX sX ≫ sX) (2 * d) d ≃ₗ[ℚ]
      Correspondence C (pullback.fst sX sX ≫ sX) (𝟙 C.S) 0 (-d) :=
  (selfCorrespondenceEquivCoevaluation C sX d).symm.trans
    (selfCorrespondenceEquivEvaluation C sX d)

/-- The unit and the counit attached to one and the same degree-zero self correspondence of `X`
— for the diagonal class, the `η` and the `ε` of the duality — correspond to each other under
the identification of their two groups. -/
theorem dualityCorrespondenceEquiv_apply (c : Correspondence C sX sX d 0) :
    dualityCorrespondenceEquiv C sX d (selfCorrespondenceEquivCoevaluation C sX d c) =
      selfCorrespondenceEquivEvaluation C sX d c := by
  simp only [dualityCorrespondenceEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-! ### Motives, Tate twists and the duality pairing -/

namespace CorrespondenceStructure

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]

/-- The motive `h(X) = (X, 1, 0)` of a smooth projective scheme `X`, as an object of the
category of correspondences: on objects the functor `h` is the identity. -/
abbrev motiveOf (S : CorrespondenceStructure.{v, u, w} D) (X : D) : S.Obj :=
  Obj.mk X

/-- The Tate motive `1(n) = 1(1)^{⊗ n}`, the `n`-fold tensor power of a given Tate motive
`L = 1(1)`; `1(0) = 1` is the unit motive. -/
def tateMotive (S : CorrespondenceStructure.{v, u, w} D) (L : S.Obj) : ℕ → S.Obj
  | 0 => 𝟙_ S.Obj
  | n + 1 => S.tateMotive L n ⊗ L

/-- The `n`-fold Tate twist `M(n) = M ⊗ 1(n)` of a motive `M`. -/
abbrev twistBy (S : CorrespondenceStructure.{v, u, w} D) (L : S.Obj) (M : S.Obj) (n : ℕ) :
    S.Obj :=
  M ⊗ S.tateMotive L n

/-- The twisted motive `h(X)(n) = (X, 1, n)`, the `n`-fold Tate twist of the motive of `X`. -/
abbrev motiveTwist (S : CorrespondenceStructure.{v, u, w} D) (L : S.Obj) (X : D) (n : ℕ) :
    S.Obj :=
  S.twistBy L (S.motiveOf X) n

/-- When the Tate motive is the unit motive every Tate twist is trivial. -/
def tateMotiveUnitIso (S : CorrespondenceStructure.{v, u, w} D) :
    ∀ n : ℕ, S.tateMotive (𝟙_ S.Obj) n ≅ 𝟙_ S.Obj
  | 0 => Iso.refl _
  | n + 1 => (ρ_ (S.tateMotive (𝟙_ S.Obj) n)).trans (S.tateMotiveUnitIso n)

end CorrespondenceStructure
/-- Duality data in the form of Tag 0FGI for two objects `A`, `B` of a monoidal category:
bijections `Hom(A, A) ≃ Hom(1, A ⊗ B)` and `Hom(A, A) ≃ Hom(B ⊗ A, 1)` (for correspondences, the
identifications of Tag 0FG0 (3) and (2),
`Stacks.WeilCohomology.selfCorrespondenceEquivCoevaluation` and
`Stacks.WeilCohomology.selfCorrespondenceEquivEvaluation`), such that the unit and the counit, the
images of the identity of `A` (the diagonal class `[Δ] = 1`), satisfy the two composition
formulas for the diagonal. -/
structure DiagonalPairingData {M : Type u} [Category.{v} M] [MonoidalCategory M] (A B : M) where
  /-- The identification of `Hom(A, A) = Corr⁰(X, X)` with `Hom(1, A ⊗ B)`, Tag 0FG0 (3). -/
  coevaluationEquiv : (A ⟶ A) ≃ (𝟙_ M ⟶ A ⊗ B)
  /-- The identification of `Hom(A, A) = Corr⁰(X, X)` with `Hom(B ⊗ A, 1)`, Tag 0FG0 (2). -/
  evaluationEquiv : (A ⟶ A) ≃ (B ⊗ A ⟶ 𝟙_ M)
  /-- Composing `[Δ] ⊗ 1 : A ⟶ (A ⊗ B) ⊗ A` with `1 ⊗ [Δ] : A ⊗ (B ⊗ A) ⟶ A` gives the diagonal
  `[Δ] = 1` of `Corr⁰(X, X)`. -/
  comp_coevaluation_evaluation :
    (λ_ A).inv ≫ coevaluationEquiv (𝟙 A) ▷ A ≫ (α_ A B A).hom ≫
      A ◁ evaluationEquiv (𝟙 A) ≫ (ρ_ A).hom = 𝟙 A
  /-- The composition in the other order is the diagonal as well. -/
  comp_evaluation_coevaluation :
    (ρ_ B).inv ≫ B ◁ coevaluationEquiv (𝟙 A) ≫ (α_ B A B).inv ≫
      evaluationEquiv (𝟙 A) ▷ B ≫ (λ_ B).hom = 𝟙 B

namespace DiagonalPairingData

variable {M : Type u} [Category.{v} M] [MonoidalCategory M] {A B : M}

/-- The unit `η = [Δ] : 1 ⟶ A ⊗ B` of the diagonal pairing: the image of the diagonal class,
the identity of `A`, under the identification of the two groups. -/
abbrev coevaluation (P : DiagonalPairingData A B) : 𝟙_ M ⟶ A ⊗ B :=
  P.coevaluationEquiv (𝟙 A)

/-- The counit `ε = [Δ] : B ⊗ A ⟶ 1` of the diagonal pairing: the image of the same class. -/
abbrev evaluation (P : DiagonalPairingData A B) : B ⊗ A ⟶ 𝟙_ M :=
  P.evaluationEquiv (𝟙 A)

/-- The diagonal pairing is an exact pairing: the two composition formulas are the two triangle
identities, written with the unit constraints moved to the other side. -/
@[instance_reducible]
def exactPairing (P : DiagonalPairingData A B) : ExactPairing A B where
  coevaluation' := P.coevaluation
  evaluation' := P.evaluation
  evaluation_coevaluation' := by
    have h := P.comp_coevaluation_evaluation
    rw [Iso.inv_comp_eq, Category.comp_id] at h
    rw [← h]
    simp
  coevaluation_evaluation' := by
    have h := P.comp_evaluation_coevaluation
    rw [Iso.inv_comp_eq, Category.comp_id] at h
    rw [← h]
    simp

/-- The adjunction bijection `Hom(A, A) ≃ Hom(1, A ⊗ B)` attached to an exact pairing. It sends
the identity of `A` to the unit of the pairing. -/
def coevaluationEquivOfExactPairing (A B : M) [ExactPairing A B] :
    (A ⟶ A) ≃ (𝟙_ M ⟶ A ⊗ B) :=
  (Iso.homCongr (λ_ A) (Iso.refl A)).symm.trans (tensorRightHomEquiv (𝟙_ M) A B A)

/-- The bijection `coevaluationEquivOfExactPairing A B` sends the identity of `A` to the unit
`η_ A B` of the exact pairing. -/
@[simp]
theorem coevaluationEquivOfExactPairing_id (A B : M) [ExactPairing A B] :
    coevaluationEquivOfExactPairing A B (𝟙 A) = η_ A B := by
  have h := tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight (Y := A) (Y' := B) (𝟙 A)
  simp only [MonoidalCategory.id_whiskerRight, Category.comp_id] at h
  have h' : ((λ_ A).homCongr (Iso.refl A)).symm (𝟙 A) = (λ_ A).hom := by
    simp [Iso.homCongr]
  simp only [coevaluationEquivOfExactPairing, Equiv.trans_apply]
  rw [h', ← h, Equiv.apply_symm_apply]

/-- The adjunction bijection `Hom(A, A) ≃ Hom(B ⊗ A, 1)` attached to an exact pairing. It sends
the identity of `A` to the counit of the pairing. -/
def evaluationEquivOfExactPairing (A B : M) [ExactPairing A B] :
    (A ⟶ A) ≃ (B ⊗ A ⟶ 𝟙_ M) :=
  ((tensorLeftHomEquiv A A B (𝟙_ M)).trans (Iso.homCongr (Iso.refl A) (ρ_ A))).symm

/-- The bijection `evaluationEquivOfExactPairing A B` sends the identity of `A` to the counit
`ε_ A B` of the exact pairing. -/
@[simp]
theorem evaluationEquivOfExactPairing_id (A B : M) [ExactPairing A B] :
    evaluationEquivOfExactPairing A B (𝟙 A) = ε_ A B := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    tensorLeftHomEquiv, Equiv.coe_fn_mk]
  rw [ExactPairing.evaluation_coevaluation]
  simp

/-- Conversely an exact pairing supplies the data above for the *same* unit and counit: its
adjunction bijections send the identity of `A` to the unit and to the counit, and its two
triangle identities are the two composition formulas. -/
def ofExactPairing (p : ExactPairing A B) : DiagonalPairingData A B :=
  letI := p
  { coevaluationEquiv := coevaluationEquivOfExactPairing A B
    evaluationEquiv := evaluationEquivOfExactPairing A B
    comp_coevaluation_evaluation := by
      simp only [coevaluationEquivOfExactPairing_id, evaluationEquivOfExactPairing_id]
      rw [ExactPairing.evaluation_coevaluation_assoc]
      simp
    comp_evaluation_coevaluation := by
      simp only [coevaluationEquivOfExactPairing_id, evaluationEquivOfExactPairing_id]
      rw [ExactPairing.coevaluation_evaluation_assoc]
      simp }

end DiagonalPairingData

/-! ### Duality for the motive of a smooth projective scheme -/

section Duality

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
  (S : CorrespondenceStructure.{v, u, w} D) (L : S.Obj) (Y : D) (e : ℕ)

/-- Given the two composition formulas for the diagonal class, `h(X)(d)` is a left dual of
`h(X)` in the sense of Tag 0FFP: the unit `1 ⟶ h(X) ⊗ h(X)(d)` and the counit
`h(X)(d) ⊗ h(X) ⟶ 1` are the diagonal class and both triangle identities hold. The hypothesis
`P` is equivalent to the conclusion
(`Stacks.WeilCohomology.DiagonalPairingData.ofExactPairing`). -/
@[instance_reducible]
def exactPairing_motiveOf_motiveTwist
    (P : DiagonalPairingData (S.motiveOf Y) (S.motiveTwist L Y e)) :
    ExactPairing (S.motiveOf Y) (S.motiveTwist L Y e) :=
  P.exactPairing

/-- Given the two composition formulas for the diagonal class, `h(X)` is also a left dual of
`h(X)(d)`, the category of correspondences being symmetric. -/
@[instance_reducible]
def exactPairing_motiveTwist_motiveOf
    (P : DiagonalPairingData (S.motiveOf Y) (S.motiveTwist L Y e)) :
    ExactPairing (S.motiveTwist L Y e) (S.motiveOf Y) :=
  letI := exactPairing_motiveOf_motiveTwist S L Y e P
  BraidedCategory.exactPairing_swap _ _

/-- Given the two composition formulas for the diagonal class, the motive of a smooth projective
scheme equidimensional of dimension `d` is dualizable, with `h(X)(d)` as its dual. In Mathlib's
naming, `h(X)(d)` being a *left* dual of `h(X)` is `HasRightDual (h X)`. -/
@[instance_reducible]
def hasRightDual_motiveOf (P : DiagonalPairingData (S.motiveOf Y) (S.motiveTwist L Y e)) :
    HasRightDual (S.motiveOf Y) where
  rightDual := S.motiveTwist L Y e
  exact := exactPairing_motiveOf_motiveTwist S L Y e P

/-- Given the two composition formulas for the diagonal class, tensoring with `h(X)` is left
adjoint to tensoring with `h(X)(d)`. -/
def motiveOf_tensorRightAdjunction
    (P : DiagonalPairingData (S.motiveOf Y) (S.motiveTwist L Y e)) :
    tensorRight (S.motiveOf Y) ⊣ tensorRight (S.motiveTwist L Y e) :=
  letI := exactPairing_motiveOf_motiveTwist S L Y e P
  tensorRightAdjunction _ _

end Duality

/-! ### The tautological correspondence structure, and a pairing in it -/

/-- The tautological correspondence structure on a symmetric monoidal category: a
correspondence from `X` to `Y` is a morphism `X ⟶ Y`, every correspondence is its own graph, and
the exterior product of correspondences is the tensor product of morphisms. -/
def graphCorrespondenceStructure (D : Type u) [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] : CorrespondenceStructure.{v, u, v} D where
  Hom X Y := X ⟶ Y
  id X := 𝟙 X
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h
  graph f := f
  graph_id _ := rfl
  graph_comp _ _ := rfl
  tensor f g := f ⊗ₘ g
  tensor_graph _ _ := rfl
  tensor_comp f₁ f₂ g₁ g₂ := MonoidalCategory.tensorHom_comp_tensorHom f₁ f₂ g₁ g₂
  associator_naturality f₁ f₂ f₃ := MonoidalCategory.associator_naturality f₁ f₂ f₃
  leftUnitor_naturality f := by simp
  rightUnitor_naturality f := by simp
  braiding_naturality f₁ f₂ := BraidedCategory.braiding_naturality f₁ f₂

/-- The diagonal pairing data for the unit motive: taking every correspondence to be a graph, the
scheme to be the base point and the Tate motive to be the unit motive, the motive `h(Spec k) = 1`
is a left dual of itself in every twist, the two composition formulas being the triangle
identities of the unit pairing. -/
def dualityPairingDataUnit (D : Type u) [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] (e : ℕ) :
    DiagonalPairingData ((graphCorrespondenceStructure D).motiveOf (𝟙_ D))
      ((graphCorrespondenceStructure D).motiveTwist
        (𝟙_ (graphCorrespondenceStructure D).Obj) (𝟙_ D) e) :=
  letI S := graphCorrespondenceStructure D
  letI : ExactPairing (S.motiveOf (𝟙_ D)) (𝟙_ S.Obj) := exactPairingUnit
  .ofExactPairing
    (exactPairingCongrRight
      ((whiskerLeftIso (𝟙_ S.Obj) (S.tateMotiveUnitIso e)).trans (ρ_ (𝟙_ S.Obj))))

end Stacks.WeilCohomology

end
