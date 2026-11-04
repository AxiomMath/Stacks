module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.SymmetricToLaurentEpi
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic

/-!
# The tensor algebra of an invertible module against its Laurent algebra

Let `L` be an invertible module on a scheme `T`. Two graded algebras of `L` occur in this
repository, and Tag 01O4's functor `F1` is written with one of them while Section 01NS's functor
`F_d` is written with the other:

* the **tensor algebra** `T(L) = ⨁_{n ≥ 0} L^{⊗ n}`, a
  `SheafOfModules.TensorExteriorSymmetricAlgebras` bundle, whose degree-`n` piece is the
  `ℕ`-indexed `SheafOfModules.tensorPower`. This is the target of the map `ψ` of a
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair`;
* the **Laurent algebra** `⨁_{n ∈ ℤ} L^{⊗ n}` of
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent`, whose degree-`n` piece is the
  `ℤ`-indexed integral tensor power of Tag 01CU. This is the target of the map `ψ` of a
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple`.

This file compares them: there is a unique unital homomorphism of sheaves of graded algebras
`T(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` extending the degree-one generator, it is an isomorphism in every
nonnegative degree, and it is zero in every negative degree, where `T(L)` vanishes: the Laurent
algebra agrees with the tensor algebra in nonnegative degrees, and the two presentations differ
exactly by the negative tensor powers.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentSituation`: the line-bundle situation of
  `L` over its own scheme.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentGenerator`: the degree-one generator
  `L ⟶ L^{⊗ 1}` of the Laurent algebra.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorToLaurent`: **the comparison
  `T(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`**, for an arbitrary tensor-algebra bundle of `L`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPieceIsoLaurentPiece`: **the degreewise
  isomorphism `Tⁿ(L) ≅ L^{⊗ n}`** it gives in each nonnegative degree.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isSymmetricAlgebra_tensor_of_isInvertible`: the
  tensor algebra of an invertible module is a symmetric algebra of it.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorToLaurent_unique`: the comparison is the only
  unital homomorphism extending the degree-one generator.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_tensorToLaurent_app`: **the comparison is an
  isomorphism in every nonnegative degree.**
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorToLaurent_app_eq_zero`: the comparison is
  zero in every negative degree, the tensor algebra being a zero object there.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurent_eq_situation_laurentAlgebra`: the Laurent
  algebra of Section 01NS and the Laurent algebra of a line-bundle situation are the same sheaf
  of graded algebras, with no transport.

## Implementation notes

The route to the comparison runs through symmetric algebras.
`Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_of_nonneg` says the comparison
`Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` out of the *chosen* symmetric algebra of a line bundle is an
isomorphism in every nonnegative degree. For an invertible module the degree-one sections of the
tensor algebra commute (`Stacks.SheafOfModules.pairwiseCommutes_tensorGenerator_of_isInvertible`),
so the tensor algebra of an arbitrary bundle of `L` is itself a symmetric algebra of `L`, and the
comparison homomorphism between two symmetric algebras of one module is an isomorphism in every
degree. The composite `Sym(L) ⟶ T(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` extends the degree-one generator, so
it *is* `symmetricToLaurent` by that homomorphism's uniqueness, and the left factor being
invertible transfers the conclusion to the right one.

A `Stacks.LineBundle.Situation` carries a structure morphism to a base, and nothing in the
Laurent algebra or in its comparison with the symmetric algebra uses it; `laurentSituation`
therefore takes the identity of `T`, and no statement below mentions a base.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {T : Scheme.{u}} (L : T.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]

/-! ### The Laurent algebra, through a line-bundle situation -/

/-- The line-bundle situation of an invertible module on a scheme, with the scheme as its own
base and the identity as its structure morphism. -/
def laurentSituation : Stacks.LineBundle.Situation.{u} where
  X := T
  S := T
  f := 𝟙 T
  L := L
  invertible := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    T.presheaf T.ringCatSheaf.2 L).mp hL

/-- **The Laurent algebra of Section 01NS is the Laurent algebra of the line-bundle situation**,
with no transport: both are
`Stacks.SheafOfModules.TensorPower.laurentAlgebra` of the same presheaf of rings, the same sheaf
condition and the same module. -/
theorem laurent_eq_situation_laurentAlgebra :
    laurent L = (laurentSituation L).laurentAlgebra :=
  rfl

/-- **The degree-one generator `L ⟶ L^{⊗ 1}` of the Laurent algebra**, the inverse of the
identification of the first integral tensor power with `L`. -/
def laurentGenerator : L ⟶ (laurent L).piece 1 :=
  (laurentSituation L).laurentGen

/-- The degree-one generator is the generator of the Laurent algebra of the line-bundle
situation. -/
@[simp]
theorem laurentGenerator_eq : laurentGenerator L = (laurentSituation L).laurentGen :=
  rfl

/-- The degree-one generator of the Laurent algebra is an isomorphism. -/
instance isIso_laurentGenerator : IsIso (laurentGenerator L) :=
  (laurentSituation L).isIso_laurentGen

/-! ### The tensor algebra of an invertible module is a symmetric algebra -/

variable (B : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥T) L)

/-- **The tensor algebra of an invertible module is a symmetric algebra of it**, its degree-one
local sections commuting because the symmetry constraint of an invertible module with itself is
the identity. -/
theorem isSymmetricAlgebra_tensor_of_isInvertible :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra B.tensor B.tensorGenerator :=
  B.isSymmetricAlgebra_tensor
    (@Stacks.SheafOfModules.pairwiseCommutes_tensorGenerator_of_isInvertible _ _ _ _ T.sheaf _ _
      L hL B)

/-! ### The comparison -/

/-- **The comparison `T(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` of the tensor algebra of an invertible module
with its Laurent algebra**: the unique unital homomorphism of sheaves of graded algebras
extending the degree-one generator `L ⟶ L^{⊗ 1}`. -/
def tensorToLaurent : SheafOfModules.GradedAlgebra.UnitalHom B.tensor (laurent L) :=
  B.tensor_isTensorAlgebra.descAny (laurent L) (laurentGenerator L)

/-- The comparison extends the degree-one generator of the tensor algebra. -/
theorem tensorGenerator_comp_tensorToLaurent :
    B.tensorGenerator ≫ (tensorToLaurent L B).app 1 = laurentGenerator L :=
  B.tensor_isTensorAlgebra.descAny_extends _ _

/-- The comparison is the only unital homomorphism of sheaves of graded algebras from the tensor
algebra to the Laurent algebra extending the degree-one generator. -/
theorem tensorToLaurent_unique
    {g : SheafOfModules.GradedAlgebra.UnitalHom B.tensor (laurent L)}
    (hg : B.tensorGenerator ≫ g.app 1 = laurentGenerator L) : g = tensorToLaurent L B :=
  B.tensor_isTensorAlgebra.descAny_unique _ _ hg

/-- The comparison of the *chosen* symmetric algebra of `L` with the tensor algebra of the
bundle: two symmetric algebras of one module are canonically isomorphic as sheaves of graded
algebras. -/
def symmetricToTensor :
    SheafOfModules.GradedAlgebra.UnitalHom (laurentSituation L).symmetricAlgebra B.tensor :=
  (laurentSituation L).isSymmetricAlgebra_symmetricAlgebra.isUniversal.desc
    B.tensor B.tensorGenerator (isSymmetricAlgebra_tensor_of_isInvertible L B).1

/-- Every component of the comparison of the chosen symmetric algebra with the tensor algebra of
the bundle is an isomorphism. -/
instance isIso_symmetricToTensor_app (n : ℤ) : IsIso ((symmetricToTensor L B).app n) := by
  have h : (symmetricToTensor L B).app n =
      ((laurentSituation L).isSymmetricAlgebra_symmetricAlgebra.isUniversal.pieceIso
        (isSymmetricAlgebra_tensor_of_isInvertible L B) n).hom := rfl
  rw [h]
  infer_instance

/-- **The comparison of the chosen symmetric algebra of `L` with its Laurent algebra factors
through the tensor algebra of the bundle.** Both composites are unital homomorphisms extending
the degree-one generator of `Sym(L)`, and such an extension is unique. -/
theorem symmetricToTensor_comp_tensorToLaurent :
    (symmetricToTensor L B).comp (tensorToLaurent L B) =
      (laurentSituation L).symmetricToLaurent := by
  refine (laurentSituation L).symmetricToLaurent_unique ?_
  show (laurentSituation L).symmetricAlgebraGen ≫
    (symmetricToTensor L B).app 1 ≫ (tensorToLaurent L B).app 1 = _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact Eq.trans (congrArg (· ≫ (tensorToLaurent L B).app 1)
    ((laurentSituation L).isSymmetricAlgebra_symmetricAlgebra.isUniversal.desc_extends
      B.tensor B.tensorGenerator (isSymmetricAlgebra_tensor_of_isInvertible L B).1))
    (tensorGenerator_comp_tensorToLaurent L B)

/-- **The comparison of the tensor algebra of an invertible module with its Laurent algebra is
an isomorphism in every nonnegative degree.**

The composite of the comparison with the canonical isomorphism from the chosen symmetric algebra
is the comparison `Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`, which is an isomorphism in every
nonnegative degree; the left factor is an isomorphism in every degree. -/
theorem isIso_tensorToLaurent_app (n : ℤ) (hn : 0 ≤ n) :
    IsIso ((tensorToLaurent L B).app n) := by
  have hc : (symmetricToTensor L B).app n ≫ (tensorToLaurent L B).app n =
      (laurentSituation L).symmetricToLaurent.app n :=
    congrArg (fun g : SheafOfModules.GradedAlgebra.UnitalHom
      (laurentSituation L).symmetricAlgebra (laurentSituation L).laurentAlgebra => g.app n)
      (symmetricToTensor_comp_tensorToLaurent L B)
  have : IsIso ((symmetricToTensor L B).app n ≫ (tensorToLaurent L B).app n) := by
    rw [hc]
    exact (laurentSituation L).isIso_symmetricToLaurent_app_of_nonneg n hn
  exact IsIso.of_isIso_comp_left ((symmetricToTensor L B).app n) ((tensorToLaurent L B).app n)

/-- **`Tⁿ(L) ≅ L^{⊗ n}`:** in every nonnegative degree the comparison identifies the homogeneous
piece of the tensor algebra of `L` with the integral tensor power of Tag 01CU. -/
def tensorPieceIsoLaurentPiece (n : ℕ) : B.tensor.piece (n : ℤ) ≅ (laurent L).piece (n : ℤ) :=
  haveI := isIso_tensorToLaurent_app L B (n : ℤ) (Int.natCast_nonneg n)
  asIso ((tensorToLaurent L B).app (n : ℤ))

/-- The degreewise isomorphism is the component of the comparison in that degree. -/
@[simp]
theorem tensorPieceIsoLaurentPiece_hom (n : ℕ) :
    (tensorPieceIsoLaurentPiece L B n).hom = (tensorToLaurent L B).app (n : ℤ) :=
  rfl

/-- **The comparison is zero in every negative degree**, where the tensor algebra vanishes while
the Laurent algebra does not: the two presentations differ exactly by the negative tensor
powers.

The piece is a zero object because the bundle records the vanishing of negative degrees as the
vanishing of every local section, which makes any two morphisms into the piece equal and so its
identity zero. `Stacks.AlgebraicGeometry.ProjRepresentsF1.isZero_tensorPiece_of_neg` is that
fact at the `TensorAlgebras` spelling. -/
theorem tensorToLaurent_app_eq_zero (n : ℤ) (hn : n < 0) : (tensorToLaurent L B).app n = 0 :=
  ((Limits.IsZero.iff_id_eq_zero _).2
    (B.hom_ext_tensorPiece_of_neg hn (𝟙 _) 0)).eq_of_src _ _

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
