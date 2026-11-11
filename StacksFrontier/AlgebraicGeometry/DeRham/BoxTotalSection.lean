module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The box-product double complex of Künneth formula, III

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, and write `f = p ∘ a = q ∘ b`.  [Stacks, Section 0G4A] opens by setting

`𝓕 ⊠ 𝓖 = p^*𝓕 ⊗_{𝒪_W} q^*𝓖`

for an `𝒪_X`-module `𝓕` and an `𝒪_Y`-module `𝓖` — the **nonderived** tensor product — and then,
for complexes `𝓕^•` on `X` and `𝓖^•` on `Y` of quasi-coherent modules whose differentials are
differential operators of finite order on `X/S` resp. `Y/S`, assembles the double complex

`(i, j) ↦ 𝓕^i ⊠ 𝓖^j`,  `d_1^{i, j} = d^i_𝓕 ⊠ 1`,  `d_2^{i, j} = 1 ⊠ d^j_𝓖`

of [Stacks, Tag 0G45] and [Stacks, Tag 0A5J], asserting that its maps are differential operators
of finite order on `X ×_S Y / S`; `Tot(𝓕^• ⊠ 𝓖^•)` then denotes the total complex of that double
complex, whose terms are again quasi-coherent `𝒪_W`-modules and whose differentials are again
differential operators of finite order on `X ×_S Y / S`.

This file states exactly that construction-level content of the section.  Everything *numbered*
in [Stacks, Section 0G4A] is carried elsewhere in this repository and nothing of it is restated
here:

* the relative cup product (\ref{0G4B}) is
  `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMapUnbounded`, for arbitrary complexes, tagged
  `0G4B` at `StacksFrontier/AlgebraicGeometry/DeRham/RelativeKunnethUnbounded.lean:446`, carrying no
  parameter; for strictly bounded below complexes it is also
  `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMap` in
  `StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalKunnethMap.lean`;
* the global cup product (\ref{0FLR}) is `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMap`,
  tagged `0FLR` at `StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalKunnethMap.lean:186`, carrying
  only the global cup product of its step (3);
* steps (4) and (5) of both constructions are
  `Stacks.Cohomology.BoxKunneth.boxTotalDerivedComparison` at
  `StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalComparison.lean:337`, over the step-(5) datum
  `Stacks.Cohomology.BoxKunneth.BoxTotalComparison`, which
  `Stacks.Cohomology.BoxKunneth.boxTotalComparison` in
  `StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalComparisonExists.lean` constructs, so that
  neither cup product carries it;
* [Stacks, Tag 0FLT], the only lemma of the section, is
  `Stacks.Cohomology.BoxKunneth.isIso_globalBoxKunnethMap`, tagged `0FLT` at
  `StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalKunnethIsomorphism.lean:207`;
* the box product itself, as a bifunctor of the categories of finite-order differential
  operators, is `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductFunctor`,
  tagged `0G46` at
  `StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/BoxProductFunctor.lean:246`, and
  `AlgebraicGeometry.externalTensorProduct`, tagged `0G46` at
  `StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/ExternalTensorProduct.lean:43`.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.boxDoubleComplex`: **the double complex `𝓕^i ⊠ 𝓖^j` displayed in
  [Stacks, Section 0G4A]**, for two `ℤ`-indexed complexes of finite-order differential operators.

## Main results

* `Stacks.Cohomology.BoxKunneth.boxDoubleComplex_X_X`: its term in degree `(i, j)` is
  `𝓕^i ⊠ 𝓖^j`.
* `Stacks.Cohomology.BoxKunneth.boxDoubleComplex_d_f` and
  `Stacks.Cohomology.BoxKunneth.boxDoubleComplex_X_d`: **its two differentials are the
  `d_1^{i, j} = d^i_𝓕 ⊠ 1` and `d_2^{i, j} = 1 ⊠ d^j_𝓖` written out in the section**, with no
  sign; the signs of [Stacks, Tag 012Z] enter only in the total complex, where
  `Stacks.Cohomology.BoxKunneth.boxTotal_d` records them.
* `Stacks.Cohomology.BoxKunneth.boxDoubleComplex_comm`: **the squares of the displayed diagram
  commute**, `(d_𝓕 ⊠ 1) ∘ (1 ⊠ d_𝓖) = (1 ⊠ d_𝓖) ∘ (d_𝓕 ⊠ 1)`.
* `Stacks.Cohomology.BoxKunneth.boxTotal_eq_total`: **`Tot(𝓕^• ⊠ 𝓖^•)` is the total complex of
  that double complex.**
* `Stacks.Cohomology.BoxKunneth.isQuasicoherent_boxTotal_X` and
  `Stacks.Cohomology.BoxKunneth.exists_isGlobalDiffOpOfOrder_boxTotal_d`: **the terms of
  `Tot(𝓕^• ⊠ 𝓖^•)` are quasi-coherent `𝒪_W`-modules and its differentials are differential
  operators of finite order on `X ×_S Y / S`**, the closing assertion of the paragraph that
  introduces the notation.
* `Stacks.Cohomology.BoxKunneth.boxProductObj_module`: **`𝓕 ⊠ 𝓖` is the nonderived tensor
  product `p^*𝓕 ⊗_{𝒪_W} q^*𝓖`**, the definition the section opens with, spelled out.

## Implementation notes

*Boundedness is forced, as it is for `boxTotal`.*  `Stacks.Cohomology.BoxKunneth.boxTotal` exists
only under strict boundedness below of both factors, because in total degree `n` the antidiagonal
of `n` in `ℤ × ℤ` is infinite and the category of finite-order differential operators has no
infinite coproducts; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalComparison.lean`.  The *double* complex needs no
such hypothesis — only its total complex does — so the statements about `boxDoubleComplex` below
are unrestricted and only those mentioning `boxTotal` carry the bounds.

*The finite order of the differentials is read off the category, not reproved.*  A morphism of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory` is by construction a global operator
together with a witness that it has some finite order, and an object is by construction a
quasi-coherent module.  So the section's two closing assertions about `Tot(𝓕^• ⊠ 𝓖^•)` are the
projections of that data; what makes them true is that the total complex was formed *in* that
category, which is where the work of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.hasMapBifunctor_up_ℤ` and of the
box product on morphisms sits.  They are stated here because the section states them, and
because an unfolded `∃ k, DiffOp.IsGlobalDiffOpOfOrder …` is what a reader wanting the claim
about `X ×_S Y / S` has to be given.

*What is not here.*  No cup product and no isomorphism; those are the numbered items of the
section, carried elsewhere as listed above.  The step-(5) comparison
`Stacks.Cohomology.BoxKunneth.BoxTotalComparison` is constructed in
`StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalComparisonExists.lean`, out of the naturality of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison` in the two
differential operators; no identification of two tensorators is involved.

## References

* [Stacks Project, Section 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0A5J](https://stacks.math.columbia.edu/tag/0A5J)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

universe u

namespace Stacks.Cohomology.BoxKunneth

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-! ### The box product is the nonderived tensor product of the two pullbacks -/

/-- **`𝓕 ⊠ 𝓖 = p^*𝓕 ⊗_{𝒪_{X ×_S Y}} q^*𝓖`**, the definition [Stacks, Section 0G4A] opens with:
the tensor product, on `X ×_S Y`, of the two pullbacks along the projections.  The tensor product
is the **nonderived** one, `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`; the
section says explicitly that, contrary to a later section, the nonderived product is meant. -/
@[stacks 0G4A "the display `F ⊠ G = p^*F ⊗_{O_{X ×_S Y}} q^*G` that opens the section, including \
that the tensor product is the nonderived one; the bifunctoriality of `⊠` is Tag 0G46, \
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductFunctor`"]
theorem boxProductObj_module (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    (boxProductObj F G).module =
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((pullback a b).toRingedSpace)).presheaf, (((pullback a b).toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pullback (pullback.fst a b)).obj F.module))).obj
        (((Scheme.Modules.pullback (pullback.snd a b)).obj G.module))) :=
  rfl

variable (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)

/-! ### The double complex `𝓕^i ⊠ 𝓖^j` -/

/-- **The double complex `𝓕^i ⊠ 𝓖^j` of [Stacks, Section 0G4A]**: the bicomplex obtained by
applying the box product of [Stacks, Tag 0G46] to two `ℤ`-indexed complexes of quasi-coherent
modules with finite-order differential operators as differentials, by the construction of
[Stacks, Tag 0A5J].  Its horizontal differential is `d_1 = d_𝓕 ⊠ 1` and its vertical one is
`d_2 = 1 ⊠ d_𝓖`; both are morphisms of the category of finite-order differential operators on
`X ×_S Y / S`, which is the section's assertion that the maps of the diagram are differential
operators of finite order there. -/
@[stacks 0G4A "the double complex displayed in the section: the bicomplex `(i, j) ↦ F^i ⊠ G^j` \
of finite-order differential operators on `X ×_S Y / S`.  No boundedness is needed for the \
double complex itself; its total complex, `Stacks.Cohomology.BoxKunneth.boxTotal`, needs both \
factors strictly bounded below"]
abbrev boxDoubleComplex :
    HomologicalComplex₂ (FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((boxProductCurried a b).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L

/-- **The term of the double complex in degree `(i, j)` is `𝓕^i ⊠ 𝓖^j`.** -/
@[stacks 0G4A "the entries of the displayed double complex"]
theorem boxDoubleComplex_X_X (i j : ℤ) :
    ((boxDoubleComplex a b K L).X i).X j = boxProductObj (K.X i) (L.X j) :=
  rfl

/-- **The horizontal differential of the double complex is `d_1^{i, j} = d^i_𝓕 ⊠ 1`**, the first
of the two formulas written out in [Stacks, Section 0G4A].  There is no sign: the signs of
[Stacks, Tag 012Z] enter only in the total complex, where
`Stacks.Cohomology.BoxKunneth.boxTotal_d` records them. -/
@[stacks 0G4A "the display `d_1^{i, j} = d^i_F ⊠ 1`, the horizontal differential of the \
double complex"]
theorem boxDoubleComplex_d_f (i i' j : ℤ) :
    ((boxDoubleComplex a b K L).d i i').f j = boxHom (K.d i i') (𝟙 (L.X j)) :=
  rfl

/-- **The vertical differential of the double complex is `d_2^{i, j} = 1 ⊠ d^j_𝓖`**, the second
of the two formulas written out in [Stacks, Section 0G4A], again with no sign. -/
@[stacks 0G4A "the display `d_2^{i, j} = 1 ⊠ d^j_G`, the vertical differential of the \
double complex"]
theorem boxDoubleComplex_X_d (i j j' : ℤ) :
    ((boxDoubleComplex a b K L).X i).d j j' = boxHom (𝟙 (K.X i)) (L.d j j') :=
  rfl

/-- **The squares of the diagram displayed in [Stacks, Section 0G4A] commute**: boxing with the
identity in one variable is natural in the other, so `(1 ⊠ d_𝓖) ∘ (d_𝓕 ⊠ 1)` and
`(d_𝓕 ⊠ 1) ∘ (1 ⊠ d_𝓖)` agree as operators `𝓕^i ⊠ 𝓖^j ⟶ 𝓕^{i'} ⊠ 𝓖^{j'}`. -/
@[stacks 0G4A "commutativity of the squares of the displayed diagram, i.e. that `(i, j) ↦ \
F^i ⊠ G^j` with those two differentials really is a double complex"]
theorem boxDoubleComplex_comm (i i' j j' : ℤ) :
    boxHom (K.d i i') (𝟙 (L.X j)) ≫ boxHom (𝟙 (K.X i')) (L.d j j') =
      boxHom (𝟙 (K.X i)) (L.d j j') ≫ boxHom (K.d i i') (𝟙 (L.X j')) :=
  (boxDoubleComplex a b K L).d_comm i i' j j'

/-! ### `Tot(𝓕^• ⊠ 𝓖^•)` -/

variable (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]

/-- **`Tot(𝓕^• ⊠ 𝓖^•)` is the total complex of the double complex `𝓕^i ⊠ 𝓖^j`**, which is what
the notation means in [Stacks, Section 0G4A].  `Stacks.Cohomology.BoxKunneth.boxTotal` is formed
as `HomologicalComplex.mapBifunctor`, the total complex of the bicomplex obtained by applying the
box product; this identifies the two. -/
@[stacks 0G4A "the sentence fixing the notation `Tot(F^• ⊠ G^•)` as the total complex of the \
displayed double complex; the sign convention of that total complex is Tag 012Z, recorded by \
`Stacks.Cohomology.BoxKunneth.boxTotal_d`"]
theorem boxTotal_eq_total
    [HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)] :
    boxTotal a b K L n₁ n₂ = (boxDoubleComplex a b K L).total (ComplexShape.up ℤ) :=
  rfl

/-- **The terms of `Tot(𝓕^• ⊠ 𝓖^•)` are quasi-coherent `𝒪_{X ×_S Y}`-modules**, the first of the
two closing assertions of the paragraph of [Stacks, Section 0G4A] that fixes the notation.  In
degree `n` the term is a finite biproduct of the `𝓕^i ⊠ 𝓖^j` with `i + j = n`, and the external
tensor product of two quasi-coherent modules is quasi-coherent
(`AlgebraicGeometry.isQuasicoherent_externalTensorProduct`). -/
@[stacks 0G4A "the assertion that `Tot(F^• ⊠ G^•)` has quasi-coherent terms"]
theorem isQuasicoherent_boxTotal_X (n : ℤ) :
    ((boxTotal a b K L n₁ n₂).X n).module.IsQuasicoherent :=
  ((boxTotal a b K L n₁ n₂).X n).isQuasicoherent

/-- **The differentials of `Tot(𝓕^• ⊠ 𝓖^•)` are differential operators of finite order on
`X ×_S Y / S`**, the second of the two closing assertions of the paragraph of
[Stacks, Section 0G4A] that fixes the notation: for each pair of degrees there is a `k` for which
the differential is a global differential operator of order `≤ k` relative to the structure map
of `X ×_S Y / S`. -/
@[stacks 0G4A "the assertion that the differentials of `Tot(F^• ⊠ G^•)` are differential \
operators of finite order on `X ×_S Y / S`"]
theorem exists_isGlobalDiffOpOfOrder_boxTotal_d (n m : ℤ) :
    ∃ k, DiffOp.IsGlobalDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k
      ((boxTotal a b K L n₁ n₂).d n m).1 :=
  ((boxTotal a b K L n₁ n₂).d n m).2

end Stacks.Cohomology.BoxKunneth

end
