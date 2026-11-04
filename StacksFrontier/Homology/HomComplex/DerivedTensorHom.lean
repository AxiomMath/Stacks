module

public import StacksFrontier.Homology.HomComplex.DerivedInternalHom

/-!
# The derived tensor--Hom diagonal and coevaluation

Let `R` be a commutative ring and let `K`, `L`, `M` be objects of the derived category `D(R)`.
This file records the two structure maps of the derived tensor--Hom formalism that move a tensor
factor across an internal Hom: the *diagonal*
`K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` and the *coevaluation* `K ⟶ RHom(L, K ⊗ᴸ L)`.
Both are obtained from the fixed derived tensor--Hom adjunction, the coevaluation being the
transpose of the identity of `K ⊗ᴸ L` and the diagonal being built from it by composing internal
Homs. The results below express their canonicity and their functoriality in each variable, with
the variable occurring on both sides of an internal Hom contributing a dinaturality equation
rather than an ordinary naturality square.

## Main definitions

* `StacksDraft.DerivedHom.derivedTensorHomDiagonal` ([stacks 0BYN]): the canonical derived
  tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)`.

## Main results

* `StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural` ([stacks 0BYN]): the diagonal is
  covariantly natural in the tensor factor `K` and in the internal-Hom target `L`, and
  contravariantly natural in the internal-Hom source `M`.
* `StacksDraft.DerivedHom.derivedTensorHomCoevaluation_natural` ([stacks 0A6B]): the canonical
  morphism `K ⟶ RHom(L, K ⊗ᴸ L)` is the transpose of the identity of `K ⊗ᴸ L`; it is
  covariantly natural in `K` and dinatural in `L`.

## Implementation notes

The derived tensor and internal-Hom bifunctors, the additive adjunction between them, and the
canonical maps built from it are the ones fixed once and for all by the K-flat/K-injective
model construction, accessed here through `DerivedInternalHom.Model`. Consequently the maps of
this file are honest data rather than existential statements, and canonicity of the coevaluation
is expressed by saying that it corresponds to the identity under that fixed adjunction.

The diagonal is the map supplied by that adjunction, so its content here is the three
naturality equations, which are packaged as a single conjunction exactly as the naturality laws
of `DerivedInternalHom.Model.CanonicalMapLaws` state them. In the coevaluation, `L` occurs both
as the contravariant internal-Hom argument and as the covariant tensor argument, so
functoriality in `L` is a dinaturality equation; the explicit type ascriptions on the morphisms
of the product category in that clause pin down which of the two occurrences moves.

## References

* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
* [Stacks Project, Tag 0A6B](https://stacks.math.columbia.edu/tag/0A6B)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace StacksDraft.DerivedHom

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat R)]

/-- **Stacks 0BYN.** The canonical morphism
`K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` in the derived category. -/
@[stacks 0BYN]
alias derivedTensorHomDiagonal := DerivedInternalHom.Model.diagonal

/-- **Stacks 0BYN.** The derived tensor--Hom diagonal is covariantly natural in `K` and `L`
and contravariantly natural in `M`. -/
@[stacks 0BYN]
theorem derivedTensorHomDiagonal_natural :
    (∀ {K K' L M : DerivedCategory (ModuleCat R)} (f : K ⟶ K'),
      (DerivedInternalHom.Model.tensor R).map
          (f, 𝟙 ((DerivedInternalHom.Model.hom R).obj (Opposite.op M, L))) ≫
          derivedTensorHomDiagonal K' L M =
        derivedTensorHomDiagonal K L M ≫
          (DerivedInternalHom.Model.hom R).map
            (𝟙 (Opposite.op M), (DerivedInternalHom.Model.tensor R).map (f, 𝟙 L))) ∧
    (∀ {K L L' M : DerivedCategory (ModuleCat R)} (f : L ⟶ L'),
      (DerivedInternalHom.Model.tensor R).map
          (𝟙 K, (DerivedInternalHom.Model.hom R).map (𝟙 (Opposite.op M), f)) ≫
          derivedTensorHomDiagonal K L' M =
        derivedTensorHomDiagonal K L M ≫
          (DerivedInternalHom.Model.hom R).map
            (𝟙 (Opposite.op M), (DerivedInternalHom.Model.tensor R).map (𝟙 K, f))) ∧
    (∀ {K L M M' : DerivedCategory (ModuleCat R)} (f : M' ⟶ M),
      (DerivedInternalHom.Model.tensor R).map
          (𝟙 K, (DerivedInternalHom.Model.hom R).map (f.op, 𝟙 L)) ≫
          derivedTensorHomDiagonal K L M' =
        derivedTensorHomDiagonal K L M ≫
          (DerivedInternalHom.Model.hom R).map
            (f.op, 𝟙 ((DerivedInternalHom.Model.tensor R).obj (K, L)))) :=
  ⟨(DerivedInternalHom.Model.canonicalMapLaws R).diagonal_naturality_tensor,
    (DerivedInternalHom.Model.canonicalMapLaws R).diagonal_naturality_target,
    (DerivedInternalHom.Model.canonicalMapLaws R).diagonal_naturality_source⟩

/-- **Stacks 0A6B.** The canonical morphism `K ⟶ RHom(L, K ⊗ᴸ L)` is the transpose
of the identity on `K ⊗ᴸ L`; it is covariantly natural in `K` and dinatural in `L`. -/
@[stacks 0A6B]
theorem derivedTensorHomCoevaluation_natural :
    (∀ (K L : DerivedCategory (ModuleCat R)),
      DerivedInternalHom.Model.homEquiv K L ((DerivedInternalHom.Model.tensor R).obj (K, L))
          (DerivedInternalHom.Model.coevaluation K L) =
        𝟙 ((DerivedInternalHom.Model.tensor R).obj (K, L))) ∧
    (∀ {K K' L : DerivedCategory (ModuleCat R)} (f : K ⟶ K'),
      f ≫ DerivedInternalHom.Model.coevaluation K' L =
        DerivedInternalHom.Model.coevaluation K L ≫
          (DerivedInternalHom.Model.hom R).map
            (𝟙 (Opposite.op L), (DerivedInternalHom.Model.tensor R).map (f, 𝟙 L))) ∧
    (∀ {K L L' : DerivedCategory (ModuleCat R)} (g : L ⟶ L'),
      DerivedInternalHom.Model.coevaluation K L' ≫
          (DerivedInternalHom.Model.hom R).map
            ((g.op, 𝟙 ((DerivedInternalHom.Model.tensor R).obj (K, L'))) :
              (Opposite.op L', (DerivedInternalHom.Model.tensor R).obj (K, L')) ⟶
                (Opposite.op L, (DerivedInternalHom.Model.tensor R).obj (K, L'))) =
        DerivedInternalHom.Model.coevaluation K L ≫
          (DerivedInternalHom.Model.hom R).map
            ((𝟙 (Opposite.op L), (DerivedInternalHom.Model.tensor R).map (𝟙 K, g)) :
              (Opposite.op L, (DerivedInternalHom.Model.tensor R).obj (K, L)) ⟶
                (Opposite.op L, (DerivedInternalHom.Model.tensor R).obj (K, L')))) := by
  refine ⟨fun K L => (DerivedInternalHom.Model.homEquiv K L
      ((DerivedInternalHom.Model.tensor R).obj (K, L))).apply_symm_apply _,
    fun f => ?_, fun g => ?_⟩
  · refine (DerivedInternalHom.Model.homEquiv _ _ _).injective ?_
    rw [(DerivedInternalHom.Model.adjunction R).homEquiv_naturality_left]
    rw [(DerivedInternalHom.Model.adjunction R).homEquiv_naturality_right]
    simp [DerivedInternalHom.Model.coevaluation]
  · refine (DerivedInternalHom.Model.homEquiv _ _ _).injective ?_
    rw [(DerivedInternalHom.Model.adjunction R).homEquiv_dinaturality]
    rw [(DerivedInternalHom.Model.adjunction R).homEquiv_naturality_right]
    simp [DerivedInternalHom.Model.coevaluation]

end StacksDraft.DerivedHom

end
