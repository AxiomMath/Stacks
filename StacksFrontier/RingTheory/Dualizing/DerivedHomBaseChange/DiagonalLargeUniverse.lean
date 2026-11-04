module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.ModelCriterion
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.Perfect.SystemDuality
import all StacksFrontier.Homology.Perfect.SystemDuality

/-!
# The derived tensor--Hom diagonal in an independent module universe

The derived tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` of Stacks 0BYN is proved
invertible by Stacks 0ATK only where the module universe equals the ring universe, because the
construction `StacksDraft.DerivedHom.DerivedInternalHom.Model.diagonal` it speaks about is
defined only there. Consumers that compare functors on `D(R)` for modules in an independently
chosen universe -- Stacks 0E2A and Stacks 0BZE among them -- need the diagonal at module
universe `max u v`, where the only available morphism of that type was
`Dualizing.derivedTensorHomDiagonalOverRing`, with no invertibility statement anywhere.

This file supplies such a morphism together with its invertibility, by transporting the
canonical diagonal over `ULift R` -- where ring and module universe agree, so Stacks 0ATK
applies -- along the scalar equivalence of Stacks 0E1W. The transported morphism
`Dualizing.derivedTensorHomDiagonalModel` has *exactly* the type of
`Dualizing.derivedTensorHomDiagonalOverRing`: the tensor and internal-Hom bifunctors of
`derivedHomAdjunctionOverRing` are by construction the canonical ones over `ULift R`
conjugated by that equivalence, so only the two unit isomorphisms of the equivalence intervene.

The file also records the generic form of the diagonal: for an arbitrary derived tensor--Hom
adjunction, `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomDiagonal` is the transpose of
associativity followed by evaluation, and `Dualizing.derivedTensorHomDiagonalOverRing` is that
construction at the adjunction of Stacks 0A63 -- definitionally, by
`Dualizing.derivedTensorHomDiagonalOverRing_eq_tensorHomDiagonal`. Whether the canonical
diagonal of Stacks 0BYN agrees with this generic one is reduced here to a single identity about
currying -- that the canonical currying isomorphism of Stacks 0A65 is double transposition
through the adjunction -- which is supplied unconditionally by
`StacksDraft.DerivedHom.DerivedInternalHom.Model.comp_curryingIso_hom`, so that
`StacksDraft.DerivedHom.DerivedInternalHom.Model.diagonal_eq_tensorHomDiagonal` is
unconditional too.

## Main definitions

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomDiagonal` -- the tensor--Hom diagonal of
  an arbitrary derived tensor--Hom adjunction, as the transpose of associativity followed by
  evaluation.
* `Dualizing.derivedTensorHomDiagonalModel` -- a tensor--Hom diagonal for
  `derivedHomAdjunctionOverRing` at a module universe independent of the ring universe,
  transported from the canonical diagonal of Stacks 0BYN over `ULift R`.

## Main results

* `Dualizing.isIso_derivedTensorHomDiagonalModel` -- **that diagonal is invertible** as soon as
  the internal-Hom source or the tensor factor is perfect. This is the invertibility statement at
  module universe `max u v`.
* `StacksDraft.DerivedHom.DerivedInternalHom.Model.composition_transpose` and
  `StacksDraft.DerivedHom.DerivedInternalHom.Model.diagonal_eq_tensorHomDiagonal` -- the
  canonical composition of Stacks 0A8J has associativity followed by two evaluations as its
  transpose, and the canonical diagonal of Stacks 0BYN is the generic one, both
  unconditionally.
* `StacksDraft.DerivedHom.DerivedInternalHom.Model.coevaluation_evaluation` -- coevaluation
  followed by evaluation is the identity.

## Implementation notes

The currying identity used here is stated in terms of the adjunction alone, with no reference to
the private construction of the currying isomorphism, so that the lemmas depending on it are
public. The *abstract* currying isomorphism built from a derived tensor--Hom adjunction by
double transposition satisfies it by construction; that the canonical currying isomorphism of
Stacks 0A65, which is pinned on K-flat/K-injective representatives by the Hom-complex currying
map of Stacks 0A5Y, coincides with it is genuine content and not a repackaging -- the
characterizing law of Stacks 0A65 pins the canonical isomorphism only after applying
`Hom(R[0], -)`, i.e. on degree-zero cohomology, which does not determine a morphism of the
derived category. It is proved at an arbitrary test object by
`StacksDraft.DerivedHom.DerivedInternalHom.Model.comp_curryingIso_hom`, which computes both
sides on K-flat/K-injective representatives and then transports along isomorphisms in each of
its four variables.

Perfectness is transported across the scalar equivalence by
`StacksDraft.Perfect.isPerfect_inverse_scalarEquivalence`, reached through `import all`; it is
used only inside proofs, never in a statement.

## References

* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace StacksDraft.DerivedHom

namespace DerivedHomAdjunction

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- The tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` of an arbitrary derived
tensor--Hom adjunction: the transpose of associativity followed by evaluation in the second
tensor factor. -/
def tensorHomDiagonal (d : DerivedHomAdjunction R)
    (K L M : DerivedCategory (ModuleCat.{v} R)) :
    d.tensor.obj (K, d.hom.obj (Opposite.op M, L)) ⟶
      d.hom.obj (Opposite.op M, d.tensor.obj (K, L)) :=
  (d.homEquiv _ M (d.tensor.obj (K, L))).symm
    ((d.tensorAssoc K (d.hom.obj (Opposite.op M, L)) M).hom ≫
      d.tensor.map (𝟙 K, d.evaluation M L))

section Transport

variable {S : Type v} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{v} S)]
  {T : Type u} [CommRing T] [HasDerivedCategory.{w} (ModuleCat.{v} T)]
  (d : DerivedHomAdjunction S)
  (e : DerivedCategory (ModuleCat.{v} S) ≌ DerivedCategory (ModuleCat.{v} T))
  [e.functor.Additive]

/-- The transported adjunction bijection, evaluated on a morphism coming from the source
category: it is the original bijection conjugated by the unit and the counit. -/
theorem transportHomEquiv_functor_map (W : DerivedCategory (ModuleCat.{v} S))
    (L M : DerivedCategory (ModuleCat.{v} T))
    (ψ : W ⟶ d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M)) :
    (d.transport e).homEquiv (e.functor.obj W) L M (e.functor.map ψ) =
      e.functor.map (d.tensor.map
          (CategoryTheory.Prod.mkHom (e.unitIso.inv.app W) (𝟙 (e.inverse.obj L))) ≫
        d.homEquiv W (e.inverse.obj L) (e.inverse.obj M) ψ) ≫ e.counit.app M := by
  have hinner : (e.symm.toAdjunction.homEquiv (e.functor.obj W)
      (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))).symm (e.functor.map ψ) =
      e.unitIso.inv.app W ≫ ψ := by
    rw [Adjunction.homEquiv_counit]
    simp
  show (DerivedHomAdjunction.transportHomEquiv d e (e.functor.obj W) L M) (e.functor.map ψ) = _
  simp only [DerivedHomAdjunction.transportHomEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_symm_apply, hinner, d.homEquiv_naturality_left,
    Adjunction.homEquiv_counit]
  rfl

/-- Evaluation for the transported adjunction is the original evaluation, conjugated. -/
theorem transport_evaluation (L M : DerivedCategory (ModuleCat.{v} T)) :
    (d.transport e).evaluation M L =
      e.functor.map (d.tensor.map
          (CategoryTheory.Prod.mkHom
            (e.unitIso.inv.app (d.hom.obj (Opposite.op (e.inverse.obj M), e.inverse.obj L)))
            (𝟙 (e.inverse.obj M))) ≫
        d.evaluation (e.inverse.obj M) (e.inverse.obj L)) ≫ e.counit.app L := by
  have h := transportHomEquiv_functor_map d e
    (d.hom.obj (Opposite.op (e.inverse.obj M), e.inverse.obj L)) M L
    (𝟙 (d.hom.obj (Opposite.op (e.inverse.obj M), e.inverse.obj L)))
  rw [e.functor.map_id] at h
  exact h

/-- Evaluation for the transported adjunction, read back in the source category: the counit has
been absorbed, leaving only one unit. -/
theorem inverse_map_transport_evaluation (L M : DerivedCategory (ModuleCat.{v} T)) :
    e.inverse.map ((d.transport e).evaluation M L) =
      e.unitIso.inv.app (d.tensor.obj (e.inverse.obj (e.functor.obj
          (d.hom.obj (Opposite.op (e.inverse.obj M), e.inverse.obj L))), e.inverse.obj M)) ≫
        d.tensor.map
          (CategoryTheory.Prod.mkHom
            (e.unitIso.inv.app (d.hom.obj (Opposite.op (e.inverse.obj M), e.inverse.obj L)))
            (𝟙 (e.inverse.obj M))) ≫
        d.evaluation (e.inverse.obj M) (e.inverse.obj L) := by
  refine ((congrArg e.inverse.map (transport_evaluation d e L M)).trans
    (e.inverse.map_comp _ _)).trans ?_
  rw [show e.inverse.map (e.counit.app L) = e.unitIso.inv.app (e.inverse.obj L) from
      (Iso.hom_comp_eq_id (e.unitIso.app (e.inverse.obj L))).mp
        (Equivalence.unit_inverse_comp e L)]
  exact e.unitIso.inv.naturality _

end Transport

end DerivedHomAdjunction

namespace DerivedInternalHom.Model

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Coevaluation followed by evaluation is the identity of the derived tensor product. -/
theorem coevaluation_evaluation (K L : DerivedCategory (ModuleCat.{u} R)) :
    (derivedHomAdjunction (R := R)).tensor.map (coevaluation K L, 𝟙 L) ≫
        (derivedHomAdjunction (R := R)).evaluation L
          ((derivedHomAdjunction (R := R)).tensor.obj (K, L)) =
      𝟙 ((derivedHomAdjunction (R := R)).tensor.obj (K, L)) := by
  have h := (derivedHomAdjunction (R := R)).homEquiv_naturality_left
    (K := (derivedHomAdjunction (R := R)).hom.obj (Opposite.op L,
      (derivedHomAdjunction (R := R)).tensor.obj (K, L)))
    (K' := K) (L := L) (M := (derivedHomAdjunction (R := R)).tensor.obj (K, L))
    (coevaluation K L) (𝟙 _)
  rw [Category.comp_id] at h
  rw [DerivedHomAdjunction.evaluation, ← h]
  exact (homEquiv K L _).apply_symm_apply _

/-- **The transpose of the canonical composition of Stacks 0A8J**: associativity followed by
the two evaluations. The currying isomorphism of Stacks 0A65 is double transposition through the
adjunction of Stacks 0A63 by
`StacksDraft.DerivedHom.DerivedInternalHom.Model.comp_curryingIso_hom`. -/
theorem composition_transpose
    (L M N : DerivedCategory (ModuleCat.{u} R)) :
    (derivedHomAdjunction (R := R)).homEquiv
        ((derivedHomAdjunction (R := R)).tensor.obj
          ((derivedHomAdjunction (R := R)).hom.obj (Opposite.op L, N),
            (derivedHomAdjunction (R := R)).hom.obj (Opposite.op M, L))) M N
        (composition M L N) =
      ((derivedHomAdjunction (R := R)).tensorAssoc
          ((derivedHomAdjunction (R := R)).hom.obj (Opposite.op L, N))
          ((derivedHomAdjunction (R := R)).hom.obj (Opposite.op M, L)) M).hom ≫
        (derivedHomAdjunction (R := R)).tensor.map
            (𝟙 ((derivedHomAdjunction (R := R)).hom.obj (Opposite.op L, N)),
              (derivedHomAdjunction (R := R)).evaluation M L) ≫
          (derivedHomAdjunction (R := R)).evaluation L N := by
  set d := derivedHomAdjunction (R := R) with hd
  set A := d.hom.obj (Opposite.op L, N) with hA
  set H := d.hom.obj (Opposite.op M, L) with hH
  set ψ : A ⟶ d.hom.obj (Opposite.op H, d.hom.obj (Opposite.op M, N)) :=
    (hom R).map ((evaluation M L).op, 𝟙 N) ≫ (curryingIso H M N).inv with hψ
  have hcomp : composition M L N = d.homEquiv A H (d.hom.obj (Opposite.op M, N)) ψ := rfl
  have h1 : ψ ≫ (curryingIso H M N).hom = (hom R).map ((evaluation M L).op, 𝟙 N) := by
    rw [hψ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [comp_curryingIso_hom] at h1
  have h2 := congrArg (d.homEquiv A (d.tensor.obj (H, M)) N) h1
  rw [AddEquiv.apply_symm_apply] at h2
  have h3 : d.homEquiv A (d.tensor.obj (H, M)) N ((hom R).map ((evaluation M L).op, 𝟙 N)) =
      d.tensor.map (𝟙 A, evaluation M L) ≫ d.evaluation L N := by
    have h := d.homEquiv_dinaturality (K := A) (L := L) (L' := d.tensor.obj (H, M)) (M := N)
      (evaluation M L) (𝟙 A)
    rw [Category.id_comp] at h
    rw [h]
    rfl
  rw [h3] at h2
  rw [hcomp]
  exact (Iso.inv_comp_eq _).mp h2

/-- **The canonical tensor--Hom diagonal of Stacks 0BYN is the generic one**: the transpose of
associativity followed by evaluation. -/
theorem diagonal_eq_tensorHomDiagonal
    (K L M : DerivedCategory (ModuleCat.{u} R)) :
    diagonal K L M =
      (derivedHomAdjunction (R := R)).toDerivedHomAdjunction.tensorHomDiagonal K L M := by
  apply (homEquiv ((tensor R).obj (K, (hom R).obj (Opposite.op M, L))) M
    ((tensor R).obj (K, L))).injective
  rw [show (derivedHomAdjunction (R := R)).toDerivedHomAdjunction.tensorHomDiagonal K L M =
      (homEquiv _ M ((tensor R).obj (K, L))).symm
        (((derivedHomAdjunction (R := R)).tensorAssoc K
            ((hom R).obj (Opposite.op M, L)) M).hom ≫
          (tensor R).map (𝟙 K, evaluation M L)) from rfl,
    AddEquiv.apply_symm_apply]
  rw [show diagonal K L M =
      (tensor R).map (coevaluation K L, 𝟙 ((hom R).obj (Opposite.op M, L))) ≫
        composition M L ((tensor R).obj (K, L)) from rfl]
  rw [(derivedHomAdjunction (R := R)).homEquiv_naturality_left,
    composition_transpose L M ((tensor R).obj (K, L))]
  rw [← Category.assoc, (derivedHomAdjunction (R := R)).tensorAssoc_naturality]
  rw [(derivedHomAdjunction (R := R)).tensor_map_id]
  simp only [Category.assoc]
  rw [(derivedHomAdjunction (R := R)).tensor_map_comp_assoc, Category.comp_id,
    Category.id_comp]
  have hsplit : (derivedHomAdjunction (R := R)).tensor.map
      (show (K, (derivedHomAdjunction (R := R)).tensor.obj
          ((hom R).obj (Opposite.op M, L), M)) ⟶
        ((hom R).obj (Opposite.op L, (tensor R).obj (K, L)), L) from
        (coevaluation K L, (derivedHomAdjunction (R := R)).evaluation M L)) =
      (derivedHomAdjunction (R := R)).tensor.map
          (𝟙 K, (derivedHomAdjunction (R := R)).evaluation M L) ≫
        (derivedHomAdjunction (R := R)).tensor.map
          (show (K, L) ⟶ ((hom R).obj (Opposite.op L, (tensor R).obj (K, L)), L) from
            (coevaluation K L, 𝟙 L)) := by
    rw [(derivedHomAdjunction (R := R)).tensor_map_comp, Category.id_comp, Category.comp_id]
  rw [hsplit, Category.assoc, coevaluation_evaluation, Category.comp_id]
  rfl

end DerivedInternalHom.Model

end StacksDraft.DerivedHom

namespace Dualizing

open StacksDraft.DerivedHom
open scoped StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The source identification for `Dualizing.derivedTensorHomDiagonalModel`: the internal-Hom
object of `derivedHomAdjunctionOverRing` is the canonical internal-Hom object over `ULift R`
pushed forward, so restricting it back introduces one unit isomorphism. -/
def derivedTensorHomDiagonalModelSource (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensor.obj
      ((derivedScalarEquivalence.{u, v, w} R).inverse.obj K,
        (derivedScalarEquivalence.{u, v, w} R).inverse.obj
          ((derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj (Opposite.op M, L))) ≅
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensor.obj
      ((derivedScalarEquivalence.{u, v, w} R).inverse.obj K,
        (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).hom.obj
          (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).inverse.obj M),
            (derivedScalarEquivalence.{u, v, w} R).inverse.obj L)) :=
  (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensor.mapIso
    ((Iso.refl _).prod ((derivedScalarEquivalence.{u, v, w} R).unitIso.app _).symm)

/-- The target identification for `Dualizing.derivedTensorHomDiagonalModel`. -/
def derivedTensorHomDiagonalModelTarget (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).hom.obj
      (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).inverse.obj M),
        (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensor.obj
          ((derivedScalarEquivalence.{u, v, w} R).inverse.obj K,
            (derivedScalarEquivalence.{u, v, w} R).inverse.obj L)) ≅
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).hom.obj
      (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).inverse.obj M),
        (derivedScalarEquivalence.{u, v, w} R).inverse.obj
          ((derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj (K, L))) :=
  (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).hom.mapIso
    ((Iso.refl _).prod ((derivedScalarEquivalence.{u, v, w} R).unitIso.app _))

/-- **The derived tensor--Hom diagonal at a module universe independent of the ring universe.**
The canonical diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` of Stacks 0BYN over `ULift R`,
transported along the scalar equivalence of Stacks 0E1W. Its type is exactly that of
`Dualizing.derivedTensorHomDiagonalOverRing`, since the tensor and internal-Hom bifunctors of
`derivedHomAdjunctionOverRing` are the canonical ones over `ULift R` conjugated by that
equivalence. -/
def derivedTensorHomDiagonalModel (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj
      (K, (derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj (Opposite.op M, L)) ⟶
    (derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj
      (Opposite.op M, (derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj (K, L)) :=
  (derivedScalarEquivalence.{u, v, w} R).functor.map
    ((derivedTensorHomDiagonalModelSource.{u, v, w} K L M).hom ≫
      DerivedInternalHom.Model.diagonal
        ((derivedScalarEquivalence.{u, v, w} R).inverse.obj K)
        ((derivedScalarEquivalence.{u, v, w} R).inverse.obj L)
        ((derivedScalarEquivalence.{u, v, w} R).inverse.obj M) ≫
      (derivedTensorHomDiagonalModelTarget.{u, v, w} K L M).hom)

/-- **The derived tensor--Hom diagonal at module universe `max u v` is invertible** when the
internal-Hom source or the tensor factor is perfect. This is Stacks 0ATK transported along the
scalar equivalence of Stacks 0E1W; perfectness travels with it. -/
theorem isIso_derivedTensorHomDiagonalModel
    (K L M : DerivedCategory (ModuleCat.{max u v} R))
    (h : StacksDraft.Perfect.IsPerfect M ∨ StacksDraft.Perfect.IsPerfect K) :
    IsIso (derivedTensorHomDiagonalModel.{u, v, w} K L M) := by
  have hd : IsIso (DerivedInternalHom.Model.diagonal
      ((derivedScalarEquivalence.{u, v, w} R).inverse.obj K)
      ((derivedScalarEquivalence.{u, v, w} R).inverse.obj L)
      ((derivedScalarEquivalence.{u, v, w} R).inverse.obj M)) := by
    refine Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ _ _ 0 ?_
    rcases h with hM | hK
    · exact Or.inl (StacksDraft.Perfect.isPerfect_inverse_scalarEquivalence R M hM)
    · exact Or.inr (Or.inl (StacksDraft.Perfect.isPerfect_inverse_scalarEquivalence R K hK))
  rw [derivedTensorHomDiagonalModel]
  have := hd
  exact Functor.map_isIso _ _

/-- The morphism of `Dualizing.derivedTensorHomDiagonalOverRing` is the generic tensor--Hom
diagonal of the adjunction of Stacks 0A63. -/
theorem derivedTensorHomDiagonalOverRing_eq_tensorHomDiagonal
    (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    derivedTensorHomDiagonalOverRing.{u, v} K L M =
      (derivedHomAdjunctionOverRing.{u, v, w} R).tensorHomDiagonal K L M := rfl

end Dualizing

end
