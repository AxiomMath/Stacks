module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.DiagonalLargeUniverse

/-!
# Transporting the tensor--Hom diagonal along an equivalence

`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomDiagonal` is the tensor--Hom diagonal
`K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` of an arbitrary derived tensor--Hom adjunction: the
transpose, under the adjunction, of associativity followed by evaluation. When the adjunction is
transported along an additive equivalence of derived categories by
`StacksDraft.DerivedHom.DerivedHomAdjunction.transport`, its diagonal is computed here. It is
the image under the equivalence of the diagonal of the original adjunction, conjugated by the
unit isomorphism in the internal-Hom source and in the tensor target; no counit survives,
because the counit produced by transporting the adjunction bijection is cancelled by the unit
appearing in the target identification.

This completes the identification of `Dualizing.derivedTensorHomDiagonalModel` -- the canonical
diagonal of Stacks 0BYN over `ULift R` transported along the scalar equivalence of Stacks 0E1W,
which is invertible by `Dualizing.isIso_derivedTensorHomDiagonalModel` -- with
`Dualizing.derivedTensorHomDiagonalOverRing`, the diagonal of the adjunction of Stacks 0A63 at a
module universe independent of the ring universe. Everything in that identification is
unconditional except the agreement of the canonical diagonal of Stacks 0BYN with the generic
one, which `StacksDraft.DerivedHom.DerivedInternalHom.Model.diagonal_eq_tensorHomDiagonal`
reduces to one currying identity: that the currying isomorphism of Stacks 0A65 is double
transposition through the adjunction of Stacks 0A63. That identity is supplied at an arbitrary
test object by `StacksDraft.DerivedHom.DerivedInternalHom.Model.comp_curryingIso_hom`, so the
consequences below are unconditional.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.transport_tensorHomDiagonal` -- the tensor--Hom
  diagonal of a transported derived tensor--Hom adjunction, unconditionally.
* `Dualizing.derivedTensorHomDiagonalModel_eq_overRing_of_diagonal_eq` and
  `Dualizing.derivedTensorHomDiagonalModel_eq_overRing` -- the transported canonical diagonal
  *is* `Dualizing.derivedTensorHomDiagonalOverRing`, granted the currying identity.
* `Dualizing.derivedTensorHomDiagonalOverRing_eq_transport` and
  `Dualizing.isIso_derivedTensorHomDiagonalOverRing_of_isIso_tensorHomDiagonal` -- the
  unconditional content in the vocabulary of Stacks 0E2A: that diagonal is a transport of the
  generic diagonal over `ULift R`, and is invertible whenever that one is.
* `Dualizing.isIso_derivedTensorHomDiagonalOverRing` -- hence that canonical diagonal is
  invertible as soon as the internal-Hom source or the tensor factor is perfect.

## Implementation notes

The identifications `hA`, `hB`, `hR` inside the proof of `transport_tensorHomDiagonal` restate
subterms of the goal in the vocabulary of the original adjunction and the equivalence. They are
needed because the goal carries both `(d.transport e).hom.obj (op M, L)` and
`e.functor.obj (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))`, which are definitionally
but not syntactically equal, so a rewrite whose pattern is written in one spelling does not fire
on the other. Associator naturality is for the same reason introduced as a hypothesis with an
explicitly written type instead of being rewritten with directly: elaboration spells the target
of `e.unitIso.inv.app` as `(𝟭 _).obj _`, where `tensorAssoc` has the bare object, and only a
defeq-tolerant elaboration -- a term-mode `have` -- relates the two.

The derived-morphism universe of `D(R)` is the standard one in the three consequences. The
transport lemmas this file consumes are stated with a single derived-morphism universe for both
sides of the equivalence, and the scalar equivalence of Stacks 0E1W pins the `ULift R` side to
`max u v + 1`.

## References

* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Prod Opposite

universe u v w

namespace StacksDraft.DerivedHom

namespace DerivedHomAdjunction

section Transport

variable {S : Type v} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{v} S)]
  {T : Type u} [CommRing T] [HasDerivedCategory.{w} (ModuleCat.{v} T)]
  (d : DerivedHomAdjunction S)
  (e : DerivedCategory (ModuleCat.{v} S) ≌ DerivedCategory (ModuleCat.{v} T))
  [e.functor.Additive]

/-- **The tensor--Hom diagonal of a transported derived tensor--Hom adjunction**: the image
under the equivalence of the diagonal of the original adjunction, conjugated by the unit
isomorphism in the internal-Hom source and in the tensor target. -/
theorem transport_tensorHomDiagonal (K L M : DerivedCategory (ModuleCat.{v} T)) :
    (d.transport e).tensorHomDiagonal K L M =
      e.functor.map
        (d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
            (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))) ≫
          d.tensorHomDiagonal (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M) ≫
          d.hom.map (mkHom (𝟙 (op (e.inverse.obj M)))
            (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj L))))) := by
  -- The transported evaluation factor, in the vocabulary of `d` and `e`.
  have hB : (d.transport e).tensor.map ((𝟙 K, (d.transport e).evaluation M L) :
        (K, (d.transport e).tensor.obj ((d.transport e).hom.obj (op M, L), M)) ⟶ (K, L)) =
      e.functor.map (d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
        (e.unitIso.inv.app (d.tensor.obj (e.inverse.obj (e.functor.obj
              (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))), e.inverse.obj M)) ≫
          d.tensor.map (mkHom
              (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
              (𝟙 (e.inverse.obj M))) ≫
          d.evaluation (e.inverse.obj M) (e.inverse.obj L)))) := by
    rw [show (d.transport e).tensor.map ((𝟙 K, (d.transport e).evaluation M L) :
          (K, (d.transport e).tensor.obj ((d.transport e).hom.obj (op M, L), M)) ⟶ (K, L)) =
        e.functor.map (d.tensor.map (mkHom (e.inverse.map (𝟙 K))
          (e.inverse.map ((d.transport e).evaluation M L)))) from rfl,
      e.inverse.map_id, inverse_map_transport_evaluation d e L M]
    rfl
  -- The transported associator, in the same vocabulary.
  have hA : ((d.transport e).tensorAssoc K ((d.transport e).hom.obj (op M, L)) M).hom =
      e.functor.map
        (d.tensor.map (mkHom
            (e.unitIso.inv.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj (e.functor.obj
              (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))))))
            (𝟙 (e.inverse.obj M))) ≫
          (d.tensorAssoc (e.inverse.obj K) (e.inverse.obj (e.functor.obj
            (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))) (e.inverse.obj M)).hom ≫
          d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
            (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj (e.functor.obj
              (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))), e.inverse.obj M))))) := rfl
  -- The transpose of the diagonal being transported.
  have hR : d.homEquiv
      (d.tensor.obj (e.inverse.obj K, e.inverse.obj (e.functor.obj
        (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))))
      (e.inverse.obj M)
      (e.inverse.obj (e.functor.obj (d.tensor.obj (e.inverse.obj K, e.inverse.obj L))))
      (d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
          (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))) ≫
        d.tensorHomDiagonal (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M) ≫
        d.hom.map (mkHom (𝟙 (op (e.inverse.obj M)))
          (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj L))))) =
      (d.tensor.map (mkHom (d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
              (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))))
            (𝟙 (e.inverse.obj M))) ≫
        (d.tensorAssoc (e.inverse.obj K) (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))
          (e.inverse.obj M)).hom ≫
        d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
          (d.evaluation (e.inverse.obj M) (e.inverse.obj L)))) ≫
      e.unitIso.hom.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj L)) := by
    rw [d.homEquiv_naturality_left, d.homEquiv_naturality_right]
    simp only [Functor.id_obj]
    rw [show d.homEquiv
          (d.tensor.obj (e.inverse.obj K, d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
          (e.inverse.obj M) (d.tensor.obj (e.inverse.obj K, e.inverse.obj L))
          (d.tensorHomDiagonal (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)) =
        (d.tensorAssoc (e.inverse.obj K) (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))
            (e.inverse.obj M)).hom ≫
          d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
            (d.evaluation (e.inverse.obj M) (e.inverse.obj L))) from
        (d.homEquiv _ _ _).apply_symm_apply _]
    simp only [Category.assoc]
  -- The two unit isomorphisms between the associator and the evaluation cancel.
  have hmerge : d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
        (e.unitIso.hom.app (d.tensor.obj (e.inverse.obj (e.functor.obj
          (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))), e.inverse.obj M)))) ≫
      d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
        (e.unitIso.inv.app (d.tensor.obj (e.inverse.obj (e.functor.obj
              (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))), e.inverse.obj M)) ≫
          d.tensor.map (mkHom
              (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
              (𝟙 (e.inverse.obj M))) ≫
          d.evaluation (e.inverse.obj M) (e.inverse.obj L))) =
      d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
        (d.tensor.map (mkHom
              (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
              (𝟙 (e.inverse.obj M))) ≫
          d.evaluation (e.inverse.obj M) (e.inverse.obj L))) := by
    rw [d.tensor_map_comp, Category.id_comp, ← Category.assoc,
      e.unitIso.hom_inv_id_app, Category.id_comp]
  have hsplit : d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
        (d.tensor.map (mkHom
              (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
              (𝟙 (e.inverse.obj M))) ≫
          d.evaluation (e.inverse.obj M) (e.inverse.obj L))) =
      d.tensor.map (mkHom (𝟙 (e.inverse.obj K)) (d.tensor.map (mkHom
          (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
          (𝟙 (e.inverse.obj M))))) ≫
        d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
          (d.evaluation (e.inverse.obj M) (e.inverse.obj L))) := by
    rw [d.tensor_map_comp, Category.id_comp]
  -- Associator naturality, with its type written out so that elaboration, not rewriting,
  -- reconciles the two spellings of the unit's target.
  have hnat : d.tensor.map (mkHom (d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
            (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))))
          (𝟙 (e.inverse.obj M))) ≫
        (d.tensorAssoc (e.inverse.obj K) (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))
            (e.inverse.obj M)).hom ≫
          d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
            (d.evaluation (e.inverse.obj M) (e.inverse.obj L))) =
      (d.tensorAssoc (e.inverse.obj K) (e.inverse.obj (e.functor.obj
          (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))) (e.inverse.obj M)).hom ≫
        d.tensor.map (mkHom (𝟙 (e.inverse.obj K)) (d.tensor.map (mkHom
            (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
            (𝟙 (e.inverse.obj M))))) ≫
          d.tensor.map (mkHom (𝟙 (e.inverse.obj K))
            (d.evaluation (e.inverse.obj M) (e.inverse.obj L))) :=
    d.tensorAssoc_naturality_assoc (𝟙 (e.inverse.obj K))
      (e.unitIso.inv.app (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L)))
      (𝟙 (e.inverse.obj M)) _
  -- Two images of the equivalence compose to one, and the counit cancels the final unit.
  have key : ∀ {X₀ X₁ X₂ X₃ : DerivedCategory (ModuleCat.{v} S)} (p : X₀ ⟶ X₁) (c : X₁ ⟶ X₃)
      (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₃), a ≫ b = p ≫ c →
      e.functor.map a ≫ e.functor.map b =
        e.functor.map (p ≫ c ≫ e.unitIso.hom.app X₃) ≫ e.counit.app (e.functor.obj X₃) := by
    intro X₀ X₁ X₂ X₃ p c a b hab
    rw [← e.functor.map_comp, hab, ← Category.assoc,
      e.functor.map_comp (p ≫ c) (e.unitIso.hom.app X₃), Category.assoc,
      show e.functor.map (e.unitIso.hom.app X₃) ≫ e.counit.app (e.functor.obj X₃) =
          𝟙 (e.functor.obj X₃) from e.functor_unitIso_comp X₃,
      Category.comp_id]
  apply ((d.transport e).homEquiv
    ((d.transport e).tensor.obj (K, (d.transport e).hom.obj (op M, L)))
    M ((d.transport e).tensor.obj (K, L))).injective
  refine (((d.transport e).homEquiv _ M _).apply_symm_apply _).trans
    (Eq.trans ?_ (transportHomEquiv_functor_map d e
      (d.tensor.obj (e.inverse.obj K, e.inverse.obj (e.functor.obj
        (d.hom.obj (op (e.inverse.obj M), e.inverse.obj L))))) M
      (e.functor.obj (d.tensor.obj (e.inverse.obj K, e.inverse.obj L))) _).symm)
  rw [hA, hB, hR]
  refine key _ _ _ _ ?_
  simp only [Category.assoc]
  rw [hmerge, hsplit, hnat]

end Transport

end DerivedHomAdjunction

end StacksDraft.DerivedHom

namespace Dualizing

open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- **`Dualizing.derivedTensorHomDiagonalOverRing` is a transport**, unconditionally: the
generic assoc-evaluation diagonal over `ULift R`, carried along the scalar equivalence of
Stacks 0E1W by exactly the two identifications that `Dualizing.derivedTensorHomDiagonalModel`
uses for the canonical diagonal of Stacks 0BYN. -/
theorem derivedTensorHomDiagonalOverRing_eq_transport
    (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    derivedTensorHomDiagonalOverRing.{u, v} K L M =
      (derivedScalarEquivalence.{u, v} R).functor.map
        ((derivedTensorHomDiagonalModelSource.{u, v} K L M).hom ≫
          (derivedHomAdjunctionULift.{u, v, max u v + 1}
              (R := R)).toDerivedHomAdjunction.tensorHomDiagonal
            ((derivedScalarEquivalence.{u, v} R).inverse.obj K)
            ((derivedScalarEquivalence.{u, v} R).inverse.obj L)
            ((derivedScalarEquivalence.{u, v} R).inverse.obj M) ≫
          (derivedTensorHomDiagonalModelTarget.{u, v} K L M).hom) :=
  DerivedHomAdjunction.transport_tensorHomDiagonal _ _ K L M

/-- **Invertibility of the independent-universe diagonal is invertibility of the generic
diagonal over `ULift R`**, unconditionally. Together with
`Dualizing.derivedTensorHomDiagonalModel_eq_overRing` this is what the currying identity buys:
the hypothesis here is about the *generic* diagonal, where Stacks 0ATK is about the canonical
one. -/
theorem isIso_derivedTensorHomDiagonalOverRing_of_isIso_tensorHomDiagonal
    (K L M : DerivedCategory (ModuleCat.{max u v} R))
    (h : IsIso ((derivedHomAdjunctionULift.{u, v, max u v + 1}
      (R := R)).toDerivedHomAdjunction.tensorHomDiagonal
        ((derivedScalarEquivalence.{u, v} R).inverse.obj K)
        ((derivedScalarEquivalence.{u, v} R).inverse.obj L)
        ((derivedScalarEquivalence.{u, v} R).inverse.obj M))) :
    IsIso (derivedTensorHomDiagonalOverRing.{u, v} K L M) := by
  rw [derivedTensorHomDiagonalOverRing_eq_transport.{u, v}]
  have := h
  exact Functor.map_isIso _ _

/-- **The transported canonical diagonal is the canonical diagonal over the ring itself**, as
soon as the canonical tensor--Hom diagonal of Stacks 0BYN over `ULift R` agrees with the generic
assoc-evaluation diagonal of the adjunction of Stacks 0A63. -/
theorem derivedTensorHomDiagonalModel_eq_overRing_of_diagonal_eq
    (hdiag : ∀ (K L M : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))),
      DerivedInternalHom.Model.diagonal K L M =
        (derivedHomAdjunctionULift.{u, v, max u v + 1}
          (R := R)).toDerivedHomAdjunction.tensorHomDiagonal K L M)
    (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    derivedTensorHomDiagonalModel.{u, v} K L M =
      derivedTensorHomDiagonalOverRing.{u, v} K L M :=
  (congrArg (derivedScalarEquivalence.{u, v} R).functor.map
      (congrArg (fun q => (derivedTensorHomDiagonalModelSource.{u, v} K L M).hom ≫ q ≫
          (derivedTensorHomDiagonalModelTarget.{u, v} K L M).hom)
        (hdiag _ _ _))).trans
    (DerivedHomAdjunction.transport_tensorHomDiagonal _ _ K L M).symm

/-- **The transported canonical diagonal is `Dualizing.derivedTensorHomDiagonalOverRing`.** -/
theorem derivedTensorHomDiagonalModel_eq_overRing
    (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    derivedTensorHomDiagonalModel.{u, v} K L M =
      derivedTensorHomDiagonalOverRing.{u, v} K L M :=
  derivedTensorHomDiagonalModel_eq_overRing_of_diagonal_eq
    DerivedInternalHom.Model.diagonal_eq_tensorHomDiagonal K L M

/-- **The canonical derived tensor--Hom diagonal at a module universe independent of the ring
universe is invertible** when the internal-Hom source or the tensor factor is perfect. This is
Stacks 0ATK for `Dualizing.derivedTensorHomDiagonalOverRing`. -/
theorem isIso_derivedTensorHomDiagonalOverRing
    (K L M : DerivedCategory (ModuleCat.{max u v} R))
    (h : StacksDraft.Perfect.IsPerfect M ∨ StacksDraft.Perfect.IsPerfect K) :
    IsIso (derivedTensorHomDiagonalOverRing.{u, v} K L M) := by
  rw [← derivedTensorHomDiagonalModel_eq_overRing K L M]
  exact isIso_derivedTensorHomDiagonalModel.{u, v} K L M h

end Dualizing

end
