module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorCompare
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation

/-!
# The library's two spellings of internal derived Hom at one universe agree

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation` composes three of the four
ingredients of Step 1 of the duality route to [stacks 0E2D] and proves the fourth, and records
that the two fragments do not join because they are stated in **two different spellings of
internal derived Hom** on one and the same derived category:

* `StacksDraft.DerivedHom.DerivedInternalHom.Model.hom`, the model bifunctor, whose module
  universe is the ring's own;
* `(StacksDraft.DerivedHom.derivedHomAdjunctionOverRing _).hom`, the universe-polymorphic one,
  which is the model bifunctor over `ULift R` conjugated by
  `StacksDraft.DerivedHom.derivedScalarEquivalence`.

No comparison of the two at a general first argument existed.  This file supplies one.

## The route

The two bifunctors are the internal Homs of two tensor--Hom adjunctions of [stacks 0A63] on one
category, so adjoint uniqueness applies as soon as their *tensors* are compared naturally.  That
is `Dualizing.homIsoOfTensorIsoLeft`, which needs naturality in the first variable alone, and the
natural comparison of the tensors is
`Dualizing.derivedHomAdjunctionTensorNatIsoCompare` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorCompare`, which rests in
turn on the uniqueness of the derived tensor product of [stacks 068I] as a bifunctor.

## Main definitions

* `Dualizing.modelHomIsoDerivedHomAdjunctionOverRing` — **the comparison**:
  `RHom_R(L, M)` in the two spellings, for arbitrary `L` and `M`.
* `Dualizing.modelHomNatIsoDerivedHomAdjunctionOverRing` — the comparison as an isomorphism of
  bifunctors on `D(R)ᵒᵖ × D(R)`.

## Main results

* `Dualizing.nonempty_relativeDualizingDiagonalHom_modelHom_iso` — the two halves of Step 1
  brought into one spelling: `T(RHom_A(M, N)) ≅ p₁_* RHom_B(Δ_*M, p₁^*N)` for `M`
  pseudo-coherent and `N` bounded below, with the internal Hom of the model bifunctor
  throughout.

## What Step 1 needed beyond this file, and where it is

Only the second gap recorded in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation`, which is a mathematical and
not a bookkeeping one: the *enriched* form of `Δ_* ⊣ Δ^!`,

`p₁_* RHom_B(Δ_*M, Y) ≅ RHom_A(M, Δ^!Y)`,

whose Yoneda reduction needs the projection formula
`Δ_*(Z ⊗ᴸ_A M) ≅ Δ_*Z ⊗ᴸ_B p₁^*M` naturally in `Z`, while
`Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` supplies it pointwise.  That
naturality is `Dualizing.diagonalProjectionNatIso` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormulaNatural` and the enriched adjunction
is `Dualizing.enrichedDiagonalHomIso`, so **Step 1 is a theorem**:
`Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction` composes it with
`Dualizing.nonempty_relativeDualizingDiagonalHom_modelHom_iso` below.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

/-- **The library's two spellings of internal derived Hom at one universe agree.**  For arbitrary
objects `L` and `M` of `D(R)`,

`RHom_R(L, M)` computed with `StacksDraft.DerivedHom.DerivedInternalHom.Model.hom`
is `RHom_R(L, M)` computed with
`(StacksDraft.DerivedHom.derivedHomAdjunctionOverRing _).hom`.

Both are the internal Hom of a tensor--Hom adjunction of [stacks 0A63] on `D(R)`, so this is
adjoint uniqueness — `Dualizing.homIsoOfTensorIsoLeft` — applied to the natural comparison of
the two tensors, `Dualizing.derivedHomAdjunctionTensorNatIsoCompare`.

This is the comparison that `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation`
records as absent at a general first argument; the two comparisons that existed,
`Dualizing.modelHomIsoRestrictScalarsDerivedHom` and `Dualizing.restrictScalarsDerivedHomIso`,
are both at the first argument `A_B`. -/
def modelHomIsoDerivedHomAdjunctionOverRing (R : Type u) [CommRing R]
    (L M : DerivedCategory (ModuleCat.{u} R)) :
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom R).obj (Opposite.op L, M) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} R).hom.obj
        (Opposite.op L, M) :=
  let τ := derivedHomAdjunctionTensorNatIsoCompare R
  homIsoOfTensorIsoLeft
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).toDerivedHomAdjunction
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} R) L M
    (fun K =>
      { hom := τ.inv.app (K, L)
        inv := τ.hom.app (K, L)
        hom_inv_id := by simp [τ]
        inv_hom_id := by simp [τ] })
    (fun _K _K' f => τ.inv.naturality (X := (_K', L)) (Y := (_K, L)) (f, 𝟙 L))

/-- **The comparison of `Dualizing.modelHomIsoDerivedHomAdjunctionOverRing` as an isomorphism of
bifunctors** on `D(R)ᵒᵖ × D(R)`. Each component is adjoint uniqueness,
`Dualizing.homIsoOfTensorIsoLeft`, and naturality in both variables is
`Dualizing.homNatIsoOfTensorNatIso`, applied to the natural comparison of the two tensors,
`Dualizing.derivedHomAdjunctionTensorNatIsoCompare`. -/
def modelHomNatIsoDerivedHomAdjunctionOverRing (R : Type u) [CommRing R] :
    StacksDraft.DerivedHom.DerivedInternalHom.Model.hom R ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} R).hom :=
  homNatIsoOfTensorNatIso
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).toDerivedHomAdjunction
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} R)
    (derivedHomAdjunctionTensorNatIsoCompare R).symm

/-- **The two halves of Step 1 of the duality route, joined.**  Let `R → A` be flat, put
`B = A ⊗[R] A`, and let `T` be the functor `X ↦ Δ^!(p₁^*X)` of the defining condition of
[stacks 0E2C].  For `M` pseudo-coherent and `N` bounded below,

`T(RHom_A(M, N)) ≅ p₁_* RHom_B(Δ_*M, p₁^*N)`.

`Dualizing.nonempty_relativeDualizingDiagonalHom_iso` is flat base change inside `T`, stated with
the internal Hom of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`;
`Dualizing.nonempty_derivedHom_modelHom_iso_restrictScalars_modelHom` composes the currying
isomorphism, the projection formula at the diagonal and `Δ_* ⊣ Δ^!`, stated with the internal Hom
of `StacksDraft.DerivedHom.DerivedInternalHom.Model.hom`.  Those were the two fragments that did
not join; `Dualizing.modelHomIsoDerivedHomAdjunctionOverRing` is what joins them.

What Step 1 asks for is `T(RHom_A(M, N)) ≅ RHom_A(M, T(N))`, and the distance from here to there
is the enriched form of `Δ_* ⊣ Δ^!` described in this module's documentation. -/
theorem nonempty_relativeDualizingDiagonalHom_modelHom_iso (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A]
    (M N : DerivedCategory (ModuleCat.{u} A))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) (b : ℤ) (hN : N.IsGE b) :
    Nonempty
      ((derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((diagonalDerivedExtension R A).obj
              ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj
                (Opposite.op M, N))) ≅
        (ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
            (Opposite.op ((ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R :
                A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj M),
              (diagonalDerivedExtension R A).obj N))) := by
  obtain ⟨e₁⟩ := nonempty_relativeDualizingDiagonalHom_iso R A M N hM b hN
  obtain ⟨e₂⟩ := nonempty_derivedHom_modelHom_iso_restrictScalars_modelHom R A M
    ((diagonalDerivedExtension R A).obj N)
  have eJoin := (derivedHom.{u, u, u}
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
      (modelHomIsoDerivedHomAdjunctionOverRing (A ⊗[R] A)
        ((diagonalDerivedExtension R A).obj M)
        ((diagonalDerivedExtension R A).obj N)).symm
  exact ⟨e₁ ≪≫ eJoin ≪≫ e₂⟩

end

end Dualizing

end
