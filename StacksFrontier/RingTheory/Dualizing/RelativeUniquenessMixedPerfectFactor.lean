module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed

/-!
# The projection formula for `Δ^!` at a tensor factor pulled back along a section

Let `R → A` be a flat ring map of finite presentation, put `B = A ⊗[R] A`, write
`p₁, p₂ : A → B` for the two coprojections and `Δ : B → A` for the multiplication map, and let
`K` be a relative dualizing complex for `R → A` in the sense of [stacks 0E2C].  This file proves
the projection formula

> `Δ^!(p₂^*X ⊗ᴸ_B p₁^*K) ≅ X`

for a **perfect** `X` in `D(A)`, unconditionally: no hypothesis is carried, no Tor amplitude is
bounded, and nothing is assumed of `K` beyond the defining condition of [stacks 0E2C].

## Main results

* `Dualizing.nonempty_derivedHom_tensor_includeRight_isPerfect_iso` — the projection formula
  above, with the tensor factor pulled back along the right coprojection.
* `Dualizing.nonempty_derivedHom_tensor_includeLeft_isPerfect_iso` — the mirror, with the tensor
  factor pulled back along the left coprojection.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_isPerfect` — the two of them
  discharge, for perfect `K` and `L`, both halves of the hypothesis carried by
  `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso`.

## What this consumes, and what it does not

Three inputs, each unconditional.  The defining condition of [stacks 0E2C], read in the
internal-Hom vocabulary of [stacks 0A63] by
`Dualizing.modelHom_diagonalObject_iso_of_derivedHom`: internal derived Hom from the diagonal
into the base change of a relative dualizing complex is the diagonal.  The descent of the
diagonal along the chosen coprojection,
`Dualizing.nonempty_restrictScalars_includeRight_tensor_diagonalObject_iso` and its mirror, which
brings `p^*X ⊗ᴸ_B A_B` down to `X` in `D(A)`.  And **part (2) of [stacks 0ATK]** — a perfect
tensor factor — at the derived base change `p^*X`, which is perfect by [stacks 066W].  These are
assembled by `Dualizing.nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section`, run with
each coprojection in turn as the chosen section of `Δ`.

Nothing here is a Tor-amplitude criterion, and that is the point: part (3) of [stacks 0ATK] asks
the tensor factor to have Tor amplitude in `[a, ∞]` over `B`, and
`Dualizing.torAmplitude_of_diagonalDerivedExtension` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTorAmplitudeDescent` shows that such a bound
on a base change along a section of `Δ` descends to the same bound over `A`, hence — with
pseudo-coherence, by `Dualizing.isPerfect_of_isRelativeDualizingComplex_of_torAmplitude` — to
perfectness.  So on the base changes of relative dualizing complexes parts (2) and (3) of
[stacks 0ATK] have the *same* reach, and the formulation below is the one whose hypothesis is
visibly a condition on the tensor factor alone.

## Where the general case stands

What [stacks 0E2D] still needs is this formula at `X = L` a second relative dualizing complex,
which is pseudo-coherent and bounded but **not** perfect; see the section "What the hypothesis
actually says" of the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed`.  The perfect case does not reach it
by a limit argument.  Writing `L` as the filtered colimit of the brutal truncations of a
bounded-above finite free representative does express it as a colimit of perfect complexes, and
`Δ^!(p₂^*(-) ⊗ᴸ_B p₁^*K)` does commute with filtered colimits of *uniformly bounded* families —
the Hom complex out of a bounded-above complex of finite free modules has finite products in
each degree exactly then, so `Δ^!` commutes with such colimits.  But the truncations of `L` are
not uniformly bounded below, and in the colimit the finite products become infinite ones: the
comparison is the inclusion of a direct sum in a product.  That is the same obstruction the
module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` records at the
chain level.
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-- The derived base change of a perfect object along the left coprojection is perfect.  This is
[stacks 066W] for `Dualizing.diagonalDerivedExtension`, which is the total left derived functor
of termwise extension of scalars along the flat coprojection by
`Dualizing.diagonalDerivedExtensionIsoTotalDerived`. -/
theorem isPerfect_diagonalDerivedExtension (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (X : DerivedCategory (ModuleCat.{u} A))
    (hX : StacksDraft.Perfect.IsPerfect X) :
    StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj X) :=
  StacksDraft.Perfect.isPerfect_of_iso
    (((diagonalDerivedExtensionIsoTotalDerived R A).app X).symm)
    (StacksDraft.Perfect.isPerfect_derivedExtensionScalars.{u, u, u} _ X hX)

/-- **The projection formula for `Δ^!` at a perfect tensor factor pulled back along the right
coprojection.**  Let `R → A` be flat of finite presentation, let `B = A ⊗[R] A`, let `K` be a
relative dualizing complex for `R → A` and let `X` be an object of `D(A)` whose derived base
change `p₂^*X` along the right coprojection is *perfect* — for instance any perfect `X`, by
[stacks 066W].  Then

`Δ^!(p₂^*X ⊗ᴸ_B p₁^*K) ≅ X`.

Nothing is carried.  The three inputs are the defining condition of [stacks 0E2C] at `K`, the
descent of the diagonal along the right coprojection, and part (2) of [stacks 0ATK] — a perfect
tensor factor.

At `X = L` a second relative dualizing complex this is the second of the two isomorphisms carried
as `hshriek` by
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso`; the
hypothesis that `X` be perfect is exactly what that theorem does not have, and the module
documentation of this file records why the perfect case does not reach the general one. -/
theorem nonempty_derivedHom_tensor_includeRight_isPerfect_iso (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K X : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K)
    (hX : StacksDraft.Perfect.IsPerfect
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj X)) :
    Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
            ((totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeRight :
                  A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj X,
              (diagonalDerivedExtension R A).obj K)) ≅ X) :=
  nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section R A
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
    (lmul'_comp_includeRight R A) _ _ X
    (modelHom_diagonalObject_iso_of_derivedHom R A _ hK.diagonalDerivedHom)
    (nonempty_restrictScalars_includeRight_tensor_diagonalObject_iso R A X)
    (Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ _ _ 0
      (Or.inr (Or.inl hX)))

/-- **The mirror: the projection formula for `Δ^!` at a perfect tensor factor pulled back along
the left coprojection.**  Let `L` be a relative dualizing complex for the flat finitely presented
`R → A` and let `X` be an object of `D(A)` whose derived base change `p₁^*X` along the left
coprojection is perfect.  Then

`Δ^!(p₁^*X ⊗ᴸ_B p₂^*L) ≅ X`.

The defining condition consumed is the one read on the **right** coprojection,
`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight`, and the descent is taken
along the left coprojection; everything else is as in
`Dualizing.nonempty_derivedHom_tensor_includeRight_isPerfect_iso`. -/
theorem nonempty_derivedHom_tensor_includeLeft_isPerfect_iso (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (L X : DerivedCategory (ModuleCat.{u} A))
    (hL : IsRelativeDualizingComplex R A L)
    (hX : StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj X)) :
    Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
            ((diagonalDerivedExtension R A).obj X,
              (totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeRight :
                  A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L)) ≅ X) :=
  nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section R A
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
    (lmul'_comp_includeLeftRingHom R A) _ _ X
    (modelHom_diagonalObject_iso_of_derivedHom R A _ hL.diagonalDerivedHom_includeRight)
    (nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso R A X)
    (Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ _ _ 0
      (Or.inr (Or.inl hX)))

/-- **The hypothesis `hshriek` of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso`, discharged
for perfect relative dualizing complexes.**  Let `R → A` be flat of finite presentation and let
`K` and `L` be relative dualizing complexes for it which are perfect as objects of `D(A)`.  Then
`K ≅ L`.

Both halves of `hshriek` are supplied by the two projection formulas of this file: the left one
`Δ^!(K₁ ⊗ᴸ_B L₂) ≅ K` by `Dualizing.nonempty_derivedHom_tensor_includeLeft_isPerfect_iso` at
`X = K`, and the right one `Δ^!(L₂ ⊗ᴸ_B K₁) ≅ L` by
`Dualizing.nonempty_derivedHom_tensor_includeRight_isPerfect_iso` at `X = L`.

This carries **more** than [stacks 0E2D] assumes, so it is not a registration of that tag;
under its hypothesis
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange` already gives the
conclusion.  What is new is that the two projection formulas are proved without naming a
Tor amplitude. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_mixed_of_isPerfect (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L)
    (hKperf : StacksDraft.Perfect.IsPerfect K)
    (hLperf : StacksDraft.Perfect.IsPerfect L) :
    Nonempty (K ≅ L) :=
  nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso R A K L hK hL
    ⟨nonempty_derivedHom_tensor_includeLeft_isPerfect_iso R A L K hL
        (isPerfect_diagonalDerivedExtension R A K hKperf),
      nonempty_derivedHom_tensor_includeRight_isPerfect_iso R A K L hK
        (StacksDraft.Perfect.isPerfect_derivedExtensionScalars.{u, u, u} _ L hLperf)⟩

end Dualizing

end
