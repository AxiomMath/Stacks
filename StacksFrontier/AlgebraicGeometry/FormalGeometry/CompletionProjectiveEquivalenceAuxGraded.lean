module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleRestrictScalars
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded

/-!
# Finite type is inherited by restriction of scalars along a surjection of graded algebras

`Stacks.Coherent.IsFiniteTypeOnAffine` says that a graded module over a sheaf of graded algebras
is generated, over every affine open, by finitely many homogeneous sections. This file records
that the property survives
`SheafOfModules.GradedModule.restrictScalars` along a unital homomorphism `φ : 𝓟 ⟶ 𝓑` of graded
algebra sheaves which is surjective on the sections over affine opens: the same finite set of
sections generates, because every homogeneous section of `𝓑` over an affine open that is used to
reach a given element is the image of one of `𝓟`.

This is the transfer the dévissage of part (2) of [Stacks, Tag 0897] needs. There the graded
module `M` lives over the associated graded algebra `𝓑 = ⨁ ℐᵐ/ℐᵐ⁺¹`, whose homogeneous pieces are
not free, and the induction is run instead over a graded algebra `𝓟` with free pieces mapping
onto `𝓑`; `M` enters the induction as `M.restrictScalars φ`, and it must still be of finite type
there for the induction hypothesis to apply to it.

## Main results

* `Stacks.Coherent.isFiniteTypeOnAffine_restrictScalars` — the transfer.

## Implementation notes

The homogeneous pieces of `M.restrictScalars φ` are *the same sheaves of modules* as those of
`M`, so the generating `Finset` is reused unchanged, with no transport: the two spanning
conditions differ only in which algebra the scalars are drawn from, and surjectivity identifies
the two sets of products.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Coherent

/-- **Finite type on affine opens is inherited by restriction of scalars along a surjection.**

Let `φ : 𝓟 ⟶ 𝓑` be a unital homomorphism of sheaves of graded algebras which is surjective on
the sections over every affine open, in every degree, and let `M` be a graded `𝓑`-module of
finite type on affine opens. Then `M`, read as a graded `𝓟`-module, is again of finite type on
affine opens — with the same generators. -/
public theorem isFiniteTypeOnAffine_restrictScalars {X : Scheme.{u}}
    {P B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (φ : SheafOfModules.GradedAlgebra.UnitalHom P B)
    (hφ : ∀ (U : X.affineOpens) (i : ℤ) (b : (B.piece i).val.obj (op U.1)),
      ∃ a : (P.piece i).val.obj (op U.1), (φ.app i).val.app (op U.1) a = b)
    (M : SheafOfModules.GradedModule B) (hft : IsFiniteTypeOnAffine M) :
    IsFiniteTypeOnAffine (M.restrictScalars φ) := by
  intro U
  obtain ⟨G, hG⟩ := hft U
  refine ⟨G, fun n => ?_⟩
  show AddSubgroup.closure
      { t : (M.piece n).val.obj (op U.1) |
        ∃ s : Σ d : ℤ, (M.piece d).val.obj (op U.1), s ∈ G ∧
          ∃ (m : ℤ) (a : (P.piece m).val.obj (op U.1)) (h : s.1 + m = n),
            t = h ▸ M.smul s.1 m (op U.1) s.2 ((φ.app m).val.app (op U.1) a) } = ⊤
  refine eq_top_iff.2 (le_trans (hG n).ge (AddSubgroup.closure_mono ?_))
  rintro t ⟨s, hsG, m, b, h, rfl⟩
  obtain ⟨a, ha⟩ := hφ U m b
  subst ha
  exact ⟨s, hsG, m, a, h, rfl⟩

end Stacks.Coherent

end
