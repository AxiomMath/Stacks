module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles

/-!
# The stage functors of Stacks Tag 0EXB as left adjoints of one restriction of scalars

Let `p` be a prime and let `X` be a scheme in characteristic `p`. Write `φ` for the `p`-th power
endomorphism of `𝒪_X`, `ι_n : 𝒪_X ⟶ colim_F 𝒪_X` for the stage-`n` coprojection, `S_n` for
extension of scalars along `ι_n` and `U_n` for restriction of scalars along `ι_n`. Because
`ι_n = ι_{n + j} ∘ φ^j`, restriction of scalars along `ι_n` is restriction along `ι_{n + j}`
followed by `j` restrictions along `φ`:

`U_{n + j} ⋙ (U_φ)^j = U_n`

as an equality of functors, not merely an isomorphism. Consequently **extending scalars `j`
times along `φ` and then once along `ι_{n + j}` is a left adjoint of `U_n`**, the same functor
that `S_n` is a left adjoint of. This is the structural fact behind
`AlgebraicGeometry.frobeniusStageFunctorIterIso`: that isomorphism compares two left adjoints of
one and the same restriction of scalars, and is therefore determined by the units of the two
adjunctions.

## Main definitions

* `AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter`: **the adjunction
  `(F^*)^j ⋙ S_{n + j} ⊣ U_n`** on all sheaves of modules, assembled from the `j` Frobenius
  adjunctions and the stage-`n + j` one.

## Main results

* `AlgebraicGeometry.pushforward_frobeniusStage_comp_iter`: **restriction of scalars along the
  stage-`n + j` coprojection followed by `j` restrictions along Frobenius is restriction along
  the stage-`n` coprojection.** This is
  `AlgebraicGeometry.pushforward_frobeniusStage_comp` iterated, and it is the functor-level form
  of `ι_n = ι_{n + j} ∘ φ^j`.

## Implementation notes

The iteration is an induction on `j` which shifts the stage: `n + (j + 1)` is read as
`(n + 1) + j`, the inductive hypothesis is applied at the stage `n + 1`, and the one remaining
step is `AlgebraicGeometry.pushforward_frobeniusStage_comp` at the stage `n`.

Extension of scalars along `φ` iterated `j` times is the `j`-fold composite of one functor,
`CategoryTheory.Functor.endoIter`, and not extension of scalars along the `j`-th power of `φ`;
the two agree only up to isomorphism, since extension of scalars is a sheafified tensor product.
The composite is the one which matches `AlgebraicGeometry.frobeniusPullbackIter`, the transition
functor of the diagram of Stacks Tag 0EXA, so it is the composite the adjunction is built on.

What is **not** here is the comparison of
`AlgebraicGeometry.frobeniusStageFunctorIterIso` with
`CategoryTheory.Adjunction.leftAdjointUniq` of this adjunction and the stage-`n` one, which is
what would turn `AlgebraicGeometry.frobeniusStageHomMap` into a statement about the units; see
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitHomReduction` for what that is wanted
for.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **Restriction of scalars along the stage-`n + j` coprojection, followed by `j` restrictions
of scalars along Frobenius, is restriction of scalars along the stage-`n` coprojection.** This
is the functor-level form of `ι_n = ι_{n + j} ∘ φ^j`, and unlike the comparison of the
extensions of scalars it is an equality of functors. -/
lemma pushforward_frobeniusStage_comp_iter (n j : ℕ) :
    _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX (n + j)) ⋙
        (_root_.SheafOfModules.pushforward.{u} (frobeniusSelfStructureMap X p hX)).endoIter j =
      _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n) := by
  induction j generalizing n with
  | zero => exact Functor.comp_id _
  | succ j ih =>
      have h : n + (j + 1) = n + 1 + j := by omega
      rw [Functor.endoIter_succ, ← Functor.assoc, h, ih (n + 1),
        pushforward_frobeniusStage_comp]

/-- **Extending scalars `j` times along Frobenius and then once along the stage-`n + j`
coprojection is a left adjoint of restriction of scalars along the stage-`n` coprojection** —
the same functor that extension of scalars along the stage-`n` coprojection is a left adjoint
of. It is the composite of the `j` Frobenius adjunctions with the stage-`n + j` one, the
right adjoint being rewritten by
`AlgebraicGeometry.pushforward_frobeniusStage_comp_iter`. -/
noncomputable def frobeniusStageExtendScalarsAdjunctionIter (n : ℕ) : ∀ j : ℕ,
    (frobeniusExtendScalars X p hX).endoIter j ⋙
        frobeniusStageExtendScalars X p hX (n + j) ⊣
      _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)
  | 0 =>
      _root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
        (frobeniusStageStructureMap X p hX n)
  | j + 1 =>
      Adjunction.ofNatIsoLeft (frobeniusStageExtendScalarsAdjunctionIter n j)
        (Functor.isoWhiskerLeft ((frobeniusExtendScalars X p hX).endoIter j)
          (frobeniusExtendScalarsStageIso X p hX (n + j))).symm

end AlgebraicGeometry

end
