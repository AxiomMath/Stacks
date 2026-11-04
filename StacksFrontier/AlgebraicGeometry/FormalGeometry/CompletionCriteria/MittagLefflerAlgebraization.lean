module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CanonicalExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerCriterion

/-!
# The in-particular clause of the Mittag-Leffler criterion

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U` whose module of compatible global sections `M = limₙ H⁰(U, F_n)` satisfies the three
hypotheses of [Stacks, Tag 0EHH]: the sections have Mittag-Leffler, the limit topology on `M` is
its `I`-adic topology, and every projection `M → H⁰(U, F_n)` has finite image. Then `(F_n)`
extends canonically to `X`, which is
`Stacks.Algebraization.canonicallyExtends_of_finite_limit_images`; this file adds the final
assertion of that lemma, that over an `I`-adically complete `A` the system is the completion of a
coherent `𝒪_U`-module.

## Main results

* `Stacks.Algebraization.essImage_completionFunctor_of_finite_limit_images` — the in-particular
  clause of [Stacks, Tag 0EHH].

## Implementation notes

The source deduces the clause in two steps, and both are available: part (2) of
[Stacks, Tag 0EIR] turns canonical extension into extendability to `X`
(`Stacks.Algebraization.extendsToX_kerComapSystem_of_canonicallyExtends`), and over a complete
ring the chain of [Stacks, Tag 0EIL] turns extendability into membership of the essential image of
the completion functor of `U` — condition (6) implies condition (5) implies condition (4) implies
condition (2).

The 0EIL conditions are stated for a system along `S.Yι.ker.comap S.U.ι`, the pullback of the
kernel ideal sheaf of `Y ⟶ X`, whereas the Mittag-Leffler criterion is stated along
`Stacks.Algebraization.idealOnOpen`. The two ideal sheaves are equal by
`Stacks.Algebraization.idealOnOpen_eq_ker_comap`, and `essImage_completionFunctor_congr` moves the
conclusion across that equality with the underlying diagram kept a variable, so that the two
presentations of the system are compared through what they share instead of asking the kernel to
identify the ideal sheaves definitionally.

## References

* [The Stacks Project, Lemma 52.11.5 (0EHH)](https://stacks.math.columbia.edu/tag/0EHH)
* [The Stacks Project, Lemma 52.11.6 (0EIR)](https://stacks.math.columbia.edu/tag/0EIR)
* [The Stacks Project, Lemma 52.10.5 (0EIL)](https://stacks.math.columbia.edu/tag/0EIL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- Membership of the essential image of the completion functor depends on the ideal sheaf and on
the underlying diagram of the system only, so it transports along an equality of ideal sheaves. -/
public theorem essImage_completionFunctor_congr {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I J : X.IdealSheafData} (e : I = J) {D : ℕᵒᵖ ⥤ X.Modules}
    (hI : Stacks.Coherent.IsCoherentAdicSystem I D)
    (hJ : Stacks.Coherent.IsCoherentAdicSystem J D)
    (h : (completionFunctor X J).essImage ⟨D, hJ⟩) :
    (completionFunctor X I).essImage ⟨D, hI⟩ := by
  subst e
  exact h

/-- **The in-particular clause of Stacks Project, Tag 0EHH.** In an algebraization situation with
`A` moreover `I`-adically complete, a coherent `I`-adic system `(ℱₙ)` on the open complement `U`
whose global sections have Mittag-Leffler, whose limit topology on `M = limₙ H⁰(U, ℱₙ)` is the
`I`-adic topology, and whose projections `M → H⁰(U, ℱₙ)` have finite image, is the completion of a
coherent `𝒪_U`-module.

The system extends canonically to `X` by
`Stacks.Algebraization.canonicallyExtends_of_finite_limit_images`, part (2) of Stacks 0EIR turns
that into extendability to `X`, and adic completeness then runs the chain of Stacks 0EIL: an
extendable system is the restriction of a completion on `X`, hence the completion of a module
restricted from `X`, hence a completion on `U`. -/
@[stacks 0EHH "the in-particular clause, that over an I-adically complete A the system is the \
completion of a coherent 𝒪_U-module, i.e. lies in the essential image of the completion functor \
of U, which is condition (2) of 0EIL; deduced from the canonical extension of the main clause by \
part (2) of 0EIR and the chain of 0EIL"]
public theorem essImage_completionFunctor_of_finite_limit_images
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hML : IsMittagLefflerCategorical (globalSectionsSystem S F))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : limitGlobalSections S F =>
        (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (limitGlobalSections S F))
    (hfinite : ∀ n : ℕ, Module.Finite S.A
      (LinearMap.range (limit.π (globalSectionsSystem S F) (op n)).hom)) :
    (completionFunctor S.U.toScheme (idealOnOpen S)).essImage F :=
  essImage_completionFunctor_congr (idealOnOpen_eq_ker_comap S) F.property
    (isCoherentAdicSystem_kerComap S F)
    ((isCompletion_iff_ofRestriction S (kerComapSystem S F)).mpr
      ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S (kerComapSystem S F)).mpr
        (isRestrictionOfCompletion_of_extendsToX S (kerComapSystem S F)
          (extendsToX_kerComapSystem_of_canonicallyExtends S F
            (canonicallyExtends_of_finite_limit_images S F hML htop hfinite)))))

end Stacks.Algebraization

end
