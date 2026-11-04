module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Functorial homotopies from a set of acyclic complexes

Let `C` be a Grothendieck abelian category and let `(K i)` be a family of acyclic cochain
complexes in `C`.  Tag 079M produces a functor `F` on cochain complexes and a natural
termwise monomorphic quasi-isomorphism `j : 𝟭 ⟶ F` such that for every complex `M`, every
index `i` and every morphism `f : K i ⟶ M`, the composite `f ≫ j M` is null-homotopic.

The functorial K-injective resolution of Tag 079P already has these properties: it is a
termwise monomorphic quasi-isomorphism by construction, and a morphism from an acyclic
complex into a K-injective complex is null-homotopic.  The source instead gives a direct
pushout construction, which it uses in the proof of Tag 079P; the proof of Tag 079P
formalized in `StacksDraft.Ch19.Sec12.FunctorialKInjectiveResolution` does not go through
Tag 079M (it kills the maps out of the chosen small acyclic complexes by its own
transfinite construction), so deducing Tag 079M from Tag 079P here is not circular.

## Main results

* `Stacks.Injectives.exists_functorial_termwise_mono_quasiIso_homotopy_zero`: Tag 079M.

## References

* [Stacks Project, Tag 079M](https://stacks.math.columbia.edu/tag/079M)
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- **Stacks Project, Tag 079M.** For a set of acyclic cochain complexes, there is a
functorial termwise monomorphic quasi-isomorphism such that postcomposing any map from one
of the given complexes makes that map null-homotopic. -/
@[stacks 079M]
theorem exists_functorial_termwise_mono_quasiIso_homotopy_zero
    {I : Type w} (K : I → CochainComplex C ℤ) (hK : ∀ i, (K i).Acyclic) :
    ∃ (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
      (j : Functor.id (CochainComplex C ℤ) ⟶ F),
      (∀ (M : CochainComplex C ℤ) (n : ℤ), Mono ((j.app M).f n)) ∧
      (∀ M : CochainComplex C ℤ, QuasiIso (j.app M)) ∧
      ∀ (M : CochainComplex C ℤ) (i : I) (f : K i ⟶ M),
        homotopic C (ComplexShape.up ℤ) (f ≫ j.app M) 0 :=
  ⟨kInjectiveResolutionFunctor C, kInjectiveResolutionInclusion C,
    fun _ _ => inferInstance, fun _ => inferInstance,
    fun _ i _ => CochainComplex.IsKInjective.nonempty_homotopy_zero _ (hK i)⟩

end Stacks.Injectives
