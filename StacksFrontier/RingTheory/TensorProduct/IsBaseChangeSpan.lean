module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# A base change is spanned by the image of its source

If `f : M →ₗ[R] N` exhibits `N` as the base change of `M` along `R → S`, then the image of `M`
spans `N` over `S`.

## Main results

* `IsBaseChange.span_range_eq_top`: the image of `M` spans the base change `N` over `S`.
-/

@[expose] public section

namespace IsBaseChange

/-- If `N` is the base change of `M` along `R → S`, the image of `M` spans `N` over `S`. -/
theorem span_range_eq_top {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Submodule.span S (Set.range f) = ⊤ :=
  eq_top_iff.2 fun n _ =>
    hf.inductionOn n _ (zero_mem _) (fun m => Submodule.subset_span ⟨m, rfl⟩)
      (fun s _ hn => Submodule.smul_mem _ s hn) (fun _ _ => Submodule.add_mem _)

end IsBaseChange
