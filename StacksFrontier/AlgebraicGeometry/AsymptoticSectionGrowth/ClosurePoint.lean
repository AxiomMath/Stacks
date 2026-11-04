module

public import StacksFrontier.AlgebraicGeometry.AsymptoticSectionGrowth.Basic
public import StacksFrontier.AlgebraicGeometry.ClosurePointDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity

/-!
# Sections on the closure of a non-closed point grow without bound

Let `k` be a field, `X` a scheme proper over `k` and `x` a point of `X` which is **not closed**.
Let `i : Z ⟶ X` be any closed subscheme whose underlying set is `closure {x}` — for instance the
reduced induced structure `(vanishingIdeal (Closeds.closure {x})).subscheme`.  Then `Z` is proper
over `k` of dimension `d ≥ 1`, so for any ample invertible `𝒪_Z`-module `𝓜`

`dim_k Γ(Z, 𝓜^{⊗ n}) → ∞`.

This is a consequence of asymptotic Riemann–Roch [Stacks, Tag 0BJ8], since `Z` is proper over `k`
of dimension at least `1`.

## Main results

* `AlgebraicGeometry.exists_forall_le_finrank_globalSections_of_range_eq_closure`: for any closed
  subscheme on `closure {x}` and any ample invertible module on it.
* `AlgebraicGeometry.exists_forall_le_finrank_globalSections_subscheme_closure`: the same for the
  reduced induced structure and the restriction `𝓛|_Z` of an ample invertible module on `X`.

## Implementation notes

The general statement takes the ample invertible module on `Z` abstractly, so that it applies to
any closed subscheme on `closure {x}`, not only the reduced one.  The corollary's conclusion
carries the invertibility of the pullback in a `letI`, because instance search does not identify
the different spellings of a scheme's structure sheaf of rings.

## References

* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
* [Stacks Project, Tag 0BJ8](https://stacks.math.columbia.edu/tag/0BJ8)
-/

@[expose] public noncomputable section

open CategoryTheory Set TopologicalSpace
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Let `X` be proper over a field `k`, `x` a point of `X` which is not closed, and `i : Z ⟶ X` a
closed immersion with range `closure {x}`. For every ample invertible `𝒪_Z`-module `M` and every
`c : ℕ`, the dimension over `k` of the global sections of `M^{⊗ n}` is at least `c` for all large
`n`. -/
public theorem exists_forall_le_finrank_globalSections_of_range_eq_closure (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    {x : X} (hx : ¬ IsClosed ({x} : Set X)) (hrange : Set.range i.base = closure ({x} : Set X))
    (M : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M]
    (hM : Scheme.Modules.IsAmple Z M) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → c ≤ Module.finrank k (globalSectionsOverField k (i ≫ f)
      (tensorPower Z.presheaf Z.ringCatSheaf.2 M (n : ℤ))) := by
  have hone : (1 : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
    rw [← topologicalKrullDim_range_eq i, hrange]
    exact one_le_topologicalKrullDim_closure_singleton hx
  have hmem : x ∈ Set.range i.base := by rw [hrange]; exact subset_closure rfl
  obtain ⟨d, hdim⟩ :=
    exists_topologicalKrullDim_eq_natCast_of_isProper k (i ≫ f) ⟨hmem.choose⟩
  have hd1 : 1 ≤ d := by exact_mod_cast hone.trans_eq hdim
  exact exists_forall_le_finrank_globalSectionsOverField k (i ≫ f) d hdim hd1 M hM c

/-- Let `X` be proper over a field `k`, `L` an ample invertible `𝒪_X`-module, and `x` a point of
`X` which is not closed. If `Z` is the reduced induced closed subscheme on `closure {x}`, then for
every `c : ℕ` the dimension over `k` of the global sections of `(L|_Z)^{⊗ n}` is at least `c` for
all large `n`. -/
public theorem exists_forall_le_finrank_globalSections_subscheme_closure (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) (x : X) (hx : ¬ IsClosed ({x} : Set X)) (c : ℕ) :
    letI I : X.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
    letI : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback I.subschemeι).obj L) := inferInstance
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → c ≤ Module.finrank k (globalSectionsOverField k
      (I.subschemeι ≫ f) (tensorPower I.subscheme.presheaf I.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback I.subschemeι).obj L) (n : ℤ))) := by
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hMample : Scheme.Modules.IsAmple I.subscheme
      ((Scheme.Modules.pullback I.subschemeι).obj L) :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
        I.subschemeι L (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L hL)
        (Or.inl ⟨inferInstance, inferInstance⟩))
  exact exists_forall_le_finrank_globalSections_of_range_eq_closure k f I.subschemeι hx
    (by rw [hI, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]; rfl) _ hMample c


end AlgebraicGeometry

end
