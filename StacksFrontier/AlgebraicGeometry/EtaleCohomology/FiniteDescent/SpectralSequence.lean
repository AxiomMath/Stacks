module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CohomologyBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.ExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.ResolutionSpectralSequence

/-!
# The descent spectral sequence of a finite surjection

Let `f : X ⟶ Y` be a finite surjective morphism of schemes, let `f_p : X_p ⟶ Y` be the structure
map of the `(p + 1)`-fold fibre product of `X` over `Y`, and let `F` be an abelian sheaf on the
small étale site of `Y`. There is a cohomological spectral sequence with

```
E_1^{p,q} = H^q_ét(X_p, f_p^{-1}F)
```

abutting to `H^{p+q}_ét(Y, F)`: each `H^n_ét(Y, F)` carries a finite decreasing filtration whose
graded pieces are the stable terms of the spectral sequence.

## Main results

* `Stacks.EtaleCohomology.exists_cechSheafSpectralSequence` — the spectral sequence, its first
  page and its abutment.

## Implementation notes

Both halves are imported. The exact sequence `0 ⟶ F ⟶ F_0 ⟶ F_1 ⟶ ⋯` with `F_p = f_{p,*}f_p^{-1}F`
is `Stacks.EtaleCohomology.exists_exact_cechSheafSequence`; the hyper-`Ext` spectral sequence of a
bounded-below complex representing `F`, with its first page and its finite filtration on the
abutment, is `Stacks.EtaleCohomology.exists_resolution_sheafH_spectralSequence`, which is
[Stacks, Tag 0AVI] read in étale cohomology. The only step taken here is the first-page
identification `H^q(Y, F_p) ≅ H^q(X_p, f_p^{-1}F)`, which holds because `f_p` is finite, hence
integral, so that direct image along it is exact and preserves injectives; that is
`Stacks.EtaleCohomology.sheafHSmallEtalePullbackPushforwardAddEquiv`, and `f_p` is finite by
`Stacks.EtaleCohomology.isFinite_cechProjection`.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtaleTopology

-- The derived category relative to `u + 1` and the Grothendieck abelian structure are the local
-- instances of
-- `StacksFrontier/AlgebraicGeometry/EtaleCohomology/FiniteDescent/ResolutionSpectralSequence.lean`;
-- their names are global, so they are re-enabled here rather than re-declared.
attribute [local instance] hasDerivedCategory_sheaf_smallEtaleTopology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **[Stacks, Tag 09Z2], the spectral sequence.** For a finite surjective morphism `f : X ⟶ Y`
of schemes and an abelian sheaf `F` on the small étale site of `Y` there is a cohomological
spectral sequence, starting on page one, with

```
E_1^{p,q} = H^q_ét(X_p, f_p^{-1}F),
```

the étale cohomology of the `(p + 1)`-fold fibre product `X_p = X ×_Y ⋯ ×_Y X` with coefficients
in the inverse image of `F`, abutting to `H^{p+q}_ét(Y, F)`: each `H^n_ét(Y, F)` carries a finite
decreasing filtration `Fil` such that in every bidegree `(p, q)` with `p + q = n` all sufficiently
late pages have vanishing incoming and outgoing differentials and are isomorphic to the graded
piece `Fil^p / Fil^{p+1}`. -/
public theorem exists_cechSheafSpectralSequence [IsFinite f] [Surjective f]
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1,
      (∀ p q : ℕ, Nonempty ((E.page 1).X ((p : ℤ), (q : ℤ)) ≅
          AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1}
            ((smallEtalePullbackAb (cechProjection f p)).obj F) q))) ∧
        ∃ (Fil : ∀ (_p : ℤ) (n : ℕ),
            Subobject (AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} F n)))
          (hFil : ∀ (p p' : ℤ) (n : ℕ), p ≤ p' → Fil p' n ≤ Fil p n),
          (∀ n : ℕ, ∃ s t : ℤ, s ≤ t ∧ Fil s n = ⊤ ∧ Fil t n = ⊥) ∧
            ∀ (p q : ℤ) (n : ℕ), p + q = (n : ℤ) → ∃ r₀ : ℤ, 1 ≤ r₀ ∧
              ∀ (r : ℤ) (hr : 1 ≤ r), r₀ ≤ r →
                (E.page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
                  (E.page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
                    Nonempty ((E.page r hr).X (p, q) ≅
                      cokernel (Subobject.ofLE (Fil (p + 1) n) (Fil p n)
                        (hFil p (p + 1) n (by omega)))) := by
  obtain ⟨d, haug, hdd, hmono, hex0, hex⟩ := exists_exact_cechSheafSequence f F
  obtain ⟨E, hE₁, Fil, hFil, hfin, hconv⟩ :=
    exists_resolution_sheafH_spectralSequence (cechSheaf f F) d hdd F (cechAug f F) haug hmono
      hex0 hex
  refine ⟨E, fun p q => ?_, Fil, hFil, hfin, hconv⟩
  exact ⟨(hE₁ p q).some ≪≫
    ((sheafHSmallEtalePullbackPushforwardAddEquiv (cechProjection f p) F q).symm).toAddCommGrpIso⟩

end Stacks.EtaleCohomology

end
