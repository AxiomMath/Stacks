module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap

/-!
# The canonical conormal map is an isomorphism exactly when the ideal-sheaf lift pulls back to one

Stacks Tag 0B3V clause 3 builds the canonical map
`ker(q) ⊗ 𝓛^{⊗ -1} ⟶ 𝒞_{σ(X)/𝐏(ℰ)}` as
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap`, and its construction is a composite of
three morphisms of which the outer two are isomorphisms: the identification
`Stacks.ProjectiveBundleConormal.pullbackSourceIso` of the source with
`σ^*((π^*ker q) ⊗ 𝒪(-1))`, then `σ^*` of
`Stacks.ProjectiveBundleConormal.idealSheafLift`, then the identification
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` of `𝒞_σ` with `σ^*ℐ(σ)`.

**So it suffices for the clause's isomorphism assertion that `σ^*` of the ideal-sheaf lift is an
isomorphism**, and this file records that reduction. It is elementary, but having it means the
twist `𝒪(-1)`, the base change of its inverse along `σ`, and the conormal-sheaf comparison need
not appear again: what is left to check is that `σ^*` carries

  `(π^*ker q) ⊗ 𝒪(-1) ⟶ ℐ(σ)`

to an isomorphism, a statement about the ideal sheaf of the section alone.

## Main results

* `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_eq_pullback_idealSheafLift`: the canonical
  map written as that three-fold composite.
* `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_isIso_pullback_idealSheafLift`:
  the reduction.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

include hσ e hqe in
/-- **The canonical map of Tag 0B3V clause 3 as a three-fold composite**, the middle factor of
which is the only one that is not an isomorphism. This is its definition, restated so that the
two reductions below can quote it. -/
theorem conormalCanonicalMap_eq_pullback_idealSheafLift :
    conormalCanonicalMap E Q hσ e hqe =
      (pullbackSourceIso E Q hσ e).inv ≫
        (Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv :=
  rfl

include hσ e hqe in
/-- **If `σ^*` carries the ideal-sheaf lift to an isomorphism then the canonical map of Tag 0B3V
clause 3 is one**, the two remaining factors being isomorphisms. -/
theorem isIso_conormalCanonicalMap_of_isIso_pullback_idealSheafLift
    (h : IsIso ((Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe))) :
    IsIso (conormalCanonicalMap E Q hσ e hqe) := by
  rw [conormalCanonicalMap_eq_pullback_idealSheafLift]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' h (Iso.isIso_inv _))

end Stacks.ProjectiveBundleConormal

end
