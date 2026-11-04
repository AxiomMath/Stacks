module

public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine
public import StacksFrontier.RingTheory.GeometricallyConnected
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections after extending a separably closed base field

Let `k` be a separably closed field, `K/k` any field extension and `S` a scheme over `k`.
The projection `p : S_K = S ×_{Spec k} Spec K ⟶ S` does not change global sections of sheaves
of sets on the small étale site: `Γ(S, F) = Γ(S_K, p^{-1} F)`.

## Main results

* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso_of_isSepClosed` — global
  sections over `S` agree, naturally in the sheaf, with global sections of the inverse image
  over the base change `S_K`.

## References

* [Stacks Project, Tag 0A3I](https://stacks.math.columbia.edu/tag/0A3I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- For a scheme `S` over a separably closed field `k` and any field extension `K/k`, pullback
along the projection `S ×_{Spec k} Spec K ⟶ S` preserves global sections of every sheaf of sets on
the small étale site, naturally in the sheaf. -/
@[stacks 0A3I, sga "4 XVI 1.5" "partial"]
public def globalSectionsSmallEtaleInverseImageIso_of_isSepClosed
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) :
    Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ≅
      smallEtaleInverseImage.{u, v}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⋙
        Sheaf.Γ
          (smallEtaleTopology (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
          (Type (max (u + 1) v)) :=
  letI : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (AlgebraicGeometry.geometricallyConnected_spec_iff k K).2
      ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum k K).2 inferInstance)
  globalSectionsSmallEtaleInverseImageIso.{u, v}
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (universally_isQuotientMap_of_flat_quasiCompact _)

end Stacks.EtaleCohomology

end
