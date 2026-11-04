module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactObjects
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compact objects of the big étale topology of a big fppf site

A quasi-compact scheme is a quasi-compact object (Stacks 090H) of the big étale topology carried
by a big fppf site (Stacks 03FF), as it is of the fppf topology
(`AlgebraicGeometry.BigFppfSite.isQuasiCompactObject_of_compactSpace`). The argument is the same:
a covering sieve contains a chosen étale covering family, whose members are open maps and jointly
surjective; finitely many of them cover the quasi-compact scheme, and the finite subfamily is
again an étale covering, which has a chosen representative
(`AlgebraicGeometry.etaleCovering_has_representative`) whose arrows are arrows of the subfamily.

## Main results

* `AlgebraicGeometry.BigFppfSite.isQuasiCompactObject_etaleTopology_of_compactSpace`.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A quasi-compact scheme is a quasi-compact object of the big étale topology of a big fppf
site** (Stacks 090H). Every covering sieve of `X` contains a chosen étale covering family; its
members are open maps and jointly surjective, so finitely many of their images cover the
quasi-compact `X`, and the finite subfamily, an étale covering, has a chosen representative whose
members factor through finitely many members of the given covering. -/
@[sga "4 VI 1.6.2" "partial"]
public theorem BigFppfSite.isQuasiCompactObject_etaleTopology_of_compactSpace
    (B : BigFppfSite.{u}) (X : B.Schemes) (hX : CompactSpace (B.inclusion.obj X)) :
    (etaleTopology B).IsQuasiCompactObject X := by
  classical
  intro 𝒰 h𝒰
  obtain ⟨E, hE, hle⟩ := _root_.exists_isCovering_sieve₀_le (etaleCovering_isSite B)
    (fun _ _ => Iff.rfl) h𝒰
  have hjfl := B.jointlySurjective_and_flat_and_lfp_of_isCovering hE.1
  have hEet : ∀ i, Etale (B.inclusion.map (E.f i)) := by
    have h₂ : Presieve.ofArrows (fun i => B.inclusion.obj (E.X i))
        (fun i => B.inclusion.map (E.f i)) ∈
          Scheme.precoverage @Etale (B.inclusion.obj X) := hE.2
    exact ((Scheme.ofArrows_mem_precoverage_iff _).1 h₂).2
  obtain ⟨T, hT⟩ := (@isCompact_univ _ _ hX).elim_finite_subcover
    (fun i : E.I₀ => Set.range (B.inclusion.map (E.f i)))
    (fun i => ((B.fppfCovering hE.1).isOpenMap i).isOpen_range)
    (fun x _ => Set.mem_iUnion.mpr (hjfl.1 x))
  have het : IsEtaleCovering (κ := B.cutoff)
      ⟨X, { I₀ := ↥T, X := fun i => E.X ↑i, f := fun i => E.f ↑i }⟩ := by
    show Presieve.ofArrows (fun i : ↥T => B.inclusion.obj (E.X i))
        (fun i : ↥T => B.inclusion.map (E.f i)) ∈
          Scheme.precoverage @Etale (B.inclusion.obj X)
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun (i : ↥T) => hEet i.1⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, hx⟩
  obtain ⟨F, hF, ⟨hXX, hcomb⟩⟩ := etaleCovering_has_representative B _ het
  -- transport `F` across the equality of targets of the combinatorial equivalence
  have htransport : ∀ {V : B.Schemes} (hUV : X = V) {F' : PreZeroHypercover.{u + 1} V},
      etaleCovering B ⟨V, F'⟩ →
      (hUV ▸ ({ I₀ := ↥T, X := fun i => E.X ↑i, f := fun i => E.f ↑i } :
        PreZeroHypercover.{u + 1} X)).CombinatoriallyEquivalent F' →
      ∃ G : PreZeroHypercover.{u + 1} X, etaleCovering B ⟨X, G⟩ ∧
        ∃ (β : G.I₀ → ↥T) (hX : ∀ j, G.X j = E.X (β j)),
          ∀ j, G.f j = eqToHom (hX j) ≫ E.f (β j) := by
    intro V hUV F' hP h
    subst hUV
    exact ⟨F', hP, h.2⟩
  obtain ⟨E', hF, β, hβX, hβf⟩ := htransport hXX hF hcomb
  choose s α hα using fun c : ↥T =>
    (Sieve.mem_ofArrows_iff _ _ _).1 (hle _ (E.sieve₀_f ↑c))
  refine ⟨E', { s₀ := fun j => s (β j)
                h₀ := fun j => eqToHom (hβX j) ≫ α (β j)
                w₀ := fun j => ?_ }, ?_, ?_⟩
  · rw [Category.assoc, ← hα (β j)]
    exact (hβf j).symm
  · exact Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hF⟩
  · exact (Set.finite_range s).subset (by rintro _ ⟨j, rfl⟩; exact ⟨β j, rfl⟩)

end AlgebraicGeometry
