module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage

/-!
# Refining a covering by an étale covering, a proper morphism and an étale covering

Let `E` be a big étale site and let `K` be a second precoverage on its underlying category, a
finer topology such as the ph or the h topology. Condition (0EZ8) of the comparison situation of
Stacks 0EZ3, for the pair `(K, étale)` with the proper morphisms as distinguished class, asks
that every `K`-covering be refined in three stages: by an étale covering, then over each member
by a single proper morphism which is a `K`-covering, then by an étale covering of its source.

For the ph and the h topologies the refinement is produced affine-locally: over an affine open
`O` of the target the given covering is refined by a proper morphism `W ⟶ O` together with a
covering of `W` by finitely many open subschemes, each mapping to a member of the given
covering. This file assembles such affine-local data into the three-stage refinement. The first
stage is the covering of the target by all its affine opens. Only the affine-local step depends
on the topology, and it is supplied by `AlgebraicGeometry.BigPHSite.exists_properRefinement` and
`AlgebraicGeometry.BigHSite.exists_properRefinement`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.ofArrows_mem_precoverage_of_isOpenImmersion` — a jointly
  surjective family of open immersions presents a covering of the big étale site.
* `AlgebraicGeometry.BigEtaleSite.exists_properRefinement_of_affine` — the three-stage refinement
  from its affine-local form.

## Implementation notes

The site's representative axiom replaces an étale covering only up to combinatorial
equivalence, which does not change the presented presieve; that is how membership in the
precoverage is obtained without bounding the index type. Every scheme in sight is an object of
the site because the open subschemes of an object of the site are (Stacks 000R (3)).

## References

* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0F0I](https://stacks.math.columbia.edu/tag/0F0I)
* [Stacks Project, Tag 0F0J](https://stacks.math.columbia.edu/tag/0F0J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigEtaleSite

variable (E : BigEtaleSite.{u})

/-- A jointly surjective family of open immersions of the underlying category of a big étale
site presents a covering of the site: it is an étale covering, and the site has a chosen covering
with the same presieve. -/
public theorem ofArrows_mem_precoverage_of_isOpenImmersion {T : E.Scheme} {ι : Type (u + 1)}
    (Y : ι → E.Scheme) (g : ∀ i, Y i ⟶ T) (hopen : ∀ i, IsOpenImmersion (E.inclusion.map (g i)))
    (hsurj : ∀ x : E.inclusion.obj T, ∃ i, x ∈ Set.range (E.inclusion.map (g i))) :
    Presieve.ofArrows Y g ∈ E.precoverage T := by
  let W : Covering E.Scheme := ⟨T, ⟨ι, Y, g⟩⟩
  have hW : IsEtaleCovering W := by
    change Presieve.ofArrows _ (fun i => E.inclusion.map (g i)) ∈
      AlgebraicGeometry.Scheme.etalePrecoverage _
    unfold AlgebraicGeometry.Scheme.etalePrecoverage
    exact (AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff (@Etale)).2
      ⟨hsurj, fun i => inferInstance⟩
  obtain ⟨⟨Wb, Wf⟩, hW', hT, hcomb⟩ := E.exists_covering_rep W hW
  obtain rfl : T = Wb := hT
  exact ⟨Wf, PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb, hW'⟩

/-- A jointly surjective family of open immersions into an object of a big étale site presents a
covering, after replacing its sources by the corresponding objects of the site. -/
private theorem ofArrows_obj_mem_precoverage {T : E.Scheme} {J : Type u}
    (V : J → AlgebraicGeometry.Scheme.{u}) (j : ∀ k, V k ⟶ E.inclusion.obj T)
    (hj : ∀ k, IsOpenImmersion (j k)) (hcov : ⋃ k, Set.range (j k) = Set.univ) :
    Presieve.ofArrows
      (fun k : ULift.{u + 1} J =>
        E.obj (V k.down) (AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion (j k.down) T.2))
      (fun k => ObjectProperty.homMk (j k.down)) ∈ E.precoverage T :=
  E.ofArrows_mem_precoverage_of_isOpenImmersion _ _ (fun k => hj k.down) fun y => by
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ y)
    exact ⟨ULift.up k, hk⟩

/-- **Property (0EZ8) of Stacks 0EZ3 from its affine-local form.** Let `K` be a precoverage on the
underlying category of a big étale site `E` and `R` a presieve on an object `U`. Suppose that over
every affine open `O` of `U` there are a proper morphism `f : W ⟶ O` of the site whose singleton
is a `K`-covering, and a covering of `W` by open subschemes each of which maps over `U` to a
member of `R`. Then `R` is refined in three stages: by an étale covering of `U` (its affine
opens), then over each member by the single proper morphism `f`, then by an étale covering of the
source of `f` (the given open subschemes). -/
public theorem exists_properRefinement_of_affine (K : Precoverage E.Scheme) {U : E.Scheme}
    {R : Presieve U}
    (h : ∀ (O : (E.inclusion.obj U).Opens), IsAffineOpen O →
      ∃ (W : E.Scheme)
        (f : W ⟶ E.obj O.toScheme (AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion O.ι U.2)),
        IsProper (E.inclusion.map f) ∧ Presieve.singleton f ∈ K _ ∧
        ∃ (J : Type u) (V : J → AlgebraicGeometry.Scheme.{u}) (j : ∀ k, V k ⟶ E.inclusion.obj W),
          (∀ k, IsOpenImmersion (j k)) ∧ (⋃ k, Set.range (j k)) = Set.univ ∧
          ∀ k, ∃ (Z : E.Scheme) (e : Z ⟶ U), R e ∧ ∃ h : V k ⟶ E.inclusion.obj Z,
            h ≫ E.inclusion.map e = j k ≫ E.inclusion.map f ≫ O.ι) :
    ∃ S : Presieve U, S ∈ E.precoverage U ∧
      ∀ ⦃V : E.Scheme⦄ (v : V ⟶ U), S v →
        ∃ (W : E.Scheme) (f : W ⟶ V), IsProper (E.inclusion.map f) ∧
          Presieve.singleton f ∈ K V ∧
          ∃ T : Presieve W, T ∈ E.precoverage W ∧ T.FactorsThruAlong R (f ≫ v) := by
  refine ⟨_, E.ofArrows_obj_mem_precoverage
    (fun a : (E.inclusion.obj U).affineOpens => a.1.toScheme) (fun a => a.1.ι)
    (fun a => inferInstance) ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ (⨆ V : (E.inclusion.obj U).affineOpens, V.1) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.2 ⟨V, by simpa using hxV⟩
  rintro _ _ ⟨a⟩
  obtain ⟨W, f, hp, hK, J, V, j, hj, hcov, hfac⟩ := h a.down.1 a.down.2
  refine ⟨W, f, hp, hK, _, E.ofArrows_obj_mem_precoverage V j hj (by rw [hcov]), ?_⟩
  rintro _ _ ⟨k⟩
  obtain ⟨Z', e, he, h, hh⟩ := hfac k.down
  refine ⟨Z', ObjectProperty.homMk h, e, he, ?_⟩
  apply E.inclusion.map_injective
  simp only [Functor.map_comp]
  exact hh

end BigEtaleSite

end AlgebraicGeometry

end
