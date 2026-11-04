module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.LocalRepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.NestedRestriction
import StacksFrontier.Algebra.Homology.QuasiIsoRoof
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# The local criterion for perfectness

Let `X` be a ringed space and let `K` be an object of the derived category of `𝒪_X`-modules.
Perfectness of `K` asks for a complex representing `K` which on an open covering receives
quasi-isomorphisms from strictly perfect complexes. This file shows that the weaker, and in
practice available, hypothesis suffices: if some complex `F` represents `K` and there is an open
covering `U i` of `X` together with strictly perfect complexes `P i` on `U i` which are merely
*isomorphic in the derived category* to `F|_{U i}`, then `K` is perfect.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfect_of_strictlyPerfect_local_models`: the local criterion
  itself, [Stacks, Tag 08CN].

## Implementation notes

The hypothesis is about the derived categories of the members `U i` of the covering, so the
statement takes a model of each of them, besides the model of the derived category of `X` in
which `K` lives; all of them are arbitrary. In any model, an isomorphism `Q(P i) ≅ Q(F|_{U i})`
is a roof of quasi-isomorphisms between `P i` and `F|_{U i}`
(`CochainComplex.quasiIsoRoof_iff_nonempty_iso`), and the proof concludes with the version of the
criterion at the level of complexes,
`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs`, which straightens each roof near
every point (Stacks 08C8). All universes of the ringed space coincide, as they must for
`StrictlyPerfect.OXMod` to exist.

## References

* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d d'

/-- An object of the derived category of `𝒪_X`-modules which is, on an open covering of `X`,
isomorphic in the derived category to a strictly perfect complex is perfect.

The hypothesis fixes a complex `F` representing the object, and asks the local strictly perfect
models to be isomorphic, in the derived categories of the members of the covering, to the
restrictions of `F`. -/
@[stacks 08CN "local_criterion"]
theorem isPerfect_of_strictlyPerfect_local_models (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ U : Opens X.carrier, HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (K : DerivedCategory (OXMod.{u, u} X))
    (h : ∃ F : CochainComplex (OXMod.{u, u} X) ℤ,
      Nonempty (DerivedCategory.Q.obj F ≅ K) ∧
        ∃ (I : Type u) (U : I → Opens X.carrier), (⨆ i, U i) = ⊤ ∧
          ∀ i : I, ∃ P : CochainComplex
            (OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) ℤ,
            IsStrictlyPerfect P ∧
              Nonempty (DerivedCategory.Q.obj P ≅
                DerivedCategory.Q.obj (restrictComplex F (U i)))) :
    IsPerfect K := by
  obtain ⟨F, hFK, I, U, hU, hP⟩ := h
  refine ⟨F, isPerfectComplex_of_local_roofs fun x => ?_, hFK⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ trivial : x ∈ ⨆ i, U i)
  obtain ⟨P, hPs, hPF⟩ := hP i
  exact ⟨U i, hi, P, hPs, (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).2 hPF⟩

end AlgebraicGeometry.RingedSpace

end
