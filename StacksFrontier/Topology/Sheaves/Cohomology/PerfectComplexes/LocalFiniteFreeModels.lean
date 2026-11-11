module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.QuasiIsoRoof
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalRingStalks
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Perfect objects as local finite complexes of finite (locally) free modules

Let `X` be a ringed space all of whose structure-sheaf stalks are local rings, and let `E` be an
object of the derived category of `𝒪_X`-modules. [Stacks, Tag 0BCJ] says that the following are
equivalent:

1. `E` is perfect;
2. there is an open covering `X = ⋃ U i` such that each `E|_{U i}` can be represented by a
   finite complex of finite locally free `𝒪_{U i}`-modules;
3. there is an open covering `X = ⋃ U i` such that each `E|_{U i}` can be represented by a
   finite complex of finite free `𝒪_{U i}`-modules.

"Can be represented by" means isomorphic in the derived category of `U i`.

The implications (3) ⇒ (2) ⇒ (1) hold on any ringed space: a finite free module is finite
locally free, and a bounded complex with finite locally free terms is a perfect complex
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_bounded_isFiniteLocallyFree`), so that
perfectness passes along the derived isomorphisms and glues over the covering. The implication
(1) ⇒ (3) needs the local-ring hypothesis, through
`AlgebraicGeometry.RingedSpace.isPerfect_iff_hasFiniteLocallyFreeRepresentation` ([Stacks,
Tag 0BCI]); shrinking the covering then makes the terms free.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_bounded_isFiniteLocallyFree`: a bounded
  complex with finite locally free terms is a perfect complex.
* `AlgebraicGeometry.RingedSpace.isPerfect_tfae`: [Stacks, Tag 0BCJ].

## Implementation notes

The restriction `E|_{U i}` is the image in the derived category of `U i` of the restriction of a
complex representing `E`, as in
`AlgebraicGeometry.RingedSpace.isPerfect_of_strictlyPerfect_local_models`; restriction to an open
is exact, so this does not depend on the representative. The derived categories of `X` and of its
open subspaces are arbitrary models.

## References

* [Stacks Project, Tag 0BCJ](https://stacks.math.columbia.edu/tag/0BCJ)
* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d d'

variable {X : RingedSpace.{u, u}}

/-- A bounded complex whose terms are finite locally free is a perfect complex: near every point
its finitely many nonzero terms are simultaneously free, so its restriction there is strictly
perfect and maps to itself by the identity. -/
theorem isPerfectComplex_of_bounded_isFiniteLocallyFree (P : CochainComplex (OXMod.{u, u} X) ℤ)
    (hbounded : {j : ℤ | ¬ IsZero (P.X j)}.Finite)
    (hterms : ∀ j : ℤ,
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := structureSheafOfRings X) (P.X j)) :
    IsPerfectComplex P := by
  refine isPerfectComplex_of_forall_exists fun x => ?_
  obtain ⟨V, hxV, hV⟩ := exists_free_iso_over_of_bounded P hbounded hterms x
  refine ⟨V, hxV, restrictComplex P V, ⟨?_, fun j => ?_⟩, 𝟙 _, inferInstance⟩
  · exact hbounded.subset fun j hj hz => hj (Functor.map_isZero (restrictModules X V) hz)
  · obtain ⟨n, ⟨e⟩⟩ := hV j
    obtain ⟨e'⟩ := nonempty_restrictModules_obj_iso_finiteFree (P.X j) V n e
    exact (isDirectSummandOfFiniteFree_iff_retract _).mpr ⟨n, ⟨⟨e'.hom, e'.inv, by simp⟩⟩⟩

/-- **Stacks 0BCJ.** Let `X` be a ringed space all of whose stalks `𝒪_{X,x}` are local rings, and
let `K` be an object of `D(𝒪_X)`. The following are equivalent:

1. `K` is perfect;
2. there is an open covering `X = ⋃ U i` such that each `K|_{U i}` is isomorphic, in the derived
   category of `U i`, to a finite complex of finite locally free `𝒪_{U i}`-modules;
3. there is an open covering `X = ⋃ U i` such that each `K|_{U i}` is isomorphic, in the derived
   category of `U i`, to a finite complex of finite free `𝒪_{U i}`-modules.

`K|_{U i}` is the restriction of a complex `F` representing `K`, read in the derived category of
`U i`; a finite free module is one isomorphic to `𝒪^{⊕ n}`. -/
@[stacks 0BCJ "perfect iff locally represented by finite complexes of finite (locally) free"]
theorem isPerfect_tfae [∀ x : X.carrier, IsLocalRing (ToType (X.presheaf.stalk x))]
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ U : Opens X.carrier, HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (K : DerivedCategory (OXMod.{u, u} X)) :
    List.TFAE [IsPerfect K,
      ∃ F : CochainComplex (OXMod.{u, u} X) ℤ, Nonempty (DerivedCategory.Q.obj F ≅ K) ∧
        ∃ (I : Type u) (U : I → Opens X.carrier), (⨆ i, U i) = ⊤ ∧
          ∀ i : I, ∃ P : CochainComplex (OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) ℤ,
            {j : ℤ | ¬ IsZero (P.X j)}.Finite ∧
              (∀ j : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
                (R := structureSheafOfRings (X.restrict (U i).isOpenEmbedding)) (P.X j)) ∧
                Nonempty (DerivedCategory.Q.obj P ≅
                  DerivedCategory.Q.obj (restrictComplex F (U i))),
      ∃ F : CochainComplex (OXMod.{u, u} X) ℤ, Nonempty (DerivedCategory.Q.obj F ≅ K) ∧
        ∃ (I : Type u) (U : I → Opens X.carrier), (⨆ i, U i) = ⊤ ∧
          ∀ i : I, ∃ P : CochainComplex (OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) ℤ,
            {j : ℤ | ¬ IsZero (P.X j)}.Finite ∧
              (∀ j : ℤ, ∃ n : ℕ,
                Nonempty (P.X j ≅ finiteFree (X.restrict (U i).isOpenEmbedding) n)) ∧
                Nonempty (DerivedCategory.Q.obj P ≅
                  DerivedCategory.Q.obj (restrictComplex F (U i)))] := by
  tfae_have 1 → 3 := fun hK => by
    obtain ⟨E, hEK, I, U, hU, hmodels⟩ :=
      (hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation K).mp
        ((isPerfect_iff_hasFiniteLocallyFreeRepresentation K).mp hK)
    refine ⟨E, hEK, I, U, hU, fun i => ?_⟩
    obtain ⟨P, hbounded, hterms, f, hf⟩ := hmodels i
    exact ⟨P, hbounded, hterms, ⟨asIso (DerivedCategory.Q.map f)⟩⟩
  tfae_have 3 → 2 := by
    rintro ⟨F, hFK, I, U, hU, hmodels⟩
    refine ⟨F, hFK, I, U, hU, fun i => ?_⟩
    obtain ⟨P, hbounded, hterms, e⟩ := hmodels i
    refine ⟨P, hbounded, fun j => ?_, e⟩
    obtain ⟨n, ⟨e'⟩⟩ := hterms j
    exact isFiniteLocallyFree_of_iso e'
      (isFiniteLocallyFree_finiteFree (X.restrict (U i).isOpenEmbedding) n)
  tfae_have 2 → 1 := by
    rintro ⟨F, hFK, I, U, hU, hmodels⟩
    refine ⟨F, isPerfectComplex_of_forall_isPerfectComplex_restrict fun x => ?_, hFK⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ trivial : x ∈ ⨆ i, U i)
    obtain ⟨P, hbounded, hterms, e⟩ := hmodels i
    exact ⟨U i, hi, (isPerfectComplex_iff_of_quasiIsoRoof
      ((CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).2 e)).1
        (isPerfectComplex_of_bounded_isFiniteLocallyFree P hbounded hterms)⟩
  tfae_finish

end AlgebraicGeometry.RingedSpace

end
