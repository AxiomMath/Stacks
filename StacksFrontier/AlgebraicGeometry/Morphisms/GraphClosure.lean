module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closure of the graph of a morphism defined on an open subscheme

Let `sX : X ⟶ S` and `q : P ⟶ S` be morphisms of schemes, `U ⊆ X` an open subscheme and
`g : U ⟶ P` a morphism over `S`. Pairing `g` with the inclusion `U ⟶ X` gives the *graph*
`U ⟶ X ×_S P`, and its scheme-theoretic image `X'` is the closure of the graph. It comes with the
two projections `b : X' ⟶ X` and `f : X' ⟶ P`. This file proves the basic properties of this
construction:

* `b` is proper when `q` is, and `f` is proper when `sX` is;
* for `U ⟶ X` quasi-compact and `q` separated, `b` is an isomorphism over `U`;
* for `X` integral and `U` dense and quasi-compact, `X'` is integral;
* `f` is dominant when `g` is.

For `P = ℙ¹_S` and `g` given by a section of `𝒪_X` over `U` this is the graph construction of
[Stacks, Tag 02RQ]. The proof of [Stacks, Tag 095U] uses it for a dominant morphism `U ⟶ ℙ¹_k`
from a dense open of an integral proper scheme over a field.

## Main definitions

* `AlgebraicGeometry.OpenGraphClosure.graph`: the graph `U ⟶ X ×_S P`.
* `AlgebraicGeometry.OpenGraphClosure.closure`: its scheme-theoretic image `X'`, with the
  projections `AlgebraicGeometry.OpenGraphClosure.projection` (`b`) and
  `AlgebraicGeometry.OpenGraphClosure.secondProjection` (`f`).

## Main results

* `AlgebraicGeometry.OpenGraphClosure.isIso_projection_restrict`: `b⁻¹(U) ⟶ U` is an isomorphism.
* `AlgebraicGeometry.OpenGraphClosure.isIntegral_closure`: `X'` is integral.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace OpenGraphClosure

variable {X S P : Scheme.{u}} (sX : X ⟶ S) (q : P ⟶ S) (U : X.Opens) (g : U.toScheme ⟶ P)
  (hg : g ≫ q = U.ι ≫ sX)

/-- The graph `U ⟶ X ×_S P` of a morphism `g : U ⟶ P` over `S`. -/
def graph : U.toScheme ⟶ pullback sX q :=
  pullback.lift U.ι g hg.symm

/-- `X'`, the closure of the graph, taken as its scheme-theoretic image. -/
@[ega "IV 20.4.1"]
abbrev closure : Scheme.{u} :=
  (graph sX q U g hg).image

/-- The closed immersion `X' ⟶ X ×_S P`. -/
abbrev closureι : closure sX q U g hg ⟶ pullback sX q :=
  (graph sX q U g hg).imageι

/-- The morphism `U ⟶ X'` onto the graph. -/
abbrev inclusion : U.toScheme ⟶ closure sX q U g hg :=
  (graph sX q U g hg).toImage

/-- The first projection `b : X' ⟶ X`. -/
abbrev projection : closure sX q U g hg ⟶ X :=
  closureι sX q U g hg ≫ pullback.fst sX q

/-- The second projection `f : X' ⟶ P`. -/
abbrev secondProjection : closure sX q U g hg ⟶ P :=
  closureι sX q U g hg ≫ pullback.snd sX q

/-- The graph is a section of the first projection over `U`. -/
theorem inclusion_comp_projection :
    inclusion sX q U g hg ≫ projection sX q U g hg = U.ι := by
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, graph, pullback.lift_fst]

/-- The graph followed by the second projection is `g`. -/
theorem inclusion_comp_secondProjection :
    inclusion sX q U g hg ≫ secondProjection sX q U g hg = g := by
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, graph, pullback.lift_snd]

/-- The first projection is proper when `q` is. -/
instance isProper_projection [IsProper q] : IsProper (projection sX q U g hg) := by
  change IsProper (closureι sX q U g hg ≫ pullback.fst sX q)
  infer_instance

/-- The second projection is proper when `sX` is. -/
instance isProper_secondProjection [IsProper sX] :
    IsProper (secondProjection sX q U g hg) := by
  change IsProper (closureι sX q U g hg ≫ pullback.snd sX q)
  infer_instance

/-- The graph morphism is quasi-compact when the open immersion of `U` is quasi-compact and `q`
is quasi-separated. -/
instance quasiCompact_graph [QuasiCompact U.ι] [QuasiSeparated q] :
    QuasiCompact (graph sX q U g hg) := by
  have : QuasiCompact (graph sX q U g hg ≫ pullback.fst sX q) := by
    rw [graph, pullback.lift_fst]
    infer_instance
  exact QuasiCompact.of_comp (graph sX q U g hg) (pullback.fst sX q)

/-- The inclusion of `U` into `X'` is scheme-theoretically dominant. -/
private theorem isSchemeTheoreticallyDominant_inclusion [QuasiCompact U.ι]
    [QuasiSeparated q] :
    IsSchemeTheoreticallyDominant (inclusion sX q U g hg) :=
  ⟨ker_toImage_eq_bot (graph sX q U g hg)⟩

/-- The morphism `U ⟶ b⁻¹(U)` induced by the graph. -/
def restrictLift :
    U.toScheme ⟶ pullback (projection sX q U g hg) U.ι :=
  pullback.lift (inclusion sX q U g hg) (𝟙 U.toScheme)
    (by rw [Category.id_comp]; exact inclusion_comp_projection sX q U g hg)

/-- The morphism `U ⟶ b⁻¹(U)` followed by the projection to `X'` is the inclusion `U ⟶ X'`. -/
@[simp]
theorem restrictLift_fst :
    restrictLift sX q U g hg ≫ pullback.fst (projection sX q U g hg) U.ι =
      inclusion sX q U g hg :=
  pullback.lift_fst _ _ _

/-- The morphism `U ⟶ b⁻¹(U)` followed by the projection to `U` is the identity. -/
@[simp]
theorem restrictLift_snd :
    restrictLift sX q U g hg ≫ pullback.snd (projection sX q U g hg) U.ι = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- For `q` separated, `U ⟶ b⁻¹(U)` is a closed immersion. -/
theorem isClosedImmersion_restrictLift [IsSeparated q] :
    IsClosedImmersion (restrictLift sX q U g hg) := by
  have : IsSeparated (projection sX q U g hg) := by
    show IsSeparated (closureι sX q U g hg ≫ pullback.fst sX q)
    infer_instance
  have : IsClosedImmersion (restrictLift sX q U g hg ≫
      pullback.snd (projection sX q U g hg) U.ι) := by
    rw [restrictLift_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd (projection sX q U g hg) U.ι)

/-- `U ⟶ b⁻¹(U)` has trivial kernel ideal sheaf. -/
theorem ker_restrictLift [QuasiCompact U.ι] [QuasiSeparated q] :
    (restrictLift sX q U g hg).ker = ⊥ := by
  have hpb : IsPullback (𝟙 U.toScheme) (restrictLift sX q U g hg)
      (inclusion sX q U g hg) (pullback.fst (projection sX q U g hg) U.ι) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have := isSchemeTheoreticallyDominant_inclusion sX q U g hg
  exact (IsSchemeTheoreticallyDominant.of_isPullback hpb).ker_eq_bot

/-- `U ⟶ b⁻¹(U)` is an isomorphism. -/
theorem isIso_restrictLift [QuasiCompact U.ι] [IsSeparated q] :
    IsIso (restrictLift sX q U g hg) :=
  have := isClosedImmersion_restrictLift sX q U g hg
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (ker_restrictLift sX q U g hg)

/-- For `U ⟶ X` quasi-compact and `q` separated, the restriction `b⁻¹(U) ⟶ U` of the first
projection is an isomorphism. -/
theorem isIso_projection_restrict [QuasiCompact U.ι] [IsSeparated q] :
    IsIso (pullback.snd (projection sX q U g hg) U.ι) := by
  have hiso := isIso_restrictLift sX q U g hg
  have : IsIso (restrictLift sX q U g hg ≫ pullback.snd (projection sX q U g hg) U.ι) := by
    rw [restrictLift_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left (restrictLift sX q U g hg) _

/-- The image of `U` in `X'` is exactly `b⁻¹(U)`. -/
theorem range_inclusion [QuasiCompact U.ι] [IsSeparated q] :
    Set.range (inclusion sX q U g hg) = (projection sX q U g hg) ⁻¹' (U : Set X) := by
  have hiso := isIso_restrictLift sX q U g hg
  rw [← Scheme.Opens.range_ι U, ← Scheme.Pullback.range_fst, ← restrictLift_fst sX q U g hg]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨restrictLift sX q U g hg x, by rw [← Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, rfl⟩
    refine ⟨inv (restrictLift sX q U g hg) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- `X'` is integral when `X` is integral and `U` is dense. -/
@[ega "IV 20.4.1" "partial"]
theorem isIntegral_closure [IsIntegral X] [QuasiCompact U.ι] [QuasiSeparated q]
    (hU : Dense (U : Set X)) : IsIntegral (closure sX q U g hg) := by
  have hne : Nonempty U.toScheme := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  have hUirr : IrreducibleSpace U.toScheme :=
    Topology.IsOpenEmbedding.irreducibleSpace (f := U.ι.base) U.isOpenEmbedding
  have := isSchemeTheoreticallyDominant_inclusion sX q U g hg
  have hred : IsReduced (closure sX q U g hg) :=
    IsSchemeTheoreticallyDominant.isReduced (inclusion sX q U g hg)
  have hdom : IsDominant (inclusion sX q U g hg) := inferInstance
  have hd : DenseRange (inclusion sX q U g hg).base := hdom.denseRange
  have himg : IsIrreducible (Set.range (inclusion sX q U g hg)) := by
    have := (IrreducibleSpace.isIrreducible_univ U.toScheme).image
      (inclusion sX q U g hg).base (Continuous.continuousOn (by continuity))
    rwa [Set.image_univ] at this
  have hirr : IrreducibleSpace (closure sX q U g hg) := by
    rw [irreducibleSpace_def]
    have := himg.closure
    rwa [hd.closure_eq] at this
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨hirr, hred⟩

/-- The second projection is dominant when `g` is. -/
theorem isDominant_secondProjection [QuasiCompact U.ι] [QuasiSeparated q] [IsDominant g] :
    IsDominant (secondProjection sX q U g hg) := by
  have : IsDominant (inclusion sX q U g hg ≫ secondProjection sX q U g hg) := by
    rw [inclusion_comp_secondProjection]
    infer_instance
  exact IsDominant.of_comp (inclusion sX q U g hg) (secondProjection sX q U g hg)

end OpenGraphClosure

end AlgebraicGeometry

end
