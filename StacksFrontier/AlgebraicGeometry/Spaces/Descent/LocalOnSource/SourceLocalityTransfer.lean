module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer

/-!
# The scheme-side topology of each topology of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Each of the five topologies `τ` of
Stacks 03YH on the algebraic spaces over `S` has a counterpart on schemes, and a `τ`-covering
family of algebraic spaces all of whose members and whose target are *representable* is a
covering family of the representing schemes for that counterpart.

## Main definitions

* `AlgebraicGeometry.Space.Topology.schemePrecoverage`: the precoverage on schemes
  corresponding to `τ`.

## Main results

* `AlgebraicGeometry.Space.Topology.isCovering_yoneda`: a `τ`-covering family of representables
  is a `τ`-covering family of the representing schemes.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The precoverage on schemes corresponding to one of the five topologies of Stacks 03YH on
the algebraic spaces over `S`. -/
def Topology.schemePrecoverage : Topology → Precoverage Scheme.{u}
  | .fpqc => Scheme.fpqcPrecoverage
  | .fppf => Scheme.fppfPrecoverage
  | .syntomic => Scheme.precoverage (@Syntomic.{u})
  | .smooth => Scheme.precoverage (@Smooth.{u})
  | .etale => Scheme.etalePrecoverage

/-- A `τ`-covering family of algebraic spaces over `S` all of whose members and whose target are
representable comes from a covering family of the representing schemes, for the precoverage on
schemes corresponding to `τ`. -/
theorem Topology.isCovering_yoneda (τ : Topology) {I : Type v}
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (f : ∀ i, U i ⟶ V)
    (hcover : τ.IsCovering B S hS
      (fun i => yoneda.obj (U i)) (fun i => yoneda.map (f i))) :
    Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj (U i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      τ.schemePrecoverage ((BigFppfOver.toScheme B S hS).obj V) := by
  cases τ with
  | fpqc => exact isFpqcCovering_yoneda_of_isCovering B S hS U V f hcover
  | fppf =>
      obtain ⟨-, -, hc⟩ := hcover
      change Presieve.ofArrows _ _ ∈ Scheme.fppfPrecoverage _
      rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨scheme_family_jointly_surjective_of_points B S hS U V f
        hc.jointly_surjective, fun i => ⟨?_, ?_⟩⟩
      · exact hc.flat i (U i) V (𝟙 (yoneda.obj (U i))) (𝟙 (yoneda.obj V)) (f i)
          (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS V) (by simp)
      · exact hc.locallyOfFinitePresentation i (U i) V (𝟙 (yoneda.obj (U i)))
          (𝟙 (yoneda.obj V)) (f i) (presheaf_etale_id B S hS (U i))
          (presheaf_etale_id B S hS V) (by simp)
  | syntomic =>
      obtain ⟨-, -, hc⟩ := hcover
      refine (Scheme.ofArrows_mem_precoverage_iff (@Syntomic.{u})).2
        ⟨scheme_family_jointly_surjective_of_points B S hS U V f
          hc.jointly_surjective, fun i => ?_⟩
      exact hc.syntomic i (U i) V (𝟙 (yoneda.obj (U i))) (𝟙 (yoneda.obj V)) (f i)
        (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS V) (by simp)
  | smooth =>
      obtain ⟨-, -, hc⟩ := hcover
      refine (Scheme.ofArrows_mem_precoverage_iff (@Smooth.{u})).2
        ⟨scheme_family_jointly_surjective_of_points B S hS U V f
          hc.jointly_surjective, fun i => ?_⟩
      exact hc.smooth i (U i) V (𝟙 (yoneda.obj (U i))) (𝟙 (yoneda.obj V)) (f i)
        (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS V) (by simp)
  | etale =>
      obtain ⟨-, -, hc⟩ := hcover
      refine (Scheme.ofArrows_mem_precoverage_iff (@Etale.{u})).2
        ⟨scheme_family_jointly_surjective_of_points B S hS U V f
          hc.jointly_surjective, fun i => ?_⟩
      refine (presheaf_yoneda_map_etale_iff B S hS (f i)).1 ?_
      simpa using hc.etale i (U i) (𝟙 (yoneda.obj (U i))) (presheaf_etale_id B S hS (U i))

end AlgebraicGeometry.Space

end
