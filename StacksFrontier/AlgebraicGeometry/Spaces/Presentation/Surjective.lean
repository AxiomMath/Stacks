module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.CategoryTheory.Presheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Surjective morphisms of algebraic spaces

For a morphism of algebraic spaces, surjectivity may mean surjectivity after every
representable base change, objectwise surjectivity of the underlying presheaf map, or local
surjectivity of the corresponding sheaf map. These are separate notions, and unless otherwise
qualified, surjectivity of a morphism of algebraic spaces means the first one.

The three are related by a descent statement: a representable morphism of sheaves on the big
fppf site of a scheme is locally surjective as soon as each of its scheme-valued base changes
is flat, locally of finite presentation and surjective.

## Main results

* `CategoryTheory.MorphismProperty.presheaf` expresses a property, here surjectivity, after
  representable base change.
* `CategoryTheory.Presheaf.isLocallySurjective_bot` identifies surjectivity of presheaves with
  objectwise surjectivity.
* `CategoryTheory.Sheaf.IsLocallySurjective` expresses surjectivity of sheaves on a covering.
* `isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective`, in the
  namespace `AlgebraicGeometry.Space`, gives local surjectivity of a representable sheaf
  morphism from the three scheme-level properties.

## Implementation notes

No new predicate is needed for the three interpretations of "surjective": they already have
distinct library declarations. For the first interpretation, specialize
`CategoryTheory.MorphismProperty.presheaf` to the inverse image of the surjective morphism
property on schemes along the functor from the big fppf site to schemes, as in
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`. The second interpretation uses the trivial
topology; the third uses the fppf topology. No implication between them is asserted.

In the descent statement the `presheaf` morphism property includes representability and
requires the three scheme-morphism properties after every represented base change. The base
change of the given section is a single-element fppf covering of the scheme underlying the
object, which the big fppf site refines by a covering of its own; a lift of the section is
then transported along that refinement.

## References

* [Stacks Project, Tag 02YN](https://stacks.math.columbia.edu/tag/02YN)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 02YN "surjectivity after representable base change, the default for \
  morphisms of algebraic spaces" CategoryTheory.MorphismProperty.presheaf
add_to_stacks 02YN "objectwise surjectivity of a map of presheaves"
  CategoryTheory.Presheaf.isLocallySurjective_bot
add_to_stacks 02YN "local surjectivity of a map of sheaves"
  CategoryTheory.Sheaf.IsLocallySurjective

/-- **Stacks Project, Tag 05VM.** A representable map of sheaves whose scheme-valued base
changes are surjective, flat, and locally of finite presentation is locally surjective for the
fppf topology. -/
@[stacks 05VM]
theorem isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (a : F ⟶ G)
    (ha : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage
        ((fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f) :
          MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a.hom) :
    Sheaf.IsLocallySurjective a := by
  classical
  show Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a.hom
  refine ⟨fun {U} s ↦ ?_⟩
  let g := yonedaEquiv.symm s
  let X := ha.rep.pullback g
  let p := ha.rep.snd g
  let q := BigFppfOver.toScheme B S hS
  have hp : Flat (q.map p) ∧ LocallyOfFinitePresentation (q.map p) ∧ Surjective (q.map p) :=
    ha.property_snd g
  let E : PreZeroHypercover.{u + 1} (B.inclusion.obj U.left) :=
    PreZeroHypercover.singleton (q.map p)
  have hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    show E.presieve₀ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
      (B.inclusion.obj U.left)
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y ↦ ?_, fun i ↦ ⟨hp.1, hp.2.1⟩⟩
    obtain ⟨x, hx⟩ := hp.2.2.surj y
    exact ⟨PUnit.unit, x, hx⟩
  obtain ⟨V, hV, ⟨ref⟩⟩ := exists_isCovering_refining_fppfCovering B U.left E hE
  have hRcov : (Sieve.overEquiv U).symm V.sieve₀ ∈ BigFppfOver.topology B S hS U := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using
      (Precoverage.generate_mem_toGrothendieck
        (show V.presieve₀ ∈ B.precoverage U.left from ⟨V, rfl, hV⟩))
  have hle : (Sieve.overEquiv U).symm V.sieve₀ ≤ Presheaf.imageSieve a.hom s := by
    rw [← (Sieve.overEquiv U).symm.apply_symm_apply (Presheaf.imageSieve a.hom s),
      (Sieve.overEquiv U).symm.map_rel_iff]
    simp only [OrderIso.symm_symm]
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    let W : BigFppfOver B S hS := Over.mk (V.f i ≫ U.hom)
    let α : W ⟶ U := Over.homMk (V.f i) (by simp [W])
    let b : W.left ⟶ X.left := B.inclusion.preimage (ref.h₀ i)
    have hbmap : B.inclusion.map b = ref.h₀ i := B.inclusion.map_preimage _
    have href0 : ref.h₀ i ≫ q.map p = B.inclusion.map (V.f i) := by
      simpa [E, q, PreZeroHypercover.singleton, PreZeroHypercover.map] using ref.w₀ i
    have hbp : b ≫ p.left = V.f i :=
      B.inclusion.map_injective (by rwa [B.inclusion.map_comp, hbmap])
    let β : W ⟶ X := Over.homMk b
      (show b ≫ X.hom = V.f i ≫ U.hom by rw [← hbp, Category.assoc, Over.w p])
    have hfactor : β ≫ p = α := by
      ext
      exact congrArg B.inclusion.map hbp
    have hsection : a.hom.app (op X) (yonedaEquiv (ha.rep.fst g)) = G.obj.map p.op s := by
      have h := congrArg yonedaEquiv (ha.rep.isPullback g).w
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map] at h
      simpa [g, p, X] using h
    have hlift : a.hom.app (op W) (F.obj.map β.op (yonedaEquiv (ha.rep.fst g))) =
        G.obj.map α.op s := by
      rw [← hfactor, op_comp, Functor.map_comp_apply, ← hsection]
      exact NatTrans.naturality_apply a.hom β.op _
    rw [Sieve.overEquiv_iff, Presheaf.imageSieve_apply]
    exact ⟨F.obj.map β.op (yonedaEquiv (ha.rep.fst g)), hlift⟩
  exact (BigFppfOver.topology B S hS).superset_covering hle hRcov

end AlgebraicGeometry.Space

end
