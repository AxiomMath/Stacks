module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Flat separated morphisms with distinct generic points are universally injective

A flat separated morphism of schemes whose residue-field maps at the generic points of its
source are isomorphisms, and which is injective on those generic points, is universally
injective.

## Main results

* `AlgebraicGeometry.universallyInjective_of_flat_of_separated_of_genericPoints_injOn` is the
  criterion.

## Implementation notes

The equality of residue fields in the source is expressed by the canonical residue-field map
being an isomorphism. The condition on distinct generic points is expressed by injectivity on
Mathlib's `genericPoints` set.

Universal injectivity is checked on the diagonal: the diagonal of a separated morphism is a
closed embedding, so its range is closed, and flatness makes both projections generalizing, so
every generic point of the fibre product comes from a generic point of the source. The
hypotheses force that point to be the diagonal image, and the range, being closed and containing
every generic point, is everything.

## References

* [Stacks Project, Tag 09NP](https://stacks.math.columbia.edu/tag/09NP)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A generalizing map between quasi-sober `T₀` spaces sends generic points to generic points. -/
public lemma genericPoints_map_of_generalizingMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space X] [T0Space Y]
    [QuasiSober X] [QuasiSober Y] (g : X → Y) (hg : GeneralizingMap g)
    {x : X} (hx : x ∈ genericPoints X) : g x ∈ genericPoints Y := by
  refine (mem_genericPoints_iff_forall_specializes_eq (g x)).2 fun y hy => ?_
  obtain ⟨x', hx', rfl⟩ := hg hy
  rw [(mem_genericPoints_iff_forall_specializes_eq x).1 hx x' hx']

/-- **Stacks Project, Tag 09NP.** A flat separated morphism with isomorphic residue fields
at, and distinct images of, the generic points of its source is universally injective. -/
@[stacks 09NP]
public theorem universallyInjective_of_flat_of_separated_of_genericPoints_injOn
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsSeparated f]
    (hres : ∀ ξ ∈ genericPoints X, IsIso (f.residueFieldMap ξ))
    (hinj : Set.InjOn f (genericPoints X)) :
    UniversallyInjective f := open CategoryTheory.Limits in by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  let P : Scheme := pullback f f
  let d : X ⟶ P := pullback.diagonal f
  have hclosed : IsClosed (Set.range d.base) := d.isClosedEmbedding.isClosed_range
  have hgeneric : genericPoints P ⊆ Set.range d.base := by
    intro η hη
    let x : X := pullback.fst f f η
    let y : X := pullback.snd f f η
    have hx : x ∈ genericPoints X :=
      genericPoints_map_of_generalizingMap (pullback.fst f f)
        (Flat.generalizingMap (pullback.fst f f)) hη
    have hy : y ∈ genericPoints X :=
      genericPoints_map_of_generalizingMap (pullback.snd f f)
        (Flat.generalizingMap (pullback.snd f f)) hη
    have hxy' : x = y := hinj hx hy
      (congrArg (fun q : P ⟶ Y => q η) pullback.condition)
    let Tη : Scheme.Pullback.Triplet f f :=
      Scheme.Pullback.Triplet.ofPoint η
    have : IsIso (f.residueFieldMap Tη.y) := hres y hy
    have : IsIso ((Y.residueFieldCongr Tη.hy).inv ≫ f.residueFieldMap Tη.y) :=
      inferInstance
    have : IsIso Tη.tensorInl := by
      change IsIso (pushout.inl _ _)
      exact (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
    have : IsIso (Spec.map Tη.tensorInl) :=
      (isIso_SpecMap_iff).2 (ConcreteCategory.bijective_of_isIso Tη.tensorInl)
    have hSpecSub : Subsingleton (Spec Tη.tensor) := ⟨fun p q =>
      (Spec.map Tη.tensorInl).homeomorph.injective (Subsingleton.elim _ _)⟩
    let cη := Scheme.Pullback.carrierEquiv (f := f) (g := f) η
    let cd := Scheme.Pullback.carrierEquiv (f := f) (g := f) (pullback.diagonal f x)
    have hfirst : cη.1 = cd.1 := by
      apply Scheme.Pullback.Triplet.ext
      · change (pullback.fst f f η) = pullback.fst f f (pullback.diagonal f x)
        rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
        rfl
      · change (pullback.snd f f η) = pullback.snd f f (pullback.diagonal f x)
        rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
        change y = x
        exact hxy'.symm
    have hcar : cη = cd := Scheme.Pullback.carrierEquiv_eq_iff.mpr
      ⟨hfirst, (hfirst ▸ hSpecSub : Subsingleton (Spec cd.1.tensor)).elim _ _⟩
    exact ⟨x, ((Scheme.Pullback.carrierEquiv (f := f) (g := f)).injective hcar).symm⟩
  have hrange : Set.range d.base = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    simpa [genericPoints.closure, hclosed.closure_eq] using closure_mono hgeneric
  exact Set.range_eq_univ.mp (by simpa [d, P] using hrange)

end AlgebraicGeometry
