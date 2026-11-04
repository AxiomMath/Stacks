module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmoothEqualsEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.SmoothAndStandardEtaleCoverings
import StacksCore.Tactic.StacksAttribute

/-!
# Basic properties of smooth coverings

A smooth covering of a scheme `T` is a family of smooth morphisms `Tᵢ ⟶ T` whose images cover
`T`. Since étale morphisms and open immersions are smooth, every étale covering, and a fortiori
every Zariski covering, is a smooth covering. The smooth coverings moreover satisfy the axioms
of a site: the singleton family of an isomorphism is a smooth covering, a smooth covering of
each member of a smooth covering composes to a smooth covering, and the base change of a smooth
covering along any morphism of schemes is a smooth covering.

## Main results

* Tag 0220 for étale coverings is recorded on the existing
  `AlgebraicGeometry.Scheme.etalePrecoverage_le_smoothPrecoverage`.
* `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_smoothPrecoverage`: every Zariski covering is
  a smooth covering.
* `AlgebraicGeometry.Scheme.singleton_mem_smoothPrecoverage_of_isIso`: the singleton family of
  an isomorphism is a smooth covering.
* `AlgebraicGeometry.Scheme.ofArrows_comp_mem_smoothPrecoverage`: smooth coverings compose.
* `AlgebraicGeometry.Scheme.ofArrows_pullback_mem_smoothPrecoverage`: smooth coverings pull
  back along arbitrary morphisms of schemes.

## Implementation notes

Coverings are recorded as presieves: the indexed family `{fᵢ : Tᵢ ⟶ T}` is a smooth covering
when `Presieve.ofArrows _ f` lies in `AlgebraicGeometry.Scheme.smoothPrecoverage`, and by
`AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff` this says exactly that every `fᵢ` is
smooth and that the images of the `fᵢ` cover `T`. The index types are allowed to live in
arbitrary universes.

## References

* [Stacks Project, Tag 0220](https://stacks.math.columbia.edu/tag/0220)
* [Stacks Project, Tag 0221](https://stacks.math.columbia.edu/tag/0221)
-/

@[expose] public section

open CategoryTheory Limits

universe u w w'

namespace AlgebraicGeometry

namespace Scheme

/-- Every Zariski covering is a smooth covering. -/
@[stacks 0220 "Zariski coverings"]
public theorem zariskiPrecoverage_le_smoothPrecoverage :
    zariskiPrecoverage.{u} ≤ smoothPrecoverage :=
  precoverage_mono fun _ _ _ _ ↦ inferInstance

/-- The singleton family of an isomorphism `T' ⟶ T` is a smooth covering of `T`. -/
@[stacks 0221 "part (1)"]
public theorem singleton_mem_smoothPrecoverage_of_isIso {T' T : Scheme.{u}} (f : T' ⟶ T)
    [IsIso f] : Presieve.singleton f ∈ smoothPrecoverage T :=
  (singleton_mem_precoverage_iff @Smooth f).2 ⟨f.homeomorph.surjective, inferInstance⟩

/-- Smooth coverings contain the singleton families of isomorphisms. -/
public instance : smoothPrecoverage.{u}.HasIsos where
  mem_coverings_of_isIso f _ := singleton_mem_smoothPrecoverage_of_isIso f

/-- If `{fᵢ : Tᵢ ⟶ T}` is a smooth covering and `{gᵢⱼ : Tᵢⱼ ⟶ Tᵢ}` is a smooth covering of each
`Tᵢ`, then the composite family `{gᵢⱼ ≫ fᵢ : Tᵢⱼ ⟶ T}` is a smooth covering. -/
@[stacks 0221 "part (2)"]
public theorem ofArrows_comp_mem_smoothPrecoverage {I : Type w} {T : Scheme.{u}}
    {T' : I → Scheme.{u}} (f : ∀ i, T' i ⟶ T)
    (hf : Presieve.ofArrows T' f ∈ smoothPrecoverage T) {J : I → Type w'}
    {T'' : ∀ i, J i → Scheme.{u}} (g : ∀ i j, T'' i j ⟶ T' i)
    (hg : ∀ i, Presieve.ofArrows (T'' i) (g i) ∈ smoothPrecoverage (T' i)) :
    Presieve.ofArrows (fun p : Σ i, J i ↦ T'' p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) ∈
      smoothPrecoverage T :=
  Precoverage.comp_mem_coverings f hf g hg

/-- If `{fᵢ : Tᵢ ⟶ T}` is a smooth covering and `g : T' ⟶ T` is a morphism of schemes, then the
family of first projections `{T' ×_T Tᵢ ⟶ T'}` is a smooth covering. -/
@[stacks 0221 "part (3)"]
public theorem ofArrows_pullback_mem_smoothPrecoverage {I : Type w} {T T' : Scheme.{u}}
    {Tᵢ : I → Scheme.{u}} (f : ∀ i, Tᵢ i ⟶ T)
    (hf : Presieve.ofArrows Tᵢ f ∈ smoothPrecoverage T) (g : T' ⟶ T) :
    Presieve.ofArrows (fun i ↦ pullback g (f i)) (fun i ↦ pullback.fst g (f i)) ∈
      smoothPrecoverage T' :=
  Precoverage.mem_coverings_of_isPullback f hf g _ (fun i ↦ pullback.snd g (f i))
    fun i ↦ IsPullback.of_hasPullback g (f i)

end Scheme

/-! The étale part of Tag 0220 is the existing
`AlgebraicGeometry.Scheme.etalePrecoverage_le_smoothPrecoverage` (its right-hand side
`precoverage @Smooth` is `smoothPrecoverage` by definition). -/
add_to_stacks 0220 "étale coverings" AlgebraicGeometry.Scheme.etalePrecoverage_le_smoothPrecoverage

end AlgebraicGeometry
