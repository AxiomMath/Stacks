module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic

/-!
# The canonical descent datum functor is fully faithful

For a morphism of schemes `f : X ⟶ S` which is an fpqc covering, the functor sending a scheme
over `S` to its canonical descent datum relative to `f` is fully faithful. Equivalently, a
morphism of the canonical descent data of two `S`-schemes comes from a unique morphism of
`S`-schemes.

## Main definitions

* `AlgebraicGeometry.DescentData.trivialFunctorFullyFaithful`: the trivial-descent-datum functor
  `Over S ⥤ DescentData (fun _ : Unit ↦ 𝟙 S)` is fully faithful.

## Main results

* `AlgebraicGeometry.DescentData.canonicalFunctor_fullyFaithful`: the canonical-descent-datum
  functor is fully faithful whenever the morphism is a one-element fpqc covering.
* `AlgebraicGeometry.DescentData.canonicalFunctor_fullyFaithful_of_flat`: the same for a
  surjective, quasi-compact and flat morphism.
* `AlgebraicGeometry.DescentData.canonicalFunctor_fullyFaithful_of_isFiniteLocallyFree`: the same
  for a surjective finite locally free morphism.
* `AlgebraicGeometry.DescentData.existsUnique_hom_of_canonicalFunctor_map`: the same full
  faithfulness spelled out as unique descent of a morphism — a morphism between the canonical
  descent data of two `S`-schemes is the canonical datum of exactly one morphism of
  `S`-schemes.

## References

* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 040L](https://stacks.math.columbia.edu/tag/040L)
* [Stacks Project, Tag 0241](https://stacks.math.columbia.edu/tag/0241)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

/-- The trivial-descent-datum functor is fully faithful: a morphism of trivial descent data is
the single morphism of `S`-schemes it carries at the sole index. -/
def trivialFunctorFullyFaithful (S : Scheme.{u}) : (trivialFunctor S).FullyFaithful where
  preimage φ := φ.hom ()
  map_preimage φ := by ext i; rfl
  preimage_map g := rfl

/-- The trivial-descent-datum functor is full. -/
instance (S : Scheme.{u}) : (trivialFunctor S).Full :=
  (trivialFunctorFullyFaithful S).full

/-- The trivial-descent-datum functor is faithful. -/
instance (S : Scheme.{u}) : (trivialFunctor S).Faithful :=
  (trivialFunctorFullyFaithful S).faithful

/-- If `f : X ⟶ S` is a one-element fpqc covering of `S`, then the functor sending a scheme over
`S` to its canonical descent datum relative to `f` is fully faithful. -/
theorem canonicalFunctor_fullyFaithful {S X : Scheme.{u}} (f : X ⟶ S)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S) :
    Nonempty ((canonicalFunctor f).FullyFaithful) :=
  (pullbackFunctor_fullyFaithful_of_fpqc (pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)) hcover).map
    (trivialFunctorFullyFaithful S).comp

/-- If `f : X ⟶ S` is surjective, quasi-compact and flat, then the canonical-descent-datum
functor relative to `f` is fully faithful. -/
theorem canonicalFunctor_fullyFaithful_of_flat {S X : Scheme.{u}} (f : X ⟶ S)
    [Surjective f] [QuasiCompact f] [Flat f] :
    Nonempty ((canonicalFunctor f).FullyFaithful) :=
  canonicalFunctor_fullyFaithful f f.singleton_mem_fpqcPrecoverage

/-- If `f : X ⟶ S` is surjective and finite locally free, then the canonical-descent-datum
functor relative to `f` is fully faithful. -/
theorem canonicalFunctor_fullyFaithful_of_isFiniteLocallyFree {S X : Scheme.{u}} (f : X ⟶ S)
    [Surjective f] [Stacks.Morphisms.IsFiniteLocallyFree f] :
    Nonempty ((canonicalFunctor f).FullyFaithful) :=
  have : IsFinite f := Stacks.Morphisms.IsFiniteLocallyFree.isFinite f
  have : Flat f := Stacks.Morphisms.IsFiniteLocallyFree.flat f
  canonicalFunctor_fullyFaithful_of_flat f

/-- **Fpqc descent for morphisms of schemes along a one-element covering.** Let `f : X ⟶ S` be a
one-element fpqc covering of `S` and let `W` and `W'` be schemes over `S`. A morphism
`W ×_S X ⟶ W' ×_S X` over `X` which is compatible with the canonical descent data of `W` and `W'`
relative to `f` is the base change of exactly one morphism `W ⟶ W'` over `S`. -/
@[sga "1 VIII 5.2"]
theorem existsUnique_hom_of_canonicalFunctor_map {S X : Scheme.{u}} (f : X ⟶ S)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S) {W W' : Over S}
    (ψ₀ : (canonicalFunctor f).obj W ⟶ (canonicalFunctor f).obj W') :
    ∃! ψ : W ⟶ W', (canonicalFunctor f).map ψ = ψ₀ := by
  obtain ⟨hC⟩ := canonicalFunctor_fullyFaithful f hcover
  exact ⟨hC.preimage ψ₀, hC.map_preimage ψ₀, fun ψ hψ ↦ by rw [← hψ, hC.preimage_map]⟩

end AlgebraicGeometry.DescentData

end

end
