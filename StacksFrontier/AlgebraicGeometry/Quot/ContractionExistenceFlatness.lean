module

public import StacksFrontier.AlgebraicGeometry.Algebraization
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.FlatnessKernelPowers
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.FlatLocusOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyConstant

/-!
# Flatness and fibre dimension over a local base, read on the closed fibre

Two facts about a scheme `X` over the spectrum of a local ring `R` whose structure morphism is
universally closed, each saying that a condition checked over the closed point holds everywhere.

* If `R` is Noetherian, `X ⟶ Spec R` is locally of finite type and its base changes to all the
  thickenings `Spec (R ⧸ 𝔪 ^ (n + 1))` are flat, then it is flat. Over the closed point this is
  [Stacks, Tag 0D4G]; the flat locus is open ([Stacks, Tag 0399]) and its complement is closed,
  so its image in `Spec R` is closed and would contain the closed point.
* If `X ⟶ Spec R` is proper, flat and of finite presentation, the fibre dimension is locally
  constant on `Spec R` ([Stacks, Tag 0D4J]); every point of `Spec R` specializes to the closed
  point, so a bound on the dimension of the closed fibre bounds every fibre.

## Main results

* `AlgebraicGeometry.flat_of_flat_pullback_adicThickeningι_maximalIdeal`: the first statement.
* `AlgebraicGeometry.fiberDimension_le_of_fiberDimension_closedPoint_le`: the second statement.

## References

* [Stacks Project, Tag 0D4G](https://stacks.math.columbia.edu/tag/0D4G)
* [Stacks Project, Tag 0D4J](https://stacks.math.columbia.edu/tag/0D4J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Over a local base, an open set of a universally closed scheme containing the closed fibre is
everything: its complement is closed, hence has closed image, which would contain the closed
point as soon as it is nonempty. -/
theorem forall_of_isOpen_of_forall_eq_closedPoint {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f] (P : X → Prop)
    (hP : IsOpen {x | P x}) (hfiber : ∀ x, f x = closedPoint R → P x) (x : X) : P x := by
  by_contra hx
  have hC := f.isClosedMap _ hP.isClosed_compl
  obtain ⟨y, hy, hfy⟩ : closedPoint R ∈ f '' {x | P x}ᶜ :=
    (specializes_closedPoint (f x)).mem_closed hC ⟨x, hx, rfl⟩
  exact hy (hfiber y hfy)

/-- **Flatness over a Noetherian local ring from flatness over its thickenings.** A universally
closed morphism `f : X ⟶ Spec R`, locally of finite type, to the spectrum of a Noetherian local
ring is flat as soon as its base change to every thickening `Spec (R ⧸ 𝔪 ^ (n + 1))` of the
closed point is flat. -/
theorem flat_of_flat_pullback_adicThickeningι_maximalIdeal {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [UniversallyClosed f] [LocallyOfFiniteType f]
    (hf : ∀ n, Flat (pullback.snd f (adicThickeningι R (maximalIdeal R) n))) : Flat f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [Flat.iff_flat_stalkMap]
  refine forall_of_isOpen_of_forall_eq_closedPoint f
    (fun x => (f.stalkMap x).hom.Flat) ?_ ?_
  · exact isOpen_setOf_isFlatAt_of_isLocallyNoetherian f
  · intro x hx
    refine flat_stalkMap_of_flat_pullbacks_spec_quotient_pow (maximalIdeal R) f hf x ?_
    rw [hx]
    exact le_rfl

/-- **The fibre dimension over a local base is that of the closed fibre.** For a proper, flat
morphism of finite presentation `f : X ⟶ Spec R` to the spectrum of a local ring, a bound on the
dimension of the closed fibre bounds the dimension of every fibre. -/
theorem fiberDimension_le_of_fiberDimension_closedPoint_le {R : Type u} [CommRing R]
    [IsLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    (hfp : FinitePresentation f) {d : WithBot ℕ∞}
    (hd : f.fiberDimension (closedPoint R) ≤ d) (y : Spec (.of R)) :
    f.fiberDimension y ≤ d := by
  have heq : f.fiberDimension y = f.fiberDimension (closedPoint R) :=
    (specializes_closedPoint y).mem_open
      ((isLocallyConstant_fiberDimension f hfp).isOpen_fiber
        (f.fiberDimension (closedPoint R))) rfl
  exact heq ▸ hd

end AlgebraicGeometry

end
