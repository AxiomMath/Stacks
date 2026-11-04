module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Universally injective ring maps

A ring map is universally injective when its underlying linear map over the source ring
remains injective after tensoring with every module. Split injections are universally
injective, and so are faithfully flat ring maps.

## Main definitions

* `Algebra.UniversallyInjective` is universal injectivity of a ring map viewed as a morphism
  of modules over its source.

## Main results

* `UniversallyInjective.of_split` treats split injections of modules.
* `Algebra.UniversallyInjective.of_split` treats split ring maps.

## Implementation notes

A ring map is represented by an `Algebra` structure, whose underlying linear map is
`Algebra.linearMap`. Universal injectivity of that linear map is the canonical notion
`UniversallyInjective`, so the ring-map predicate is defined directly in its terms. For rings,
a left inverse of the algebra map is expressed as a ring homomorphism, and the module splitting
is a linear left inverse.

## References

* [Stacks Project, Tag 08WL](https://stacks.math.columbia.edu/tag/08WL)
* [Stacks Project, Tag 08WM](https://stacks.math.columbia.edu/tag/08WM)
* [Stacks Project, Tag 08WP](https://stacks.math.columbia.edu/tag/08WP)
-/

@[expose] public section

universe u v

/-- A ring map `R → S` is universally injective as a map of `R`-modules: for every `R`-module
`Q`, the map `(Algebra.linearMap R S) ⊗ id_Q` is injective. -/
@[stacks 08WL]
def Algebra.UniversallyInjective (R : Type u) [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] : Prop :=
  _root_.UniversallyInjective (Algebra.linearMap R S)

/-- A split injection of modules is universally injective. -/
@[stacks 08WM "module maps"]
theorem UniversallyInjective.of_split
    {R : Type u} [CommRing R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : g.comp f = LinearMap.id) :
    UniversallyInjective f := by
  intro Q _ _; apply Function.Injective.of_comp (f := g.rTensor Q) (g := f.rTensor Q)
  rw [← LinearMap.coe_comp, ← LinearMap.rTensor_comp, h, LinearMap.rTensor_id]
  exact Function.injective_id

/-- A split ring map is universally injective. -/
@[stacks 08WM "ring maps"]
theorem Algebra.UniversallyInjective.of_split
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (g : S →+* R) (h : g.comp (algebraMap R S) = RingHom.id R) :
    Algebra.UniversallyInjective R S := by
  have hg (r : R) : g (algebraMap R S r) = r := by
    simpa using congrArg (fun f : R →+* R => f r) h
  refine _root_.UniversallyInjective.of_split (Algebra.linearMap R S)
    { toFun := g, map_add' := g.map_add, map_smul' := ?_ } ?_
  · intro r s; simp [Algebra.smul_def, map_mul, hg]
  · exact LinearMap.ext hg

add_to_stacks 08WP faithfullyFlat_universallyInjective
