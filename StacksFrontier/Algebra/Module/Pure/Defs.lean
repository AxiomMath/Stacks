module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Pure injective and pure projective modules

A module is *pure injective* when `Hom(-, I)` carries universally exact short exact sequences to
short exact sequences, and *pure projective* when `Hom(P, -)` does.

## References

* [Stacks Project, Tag 06ZY](https://stacks.math.columbia.edu/tag/06ZY)
-/

@[expose] public section

namespace Module

section

universe u v

/-- An `A`-module `I` is *pure injective* if applying `Hom_A(-, I)` to every
universally exact short exact sequence of `A`-modules gives a short exact
sequence. -/
@[stacks 06ZY "pure_injective"]
public abbrev PureInjective (A : Type u) [CommRing A] (I : Type v)
    [AddCommGroup I] [Module A I] : Prop :=
  ∀ (K M N : Type v) [AddCommGroup K] [Module A K]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N),
    Function.Injective f → Function.Surjective g →
      LinearMap.range f = LinearMap.ker g → UniversallyInjective f →
        Function.Injective (LinearMap.lcomp A I g) ∧
          Function.Surjective (LinearMap.lcomp A I f) ∧
            LinearMap.range (LinearMap.lcomp A I g) =
              LinearMap.ker (LinearMap.lcomp A I f)

end

section

universe u v

/-- An `A`-module `P` is *pure projective* if applying `Hom_A(P, -)` to every
universally exact short exact sequence of `A`-modules gives a short exact
sequence. -/
@[stacks 06ZY "pure_projective"]
public abbrev PureProjective (A : Type u) [CommRing A] (P : Type v)
    [AddCommGroup P] [Module A P] : Prop :=
  ∀ (K M N : Type (max u v)) [AddCommGroup K] [Module A K]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N),
    Function.Injective f → Function.Surjective g →
      LinearMap.range f = LinearMap.ker g → UniversallyInjective f →
        Function.Injective (LinearMap.compRight (M := P) A f) ∧
          Function.Surjective (LinearMap.compRight (M := P) A g) ∧
            LinearMap.range (LinearMap.compRight (M := P) A f) =
              LinearMap.ker (LinearMap.compRight (M := P) A g)

end

end Module

end
