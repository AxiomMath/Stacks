module

public import StacksFrontier.Algebra.MittagLeffler.Basic
public import StacksFrontier.Algebra.MittagLeffler.Projective
public import StacksFrontier.Algebra.MittagLeffler.ShortExact

/-!
# A countably generated flat module universally injecting into a projective module is projective

Let `R` be a commutative ring and let `f : M → N` be a universally injective map of `R`-modules,
that is, one for which `f ⊗ id_T` is injective for every `R`-module `T`. If `N` is projective and
`M` is flat and countably generated, then `M` is projective.

This is the last step of Tag 05MD. There the base ring is the ring of sections of an affine base,
`N` is the ring of sections of an étale chart covering the relative assassin, over which
projectivity is supplied by Tag 05KW, and `M` is the module whose projectivity is wanted; the
universal injectivity is Tag 05DH.

## Main results

* `Module.isMittagLeffler_of_forall_rTensor_injective`: the Mittag-Leffler property descends along
  a universally injective map. This is item (1) of Tag 059N.
* `Module.projective_of_forall_rTensor_injective_of_countablyGenerated`: the statement above.

## Implementation notes

Tag 059N is held in this repository as
`Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective`, stated for a
universally exact sequence with the Mittag-Leffler property written out inline rather than as
`IsMittagLeffler`. Only item (1) is used, and it does not mention the third term of the sequence,
so the sequence is manufactured from `f` alone by taking the third term to be
`N ⧸ LinearMap.range f`, with `LinearMap.exact_map_mkQ_range` and `Submodule.mkQ_surjective` for
its exactness and surjectivity. `isMittagLeffler_def_iff` converts between the inline form and
`IsMittagLeffler`, which is the form Tag 059X consumes.

*Flatness of `M` is a hypothesis rather than a consequence.* It does descend along a universally
injective map into a flat module, by the first conclusion of Tag 058P, but every consumer of these
statements already has flatness of `M` in hand — in Tag 05MD it is the flatness of the module over
the base, which that tag assumes — so carrying it is free and importing the descent is not.

The universe convention is that of Tags 058K, 059E, 059N and 059Z: `R : Type u` and the modules in
`Type v`, with the test data in the universe of the modules, whence the `Small.{v} R` side
condition inherited from Tags 059R and 059X.
-/

@[expose] public section

universe u v

namespace Module

/-- **The Mittag-Leffler property descends along a universally injective map.** If
`f : M →ₗ[R] N` is such that `f ⊗ id_T` is injective for every `R`-module `T`, and `N` is
Mittag-Leffler, then `M` is Mittag-Leffler.

This is item (1) of Tag 059N, whose universally exact sequence is taken to be
`0 → M → N → N ⧸ f(M) → 0`; that item does not mention the third term. -/
theorem isMittagLeffler_of_forall_rTensor_injective (R : Type u) [CommRing R] [Small.{v} R]
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : ∀ (T : Type v) [AddCommGroup T] [Module R T], Function.Injective (f.rTensor T))
    (hN : IsMittagLeffler.{u, v, v, v, v} R N) :
    IsMittagLeffler.{u, v, v, v, v} R M :=
  (isMittagLeffler_def_iff R M).2
    ((Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective
      (M₃ := N ⧸ LinearMap.range f) (LinearMap.exact_map_mkQ_range f)
      (Submodule.mkQ_surjective _) hf).1 fun P _ _ _ g =>
        (isMittagLeffler_def_iff R N).1 hN P g)

/-- **A countably generated flat module universally injecting into a projective module is
projective.** Let `f : M →ₗ[R] N` be such that `f ⊗ id_T` is injective for every `R`-module `T`,
with `N` projective. If `M` is flat and countably generated, then `M` is projective.

A projective module is Mittag-Leffler by Tag 059R, the property descends to `M` along `f` by
Tag 059N, and a flat, Mittag-Leffler, countably generated module is projective by Tag 059X. -/
theorem projective_of_forall_rTensor_injective_of_countablyGenerated (R : Type u) [CommRing R]
    [Small.{v} R] (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Projective R N] (f : M →ₗ[R] N)
    (hf : ∀ (T : Type v) [AddCommGroup T] [Module R T], Function.Injective (f.rTensor T))
    (hcg : Module.CountablyGenerated R M) :
    Module.Projective R M :=
  Module.Flat.projective_of_isMittagLeffler_of_countablyGenerated R M
    (isMittagLeffler_of_forall_rTensor_injective R M N f hf
      ((isMittagLeffler_def_iff R N).2 fun P _ _ _ g =>
        Module.mittagLeffler_of_projective R N P g))
    hcg

end Module

end
