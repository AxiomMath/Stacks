module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldMono

/-!
# The two denominator short exact sequences for the structure sheaf

Let `X` be a scheme, `s` a meromorphic section of `𝒪_X` and `I` the ideal of denominators of
`s`. The two canonical morphisms `I ⟶ 𝒪_X` — the inclusion and multiplication by `s` — are
monomorphisms, so each sits in a short exact sequence

`0 → I → 𝒪_X → 𝒪_X/I → 0`  and  `0 → I →^{s} 𝒪_X → 𝒪_X/sI → 0`.

These are the two sequences of Stacks 02SW part (1) in the case `L = 𝒪_X` that the proof of
Stacks 0FDS uses. They share their first term `I` and their second term `𝒪_X`, which is what
makes the two quotients have the same class in the wide dimension layer, by
`Stacks.Chow.coherentDimensionKZeroMk_eq_of_shortExact` with both comparison isomorphisms the
identity.

## Main results

* `AlgebraicGeometry.Scheme.Modules.epi_cokernelπ_sheafOfModules` — the projection to a cokernel
  is an epimorphism in the `SheafOfModules` reading of the category of modules on a scheme.
* `AlgebraicGeometry.Scheme.Modules.shortExact_cokernel` — a monomorphism of modules on a scheme
  sits in a short exact sequence with its cokernel.
* `AlgebraicGeometry.shortExact_denominatorIdealι` and
  `AlgebraicGeometry.shortExact_denominatorIdealMul` — the two sequences above.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a definition over `CategoryTheory.SheafOfModules` whose
categorical instances are *copies*, so a property proved in one reading is invisible to instance
search in the other. The cokernel itself is not affected: `cokernel f` taken in
`AlgebraicGeometry.Scheme.Modules` and taken in `CategoryTheory.SheafOfModules` over the
structure sheaf are the same term, by `rfl`. What does not transfer is the `Epi` instance on the
projection — `CategoryTheory.Limits.cokernel.π f` is an epimorphism by an instance available only
in the first reading, and `AlgebraicGeometry.Scheme.Modules.epi_sheafOfModules` must be applied
by hand to move it.

That transport is stated here over abstract data: a morphism `f : A ⟶ B` of modules on a scheme,
with no denominator-ideal term in sight. Applied to a concrete morphism inside a structure
instance the instance argument is searched before the goal is unified with
`cokernel.π f`, and the search fails on the large term; as a standalone lemma the instance is
discharged once, at a variable, and the concrete case is an application. The same shape — state
the step over abstract data, instantiate once — is what dissolves the `CommRingCat`/`RingCat`
stalk diamond and what the abstract-ring length computation uses.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample (unitModule)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The projection to a cokernel is an epimorphism, in the `SheafOfModules` reading.** The
categorical instances on `AlgebraicGeometry.Scheme.Modules` are copies of those on
`CategoryTheory.SheafOfModules`, so the epimorphism has to be transported by hand; the cokernel
itself is the same term in both readings. -/
theorem epi_cokernelπ_sheafOfModules {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B) :
    @Epi (SheafOfModules.{u} X.ringCatSheaf) (inferInstance) _ _ (cokernel.π f) :=
  @epi_sheafOfModules X _ _ (cokernel.π f) inferInstance

/-- **A monomorphism of modules on a scheme sits in a short exact sequence with its cokernel.**
Exactness is the universal property of the cokernel, and the projection is an epimorphism. -/
theorem shortExact_cokernel {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (hf : @Mono (SheafOfModules.{u} X.ringCatSheaf) (inferInstance) _ _ f) :
    (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) f (cokernel.π f)
      (cokernel.condition _)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := hf
  epi_g := epi_cokernelπ_sheafOfModules f

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- **Stacks 02SW part (1) for `L = 𝒪_X`, first sequence.** The ideal of denominators of a
meromorphic section of `𝒪_X` includes into `𝒪_X` with cokernel `𝒪_X/I`. -/
theorem shortExact_denominatorIdealι (s : MeromorphicSection X.sheaf (unitModule X)) :
    (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf)
      (denominatorIdealι X (unitModule X) s)
      (cokernel.π (denominatorIdealι X (unitModule X) s))
      (cokernel.condition _)).ShortExact :=
  Scheme.Modules.shortExact_cokernel _ (mono_denominatorIdealι_unitModule X s)

/-- **Stacks 02SW part (1) for `L = 𝒪_X`, second sequence.** Multiplication by a regular
meromorphic section embeds its ideal of denominators in `𝒪_X`, with cokernel `𝒪_X/sI`. -/
theorem shortExact_denominatorIdealMul [IsIntegral X]
    (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) :
    (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf)
      (denominatorIdealMul X (unitModule X) s)
      (cokernel.π (denominatorIdealMul X (unitModule X) s))
      (cokernel.condition _)).ShortExact :=
  Scheme.Modules.shortExact_cokernel _
    (denominatorIdeal_section_mono X (unitModule X) s (isInvertible_unitModule X) hs)

end AlgebraicGeometry
