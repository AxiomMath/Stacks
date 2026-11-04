module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange

/-!
# The kernel sequence of an invertible quotient is short exact under every pullback

Let `q : ℳ ⟶ ℒ` be an epimorphism of modules on a scheme onto an invertible one. Its kernel
sequence

  `0 ⟶ ker q ⟶ ℳ ⟶ ℒ ⟶ 0`

stays short exact after pullback along **any** morphism of schemes, with no flatness hypothesis
on the morphism. This is the field `shortExact_pullback` of
`Stacks.Divisors.BundleSplittingDatum`, whose instance at the tautological sequence of a
projective bundle is what Tag 0AYP asks for.

## Main results

* `Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_kernelSequence`: the kernel sequence
  of an invertible quotient is short exact after an arbitrary pullback.
* `Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible`: the same read
  off an epimorphism onto an invertible module, which is the form the splitting datum consumes.

## Implementation notes

**No flatness of the morphism is needed, and none is available.** The pullback of sheaves of
modules is a left adjoint, so it preserves the cokernel half of the sequence for free; the
content is that it keeps the kernel inclusion a monomorphism. That is
`Stacks.Divisors.mono_pullback_map_kernel_ι`, which holds because the quotient is invertible:
at every stalk the surjection lands on an invertible, hence projective, module and therefore
splits, and a module pullback keeps the kernel inclusion of a stalkwise-split surjection
injective. Tag 02N4's exactness of flat pullback plays no part.

**Epimorphy of the quotient is not avoidable.** Taking the pullback along the identity returns
the sequence itself, so a short exact pullback in every degree forces the quotient map to be an
epimorphism to begin with; it is therefore a hypothesis here rather than a conclusion.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundleSplitting

open Stacks.Divisors

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **The kernel sequence of an invertible quotient stays short exact under every pullback.**
The pulled-back sequence is still a cokernel presentation, because the pullback of modules is a
left adjoint and so preserves the colimit; and its first map is still a monomorphism by
`Stacks.Divisors.mono_pullback_map_kernel_ι`, which reads the invertibility of the quotient at
the stalks. -/
theorem shortExact_map_pullback_kernelSequence (E : X.Modules) (Q : InvertibleQuotient X E) :
    ((ShortComplex.mk (kernel.ι Q.q) Q.q (kernel.condition Q.q)).map
      (Scheme.Modules.pullback g)).ShortExact := by
  have hq : Epi Q.q := Q.epi
  set S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι Q.q) Q.q (kernel.condition Q.q) with hSdef
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel Q.q }
  have hc : IsColimit (CokernelCofork.ofπ (S.map (Scheme.Modules.pullback g)).g
      (S.map (Scheme.Modules.pullback g)).zero) :=
    CokernelCofork.mapIsColimit _ hS.gIsCokernel (Scheme.Modules.pullback g)
  have hm : Mono (S.map (Scheme.Modules.pullback g)).f :=
    mono_pullback_map_kernel_ι g E Q
  exact ShortComplex.ShortExact.mk'
    ((S.map (Scheme.Modules.pullback g)).exact_of_g_is_cokernel hc) hm
    (Limits.epi_of_isColimit_cofork hc)

/-- **The same, read off an epimorphism onto an invertible module.** This is the shape the field
`shortExact_pullback` of `Stacks.Divisors.BundleSplittingDatum` is stated in: the sub-object is
the categorical kernel and the two maps compose to zero by the kernel condition. -/
theorem shortExact_map_pullback_of_epi_isInvertible {E L : X.Modules} (q : E ⟶ L) (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    ((ShortComplex.mk (kernel.ι q) q (kernel.condition q)).map
      (Scheme.Modules.pullback g)).ShortExact :=
  shortExact_map_pullback_kernelSequence g E ⟨L, hL, q, hq⟩

end Stacks.ProjectiveBundleSplitting

end
