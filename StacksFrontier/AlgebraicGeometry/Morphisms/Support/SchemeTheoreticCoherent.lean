module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic

/-!
# The scheme-theoretic support of a coherent module

Let `X` be a locally Noetherian scheme and let `F` be a coherent `𝒪_X`-module, that is a
quasi-coherent module of finite type. Its support is closed, and `F` is the direct image of a
*coherent* module on its scheme-theoretic support: the scheme-theoretic support is a closed
subscheme of `X`, hence again locally Noetherian, and a descent of `F` to it is quasi-coherent
of finite type.

## Main results

* `AlgebraicGeometry.Scheme.Modules.module_on_schemeTheoreticSupport_isCoherent`: every
  quasi-coherent descent of `F` to its scheme-theoretic support is coherent.
* `AlgebraicGeometry.Scheme.Modules.exists_coherent_module_on_schemeTheoreticSupport`: `F` is
  the direct image of a coherent module on its scheme-theoretic support.

Closedness of the support is `SheafOfModules.isClosed_supp`, which holds for any module of
finite type on a topological space and so needs no hypothesis here.

## Implementation notes

The hypotheses are stated as quasi-coherence together with finite type rather than as
coherence. On a locally Noetherian scheme the two are equivalent, by [Stacks, Tag 01XZ], so
nothing is lost, and this is the form in which the scheme-theoretic support is defined.

That the scheme-theoretic support is locally Noetherian is
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` applied to its closed immersion
into `X`, which is locally of finite type; this is the content of [Stacks, Tags 01T5, 01T6] in
the source.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y5](https://stacks.math.columbia.edu/tag/01Y5)
* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
-/

@[expose] public section

open CategoryTheory

universe u

add_to_stacks 01Y5 "closedness of the support" SheafOfModules.isClosed_supp

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent]
  [F.IsFiniteType]

/-- **Every quasi-coherent descent of `F` to its scheme-theoretic support is coherent.** It is
of finite type, and the scheme-theoretic support is a closed subscheme of `X`, hence locally
Noetherian. -/
theorem module_on_schemeTheoreticSupport_isCoherent
    (G : (schemeTheoreticSupport F).subscheme.Modules) [G.IsQuasicoherent]
    (e : (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj G ≅ F) :
    G.IsCoherent :=
  have : IsLocallyNoetherian (schemeTheoreticSupport F).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (schemeTheoreticSupport F).subschemeι
  have : G.IsFiniteType := module_on_schemeTheoreticSupport_isFiniteType F G e
  Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType G

/-- **[Stacks, Tag 01Y5].** A coherent module on a locally Noetherian scheme is the direct
image of a coherent module on its scheme-theoretic support. -/
@[stacks 01Y5 "descent to a coherent module on the scheme-theoretic support"]
theorem exists_coherent_module_on_schemeTheoreticSupport :
    ∃ G : (schemeTheoreticSupport F).subscheme.Modules,
      G.IsCoherent ∧
        Nonempty ((Scheme.Modules.pushforward
          (schemeTheoreticSupport F).subschemeι).obj G ≅ F) := by
  obtain ⟨G, _, -, ⟨e⟩⟩ := exists_module_on_schemeTheoreticSupport F
  exact ⟨G, module_on_schemeTheoreticSupport_isCoherent F G e, ⟨e⟩⟩

end AlgebraicGeometry.Scheme.Modules

end
