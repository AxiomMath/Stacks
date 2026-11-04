module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent

/-!
# Quasi-coherent sub- and quotient modules of a coherent module

On a locally Noetherian scheme, a quasi-coherent submodule of a coherent module is coherent, and
so is a quasi-coherent quotient. A submodule is represented by a monomorphism into the coherent
module and a quotient by an epimorphism out of it, so neither statement depends on a choice of
representative.

Both reduce to the characterisation of coherence on a locally Noetherian scheme. For a quotient,
the generating sections of the source push forward along the epimorphism, so the quotient is of
finite type and condition (2) of that characterisation holds. For a submodule the argument is the
Noetherian one: on an affine open `U`, the sections of the coherent module form a finite module
over the Noetherian ring `Γ(X, U)`, the sections of the submodule inject into them, and a
submodule of a finite module over a Noetherian ring is finite, which is condition (4).

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.finite_specModule`: for a quasi-coherent module of
  finite type, the `Γ(X, U)`-module attached to an affine open `U` is finite.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_epi_of_isQuasicoherent`: a quasi-coherent
  quotient of a coherent module is coherent.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent`: a quasi-coherent
  submodule of a coherent module is coherent.

## References

* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

variable {X : Scheme.{u}}

/-- **For a quasi-coherent module of finite type the sections over an affine open form a finite
module.** The restriction to `Spec Γ(X, U)` is of finite type and isomorphic to the sheaf
associated with its global sections, so those global sections are finitely generated. -/
alias finite_specModule := Stacks.AlgebraicGeometry.CoherentFinite.finite_specModule

/-- **Stacks Project, Tag 01Y1.** A quasi-coherent quotient of a coherent module on a locally
Noetherian scheme is coherent. -/
@[stacks 01Y1 "quasi_coherent_quotient"]
theorem isCoherent_of_epi_of_isQuasicoherent [IsLocallyNoetherian X]
    {F G : X.Modules} [F.IsCoherent] [G.IsQuasicoherent]
    (f : F ⟶ G) [Epi f] : G.IsCoherent := by
  have hFft : F.IsFiniteType := (‹F.IsCoherent›).isFiniteType
  have hiff : (G.IsQuasicoherent ∧ G.IsFiniteType) ↔ G.IsCoherent :=
    (coherent_tfae X G).out 2 1
  exact hiff.mp
    ⟨inferInstance, @Stacks.SheafOfModules.isFiniteType_of_epi _ _ _ _ _ _ _ F G f ‹Epi f› hFft⟩

/-- Restriction along an open immersion of schemes preserves monomorphisms, because it preserves
finite limits. -/
theorem preservesMonomorphisms_restrictFunctor {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] : (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms := by
  have := preservesFiniteLimits_restrictFunctor f
  exact preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **Stacks Project, Tag 01Y1.** A quasi-coherent submodule of a coherent module on a locally
Noetherian scheme is coherent. -/
@[stacks 01Y1 "quasi_coherent_submodule"]
theorem isCoherent_of_mono_of_isQuasicoherent [IsLocallyNoetherian X]
    {F G : X.Modules} [F.IsCoherent] [G.IsQuasicoherent]
    (f : G ⟶ F) [Mono f] : G.IsCoherent := by
  refine ((coherent_tfae X G).out 1 4).mpr ?_
  intro U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨_, _⟩ := isQuasicoherent_isFiniteType_of_isCoherent F
  have : Module.Finite Γ(X, U) (specModule F hU) := finite_specModule F hU
  have : IsNoetherian Γ(X, U) (specModule F hU) :=
    isNoetherian_of_isNoetherianRing_of_finite _ (specModule F hU)
  have := preservesMonomorphisms_restrictFunctor U.ι
  have := preservesMonomorphisms_restrictFunctor hU.isoSpec.inv
  let g : specRestrict G hU ⟶ specRestrict F hU :=
    (Scheme.Modules.restrictFunctor hU.isoSpec.inv).map
      ((Scheme.Modules.restrictFunctor U.ι).map f)
  have : Mono g := inferInstance
  have : (moduleSpecΓFunctor (R := Γ(X, U))).IsRightAdjoint :=
    (tilde.adjunction (R := Γ(X, U))).isRightAdjoint
  have : (moduleSpecΓFunctor (R := Γ(X, U))).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  exact isFiniteTildeOn_of_finite_specModule G U hU
    (Module.Finite.of_injective (moduleSpecΓFunctor.map g).hom
      ((ModuleCat.mono_iff_injective (moduleSpecΓFunctor.map g)).mp inferInstance))

end Stacks.AlgebraicGeometry.CoherentTFAE

end
