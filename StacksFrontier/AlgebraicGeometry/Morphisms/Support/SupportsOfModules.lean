module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Specialization

/-!
# Supports of quasi-coherent modules

For a quasi-coherent module on a scheme the support of the sheaf and the supports of its
modules of sections over the affine opens are the same subset of the scheme: the support of the
sheaf pulls back, along the inclusion of an affine open, to the support of the module of
sections there.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fromSpec_preimage_supp`: the inverse image of the support of
  a quasi-coherent module under the inclusion of an affine open `Spec A` is the support of the
  `A`-module of sections over that open.

## References

* [Stacks Project, Tag 056H](https://stacks.math.columbia.edu/tag/056H)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The sheaf-theoretic and module-theoretic supports agree.** The inverse image of the
support of a quasi-coherent module `F` under the inclusion `Spec Γ(X, U) → X` of an affine open
`U` is the support of the `Γ(X, U)`-module `Γ(F, U)`. -/
@[stacks 056H "the sheaf-theoretic and module-theoretic supports agree"]
public theorem fromSpec_preimage_supp {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (U : X.affineOpens) :
    ⇑U.2.fromSpec ⁻¹' SheafOfModules.supp F = Module.support Γ(X, U.1) Γ(F, U.1) := by
  have hopen : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  ext p
  have hmem : U.2.fromSpec p ∈ U.1 :=
    U.2.range_fromSpec.subset (Set.mem_range_self p)
  have hp : U.2.primeIdealOf ⟨U.2.fromSpec p, hmem⟩ = p :=
    U.2.fromSpec.isOpenEmbedding.injective (U.2.fromSpec_primeIdealOf _)
  have key := mem_support_sections_iff_mem_supp F U (U.2.fromSpec p) hmem
  rw [hp] at key
  exact key.symm

end AlgebraicGeometry.Scheme.Modules

/-! ### Coverage of Section 29.5

Each declaration below carries the tag of the whole section, with one clause naming the
assertion of the section that it realizes.
-/

add_to_stacks 056H "Lemma 29.5.1: on an affine open the supports agree"
  AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp

add_to_stacks 056H "Lemma 29.5.2: the support is stable under specialization"
  AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_supp

add_to_stacks 056H "Lemma 29.5.3 part (1): the support of a finite type module is closed"
  SheafOfModules.isClosed_supp

add_to_stacks 056H "Lemma 29.5.3 part (2): the support is where the stalk is nonzero"
  SheafOfModules.mem_supp_iff_nontrivial_stalk

add_to_stacks 056H "Lemma 29.5.3 part (2): nonzero stalk is nonzero fibre"
  AlgebraicGeometry.Scheme.Modules.nontrivial_stalk_iff_nontrivial_fibre

add_to_stacks 056H "Lemma 29.5.3 part (3): a pullback of a finite type module is of finite type"
  AlgebraicGeometry.SheafOfModules.pullback_isFiniteType

add_to_stacks 056H "Lemma 29.5.3 part (3): the support of a pullback is the inverse image"
  Stacks.Modules.supp_pullback

add_to_stacks 056H "Lemma 29.5.4 and Definition 29.5.5: the scheme-theoretic support"
  AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport

add_to_stacks 056H "Lemma 29.5.4 part (1): the affine annihilator formula"
  AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport_ideal

add_to_stacks 056H "Lemma 29.5.4: the module descends to its scheme-theoretic support"
  AlgebraicGeometry.Scheme.Modules.exists_module_on_schemeTheoreticSupport

add_to_stacks 056H "Lemma 29.5.4: minimality of the scheme-theoretic support"
  AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport_isSmallest

add_to_stacks 056H "Lemma 29.5.4 part (2): uniqueness of the descended module"
  AlgebraicGeometry.Scheme.Modules.module_on_schemeTheoreticSupport_unique

add_to_stacks 056H "Lemma 29.5.4 part (3): the descended module is of finite type"
  AlgebraicGeometry.Scheme.Modules.module_on_schemeTheoreticSupport_isFiniteType

add_to_stacks 056H "Lemma 29.5.4 part (4): the support is the scheme-theoretic support"
  AlgebraicGeometry.Scheme.Modules.supp_eq_support_schemeTheoreticSupport

add_to_stacks 056H "Lemma 29.5.4 part (4): the descended module has support everything"
  AlgebraicGeometry.Scheme.Modules.module_on_schemeTheoreticSupport_support

end
