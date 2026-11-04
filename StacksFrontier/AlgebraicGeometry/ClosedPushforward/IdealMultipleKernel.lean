module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
import StacksFrontier.AlgebraicGeometry.Duality.SheafSubquotient

/-!
# The kernel of the restriction to a closed subscheme is `I ⁿ M`

Let `v : V ⟶ X` be a closed immersion of schemes whose ideal sheaf is the `n`-th power of an
ideal sheaf `I`, and let `M` be a quasi-coherent module on `X`. Restriction to the closed
subscheme is the unit `M ⟶ v_* v^* M` of the adjunction `v^* ⊣ v_*`, and this file identifies its
sectionwise kernel with the subsheaf `I ⁿ M`:

`ker (M ⟶ v_* v^* M) = I ⁿ M`.

Only one inclusion was available before. `…idealPowerMultiple_le_kernelSubmodule` gives
`I ⁿ M ≤ ker`, from the annihilation of the sections of a pushforward along `v`; the reverse
inclusion is the content of Stacks Tag 0EL1, and this file is where that content is read off as a
statement about kernels.

## Main results

* `Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealPowerMultiple`: **the kernel of the
  restriction to a closed subscheme with ideal sheaf `I ⁿ` is `I ⁿ M`.**
* `Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple`: the same at `n = 1` and
  `I = v.ker`, with no hypothesis beyond `v` being a closed immersion — the form
  `ker (M ⟶ i_* i^* M) = ℐ_Z · M` in which the statement is wanted.

## Implementation notes

Tag 0EL1 is formalized as the *isomorphism* `…idealQuotientPushforwardIso`, normalized by the
adjunction unit: `…idealQuotientPushforwardMap_π` factors the unit as the projection
`M ⟶ M / I ⁿ M` followed by that isomorphism. An isomorphism of sheaves of modules is injective
on the sections over every open, so it may be cancelled from a sectionwise kernel by
`AlgebraicGeometry.kernelSubmodule_comp_eq`, which leaves the kernel of the projection; that is
the submodule itself, by `…kernelSubmodule_cokernel_π_ι`.

The injectivity is proved from the inverse morphism rather than through a mono-implies-injective
lemma: the components of a composite are the composites of the components by `rfl`, so
`IsIso.hom_inv_id` gives a left inverse of the component directly, and no transport between the
bundled and unbundled spellings of a `ModuleCat` morphism is needed.

The two modules supplying those two lemmas are imported **privately**: their names occur only
inside the proof, and a `public import` would add them to the closure of every module downstream
of this one.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)

## Not done here

No `stacks` attribute is attached. Tag 0EL1's own statement is the isomorphism, which is formalized
and registered where it is proved; what is added here is its kernel form, a corollary, and
placing a tag on a corollary would not be a covering set for any tag.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.Algebraization

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
  {V : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v] (hv : v.ker = I ^ n)

include hv in
/-- **The kernel of the restriction to a closed subscheme is `I ⁿ M`.** For a closed immersion
`v` whose ideal sheaf is `I ⁿ` and a quasi-coherent `M`, a local section of `M` dies in
`v_* v^* M` exactly when it lies in the subsheaf `I ⁿ M`.

Stacks Tag 0EL1 factors the adjunction unit as the projection `M ⟶ M / I ⁿ M` followed by an
isomorphism; the isomorphism cancels from the sectionwise kernel, and the kernel of the
projection is `I ⁿ M`. -/
public theorem kernelSubmodule_unit_app_eq_idealPowerMultiple [F.IsQuasicoherent] :
    kernelSubmodule ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app F) =
      idealPowerMultiple I n F := by
  have := isIso_idealQuotientPushforwardMap I n F v hv
  have e : ∀ (U : (TopologicalSpace.Opens X)ᵒᵖ) (t : _),
      ((inv (idealQuotientPushforwardMap I n F v hv)).val.app U).hom
        (((idealQuotientPushforwardMap I n F v hv).val.app U).hom t) = t := by
    intro U t
    have h : ((idealQuotientPushforwardMap I n F v hv ≫
        inv (idealQuotientPushforwardMap I n F v hv)).val.app U).hom t = t := by
      rw [IsIso.hom_inv_id]; rfl
    exact h
  rw [← idealQuotientPushforwardMap_π I n F v hv,
    AlgebraicGeometry.kernelSubmodule_comp_eq _ _
      (fun U a b hab => by rw [← e U a, ← e U b, hab]),
    kernelSubmodule_cokernel_π_ι]

/-- **`ker (M ⟶ i_* i^* M) = ℐ_Z · M`**, for an arbitrary closed immersion of schemes and an
arbitrary quasi-coherent module: the sections of `M` vanishing on the closed subscheme are
exactly those of the subsheaf cut out by the immersion's ideal sheaf.

This is the previous result at `n = 1` and `I = v.ker`, where the hypothesis identifying the
ideal sheaf with a power is `pow_one`. -/
public theorem kernelSubmodule_unit_app_eq_idealMultiple {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {V : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v] :
    kernelSubmodule ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app F) =
      idealPowerMultiple v.ker 1 F :=
  kernelSubmodule_unit_app_eq_idealPowerMultiple v.ker 1 F v (pow_one _).symm

end Stacks.Algebraization

end
