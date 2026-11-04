module

public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree
public import
  StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.DirectImageAlongAnIsomorphism

/-!
# Strictly perfect complexes from complexes of finite projective modules

Let `R` be a commutative ring. The functor `M ↦ M^~` sends a finite *projective* `R`-module to a
direct summand of a finite free `𝒪_{Spec R}`-module, hence a bounded complex of finite projective
`R`-modules to a strictly perfect complex of `𝒪_{Spec R}`-modules. Transporting along an
isomorphism of ringed spaces then produces a strictly perfect complex on any ringed space
isomorphic to `Spec R` — in particular on an affine open of a scheme, which is the shape in which
a local projective resolution over a ring of sections is consumed by the local criterion for
perfectness, [Stacks, Tag 08CN].

`Stacks.AffineTilde.isStrictlyPerfect_tildeComplex` already carries a bounded complex of finite
*free* `R`-modules to a strictly perfect complex. Finite freeness is strictly stronger than what
a projective resolution of length one produces — the terms of such a resolution are finite
projective and need not be free — so that statement does not apply to one, and this file supplies
the version that does.

## Main definitions

* `Stacks.AffineTilde.transportTildeComplex`: the complex of `𝒪_Y`-modules obtained from a
  complex of `R`-modules along an isomorphism of ringed spaces `Spec R ≅ Y`.

## Main results

* `Stacks.AffineTilde.isDirectSummandOfFiniteFree_tilde_of_projective`: the sheaf associated to a
  finite projective `R`-module is a direct summand of a finite free `𝒪_{Spec R}`-module.
* `Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective`: **Stacks 08C4 on an affine
  scheme, for finite projective terms.** The complex associated to a bounded complex of finite
  projective `R`-modules is strictly perfect.
* `Stacks.AffineTilde.isStrictlyPerfect_transportTildeComplex`: the same conclusion transported
  along an isomorphism of ringed spaces.

## Implementation notes

The only input beyond the finite free case is item (3) of `Module.finite_projective_tfae`
(Stacks 00NX): a finite projective module is a direct summand of `R^n`, given as two linear maps
and the equation `f ∘ₗ g = id`. That retract is carried to `Spec R` by `CategoryTheory.Retract.map`
along `M ↦ M^~` and then composed, with `CategoryTheory.Retract.trans`, with the identification
`Stacks.AffineTilde.finiteFreeIsoTilde` of `Stacks.StrictlyPerfect.finiteFree` on `Spec R` with
`(R^n)^~`. Crossing from the `AlgebraicGeometry.Scheme.Modules` spelling, where Mathlib's `tilde`
API lives, to the `Stacks.StrictlyPerfect.OXMod` spelling, where strict perfection is stated, is
`Stacks.AffineTilde.retractOxMod`; the two categories are definitionally equal but carry different
`Category` instances, so a `CategoryTheory.Retract` over one is not syntactically one over the
other.

The transport is `AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivOfIso`, whose
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_moduleEquiv` is exactly the
statement that strict perfection survives it. The isomorphism is taken with `Spec R` as its
*source*, which is the direction in which the direct image along it is the transport wanted here;
a consumer holding `Y ≅ Spec R` applies `CategoryTheory.Iso.symm` first.

All universes of the ringed space coincide, as they must for `Stacks.StrictlyPerfect.OXMod` to be
stated, and the module universe is the ring universe, as it is throughout the `tilde` material.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StrictlyPerfect

namespace Stacks.AffineTilde

universe u

variable {R : CommRingCat.{u}}

/-- **The sheaf associated to a finite projective module is a direct summand of a finite free
`𝒪_{Spec R}`-module.**

A finite projective module is a direct summand of `R^n` (item (3) of
`Module.finite_projective_tfae`, Stacks 00NX); applying `M ↦ M^~` to that retract and composing
with `Stacks.AffineTilde.finiteFreeIsoTilde` exhibits `N^~` as a retract of
`Stacks.StrictlyPerfect.finiteFree` on `Spec R`.

This generalises `Stacks.AffineTilde.isDirectSummandOfFiniteFree_tilde`, which assumes the module
free. -/
theorem isDirectSummandOfFiniteFree_tilde_of_projective (N : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Projective R N] :
    IsDirectSummandOfFiniteFree (X := (Spec R).toRingedSpace) ((tilde.functor R).obj N) := by
  have hFP : Module.Finite R N ∧ Module.Projective R N := ⟨‹_›, ‹_›⟩
  obtain ⟨n, f, g, hfg⟩ := ((Module.finite_projective_tfae R N).out 2 3).mp hFP
  refine (isDirectSummandOfFiniteFree_iff_retract _).mpr ⟨n, ⟨retractOxMod ?_⟩⟩
  refine ((?_ : Retract N (ModuleCat.of R (Fin n → R))).map (tilde.functor R)).trans
    (Retract.ofIso (finiteFreeIsoTilde R n).symm)
  exact ⟨ModuleCat.ofHom g, ModuleCat.ofHom f, by ext x; exact LinearMap.congr_fun hfg x⟩

/-- **Stacks 08C4 on an affine scheme, for finite projective terms.** The complex of
`𝒪_{Spec R}`-modules associated to a bounded complex of finite projective `R`-modules is strictly
perfect.

This is the form a projective resolution of finite length produces: its terms are finite
projective and need not be free, so
`Stacks.AffineTilde.isStrictlyPerfect_tildeComplex` — which assumes them free — does not apply. -/
theorem isStrictlyPerfect_tildeComplex_of_projective (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hfp : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Projective R (E.X i)) :
    IsStrictlyPerfect (X := (Spec R).toRingedSpace)
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) where
  bounded := hbdd.subset fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    exact fun hz => hi ((tilde.functor R).map_isZero hz)
  directSummand i :=
    have := (hfp i).1
    have := (hfp i).2
    isDirectSummandOfFiniteFree_tilde_of_projective (E.X i)

/-- **The complex of `𝒪_Y`-modules associated to a complex of `R`-modules along an isomorphism
`Spec R ≅ Y` of ringed spaces.** It is the termwise direct image, along the isomorphism, of the
complex `\widetilde{E^•}` on `Spec R`. -/
def transportTildeComplex {Y : RingedSpace.{u, u}} (e : (Spec R).toRingedSpace ≅ Y)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (OXMod.{u, u} Y) ℤ :=
  ((AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivOfIso e).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)

/-- **A bounded complex of finite projective modules over `R` is a strictly perfect complex on any
ringed space isomorphic to `Spec R`.**

The complex `\widetilde{E^•}` is strictly perfect on `Spec R` by
`Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective`, and strict perfection survives
the direct image along an isomorphism of ringed spaces by
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_moduleEquiv`.

This is the statement the local criterion for perfectness, [Stacks, Tag 08CN], consumes on an
affine open: a projective resolution over the ring of sections becomes a strictly perfect complex
of modules on the open subspace. -/
theorem isStrictlyPerfect_transportTildeComplex {Y : RingedSpace.{u, u}}
    (e : (Spec R).toRingedSpace ≅ Y) (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hfp : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Projective R (E.X i)) :
    IsStrictlyPerfect (transportTildeComplex e E) :=
  AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_moduleEquiv e _
    (isStrictlyPerfect_tildeComplex_of_projective E hbdd hfp)

end Stacks.AffineTilde

end
