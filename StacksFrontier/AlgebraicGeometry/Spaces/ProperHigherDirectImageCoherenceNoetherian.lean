module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherence

/-!
# Coherence of the higher direct images from a Noetherian algebraic space, by dévissage

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `X` Noetherian and `Y` locally
Noetherian.  The source's proof of Stacks 08AR, after localizing on `Y`, applies the dévissage of
Stacks 08AN on `X` to the property that all higher direct images of a module are coherent.  This
file runs that step with the unconditional Stacks 08AN of
`AlgebraicGeometry.Space.property_of_coherent_of_isNoetherian`, so that the dévissage is no longer
a hypothesis: what remains are the two inputs the source draws from elsewhere, namely

* `h0720`, quasi-coherence of the higher direct images of coherent modules (Stacks 0720), which
  the two-out-of-three and finite-sum conditions consume through Stacks 07UD; and
* `hwitness`, condition (3) of Stacks 08AN for this property: at each reduced closed subspace
  with irreducible space of points a coherent module with that scheme-theoretic support whose
  higher direct images are coherent (the source builds it from Stacks 089J, 08AQ and 02O4).

The zero-module condition is the vanishing of the derived functors at a zero object.

This is groundwork for Stacks 08AR: no attribute is attached, since `h0720` and `hwitness` are
results of other tags carried as hypotheses.

## Main results

* `AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_isNoetherian_source`:
  `R^i f_*𝓕` is coherent for every coherent `𝓕` on a Noetherian `X`, granted `h0720` and
  `hwitness`.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The higher direct images of a coherent module on a Noetherian algebraic space are
coherent, granted Stacks 0720 and condition (3) of Stacks 08AN.**  Stacks 08AN is applied to the
property `AlgebraicGeometry.Space.HasCoherentHigherDirectImages`; its two-out-of-three and
finite-sum conditions are `AlgebraicGeometry.Space.hasCoherentHigherDirectImages_twoOutOfThree`
and `AlgebraicGeometry.Space.hasCoherentHigherDirectImages_finiteSum`, the direct sum of `r`
copies of a module being the colimit of its cofan of inclusions, and the property holds at a zero
module because a zero module is injective, so its derived functors vanish in positive degree,
and in degree zero the derived functor is the direct image itself. -/
theorem isCoherent_rightDerived_modulePushforward_of_isNoetherian_source
    (hZtop : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hX : IsNoetherian B S hS hZtop X.1)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (h0720 : QuasicoherentHigherDirectImages B S hS f)
    (hwitness :
      HasCoherentWitnessOnIntegralSubspaces B S hS X (HasCoherentHigherDirectImages B S hS f))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived i).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine property_of_coherent_of_isNoetherian B S hS hZtop X hX
    (HasCoherentHigherDirectImages B S hS f) ?_
    (hasCoherentHigherDirectImages_twoOutOfThree B S hS f hY h0720) ?_ hwitness F hF i
  · intro M hM n
    have := hM.injective
    refine isCoherent_of_isZero B S hS Y ?_
    cases n with
    | zero =>
      exact (Functor.map_isZero (modulePushforward B S hS f) hM).of_iso
        ((modulePushforward B S hS f).rightDerivedZeroIsoSelf.app M)
    | succ n => exact (modulePushforward B S hS f).isZero_rightDerived_obj_injective_succ n M
  · intro G hG r hr hP
    exact hasCoherentHigherDirectImages_finiteSum B S hS f hY h0720 G (⨁ fun _ : Fin r ↦ G) r
      hG hr (fun j ↦ biproduct.ι (fun _ : Fin r ↦ G) j) ⟨biproduct.isColimit _⟩ hP

end AlgebraicGeometry.Space

end
