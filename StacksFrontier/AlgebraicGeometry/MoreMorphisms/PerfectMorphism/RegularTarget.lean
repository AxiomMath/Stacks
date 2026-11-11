module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.PseudoCoherentMap.Regular

/-!
# Perfect morphisms over a regular base

A morphism of schemes locally of finite type over a regular scheme is perfect.

## Main results

* `AlgebraicGeometry.perfect_of_isRegular`: Stacks 068B.

## Implementation notes

Regularity of the target is `AlgebraicGeometry.IsRegular`, which is Stacks 02IS: every point has
an affine open neighbourhood whose ring of sections is regular. Those neighbourhoods cover the
target, and perfectness is the affine-local property attached to `RingHom.Perfect`
(`AlgebraicGeometry.hasRingHomProperty_perfect`), so it is local on the target, and over an affine
open of the target it may be checked on the affine opens of the preimage (Mathlib's
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top` and
`AlgebraicGeometry.HasRingHomProperty.of_iSup_eq_top`; this is Stacks 0686). That reduces the
statement to its ring-theoretic form: a finite-type algebra over a regular ring is perfect, which
is Stacks 067K as `Algebra.Perfect.of_finiteType_of_isRegularRing`.

The ring of sections of a member of the cover need not have finite Krull dimension — a regular
Noetherian ring of infinite Krull dimension has infinite global dimension — so the source's extra
hypothesis in Stacks 067K is genuinely absent here. It is not needed: see the implementation
notes of `StacksFrontier.RingTheory.PseudoCoherentMap.Regular`, where the bound on the length of the
resolution is obtained from quasi-compactness of a prime spectrum rather than from a global
dimension bound.

## References

* [The Stacks Project, Lemma 37.61.5 (068B)](https://stacks.math.columbia.edu/tag/068B)
* [The Stacks Project, Definition 28.9.1 (02IS)](https://stacks.math.columbia.edu/tag/02IS)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Lemma 15.83.5 (067K)](https://stacks.math.columbia.edu/tag/067K)
-/

public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks 068B.** A morphism of schemes locally of finite type over a regular scheme is
perfect. -/
@[stacks 068B]
public theorem perfect_of_isRegular {X S : Scheme.{u}} (f : X ⟶ S) (hS : IsRegular S)
    [LocallyOfFiniteType f] : Perfect f := by
  choose U hxU hU using hS
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Perfect) (fun s => (U s).1)
    (eq_top_iff.mpr fun s _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hxU s⟩) fun s => ?_
  have (W : X.Opens) (hW : IsAffineOpen W) (e : W ≤ f ⁻¹ᵁ (U s).1) :
      (f.appLE _ W e).hom.Perfect := by
    have := hU s
    have := f.finiteType_appLE (U s).2 hW e
    algebraize [(f.appLE _ W e).hom]
    exact RingHom.perfect_algebraMap.mpr (Algebra.Perfect.of_finiteType_of_isRegularRing _ _)
  refine HasRingHomProperty.of_iSup_eq_top (P := @Perfect) (fun V => V)
    (iSup_affineOpens_eq_top _) fun V => ?_
  refine (congrArg (fun φ => φ.hom.Perfect)
    (morphismRestrict_appLE f (U s).1 ⊤ V.1 le_top)).mpr ?_
  refine (f.appLE_congr _ (U s).1.ι_image_top rfl fun φ => φ.hom.Perfect).mpr ?_
  exact this _ (V.2.image_of_isOpenImmersion _) _

end AlgebraicGeometry

end
