module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine

/-!
# Cohomology of a point: the vanishing links of the two chains

[Stacks, Tag 03QV] displays two chains of equalities for `S = Spec(K)` with `K` a field,
$$ 0 \;=\; \mathrm{Pic}(\mathrm{Spec}(K)) \;=\;
   H^1_{\acute{e}tale}(\mathrm{Spec}(K)_{\acute{e}tale}, \mathbf{G}_m) \;=\;
   H^1(G, (K^{sep})^*), $$
Hilbert's 90 theorem, and for `i ≥ 1`
$$ 0 \;=\; H^i(\mathrm{Spec}(K), \mathcal{O}) \;=\;
   H^i_{\acute{e}tale}(\mathrm{Spec}(K)_{\acute{e}tale}, \mathbf{G}_a) \;=\;
   H^i(G, K^{sep}). $$
This file proves the first link of each: the Picard group of the spectrum of a field vanishes,
and so does the positive-degree Zariski cohomology of its structure sheaf.

## Main results

* `AlgebraicGeometry.subsingleton_picardGroup_spec_field`: `Pic(Spec K) = 0` for a field `K`.
* `AlgebraicGeometry.isZero_hgroup_structureSheaf_spec_field`:
  `H^i(Spec K, 𝒪) = 0` for `i ≥ 1`.

## Implementation notes

A field is a unique factorization domain — vacuously, every nonzero element being a unit — so
the vanishing of the Picard group is the case `R = K` of [Stacks, Tag 0BDA] as proved in
`Stacks.PicardUFD.isTrivial_of_isInvertible_spec_of_ufd`: every invertible module on the
spectrum of a unique factorization domain is trivial.  The Picard group is
`AlgebraicGeometry.Scheme.picardGroup`, the Picard group of the `RingCat`-valued structure
sheaf, and triviality of every invertible module gives its vanishing by
`AlgebraicGeometry.Scheme.subsingleton_picardGroup`.

The group is shown to be a subsingleton rather than equal to the zero group: it is an additive
group, so being a subsingleton is exactly being zero, and the subsingleton form is the one the
triviality criteria of this repository are stated at.

The vanishing of `H^i(Spec K, 𝒪)` is Serre vanishing, [Stacks, Tag 01XB], at the affine open
`⊤` of `Spec K`, applied to the structure sheaf read as a module over itself, which is
quasi-coherent.  The cohomology group is `Hgroup`, the right derived functor of sections over an
open, which is the Zariski cohomology the chain refers to.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 03QV, the first link of the Hilbert 90 chain**: the Picard group of the spectrum of
a field vanishes.  A field is a unique factorization domain, so every invertible module on its
spectrum is trivial. -/
@[ega "I 2.4.8" "special case"]
theorem subsingleton_picardGroup_spec_field (K : Type u) [Field K] :
    Subsingleton (Spec (.of K)).picardGroup :=
  Scheme.subsingleton_picardGroup _ fun L hL =>
    have := hL; Stacks.PicardUFD.isTrivial_of_isInvertible_spec_of_ufd K L

/-- **Stacks 03QV, the first link of the additive chain**: the positive-degree Zariski cohomology
of the structure sheaf of the spectrum of a field vanishes.  The spectrum of a field is affine
and its structure sheaf is quasi-coherent, so this is Serre vanishing. -/
theorem isZero_hgroup_structureSheaf_spec_field (K : Type u) [Field K] (p : ℕ) (hp : 0 < p) :
    Limits.IsZero (Hgroup (Spec (.of K)).ringCatSheaf ⊤ p
      (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)) :=
  Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen (Spec (.of K))
    (SheafOfModules.unit (Spec (.of K)).ringCatSheaf) ⊤ (isAffineOpen_top _) p hp

end AlgebraicGeometry

end
