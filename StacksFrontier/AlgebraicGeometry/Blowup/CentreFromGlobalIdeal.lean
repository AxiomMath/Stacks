module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Limits.ClosedImmersionFinitePresentationLimit

/-!
# The centre of a blowup cut out by an ideal of the global sections

The affine engine of [Stacks, Tag 0810] produces a *finitely generated ideal* `I` of a ring `R`
whose vanishing locus agrees with that of a single element `t`. The blowup API consumes a centre
instead: an `AlgebraicGeometry.Scheme.IdealSheafData` which is of finite type — equivalently, cuts
out a closed subscheme of finite presentation — and whose support is disjoint from the open the
blowup is to leave untouched. This file performs that translation for the ideal sheaf
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop I` attached to an ideal of the global
sections.

Both translations are one step each, and neither needs the scheme to be affine: the ideal sheaf
`ofIdealTop I` has, on an affine open `U`, the image of `I` under restriction, which is finitely
generated as the image of a finitely generated ideal; and its support is the zero locus of `I`,
which is the zero locus of the radical of `I`, so it is contained in the zero locus of any element
of that radical.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_ofIdealTop`: the ideal sheaf attached to
  a finitely generated ideal of the global sections is of finite type. That it therefore cuts out
  a closed subscheme of finite presentation — the clause a `U`-admissible blowup asks of its
  centre — is `AlgebraicGeometry.finitePresentation_subschemeι_ofIdealTop`, proved in
  `StacksFrontier.AlgebraicGeometry.Limits.ClosedImmersionFinitePresentationLimit`, which this file
  imports.
* `AlgebraicGeometry.disjoint_basicOpen_coe_support_ofIdealTop`: if `t` lies in every prime
  containing `I`, the support of that ideal sheaf misses the basic open of `t`. This is the form
  the "supported away from `U`" clause of a `U`-admissible blowup takes when `U` is the
  nonvanishing locus of `t`, which is the situation [Stacks, Tag 0810] leaves one in.

## Implementation notes

The hypothesis of `AlgebraicGeometry.disjoint_basicOpen_coe_support_ofIdealTop` is one direction
of the conclusion `V(t) = V(I)` of [Stacks, Tag 0810], stated as the equivalence
`t ∈ q ↔ I ≤ q` over primes `q`; only the implication `I ≤ q → t ∈ q` is used, and through
`Ideal.radical_eq_sInf` it says exactly that `t` lies in the radical of `I`.

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The ideal sheaf attached to a finitely generated ideal of the global sections is of finite
type.** On an affine open it is the image of the ideal under restriction, and the image of a
finitely generated ideal is finitely generated. -/
public theorem Scheme.IdealSheafData.isFiniteType_ofIdealTop {X : Scheme.{u}}
    {I : Ideal Γ(X, ⊤)} (hI : I.FG) :
    (Scheme.IdealSheafData.ofIdealTop I).IsFiniteType := fun U ↦ by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  exact hI.map _

/-- **An ideal whose vanishing locus is that of `t` has support missing the basic open of `t`.**
If every prime containing `I` contains `t`, then `t` lies in the radical of `I`, so the zero locus
of `I` — which is the support of the ideal sheaf `I` defines — is contained in the zero locus of
`t`, the complement of the basic open of `t`.

This is the clause "supported away from `U`" of a `U`-admissible blowup for the centre produced
by [Stacks, Tag 0810], whose conclusion `V(t) = V(I)` is stated as the equivalence
`t ∈ q ↔ I ≤ q` over primes. -/
public theorem disjoint_basicOpen_coe_support_ofIdealTop {X : Scheme.{u}} (t : Γ(X, ⊤))
    (I : Ideal Γ(X, ⊤)) (h : ∀ q : Ideal Γ(X, ⊤), q.IsPrime → (t ∈ q ↔ I ≤ q)) :
    Disjoint ((X.basicOpen t : X.Opens) : Set X)
      ((Scheme.IdealSheafData.ofIdealTop I).support : Set X) := by
  have ht : t ∈ I.radical := by
    rw [Ideal.radical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun J hJ ↦ (h J hJ.2).mpr hJ.1
  have hsub : ((Scheme.IdealSheafData.ofIdealTop I).support : Set X) ⊆
      ((X.basicOpen t : X.Opens) : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop, ← X.zeroLocus_radical I,
      ← X.zeroLocus_singleton t]
    exact X.zeroLocus_mono (Set.singleton_subset_iff.mpr ht)
  exact Set.disjoint_left.mpr fun x hx hx' ↦ hsub hx' hx

end AlgebraicGeometry

end
