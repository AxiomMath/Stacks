module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite affine open covering of a quasi-compact scheme, and its functions

A quasi-compact scheme is covered by finitely many affine opens, and its structure sheaf is
separated, so a global function vanishing on each member of such a covering is zero.  Together
these say that the global functions on a quasi-compact scheme inject into a *finite* product of
rings of affine schemes mapping to it.

## Main results

* `AlgebraicGeometry.Scheme.exists_finite_affine_openCover`: a quasi-compact scheme has an open
  covering with finite index type and affine members.
* `AlgebraicGeometry.Scheme.exists_finite_affine_cover_appTop_injective`: the same covering,
  packaged with the injectivity of the global functions into the product of the functions on its
  members.

## Implementation notes

This is the reduction step of Stacks 083K — *"choose a finite affine open covering
`T = T_1 ∪ … ∪ T_m`"* — in the form in which
`Stacks.Flattening.tmul_one_eq_zero_of_forall_tmul_one_eq_zero` consumes it.  The source
continues *"it is clear that we may replace `T` by `⨿_j T_j`"*, which asks for the coproduct of
the members as a scheme over the base and for the identification of its functions with the
product; neither is needed, because the only property of the coproduct used afterwards is
exactly the injectivity proved here, and that injectivity holds for `Γ(T)` itself.

The covering is `AlgebraicGeometry.Scheme.OpenCover.finiteSubcover` of the canonical affine
covering, and the injectivity is `AlgebraicGeometry.Scheme.zero_of_zero_cover`, the separatedness
of the structure sheaf on an open covering.  Quasi-compactness is spelt `CompactSpace` on the
underlying topological space, which is what the finite subcovering consumes.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- **A quasi-compact scheme has a finite affine open covering.**  Take the finite subcovering of
the canonical affine covering. -/
@[ega "IV 1.8.1" "partial"]
theorem exists_finite_affine_openCover (T : Scheme.{u}) [CompactSpace T] :
    ∃ 𝒰 : Scheme.OpenCover.{u, u} T, Finite 𝒰.I₀ ∧ ∀ i, IsAffine (𝒰.X i) :=
  ⟨T.affineCover.finiteSubcover, inferInstance, fun _ => inferInstance⟩

/-- **The global functions on a quasi-compact scheme inject into a finite product of affine
rings.**  There are finitely many affine schemes mapping to `T` such that a global function on
`T` pulling back to zero on each of them is zero.

The maps are the members of a finite affine open covering, and the injectivity is separatedness
of the structure sheaf along that covering. -/
theorem exists_finite_affine_cover_appTop_injective (T : Scheme.{u}) [CompactSpace T] :
    ∃ (ι : Type u) (_ : Finite ι) (A : ι → Scheme.{u}) (_ : ∀ i, IsAffine (A i))
      (g : ∀ i, A i ⟶ T), ∀ x : Γ(T, ⊤), (∀ i, (g i).appTop.hom x = 0) → x = 0 :=
  ⟨T.affineCover.finiteSubcover.I₀, inferInstance, T.affineCover.finiteSubcover.X,
    fun _ => inferInstance, T.affineCover.finiteSubcover.f,
    fun x hx => Scheme.zero_of_zero_cover x T.affineCover.finiteSubcover hx⟩

end AlgebraicGeometry.Scheme

end
