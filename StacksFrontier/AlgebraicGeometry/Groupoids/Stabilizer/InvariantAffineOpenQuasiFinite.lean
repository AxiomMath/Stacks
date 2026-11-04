module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Groupoids.CechDescentInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite

/-!
# Invariant affine opens of a finite locally free groupoid quasi-finite over an affine scheme

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` finite locally free, and suppose that
`U` admits a separated, locally quasi-finite morphism of finite type to an affine scheme — for
instance a separated étale morphism. Then every point of `U` has an `R`-invariant affine open
neighbourhood.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_of_quasiFinite`: if
  the object scheme has a separated, locally quasi-finite, locally of finite type morphism to an
  affine scheme, every point has an invariant affine open neighbourhood.
* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_of_etale`: the same
  conclusion for a separated étale morphism to an affine scheme.
* `AlgebraicGeometry.GroupoidScheme.source_preimage_eq_target_preimage_of_isInvariantOpen`: an
  invariant open has the same inverse image under the source and the target maps.

## References

* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
* [Stacks Project, Tag 07S0](https://stacks.math.columbia.edu/tag/07S0)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]

/-- **Invariant affine neighbourhoods for a groupoid quasi-finite over an affine scheme.** If the
object scheme of a finite locally free groupoid scheme has a separated, locally quasi-finite,
locally of finite type morphism to an affine scheme, then every point of it has an invariant
affine open neighbourhood. -/
theorem exists_isInvariantOpen_isAffineOpen_mem_of_quasiFinite {T : Scheme.{u}} [IsAffine T]
    (π : G.objects.left ⟶ T) [IsSeparated π] [LocallyQuasiFinite π] [LocallyOfFiniteType π]
    (u : G.objects.left) :
    ∃ V : G.objects.left.Opens, IsInvariantOpen G V ∧ IsAffineOpen V ∧ u ∈ V := by
  obtain ⟨hsfin, -, -⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    G.source.left).mp inferInstance
  have hs : IsFinite G.source.left := hsfin
  have hfin : (G.target.left.base '' (G.source.left.base ⁻¹' {u})).Finite :=
    (G.source.left.finite_preimage_singleton u).image _
  obtain ⟨W, hW, hTW⟩ := exists_isAffineOpen_containing_finite_of_locallyQuasiFinite π hfin
  exact exists_isInvariantOpen_isAffineOpen_mem G u ⟨W, hW, hTW⟩

/-- **Invariant affine neighbourhoods for a groupoid separated and étale over an affine scheme.**
The case of `exists_isInvariantOpen_isAffineOpen_mem_of_quasiFinite` for an étale morphism,
which is locally quasi-finite and locally of finite type. -/
theorem exists_isInvariantOpen_isAffineOpen_mem_of_etale {T : Scheme.{u}} [IsAffine T]
    (π : G.objects.left ⟶ T) [IsSeparated π] [Etale π] (u : G.objects.left) :
    ∃ V : G.objects.left.Opens, IsInvariantOpen G V ∧ IsAffineOpen V ∧ u ∈ V := by
  obtain ⟨h1, h2⟩ := locallyQuasiFinite_of_etale π
  exact exists_isInvariantOpen_isAffineOpen_mem_of_quasiFinite G π u

omit [IsFiniteLocallyFree (Over.Hom.left G.source)]
  [IsFiniteLocallyFree (Over.Hom.left G.target)] in
/-- An invariant open has the same inverse image under the source and the target maps. -/
theorem source_preimage_eq_target_preimage_of_isInvariantOpen (V : G.objects.left.Opens)
    (hV : IsInvariantOpen G V) : G.source.left ⁻¹ᵁ V = G.target.left ⁻¹ᵁ V :=
  Opens.ext ((isInvariantSet_iff_preimage_eq G V.1).1 hV)

end AlgebraicGeometry.GroupoidScheme

end
