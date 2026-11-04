module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCore.Tactic.StacksAttribute

/-!
# Ample families of invertible modules

An *ample family of invertible modules* on a scheme `X` is a family `{L i}` of invertible
`O_X`-modules such that `X` is quasi-compact and every point of `X` lies in an affine
nonvanishing locus of a global section of some positive tensor power `L i ^ n`.

The intended use is the resolution property: a scheme carrying such a family has it. That
implication is **not** proved here; see the implementation notes for exactly what it waits on.

## Main definitions

* `AlgebraicGeometry.Scheme.tensorPow` is the `n`th tensor power of a module on a scheme, for
  `n : ℕ`, read off the site-level tensor power.
* `AlgebraicGeometry.Scheme.nonvanishingSet` is the nonvanishing locus of a global section,
  read off the ringed-space-level nonvanishing locus.
* `AlgebraicGeometry.Scheme.IsAmpleFamily` is an ample family of invertible modules.

## Main results

* `AlgebraicGeometry.Scheme.IsAmpleFamily.compactSpace_carrier` records that the underlying
  space of a scheme with an ample family is quasi-compact.
* `AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover` extracts from an ample
  family a *finite* affine open cover, each member of which is the nonvanishing locus of a
  global section of a positive tensor power of a member of the family. This is the first
  sentence of the Stacks proof of Tag 0GMM.

## Implementation notes

The nonvanishing locus is stated for a global section in the sense of
`PresheafOfModules.sections`, a compatible family over all opens, which for a sheaf is the same
thing as a section over `⊤`. It is phrased through `nonvanishingSet` rather than through
`Stacks.SheafOfModules.nonvanishingOpen` so that the statement of `IsAmpleFamily` carries no
invertibility hypothesis: `nonvanishingOpen` needs the module to be invertible in order to know
the locus is open, whereas `nonvanishingLocus` is defined for every module. Openness is instead
supplied by the `Opens` witness `U` together with the equation `U = nonvanishingSet ..`, which
is also closer to the source, where `X_s` is simply asserted to be affine.

The tensor power used is the natural-number one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExteriorSymmetricAlgebras.lean`, which is
defined by recursion for an arbitrary sheaf of modules. The integer-indexed power of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPower.lean` is the one invertibility is
developed for, but it takes the invertibility of its argument as an instance, which would make the
last field of `IsAmpleFamily` depend on the first; the recursive power avoids that.

**Universe narrowing, inherited rather than chosen here.** The nonvanishing locus is developed
at `RingedSpace.{u, u}` — see the `variable {X : RingedSpace.{u, u}}` at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean:366` — so
`nonvanishingSet`, and with it `IsAmpleFamily`, is available only with the ringed-space
universes collapsed. The index type `I` of the family keeps its own universe `v`. This
narrowing comes down the chain from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean` and is not a decision
taken in this file.

**`nonvanishingSet` is `@[expose]`.** A consumer proving the last field of `IsAmpleFamily` has
to identify `nonvanishingSet` with the ringed-space-level
`Stacks.SheafOfModules.nonvanishingLocus` that a lemma about its section is stated for — for
instance `Stacks.Divisors.nonvanishingLocus_canonicalSections`, which computes the nonvanishing
locus of the canonical section of an effective Cartier divisor. That identification is a `rfl`,
so the body has to be available outside this module.

**The resolution property.** The Stacks proof of Tag 0GMM applies Tag 0F89 to the cover
produced by `exists_finite_affine_nonvanishing_cover` together with the ideal sheaves cut out by
the sections; that is `AlgebraicGeometry.hasResolutionProperty_of_isAmpleFamily` in
`./ResolutionPropertyAmpleFamilyIdealCovering.lean`.

## References

* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u v

namespace AlgebraicGeometry.Scheme

/-- The `n`th tensor power `L^{⊗ n}` of a module on a scheme, for `n : ℕ`. This is the
site-level tensor power taken for the open-cover topology on `X`. -/
noncomputable abbrev tensorPow (X : Scheme.{u}) (L : X.Modules) (n : ℕ) : X.Modules :=
  SheafOfModules.tensorPower (Osharp := X.sheaf) (Opens.grothendieckTopology X.carrier) L n

/-- The nonvanishing locus `X_s` of a global section `s` of a module `M` on a scheme: the set of
points at which the germ of `s` does not lie in `𝔪_x M_x`. -/
@[expose]
def nonvanishingSet (X : Scheme.{u}) (M : X.Modules) (s : M.sections) : Set X.carrier :=
  Stacks.SheafOfModules.nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace) M s

/-- The nonvanishing locus of a global section on a scheme is the ringed-space nonvanishing
locus of Stacks Tag 01CY, read on the underlying ringed space. -/
theorem nonvanishingSet_eq (X : Scheme.{u}) (M : X.Modules) (s : M.sections) :
    X.nonvanishingSet M s =
      Stacks.SheafOfModules.nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace) M s :=
  rfl

/-- **Stacks Project, Tag 0FXR.** A family `{L i}` of invertible modules on a scheme `X` is an
*ample family of invertible modules* if `X` is quasi-compact and every point of `X` lies in an
affine nonvanishing locus of a global section of some positive tensor power of some `L i`. -/
structure IsAmpleFamily {I : Type v} (X : Scheme.{u}) (L : I → X.Modules) : Prop where
  /-- Each member of the family is invertible. -/
  isInvertible (i : I) : IsInvertible X.presheaf X.ringCatSheaf.2 (L i)
  /-- The scheme is quasi-compact. -/
  compactSpace : CompactSpace X.carrier
  /-- Every point lies in an affine nonvanishing locus of a global section of a positive tensor
  power of some member of the family. -/
  exists_affine_nonvanishing (x : X.carrier) :
    ∃ (i : I) (n : ℕ) (_ : 1 ≤ n) (s : (X.tensorPow (L i) n).sections) (U : X.Opens),
      (U : Set X.carrier) = X.nonvanishingSet (X.tensorPow (L i) n) s ∧
        x ∈ U ∧ IsAffineOpen U

namespace IsAmpleFamily

variable {I : Type v} {X : Scheme.{u}} {L : I → X.Modules}

/-- The underlying space of a scheme carrying an ample family is quasi-compact. -/
theorem compactSpace_carrier (hL : X.IsAmpleFamily L) : CompactSpace X.carrier :=
  hL.compactSpace

end IsAmpleFamily

/-- **The first sentence of the Stacks proof of Tag 0GMM.** From an ample family of invertible
modules on `X` one extracts a *finite* open cover of `X` by affine opens, each of which is the
nonvanishing locus of a global section of a positive tensor power of a member of the family.

Quasi-compactness is what makes the cover finite: the nonvanishing loci supplied pointwise by
`IsAmpleFamily.exists_affine_nonvanishing` already cover `X`, and a finite subfamily suffices. -/
theorem exists_finite_affine_nonvanishing_cover {I : Type v} (X : Scheme.{u})
    (L : I → X.Modules) (hL : X.IsAmpleFamily L) :
    ∃ (m : ℕ) (i : Fin m → I) (n : Fin m → ℕ) (U : Fin m → X.Opens)
      (s : ∀ k, (X.tensorPow (L (i k)) (n k)).sections),
      IsOpenCover U ∧ ∀ k, 1 ≤ n k ∧ IsAffineOpen (U k) ∧
        (U k : Set X.carrier) = X.nonvanishingSet (X.tensorPow (L (i k)) (n k)) (s k) := by
  have : CompactSpace X.carrier := hL.compactSpace
  choose i n hn s U hEq hx hAff using hL.exists_affine_nonvanishing
  -- the pointwise nonvanishing loci already cover `X`
  have hcov : (Set.univ : Set X.carrier) ⊆ ⋃ x, (U x : Set X.carrier) :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.carrier => (U x : Set X.carrier)) (fun x => (U x).isOpen) hcov
  -- reindex the finite subfamily by `Fin t.card`
  let ξ : Fin t.card → X.carrier := fun k => (t.equivFin.symm k).1
  refine ⟨t.card, fun k => i (ξ k), fun k => n (ξ k), fun k => U (ξ k),
    fun k => s (ξ k), ?_, fun k => ⟨hn (ξ k), hAff (ξ k), hEq (ξ k)⟩⟩
  refine IsOpenCover.mk (le_antisymm (iSup_le fun _ => le_top) ?_)
  intro x _
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ (U y : Set X.carrier) := by
    simpa only [Set.mem_iUnion, Finset.mem_coe, exists_prop] using ht (Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa [ξ] using hxy⟩

add_to_stacks 0FXR AlgebraicGeometry.Scheme.IsAmpleFamily
add_to_sga "6 II 2.2.4" AlgebraicGeometry.Scheme.IsAmpleFamily

end AlgebraicGeometry.Scheme

end
