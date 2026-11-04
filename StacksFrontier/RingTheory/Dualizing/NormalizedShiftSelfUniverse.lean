module

public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayFromModule
public import StacksFrontier.RingTheory.Dualizing.DepthFromExt
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.RegularLocalNormalizedShift

/-!
# The normalizing shift of a Gorenstein local ring, read in the ring's own universe

Let `A` be a Noetherian local Gorenstein ring of Krull dimension `d` in `Type u`. Then `A[0]` is
a dualizing complex and `A[d] = A[0]⟦d⟧` is the shift that normalizes it.

Normalization is a condition on the derived Hom out of the residue field, and that functor
carries a second universe parameter: `Dualizing.IsNormalizedDualizingComplex.{u, v}` compares
`RHom_A(κ, K)` with the residue field pushed into `Type (max v u)` along
`ModuleCat.uliftFunctor.{v}`. For a ring in `Type u` the two interesting values are `v = 0` and
`v = u`; the ambient complex `A[0]⟦d⟧` is the same object in both cases, since `max u u` is `u`,
but the predicate is not the same proposition. This file proves the `v = u` form, which is the
one needed by duality statements that keep the ring and its modules in a single universe.

The argument is the squeeze of [stacks 0A7U] applied to the module `A` itself, exactly as in
`Dualizing.exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift`, and every
ingredient of that squeeze is already polymorphic in the second universe. The minimality half of
[stacks 0A7U] identifies `-m` with `depth(A)` for the normalizing shift `m`, the degree-bound
half confines `-m` to `[0, dim supp(A)]`, and over a Gorenstein — hence Cohen--Macaulay — local
ring `depth(A) = dim(A) = d`.

## Main results

* `LocalDuality.isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing_self`
  — over a Noetherian local Gorenstein ring of dimension `d`, the complex `A[0]⟦d⟧` is a
  normalized dualizing complex in the sense of `Dualizing.IsNormalizedDualizingComplex.{u, u}`.
* `LocalDuality.isNormalizedDualizingComplex_single_self_shift_of_isRegularLocalRing_self`
  — the same for a regular local ring, which is Gorenstein by [stacks 0AWX].

## Implementation notes

The dimension enters as a natural number `d` with `ringKrullDim A = d`, the idiom of
[stacks 0AWS] and [stacks 0A7U]; such a `d` exists for every Noetherian local ring, so this is
no extra assumption.

Two bridges are reproved here rather than imported: that the depth of a local ring read off
lists of ring elements agrees with its depth as a module over itself, and that a Cohen--Macaulay
local ring has self-depth equal to its Krull dimension. Both exist elsewhere in the library only
as private lemmas.

## References

* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 0DW8](https://stacks.math.columbia.edu/tag/0DW8)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing.LocalDuality

/-- The depth of a local ring, read off lists of elements of its maximal ideal, is its depth as
a module over itself. -/
private theorem localRingDepth_eq_depthSup_self (A : Type u) [CommRing A] [IsLocalRing A] :
    localRingDepth A = Module.depthSup A (IsLocalRing.maximalIdeal A) A := by
  rw [localRingDepth, Module.depthSup_eq_iSup]
  exact le_antisymm
    (iSup_le fun s => le_iSup₂_of_le s.val s.property le_rfl)
    (iSup_le fun rs => iSup_le fun hrs => le_iSup_of_le ⟨rs, hrs⟩ le_rfl)

/-- A Cohen--Macaulay local ring has self-depth equal to its Krull dimension: that is what
Cohen--Macaulayness says, once the depth of the ring as a module over itself is matched with the
depth read off lists of elements, and the dimension of the support of the regular module with
the Krull dimension. -/
private theorem depth_self_eq_ringKrullDim_of_isCohenMacaulayLocalRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsCohenMacaulayLocalRing A) :
    (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) = ringKrullDim A := by
  have hsup : (Module.depthSup A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) =
      Module.supportDim A A := hA
  rw [← localRingDepth_eq_depth_self A, localRingDepth_eq_depthSup_self A, hsup]
  exact Module.supportDim_self_eq_ringKrullDim A

/-- **`A[d]` normalizes the dualizing complex of a Gorenstein local ring, in the ring's own
module universe.** Some shift `A[0]⟦-m⟧` of the dualizing complex `A[0]` is normalized. The
minimality half of [Stacks, Tag 0A7U], applied to the module `A`, whose self-Ext into that shift
is nonzero in degree `m` because it contains the comparison isomorphism, forces
`depth(A) ≤ -m`, while the degree-bound half forces `-m ≤ dim supp(A) = dim(A)`. A Gorenstein
local ring is Cohen--Macaulay, so `depth(A) = dim(A) = d` and the two inequalities meet at
`-m = d`. -/
theorem isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing_self
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Dualizing.IsGorensteinLocalRing A) (d : ℕ)
    (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A))⟦(d : ℤ)⟧) := by
  set S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, u} S hA
  obtain ⟨delta, hleast, hdepth⟩ :=
    depth_eq_least_nonzero_negative_ext.{u, u} (A := A) (M := A) (S⟦-m⟧) hm inferInstance
  have hkrull : ringKrullDim A = ((delta : ℕ∞) : WithBot ℕ∞) := by
    rw [← depth_self_eq_ringKrullDim_of_isCohenMacaulayLocalRing A
      (IsGorensteinLocalRing.isCohenMacaulayLocalRing A hA)]
    exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hdepth
  have hsupp : Module.supportDim A A = ((delta : ℕ) : WithBot ℕ∞) := by
    rw [Module.supportDim_self_eq_ringKrullDim, hkrull]
    rfl
  have hnt : Nontrivial (DerivedCategory.Ext S (S⟦-m⟧) m) := by
    simpa using nontrivial_ext_single_self_shift A (-m)
  have hIcc := ext_degree_mem_Icc_of_nontrivial.{u, u} (A := A) (M := A) (S⟦-m⟧) hm delta hsupp
    m hnt
  have hupper : m ≤ 0 := hIcc.2
  have hlower : -(delta : ℤ) ≤ m := hIcc.1
  have hmem : Nontrivial (DerivedCategory.Ext S (S⟦-m⟧) (-(((-m).toNat : ℕ) : ℤ))) := by
    have hcast : -(((-m).toNat : ℕ) : ℤ) = m := by omega
    rw [hcast]
    exact hnt
  have hle : delta ≤ (-m).toNat := hleast.2 hmem
  have hdelta : ((delta : ℕ) : ℤ) = -m := by omega
  have hdeltad : delta = d := by
    have hcast : ((delta : ℕ∞) : WithBot ℕ∞) = ((d : ℕ) : WithBot ℕ∞) := by
      rw [← hkrull]
      exact hdim
    exact_mod_cast hcast
  have hd : ((d : ℕ) : ℤ) = -m := by
    rw [← hdeltad]
    exact hdelta
  rw [hd]
  exact hm

/-- **`A[d]` normalizes the dualizing complex of a regular local ring, in the ring's own module
universe.** A regular local ring is Gorenstein ([Stacks, Tag 0AWX]), so this is the Gorenstein
statement above. -/
theorem isNormalizedDualizingComplex_single_self_shift_of_isRegularLocalRing_self
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (d : ℕ)
    (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A))⟦(d : ℤ)⟧) :=
  isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing_self A
    (Dualizing.IsRegularLocalRing.isGorensteinLocalRing A) d hdim

end Dualizing.LocalDuality

end
