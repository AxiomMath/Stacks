module

public import StacksFrontier.RingTheory.Dualizing.DepthFromExt
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom

/-!
# The normalizing shift of the regular module over a regular local ring

Let `A` be a regular local ring of Krull dimension `d`. Then `A` is Gorenstein, so `A[0]` is a
dualizing complex, and some shift of it is normalized. This file identifies that shift: the
normalized dualizing complex is `A[d]`, that is `A[0]⟦d⟧`.

The identification is a squeeze between the two halves of [stacks 0A7U] applied to the module
`A` itself. Nonvanishing of `Ext^{-δ}(A, A[0]⟦-m⟧)` in the single degree `δ = -m` — which holds
because that Ext group contains an isomorphism — forces `depth(A) ≤ -m` through the minimality
half, while the degree bound half forces `-m ≤ dim(A)` through `dim supp(A) = dim(A)`. For a
regular local ring `depth(A) = dim(A)`, so the two inequalities meet and `-m = dim(A)`.

## Main results

* `Dualizing.nontrivial_ext_single_self_shift` — the degree `-n` self-Ext group of `A[0]` into
  its own shift by `n` is nontrivial, because the shift comparison isomorphism lives in it.
* `Dualizing.exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift` — over a
  regular local ring the Krull dimension is a natural number `d` and `A[0]⟦d⟧` is a normalized
  dualizing complex.

## References

* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The identity of the regular module of a nonzero commutative ring, placed in degree zero, is
a nonzero endomorphism in the derived category. -/
private theorem id_single_self_ne_zero (A : Type u) [CommRing A] [Nontrivial A] :
    (𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ≠ 0 := by
  have hmod : (𝟙 (ModuleCat.of A A) : ModuleCat.of A A ⟶ ModuleCat.of A A) ≠ 0 := by
    intro h
    have hh := congrArg (fun q : ModuleCat.of A A ⟶ ModuleCat.of A A => q.hom (1 : A)) h
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at hh
    exact one_ne_zero hh
  intro h
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  apply hmod
  have : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  apply F.map_injective
  simpa [F] using h

/-- For a nonzero commutative ring, the self-Ext group of `A[0]` into its shift by `n`, in
degree `-n`, is nontrivial: the isomorphism undoing the shift is a nonzero element of it. -/
public theorem nontrivial_ext_single_self_shift (A : Type u) [CommRing A] [Nontrivial A]
    (n : ℤ) :
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))⟦n⟧)
      (-n)) := by
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let e : (S⟦n⟧)⟦-n⟧ ≅ S :=
    (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} A)) n (-n) (by omega)).app S
  refine ⟨⟨e.inv, 0, fun h => id_single_self_ne_zero A ?_⟩⟩
  have hid : e.inv ≫ e.hom = 𝟙 S := e.inv_hom_id
  rw [h, Limits.zero_comp] at hid
  exact hid.symm

/-- **Over a regular local ring the normalizing shift of the regular module is the Krull
dimension.** The dimension is a natural number `d`, and `A[0]⟦d⟧` is a normalized dualizing
complex. -/
public theorem exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    ∃ d : ℕ, ringKrullDim A = (d : ℕ∞) ∧
      IsNormalizedDualizingComplex.{u, 0}
        ((((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A))⟦(d : ℤ)⟧)) := by
  set S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0} S
    (IsRegularLocalRing.isGorensteinLocalRing A)
  obtain ⟨delta, hleast, hdepth⟩ :=
    depth_eq_least_nonzero_negative_ext.{u, 0} (A := A) (M := A) (S⟦-m⟧) hm inferInstance
  have hkrull : ringKrullDim A = ((delta : ℕ∞) : WithBot ℕ∞) := by
    rw [← depth_eq_ringKrullDim_of_isRegularLocalRing A, hdepth]
  have hsupp : Module.supportDim A A = ((delta : ℕ) : WithBot ℕ∞) := by
    rw [Module.supportDim_self_eq_ringKrullDim, hkrull]
    rfl
  have hnt : Nontrivial (DerivedCategory.Ext S (S⟦-m⟧) m) := by
    simpa using nontrivial_ext_single_self_shift A (-m)
  have hIcc := ext_degree_mem_Icc_of_nontrivial.{u, 0} (A := A) (M := A) (S⟦-m⟧) hm delta hsupp
    m hnt
  have hupper : m ≤ 0 := hIcc.2
  have hlower : -(delta : ℤ) ≤ m := hIcc.1
  have hmem : Nontrivial (DerivedCategory.Ext S (S⟦-m⟧) (-(((-m).toNat : ℕ) : ℤ))) := by
    rwa [show -(((-m).toNat : ℕ) : ℤ) = m by omega]
  have hd : ((delta : ℕ) : ℤ) = -m := by
    have := hleast.2 hmem
    omega
  exact ⟨delta, hkrull, by rwa [hd]⟩

end Dualizing

end
