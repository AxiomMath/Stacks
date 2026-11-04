module

public import StacksFrontier.RingTheory.Regular.HeightMinimalPrime
public import StacksFrontier.AlgebraicGeometry.Chow.DeltaDimensionCoheight
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The codimension of a regular closed immersion

Let `j : Z ⟶ U` be a closed immersion into a locally Noetherian scheme whose kernel is generated,
over an affine open `V` of `U`, by a weakly regular sequence `f₁, …, f_r`. For a generic point `z`
of an irreducible component of `Z` with `j(z) ∈ V`, the local ring `𝒪_{U, j(z)}` has dimension `r`:
the prime of `j(z)` is minimal over `(f₁, …, f_r)`, so its height is `r`
(`Ideal.height_eq_length_of_mem_minimalPrimes_ofList`).

Combined with `Stacks.Chow.relativeDimension_eq_sub_of_coheight` this gives the δ-dimension of the
components of a regularly embedded closed subscheme: `δ(z) = e - r` when the irreducible
components of `U` through `j(z)` have δ-dimension `e`.

## Main results

* `Stacks.Chow.coheight_eq_of_isWeaklyRegular_ker` — `dim 𝒪_{U,j(z)} = r`.
* `Stacks.Chow.relativeDimension_eq_sub_of_coheight` — `δ(x) = e - dim 𝒪_{X,x}`.

## References

* [Stacks Project, Tag 00KW](https://stacks.math.columbia.edu/tag/00KW)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order RingTheory.Sequence

universe u

namespace Stacks.Chow

/-- **`δ(x) = e - dim 𝒪_{X,x}`** when every generalization of `x` has `δ ≤ e` and some
generalization has `δ = e`. -/
theorem relativeDimension_eq_sub_of_coheight (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (x : X) (e : ℤ)
    (he : ∀ y : X, y ⤳ x → relativeDimension C.dimensionFunction p y ≤ e)
    {η : X} (hη : η ⤳ x) (hηe : relativeDimension C.dimensionFunction p η = e) {n : ℕ}
    (hn : coheight x = n) :
    relativeDimension C.dimensionFunction p x = e - n := by
  obtain ⟨n', hn', hle⟩ := exists_coheight_eq_and_relativeDimension_add_le C p x e he
  rw [hn] at hn'
  obtain rfl : n = n' := by exact_mod_cast hn'
  have h2 := relativeDimension_sub_le_coheight C p hη hn
  omega

/-- **The local ring of the ambient scheme at a generic point of a regularly embedded closed
subscheme has dimension the number of equations.** -/
theorem coheight_eq_of_isWeaklyRegular_ker {U Z : Scheme.{u}} [IsLocallyNoetherian U]
    (j : Z ⟶ U) [IsClosedImmersion j] (z : Z) (hz : coheight z = 0) {V : U.affineOpens}
    (hzV : j z ∈ V.1) {r : ℕ} (f : Fin r → Γ(U, V.1))
    (hreg : IsWeaklyRegular Γ(U, V.1) (List.ofFn f))
    (hker : RingHom.ker (j.app V.1).hom = Ideal.span (Set.range f)) :
    coheight (j z) = r := by
  have := V.2.isOpenImmersion_fromSpec
  have : IsNoetherianRing Γ(U, V.1) := IsLocallyNoetherian.component_noetherian V
  have e1 := V.2.fromSpec_primeIdealOf ⟨j z, hzV⟩
  generalize V.2.primeIdealOf ⟨j z, hzV⟩ = p at e1
  replace e1 : V.2.fromSpec p = j z := e1
  have hofl : Ideal.ofList (List.ofFn f) = j.ker.ideal V := by
    rw [Scheme.Hom.ker_apply, hker]
    unfold Ideal.ofList; congr 1; ext x; simp [List.mem_ofFn]
  have hsupp : (j.ker.supportSet : Set U) = Set.range j := by
    have := Scheme.Hom.support_ker j
    rw [j.isClosedEmbedding.isClosed_range.closure_eq] at this
    exact this
  have hmem : ∀ q : PrimeSpectrum Γ(U, V.1),
      Ideal.ofList (List.ofFn f) ≤ q.asIdeal ↔ V.2.fromSpec q ∈ Set.range j := by
    intro q
    rw [hofl, ← hsupp]
    have h1 := Set.ext_iff.mp
      (V.2.fromSpec_preimage_zeroLocus ((j.ker.ideal V : Ideal Γ(U, V.1)) : Set Γ(U, V.1))) q
    have h2 : V.2.fromSpec q ∈ U.zeroLocus ((j.ker.ideal V : Ideal Γ(U, V.1)) : Set Γ(U, V.1)) ↔
        j.ker.ideal V ≤ q.asIdeal := h1
    rw [← h2]
    have hqV : V.2.fromSpec q ∈ (V.1 : Set U) := V.2.range_fromSpec ▸ ⟨q, rfl⟩
    exact ⟨fun h => j.ker.zeroLocus_inter_subset_supportSet V ⟨h, hqV⟩,
      fun h => j.ker.supportSet_subset_zeroLocus V h⟩
  have hp : p.asIdeal ∈ (Ideal.ofList (List.ofFn f)).minimalPrimes := by
    refine ⟨⟨inferInstance, (hmem p).2 ⟨z, e1.symm⟩⟩, fun q hq hqp => ?_⟩
    have hqprime := hq.1
    obtain ⟨z', hz'⟩ := (hmem ⟨q, hqprime⟩).1 hq.2
    have hsp : (⟨q, hqprime⟩ : PrimeSpectrum Γ(U, V.1)) ⤳ p :=
      (PrimeSpectrum.le_iff_specializes _ _).1 hqp
    have hsp' : j z' ⤳ j z := by
      rw [hz', ← e1]; exact hsp.map V.2.fromSpec.continuous
    have hzz : z' ⤳ z := j.isClosedEmbedding.isInducing.specializes_iff.1 hsp'
    have hmax : IsMax z := Order.coheight_eq_zero.1 hz
    have hzz' : z ⤳ z' := hmax (show z ≤ z' from hzz)
    have hjz : j z' = j z := by rw [(hzz.antisymm hzz').eq]
    have hQ : (⟨q, hqprime⟩ : PrimeSpectrum Γ(U, V.1)) = p :=
      V.2.fromSpec.isOpenEmbedding.injective (hz'.symm.trans (hjz.trans e1.symm))
    rw [← hQ]
  have h := Ideal.height_eq_length_of_mem_minimalPrimes_ofList hreg hp
  rw [List.length_ofFn] at h
  have hc : coheight (V.2.fromSpec.base p) = @coheight (Spec Γ(U, V.1)) _ p :=
    coheight_eq_of_isOpenImmersion V.2.fromSpec
  rw [← e1]
  exact hc.trans ((idealHeight_eq_coheight _ p).symm.trans (by exact_mod_cast h))

end Stacks.Chow

end
