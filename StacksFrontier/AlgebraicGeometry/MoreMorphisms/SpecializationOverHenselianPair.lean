module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreGlobalSections

/-!
# Specializations out of an immersed closed set over a henselian pair

Let `(A, I)` be a henselian pair, `π : P ⟶ Spec A` proper and `j : X ⟶ P` an immersion. Let
`V ⊆ X` be closed and let `F = V ∩ (j ≫ π)⁻¹ V(I)` be its part over the closed fibre. Suppose
that `j(F)` is closed in `P` and that every point of `V` specializes to a point of `F`. Then every
specialization in `P` of a point `j t`, `t ∈ V`, is the image of a specialization of `t` in `X`.
If moreover `V` is the range of a closed immersion and `j` is quasi-compact, `j(V)` is closed in
`P`.

The proof. Write `j(X) = U ∩ Z` with `U` open and `Z` closed, and let `C` be the closure of
`j t`, which lies in `Z`. The closed fibre `G = C ∩ π⁻¹ V(I)` is connected
(`AlgebraicGeometry.isConnected_closedFibre_inter_closure_of_henselianPair`). It is covered by
the two disjoint closed sets `j(F)` and `Uᶜ`, because a point of `C ∩ U` lies in `j(X)` and is
the image of a specialization of `t`, which stays in the closed set `V`. It meets `j(F)`, since
`t` specializes into `F`; hence `G ⊆ j(F) ⊆ U`. So the points of the closed set `C` over `V(I)`
lie in the open `U`, and as `I` lies in the Jacobson radical of `A` this forces `C ⊆ U`
(`AlgebraicGeometry.subset_of_isClosed_of_forall_mem_zeroLocus`). Then `C ⊆ U ∩ Z = j(X)`.

This is the topological core of the properness of the support of the cohomology of the object
of the derived form of Grothendieck's existence theorem proposed in Stacks 0DIR (see the entry
for 0DIR in `errata.md`), where `j` is the immersion of a Chow cover into a projective space.

## Main results

* `AlgebraicGeometry.exists_specializes_eq_of_henselianPair`: specializations of `j t` lift.
* `AlgebraicGeometry.isClosed_range_comp_of_henselianPair`: `j(V)` is closed in `P`.

## References

* [Stacks Project, Tag 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
* [Stacks Project, Tag 01K9](https://stacks.math.columbia.edu/tag/01K9)
* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

/-- **Specializations of an immersed closed set over a henselian pair lift.** Let `(A, I)` be a
henselian pair, `π : P ⟶ Spec A` proper and `j : X ⟶ P` an immersion. Let `V ⊆ X` be closed,
with part `F = V ∩ (j ≫ π)⁻¹ V(I)` over the closed fibre such that `j(F)` is closed in `P` and
every point of `V` specializes to a point of `F`. Then for `t ∈ V`, every specialization `b` of
`j t` in `P` is `j x` for a specialization `x` of `t`. -/
theorem exists_specializes_eq_of_henselianPair (A : Type u) [CommRing A] (I : Ideal A)
    (hI : HenselianPair A I) {P X : Scheme.{u}} (π : P ⟶ Spec (.of A)) [IsProper π]
    (j : X ⟶ P) [IsImmersion j] {V : Set X} (hV : IsClosed V)
    (hF : IsClosed (j '' (V ∩ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))))
    (hspec : ∀ t ∈ V, ∃ v ∈ V ∩ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A), t ⤳ v)
    {t : X} (ht : t ∈ V) {b : P} (hb : j t ⤳ b) : ∃ x, t ⤳ x ∧ j x = b := by
  obtain ⟨U, Z, hU, hZ, hUZ⟩ := j.isLocallyClosed_range
  have hjU (x : X) : j x ∈ U := (hUZ ▸ Set.mem_range_self x : j x ∈ U ∩ Z).1
  have hCZ : closure ({j t} : Set P) ⊆ Z :=
    closure_minimal (Set.singleton_subset_iff.2 (hUZ ▸ Set.mem_range_self t : j t ∈ U ∩ Z).2) hZ
  -- A point of the closure of `j t` lying in `U` is the image of a specialization of `t`.
  have key : ∀ y ∈ closure ({j t} : Set P), y ∈ U → ∃ x, t ⤳ x ∧ j x = y := by
    intro y hy hyU
    obtain ⟨x, rfl⟩ : y ∈ Set.range j := hUZ ▸ ⟨hyU, hCZ hy⟩
    exact ⟨x, j.isEmbedding.specializes_iff.1 (specializes_iff_mem_closure.2 hy), rfl⟩
  -- The closed fibre of the closure of `j t` is connected.
  have hG : _root_.IsConnected
      (π ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ∩ closure ({j t} : Set P)) :=
    isConnected_closedFibre_inter_closure_of_henselianPair A I hI π
      (fun g _ => Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper g)
      (j t)
  -- It lies in `j(F)`.
  have hGF : π ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ∩ closure ({j t} : Set P) ⊆
      j '' (V ∩ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
    have hcover : π ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ∩ closure ({j t} : Set P) ⊆
        j '' (V ∩ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) ∪ Uᶜ := by
      rintro y ⟨hy₀, hy⟩
      by_cases hyU : y ∈ U
      · obtain ⟨x, htx, rfl⟩ := key y hy hyU
        exact Or.inl ⟨x, ⟨hV.stableUnderSpecialization htx ht, hy₀⟩, rfl⟩
      · exact Or.inr hyU
    obtain ⟨v, hvF, htv⟩ := hspec t ht
    have hjv : j v ∈ π ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ∩ closure ({j t} : Set P) :=
      ⟨hvF.2, specializes_iff_mem_closure.1 (htv.map j.continuous)⟩
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hG.isPreconnected _ _ hF
        hU.isClosed_compl hcover (by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
          rintro ⟨-, ⟨x, -, rfl⟩, hx⟩
          exact hx (hjU x)) with h | h
    · exact h
    · exact absurd (hjU v) (h hjv)
  -- Hence the closure of `j t` lies in `U`, and so in `j(X)`.
  have hCU : closure ({j t} : Set P) ⊆ U :=
    subset_of_isClosed_of_forall_mem_zeroLocus I hI π π.isClosedMap isClosed_closure hU
      fun y hy₀ hy => by
        obtain ⟨x, -, rfl⟩ := hGF ⟨hy₀, hy⟩
        exact hjU x
  have hbC : b ∈ closure ({j t} : Set P) := specializes_iff_mem_closure.1 hb
  exact key b hbC (hCU hbC)

/-- **An immersed closed set over a henselian pair is closed.** Let `(A, I)` be a henselian pair,
`π : P ⟶ Spec A` proper and `j : X ⟶ P` a quasi-compact immersion, and let `V ⊆ X` be the range
of a closed immersion `ι : Y ⟶ X`. If `j(F)` is closed for `F = V ∩ (j ≫ π)⁻¹ V(I)` and every
point of `V` specializes to a point of `F`, then `j(V)` is closed in `P`: the quasi-compact
`ι ≫ j` lifts specializations (`AlgebraicGeometry.exists_specializes_eq_of_henselianPair`),
hence is closed (Stacks 01K9). -/
theorem isClosed_range_comp_of_henselianPair (A : Type u) [CommRing A] (I : Ideal A)
    (hI : HenselianPair A I) {P X Y : Scheme.{u}} (π : P ⟶ Spec (.of A)) [IsProper π]
    (j : X ⟶ P) [IsImmersion j] [QuasiCompact j] (ι : Y ⟶ X) [IsClosedImmersion ι]
    (hF : IsClosed (j '' (Set.range ι ∩ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))))
    (hspec : ∀ t ∈ Set.range ι,
      ∃ v ∈ Set.range ι ∩ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A), t ⤳ v) :
    IsClosed (Set.range (ι ≫ j)) := by
  have hsp : SpecializingMap (ι ≫ j) := by
    intro y b hb
    obtain ⟨x, hyx, hxb⟩ := exists_specializes_eq_of_henselianPair A I hI π j
      ι.isClosedEmbedding.isClosed_range hF hspec (Set.mem_range_self y) hb
    obtain ⟨y', rfl⟩ := ι.isClosedEmbedding.isClosed_range.stableUnderSpecialization hyx
      (Set.mem_range_self y)
    exact ⟨y', ι.isClosedEmbedding.isEmbedding.specializes_iff.1 hyx, hxb⟩
  exact ((isClosedMap_iff_specializingMap (ι ≫ j)).2 hsp).isClosed_range

end AlgebraicGeometry

end
