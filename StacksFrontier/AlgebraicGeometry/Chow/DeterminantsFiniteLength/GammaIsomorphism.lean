module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.ExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Spanning

/-!
# The determinant map of a short exact sequence is an isomorphism

The canonical determinant map associated to a short exact sequence of finite-length modules
over a local ring is an isomorphism of vector spaces over the residue field.

## Main results

* `Module.FiniteLength.determinantExactSequenceMap_bijective` states that the determinant
  map is bijective.

## Implementation notes

A short exact sequence is represented by two linear maps, injectivity of the first,
surjectivity of the second, and exactness at the middle term. The assertion that its linear
determinant map is an isomorphism is expressed as bijectivity of the underlying function.
Both sides are one-dimensional over the residue field, so it is enough to see that the map
is nonzero, and that follows from its value on the tensor of two spanning symbols, which is
the symbol of their concatenation.

## References

* [Stacks Project, Tag 02PA](https://stacks.math.columbia.edu/tag/02PA)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module.FiniteLength

universe u v w x

/-- The symbol of an admissible sequence spanning a finite-length module is nonzero. -/
private theorem symbol_ne_zero_of_span_eq_top
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (e : AdmissibleSequence R M)
    (he : Submodule.span R (Set.range e.1) = ⊤) : symbol e ≠ 0 := by
  have : Nontrivial (determinant R M) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_determinant_eq_one hM]; exact Nat.zero_lt_one)
  intro hz
  have := span_symbol_eq_top hM e he
  simp [hz] at this

/-- **The determinant map of a short exact sequence is an isomorphism.** For a short exact
sequence `0 → K → L → M → 0` of finite-length modules over a local ring, the determinant map
`det(K) ⊗ det(M) → det(L)` is bijective. -/
@[stacks 02PA "gamma_isomorphism"]
public theorem determinantExactSequenceMap_bijective
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hM : IsFiniteLength R M) :
    Function.Bijective (determinantExactSequenceMap i p hi hp hip hK hL hM) := by
  classical
  let κ := IsLocalRing.ResidueField R
  let γ := determinantExactSequenceMap i p hi hp hip hK hL hM
  obtain ⟨eK, heK⟩ := exists_admissible_generator hK
  obtain ⟨eM, heM⟩ := exists_admissible_generator hM
  have hdimK := finrank_determinant_eq_one hK
  have hdimM := finrank_determinant_eq_one hM
  have hdimL := finrank_determinant_eq_one hL
  have hsymK := symbol_ne_zero_of_span_eq_top hK eK heK
  have hsymM := symbol_ne_zero_of_span_eq_top hM eM heM
  have hsource : Module.finrank κ (determinant R K ⊗[κ] determinant R M) = 1 := by
    rw [Module.finrank_tensorProduct, hdimK, hdimM]
  let _ : IsSimpleModule κ (determinant R K ⊗[κ] determinant R M) :=
    isSimpleModule_iff_finrank_eq_one.mpr hsource
  let _ : IsSimpleModule κ (determinant R L) :=
    isSimpleModule_iff_finrank_eq_one.mpr hdimL
  have hγ : γ ≠ 0 := by
    intro hγzero
    let f : Fin (moduleLength R M) → L := fun a => Classical.choose (hp (eM.1 a))
    have hf : ∀ a, p (f a) = eM.1 a :=
      fun a => Classical.choose_spec (hp (eM.1 a))
    obtain ⟨hlen, hadm, hvalue⟩ :=
      determinantExactSequenceMap_spec i p hi hp hip hK hL hM
        eK eM hsymK hsymM f hf
    let c : Fin (moduleLength R K + moduleLength R M) → L :=
      Fin.append (fun a => i (eK.1 a)) f
    let cseq : Fin (moduleLength R L) → L := fun a => c (Fin.cast hlen a)
    let Sc : Submodule R L := Submodule.span R (Set.range c)
    have hrangeM : Set.range eM.1 ⊆ Submodule.map p Sc := by
      rintro y ⟨a, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨c (Fin.natAdd (moduleLength R K) a), ?_, ?_⟩
      · exact Submodule.subset_span ⟨Fin.natAdd (moduleLength R K) a, rfl⟩
      · simp [c, Fin.append_right, f, hf]
    have hmap : Submodule.map p Sc = ⊤ := by
      apply top_unique
      rw [← heM]
      calc
        Submodule.span R (Set.range eM.1) ≤
            Submodule.span R (Submodule.map p Sc) := Submodule.span_mono hrangeM
        _ = Submodule.map p Sc := Submodule.span_eq _
    have hrangeK : i '' Set.range eK.1 ⊆ Set.range c := by
      rintro y ⟨a, ha, rfl⟩
      obtain ⟨j, rfl⟩ := ha
      exact ⟨Fin.castAdd (moduleLength R M) j, by simp [c, Fin.append_left]⟩
    have hCgen : Sc = ⊤ := by
      apply Submodule.eq_top_iff'.mpr
      intro y
      have hpy : p y ∈ Submodule.map p Sc := by rw [hmap]; exact Submodule.mem_top
      obtain ⟨z, hzS, hzy⟩ := Submodule.mem_map.mp hpy
      have hyker : y - z ∈ LinearMap.ker p := by rw [LinearMap.mem_ker, map_sub, hzy, sub_self]
      have hyi : y - z ∈ LinearMap.range i := by rwa [← LinearMap.exact_iff.mp hip]
      obtain ⟨k, hk⟩ := LinearMap.mem_range.mp hyi
      have hkgen : k ∈ Submodule.span R (Set.range eK.1) := by
        rw [heK]
        exact Submodule.mem_top
      have hkmap : i k ∈ Submodule.map i (Submodule.span R (Set.range eK.1)) :=
        Submodule.mem_map.mpr ⟨k, hkgen, rfl⟩
      rw [Submodule.map_span] at hkmap
      have hkmem : i k ∈ Sc := Submodule.span_mono hrangeK hkmap
      have := Sc.add_mem hkmem hzS
      rwa [hk, sub_add_cancel] at this
    have hrangeC : Set.range cseq = Set.range c := (finCongr hlen).surjective.range_comp c
    have houtgen : Submodule.span R (Set.range cseq) = ⊤ := by rwa [hrangeC]
    let eout : AdmissibleSequence R L := ⟨cseq, hadm⟩
    have houtne := symbol_ne_zero_of_span_eq_top hL eout houtgen
    apply houtne
    rw [← hvalue]
    change γ (symbol eK ⊗ₜ[κ] symbol eM) = 0
    rw [hγzero]
    simp
  exact LinearMap.bijective_of_ne_zero hγ

end Module.FiniteLength
end
