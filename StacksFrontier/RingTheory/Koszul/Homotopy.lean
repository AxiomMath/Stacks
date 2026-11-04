module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Linear
public import StacksFrontier.RingTheory.Koszul.Functoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Null-homotopy of multiplication on the Koszul complex

Let `R` be a commutative ring and `f : Fin r → R` a finite sequence in `R`. Multiplication
by any member `f i` of the sequence is null-homotopic as a chain endomorphism of the Koszul
complex `K_•(f₁, …, f_r)`: the homotopy is given in degree `n` by wedging on the left with
the `i`-th standard basis vector `Pi.single i 1`, and the homotopy identity is exactly the
Koszul relation `f i • a = d (eᵢ ∧ a) + eᵢ ∧ d a` of `koszul_scalar_eq_homotopy`
(Stacks Tag 0626).

Since a null-homotopic chain map induces the zero map on homology, while multiplication by
a scalar `a` induces multiplication by `a`, every homology module `H_n(K_•(f))` is
annihilated by each `f i`, hence by the whole ideal `(f₁, …, f_r)`.

## Main results

* `Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator`: multiplication by `f i` is
  null-homotopic on `Koszul.seqComplex f` for every `i`, and `Ideal.span (Set.range f)` is
  contained in the annihilator of `(Koszul.seqComplex f).homology n` for every `n`.

## Implementation notes

The sequence is represented by a function `Fin r → R`, its Koszul complex by
`Koszul.seqComplex f`, multiplication by a scalar by the scalar action `f i • 𝟙 _` on the
identity chain map, and the ideal it generates by `Ideal.span (Set.range f)`. The homotopy
in degree `n` is `Koszul.wedgeLeft i n`, left multiplication by
`ExteriorAlgebra.ι R (Pi.single i 1)` restricted to the exterior powers.

## References

* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
* [Stacks Project, Tag 0626](https://stacks.math.columbia.edu/tag/0626)
-/

@[expose] public section

open CategoryTheory
open scoped ExteriorAlgebra

namespace Koszul

/-- Left multiplication by the `i`-th standard basis vector of `Fin r → R`, restricted to a
map of exterior powers `⋀ⁿ → ⋀ⁿ⁺¹`. This is the degreewise component of the null-homotopy
of multiplication by `f i` on the Koszul complex. -/
@[ega "III 1.1.7" "special case"]
public noncomputable def wedgeLeft {R : Type*} [CommRing R] {r : ℕ}
    (i : Fin r) (n : ℕ) :
    (⋀[R]^n (Fin r → R)) →ₗ[R] (⋀[R]^(n + 1) (Fin r → R)) :=
  LinearMap.codRestrict _
    ((LinearMap.mulLeft R (ExteriorAlgebra.ι R (Pi.single i 1))).comp
      (⋀[R]^n (Fin r → R)).subtype)
    (fun x => by simpa [add_comm] using
      SetLike.mul_mem_graded (Koszul.ι_mem_one (Pi.single i 1)) x.2)

/-- The homotopy identity for `wedgeLeft`: contracting after wedging, plus wedging after
contracting, is multiplication by `f i`. This is `koszul_scalar_eq_homotopy` (Stacks Tag
0626) for the dual vector `Koszul.seqDual f` and the basis vector `Pi.single i 1`. -/
public lemma contraction_wedgeLeft_add_wedgeLeft_contraction
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R) (i : Fin r) (n : ℕ)
    (x : ⋀[R]^n (Fin r → R)) :
    Koszul.contraction (Koszul.seqDual f) (wedgeLeft i n x : ExteriorAlgebra R (Fin r → R)) +
        ExteriorAlgebra.ι R (Pi.single i 1) *
          Koszul.contraction (Koszul.seqDual f) (x : ExteriorAlgebra R (Fin r → R)) =
      f i • (x : ExteriorAlgebra R (Fin r → R)) := by
  simpa [wedgeLeft, add_comm] using
    (koszul_scalar_eq_homotopy (Koszul.seqDual f) (Pi.single i 1)
      (x : ExteriorAlgebra R (Fin r → R))).symm

/-- The Koszul differential vanishes on the exterior power `⋀⁰`, which consists of scalars. -/
public lemma contraction_zero_degree {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (x : ⋀[R]^0 (Fin r → R)) :
    Koszul.contraction (Koszul.seqDual f) (x : ExteriorAlgebra R (Fin r → R)) = 0 := by
  have hx : (x : ExteriorAlgebra R (Fin r → R)) ∈
      Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R 0)) := by
    rw [exteriorPower.ιMulti_span_fixedDegree]
    exact x.2
  refine Submodule.span_induction (fun y hy => ?_) (by simp) (fun _ _ _ _ hx hy => by simp [hx, hy])
    (fun _ _ _ hx => by simp [hx]) hx
  obtain ⟨v, rfl⟩ := hy
  simp [ExteriorAlgebra.ιMulti, Koszul.contraction]

set_option maxHeartbeats 800000 in
-- Normalizing the two compositions of restricted exterior-power maps is elaboration-intensive.
/-- Multiplication by `f i` on the Koszul complex of `f` is null-homotopic, the homotopy
being left multiplication by the `i`-th standard basis vector. -/
public theorem nullHomotopic {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (i : Fin r) : Nonempty (Homotopy (f i • 𝟙 (Koszul.seqComplex f)) 0) := by
  let h : ∀ n, (Koszul.seqComplex f).X n ⟶ (Koszul.seqComplex f).X (n + 1) :=
    fun n => ModuleCat.ofHom (wedgeLeft i n)
  refine ⟨{
    hom := fun n m => if e : n + 1 = m then h n ≫ eqToHom (by subst m; rfl) else 0
    zero := ?_
    comm := ?_ }⟩
  · exact fun n m hrel => dite_eq_right hrel
  · intro n
    rw [Homotopy.prevD_chainComplex]
    cases n with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex]
        simp only [zero_add]
        dsimp [h]
        apply ModuleCat.hom_ext
        ext x
        change (⋀[R]^0 (Fin r → R)) at x
        apply Subtype.ext
        simp only [add_zero, ModuleCat.hom_smul, ModuleCat.hom_id, Koszul.seqComplex_d]
        show f i • (x : ExteriorAlgebra R (Fin r → R)) =
          Koszul.contraction (Koszul.seqDual f)
            (wedgeLeft i 0 x : ExteriorAlgebra R (Fin r → R))
        simpa [contraction_zero_degree f x] using
          (contraction_wedgeLeft_add_wedgeLeft_contraction f i 0 x).symm
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex]
        dsimp [h]
        apply ModuleCat.hom_ext
        ext x
        change (⋀[R]^(n + 1) (Fin r → R)) at x
        apply Subtype.ext
        simp only [add_zero, ModuleCat.hom_smul, ModuleCat.hom_id, Koszul.seqComplex_d]
        show f i • (x : ExteriorAlgebra R (Fin r → R)) =
          ExteriorAlgebra.ι R (Pi.single i 1) *
              Koszul.contraction (Koszul.seqDual f) (x : ExteriorAlgebra R (Fin r → R)) +
            Koszul.contraction (Koszul.seqDual f)
              (wedgeLeft i (n + 1) x : ExteriorAlgebra R (Fin r → R))
        simpa [add_comm] using
          (contraction_wedgeLeft_add_wedgeLeft_contraction f i (n + 1) x).symm

/-- The map induced on homology by the scalar multiple `a • 𝟙 C` of the identity chain map
is multiplication by `a`. -/
public theorem homologyMap_smul_id {R : Type*} [CommRing R] (a : R)
    (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (a • 𝟙 C) n = a • 𝟙 _ := by
  have hcyc : HomologicalComplex.cyclesMap (a • 𝟙 C) n = a • 𝟙 _ := by
    rw [← cancel_mono (C.iCycles n), HomologicalComplex.cyclesMap_i]
    simp [Linear.smul_comp, Linear.comp_smul]
  rw [← cancel_epi (C.homologyπ n), HomologicalComplex.homologyπ_naturality, hcyc]
  simp [Linear.smul_comp, Linear.comp_smul]

/-- Multiplication by each member of a finite sequence is null-homotopic on its Koszul complex,
and the ideal generated by the sequence annihilates every Koszul homology module. -/
@[stacks 0663]
public theorem koszulSeq_smul_nullHomotopic_and_span_le_annihilator
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R) :
    (∀ i, Nonempty (Homotopy (f i • 𝟙 (Koszul.seqComplex f)) 0)) ∧
      ∀ n, Ideal.span (Set.range f) ≤
        Module.annihilator R ((Koszul.seqComplex f).homology n) := by
  refine ⟨nullHomotopic f, fun n => Ideal.span_le.2 ?_⟩
  rintro a ⟨i, rfl⟩
  apply Module.mem_annihilator.mpr
  intro x
  have H := Classical.choice (nullHomotopic f i)
  have hm := H.homologyMap_eq n
  rw [homologyMap_smul_id, HomologicalComplex.homologyMap_zero] at hm
  simpa using congrArg (fun q => q.hom x) hm

end Koszul

end
