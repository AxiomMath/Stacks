module

public import Mathlib.FieldTheory.MvRatFunc.Rank
public import StacksCore.FieldTheory.AlgebraicClosure
public import StacksCore.FieldTheory.MvRatFunc.Algebra
public import StacksCore.FieldTheory.PurelyTranscendental

/-!
# A purely transcendental extension is relatively algebraically closed

A field is algebraically closed in a purely transcendental extension of it: an element of
`MvRatFunc σ k` algebraic over `k` generates a finite subextension, and every finite
subextension of `MvRatFunc σ k` is trivial, because passing from `k` to it does not change the
rational function field.

Pure transcendence is also transported here along a pair of ring isomorphisms forming a
commutative square with the two algebra maps; this is the form in which Tag 057K moves the
purely transcendental residue field extension of Tag 052E across the identifications made by its
étale neighbourhoods, where no common base field is available to make the isomorphisms algebra
maps.

## Main results

* `IsAlgClosedIn.of_purelyTranscendental`: a field is algebraically closed in any purely
  transcendental extension of it.
* `PurelyTranscendental.of_ringEquiv_square`: transport of pure transcendence along a
  commutative square of ring isomorphisms.

## Implementation notes

The key computation is `Module.finrank k L = 1` for a finite subextension `L` of
`MvRatFunc σ k`: the rank of `MvRatFunc σ L` over `MvRatFunc σ k` equals the rank of `L` over
`k` by Tag 0G1M, while `MvRatFunc σ L` is isomorphic to `MvRatFunc σ k` as a
`MvRatFunc σ k`-algebra, because the variables are already algebraically independent over `L`
inside `MvRatFunc σ k` and generate it.

## References

* [Stacks Project, Tag 037I](https://stacks.math.columbia.edu/tag/037I)
* [Stacks Project, Tag 030E](https://stacks.math.columbia.edu/tag/030E)
* [Stacks Project, Tag 0G1M](https://stacks.math.columbia.edu/tag/0G1M)
-/

@[expose] public section

open IntermediateField

universe u

/-- The rational function field over a finite subextension of a rational function field is
finite over the rational function field of the base. -/
private theorem finite_mvRatFunc_of_finite (k L σ : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] :
    let : Algebra (MvRatFunc σ k) (MvRatFunc σ L) := MvRatFunc.algebra k L σ
    Module.Finite (MvRatFunc σ k) (MvRatFunc σ L) := by
  let : Algebra (MvRatFunc σ k) (MvRatFunc σ L) := MvRatFunc.algebra k L σ
  exact (MvRatFunc.finite_iff k L σ).mpr inferInstance

/-- The variables of `MvRatFunc σ k` are algebraically independent over `k`. -/
theorem MvRatFunc.algebraicIndependent_algebraMap_X (k σ : Type u) [Field k] :
    AlgebraicIndependent k
      (fun i : σ ↦ algebraMap (MvPolynomial σ k) (MvRatFunc σ k) (MvPolynomial.X i)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have heval : MvPolynomial.aeval (fun i : σ ↦ algebraMap (MvPolynomial σ k) (MvRatFunc σ k)
      (MvPolynomial.X i)) = IsScalarTower.toAlgHom k (MvPolynomial σ k) (MvRatFunc σ k) := by
    ext i
    simp
  rw [heval]
  exact IsFractionRing.injective (MvPolynomial σ k) (MvRatFunc σ k)

/-- For a finite subextension `L` of `MvRatFunc σ k`, the variables stay algebraically
independent over `L` and generate, so `MvRatFunc σ L` is `MvRatFunc σ k` itself. -/
private theorem exists_mvRatFunc_equiv (k : Type u) [Field k] (σ : Type u)
    (L : IntermediateField k (MvRatFunc σ k)) [FiniteDimensional k L] :
    let : Algebra (MvRatFunc σ k) (MvRatFunc σ L) := MvRatFunc.algebra k L σ
    Nonempty (MvRatFunc σ L ≃ₐ[MvRatFunc σ k] MvRatFunc σ k) := by
  classical
  let M := MvRatFunc σ k
  let x : σ → M := fun i ↦ algebraMap (MvPolynomial σ k) M (MvPolynomial.X i)
  have : Algebra.IsAlgebraic k L := inferInstance
  let : Algebra L M := L.val.toRingHom.toAlgebra
  let : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let q : MvPolynomial σ L →ₐ[L] M := MvPolynomial.aeval x
  have hq : Function.Injective q := algebraicIndependent_iff_injective_aeval.mp
    ((MvRatFunc.algebraicIndependent_algebraMap_X k σ).extendScalars L)
  let M' := MvRatFunc σ L
  let : Algebra L M' :=
    ((algebraMap (MvPolynomial σ L) M').comp (algebraMap L (MvPolynomial σ L))).toAlgebra
  let : SMul L M' := Algebra.toSMul
  let : Algebra (MvRatFunc σ k) M' := MvRatFunc.algebra k L σ
  let : IsScalarTower k (MvPolynomial σ L) M' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower L (MvPolynomial σ L) M' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let j₀ : M' →ₐ[L] M := IsFractionRing.liftAlgHom hq
  let : IsScalarTower k L (MvPolynomial σ L) := inferInstance
  let : IsScalarTower k L M' := IsScalarTower.to₁₂₄ k L (MvPolynomial σ L) M'
  have hj₀ (p : MvPolynomial σ k) :
      j₀ (algebraMap M M' (algebraMap (MvPolynomial σ k) M p)) =
        MvPolynomial.aeval x (MvPolynomial.map (algebraMap k L) p) := by
    have : algebraMap M M' (algebraMap (MvPolynomial σ k) M p) =
        algebraMap (MvPolynomial σ L) M' (MvPolynomial.map (algebraMap k L) p) := by
      simp [M, M']
    rw [this]
    exact IsFractionRing.lift_algebraMap hq _
  let j : M' →ₐ[M] M :=
    { toRingHom := j₀.toRingHom
      commutes' := by
        intro r
        have hbase : j₀.toRingHom.comp (algebraMap M M') = RingHom.id M := by
          apply MvRatFunc.ext_ringHom
          · ext a
            have := hj₀ (.C a)
            rw [MvPolynomial.map_C, MvPolynomial.aeval_C] at this
            exact this.trans (IsScalarTower.algebraMap_apply k L M a).symm
          · intro i
            simpa [x] using hj₀ (.X i)
        exact RingHom.congr_fun hbase r }
  have hj : Function.Bijective j := by
    refine ⟨j.injective, fun m ↦ ⟨algebraMap M M' m, ?_⟩⟩
    simp [j]
  exact ⟨AlgEquiv.ofBijective j hj⟩

/-- A finite subextension of a rational function field is trivial. -/
private theorem finrank_intermediateField_mvRatFunc_eq_one (k : Type u) [Field k] (σ : Type u)
    (L : IntermediateField k (MvRatFunc σ k)) [FiniteDimensional k L] :
    Module.finrank k L = 1 := by
  let M := MvRatFunc σ k
  let M' := MvRatFunc σ L
  let : Algebra M M' := MvRatFunc.algebra k L σ
  obtain ⟨e⟩ := exists_mvRatFunc_equiv k σ L
  have hfin : Module.Finite M M' := finite_mvRatFunc_of_finite k L σ
  have hrank : Module.rank M M' = Cardinal.lift.{u} (Module.rank k L) :=
    Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R := k) (S := L) σ
  have hcast : (Module.finrank M M' : Cardinal) = Module.finrank k L := by
    apply Cardinal.lift_injective.{u}
    simpa only [← Module.finrank_eq_rank, Cardinal.lift_natCast] using hrank
  calc
    Module.finrank k L = Module.finrank M M' := by exact_mod_cast hcast.symm
    _ = Module.finrank M M := e.toLinearEquiv.finrank_eq
    _ = 1 := Module.finrank_self M

/-- A field is algebraically closed in the rational function field over it. -/
private theorem isAlgClosedIn_mvRatFunc (k : Type u) [Field k] (σ : Type u) :
    IsAlgClosedIn k (MvRatFunc σ k) := by
  rw [IsAlgClosedIn, eq_bot_iff]
  intro z hz
  rw [mem_algebraicClosure_iff] at hz
  let M := MvRatFunc σ k
  let L : IntermediateField k M := IntermediateField.adjoin k ({z} : Set M)
  have : FiniteDimensional k L := IntermediateField.adjoin.finiteDimensional hz.isIntegral
  exact (IntermediateField.finrank_eq_one_iff.mp
    (finrank_intermediateField_mvRatFunc_eq_one k σ L)) ▸
      (subset_adjoin k ({z} : Set M) (Set.mem_singleton z) : z ∈ L)

/-- **Stacks Project, Tag 037I.** A field is algebraically closed in every purely transcendental
extension of it. -/
theorem IsAlgClosedIn.of_purelyTranscendental (k K : Type u) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] : IsAlgClosedIn k K := by
  obtain ⟨σ, ⟨e⟩⟩ := PurelyTranscendental.exists_algEquiv_mvRatFunc k K
  have h := isAlgClosedIn_mvRatFunc k σ
  rw [IsAlgClosedIn] at h ⊢
  rw [← algebraicClosure.map_eq_of_algEquiv e, h]
  exact IntermediateField.map_bot _

/-- **Stacks Project, Tag 030E.** Pure transcendence transports along a commutative square of
ring isomorphisms: no common base field is needed, only that the two algebra maps are
intertwined. -/
theorem PurelyTranscendental.of_ringEquiv_square {k K k' K' : Type u} [Field k] [Field K]
    [Field k'] [Field K'] [Algebra k K] [Algebra k' K'] (e : k ≃+* k') (E : K ≃+* K')
    (hc : (algebraMap k' K').comp e.toRingHom = E.toRingHom.comp (algebraMap k K))
    [PurelyTranscendental k K] : PurelyTranscendental k' K' := by
  obtain ⟨s, hs, hgen⟩ := PurelyTranscendental.exists_basis k K
  have hv : AlgebraicIndependent k (Subtype.val : s → K) := hs
  refine PurelyTranscendental.of_algebraicIndependent
    (hv.ringHom_of_comp_eq e E e.surjective E.injective hc) ?_
  let L' := IntermediateField.adjoin k' (Set.range (E ∘ (Subtype.val : s → K)))
  let L : IntermediateField k K :=
    { L'.toSubfield.comap E.toRingHom with
      algebraMap_mem' := fun a ↦ by
        change E (algebraMap k K a) ∈ L'
        rw [show E (algebraMap k K a) = algebraMap k' K' (e a) from (RingHom.congr_fun hc a).symm]
        exact L'.algebraMap_mem (e a) }
  have hL : IntermediateField.adjoin k s ≤ L := by
    rw [IntermediateField.adjoin_le_iff]
    exact fun z hz ↦ IntermediateField.subset_adjoin k' _ ⟨⟨z, hz⟩, rfl⟩
  rw [hgen] at hL
  refine top_unique fun z _ ↦ ?_
  obtain ⟨w, rfl⟩ := E.surjective z
  exact hL (IntermediateField.mem_top : w ∈ (⊤ : IntermediateField k K))

end
