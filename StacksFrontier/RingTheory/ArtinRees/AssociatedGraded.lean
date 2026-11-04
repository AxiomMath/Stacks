module

public import Mathlib.LinearAlgebra.Isomorphisms
public import StacksFrontier.RingTheory.ArtinRees.Constant
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# Associated graded modules of nearby cokernels

Let `A` be Noetherian, `I ⊆ A` contained in the Jacobson radical, and let
`L --f--> M --g--> N` and `L --f'--> M --g'--> N` be two complexes of finite `A`-modules that are
congruent modulo `I^(c+1)`, where `c` works for `f` and `g` in the Artin-Rees lemma and the first
complex is exact. Then the cokernels of `g` and of `g'` have the same associated graded module.

In degree `n` the two graded pieces are the subquotients
`I^n N / (I^(n+1) N + g(M) ∩ I^n N)` of `N`, and the Artin-Rees bound makes the two denominators
equal: an element of `g(M) ∩ I^n N` is `g a` with `a ∈ I^(n-c) M`, and `g a - g' a` lies in
`I^(n+1) N`. Assembling the degreewise isomorphisms gives an isomorphism of graded modules over
the associated graded ring, because the identification is induced by the identity of `N` and so
respects the graded scalar action.

## Main results

* `associatedGraded_coker_equiv_of_isArtinReesConstant`: the same comparison carrying only the
  hypotheses its proof uses, namely that `c` works for both `g` and `g'` and that the two maps
  agree modulo `I^{c+1}`.
* `associatedGraded_coker_equiv_of_congr`: the isomorphism of associated graded modules above.

## Implementation notes

The cokernel of a linear map is the quotient of `N` by its range, and the conclusion is an
`AssociatedGraded.GradedLinearEquiv`, so it carries compatibility with the scalar action of the
associated graded ring and preservation of homogeneous degrees. The congruence hypotheses are
`CongruentModPow I f f' (c + 1)` and `CongruentModPow I g g' (c + 1)`, matching
`artinRees_stability`, which supplies the Artin-Rees bound for `g'` that the symmetric half of the
denominator computation needs.

## References

* [Stacks Project, Tag 07VF](https://stacks.math.columbia.edu/tag/07VF)
-/

universe u v w x

open AssociatedGraded

private noncomputable def piecePresentation
    {A : Type u} [CommRing A] (I : Ideal A) {N : Type x}
    [AddCommGroup N] [Module A N] (R : Submodule A N) (n : ℕ) :
    ((power (M := N) I n) ⧸
        (power (M := N) I (n + 1) ⊔ R).comap (power I n).subtype) ≃ₗ[A]
      piece (M := N ⧸ R) I n := by
  let P := power (M := N) I n
  let Q := power (M := N ⧸ R) I n
  let φ : P →ₗ[A] Q :=
    (R.mkQ.domRestrict P).codRestrict Q fun z => mkQ_mem_power I R n z.property
  let F : P →ₗ[A] piece (M := N ⧸ R) I n :=
    ((power (M := N ⧸ R) I (n + 1)).comap Q.subtype).mkQ.comp φ
  have hsurjφ : Function.Surjective φ := by
    intro q
    obtain ⟨z, hz, eq⟩ : (q : N ⧸ R) ∈ P.map R.mkQ := by
      rw [map_mkQ_power]
      exact q.property
    exact ⟨⟨z, hz⟩, Subtype.ext eq⟩
  have hker : LinearMap.ker F =
      (power (M := N) I (n + 1) ⊔ R).comap P.subtype := by
    ext z
    simp only [LinearMap.mem_ker, F, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, φ]
    change R.mkQ (z : N) ∈ power (M := N ⧸ R) I (n + 1) ↔ _
    rw [← map_mkQ_power, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_comm]
    rfl
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective
    ((Submodule.mkQ_surjective _).comp hsurjφ))

set_option backward.isDefEq.respectTransparency false in
private theorem piecePresentation_mk
    {A : Type u} [CommRing A] (I : Ideal A) {N : Type x}
    [AddCommGroup N] [Module A N] (R : Submodule A N) (n : ℕ)
    (z : power (M := N) I n) :
    piecePresentation I R n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (⟨R.mkQ z, by
          change R.mkQ z ∈ power (M := N ⧸ R) I n
          rw [show power (M := N ⧸ R) I n =
              (power (M := N) I n).map R.mkQ by
            simp [power, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]]
          exact ⟨z, z.property, rfl⟩⟩ : power (M := N ⧸ R) I n) := by
  simp [piecePresentation]
  congr 1

private theorem range_inf_power_le
    {A : Type u} [CommRing A] (I : Ideal A) {M : Type w} {N : Type x}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (g g' : M →ₗ[A] N) (c n : ℕ) (hg : IsArtinReesConstant I g c)
    (hgg' : CongruentModPow I g g' (c + 1)) :
    LinearMap.range g ⊓ power (M := N) I n ≤
      power (M := N) I (n + 1) ⊔ LinearMap.range g' := by
  rintro _ ⟨⟨a, rfl⟩, hpow⟩
  unfold CongruentModPow at hgg'
  by_cases hn : n ≤ c
  · exact Submodule.mem_sup.mpr ⟨(g - g') a,
      Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl (hgg' ⟨a, rfl⟩),
      g' a, ⟨a, rfl⟩, by simp⟩
  obtain ⟨a', ha', hga'⟩ := hg.mem_map (by omega) hpow
  have hdiff : (g - g') a' ∈ power (M := N) I (n - c + c + 1) := by
    refine Submodule.smul_induction_on ha' ?_ ?_
    · intro r hr m _
      rw [map_smul]
      simpa [power, smul_smul, ← pow_add, add_assoc] using
        Submodule.smul_mem_smul hr (hgg' ⟨m, rfl⟩)
    · intro y z hy hz
      simpa only [map_add] using Submodule.add_mem _ hy hz
  refine Submodule.mem_sup.mpr ⟨(g - g') a', ?_, g' a', ⟨a', rfl⟩, ?_⟩
  · rwa [Nat.sub_add_cancel (by omega)] at hdiff
  · simp only [LinearMap.sub_apply]
    rw [hga']
    abel

/-- For `n` arbitrary, the two denominators `I^(n+1) N + g(M)` and `I^(n+1) N + g'(M)` cut the
same submodule out of `I^n N`, when `c` works for both `g` and `g'` and they agree modulo
`I^(c+1)`. -/
public theorem presentation_denominator_eq
    {A : Type u} [CommRing A] (I : Ideal A) {M : Type w} {N : Type x}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (g g' : M →ₗ[A] N) (c n : ℕ)
    (hg : IsArtinReesConstant I g c) (hg' : IsArtinReesConstant I g' c)
    (hgg' : CongruentModPow I g g' (c + 1)) :
    (power (M := N) I (n + 1) ⊔ LinearMap.range g).comap (power I n).subtype =
      (power (M := N) I (n + 1) ⊔ LinearMap.range g').comap (power I n).subtype := by
  have key : ∀ f f' : M →ₗ[A] N, IsArtinReesConstant I f c → CongruentModPow I f f' (c + 1) →
      (power (M := N) I (n + 1) ⊔ LinearMap.range f).comap (power I n).subtype ≤
        (power (M := N) I (n + 1) ⊔ LinearMap.range f').comap (power I n).subtype := by
    intro f f' hf hff' z hz
    obtain ⟨p, hp, r, hr, eq⟩ := Submodule.mem_sup.mp hz
    change p + r = (z : N) at eq
    have hrn : r ∈ LinearMap.range f ⊓ power (M := N) I n := by
      refine ⟨hr, ?_⟩
      have h := Submodule.sub_mem (power (M := N) I n) z.property (power_succ_le I n hp)
      rwa [← eq, add_sub_cancel_left] at h
    change (z : N) ∈ power (M := N) I (n + 1) ⊔ LinearMap.range f'
    rw [← eq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hp)
      (range_inf_power_le I f f' c n hf hff' hrn)
  exact le_antisymm (key g g' hg hgg') (key g' g hg' hgg'.symm)

/-- The degree `n` comparison of the associated graded modules of `N ⧸ R` and `N ⧸ S` induced by
the identity of `N`, given that the two denominators cut the same submodule out of `I^n N`. -/
public noncomputable def pieceEquiv
    {A : Type u} [CommRing A] (I : Ideal A) {N : Type x}
    [AddCommGroup N] [Module A N] (R S : Submodule A N) (n : ℕ)
    (h : (power (M := N) I (n + 1) ⊔ R).comap (power I n).subtype =
      (power (M := N) I (n + 1) ⊔ S).comap (power I n).subtype) :
    piece (M := N ⧸ R) I n ≃ₗ[A] piece (M := N ⧸ S) I n :=
  (piecePresentation I R n).symm |>.trans <|
    (Submodule.quotEquivOfEq _ _ h).trans (piecePresentation I S n)

set_option backward.isDefEq.respectTransparency false in
/-- `pieceEquiv` is induced by the identity of `N`: it carries the class of `z ∈ I^n N` modulo
`R` to the class of the same `z` modulo `S`. -/
public theorem pieceEquiv_mk
    {A : Type u} [CommRing A] (I : Ideal A) {N : Type x}
    [AddCommGroup N] [Module A N] (R S : Submodule A N) (n : ℕ)
    (h : (power (M := N) I (n + 1) ⊔ R).comap (power I n).subtype =
      (power (M := N) I (n + 1) ⊔ S).comap (power I n).subtype)
    (z : power (M := N) I n) :
    pieceEquiv I R S n h
        (mk I n ⟨R.mkQ z, by
          rw [show power (M := N ⧸ R) I n = (power (M := N) I n).map R.mkQ by
            simp [power, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]]
          exact ⟨z, z.property, rfl⟩⟩) =
      mk I n ⟨S.mkQ z, by
        rw [show power (M := N ⧸ S) I n = (power (M := N) I n).map S.mkQ by
          simp [power, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]]
        exact ⟨z, z.property, rfl⟩⟩ := by
  have hR := piecePresentation_mk I R n z
  have hS := piecePresentation_mk I S n z
  have hinv : (piecePresentation I R n).symm
      (mk I n ⟨R.mkQ z, mkQ_mem_power I R n z.property⟩) = Submodule.Quotient.mk z :=
    (piecePresentation I R n).symm_apply_eq.mpr hR
  simp only [pieceEquiv, LinearEquiv.trans_apply]
  rw [hinv, Submodule.quotEquivOfEq_mk]
  simpa [mk] using hS

/-- `pieceEquiv` commutes with the action of the homogeneous classes of `Gr_I(A)`, because it is
induced by the identity of `N`. -/
public theorem pieceEquiv_homogeneousSMul
    {A : Type u} [CommRing A] (I : Ideal A) {N : Type x}
    [AddCommGroup N] [Module A N] (R S : Submodule A N) (i j : ℕ)
    (hj : (power (M := N) I (j + 1) ⊔ R).comap (power I j).subtype =
      (power (M := N) I (j + 1) ⊔ S).comap (power I j).subtype)
    (hij : (power (M := N) I (i + j + 1) ⊔ R).comap (power I (i + j)).subtype =
      (power (M := N) I (i + j + 1) ⊔ S).comap (power I (i + j)).subtype)
    (a : piece (M := A) I i) (x : piece (M := N ⧸ R) I j) :
    pieceEquiv I R S (i + j) hij (homogeneousSMul I a x) =
      homogeneousSMul I a (pieceEquiv I R S j hj x) := by
  obtain ⟨m₀, rfl⟩ := exists_eq_mk_mkQ I R j x
  induction a using Quotient.inductionOn with
  | _ a =>
    have hej := pieceEquiv_mk I R S j hj m₀
    have hep := pieceEquiv_mk I R S (i + j) hij
      ⟨(a : A) • (m₀ : N), smul_mem_power I a.property m₀.property⟩
    change pieceEquiv I R S (i + j) hij
        (homogeneousSMul I (mk I i a) (mk I j ⟨R.mkQ m₀, _⟩)) =
      homogeneousSMul I (mk I i a) (pieceEquiv I R S j hj (mk I j ⟨R.mkQ m₀, _⟩))
    rw [hej, homogeneousSMul_mk, homogeneousSMul_mk]
    simp only [Submodule.mkQ_apply]
    convert hep
    · exact (R.mkQ.map_smul (a : A) m₀).symm
    · exact (S.mkQ.map_smul (a : A) m₀).symm

/-- The graded comparison underlying **Stacks 07VF**, carrying only the hypotheses its proof uses:
if `c` works in the Artin-Rees lemma for both `g` and `g'` and the two maps agree modulo
`I^{c+1}`, then `coker g` and `coker g'` have isomorphic associated graded modules over
`Gr_I(A)`. Degree `n` of either is the subquotient `I^n N / (I^{n+1} N + g(M) ∩ I^n N)` of `N`,
and the two denominators coincide. -/
public noncomputable def associatedGraded_coker_equiv_of_isArtinReesConstant
    {A : Type u} [CommRing A] (I : Ideal A) {M : Type w} {N : Type x}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (g g' : M →ₗ[A] N) (c : ℕ)
    (hg : IsArtinReesConstant I g c) (hg' : IsArtinReesConstant I g' c)
    (hgg' : CongruentModPow I g g' (c + 1)) :
    AssociatedGraded.GradedLinearEquiv I
      (N ⧸ LinearMap.range g) (N ⧸ LinearMap.range g') :=
  AssociatedGraded.GradedLinearEquiv.ofPieceEquiv I
    (fun n => pieceEquiv I _ _ n (presentation_denominator_eq I g g' c n hg hg' hgg'))
    fun i j a x => pieceEquiv_homogeneousSMul I _ _ i j _ _ a x

/-- **Stacks 07VF.** With the hypotheses of `artinRees_stability`, the cokernels of the two
nearby maps `g` and `g'` have isomorphic associated graded modules over the associated graded
ring of `I`. -/
@[stacks 07VF]
public noncomputable def associatedGraded_coker_equiv_of_congr
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson)
    {L : Type v} {M : Type w} {N : Type x}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module A L] [Module A M] [Module A N]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A N]
    (f : L →ₗ[A] M) (g : M →ₗ[A] N) (f' : L →ₗ[A] M) (g' : M →ₗ[A] N)
    (c : ℕ)
    (hS'c : g'.comp f' = 0)
    (hf : IsArtinReesConstant I f c) (hg : IsArtinReesConstant I g c)
    (hexact : LinearMap.ker g = LinearMap.range f)
    (hff' : CongruentModPow I f f' (c + 1)) (hgg' : CongruentModPow I g g' (c + 1)) :
    AssociatedGraded.GradedLinearEquiv I
      (N ⧸ LinearMap.range g) (N ⧸ LinearMap.range g') :=
  associatedGraded_coker_equiv_of_isArtinReesConstant I g g' c hg
    (artinRees_stability I hI f f' g g' c hS'c hf hg hexact hff' hgg').1 hgg'
