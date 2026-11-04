module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ZeroDivisorsNilpotentDense

/-!
# Zero divisors of `Γ(U) ⊗[k] κ` for an affine open of a group scheme

Let `k` be a field of characteristic zero, `G` a geometrically irreducible group scheme over `k`,
`U ⊆ G` an affine open and `κ` a field extension of `k`.  Every zero divisor of `Γ(U) ⊗[k] κ` is
nilpotent.  This is the hypothesis on the rings of affine opens under which the stabilisers of
rational functions are representable (Perrin, thèse, I §2–3): the content lemma
`TensorProduct.mem_nonZeroDivisors_of_forall_not_isNilpotent` asks it of every fibre.

## Main results

* `ZeroDivisorsNilpotent.of_isPrime_nilradical`: a ring with irreducible spectrum whose local
  rings have nilpotent zero divisors has nilpotent zero divisors (Perrin, I 1.6).
* `AlgebraicGeometry.zeroDivisorsNilpotent_tensor_of_isOpenImmersion`: the statement for any
  `k`-algebra `A` with an open immersion `Spec A ⟶ G` over `k`.
* `AlgebraicGeometry.zeroDivisorsNilpotent_tensor_of_isAffineOpen`: the statement for an affine
  open `U` of `G`, with `Γ(G, U)` a `k`-algebra through the structure morphism.

## Implementation notes

`Spec (A ⊗[k] κ)` is the fibre product `Spec A ×_k Spec κ` (`AlgebraicGeometry.pullbackSpecIso`),
an open subscheme of the base change `G_κ`, which is irreducible because `G` is geometrically
irreducible and is a group scheme over `κ` (`AlgebraicGeometry.GroupScheme.baseChange`).  So the
spectrum of `A ⊗[k] κ` is irreducible, and its local rings are local rings of `G_κ`, whose zero
divisors are nilpotent by `AlgebraicGeometry.zeroDivisorsNilpotent_stalk_of_charZero`.
-/

@[expose] public section

open CategoryTheory Limits TensorProduct

universe u

/-- **Perrin, I 1.6.** A ring whose nilradical is prime and all of whose local rings have
nilpotent zero divisors has nilpotent zero divisors.  If `b r = 0` with `b ≠ 0`, the annihilator
of `b` lies in a maximal ideal `𝔭`, where `b` survives; so `r` is a zero divisor of `A_𝔭`, hence
`s r ^ n = 0` for some `s ∉ 𝔭`, and primality of the nilradical puts `r` in it. -/
theorem ZeroDivisorsNilpotent.of_isPrime_nilradical {A : Type*} [CommRing A]
    (hnil : (nilradical A).IsPrime)
    (hA : ∀ (p : Ideal A) [p.IsPrime], ZeroDivisorsNilpotent (Localization.AtPrime p)) :
    ZeroDivisorsNilpotent A := by
  intro r hr
  rw [mem_nonZeroDivisors_iff_right] at hr
  push Not at hr
  obtain ⟨b, hbr, hb⟩ := hr
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (Submodule.annihilator (Ideal.span {b}) :
    Ideal A) (by
      intro h
      apply hb
      have : (1 : A) ∈ Submodule.annihilator (Ideal.span {b}) := h ▸ Submodule.mem_top
      rw [Submodule.mem_annihilator_span_singleton] at this
      simpa using this)
  have hb' : algebraMap A (Localization.AtPrime p) b ≠ 0 := by
    intro h0
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ _).1 h0
    exact hs (hle (by rw [Submodule.mem_annihilator_span_singleton]; exact hsb))
  have hzd : algebraMap A (Localization.AtPrime p) r ∉ nonZeroDivisors _ := by
    rw [mem_nonZeroDivisors_iff_right]
    push Not
    exact ⟨_, by rw [← map_mul, hbr, map_zero], hb'⟩
  obtain ⟨n, hn⟩ := hA p _ hzd
  rw [← map_pow] at hn
  obtain ⟨⟨s, hs⟩, hsr⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ _).1 hn
  have hmem : s * r ^ n ∈ nilradical A := by rw [hsr]; exact (nilradical A).zero_mem
  rcases hnil.mem_or_mem hmem with h | h
  · exact absurd (nilradical_le_prime p h) hs
  · exact (mem_nilradical.1 (hnil.mem_of_pow_mem n h))

namespace AlgebraicGeometry

/-- **Zero divisors of `A ⊗[k] κ` are nilpotent** when `Spec A` is an open subscheme of a
geometrically irreducible group scheme `G` over a field `k` of characteristic zero: `Spec (A ⊗ κ)`
is an open subscheme of the irreducible group scheme `G_κ`. -/
theorem zeroDivisorsNilpotent_tensor_of_isOpenImmersion (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) [GeometricallyIrreducible G.X.hom]
    (A : Type u) [CommRing A] [Algebra k A] (j : Spec (CommRingCat.of A) ⟶ G.X.left)
    [IsOpenImmersion j] (hj : j ≫ G.X.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (κ : Type u) [Field κ] [Algebra k κ] : ZeroDivisorsNilpotent (A ⊗[k] κ) := by
  rcases subsingleton_or_nontrivial (A ⊗[k] κ) with hB | hB
  · exact fun r _ => ⟨1, Subsingleton.elim _ _⟩
  set fκ := Spec.map (CommRingCat.ofHom (algebraMap k κ))
  set fA := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have : CharZero κ := charZero_of_injective_algebraMap (algebraMap k κ).injective
  have : IrreducibleSpace (pullback G.X.hom fκ : Scheme.{u}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := G.X.hom) fκ (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  -- the open immersion `Spec A ×_k Spec κ ⟶ G_κ`
  let φ : pullback fA fκ ⟶ pullback G.X.hom fκ :=
    pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by rw [hj, Category.comp_id]) (by simp)
  have hsq : IsPullback φ (pullback.fst fA fκ) (pullback.fst G.X.hom fκ) j := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.X.hom fκ) (h₂₂ := G.X.hom) (v₁₃ := fκ)
      ?_ (by simp only [φ, pullback.map]; exact pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback G.X.hom fκ).flip
    have h1 : φ ≫ pullback.snd G.X.hom fκ = pullback.snd fA fκ := by
      simp only [φ, pullback.map]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    rw [h1, hj]
    exact (IsPullback.of_hasPullback fA fκ).flip
  have : IsOpenImmersion φ := MorphismProperty.of_isPullback hsq.flip ‹IsOpenImmersion j›
  let ψ : Spec (CommRingCat.of (A ⊗[k] κ)) ⟶ pullback G.X.hom fκ :=
    (pullbackSpecIso k A κ).inv ≫ φ
  -- irreducibility
  have : IrreducibleSpace (Spec (CommRingCat.of (A ⊗[k] κ))) :=
    ψ.isOpenEmbedding.irreducibleSpace
  refine ZeroDivisorsNilpotent.of_isPrime_nilradical
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 ‹_›) fun Q _ => ?_
  let x : Spec (CommRingCat.of (A ⊗[k] κ)) := ⟨Q, inferInstance⟩
  refine ZeroDivisorsNilpotent.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of (A ⊗[k] κ)) x).symm.commRingCatIsoToRingEquiv ?_
  exact ZeroDivisorsNilpotent.of_ringEquiv
    (asIso (ψ.stalkMap x)).symm.commRingCatIsoToRingEquiv
    (zeroDivisorsNilpotent_stalk_of_charZero κ ((GroupScheme.baseChange fκ).obj G) (ψ x))

/-- **Zero divisors of `Γ(G, U) ⊗[k] κ` are nilpotent** for an affine open `U` of a
geometrically irreducible group scheme `G` over a field `k` of characteristic zero and any field
extension `κ` of `k`.  The `k`-algebra structure on `Γ(G, U)` is any one whose structure map is
the composite `k ≅ Γ(Spec k) ⟶ Γ(G, U)` of the structure morphism of `G`. -/
theorem zeroDivisorsNilpotent_tensor_of_isAffineOpen (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) [GeometricallyIrreducible G.X.hom]
    {U : G.X.left.Opens} (hU : IsAffineOpen U) [Algebra k Γ(G.X.left, U)]
    (halg : CommRingCat.ofHom (algebraMap k Γ(G.X.left, U)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ G.X.hom.appLE ⊤ U (by simp))
    (κ : Type u) [Field κ] [Algebra k κ] : ZeroDivisorsNilpotent (Γ(G.X.left, U) ⊗[k] κ) := by
  refine zeroDivisorsNilpotent_tensor_of_isOpenImmersion k G Γ(G.X.left, U) hU.fromSpec ?_ κ
  have h := IsAffineOpen.SpecMap_appLE_fromSpec G.X.hom (isAffineOpen_top _) hU
    (U := ⊤) (V := U) (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, halg, Spec.map_comp]

end AlgebraicGeometry

end
