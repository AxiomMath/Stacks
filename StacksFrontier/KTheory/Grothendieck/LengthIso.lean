module

public import StacksFrontier.KTheory.Grothendieck.Artinian
public import StacksFrontier.KTheory.Grothendieck.Product.BaseChange

/-!
# `K'_0` of an Artinian local ring is `ℤ`

Let `R` be an Artinian local ring.

* Stacks 00JI: the length homomorphism `length_R : K'_0(R) → ℤ` of Stacks 00JD (`lengthHom R`)
  is an isomorphism (`K0prime.lengthHom_isIso`). Surjectivity comes from the residue field,
  of length `1`; injectivity from `K0prime.mkModule_eq_length_smul`: the class of a finite
  module of length `n` is `n` times the class of the residue field, proved by splitting off a
  simple quotient `M ⧸ N ≅ ResidueField R` along a maximal submodule `N`.
* Stacks 00JK: the square formed by `K0.toK0prime : K_0(R) → K'_0(R)`, the rank and length
  isomorphisms to `ℤ`, and multiplication by `length_R(R)` commutes (`K0.toK0prime_comm`).
-/

@[expose] public section

open IsLocalRing

/-! ### `length_R : K'_0(R) → ℤ` is an isomorphism -/

universe u

namespace K0prime

variable {R : Type u} [CommRing R]

/-- The class of a presentation is the class of its module. -/
lemma mk_eq_mkModule (P : FGPres R) : K0prime.mk P = K0prime.mkModule R P.module := by
  obtain ⟨e⟩ := (FGPres.skeleton_surjective (R := R) P.module).choose_spec
  exact QuotientAddGroup.eq_iff_sub_mem.2
    (AddSubgroup.subset_closure (K0Rel.iso _ _ e.symm))

/-- A finite module with at most one element has class `0` in `K'_0(R)`. -/
lemma mkModule_eq_zero_of_subsingleton (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M] : K0prime.mkModule R M = 0 := by
  have h := K0prime.mkModule_add_of_ses M M M LinearMap.id (0 : M →ₗ[R] M)
    Function.injective_id (fun y => ⟨y, Subsingleton.elim _ _⟩)
    (fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => Subsingleton.elim _ _⟩)
  exact (add_eq_left.mp h.symm)

/-- The class of a direct sum in `K'_0(R)` is the sum of the classes. -/
lemma mkModule_prod (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    K0prime.mkModule R (M × N) = K0prime.mkModule R M + K0prime.mkModule R N :=
  K0prime.mkModule_add_of_ses (M × N) M N (LinearMap.inl R M N) (LinearMap.snd R M N)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd

/-- A simple module over a local ring is isomorphic to the residue field. -/
lemma _root_.IsLocalRing.nonempty_linearEquiv_residueField_of_isSimpleModule
    [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    Nonempty (M ≃ₗ[R] ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R M›
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  exact ⟨e.trans (LinearEquiv.refl R (ResidueField R))⟩

variable [IsArtinianRing R] [IsLocalRing R]

/-- Over an Artinian local ring, the class in `K'_0(R)` of a finite module of length `n` is `n`
times the class of the residue field. -/
theorem mkModule_eq_length_smul (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hM : Module.length R M = n) :
    K0prime.mkModule R M = (n : ℤ) • K0prime.mkModule R (ResidueField R) := by
  induction n generalizing M with
  | zero =>
    have : Subsingleton M := Module.length_eq_zero_iff.mp (by simpa using hM)
    simp [mkModule_eq_zero_of_subsingleton]
  | succ n ih =>
    have : Nontrivial M := Module.length_pos_iff.mp (by rw [hM]; exact_mod_cast n.succ_pos)
    obtain ⟨N, hN, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left
      bot_ne_top
    have : IsSimpleModule R (M ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
    have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
    have : Module.Finite R N := Module.IsNoetherian.finite R N
    have hses := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one R (M ⧸ N), hM] at hses
    have hfinN : Module.length R N ≠ ⊤ := by
      intro h
      rw [h, top_add] at hses
      exact ENat.natCast_ne_top _ hses
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinN
    rw [← hm] at hses
    have hmn : n + 1 = m + 1 := by exact_mod_cast hses
    have hN' : Module.length R N = n := by rw [← hm, show m = n by omega]
    obtain ⟨e⟩ := IsLocalRing.nonempty_linearEquiv_residueField_of_isSimpleModule (R := R) (M ⧸ N)
    rw [K0prime.mkModule_add_of_ses M N (M ⧸ N) N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), ih N hN',
      K0prime.mkModule_eq_of_iso _ _ e]
    push_cast
    rw [add_smul, one_smul]

/-- The length homomorphism sends the class of a finite module to its length. -/
theorem lengthHom_mkModule (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    lengthHom R (K0prime.mkModule R M) = ((Module.length R M).toNat : ℤ) := by
  obtain ⟨e⟩ := (FGPres.skeleton_surjective (R := R) M).choose_spec
  rw [K0prime.mkModule, lengthHom_mk, lengthOfPresℤ, e.length_eq]

/-- The residue field has class of length `1`. -/
lemma lengthHom_mkModule_residueField :
    lengthHom R (K0prime.mkModule R (ResidueField R)) = 1 := by
  rw [lengthHom_mkModule, length_residueField_eq_one]
  simp

/-- Every element of `K'_0(R)` is its length times the class of the residue field. -/
theorem eq_lengthHom_smul (x : K0prime R) :
    x = lengthHom R x • K0prime.mkModule R (ResidueField R) := by
  refine QuotientAddGroup.induction_on x fun y => ?_
  refine FreeAbelianGroup.induction_on y ?_ ?_ ?_ ?_
  · simp
  · intro P
    have hfin : Module.length R P.module ≠ ⊤ := by
      have : IsArtinian R P.module := isArtinian_of_tower R inferInstance
      have : IsNoetherian R P.module := isNoetherian_of_isNoetherianRing_of_finite R P.module
      exact Module.length_ne_top
    change K0prime.mk P = lengthHom R (K0prime.mk P) • _
    rw [mk_eq_mkModule, lengthHom_mkModule]
    exact mkModule_eq_length_smul _ _ (ENat.natCast_toNat hfin).symm
  · intro P hP
    rw [QuotientAddGroup.mk_neg, map_neg, neg_smul, ← hP]
  · intro y z hy hz
    rw [QuotientAddGroup.mk_add, map_add, add_smul, ← hy, ← hz]

/-- **Stacks 00JI.** Let `R` be an Artinian local ring. The length homomorphism
`length_R : K'_0(R) → ℤ` of Stacks 00JD (`lengthHom R`, sending the class of a finite module
to its length) is an isomorphism. -/
@[stacks 00JI]
theorem lengthHom_isIso : ∃ e : K0prime R ≃+ ℤ, ⇑e = lengthHom R :=
  ⟨{ toFun := lengthHom R
     invFun := fun z => z • K0prime.mkModule R (ResidueField R)
     left_inv := fun x => (eq_lengthHom_smul x).symm
     right_inv := fun z => by
       simp [map_zsmul, lengthHom_mkModule_residueField]
     map_add' := map_add _ }, rfl⟩

/-- The length homomorphism `K'_0(R) → ℤ` of an Artinian local ring is bijective. -/
theorem lengthHom_bijective : Function.Bijective (lengthHom R) := by
  obtain ⟨e, he⟩ := lengthHom_isIso (R := R)
  rw [← he]
  exact e.bijective

end K0prime

/-! ### The map `K_0(R) → K'_0(R)` and the diagram for an Artinian local ring -/

namespace K0

variable (R : Type u) [CommRing R]

/-- The canonical homomorphism `K_0(R) → K'_0(R)` sending the class of a finite projective
module to its class as a finite module. -/
noncomputable def toK0prime : K0 R →+ K0prime R :=
  QuotientAddGroup.lift (K0.rels R)
    (FreeAbelianGroup.lift fun M : FGProj R => K0prime.mkModule R M.carrier) <| by
    refine AddSubgroup.closure_le _ |>.2 ?_
    rintro y (⟨M, N, rfl⟩ | ⟨M, N, ⟨e⟩, rfl⟩)
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      change K0prime.mkModule R (M.carrier × N.carrier) - _ - _ = 0
      rw [K0prime.mkModule_prod]
      abel
    · simp [K0prime.mkModule_eq_of_iso _ _ e]

/-- `toK0prime` sends the class of a finite projective module to its class in `K'_0(R)`. -/
@[simp]
theorem toK0prime_mk (M : FGProj R) :
    toK0prime R (K0.mk M) = K0prime.mkModule R M.carrier :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **Stacks 00JK.** Let `R` be a local Artinian ring. The diagram
$$
\begin{array}{ccc}
K_0(R) & \to & K_0'(R) \\
\text{rank}_R \downarrow & & \downarrow \text{length}_R \\
\mathbf{Z} & \xrightarrow{\text{length}_R(R)} & \mathbf{Z}
\end{array}
$$
commutes, and its vertical maps are isomorphisms: `K0.rank R` and `lengthHom R` are bijective,
and `length_R ∘ (K_0(R) → K'_0(R)) = length_R(R) · rank_R`.

Here `K_0(R)` (`K0 R`) is presented by direct-sum relations; since short exact sequences of
projective modules split, these are the relations of the Stacks definition. -/
@[stacks 00JK]
theorem toK0prime_comm [IsLocalRing R] [IsArtinianRing R] :
    Function.Bijective (K0.rank R) ∧ Function.Bijective (lengthHom R) ∧
      (lengthHom R).comp (toK0prime R) =
        (AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp (K0.rank R) := by
  refine ⟨?_, K0prime.lengthHom_bijective, ?_⟩
  · obtain ⟨e, he⟩ := K0.rank_isIso R
    rw [← he]
    exact e.bijective
  · refine QuotientAddGroup.addMonoidHom_ext _ ?_
    ext M
    change lengthHom R (toK0prime R (K0.mk M)) = ((Module.length R R).toNat : ℤ) *
      K0.rank R (K0.mk M)
    rw [toK0prime_mk, K0prime.lengthHom_mkModule, K0.rank_mk, FGProj.rank,
      length_eq_finrank_mul_length_self R M.carrier, ENat.toNat_mul, ENat.toNat_natCast]
    push_cast
    ring

end K0
