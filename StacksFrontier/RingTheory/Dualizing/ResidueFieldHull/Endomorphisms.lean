module

public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull.PowerTorsionFiltration

/-!
# The endomorphism ring of the injective hull of the residue field

Let `R` be a Noetherian local ring and let `E` be an injective hull of its residue field,
presented by an essential monomorphism `i : κ ⟶ E` in `ModuleCat R`.  Restricting an
endomorphism of `E` to the Artinian pieces `E[𝔪^(n+1)]` gives a compatible family of elements of
the quotients `R / 𝔪^(n+1)`, and this identifies `End_R(E)` with the completion `R^∧` of `R`.

It was split from `StacksFrontier.RingTheory.Dualizing.ResidueFieldHull`, which re-exports it.

## Main results

* `Dualizing.endAlgEquivAdicCompletion` — `End_R(E) ≃ₐ[R] R^∧`.

## References

* [Stacks Project, Tag 08Z6](https://stacks.math.columbia.edu/tag/08Z6)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Dualizing

section Endomorphisms

/-- An `R`-linear endomorphism of `E` maps `E[𝔪^(n+1)]` into itself. -/
public lemma endomorphism_preserves_maximalIdealPowTorsion
    (R : Type u) [CommRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (f : Module.End R E) (n : ℕ)
    (x : maximalIdealPowTorsion R (ModuleCat.of R E) n) :
    f x ∈ maximalIdealPowTorsion R (ModuleCat.of R E) n := by
  have hx := x.property
  rw [Submodule.mem_torsionBySet_iff] at hx ⊢
  intro a
  rw [← f.map_smul]
  simpa using congrArg f (hx a)

/-- `E[𝔪^(m+1)] ≤ E[𝔪^(n+1)]` for `m ≤ n`. -/
private theorem maximalIdealPowTorsion_mono
    (R : Type u) [CommRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E] {m n : ℕ} (h : m ≤ n) :
    maximalIdealPowTorsion R (ModuleCat.of R E) m ≤ maximalIdealPowTorsion R (ModuleCat.of R E) n :=
  Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.add_le_add_right h 1) _

/-- Every element of an injective hull `E` of the residue field is killed by some power of the
maximal ideal: it lies in some `E[𝔪^(n+1)]`. -/
public lemma exists_maximalIdealPowTorsion_mem
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (x : E) :
    ∃ n : ℕ, x ∈ maximalIdealPowTorsion R (ModuleCat.of R E) n := by
  let T : ℕ →o Submodule R E :=
    ⟨fun n ↦ maximalIdealPowTorsion R (ModuleCat.of R E) n,
      fun _ _ h ↦ maximalIdealPowTorsion_mono R E h⟩
  have htop : (⨆ n, T n) = ⊤ :=
    iSup_maximalIdealPowTorsion_eq_top R
      (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
      (ModuleCat.of R E) (LinearEquiv.refl R _) i hi
  have hx : x ∈ ⨆ n, T n := htop ▸ Submodule.mem_top
  exact (Submodule.mem_iSup_of_chain T x).mp hx

/-- For a Noetherian local ring `R`, the quotient `R / 𝔪^(n+1)` is Artinian. -/
public lemma artinian_maximalIdeal_pow_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) : IsArtinianRing (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) := by
  let m := IsLocalRing.maximalIdeal R
  have : m.IsPrime := (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  change m ∈ (m ^ (n + 1)).minimalPrimes
  rw [← Ideal.radical_minimalPrimes,
    Ideal.radical_pow m (Nat.succ_ne_zero n), Ideal.IsPrime.radical (I := m) inferInstance,
    Ideal.minimalPrimes_eq_subsingleton_self]
  simp

/-- For a local ring `R`, the quotient `R / 𝔪^(n+1)` is local. -/
public lemma local_maximalIdeal_pow_quotient
    (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) : IsLocalRing (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) := by
  let m := IsLocalRing.maximalIdeal R
  have hp : m ^ (n + 1) ≠ ⊤ := by
    intro h
    have hle : (⊤ : Ideal R) ≤ m := h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)
  let : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr hp
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (m ^ (n + 1)))
    Ideal.Quotient.mk_surjective

/-- The quotient map `R → R / 𝔪^(n+1)` induces a bijection on residue fields. -/
public lemma residueFieldMap_maximalIdealPow_quotient_bijective
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    letI := local_maximalIdeal_pow_quotient R n
    letI : IsLocalHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n + 1))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    Function.Bijective
      (IsLocalRing.ResidueField.map
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n + 1)))) := by
  let := local_maximalIdeal_pow_quotient R n
  let q : R →+* R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1) := Ideal.Quotient.mk _
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  refine ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨IsLocalRing.residue R r, by simp⟩

/-- The ring isomorphism between the residue fields of `R` and of `R / 𝔪^(n+1)` induced by the
quotient map. -/
public noncomputable def residueFieldMaximalIdealPowQuotientEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    letI := local_maximalIdeal_pow_quotient R n
    IsLocalRing.ResidueField R ≃+*
      IsLocalRing.ResidueField (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) := by
  letI := local_maximalIdeal_pow_quotient R n
  letI : IsLocalHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map (Ideal.Quotient.mk _))
    (residueFieldMap_maximalIdealPow_quotient_bijective R n)

/-- The identification of the residue field of `R / 𝔪^(n+1)` with the residue field of `R`, as a
linear equivalence over `R / 𝔪^(n+1)`. -/
public noncomputable def residueFieldMaximalIdealPowQuotientLinearEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    let Q := R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)
    letI := local_maximalIdeal_pow_quotient R n
    letI := (residueFieldIsTorsionByMaximalIdealPow R n).module
    IsLocalRing.ResidueField Q ≃ₗ[Q] IsLocalRing.ResidueField R := by
  let Q := R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)
  letI := local_maximalIdeal_pow_quotient R n
  letI := (residueFieldIsTorsionByMaximalIdealPow R n).module
  let e := residueFieldMaximalIdealPowQuotientEquiv R n
  refine { e.symm.toAddEquiv with map_smul' := ?_ }
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  apply e.injective
  change e (e.symm ((Ideal.Quotient.mk _) r • x)) =
    e ((Ideal.Quotient.mk _) r • e.symm x)
  rw [e.apply_symm_apply]
  change (IsLocalRing.residue Q (Ideal.Quotient.mk _ r)) * x =
    e ((IsLocalRing.residue R r) * e.symm x)
  rw [map_mul, e.apply_symm_apply]
  congr 1

/-- Precomposing an injective hull of `K` with a linear equivalence from the residue field onto `K`
gives an injective hull of the residue field. -/
public lemma injectiveHull_precomp_linearEquiv
    (S : Type u) [CommRing S] [IsLocalRing S]
    (K T : Type u) [AddCommGroup K] [AddCommGroup T]
    [Module S K] [Module S T]
    (e : IsLocalRing.ResidueField S ≃ₗ[S] K)
    (j : ModuleCat.of S K ⟶ ModuleCat.of S T) [Mono j]
    (hj : Module.IsInjectiveHull j) :
    let i := e.toModuleIso.hom ≫ j
    letI : Mono i :=
      (ModuleCat.mono_iff_injective _).2 (by
        intro x y h
        change j.hom (e x) = j.hom (e y) at h
        exact e.injective (((ModuleCat.mono_iff_injective j).1 (by infer_instance)) h))
    Module.IsInjectiveHull i := by
  intro i
  refine ⟨hj.1, ?_⟩
  have hmk : Subobject.mk i = Subobject.mk j :=
    Subobject.mk_eq_mk_of_comm i j e.toModuleIso (by ext; rfl)
  intro U hU
  change U ⊓ Subobject.mk i ≠ ⊥
  rw [hmk]
  exact hj.2 U hU

/-- The residue field of `R` and the quotient `R / 𝔪` are the same `R`-module. -/
public def residueFieldQuotientLinearEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalRing.ResidueField R ≃ₗ[R] R ⧸ IsLocalRing.maximalIdeal R :=
  { toFun := fun x ↦ x
    invFun := fun x ↦ x
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

/-- The identification of the residue field of `R` with `R / 𝔪`, as a linear equivalence over
`R / 𝔪^(n+1)`. -/
public noncomputable def residueFieldQuotientLinearEquivOverPow
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    let Q := R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)
    letI := (residueFieldIsTorsionByMaximalIdealPow R n).module
    letI := (residueFieldModelIsTorsionByMaximalIdealPow R
      (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
      (residueFieldQuotientLinearEquiv R) n).module
    IsLocalRing.ResidueField R ≃ₗ[Q] R ⧸ IsLocalRing.maximalIdeal R := by
  letI := (residueFieldIsTorsionByMaximalIdealPow R n).module
  letI := (residueFieldModelIsTorsionByMaximalIdealPow R
    (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
    (residueFieldQuotientLinearEquiv R) n).module
  exact { (residueFieldQuotientLinearEquiv R).toAddEquiv with
    map_smul' := by intro _ _; rfl }

/-- Over `Q = R / 𝔪^(n+1)`, every endomorphism of `E[𝔪^(n+1)]` is multiplication by a unique
scalar of `Q`: the map `Q → End_Q(E[𝔪^(n+1)])` is bijective. -/
public lemma scalarAction_maximalIdealPowTorsion_bijective
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (n : ℕ) :
    let Q := R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)
    letI := artinian_maximalIdeal_pow_quotient R n
    Function.Bijective (algebraMap Q
      (Module.End Q (maximalIdealPowTorsion R (ModuleCat.of R E) n))) := by
  let Q := R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)
  let := artinian_maximalIdeal_pow_quotient R n
  let := local_maximalIdeal_pow_quotient R n
  let e₀ := residueFieldQuotientLinearEquiv R
  let hK := residueFieldModelIsTorsionByMaximalIdealPow R
    (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) e₀ n
  let := hK.module
  let e := (residueFieldMaximalIdealPowQuotientLinearEquiv R n).trans
    (residueFieldQuotientLinearEquivOverPow R n)
  let j := residueFieldToMaximalIdealPowTorsion R e₀ i n
  let : Mono (ModuleCat.ofHom j) :=
    (ModuleCat.mono_iff_injective _).2
      (residueFieldToMaximalIdealPowTorsion_injective R e₀ i
        ((ModuleCat.mono_iff_injective i).1 (by infer_instance)) n)
  have hj : Module.IsInjectiveHull (ModuleCat.ofHom j) :=
    maximalIdealPowTorsion_isInjectiveHull R
      (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
      (ModuleCat.of R E) e₀ i hi n
  let iQ := e.toModuleIso.hom ≫ ModuleCat.ofHom j
  let : Mono iQ := inferInstance
  have hiQ : Module.IsInjectiveHull iQ :=
    injectiveHull_precomp_linearEquiv Q _ _ e (ModuleCat.ofHom j) hj
  exact algebraMap_end_bijective_of_isInjectiveHull Q _ iQ hiQ

/-- Restricting an `R`-linear endomorphism of `E` to `E[𝔪^(n+1)]`, viewed as an endomorphism over
`R / 𝔪^(n+1)`. -/
public def restrictEndToMaximalIdealPowTorsionOverQuotient
    (R : Type u) [CommRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E] (n : ℕ) :
    Module.End R E →+* Module.End
      (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
      (maximalIdealPowTorsion R (ModuleCat.of R E) n) where
  toFun f :=
    { toFun := fun x ↦ ⟨f x, endomorphism_preserves_maximalIdealPowTorsion R E f n x⟩
      map_add' := fun x y ↦ Subtype.ext (f.map_add x y)
      map_smul' := by
        intro q x
        induction q using Quotient.inductionOn' with
        | _ r => exact Subtype.ext (f.map_smul r x) }
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl
  map_zero' := by ext x; rfl
  map_add' f g := by ext x; rfl

/-- The scalar of `R / 𝔪^(n+1)` by which an endomorphism of `E` acts on `E[𝔪^(n+1)]`. -/
public noncomputable def endomorphismCoefficient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (n : ℕ) (f : Module.End R E) :
    R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1) :=
  Classical.choose ((scalarAction_maximalIdealPowTorsion_bijective R E i hi n).2
    (restrictEndToMaximalIdealPowTorsionOverQuotient R E n f))

/-- An endomorphism of `E` acts on `E[𝔪^(n+1)]` as multiplication by its coefficient. -/
public lemma endomorphismCoefficient_spec
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (n : ℕ) (f : Module.End R E) :
    algebraMap (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
      (Module.End (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
        (maximalIdealPowTorsion R (ModuleCat.of R E) n))
      (endomorphismCoefficient R E i hi n f) =
      restrictEndToMaximalIdealPowTorsionOverQuotient R E n f :=
  Classical.choose_spec ((scalarAction_maximalIdealPowTorsion_bijective R E i hi n).2
    (restrictEndToMaximalIdealPowTorsionOverQuotient R E n f))

/-- The coefficient of an endomorphism is the only scalar of `R / 𝔪^(n+1)` acting on `E[𝔪^(n+1)]`
as the endomorphism does. -/
public lemma endomorphismCoefficient_unique
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (n : ℕ) (f : Module.End R E)
    (q : R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
    (hq : algebraMap _ (Module.End _
      (maximalIdealPowTorsion R (ModuleCat.of R E) n)) q =
      restrictEndToMaximalIdealPowTorsionOverQuotient R E n f) :
    q = endomorphismCoefficient R E i hi n f :=
  (scalarAction_maximalIdealPowTorsion_bijective R E i hi n).1
    (hq.trans (endomorphismCoefficient_spec R E i hi n f).symm)

/-- An endomorphism of `E` acts on `E[𝔪^(n+1)]` as multiplication by its coefficient. -/
private theorem endomorphismCoefficient_smul_val
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (n : ℕ) (f : Module.End R E)
    (x : maximalIdealPowTorsion R (ModuleCat.of R E) n) :
    ((endomorphismCoefficient R E i hi n f) • x).val = f x :=
  congrArg Subtype.val (by
    simpa using congrArg (fun g ↦ g x) (endomorphismCoefficient_spec R E i hi n f))

/-- Scalars of `R / 𝔪^(n+1)` and their images in `R / 𝔪^(m+1)` act in the same way on
`E[𝔪^(m+1)] ⊆ E[𝔪^(n+1)]`. -/
private theorem val_factor_smul_maximalIdealPowTorsion
    (R : Type u) [CommRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E] {m n : ℕ} (hmn : m ≤ n)
    (q : R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
    (x : maximalIdealPowTorsion R (ModuleCat.of R E) m) :
    ((Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) q) • x).val =
      (q • (⟨x, maximalIdealPowTorsion_mono R E hmn x.property⟩ :
        maximalIdealPowTorsion R (ModuleCat.of R E) n)).val := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.factor_mk]
  simp only [maximalIdealPowTorsion, Submodule.torsionBySet.mk_smul, Submodule.coe_smul]

/-- The coefficients of an endomorphism in degrees `m ≤ n` are compatible under the projection
`R / 𝔪^(n+1) → R / 𝔪^(m+1)`. -/
public lemma endomorphismCoefficient_compatible
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    {m n : ℕ} (hmn : m ≤ n) (f : Module.End R E) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))
      (endomorphismCoefficient R E i hi n f) =
      endomorphismCoefficient R E i hi m f := by
  apply (scalarAction_maximalIdealPowTorsion_bijective R E i hi m).1
  ext x
  simp only [Module.algebraMap_end_apply]
  exact (val_factor_smul_maximalIdealPowTorsion R E hmn _ x).trans
    ((endomorphismCoefficient_smul_val R E i hi n f _).trans
      (endomorphismCoefficient_smul_val R E i hi m f x).symm)

/-- The components of an element of the `I`-adic completion are compatible under the projections
`R / I^n → R / I^m` for `m ≤ n`. -/
public lemma adicCompletion_evalₐ_factor
    (R : Type u) [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      (AdicCompletion.evalₐ I n (AdicCompletion.mkₐ I a)) =
      AdicCompletion.evalₐ I m (AdicCompletion.mkₐ I a)
  simpa only [AdicCompletion.evalₐ_mkₐ, Ideal.Quotient.factor_mk] using
    AdicCompletion.Ideal.mk_eq_mk I hmn a

/-- For an element `y` of the completion, the action of its component in degree `m` on
`E[𝔪^(m+1)]` agrees with that of its component in any degree `n ≥ m`. -/
public lemma completionScalar_coherent
    (R : Type u) [CommRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (y : AdicCompletion (IsLocalRing.maximalIdeal R) R)
    {m n : ℕ} (hmn : m ≤ n)
    (x : maximalIdealPowTorsion R (ModuleCat.of R E) m) :
    ((AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (m + 1) y) • x :
      maximalIdealPowTorsion R (ModuleCat.of R E) m).val =
    ((AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1) y) •
      (⟨x, Submodule.torsionBySet_le_torsionBySet_pow
        (m + 1) (n + 1) (Nat.add_le_add_right hmn 1)
        (IsLocalRing.maximalIdeal R) x.property⟩ :
        maximalIdealPowTorsion R (ModuleCat.of R E) n)).val := by
  rw [← adicCompletion_evalₐ_factor R (IsLocalRing.maximalIdeal R)
    (Nat.add_le_add_right hmn 1) y]
  exact val_factor_smul_maximalIdealPowTorsion R E hmn _ x

/-- The action of an element `y` of the completion `R^∧` on `E`: on an element of `E[𝔪^(n+1)]` it
is the action of the component of `y` in `R / 𝔪^(n+1)`. -/
public noncomputable def completionScalarAction
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (y : AdicCompletion (IsLocalRing.maximalIdeal R) R) (x : E) : E :=
  let n := Classical.choose (exists_maximalIdealPowTorsion_mem R E i hi x)
  let hx := Classical.choose_spec (exists_maximalIdealPowTorsion_mem R E i hi x)
  ((AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1) y) •
    (⟨x, hx⟩ : maximalIdealPowTorsion R (ModuleCat.of R E) n)).val

/-- The action of `y ∈ R^∧` on an element of `E[𝔪^(n+1)]` is that of its component in
`R / 𝔪^(n+1)`, whichever such `n` is used. -/
public lemma completionScalarAction_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (y : AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (n : ℕ) (x : E)
    (hx : x ∈ maximalIdealPowTorsion R (ModuleCat.of R E) n) :
    completionScalarAction R E i hi y x =
      ((AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1) y) •
        (⟨x, hx⟩ : maximalIdealPowTorsion R (ModuleCat.of R E) n)).val := by
  unfold completionScalarAction
  let k := Classical.choose (exists_maximalIdealPowTorsion_mem R E i hi x)
  let hk := Classical.choose_spec (exists_maximalIdealPowTorsion_mem R E i hi x)
  have hkt := completionScalar_coherent R E y (Nat.le_max_left k n)
    (⟨x, hk⟩ : maximalIdealPowTorsion R (ModuleCat.of R E) k)
  have hnt := completionScalar_coherent R E y (Nat.le_max_right k n)
    (⟨x, hx⟩ : maximalIdealPowTorsion R (ModuleCat.of R E) n)
  exact hkt.trans hnt.symm

/-- The endomorphism of `E` given by the action of an element of the completion `R^∧`. -/
public noncomputable def completionToEnd
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (y : AdicCompletion (IsLocalRing.maximalIdeal R) R) : Module.End R E where
  toFun := completionScalarAction R E i hi y
  map_add' x z := by
    obtain ⟨m, hm⟩ := exists_maximalIdealPowTorsion_mem R E i hi x
    obtain ⟨n, hn⟩ := exists_maximalIdealPowTorsion_mem R E i hi z
    let t := max m n
    have hmt : maximalIdealPowTorsion R (ModuleCat.of R E) m ≤
        maximalIdealPowTorsion R (ModuleCat.of R E) t :=
      Submodule.torsionBySet_le_torsionBySet_pow
        (m + 1) (t + 1) (Nat.add_le_add_right (Nat.le_max_left m n) 1)
        (IsLocalRing.maximalIdeal R)
    have hnt : maximalIdealPowTorsion R (ModuleCat.of R E) n ≤
        maximalIdealPowTorsion R (ModuleCat.of R E) t :=
      Submodule.torsionBySet_le_torsionBySet_pow
        (n + 1) (t + 1) (Nat.add_le_add_right (Nat.le_max_right m n) 1)
        (IsLocalRing.maximalIdeal R)
    have hxt := hmt hm
    have hzt := hnt hn
    have hxzt : x + z ∈ maximalIdealPowTorsion R
        (ModuleCat.of R E) t := add_mem hxt hzt
    rw [completionScalarAction_eq R E i hi y t (x + z) hxzt,
      completionScalarAction_eq R E i hi y t x hxt,
      completionScalarAction_eq R E i hi y t z hzt]
    exact Subtype.ext_iff.mp (smul_add
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (t + 1) y)
      (⟨x, hxt⟩ : maximalIdealPowTorsion R (ModuleCat.of R E) t)
      (⟨z, hzt⟩ : maximalIdealPowTorsion R (ModuleCat.of R E) t))
  map_smul' r x := by
    obtain ⟨n, hx⟩ := exists_maximalIdealPowTorsion_mem R E i hi x
    have hrx : r • x ∈ maximalIdealPowTorsion R
        (ModuleCat.of R E) n := Submodule.smul_mem _ r hx
    rw [completionScalarAction_eq R E i hi y n (r • x) hrx,
      completionScalarAction_eq R E i hi y n x hx]
    exact congrArg Subtype.val (smul_comm
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1) y) r
      (⟨x, hx⟩ : maximalIdealPowTorsion R (ModuleCat.of R E) n))

/-- The element of the completion `R^∧` whose components are the coefficients of an endomorphism
of `E`. -/
public noncomputable def endomorphismToCompletion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (f : Module.End R E) : AdicCompletion (IsLocalRing.maximalIdeal R) R :=
  ⟨fun n => Ideal.Quotient.factor (show
      (IsLocalRing.maximalIdeal R) ^ (n + 1) ≤
        (IsLocalRing.maximalIdeal R) ^ n • ⊤ by
      simpa using (Ideal.pow_le_pow_right n.le_succ :
        (IsLocalRing.maximalIdeal R) ^ (n + 1) ≤
          (IsLocalRing.maximalIdeal R) ^ n))
      (endomorphismCoefficient R E i hi n f), by
    intro m n hmn
    dsimp only [AdicCompletion.transitionMap, Submodule.factorPow]
    rw [Submodule.factor_eq_factor]
    rw [← endomorphismCoefficient_compatible R E i hi hmn f]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (endomorphismCoefficient R E i hi n f)
    rw [← hr]
    simp only [Ideal.Quotient.factor_mk]⟩

/-- The component in `R / 𝔪^(n+1)` of the element of `R^∧` attached to an endomorphism is its
coefficient in degree `n`. -/
public lemma evalₐ_endomorphismToCompletion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (n : ℕ) (f : Module.End R E) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1)
      (endomorphismToCompletion R E i hi f) =
      endomorphismCoefficient R E i hi n f := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ
    (IsLocalRing.maximalIdeal R) (endomorphismToCompletion R E i hi f)
    (show (IsLocalRing.maximalIdeal R) ^ (n + 1) • ⊤ ≤
      (IsLocalRing.maximalIdeal R) ^ (n + 1) by simp)]
  rw [Submodule.factor_eq_factor, AdicCompletion.eval_apply]
  dsimp only [endomorphismToCompletion]
  rw [← endomorphismCoefficient_compatible R E i hi (Nat.le_succ n) f]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (endomorphismCoefficient R E i hi (n + 1) f)
  rw [← hr]
  simp

/-- Every endomorphism of `E` is the action of the element of `R^∧` attached to it. -/
public lemma completionToEnd_endomorphismToCompletion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (f : Module.End R E) :
    completionToEnd R E i hi (endomorphismToCompletion R E i hi f) = f := by
  ext x
  obtain ⟨n, hx⟩ := exists_maximalIdealPowTorsion_mem R E i hi x
  change completionScalarAction R E i hi (endomorphismToCompletion R E i hi f) x = f x
  rw [completionScalarAction_eq R E i hi _ n x hx,
    evalₐ_endomorphismToCompletion R E i hi n f]
  exact endomorphismCoefficient_smul_val R E i hi n f ⟨x, hx⟩

/-- The coefficient of the action of `y ∈ R^∧` in degree `n` is the component of `y` in
`R / 𝔪^(n+1)`. -/
public lemma endomorphismCoefficient_completionToEnd
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (n : ℕ) (y : AdicCompletion (IsLocalRing.maximalIdeal R) R) :
    endomorphismCoefficient R E i hi n (completionToEnd R E i hi y) =
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1) y := by
  symm
  apply endomorphismCoefficient_unique R E i hi n
  ext x
  simp only [Module.algebraMap_end_apply]
  exact (completionScalarAction_eq R E i hi y n x x.property).symm

/-- Two elements of the `I`-adic completion that agree in every positive degree are equal. -/
public lemma adicCompletion_ext_of_evalₐ_succ
    (R : Type u) [CommRing R] (I : Ideal R)
    {x y : AdicCompletion I R}
    (h : ∀ n : ℕ, AdicCompletion.evalₐ I (n + 1) x =
      AdicCompletion.evalₐ I (n + 1) y) : x = y := by
  apply AdicCompletion.ext_evalₐ
  intro n
  calc
    _ = Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
        (AdicCompletion.evalₐ I (n + 1) x) :=
      (adicCompletion_evalₐ_factor R I n.le_succ x).symm
    _ = Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
        (AdicCompletion.evalₐ I (n + 1) y) := by rw [h n]
    _ = _ := adicCompletion_evalₐ_factor R I n.le_succ y

/-- The element of `R^∧` attached to the action of `y ∈ R^∧` on `E` is `y` itself. -/
public lemma endomorphismToCompletion_completionToEnd
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (y : AdicCompletion (IsLocalRing.maximalIdeal R) R) :
    endomorphismToCompletion R E i hi (completionToEnd R E i hi y) = y := by
  apply adicCompletion_ext_of_evalₐ_succ R (IsLocalRing.maximalIdeal R)
  intro n
  rw [evalₐ_endomorphismToCompletion,
    endomorphismCoefficient_completionToEnd]

/-- The identity of `E` has coefficient `1` in every degree. -/
public lemma endomorphismCoefficient_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (n : ℕ) :
    endomorphismCoefficient R E i hi n 1 = 1 := by
  symm; apply endomorphismCoefficient_unique R E i hi n 1 1; simp

/-- The zero endomorphism of `E` has coefficient `0` in every degree. -/
public lemma endomorphismCoefficient_zero
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (n : ℕ) :
    endomorphismCoefficient R E i hi n 0 = 0 := by
  symm; apply endomorphismCoefficient_unique R E i hi n 0 0; simp

/-- The coefficient of a sum of endomorphisms is the sum of their coefficients. -/
public lemma endomorphismCoefficient_add
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (n : ℕ)
    (f g : Module.End R E) :
    endomorphismCoefficient R E i hi n (f + g) =
      endomorphismCoefficient R E i hi n f +
        endomorphismCoefficient R E i hi n g := by
  symm; apply endomorphismCoefficient_unique R E i hi n (f + g) _
  rw [map_add, map_add, endomorphismCoefficient_spec, endomorphismCoefficient_spec]

/-- The coefficient of a composite of endomorphisms is the product of their coefficients. -/
public lemma endomorphismCoefficient_mul
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (n : ℕ)
    (f g : Module.End R E) :
    endomorphismCoefficient R E i hi n (f * g) =
      endomorphismCoefficient R E i hi n f *
        endomorphismCoefficient R E i hi n g := by
  symm; apply endomorphismCoefficient_unique R E i hi n (f * g) _
  rw [map_mul, map_mul, endomorphismCoefficient_spec, endomorphismCoefficient_spec]

/-- Multiplication by `r ∈ R` on `E` has coefficient the class of `r` in `R / 𝔪^(n+1)`. -/
public lemma endomorphismCoefficient_algebraMap
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) (n : ℕ) (r : R) :
    endomorphismCoefficient R E i hi n (algebraMap R (Module.End R E) r) =
      Ideal.Quotient.mk _ r := by
  symm
  apply endomorphismCoefficient_unique R E i hi n _ _
  ext x
  simp only [Module.algebraMap_end_apply]
  exact Subtype.ext_iff.mp (Submodule.torsionBySet.mk_smul _ r x)

/-- The `R`-algebra homomorphism `End_R(E) → R^∧` sending an endomorphism to the compatible family
of its coefficients. -/
public noncomputable def endomorphismToCompletionAlgHom
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    Module.End R E →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R where
  toFun := endomorphismToCompletion R E i hi
  map_one' := by
    apply adicCompletion_ext_of_evalₐ_succ R (IsLocalRing.maximalIdeal R)
    intro n
    rw [evalₐ_endomorphismToCompletion, endomorphismCoefficient_one, map_one]
  map_mul' f g := by
    apply adicCompletion_ext_of_evalₐ_succ R (IsLocalRing.maximalIdeal R)
    intro n
    rw [evalₐ_endomorphismToCompletion, endomorphismCoefficient_mul, map_mul,
      evalₐ_endomorphismToCompletion, evalₐ_endomorphismToCompletion]
  map_zero' := by
    apply adicCompletion_ext_of_evalₐ_succ R (IsLocalRing.maximalIdeal R)
    intro n
    rw [evalₐ_endomorphismToCompletion, endomorphismCoefficient_zero, map_zero]
  map_add' f g := by
    apply adicCompletion_ext_of_evalₐ_succ R (IsLocalRing.maximalIdeal R)
    intro n
    rw [evalₐ_endomorphismToCompletion, endomorphismCoefficient_add, map_add,
      evalₐ_endomorphismToCompletion, evalₐ_endomorphismToCompletion]
  commutes' r := by
    apply adicCompletion_ext_of_evalₐ_succ R (IsLocalRing.maximalIdeal R)
    intro n
    rw [evalₐ_endomorphismToCompletion, endomorphismCoefficient_algebraMap]
    exact (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1)).commutes r |>.symm

/-- **Stacks Project, Tag 08Z6.** The endomorphism ring of an injective hull of
the residue field of a Noetherian local ring is canonically isomorphic to its
completion. -/
@[stacks 08Z6]
public noncomputable def endAlgEquivAdicCompletion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    Module.End R E ≃ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R :=
  AlgEquiv.ofBijective (endomorphismToCompletionAlgHom R E i hi)
    ⟨Function.LeftInverse.injective (completionToEnd_endomorphismToCompletion R E i hi),
      Function.RightInverse.surjective (endomorphismToCompletion_completionToEnd R E i hi)⟩

end Endomorphisms

end Dualizing
