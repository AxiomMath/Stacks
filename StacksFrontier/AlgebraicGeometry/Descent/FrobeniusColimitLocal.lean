module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwist
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctions
public import StacksFrontier.AlgebraicGeometry.Modules.UnitEndScalar

/-!
# The affine free case of the full faithfulness in Stacks Tag 0EXH

Let `p` be a prime, `Y` a scheme in characteristic `p`, `H : V ⟶ Y` a scheme over `Y` with `V`
affine, and `ρ : X' ⟶ V` proper and surjective with geometrically connected fibres. For
`𝒪_Y`-modules `A`, `B` whose pullbacks to `V` are free of finite rank, the map

`colim_k Hom(H_k^*A, H_k^*B) ⟶ colim_k Hom((ρ ≫ H)_k^*A, (ρ ≫ H)_k^*B)`

given by restriction along `ρ`, the colimits being along the Frobenius twist, is bijective
(`AlgebraicGeometry.exists_twistIter_eq_of_homRes_eq` and
`AlgebraicGeometry.exists_homRes_eq_twistIter`). Morphisms between free modules are matrices of
endomorphisms of the structure sheaf; restriction acts on those by the pullback of functions and
the Frobenius twist by the `p`-th power, so this is the bijectivity of
`colim_F Γ(V, 𝒪_V) ⟶ colim_F Γ(X', 𝒪_{X'})` of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctions`, applied entrywise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {Y : Scheme.{u}} {p : ℕ} [Fact p.Prime] {hY : IsInCharacteristic Y p}

/-! ### Iterated twists -/

variable (p hY) in
/-- `H_m`: the `m`-fold Frobenius of `H`, with `H_{m+1} = F ≫ H_m`. -/
def frobPow {T : Scheme.{u}} (H : T ⟶ Y) : ℕ → (T ⟶ Y)
  | 0 => H
  | m + 1 => frobOf p hY (frobPow H m) ≫ frobPow H m

/-- Iterated Frobenius twists are compatible with precomposition: if `u ≫ H = H'` then
`u ≫ H_m = H'_m` for every `m`. -/
lemma comp_frobPow {T T' : Scheme.{u}} (u : T' ⟶ T) {H : T ⟶ Y} {H' : T' ⟶ Y}
    (hu : u ≫ H = H') : ∀ m, u ≫ frobPow p hY H m = frobPow p hY H' m
  | 0 => hu
  | m + 1 => comp_frobOf_comp u (comp_frobPow u hu m)

variable (p hY) in
/-- The `m`-fold Frobenius twist. -/
def twistIter {T : Scheme.{u}} {H : T ⟶ Y} {A B : Y.Modules} :
    ∀ m, HomAt H A B → HomAt (frobPow p hY H m) A B
  | 0 => id
  | m + 1 => fun φ ↦ twist p hY (twistIter m φ)

section Iter

variable {T T' : Scheme.{u}} {H : T ⟶ Y} {A B C : Y.Modules}

/-- The iterated twist preserves composition. -/
lemma twistIter_comp (m : ℕ) (φ : HomAt H A B) (ψ : HomAt H B C) :
    twistIter p hY m (φ ≫ ψ) = twistIter p hY m φ ≫ twistIter p hY m ψ := by
  induction m with
  | zero => rfl
  | succ m ih => exact (congrArg (twist p hY) ih).trans (twist_comp _ _)

/-- The iterated twist sends identities to identities. -/
lemma twistIter_id (m : ℕ) :
    twistIter p hY m (𝟙 ((Scheme.Modules.pullback H).obj A)) = 𝟙 _ := by
  induction m with
  | zero => rfl
  | succ m ih => exact (congrArg (twist p hY) ih).trans twist_id

/-- The iterated twist preserves differences. -/
lemma twistIter_sub (m : ℕ) (φ ψ : HomAt H A B) :
    twistIter p hY m (φ - ψ) = twistIter p hY m φ - twistIter p hY m ψ := by
  induction m with
  | zero => rfl
  | succ m ih => exact (congrArg (twist p hY) ih).trans (twist_sub _ _)

/-- The iterated twist preserves finite sums. -/
lemma twistIter_sum {ι : Type} (s : Finset ι) (m : ℕ) (φ : ι → HomAt H A B) :
    twistIter p hY m (∑ i ∈ s, φ i) = ∑ i ∈ s, twistIter p hY m (φ i) := by
  induction m with
  | zero => rfl
  | succ m ih => exact (congrArg (twist p hY) ih).trans (twist_sum _ _)

/-- **The iterated twist commutes with restriction.** -/
lemma homRes_twistIter (u : T' ⟶ T) {H' : T' ⟶ Y} (hu : u ≫ H = H') (m : ℕ)
    (φ : HomAt H A B) :
    homRes u (comp_frobPow u hu m) (twistIter p hY m φ) =
      twistIter p hY m (homRes u hu φ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact (homRes_twist u (comp_frobPow u hu m) (twistIter p hY m φ)).trans
      (congrArg (twist p hY) ih)

end Iter

/-! ### Scalars of endomorphisms of objects isomorphic to the structure sheaf -/

open Scheme.Modules in
/-- The function by which an endomorphism of an object isomorphic to `𝒪_T` acts. -/
def scal {T : Scheme.{u}} {P : T.Modules} (α : P ≅ Scheme.unitModule T) (θ : P ⟶ P) : Γ(T, ⊤) :=
  unitScalar (α.inv ≫ θ ≫ α.hom)

open Scheme.Modules

section Scal

variable {T : Scheme.{u}} {P : T.Modules}

/-- The scalar of an endomorphism does not depend on the chosen isomorphism with `𝒪_T`. -/
lemma scal_indep (α β : P ≅ Scheme.unitModule T) (θ : P ⟶ P) : scal β θ = scal α θ := by
  unfold scal
  have e : β.inv ≫ θ ≫ β.hom = (β.inv ≫ α.hom) ≫ (α.inv ≫ θ ≫ α.hom) ≫ (α.inv ≫ β.hom) := by
    simp
  have hw : unitScalar (β.inv ≫ α.hom) * unitScalar (α.inv ≫ β.hom) = 1 := by
    rw [← unitScalar_comp]
    have : (β.inv ≫ α.hom) ≫ α.inv ≫ β.hom = 𝟙 _ := by simp
    rw [this, unitScalar_id]
  rw [e, unitScalar_comp, unitScalar_comp, mul_left_comm, hw, mul_one]

/-- The scalar of a composite is the product of the scalars. -/
lemma scal_comp (α : P ≅ Scheme.unitModule T) (θ θ' : P ⟶ P) :
    scal α (θ ≫ θ') = scal α θ * scal α θ' := by
  unfold scal
  rw [← unitScalar_comp]
  congr 1
  simp

/-- The scalar of a difference is the difference of the scalars. -/
lemma scal_sub (α : P ≅ Scheme.unitModule T) (θ θ' : P ⟶ P) :
    scal α (θ - θ') = scal α θ - scal α θ' := by
  unfold scal
  rw [← unitScalar_sub, Preadditive.sub_comp, Preadditive.comp_sub]

/-- An endomorphism is determined by its scalar. -/
lemma scal_injective (α : P ≅ Scheme.unitModule T) : Function.Injective (scal α) := by
  intro θ θ' h
  have := unitScalar_injective h
  simpa using congrArg (fun t ↦ α.hom ≫ t ≫ α.inv) this

/-- Every global function is the scalar of some endomorphism. -/
lemma scal_surjective (α : P ≅ Scheme.unitModule T) : Function.Surjective (scal α) := by
  intro a
  obtain ⟨θ, hθ⟩ := unitScalar_surjective a
  refine ⟨α.hom ≫ θ ≫ α.inv, ?_⟩
  unfold scal
  simpa using hθ

/-- The scalar of the pullback of an endomorphism along `u` is the pullback `u.appTop` of its
scalar, for any identifications of the objects with the structure sheaves. -/
lemma scal_pullback {T' : Scheme.{u}} (u : T' ⟶ T) {Q : T'.Modules} (α : P ≅ Scheme.unitModule T)
    (α' : Q ≅ Scheme.unitModule T') (γ : (Scheme.Modules.pullback u).obj P ≅ Q) (θ : P ⟶ P) :
    scal α' (γ.inv ≫ (Scheme.Modules.pullback u).map θ ≫ γ.hom) = u.appTop (scal α θ) := by
  rw [scal_indep (γ.symm ≪≫ (Scheme.Modules.pullback u).mapIso α ≪≫ pullbackUnitIso u) α']
  unfold scal
  rw [← unitScalar_pullback u]
  congr 1
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

end Scal

/-! ### Restriction and twist on endomorphisms of the structure sheaf -/

section UnitCase

variable {T T' : Scheme.{u}}

/-- The rank-one endomorphisms over `K : T ⟶ Y`: those of `K^*𝒪_Y`. -/
abbrev unitScal (K : T ⟶ Y) (θ : HomAt K (Scheme.unitModule Y) (Scheme.unitModule Y)) :
    Γ(T, ⊤) :=
  scal (Scheme.Modules.pullbackUnitIso K) θ

/-- The scalar of the restriction along `u` of an endomorphism of `K^*𝒪_Y` is the pullback
`u.appTop` of its scalar. -/
lemma unitScal_homRes (u : T' ⟶ T) {K : T ⟶ Y} {K' : T' ⟶ Y} (hu : u ≫ K = K')
    (θ : HomAt K (Scheme.unitModule Y) (Scheme.unitModule Y)) :
    unitScal K' (homRes u hu θ) = u.appTop (unitScal K θ) :=
  scal_pullback u (Scheme.Modules.pullbackUnitIso K) (Scheme.Modules.pullbackUnitIso K')
    ((Scheme.Modules.pullbackComp u K).app _ ≪≫ (Scheme.Modules.pullbackCongr hu).app _) θ

/-- The Frobenius twist raises the scalar of an endomorphism of `K^*𝒪_Y` to the `p`-th power. -/
lemma unitScal_twist {K : T ⟶ Y} (θ : HomAt K (Scheme.unitModule Y) (Scheme.unitModule Y)) :
    unitScal (frobOf p hY K ≫ K) (twist p hY θ) = unitScal K θ ^ p := by
  have := scal_pullback (frobOf p hY K) (Scheme.Modules.pullbackUnitIso K)
    (Scheme.Modules.pullbackUnitIso (frobOf p hY K ≫ K))
    ((Scheme.Modules.pullbackComp (frobOf p hY K) K).app _) θ
  exact this.trans (absoluteFrobenius_app_apply _ _ _ ⊤ _)

/-- The `m`-fold Frobenius twist raises the scalar of an endomorphism of `K^*𝒪_Y` to the
`p^m`-th power. -/
lemma unitScal_twistIter {K : T ⟶ Y} (θ : HomAt K (Scheme.unitModule Y) (Scheme.unitModule Y))
    (m : ℕ) : unitScal (frobPow p hY K m) (twistIter p hY m θ) = unitScal K θ ^ p ^ m := by
  induction m with
  | zero => simp [twistIter, frobPow]
  | succ m ih =>
    change unitScal (frobOf p hY (frobPow p hY K m) ≫ frobPow p hY K m)
      (twist p hY (twistIter p hY m θ)) = _
    rw [unitScal_twist, ih, ← pow_mul, pow_succ]

/-- An endomorphism of `K^*𝒪_Y` is determined by its scalar. -/
lemma unitScal_injective (K : T ⟶ Y) : Function.Injective (unitScal (Y := Y) K) :=
  scal_injective _

/-- Every global function is the scalar of an endomorphism of `K^*𝒪_Y`. -/
lemma unitScal_surjective (K : T ⟶ Y) : Function.Surjective (unitScal (Y := Y) K) :=
  scal_surjective _

/-- The scalar of a difference of endomorphisms of `K^*𝒪_Y` is the difference of the
scalars. -/
lemma unitScal_sub (K : T ⟶ Y) (θ θ' : HomAt K (Scheme.unitModule Y) (Scheme.unitModule Y)) :
    unitScal K (θ - θ') = unitScal K θ - unitScal K θ' :=
  scal_sub _ _ _

end UnitCase

/-! ### Free decompositions -/

/-- A decomposition of `K^*A` as a finite direct sum of copies of `K^*𝒪_Y`, recorded by
injections and projections whose composites sum to the identity. -/
structure FreeDecomp {T : Scheme.{u}} (K : T ⟶ Y) (A : Y.Modules) where
  /-- the rank -/
  n : ℕ
  /-- the injections -/
  ι : Fin n → HomAt K (Scheme.unitModule Y) A
  /-- the projections -/
  π : Fin n → HomAt K A (Scheme.unitModule Y)
  /-- the composites sum to the identity -/
  total : ∑ j, π j ≫ ι j = 𝟙 _

namespace FreeDecomp

variable {T T' : Scheme.{u}} {K : T ⟶ Y} {A B : Y.Modules}

/-- **A morphism is the sum of its matrix entries**, placed by the decompositions. -/
lemma reconstruct (DA : FreeDecomp K A) (DB : FreeDecomp K B) (a : HomAt K A B) :
    a = ∑ j, ∑ l, DA.π j ≫ (DA.ι j ≫ a ≫ DB.π l) ≫ DB.ι l := by
  have h : a = (∑ j, DA.π j ≫ DA.ι j) ≫ a ≫ (∑ l, DB.π l ≫ DB.ι l) := by
    rw [DA.total, DB.total, Category.id_comp, Category.comp_id]
  conv_lhs => rw [h]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  exact Finset.sum_comm

variable (p hY) in
/-- Twisting a decomposition. -/
def twistIter (D : FreeDecomp K A) (m : ℕ) : FreeDecomp (frobPow p hY K m) A where
  n := D.n
  ι j := AlgebraicGeometry.twistIter p hY m (D.ι j)
  π j := AlgebraicGeometry.twistIter p hY m (D.π j)
  total := by
    simp only [← twistIter_comp, ← twistIter_sum, D.total, twistIter_id]

/-- Restricting a decomposition. -/
def homRes (D : FreeDecomp K A) (u : T' ⟶ T) {K' : T' ⟶ Y} (hu : u ≫ K = K') :
    FreeDecomp K' A where
  n := D.n
  ι j := AlgebraicGeometry.homRes u hu (D.ι j)
  π j := AlgebraicGeometry.homRes u hu (D.π j)
  total := by
    simp only [← homRes_comp, ← homRes_sum, D.total, homRes_id]

end FreeDecomp

/-! ### The affine free case -/

/-- A family of natural numbers indexed by `Fin a × Fin b` has a common upper bound. -/
private lemma exists_forall_le_of_fin {a b : ℕ} (m : Fin a → Fin b → ℕ) :
    ∃ M, ∀ j l, m j l ≤ M :=
  ⟨Finset.univ.sup fun jl : Fin a × Fin b ↦ m jl.1 jl.2, fun j l ↦
    Finset.le_sup (f := fun jl : Fin a × Fin b ↦ m jl.1 jl.2) (Finset.mem_univ (j, l))⟩

/-- The twist of a matrix entry is the matrix entry of the twist. -/
private lemma twistIter_entry {T : Scheme.{u}} {K : T ⟶ Y} {A B : Y.Modules} (DA : FreeDecomp K A)
    (DB : FreeDecomp K B) (m : ℕ) (a : HomAt K A B) (j : Fin DA.n) (l : Fin DB.n) :
    (DA.twistIter p hY m).ι j ≫ twistIter p hY m a ≫ (DB.twistIter p hY m).π l =
      twistIter p hY m (DA.ι j ≫ a ≫ DB.π l) := by
  simp only [FreeDecomp.twistIter, twistIter_comp]

/-- In a ring in which the prime `p` vanishes, `(x - y)^{p^m} = 0` gives `x^{p^m} = y^{p^m}`. -/
lemma pow_prime_pow_eq_of_sub_pow_eq_zero {R : Type*} [CommRing R] (hR : (p : R) = 0)
    {x y : R} {m : ℕ} (h : (x - y) ^ p ^ m = 0) : x ^ p ^ m = y ^ p ^ m := by
  by_cases hn : Nontrivial R
  · have : CharP R p := (CharP.charP_iff_prime_eq_zero (R := R) (p := p) Fact.out).2 hR
    rw [sub_pow_char_pow x y m] at h
    exact sub_eq_zero.mp h
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hn
    exact Subsingleton.elim _ _

omit [Fact p.Prime] in
/-- `p` vanishes in the global functions of a scheme over `Y`. -/
lemma cast_eq_zero_of_over (hY : IsInCharacteristic Y p) {T : Scheme.{u}} (H : T ⟶ Y) :
    (p : Γ(T, ⊤)) = 0 :=
  isInCharacteristic_of_hom H p hY

/-- **Injectivity in the affine free case.** -/
theorem exists_twistIter_eq_of_homRes_eq {V X' : Scheme.{u}} [CompactSpace V] (H : V ⟶ Y)
    (ρ : X' ⟶ V) [Surjective ρ] {A B : Y.Modules} (DA : FreeDecomp H A) (DB : FreeDecomp H B)
    (a b : HomAt H A B) (hab : homRes ρ rfl a = homRes ρ rfl b) :
    ∃ m, twistIter p hY m a = twistIter p hY m b := by
  classical
  let θ : HomAt H A B → Fin DA.n → Fin DB.n →
      HomAt H (Scheme.unitModule Y) (Scheme.unitModule Y) :=
    fun c j l ↦ DA.ι j ≫ c ≫ DB.π l
  have hz : ∀ j l, ∃ m, (unitScal H (θ a j l) - unitScal H (θ b j l)) ^ p ^ m = 0 := by
    intro j l
    refine exists_pow_prime_pow_eq_zero_of_appTop_eq_zero p ρ _ ?_
    rw [map_sub, ← unitScal_homRes ρ rfl, ← unitScal_homRes ρ rfl]
    simp only [θ, homRes_comp, hab, sub_self]
  choose m hm using hz
  obtain ⟨M, hle⟩ := exists_forall_le_of_fin m
  have hM : ∀ j l, twistIter p hY M (θ a j l) = twistIter p hY M (θ b j l) := by
    intro j l
    apply unitScal_injective (frobPow p hY H M)
    rw [unitScal_twistIter, unitScal_twistIter]
    refine pow_prime_pow_eq_of_sub_pow_eq_zero (cast_eq_zero_of_over hY H) ?_
    exact pow_eq_zero_of_le (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (hle j l)) (hm j l)
  refine ⟨M, ?_⟩
  rw [(DA.twistIter p hY M).reconstruct (DB.twistIter p hY M) (twistIter p hY M a),
    (DA.twistIter p hY M).reconstruct (DB.twistIter p hY M) (twistIter p hY M b)]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [twistIter_entry DA DB M a j l, twistIter_entry DA DB M b j l, hM j l]

/-- **Surjectivity in the affine free case.** -/
theorem exists_homRes_eq_twistIter {V X' : Scheme.{u}} [IsAffine V] (H : V ⟶ Y)
    (ρ : X' ⟶ V) [IsProper ρ] [Surjective ρ] [GeometricallyConnected ρ] {A B : Y.Modules}
    (DA : FreeDecomp H A) (DB : FreeDecomp H B) (c : HomAt (ρ ≫ H) A B) :
    ∃ m, ∃ a : HomAt (frobPow p hY H m) A B,
      homRes ρ (comp_frobPow ρ rfl m) a = twistIter p hY m c := by
  classical
  let DA' := DA.homRes ρ rfl
  let DB' := DB.homRes ρ rfl
  let cc : Fin DA.n → Fin DB.n → HomAt (ρ ≫ H) (Scheme.unitModule Y) (Scheme.unitModule Y) :=
    fun j l ↦ DA'.ι j ≫ c ≫ DB'.π l
  have hV : (p : Γ(V, ⊤)) = 0 := cast_eq_zero_of_over hY H
  have hroot : ∀ j l, ∃ n, ∃ a : Γ(V, ⊤), unitScal (ρ ≫ H) (cc j l) ^ p ^ n = ρ.appTop a :=
    fun j l ↦ exists_pow_prime_pow_eq_appTop_of_geometricallyConnected p hV ρ _
  choose n a' ha' using hroot
  obtain ⟨N, hle⟩ := exists_forall_le_of_fin n
  have hN : ∀ j l, unitScal (ρ ≫ H) (cc j l) ^ p ^ N =
      ρ.appTop (a' j l ^ p ^ (N - n j l)) := by
    intro j l
    rw [map_pow, ← ha', ← pow_mul, ← pow_add, Nat.add_sub_cancel' (hle j l)]
  choose θ hθ using fun j l ↦
    unitScal_surjective (frobPow p hY H N) (a' j l ^ p ^ (N - n j l))
  refine ⟨N, ∑ j, ∑ l, (DA.twistIter p hY N).π j ≫ θ j l ≫ (DB.twistIter p hY N).ι l, ?_⟩
  rw [(DA'.twistIter p hY N).reconstruct (DB'.twistIter p hY N) (twistIter p hY N c)]
  simp only [homRes_sum, homRes_comp]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  have h₁ : homRes ρ (comp_frobPow ρ rfl N) ((DA.twistIter p hY N).π j) =
      (DA'.twistIter p hY N).π j :=
    homRes_twistIter ρ rfl N (DA.π j)
  have h₂ : homRes ρ (comp_frobPow ρ rfl N) ((DB.twistIter p hY N).ι l) =
      (DB'.twistIter p hY N).ι l :=
    homRes_twistIter ρ rfl N (DB.ι l)
  have h₃ : homRes ρ (comp_frobPow ρ rfl N) (θ j l) = twistIter p hY N (cc j l) :=
    unitScal_injective (frobPow p hY (ρ ≫ H) N) <| (unitScal_homRes ρ _ (θ j l)).trans
      ((congrArg (fun x ↦ ρ.appTop x) (hθ j l)).trans
        ((hN j l).symm.trans (unitScal_twistIter (cc j l) N).symm))
  rw [h₁, h₂, h₃, twistIter_entry DA' DB' N c j l]

end AlgebraicGeometry

end
