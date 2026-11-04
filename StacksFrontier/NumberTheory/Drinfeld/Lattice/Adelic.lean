module

public import StacksFrontier.NumberTheory.Drinfeld.Lattice.Local

/-!
# Adelic lattices and `GL_n(A) / GL_n(O)`

Let `K` be a field, with adele ring `A = ∏'_v K_v` and integral adeles `O = ∏_v O_v`. An *adelic
lattice* of rank `n` is a family `(Λ_v)_v` of `O_v`-lattices `Λ_v ⊆ K_v^n` with `Λ_v = O_v^n` for
all but finitely many places `v`. The group `GL_n(A)` acts on adelic lattices by
`(g Λ)_v = g_v Λ_v`; the stabiliser of the standard lattice `(O_v^n)_v` is `GL_n(O)`, and for a
function field over a finite field the action is transitive, so that
`AdelicLattice K n ≃ GL_n(A) / GL_n(O)`, `g O^n ↤ g GL_n(O)`.

## Main definitions

* `Stacks.Drinfeld.Lattice.AdelicLattice` — the adelic lattices of rank `n`.
* `Stacks.Drinfeld.Lattice.AdelicLattice.standard` — the standard lattice `(O_v^n)_v`.
* `Stacks.Drinfeld.Lattice.glAt` — the component `g_v ∈ GL_n(K_v)` of `g ∈ GL_n(A)`.
* `Stacks.Drinfeld.Lattice.AdelicLattice.equivQuotient` — `AdelicLattice K n ≃ GL_n(A) / GL_n(O)`.

## Main results

* `Stacks.Drinfeld.Lattice.AdelicLattice.stabilizer_standard` — the stabiliser of `(O_v^n)_v` is
  `GL_n(O)`.
* `Stacks.Drinfeld.Lattice.AdelicLattice.exists_smul_standard` — over a function field every
  adelic lattice is `g (O_v^n)_v`.
* `Stacks.Drinfeld.Lattice.AdelicLattice.equivQuotient_symm_mk` — the equivalence sends the coset
  of `g` to `g (O_v^n)_v`.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Drinfeld.Lattice

open Stacks.Adeles Stacks.Adeles.GlobalFunctionField

variable (K : Type u) [Field K] (n : ℕ)

/-- An adelic lattice of rank `n`: a family of `O_v`-lattices `Λ_v ⊆ K_v^n`, one at each place,
equal to the standard lattice `O_v^n` at all but finitely many places. -/
@[ext]
public structure AdelicLattice where
  /-- The component `Λ_v ⊆ K_v^n` at the place `v`. -/
  lattice : ∀ v : Place K, Submodule v.integers (Fin n → v.completion)
  /-- Each `Λ_v` is an `O_v`-lattice: finitely generated, spanning `K_v^n`. -/
  isLattice : ∀ v, (lattice v).IsLattice v.completion
  /-- `Λ_v = O_v^n` for all but finitely many places `v`. -/
  finite_ne : {v | lattice v ≠ stdLattice v n}.Finite

variable (v : Place K)

/-- The component `g_v ∈ GL_n(K_v)` at a place `v` of `g ∈ GL_n(A)`. -/
public abbrev glAt : GL (Fin n) (AdeleRing K) →* GL (Fin n) v.completion :=
  Matrix.GeneralLinearGroup.map (evalAt K v)

variable {K n}

/-- An element of `GL_n(A)` has components in `GL_n(O_v)` at all but finitely many places. -/
public theorem finite_setOf_not_integral (g : GL (Fin n) (AdeleRing K)) :
    {v : Place K | ¬ ∀ i j, (glAt K n v g).val i j ∈ v.integers}.Finite := by
  refine (Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    Filter.eventually_cofinite.1 (g.val i j).2).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨i, j, h⟩ := hv
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, h⟩⟩

namespace AdelicLattice

variable (K n) in
/-- The standard adelic lattice `(O_v^n)_v`. -/
public def standard : AdelicLattice K n where
  lattice v := stdLattice v n
  isLattice v := isLattice_stdLattice v n
  finite_ne := by simp

@[simp]
public theorem standard_lattice : (standard K n).lattice v = stdLattice v n := rfl

/-- `GL_n(A)` acts on adelic lattices by `(g Λ)_v = g_v Λ_v`. -/
public instance : SMul (GL (Fin n) (AdeleRing K)) (AdelicLattice K n) where
  smul g Λ :=
    { lattice := fun v => translate (glAt K n v g) (Λ.lattice v)
      isLattice := fun v => isLattice_translate _ (Λ.isLattice v)
      finite_ne := by
        refine (Λ.finite_ne.union ((finite_setOf_not_integral g).union
          (finite_setOf_not_integral g⁻¹))).subset fun v hv => ?_
        by_contra h
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
        obtain ⟨h₀, h₁, h₂⟩ := h
        apply hv
        rw [h₀, translate_stdLattice_eq_iff]
        exact ⟨h₁, by rwa [← map_inv]⟩ }

@[simp]
public theorem smul_lattice (g : GL (Fin n) (AdeleRing K)) (Λ : AdelicLattice K n) :
    (g • Λ).lattice v = translate (glAt K n v g) (Λ.lattice v) := rfl

public instance : MulAction (GL (Fin n) (AdeleRing K)) (AdelicLattice K n) where
  one_smul Λ := AdelicLattice.ext (funext fun v => by simp)
  mul_smul g h Λ := AdelicLattice.ext (funext fun v => by simp [translate_mul])

/-- If `M, N` map under an injective ring hom `φ` to a unit and its inverse, then `φ` lifts the
unit to a unit of the source. -/
private theorem exists_units_map_eq {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (hφ : Function.Injective φ) (M N : R) (g : Sˣ) (hM : φ M = g) (hN : φ N = ↑g⁻¹) :
    ∃ u : Rˣ, Units.map φ.toMonoidHom u = g :=
  ⟨⟨M, N, hφ (by rw [map_mul, map_one, hM, hN, Units.mul_inv]),
    hφ (by rw [map_mul, map_one, hM, hN, Units.inv_mul])⟩, Units.ext hM⟩

/-- `g (O_v^n)_v = (O_v^n)_v` exactly when every component `g_v` lies in `GL_n(O_v)`. -/
public theorem smul_standard_eq_iff (g : GL (Fin n) (AdeleRing K)) :
    g • standard K n = standard K n ↔
      ∀ v : Place K, (∀ i j, (glAt K n v g).val i j ∈ v.integers) ∧
        ∀ i j, (glAt K n v g⁻¹).val i j ∈ v.integers := by
  rw [AdelicLattice.ext_iff, funext_iff]
  refine forall_congr' fun v => ?_
  rw [smul_lattice, standard_lattice, translate_stdLattice_eq_iff, map_inv]

variable (K n) in
/-- **The stabiliser of the standard lattice is `GL_n(O)`**: `g (O_v^n)_v = (O_v^n)_v` exactly
when `g` lies in the image of `GL_n(O) → GL_n(A)`. -/
public theorem stabilizer_standard :
    MulAction.stabilizer (GL (Fin n) (AdeleRing K)) (standard K n) =
      (Matrix.GeneralLinearGroup.map (integralAdeles K).subtype).range := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_standard_eq_iff, MonoidHom.mem_range]
  constructor
  · intro h
    let kM : Matrix (Fin n) (Fin n) (integralAdeles K) := Matrix.of fun i j =>
      ⟨g.val i j, fun w => (h w).1 i j⟩
    let kI : Matrix (Fin n) (Fin n) (integralAdeles K) := Matrix.of fun i j =>
      ⟨(g⁻¹ : GL (Fin n) (AdeleRing K)).val i j, fun w => (h w).2 i j⟩
    obtain ⟨κ, hκ⟩ := exists_units_map_eq (S := Matrix (Fin n) (Fin n) (AdeleRing K))
      (integralAdeles K).subtype.mapMatrix
      (fun M N hMN => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hMN i) j))
      kM kI g (by ext i j; rfl) (by ext i j; rfl)
    exact ⟨κ, hκ⟩
  · rintro ⟨κ, rfl⟩ w
    refine ⟨fun i j => ((κ.val i j).2 w), fun i j => ?_⟩
    rw [← map_inv]
    exact (κ⁻¹.val i j).2 w

section FunctionField

variable (k : Type u) [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k in
/-- **`GL_n(A)` acts transitively on adelic lattices**: over a function field over a finite
field, every adelic lattice is `g (O_v^n)_v` for some `g ∈ GL_n(A)`. -/
public theorem exists_smul_standard (Λ : AdelicLattice K n) :
    ∃ g : GL (Fin n) (AdeleRing K), g • standard K n = Λ := by
  classical
  have hloc := fun v => exists_eq_translate_stdLattice (isDiscrete k v) (Λ.isLattice v)
  let h : ∀ v : Place K, GL (Fin n) v.completion := fun v =>
    if Λ.lattice v = stdLattice v n then 1 else (hloc v).choose
  have hh : ∀ v, Λ.lattice v = translate (h v) (stdLattice v n) := by
    intro v
    by_cases hv : Λ.lattice v = stdLattice v n
    · simp only [h, if_pos hv, translate_one, hv]
    · simp only [h, if_neg hv]
      exact (hloc v).choose_spec
  have hh1 : ∀ v, v ∉ {v | Λ.lattice v ≠ stdLattice v n} → h v = 1 := by
    intro v hv
    simp only [Set.mem_setOf_eq, not_not] at hv
    simp only [h, if_pos hv]
  have hfin : ∀ (A : ∀ v : Place K, Matrix (Fin n) (Fin n) v.completion),
      (∀ v, v ∉ {v | Λ.lattice v ≠ stdLattice v n} → A v = 1) → ∀ i j,
      ∀ᶠ v in Filter.cofinite, A v i j ∈ v.integers := by
    intro A hA i j
    refine Filter.eventually_cofinite.2 (Λ.finite_ne.subset fun v hv => ?_)
    by_contra hvS
    apply hv
    rw [hA v hvS, one_apply]
    split_ifs
    · exact v.integers.one_mem
    · exact v.integers.zero_mem
  let M : Matrix (Fin n) (Fin n) (AdeleRing K) := Matrix.of fun i j =>
    ⟨fun v => (h v).val i j, hfin (fun v => (h v).val)
      (fun v hv => by rw [hh1 v hv, Units.val_one]) i j⟩
  let N : Matrix (Fin n) (Fin n) (AdeleRing K) := Matrix.of fun i j =>
    ⟨fun v => (h v)⁻¹.val i j, hfin (fun v => (h v)⁻¹.val)
      (fun v hv => by rw [hh1 v hv, inv_one, Units.val_one]) i j⟩
  have hM : ∀ v, (evalAt K v).mapMatrix M = (h v).val := fun v => by ext i j; rfl
  have hN : ∀ v, (evalAt K v).mapMatrix N = (h v)⁻¹.val := fun v => by ext i j; rfl
  obtain ⟨κ, hκ⟩ := exists_units_map_eq (RingHom.pi fun v => (evalAt K v).mapMatrix)
    (fun X Y hXY => by ext i j v; exact congrFun (congrFun (congrFun hXY v) i) j)
    M N (MulEquiv.piUnits.symm fun v => h v) (funext hM) (funext hN)
  refine ⟨κ, AdelicLattice.ext (funext fun v => ?_)⟩
  have hg : glAt K n v κ = h v := Units.ext (congrFun (congrArg Units.val hκ) v)
  rw [smul_lattice, hg, standard_lattice, ← hh]

include k in
/-- The action of `GL_n(A)` on adelic lattices over a function field is transitive. -/
public theorem isPretransitive : MulAction.IsPretransitive (GL (Fin n) (AdeleRing K))
    (AdelicLattice K n) := by
  refine MulAction.IsPretransitive.mk fun Λ Λ' => ?_
  obtain ⟨g, rfl⟩ := exists_smul_standard k Λ
  obtain ⟨g', rfl⟩ := exists_smul_standard k Λ'
  exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

variable (K n) in
/-- **Adelic lattices are `GL_n(A) / GL_n(O)`**: over a function field over a finite field, the
map `g ↦ g (O_v^n)_v` identifies the left cosets of `GL_n(O)` in `GL_n(A)` with the adelic
lattices of rank `n`. -/
public def equivQuotient : AdelicLattice K n ≃
    GL (Fin n) (AdeleRing K) ⧸ (Matrix.GeneralLinearGroup.map (integralAdeles K).subtype).range :=
  ((Equiv.subtypeUnivEquiv fun Λ => (exists_smul_standard k Λ).imp fun _ h => h).symm.trans
    (MulAction.orbitEquivQuotientStabilizer _ (standard K n))).trans
    (Subgroup.quotientEquivOfEq (stabilizer_standard K n))

/-- The inverse of `equivQuotient` sends the coset `g GL_n(O)` to `g (O_v^n)_v`. -/
public theorem equivQuotient_symm_mk (g : GL (Fin n) (AdeleRing K)) :
    (equivQuotient K n k).symm (QuotientGroup.mk g) = g • standard K n := by
  rfl

/-- `equivQuotient` sends `g (O_v^n)_v` to the coset `g GL_n(O)`. -/
public theorem equivQuotient_smul_standard (g : GL (Fin n) (AdeleRing K)) :
    equivQuotient K n k (g • standard K n) = QuotientGroup.mk g := by
  rw [Equiv.apply_eq_iff_eq_symm_apply, equivQuotient_symm_mk]

end FunctionField

end AdelicLattice

end Stacks.Drinfeld.Lattice

end
