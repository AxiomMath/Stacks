module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The local equational criterion for flatness of a sheaf of modules

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules. Stacks 08FC characterises
flatness of `F` by a local factorisation property of the relations among its sections: for every
complex `O_U^{⊕ m} --A--> O_U^{⊕ n} --(s_1,…,s_n)--> F|_U` there is a covering `{U_i → U}` and for
each `i` a factorisation of `(s_1,…,s_n)|_{U_i}` through a finite free module,
`O_{U_i}^{⊕ n} --B_i--> O_{U_i}^{⊕ l_i} --(t_{i1},…,t_{il_i})--> F|_{U_i}`, with
`B_i ∘ A|_{U_i} = 0`. Part (2) of the source is the case `m = 1` and part (3) is the general case.

This file proves that the two local criteria — one relation at a time and a finite matrix of
relations at once — are equivalent.

## Main definitions

* `Stacks.SheafOfModules.LocallyFactorsRelations`: a finite matrix `A` of relations among sections
  `s` over `U` admits, locally on `U`, a factorisation of `s` through a finite free module which
  annihilates every column of `A`.
* `Stacks.SheafOfModules.HasLocalSingleRelationFactorizations`: every *single* relation
  `∑ a i • s i = 0` admits such a local annihilating factorisation.
* `Stacks.SheafOfModules.HasLocalFiniteRelationFactorizations`: every *finite matrix* of relations
  admits such a local annihilating factorisation.

## Main results

* `Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_iff_finite`: the two criteria agree.
* `Stacks.SheafOfModules.LocallyFactorsRelations.of_hasLocalSingleRelationFactorizations`: the
  single-relation criterion implies the finite-matrix criterion.

## Implementation notes

The ringed site is kept *unbundled*: the underlying category, its topology and the structure sheaf
are separate parameters, and the sheaf of rings for the modules is
`Stacks.commRingSheafToRingSheaf O`, the structure sheaf with commutativity forgotten. A bundled
ringed site is an instance of this; the universes `u` (objects), `v` (morphisms) and `w` (sections)
are independent.

A map `O_U^{⊕ n} → O_U^{⊕ m}` of finite free modules is recorded by its matrix of sections,
`A : Fin n → Fin m → O(U)`, with `A i j` the `i`-th coordinate of the image of the `j`-th basis
vector, and composition of matrices is `(B ∘ A) k j = ∑ i, B k i * A i j`. This convention only
describes morphisms of *left* modules because the structure sheaf is a sheaf of **commutative**
rings, which is the source's convention for a ringed site.

A covering `{U_i → U}` is represented by the covering sieve it generates and the factorisation is
required on every arrow of that sieve. This is equivalent to the source's formulation: a sieve is
a covering exactly when it contains a covering family, and the data on a sieve restricts along any
arrow.

Commutativity of the sections of the structure sheaf is a hypothesis rather than an instance.
`Stacks.commRingSheafToRingSheaf O` lands in `RingCat`, and the `Module` instances on the sections
of `F` are stated for the `Ring` instance that `RingCat` carries; a `CommRing` instance on the same
sections competes with it and makes the scalar action `•` fail to elaborate. Accordingly the
identities `sum_sum_mul_smul` and `sum_sum_mul_mul` are stated for a plain `Ring` together with an
explicit commutativity hypothesis, which `Stacks.SheafOfModules.ringSheaf_mul_comm` supplies.

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace Stacks.SheafOfModules

section Algebra

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Applying a matrix of scalars to a vector of module elements, and then contracting with a
vector of scalars, can be done in either order, provided the scalars commute. -/
lemma sum_sum_mul_smul (hc : ∀ x y : R, x * y = y * x) {l n : ℕ}
    (B : Fin l → Fin n → R) (a : Fin n → R) (t : Fin l → M) :
    ∑ k : Fin l, (∑ i : Fin n, B k i * a i) • t k
      = ∑ i : Fin n, a i • ∑ k : Fin l, B k i • t k := by
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul, hc _ (a _)]
  exact Finset.sum_comm

/-- Composing two matrices of scalars before acting on a vector of module elements agrees with
acting with them one after the other. -/
lemma smul_sum_smul_eq {l p : ℕ} (r : Fin l → R) (e : Fin p → Fin l → R) (v : Fin p → M) :
    ∑ k : Fin l, r k • ∑ a : Fin p, e a k • v a
      = ∑ a : Fin p, (∑ k : Fin l, r k * e a k) • v a := by
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- Contracting a composite of two matrices of scalars with a vector of scalars can be done in
either order, provided the scalars commute. -/
lemma sum_sum_mul_mul (hc : ∀ x y : R, x * y = y * x) {l n : ℕ}
    (b : Fin l → Fin n → R) (e : Fin l → R) (c : Fin n → R) :
    ∑ i : Fin n, (∑ k : Fin l, b k i * e k) * c i
      = ∑ k : Fin l, e k * ∑ i : Fin n, b k i * c i := by
  simpa [Finset.sum_mul, Finset.mul_sum, mul_assoc, hc _ (e _)] using
    (Finset.sum_comm : _ = ∑ k, ∑ i, e k * (b k i * c i))

end Algebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- `LocallyFactorsRelations O F U m n A s` says that the `m` relations recorded by the matrix
`A : Fin n → Fin m → O(U)` among the sections `s : Fin n → F(U)` admit, locally on `U`, a
factorisation of `s` through a finite free module annihilating `A`: there is a covering sieve `S`
of `U` such that every `f : V ⟶ U` in `S` admits sections `t : Fin l → F(V)` and a matrix
`B : Fin l → Fin n → O(V)` with `s i |_V = ∑ k, B k i • t k` and `B ∘ A|_V = 0`. -/
abbrev LocallyFactorsRelations (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) (U : C) (m n : ℕ)
    (A : Fin n → Fin m → (commRingSheafToRingSheaf O).obj.obj (op U))
    (s : Fin n → F.val.obj (op U)) : Prop :=
  ∃ S : Sieve U, (S ∈ J U) ∧
    (∀ {V : C} (f : V ⟶ U), S f →
      ∃ (l : ℕ) (t : Fin l → F.val.obj (op V))
        (B : Fin l → Fin n → (commRingSheafToRingSheaf O).obj.obj (op V)),
        (∀ i : Fin n, (F.val.map f.op).hom (s i) =
          ∑ k : Fin l, B k i • t k) ∧
        (∀ k : Fin l, ∀ j : Fin m,
          ∑ i : Fin n, B k i * ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i j) = 0))

/-- Every *single* relation `∑ i, a i • s i = 0` among sections of `F` over an object `U` admits a
local finite-free factorisation of the sections annihilating that relation. -/
abbrev HasLocalSingleRelationFactorizations (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) : Prop :=
  ∀ (U : C) (n : ℕ) (a : Fin n → (commRingSheafToRingSheaf O).obj.obj (op U))
    (s : Fin n → F.val.obj (op U)),
    (∑ i : Fin n, a i • s i = 0) →
      LocallyFactorsRelations O F U 1 n (fun i _ => a i) s

/-- Every *finite matrix* of relations among sections of `F` over an object `U` admits a local
finite-free factorisation of the sections annihilating all of those relations simultaneously. -/
abbrev HasLocalFiniteRelationFactorizations (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) : Prop :=
  ∀ (U : C) (m n : ℕ) (A : Fin n → Fin m → (commRingSheafToRingSheaf O).obj.obj (op U))
    (s : Fin n → F.val.obj (op U)),
    (∀ j : Fin m, ∑ i : Fin n, A i j • s i = 0) →
      LocallyFactorsRelations O F U m n A s

variable {O : Sheaf J CommRingCat.{w}} {F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)}

/-- The sections of `Stacks.commRingSheafToRingSheaf O` commute: forgetting commutativity to pass
from `CommRingCat` to `RingCat` does not change the underlying ring. -/
lemma ringSheaf_mul_comm (O : Sheaf J CommRingCat.{w}) {X : Cᵒᵖ}
    (a b : (commRingSheafToRingSheaf O).obj.obj X) : a * b = b * a :=
  let : CommRing ((commRingSheafToRingSheaf O).obj.obj X) :=
    inferInstanceAs (CommRing (O.obj.obj X))
  mul_comm a b

/-- Restricting a section of `Stacks.commRingSheafToRingSheaf O` along a composite is restricting
twice. -/
lemma ringSheaf_map_comp_apply (O : Sheaf J CommRingCat.{w}) {X Y Z : Cᵒᵖ} (i : X ⟶ Y) (j : Y ⟶ Z)
    (x : (commRingSheafToRingSheaf O).obj.obj X) :
    ((commRingSheafToRingSheaf O).obj.map (i ≫ j)).hom x =
      ((commRingSheafToRingSheaf O).obj.map j).hom
        (((commRingSheafToRingSheaf O).obj.map i).hom x) := by
  rw [(commRingSheafToRingSheaf O).obj.map_comp]
  rfl

/-- Restriction along `f : V ⟶ U` of a relation `∑ i, a i • s i = 0` is the corresponding relation
between the restricted sections. -/
lemma sum_smul_restrict_eq_zero {U V : C} (f : V ⟶ U) {n : ℕ}
    (a : Fin n → (commRingSheafToRingSheaf O).obj.obj (op U)) (s : Fin n → F.val.obj (op U))
    (h : ∑ i : Fin n, a i • s i = 0) :
    ∑ i : Fin n, ((commRingSheafToRingSheaf O).obj.map f.op).hom (a i) •
      (F.val.map f.op).hom (s i) = 0 := by
  have h₂ := congrArg (F.val.map f.op).hom h
  rw [map_sum] at h₂
  simp only [PresheafOfModules.map_smul] at h₂
  simpa using h₂

/-- The identity factorisation: the restrictions of `s` to `V` are expressed by the identity
matrix in terms of themselves. -/
lemma restrict_eq_sum_single_smul {U V : C} (f : V ⟶ U) {n : ℕ}
    (s : Fin n → F.val.obj (op U)) (i : Fin n) :
    (F.val.map f.op).hom (s i) =
      ∑ k : Fin n, (if k = i then (1 : (commRingSheafToRingSheaf O).obj.obj (op V)) else 0) •
        (F.val.map f.op).hom (s k) := by
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun b _ hb => by rw [ite_eq_right hb]; exact zero_smul _ _),
    show (if i = i then (1 : (commRingSheafToRingSheaf O).obj.obj (op V)) else 0) = 1 by simp]
  exact (one_smul _ _).symm

/-- The single-relation criterion implies the finite-matrix criterion: if every single relation
among sections of `F` factors locally, then so does every finite matrix of `m` relations. -/
theorem LocallyFactorsRelations.of_hasLocalSingleRelationFactorizations
    (h : HasLocalSingleRelationFactorizations O F) (m : ℕ) :
    ∀ (U : C) (n : ℕ) (A : Fin n → Fin m → (commRingSheafToRingSheaf O).obj.obj (op U))
      (s : Fin n → F.val.obj (op U)), (∀ j : Fin m, ∑ i : Fin n, A i j • s i = 0) →
      LocallyFactorsRelations O F U m n A s := by
  induction m with
  | zero =>
    intro U n A s _
    exact ⟨⊤, J.top_mem U, fun {V} f _ =>
      ⟨n, fun i => (F.val.map f.op).hom (s i), fun k i => if k = i then 1 else 0,
        fun i => restrict_eq_sum_single_smul f s i, fun k j => j.elim0⟩⟩
  | succ m ih =>
    intro U n A s hA
    obtain ⟨S, hS, hfac⟩ := h U n (fun i => A i (Fin.last m)) s (hA (Fin.last m))
    have hfac' : ∀ (V : C) (f : V ⟶ U), S f →
        ∃ (l : ℕ) (t : Fin l → F.val.obj (op V))
          (B : Fin l → Fin n → (commRingSheafToRingSheaf O).obj.obj (op V)),
          (∀ i : Fin n, (F.val.map f.op).hom (s i) = ∑ k : Fin l, B k i • t k) ∧
          (∀ k : Fin l, ∑ i : Fin n,
            B k i * ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i (Fin.last m)) = 0) := by
      intro V f hf
      obtain ⟨l, t, B, h₁, h₂⟩ := hfac f hf
      exact ⟨l, t, B, h₁, fun k => h₂ k 0⟩
    choose l t B hB1 hB2 using hfac'
    have key : ∀ (V : C) (f : V ⟶ U) (hf : S f),
        LocallyFactorsRelations O F V m (l V f hf)
          (fun k j => ∑ i : Fin n,
            B V f hf k i * ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i j.castSucc))
          (t V f hf) := by
      intro V f hf
      refine ih V (l V f hf) _ (t V f hf) fun j => ?_
      rw [sum_sum_mul_smul (ringSheaf_mul_comm O) (B V f hf)
        (fun i => ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i j.castSucc)) (t V f hf)]
      refine Eq.trans (Finset.sum_congr rfl fun i _ =>
        congrArg (fun x => ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i j.castSucc) • x)
          (hB1 V f hf i).symm)
        (sum_smul_restrict_eq_zero f (fun i => A i j.castSucc) s (hA j.castSucc))
    choose T hT hTfac using key
    refine ⟨Sieve.bind S fun _ _ hf => T _ _ hf, ?_, ?_⟩
    · exact J.bind_covering hS fun V f hf => hT V f hf
    rintro W _ ⟨V, g, f, hf, hg, rfl⟩
    obtain ⟨p, v, E, hv1, hv2⟩ := hTfac V f hf g hg
    refine ⟨p, v, fun a i => ∑ κ : Fin (l V f hf),
      ((commRingSheafToRingSheaf O).obj.map g.op).hom (B V f hf κ i) * E a κ, fun i => ?_,
      fun a j => ?_⟩
    · have step : (F.val.map (g ≫ f).op).hom (s i)
          = (F.val.map g.op).hom ((F.val.map f.op).hom (s i)) := by
        rw [op_comp, PresheafOfModules.map_comp_apply]
      refine Eq.trans step (Eq.trans ?_ (smul_sum_smul_eq
        (fun κ => ((commRingSheafToRingSheaf O).obj.map g.op).hom (B V f hf κ i)) E v))
      rw [hB1 V f hf i, map_sum]
      exact Finset.sum_congr rfl fun κ _ =>
        Eq.trans (PresheafOfModules.map_smul _ _ _ _)
          (congrArg (fun x => ((commRingSheafToRingSheaf O).obj.map g.op).hom (B V f hf κ i) • x)
              (hv1 κ))
    · have hres : ∀ (κ : Fin (l V f hf)) (j' : Fin (m + 1)),
          ∑ i : Fin n, ((commRingSheafToRingSheaf O).obj.map g.op).hom (B V f hf κ i) *
              ((commRingSheafToRingSheaf O).obj.map (g ≫ f).op).hom (A i j')
            = ((commRingSheafToRingSheaf O).obj.map g.op).hom
                (∑ i : Fin n,
                  B V f hf κ i * ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i j')) := by
        intro κ j'
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, op_comp, ringSheaf_map_comp_apply]
      have hswap : ∀ j' : Fin (m + 1),
          ∑ i : Fin n, (∑ κ : Fin (l V f hf),
              ((commRingSheafToRingSheaf O).obj.map g.op).hom (B V f hf κ i) * E a κ) *
              ((commRingSheafToRingSheaf O).obj.map (g ≫ f).op).hom (A i j')
            = ∑ κ : Fin (l V f hf), E a κ * ((commRingSheafToRingSheaf O).obj.map g.op).hom
                (∑ i : Fin n,
                  B V f hf κ i * ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i j')) := by
        intro j'
        rw [sum_sum_mul_mul (ringSheaf_mul_comm O)
          (fun κ i => ((commRingSheafToRingSheaf O).obj.map g.op).hom (B V f hf κ i))
          (fun κ => E a κ)
          (fun i => ((commRingSheafToRingSheaf O).obj.map (g ≫ f).op).hom (A i j'))]
        exact Finset.sum_congr rfl fun κ _ => congrArg (fun x => E a κ * x) (hres κ j')
      induction j using Fin.lastCases with
      | last =>
        rw [hswap]
        exact Finset.sum_eq_zero fun κ _ => by rw [hB2 V f hf κ, map_zero, mul_zero]
      | cast j' =>
        rw [hswap]
        exact hv2 a j'

/-- For a sheaf of modules on a ringed site, the single-relation and the finite-matrix forms of
the local equational criterion for flatness are equivalent. -/
@[stacks 08FC "parts (2) and (3)"]
theorem hasLocalSingleRelationFactorizations_iff_finite
    (O : Sheaf J CommRingCat.{w}) (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    HasLocalSingleRelationFactorizations O F ↔ HasLocalFiniteRelationFactorizations O F :=
  ⟨fun h U m n A s hA =>
    LocallyFactorsRelations.of_hasLocalSingleRelationFactorizations h m U n A s hA,
    fun h U n a s ha => h U 1 n (fun i _ => a i) s fun _ => ha⟩

end Stacks.SheafOfModules
