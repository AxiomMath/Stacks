module

public import StacksFrontier.AlgebraicGeometry.AffineCover.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFamilyDescent
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCompatComparison

/-!
# Descending the transition matrices of a `colim_F 𝒪_X`-module to a finite stage

Let `p` be a prime and let `X` be a quasi-compact quasi-separated scheme in characteristic `p`.
A finite locally free module over the sheaf of rings `colim_F 𝒪_X` of Stacks Tag 0EXB is
trivialised over a finite cover of `X` by affine opens
(`AlgebraicGeometry.exists_finite_affine_subcover`), and its transition matrices
(`Stacks.SheafOfModules.transMat`) have entries in the sections of `colim_F 𝒪_X` over the
pairwise overlaps, which are quasi-compact.

This file descends those matrices: there is a stage `n` and a matrix cocycle over `𝒪_X`
(`Stacks.SheafOfModules.MatrixCocycle`) whose entries map to the given transition matrices under
the stage-`n` coprojection. The two inputs are that finitely many sections of `colim_F 𝒪_X` over
quasi-compact opens come from one stage, and that finitely many relations among sections of
`𝒪_X` that hold after a coprojection hold exactly after one common Frobenius twist — and the
reason twisting is harmless is that the `p ^ k`-th power map is a ring endomorphism, so a
relation built from sums and products survives it, while
`AlgebraicGeometry.frobeniusStructureSheafι_pow_app` says the twisted section has the same image
one stage further along.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitι`: the stage-`n` coprojection `𝒪_X ⟶ colim_F 𝒪_X`, read as
  a morphism of sheaves of rings on the site of opens of `X`, which is the spelling the
  matrix-cocycle API wants.
* `AlgebraicGeometry.rst`: restriction of a section of the structure sheaf along an inclusion of
  opens, with its ring-homomorphism API.

## Main results

* `AlgebraicGeometry.exists_matrixCocycle_of_trivialisation`: **the transition matrices of a
  trivialised `colim_F 𝒪_X`-module descend to a matrix cocycle over `𝒪_X` at a finite stage.**

## Implementation notes

`Γ(X, V)` and `ToType (X.ringSheafOnOpens.obj.obj (op V))` are definitionally equal but not
syntactically so, and likewise for the two spellings of restriction; `AlgebraicGeometry.rst` is
the `X.presheaf` spelling together with the ring-homomorphism lemmas, and
`AlgebraicGeometry.resR_eq_rst` crosses to the spelling
`Stacks.SheafOfModules.MatrixCocycle` is phrased in. Every statement below stays on one side of
that boundary.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius Stacks.SheafOfModules TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### Restriction of sections of the structure sheaf -/

variable {X} in
/-- Restriction of a section of the structure sheaf along an inclusion of opens. -/
noncomputable def rst {V W : X.Opens} (h : W ≤ V) (a : Γ(X, V)) : Γ(X, W) :=
  X.presheaf.map (homOfLE h).op a

variable {X}

/-- `AlgebraicGeometry.rst` is multiplicative. -/
lemma rst_mul {V W : X.Opens} (h : W ≤ V) (a b : Γ(X, V)) :
    rst h (a * b) = rst h a * rst h b := map_mul _ a b

/-- `AlgebraicGeometry.rst` commutes with powers. -/
lemma rst_pow {V W : X.Opens} (h : W ≤ V) (a : Γ(X, V)) (k : ℕ) :
    rst h (a ^ k) = rst h a ^ k := map_pow _ a k

/-- `AlgebraicGeometry.rst` sends `1` to `1`. -/
lemma rst_one {V W : X.Opens} (h : W ≤ V) : rst h (1 : Γ(X, V)) = 1 := map_one _

/-- `AlgebraicGeometry.rst` sends `0` to `0`. -/
lemma rst_zero {V W : X.Opens} (h : W ≤ V) : rst h (0 : Γ(X, V)) = 0 := map_zero _

/-- `AlgebraicGeometry.rst` commutes with finite sums. -/
lemma rst_sum {V W : X.Opens} (h : W ≤ V) {ι : Type*} (s : Finset ι) (f : ι → Γ(X, V)) :
    rst h (∑ i ∈ s, f i) = ∑ i ∈ s, rst h (f i) := map_sum _ f s

/-- Restricting twice, along `W' ≤ W ≤ V`, is restricting along `W' ≤ V`. -/
lemma rst_rst {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (h'' : W' ≤ V) (a : Γ(X, V)) :
    rst h' (rst h a) = rst h'' a := by
  rw [rst, rst, rst, ← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    Subsingleton.elim ((homOfLE h).op ≫ (homOfLE h').op) ((homOfLE h'').op)]

/-- Restricting twice, along `W' ≤ W ≤ V`, is restricting along the composite
`h'.trans h`. -/
lemma rst_rst' {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (a : Γ(X, V)) :
    rst h' (rst h a) = rst (h'.trans h) a :=
  rst_rst h h' (h'.trans h) a

/-- `AlgebraicGeometry.rst` of `if P then 1 else 0` is `if P then 1 else 0`. -/
lemma rst_ite {V W : X.Opens} (h : W ≤ V) (P : Prop) [Decidable P] :
    rst h (if P then (1 : Γ(X, V)) else 0) = if P then 1 else 0 := by
  split_ifs
  exacts [rst_one h, rst_zero h]

/-- The restriction `Stacks.SheafOfModules.resR` of the sheaf of rings on the site of opens is
`AlgebraicGeometry.rst` (definitionally). -/
lemma resR_eq_rst {V W : X.Opens} (h : W ≤ V) (a : Γ(X, V)) :
    resR X.ringSheafOnOpens (homOfLE h) a = rst h a := rfl

variable (X)

/-! ### The coprojection, read on the site of opens -/

/-- The stage-`n` coprojection `𝒪_X ⟶ colim_F 𝒪_X`, read as a morphism of sheaves of rings on
the site of opens of `X`. This is `AlgebraicGeometry.frobeniusStructureSheafι`; only its source
is spelled differently, so that the matrix-cocycle API, which does not unfold `TopCat.Sheaf`,
can see the site and its topology. -/
noncomputable def frobeniusColimitι (n : ℕ) :
    X.ringSheafOnOpens ⟶ frobeniusColimitRingSheaf X p hX :=
  frobeniusStructureSheafι X p hX n

/-- `AlgebraicGeometry.frobeniusColimitι` agrees on sections with
`AlgebraicGeometry.frobeniusStructureSheafι` (definitionally). -/
lemma frobeniusColimitι_hom_app (n : ℕ) (V : X.Opens) (a : Γ(X, V)) :
    (frobeniusColimitι X p hX n).hom.app (op V) a
      = (frobeniusStructureSheafι X p hX n).hom.app (op V) a := rfl

/-- `AlgebraicGeometry.frobeniusColimitι` commutes with restriction to a smaller open. -/
lemma frobeniusColimitι_hom_app_rst (n : ℕ) {V W : X.Opens} (h : W ≤ V) (a : Γ(X, V)) :
    (frobeniusColimitι X p hX n).hom.app (op W) (rst h a)
      = resR (frobeniusColimitRingSheaf X p hX) (homOfLE h)
        ((frobeniusColimitι X p hX n).hom.app (op V) a) :=
  frobeniusStructureSheafι_hom_app_res X p hX n h a

/-- `AlgebraicGeometry.frobeniusColimitι` commutes with finite sums of sections. -/
lemma frobeniusColimitι_hom_app_sum (n : ℕ) (V : X.Opens) {ι : Type*} (s : Finset ι)
    (f : ι → Γ(X, V)) :
    (frobeniusColimitι X p hX n).hom.app (op V) (∑ i ∈ s, f i)
      = ∑ i ∈ s, (frobeniusColimitι X p hX n).hom.app (op V) (f i) :=
  map_sum _ f s

/-- `AlgebraicGeometry.frobeniusColimitι` is multiplicative on sections. -/
lemma frobeniusColimitι_hom_app_mul (n : ℕ) (V : X.Opens) (a b : Γ(X, V)) :
    (frobeniusColimitι X p hX n).hom.app (op V) (a * b)
      = (frobeniusColimitι X p hX n).hom.app (op V) a
        * (frobeniusColimitι X p hX n).hom.app (op V) b :=
  map_mul _ a b

/-- `AlgebraicGeometry.frobeniusColimitι` sends the section `1` to `1`. -/
lemma frobeniusColimitι_hom_app_one (n : ℕ) (V : X.Opens) :
    (frobeniusColimitι X p hX n).hom.app (op V) (1 : Γ(X, V)) = 1 := map_one _

/-- `AlgebraicGeometry.frobeniusColimitι` sends the section `0` to `0`. -/
lemma frobeniusColimitι_hom_app_zero (n : ℕ) (V : X.Opens) :
    (frobeniusColimitι X p hX n).hom.app (op V) (0 : Γ(X, V)) = 0 := map_zero _

/-- The stage-`n + d` image of `a ^ p ^ d` is the stage-`n` image of `a`. -/
lemma frobeniusColimitι_pow_app (n d : ℕ) (V : X.Opens) (a : Γ(X, V)) :
    (frobeniusColimitι X p hX (n + d)).hom.app (op V) (a ^ p ^ d)
      = (frobeniusColimitι X p hX n).hom.app (op V) a :=
  frobeniusStructureSheafι_pow_app X p hX n d V a

/-! ### Descending the transition matrices -/

/-- **The transition matrices of a trivialised `colim_F 𝒪_X`-module descend to a matrix cocycle
over `𝒪_X` at a finite stage.** The matrices have entries in the sections of `colim_F 𝒪_X` over
the pairwise overlaps of the cover, which are quasi-compact because they are intersections of
affine opens in a quasi-separated space; they therefore lift to sections of `𝒪_X` at a common
stage, and raising those lifts to one common `p`-th power makes the cocycle and the diagonal
conditions hold exactly rather than only after a coprojection. -/
theorem exists_matrixCocycle_of_trivialisation [QuasiSeparatedSpace X]
    (G : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX))
    {K : Type u} [Finite K] (V : K → X.Opens) (haff : ∀ k, IsAffineOpen (V k))
    (m : K → ℕ) (t : ∀ k, ULift.{u} (Fin (m k)) → ToType (G.val.obj (op (V k))))
    (hbij : ∀ (k : K) ⦃W : X.Opens⦄ (h : W ≤ V k),
      Function.Bijective (combSections G (t k) (homOfLE h))) :
    ∃ (N : ℕ) (D : MatrixCocycle X.ringSheafOnOpens V m),
      ∀ (k l : K) ⦃W : X.Opens⦄ (hk : W ≤ V k) (hl : W ≤ V l) a b,
        (frobeniusColimitι X p hX N).hom.app (op W) (D.entry k l hk hl a b)
          = transMat G V m t hbij k l hk hl a b := by
  classical
  have hc2 : ∀ k l : K, IsCompact ((V k ⊓ V l : X.Opens) : Set X) := fun k l =>
    isCompact_inf_of_isAffineOpen (haff k) (haff l)
  have hc3 : ∀ k l j : K, IsCompact ((V k ⊓ V l ⊓ V j : X.Opens) : Set X) := fun k l j =>
    QuasiSeparatedSpace.inter_isCompact _ _ (V k ⊓ V l).isOpen (hc2 k l) (V j).isOpen
      (haff j).isCompact
  obtain ⟨n, A, hA⟩ := exists_frobeniusStructureSheafι_app_eq_family X p hX
    (T := Σ q : K × K, ULift.{u} (Fin (m q.1)) × ULift.{u} (Fin (m q.2)))
    (fun q => V q.1.1 ⊓ V q.1.2) (fun q => hc2 _ _)
    (fun q => transMat G V m t hbij q.1.1 q.1.2 inf_le_left inf_le_right q.2.1 q.2.2)
  have himg : ∀ (k l : K) (a : ULift.{u} (Fin (m k))) (b : ULift.{u} (Fin (m l))),
      (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V l)) (A ⟨(k, l), (a, b)⟩)
        = transMat G V m t hbij k l inf_le_left inf_le_right a b :=
    fun k l a b => hA ⟨(k, l), (a, b)⟩
  have himg' : ∀ (k l : K) ⦃W : X.Opens⦄ (hk : W ≤ V k) (hl : W ≤ V l)
      (a : ULift.{u} (Fin (m k))) (b : ULift.{u} (Fin (m l))),
      (frobeniusColimitι X p hX n).hom.app (op W) (rst (le_inf hk hl) (A ⟨(k, l), (a, b)⟩))
        = transMat G V m t hbij k l hk hl a b := fun k l W hk hl a b => by
    rw [frobeniusColimitι_hom_app_rst, himg k l a b,
      transMat_res G V m t hbij k l inf_le_left inf_le_right (le_inf hk hl) a b]
  -- the cocycle condition, after the coprojection
  have hcoc : ∀ (k l j : K) (a : ULift.{u} (Fin (m k))) (c : ULift.{u} (Fin (m j))),
      (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V l ⊓ V j))
          (∑ b, rst (inf_le_left : V k ⊓ V l ⊓ V j ≤ V k ⊓ V l) (A ⟨(k, l), (a, b)⟩) *
            rst (le_inf (inf_le_left.trans inf_le_right : V k ⊓ V l ⊓ V j ≤ V l)
                (inf_le_right : V k ⊓ V l ⊓ V j ≤ V j)) (A ⟨(l, j), (b, c)⟩))
        = (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V l ⊓ V j))
          (rst (le_inf (inf_le_left.trans inf_le_left : V k ⊓ V l ⊓ V j ≤ V k)
              (inf_le_right : V k ⊓ V l ⊓ V j ≤ V j)) (A ⟨(k, j), (a, c)⟩)) := by
    intro k l j a c
    have hk : V k ⊓ V l ⊓ V j ≤ V k := inf_le_left.trans inf_le_left
    have hl : V k ⊓ V l ⊓ V j ≤ V l := inf_le_left.trans inf_le_right
    have hj : V k ⊓ V l ⊓ V j ≤ V j := inf_le_right
    calc (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V l ⊓ V j))
            (∑ b, rst (inf_le_left : V k ⊓ V l ⊓ V j ≤ V k ⊓ V l) (A ⟨(k, l), (a, b)⟩) *
              rst (le_inf hl hj) (A ⟨(l, j), (b, c)⟩))
        = ∑ b, (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V l ⊓ V j))
            (rst (le_inf hk hl) (A ⟨(k, l), (a, b)⟩) * rst (le_inf hl hj) (A ⟨(l, j), (b, c)⟩)) :=
          frobeniusColimitι_hom_app_sum X p hX n (V k ⊓ V l ⊓ V j) Finset.univ _
      _ = ∑ b, transMat G V m t hbij k l hk hl a b * transMat G V m t hbij l j hl hj b c :=
          Finset.sum_congr rfl fun b _ =>
            (frobeniusColimitι_hom_app_mul X p hX n (V k ⊓ V l ⊓ V j) _ _).trans
              (congrArg₂ (· * ·) (himg' k l hk hl a b) (himg' l j hl hj b c))
      _ = transMat G V m t hbij k j hk hj a c := transMat_mul G V m t hbij k l j hk hl hj a c
      _ = (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V l ⊓ V j))
            (rst (le_inf hk hj) (A ⟨(k, j), (a, c)⟩)) := (himg' k j hk hj a c).symm
  obtain ⟨K1, hK1⟩ := exists_pow_eq_of_frobeniusStructureSheafι_app_eq_family X p hX
    (T := Σ q : K × K × K, ULift.{u} (Fin (m q.1)) × ULift.{u} (Fin (m q.2.2)))
    (fun q => V q.1.1 ⊓ V q.1.2.1 ⊓ V q.1.2.2) (fun q => hc3 _ _ _) n
    (fun q => ∑ b, rst (inf_le_left : V q.1.1 ⊓ V q.1.2.1 ⊓ V q.1.2.2 ≤ V q.1.1 ⊓ V q.1.2.1)
          (A ⟨(q.1.1, q.1.2.1), (q.2.1, b)⟩) *
        rst (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            V q.1.1 ⊓ V q.1.2.1 ⊓ V q.1.2.2 ≤ V q.1.2.1 ⊓ V q.1.2.2)
          (A ⟨(q.1.2.1, q.1.2.2), (b, q.2.2)⟩))
    (fun q => rst (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        V q.1.1 ⊓ V q.1.2.1 ⊓ V q.1.2.2 ≤ V q.1.1 ⊓ V q.1.2.2)
      (A ⟨(q.1.1, q.1.2.2), (q.2.1, q.2.2)⟩))
    (fun q => hcoc q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2)
  have hK1' : ∀ (k l j : K) (a : ULift.{u} (Fin (m k))) (c : ULift.{u} (Fin (m j))),
      (∑ b, rst (inf_le_left : V k ⊓ V l ⊓ V j ≤ V k ⊓ V l) (A ⟨(k, l), (a, b)⟩) *
            rst (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
                V k ⊓ V l ⊓ V j ≤ V l ⊓ V j) (A ⟨(l, j), (b, c)⟩)) ^ p ^ K1
        = (rst (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              V k ⊓ V l ⊓ V j ≤ V k ⊓ V j) (A ⟨(k, j), (a, c)⟩)) ^ p ^ K1 :=
    fun k l j a c => hK1 ⟨(k, l, j), (a, c)⟩
  -- the diagonal condition, after the coprojection
  have hdia : ∀ (k : K) (a b : ULift.{u} (Fin (m k))),
      (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V k)) (A ⟨(k, k), (a, b)⟩)
        = (frobeniusColimitι X p hX n).hom.app (op (V k ⊓ V k))
          (if a = b then 1 else 0) := by
    intro k a b
    refine (himg k k a b).trans (Eq.trans (transMat_self G V m t hbij k inf_le_left a b) ?_)
    split_ifs
    exacts [(frobeniusColimitι_hom_app_one X p hX n (V k ⊓ V k)).symm,
      (frobeniusColimitι_hom_app_zero X p hX n (V k ⊓ V k)).symm]
  obtain ⟨K2, hK2⟩ := exists_pow_eq_of_frobeniusStructureSheafι_app_eq_family X p hX
    (T := Σ k : K, ULift.{u} (Fin (m k)) × ULift.{u} (Fin (m k)))
    (fun q => V q.1 ⊓ V q.1) (fun q => hc2 _ _) n
    (fun q => A ⟨(q.1, q.1), (q.2.1, q.2.2)⟩) (fun q => if q.2.1 = q.2.2 then 1 else 0)
    (fun q => hdia q.1 q.2.1 q.2.2)
  have hK2' : ∀ (k : K) (a b : ULift.{u} (Fin (m k))),
      A ⟨(k, k), (a, b)⟩ ^ p ^ K2
        = (if a = b then (1 : Γ(X, V k ⊓ V k)) else 0) ^ p ^ K2 :=
    fun k a b => hK2 ⟨k, a, b⟩
  -- raise every lift to one common power
  have hpne : p ^ max K1 K2 ≠ 0 := pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)
  have hres : ∀ (k l : K) ⦃W W' : X.Opens⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hW : W' ≤ W)
      (a : ULift.{u} (Fin (m k))) (b : ULift.{u} (Fin (m l))),
      resR X.ringSheafOnOpens (homOfLE hW)
          (rst (le_inf hk hl) (A ⟨(k, l), (a, b)⟩ ^ p ^ max K1 K2))
        = rst (le_inf (hW.trans hk) (hW.trans hl)) (A ⟨(k, l), (a, b)⟩ ^ p ^ max K1 K2) :=
    fun k l W W' hk hl hW a b => by rw [resR_eq_rst, rst_rst']
  have hself : ∀ (k : K) ⦃W : X.Opens⦄ (hk : W ≤ V k) (a b : ULift.{u} (Fin (m k))),
      rst (le_inf hk hk) (A ⟨(k, k), (a, b)⟩ ^ p ^ max K1 K2) = if a = b then 1 else 0 := by
    intro k W hk a b
    rw [pow_prime_pow_eq_of_le (le_max_right K1 K2) (hK2' k a b), rst_pow, rst_ite]
    split_ifs
    exacts [one_pow _, zero_pow hpne]
  have hmul : ∀ (k l j : K) ⦃W : X.Opens⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hj : W ≤ V j)
      (a : ULift.{u} (Fin (m k))) (c : ULift.{u} (Fin (m j))),
      ∑ b, rst (le_inf hk hl) (A ⟨(k, l), (a, b)⟩ ^ p ^ max K1 K2) *
          rst (le_inf hl hj) (A ⟨(l, j), (b, c)⟩ ^ p ^ max K1 K2)
        = rst (le_inf hk hj) (A ⟨(k, j), (a, c)⟩ ^ p ^ max K1 K2) := by
    intro k l j W hk hl hj a c
    have h := congrArg (rst (le_inf (le_inf hk hl) hj))
      (pow_prime_pow_eq_of_le (le_max_left K1 K2) (hK1' k l j a c))
    rw [sum_pow_prime_pow_sections X p hX] at h
    simpa only [rst_sum, rst_pow, rst_mul, rst_rst', mul_pow] using h
  refine ⟨n + max K1 K2,
    ⟨fun k l W hk hl a b => rst (le_inf hk hl) (A ⟨(k, l), (a, b)⟩ ^ p ^ max K1 K2),
      hres, hself, hmul⟩, fun k l W hk hl a b => ?_⟩
  change (frobeniusColimitι X p hX (n + max K1 K2)).hom.app (op W)
      (rst (le_inf hk hl) (A ⟨(k, l), (a, b)⟩ ^ p ^ max K1 K2))
    = transMat G V m t hbij k l hk hl a b
  rw [rst_pow, frobeniusColimitι_pow_app]
  exact himg' k l hk hl a b

end AlgebraicGeometry

end
