module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Colimits and maps of finite presentation: finitely presented maps as colimits

Let `R → S` be a ring map with `S` of finite presentation over `R`. Then there
exist a directed set `(Λ, ≤)` and a system of ring maps `R_λ → S_λ` indexed by
`(Λ, ≤)` such that:

1. (Colimit.) `colim_λ R_λ ≅ R` and `colim_λ S_λ ≅ S`, and under these
   isomorphisms the induced colimit map `colim_λ ψ_λ` corresponds to `R → S`.
2. (Finite type base.) Each `R_λ` is of finite type over `ℤ`.
3. (Finite type fibers.) Each `ψ_λ : R_λ → S_λ` is of finite type.
4. (Cartesian transitions.) For each `λ ≤ μ`, the base change map
   `S_λ ⊗_{R_λ} R_μ → S_μ` is an isomorphism of rings.

All rings are commutative with unit; all ring maps are unital.

## How the statement is encoded

* A directed set is modeled as a nonempty `PartialOrder Λ` with
  `IsDirected Λ (· ≤ ·)` (every pair has an upper bound).
* A system of rings is bundled in `RingSystem`: a family of commutative rings
  together with transition ring homomorphisms satisfying the functoriality
  identities `φ_λλ = id` and `φ_μν ∘ φ_λμ = φ_λν`.
* The colimit of a system of rings is the filtered colimit of rings, computed in
  Mathlib by `Ring.DirectLimit`. The universal cocone maps are
  `Ring.DirectLimit.of` and the universal property is `Ring.DirectLimit.lift`
  together with its uniqueness lemma.
* A system of ring maps is bundled in `RingMapSystem`: two ring systems sharing
  the index set together with ring maps `ψ_λ` forming commuting squares with the
  transition maps. Its colimit is the induced ring map between the colimits,
  `RingMapSystem.colimitMap`.
* The base change map `S_λ ⊗_{R_λ} R_μ → S_μ`, `s ⊗ r ↦ φ^S_λμ(s) · ψ_μ(r)`, is
  `RingMapSystem.baseChange` below.
* Finite type and finite presentation are `RingHom.FiniteType` and
  `RingHom.FinitePresentation`. Finite type over `ℤ` is `Algebra.FiniteType ℤ A`
  for the canonical `ℤ`-algebra structure.
-/

@[expose] public section

universe u v

/-- A system of rings indexed by a directed set `(Λ, ≤)`. It
consists of a family of commutative rings `R i` together with transition ring
maps `φ : R i →+* R j` for `i ≤ j`, satisfying functoriality
(`φ_λλ = id` and `φ_μν ∘ φ_λμ = φ_λν`). -/
structure RingSystem (Λ : Type u) [Preorder Λ] where
  /-- The ring at index `i`. -/
  R : Λ → Type v
  /-- Each `R i` is a commutative ring. -/
  commRing : ∀ i, CommRing (R i)
  /-- The transition map `φ_λμ : R λ →+* R μ` for `λ ≤ μ`. -/
  φ : ∀ ⦃i j : Λ⦄, i ≤ j → R i →+* R j
  /-- Functoriality: `φ_λλ = id`. -/
  φ_self : ∀ (i : Λ) (x : R i), φ (le_refl i) x = x
  /-- Functoriality: `φ_μν ∘ φ_λμ = φ_λν`. -/
  φ_comp : ∀ ⦃i j k : Λ⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : R i),
    φ hjk (φ hij x) = φ (le_trans hij hjk) x

attribute [instance] RingSystem.commRing

/-- The colimit of a system of rings, i.e. the filtered colimit of commutative
rings, realized by `Ring.DirectLimit`. -/
noncomputable def RingSystem.colimit {Λ : Type u} [Preorder Λ] (𝓡 : RingSystem Λ) : Type _ :=
  Ring.DirectLimit 𝓡.R (fun _ _ h => 𝓡.φ h)

/-- The colimit of a system of rings is a commutative ring. -/
noncomputable instance {Λ : Type u} [Preorder Λ] (𝓡 : RingSystem Λ) :
    CommRing 𝓡.colimit := by unfold RingSystem.colimit; infer_instance

/-- The functoriality identities make the family a `DirectedSystem`, so the
`Ring.DirectLimit` API (`of`, `lift`, ...) applies. -/
instance RingSystem.directedSystem {Λ : Type u} [Preorder Λ] (𝓡 : RingSystem Λ) :
    DirectedSystem 𝓡.R (fun _ _ h => 𝓡.φ h) :=
  ⟨𝓡.φ_self, fun _ _ _ _ _ => 𝓡.φ_comp _ _⟩

/-- The canonical cocone map `c_λ : R λ →+* colim R`. -/
noncomputable def RingSystem.ι {Λ : Type u} [Preorder Λ] (𝓡 : RingSystem Λ) (i : Λ) :
    𝓡.R i →+* 𝓡.colimit :=
  Ring.DirectLimit.of 𝓡.R (fun _ _ h => 𝓡.φ h) i

/-- The cocone condition `c_μ ∘ φ_λμ = c_λ`. -/
theorem RingSystem.ι_comp_φ {Λ : Type u} [Preorder Λ] (𝓡 : RingSystem Λ)
    ⦃i j : Λ⦄ (hij : i ≤ j) (x : 𝓡.R i) : 𝓡.ι j (𝓡.φ hij x) = 𝓡.ι i x :=
  Ring.DirectLimit.of_f (i := i) (j := j) hij x

/-- A system of ring maps `R_λ → S_λ`. It consists of a source ring
system, a target ring system (both indexed by the same directed set), and ring
maps `ψ_λ : R_λ →+* S_λ` forming commuting squares with the transition maps. -/
structure RingMapSystem (Λ : Type u) [Preorder Λ] where
  /-- The source system `(R_λ, φ^R)`. -/
  source : RingSystem.{u, v} Λ
  /-- The target system `(S_λ, φ^S)`. -/
  target : RingSystem.{u, v} Λ
  /-- The ring maps `ψ_λ : R_λ →+* S_λ`. -/
  ψ : ∀ i, source.R i →+* target.R i
  /-- The squares commute: `ψ_μ ∘ φ^R_λμ = φ^S_λμ ∘ ψ_λ`. -/
  ψ_comm : ∀ ⦃i j : Λ⦄ (hij : i ≤ j) (x : source.R i),
    ψ j (source.φ hij x) = target.φ hij (ψ i x)

/-- The colimit of a system of ring maps, the induced ring map
`colim_λ ψ_λ : colim R_λ →+* colim S_λ`, defined via the universal property of
the colimit of the source system. -/
noncomputable def RingMapSystem.colimitMap {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (𝓟 : RingMapSystem Λ) : 𝓟.source.colimit →+* 𝓟.target.colimit :=
  Ring.DirectLimit.lift 𝓟.source.R (fun _ _ h => 𝓟.source.φ h) 𝓟.target.colimit
    (fun i => (𝓟.target.ι i).comp (𝓟.ψ i))
    (by
      intro i j hij x
      change 𝓟.target.ι j (𝓟.ψ j (𝓟.source.φ hij x)) = 𝓟.target.ι i (𝓟.ψ i x)
      rw [𝓟.ψ_comm hij]
      exact 𝓟.target.ι_comp_φ hij (𝓟.ψ i x))

/-- The base change map `S_λ ⊗_{R_λ} R_μ →+* S_μ` for `λ ≤ μ`.

Here `R_μ` is an `R_λ`-algebra via `φ^R_λμ` and `S_λ` is an `R_λ`-algebra via
`ψ_λ`; the map sends `s ⊗ r ↦ φ^S_λμ(s) · ψ_μ(r)`. -/
noncomputable def RingMapSystem.baseChange {Λ : Type u} [Preorder Λ]
    (𝓟 : RingMapSystem Λ) ⦃i j : Λ⦄ (hij : i ≤ j) :
    letI := (𝓟.ψ i).toAlgebra; letI := (𝓟.source.φ hij).toAlgebra
    @TensorProduct (𝓟.source.R i) _ (𝓟.target.R i) (𝓟.source.R j) _ _ _ _ →+* 𝓟.target.R j :=
  letI := (𝓟.ψ i).toAlgebra
  letI := (𝓟.source.φ hij).toAlgebra
  letI : Algebra (𝓟.source.R i) (𝓟.target.R j) := ((𝓟.ψ j).comp (𝓟.source.φ hij)).toAlgebra
  let fS : 𝓟.target.R i →ₐ[𝓟.source.R i] 𝓟.target.R j :=
    { 𝓟.target.φ hij with
      commutes' := fun r => (𝓟.ψ_comm hij r).symm }
  let fR : 𝓟.source.R j →ₐ[𝓟.source.R i] 𝓟.target.R j :=
    { 𝓟.ψ j with commutes' := fun _ => rfl }
  (Algebra.TensorProduct.productMap fS fR).toRingHom

/-!
## Outline of the proof

Fix `f : R →+* S` finitely presented, so there is `n`, an `R`-algebra surjection
`g : R[x_1,…,x_n] ↠ S` with finitely generated kernel `(h_1,…,h_m)` (each
`h_k ∈ R[x_1,…,x_n]`); write the finitely many coefficients of all the `h_k` as
`c_1,…,c_N ∈ R`.

The index set.  Let `Λ = {A : Subalgebra ℤ R // A.FG ∧ c_1,…,c_N ∈ A}`, ordered
by inclusion.  This is nonempty (`adjoin ℤ {c_1,…,c_N}` is a member) and directed
(the join of two FG subalgebras is FG and contains the `c_i`, by
`Subalgebra.FG.sup`).  For `A ∈ Λ` put `R_A := A` (a `CommRing`, FG ⇒ finite type
over `ℤ` by `Subalgebra.fg_iff_finiteType`); the transition maps `φ^R_{A≤B}` are
the inclusions `Subalgebra.inclusion`.  Because every element of `R` lies in some
FG subalgebra containing the `c_i` and these are cofinal, the cocone makes
`colim_A R_A ≅ R` (`sourceColimitEquiv`); this is `eR`.  Restricting to `A ⊇ c`
is *essential*: it forces every relation to lift to every `R_A`, so item 4 holds
for all pairs (without it, small `A` would give a degenerate `S_A = 0`, breaking
cartesianness).

The target system.  Since all coefficients of the `h_k` lie in every `A ∈ Λ`,
each `h_k` lifts canonically to `h_{k,A} ∈ R_A[x_1,…,x_n]` (the same polynomial
with coefficients read inside `A`), via the section of `MvPolynomial.map` on the
FG subalgebra.  Put `I_A := (h_{1,A},…,h_{m,A})` and
`S_A := R_A[x_1,…,x_n]/I_A`, with `ψ_A : R_A → S_A` the structure map
`(Ideal.Quotient.mk) ∘ C`.  Each `ψ_A` is finite type (quotient of a polynomial
ring in `n` variables).  For `A ≤ B`, `MvPolynomial.map (inclusion)` sends each
`h_{k,A}` to `h_{k,B}`, hence sends `I_A` into `I_B`, so it descends to a ring
map `φ^S_{A≤B} : S_A → S_B`; functoriality and the commuting squares
`ψ_B ∘ φ^R = φ^S ∘ ψ_A` follow from functoriality of `MvPolynomial.map` and
`Ideal.Quotient.mk`.  This assembles a `RingMapSystem 𝓟` with
`𝓟.source = sourceSystem R`.

Colimit on the target.  Because `R = colim R_A` and `MvPolynomial`, quotients and
ideal-generation all commute with filtered colimits of rings,
`colim_A S_A ≅ R[x_1,…,x_n]/(h_1,…,h_m) ≅ S` (the last iso is `g`); this is `eS`.
The square `f ∘ eR = eS ∘ colim ψ` commutes because on each `R_A` both sides send
`r` to `g(C r)·1 = f(r)`, and the cocone maps generate; uniqueness of maps out of
a colimit (`Ring.DirectLimit.hom_ext`) closes it.

Cartesian transitions.  For `A ≤ B`, base change of
`S_A = R_A[x]/I_A` along `R_A → R_B` is
`R_B ⊗_{R_A} (R_A[x]/I_A) ≅ R_B[x]/(I_A·R_B[x]) = R_B[x]/I_B = S_B`, because the
generators of `I_A` map exactly to those of `I_B` (no new relations are needed
once the coefficients already live in `R_A`).  Concretely the base change map
`S_A ⊗_{R_A} R_B → S_B` is the inverse-up-to-iso of this chain, hence bijective.

This is decomposed into:
* `sourceSystem`            — the (concrete) inclusion system of FG ℤ-subalgebras;
* `sourceColimitEquiv`      — `colim R_A ≅ R` (item 1 source side, and item 2);
* `exists_ringMapSystem_colimit_of_finitePresentation`— the target system + `eS` + items 1,3,4,
  with the
  source fixed to `sourceSystem` and `eR` to `sourceColimitEquiv`.
-/

/-- The index set `Λ` for the construction: finitely generated `ℤ`-subalgebras of
`R` that **contain a fixed finite set `c ⊆ R`** (the coefficients of the chosen
relations), ordered by inclusion.  Restricting to `A ⊇ c` is essential: it makes
the relations live in every `R_A`, so the cartesian condition (item 4) holds for
*all* pairs `A ≤ B`, while the family stays cofinal among all FG subalgebras (so
the colimit is still `R`). -/
abbrev FGSubalg (R : Type u) [CommRing R] (c : Finset R) :=
  { A : Subalgebra ℤ R // A.FG ∧ (c : Set R) ⊆ A }

/-- `adjoin ℤ c` is a member of `FGSubalg R c` (FG and contains `c`), so the index
set is nonempty. -/
instance FGSubalg.nonempty (R : Type u) [CommRing R] (c : Finset R) :
    Nonempty (FGSubalg R c) :=
  ⟨⟨Algebra.adjoin ℤ (c : Set R), Subalgebra.fg_adjoin_finset c, Algebra.subset_adjoin⟩⟩

/-- The poset `FGSubalg R c` is directed: the join of two members is FG
(`Subalgebra.FG.sup`), contains `c`, and dominates both. -/
instance FGSubalg.isDirected (R : Type u) [CommRing R] (c : Finset R) :
    IsDirected (FGSubalg R c) (· ≤ ·) :=
  ⟨fun A B => ⟨⟨A.val ⊔ B.val, A.property.left.sup B.property.left,
      A.property.right.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

/-- The source ring system: `R_A := A` for each `A ∈ FGSubalg R c`, with the
inclusion ring maps as transitions.  Functoriality holds definitionally for
`Subalgebra.inclusion`. -/
@[ega "IV 8.1.2"]
noncomputable def sourceSystem (R : Type u) [CommRing R] (c : Finset R) :
    RingSystem.{u, u} (FGSubalg R c) where
  R := fun A => A.val
  commRing := fun _ => inferInstance
  φ := fun _ _ h => (Subalgebra.inclusion h).toRingHom
  φ_self := by intro i x; rfl
  φ_comp := by intro i j k hij hjk x; rfl

/-- Each `R_A` in `sourceSystem` is of finite type over `ℤ` (item 2): `A` is a
finitely generated subalgebra, and `Subalgebra.fg_iff_finiteType` turns
`A.FG` into `Algebra.FiniteType ℤ A`. -/
theorem sourceSystem_finiteType (R : Type u) [CommRing R] (c : Finset R) (A : FGSubalg R c) :
    Algebra.FiniteType ℤ ((sourceSystem R c).R A) :=
  (Subalgebra.fg_iff_finiteType A.val).mp A.property.left

/-- **Item 1, source side.** `R` is the filtered colimit of the FG `ℤ`-subalgebras
containing `c`.

Proof outline.  The cocone maps `ι_A : A → R` are the subalgebra inclusions,
which are compatible with the transitions, so by the universal property they
induce `e : colim_A R_A →+* R` (`Ring.DirectLimit.lift`).  `e` is *surjective*:
every `r : R` lies in `adjoin ℤ (insert r c)`, which is FG (`fg_adjoin_finset`)
and contains `c`, hence is a member `A_r ∈ FGSubalg R c`, and
`e (ι_{A_r} ⟨r, _⟩) = r`.  `e` is *injective*: by `Ring.DirectLimit.exists_of`
any element of the colimit is `ι_A x` for some `A` and `x : A`, and the
inclusions `A ↪ R` are injective, so `Ring.DirectLimit.lift_injective` applies.
Hence `e` is a ring isomorphism `colim R_A ≃+* R`.  (The restriction to `A ⊇ c`
is harmless: the family is still cofinal among all FG subalgebras, since enlarging
any `A` to `A ⊔ adjoin ℤ c` keeps it FG and adds `c`.) -/
@[ega "IV 8.1.2"]
noncomputable def sourceColimitEquiv (R : Type u) [CommRing R] (c : Finset R) :
    (sourceSystem R c).colimit ≃+* R := by
  -- `adjoin ℤ (insert r c)`, injective via injective inclusions + `lift_injective`;
  -- edge cases R trivial / c empty fine).
  classical
  -- The underlying ring hom `e : colim R_A →+* R`, induced by the inclusions `A ↪ R`,
  -- packaged directly into `RingEquiv.ofBijective` (kept inline so the `Ring.DirectLimit`
  -- API lemmas match syntactically).
  refine RingEquiv.ofBijective
    (Ring.DirectLimit.lift (sourceSystem R c).R (fun _ _ h => (sourceSystem R c).φ h) R
      (fun A => A.val.val.toRingHom)
      (by intro i j hij x; rfl)) ⟨?_, ?_⟩
  · -- injectivity: each inclusion `A ↪ R` is injective
    apply Ring.DirectLimit.lift_injective
    intro A
    exact Subtype.val_injective
  · -- surjectivity: `r` lives in the FG subalgebra `adjoin ℤ (insert r c)`
    intro r
    set A_r : Subalgebra ℤ R := Algebra.adjoin ℤ (insert r (c : Set R)) with hA_r
    have hfg : A_r.FG := by
      rw [hA_r, ← Finset.coe_insert]
      exact Subalgebra.fg_adjoin_finset _
    have hc : (c : Set R) ⊆ A_r := by
      rw [hA_r]
      exact (Set.subset_insert _ _).trans Algebra.subset_adjoin
    have hr : r ∈ A_r := by
      rw [hA_r]
      exact Algebra.subset_adjoin (Set.mem_insert _ _)
    let A : FGSubalg R c := ⟨A_r, hfg, hc⟩
    refine ⟨Ring.DirectLimit.of (sourceSystem R c).R
      (fun _ _ h => (sourceSystem R c).φ h) A ⟨r, hr⟩, ?_⟩
    -- `e (ι_A ⟨r,_⟩) = (A.1).val ⟨r,_⟩ = r` by the colimit computation rule
    exact @Ring.DirectLimit.lift_of (FGSubalg R c) _ (sourceSystem R c).R _
      (fun _ _ h => (sourceSystem R c).φ h) R _
      (fun A => A.val.val.toRingHom) (by intro i j hij x; rfl) A ⟨r, hr⟩

/-! ### Construction of the target system

The following block builds the target ring-map system `S_A = R_A[x_1,…,x_n]/I_A`
over the index set `FGSubalg R c`, the colimit isomorphism `eS : colim S_A ≃+* S`,
and the four items.  Each piece is factored into a named lemma/def so the
`exists_ringMapSystem_colimit_of_finitePresentation` proof is a short assembly. -/

open Classical in
/-- Lift of a polynomial `p ∈ MvPolynomial (Fin n) R` whose coefficients all lie in
the subalgebra `A` to `MvPolynomial (Fin n) A` (the same polynomial, coefficients
read inside `A`; coefficients outside `A` are sent to `0`, harmless when they all
lie in `A`). -/
noncomputable def liftPoly {R : Type u} [CommRing R] (n : ℕ)
    (A : Subalgebra ℤ R) (p : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) A :=
  ∑ m ∈ p.support, MvPolynomial.monomial m
    (if h : p.coeff m ∈ A then (⟨p.coeff m, h⟩ : A) else 0)

/-- `liftPoly` is a genuine lift: mapping it back along `A ↪ R` returns `p`, provided
all coefficients of `p` lie in `A`. -/
theorem map_liftPoly {R : Type u} [CommRing R] (n : ℕ)
    (A : Subalgebra ℤ R) (p : MvPolynomial (Fin n) R) (hp : ∀ m, p.coeff m ∈ A) :
    MvPolynomial.map (A.subtype : A →+* R) (liftPoly n A p) = p := by
  unfold liftPoly
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum p]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dite_eq_left (hp m), MvPolynomial.map_monomial]
  rfl

/-- `liftPoly` commutes with the subalgebra inclusion `A ↪ B` (for `A ≤ B`):
lifting `p` to `A` then including into `B` equals lifting `p` directly to `B`.
Both sides map to `p` in `MvPolynomial (Fin n) R` along the injective
`map (B.subtype)`, since `B.subtype ∘ inclusion = A.subtype`. -/
theorem liftPoly_map_inclusion {R : Type u} [CommRing R] (n : ℕ)
    {A B : Subalgebra ℤ R} (h : A ≤ B) (p : MvPolynomial (Fin n) R)
    (hp : ∀ m, p.coeff m ∈ A) :
    MvPolynomial.map (Subalgebra.inclusion h).toRingHom (liftPoly n A p) = liftPoly n B p := by
  have hpB : ∀ m, p.coeff m ∈ B := fun m => h (hp m)
  apply MvPolynomial.map_injective (B.subtype : B →+* R) Subtype.val_injective
  rw [MvPolynomial.map_map, map_liftPoly n B p hpB]
  have hcomp : (B.subtype : B →+* R).comp (Subalgebra.inclusion h).toRingHom = (A.subtype : A →+*
      R) := by
    ext x
    rfl
  rw [hcomp, map_liftPoly n A p hp]

/-- The relation ideal `I_A := (h_{1,A},…,h_{m,A})` in `MvPolynomial (Fin n) A`, the
span of the lifted generators. -/
noncomputable def targetIdeal {R : Type u} [CommRing R] (c : Finset R) (n : ℕ)
    (gens : Finset (MvPolynomial (Fin n) R)) (A : FGSubalg R c) :
    Ideal (MvPolynomial (Fin n) A.1) :=
  Ideal.span ((fun p => liftPoly n A.val p) '' (gens : Set (MvPolynomial (Fin n) R)))

/-- A polynomial all of whose nonzero coefficients lie in `A` has all coefficients in `A`. -/
private theorem coeff_mem_of_forall_mem_support {R : Type u} [CommRing R] {n : ℕ}
    (A : Subalgebra ℤ R) {p : MvPolynomial (Fin n) R}
    (h : ∀ m ∈ p.support, p.coeff m ∈ A) (m : Fin n →₀ ℕ) : p.coeff m ∈ A := by
  by_cases hm : m ∈ p.support
  · exact h m hm
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    exact A.zero_mem

/-- The hypothesis bundling that `c` contains every coefficient of every generator;
then for any `A ∈ FGSubalg R c` (so `c ⊆ A`) every coefficient of every generator
lies in `A`.  This is the property that makes `liftPoly` a genuine lift on every
`A`, and is the *reason* the index set is restricted to `A ⊇ c`. -/
def CoeffsIn {R : Type u} [CommRing R] (c : Finset R) (n : ℕ)
    (gens : Finset (MvPolynomial (Fin n) R)) : Prop :=
  ∀ p ∈ gens, ∀ m ∈ p.support, p.coeff m ∈ c

/-- Under `CoeffsIn`, every generator's coefficients lie in every `A ∈ FGSubalg R c`,
since every member of the index set contains `c`. -/
theorem coeff_mem_of_coeffsIn {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens)
    (A : FGSubalg R c) {p : MvPolynomial (Fin n) R} (hpg : p ∈ gens) (m) :
    p.coeff m ∈ A.1 := by
  exact coeff_mem_of_forall_mem_support A.1
    (fun m hm => A.property.right (Finset.mem_coe.mpr (hc p hpg m hm))) m

/-- The transition `map (inclusion)` sends `targetIdeal A` into `targetIdeal B`
(`A ≤ B`).  It suffices to check this on generators: a generator `liftPoly A p`
maps to `liftPoly B p` by `liftPoly_map_inclusion`, which is a generator of
`targetIdeal B`. -/
theorem targetIdeal_map_le {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens)
    {A B : FGSubalg R c} (h : A ≤ B) :
    (targetIdeal c n gens A).map (MvPolynomial.map (Subalgebra.inclusion h).toRingHom)
      ≤ targetIdeal c n gens B := by
  rw [targetIdeal, Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro _ ⟨p, hpg, rfl⟩
  simp only [SetLike.mem_coe, Ideal.mem_comap]
  rw [liftPoly_map_inclusion n h p (fun m => coeff_mem_of_coeffsIn hc A hpg m)]
  exact Ideal.subset_span ⟨p, hpg, rfl⟩

/-- `S_A := MvPolynomial (Fin n) A ⧸ I_A`. -/
abbrev targetRing {R : Type u} [CommRing R] (c : Finset R) (n : ℕ)
    (gens : Finset (MvPolynomial (Fin n) R)) (A : FGSubalg R c) : Type u :=
  MvPolynomial (Fin n) A.val ⧸ targetIdeal c n gens A

/-- The transition map `φ^S_{A≤B} : S_A → S_B` induced by `map (inclusion)`,
well-defined by `targetIdeal_map_le`. -/
noncomputable def targetTrans {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens)
    {A B : FGSubalg R c} (h : A ≤ B) :
    targetRing c n gens A →+* targetRing c n gens B :=
  Ideal.Quotient.lift (targetIdeal c n gens A)
    ((Ideal.Quotient.mk (targetIdeal c n gens B)).comp
      (MvPolynomial.map (Subalgebra.inclusion h).toRingHom))
    (by
      intro a ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact targetIdeal_map_le hc h (Ideal.mem_map_of_mem _ ha))

/-- `targetTrans` on a class `mk q` computes as `mk (map (inclusion) q)`. -/
theorem targetTrans_mk {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens)
    {A B : FGSubalg R c} (h : A ≤ B) (q : MvPolynomial (Fin n) A.1) :
    targetTrans hc h (Ideal.Quotient.mk _ q)
      = Ideal.Quotient.mk _ (MvPolynomial.map (Subalgebra.inclusion h).toRingHom q) := by
  rw [targetTrans, Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- The target ring system `(S_A, φ^S)`.  Functoriality (`φ_self`, `φ_comp`)
follows from `targetTrans_mk` together with functoriality of `MvPolynomial.map`
and of `Subalgebra.inclusion`. -/
noncomputable def targetSystem {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens) :
    RingSystem.{u, u} (FGSubalg R c) where
  R := fun A => targetRing c n gens A
  commRing := fun _ => inferInstance
  φ := fun _ _ h => targetTrans hc h
  φ_self := by
    intro A x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [targetTrans_mk hc (le_refl A) q]
    congr 1
    rw [show (Subalgebra.inclusion (le_refl A)).toRingHom = RingHom.id _ by ext y; rfl,
      MvPolynomial.map_id]
  φ_comp := by
    intro A B C hAB hBC x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [targetTrans_mk hc hAB q, targetTrans_mk hc hBC _, targetTrans_mk hc (le_trans hAB hBC) q,
      MvPolynomial.map_map]
    congr 2

/-- `ψ_A : R_A →+* S_A`, the structure map `(Ideal.Quotient.mk) ∘ C`. -/
noncomputable def targetPsi {R : Type u} [CommRing R] (c : Finset R) (n : ℕ)
    (gens : Finset (MvPolynomial (Fin n) R)) (A : FGSubalg R c) :
    (sourceSystem R c).R A →+* targetRing c n gens A :=
  (Ideal.Quotient.mk (targetIdeal c n gens A)).comp (MvPolynomial.C)

-- needed: `targetMapSystem`'s `ψ_comm` `change`/`simp only [targetPsi]` needs the
-- metavariable type `targetRing c n gens B` to match at `default` transparency
set_option backward.isDefEq.respectTransparency.types false in
/-- The full target ring-map system `𝓟` with `source = sourceSystem R c`.  The
commuting squares `ψ_comm` reduce to naturality of `MvPolynomial.C` under
`MvPolynomial.map` and the inclusion being a ring hom. -/
noncomputable def targetMapSystem {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens) :
    RingMapSystem.{u, u} (FGSubalg R c) where
  source := sourceSystem R c
  target := targetSystem hc
  ψ := fun A => targetPsi c n gens A
  ψ_comm := by
    intro A B h x
    change targetPsi c n gens B ((Subalgebra.inclusion h).toRingHom x)
      = targetTrans hc h (targetPsi c n gens A x)
    simp only [targetPsi, RingHom.comp_apply]
    rw [targetTrans, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    congr 1
    exact (MvPolynomial.map_C _ _).symm

/-- **Item 3 (finite-type fibers).** Each `ψ_A : R_A →+* S_A` is of finite type:
it factors as `MvPolynomial.C` (the polynomial ring in `n` variables over `R_A`
is of finite type over `R_A`) followed by the surjection `Ideal.Quotient.mk`. -/
theorem targetPsi_finiteType {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens)
    (A : FGSubalg R c) : ((targetMapSystem hc).ψ A).FiniteType := by
  simp only [targetMapSystem, targetPsi]
  exact (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp
    (RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType A.val (MvPolynomial (Fin n) A.val)))

-- needed: `baseChange_bijective`'s `rw` on `RingHom.comp` composites only matches once
-- `aux_00r0`'s type unfolds at `default` transparency
set_option backward.isDefEq.respectTransparency.types false in
/-- **Item 4 (cartesian transitions).** For `A ≤ B` the base change map
`S_A ⊗_{R_A} R_B →+* S_B` is bijective.

Proof outline.  Chain the isomorphisms
`R_B ⊗_{R_A} (R_A[x]/I_A) ≅ (R_B ⊗_{R_A} R_A[x]) / (I_A·) ≅ R_B[x]/(I_A·R_B[x])`
and identify `I_A·R_B[x] = I_B`: the generators of `I_A` map exactly to those of
`I_B` (`liftPoly_map_inclusion`).  Below this is carried out concretely, by
exhibiting a two-sided inverse of `𝓟.baseChange h`. -/
theorem baseChange_bijective {R : Type u} [CommRing R] {c : Finset R} {n : ℕ}
    {gens : Finset (MvPolynomial (Fin n) R)} (hc : CoeffsIn c n gens)
    {A B : FGSubalg R c} (h : A ≤ B) :
    Function.Bijective ((targetMapSystem hc).baseChange h) := by
  classical
  -- Algebra instances matching `baseChange`.
  let instPsi : Algebra ((sourceSystem R c).R A) ((targetSystem hc).R A) :=
    ((targetMapSystem hc).ψ A).toAlgebra
  let instPhi : Algebra ((sourceSystem R c).R A) ((sourceSystem R c).R B) :=
    ((targetMapSystem hc).source.φ h).toAlgebra
  let instMix : Algebra ((sourceSystem R c).R A) ((targetSystem hc).R B) :=
    (((targetMapSystem hc).ψ B).comp ((targetMapSystem hc).source.φ h)).toAlgebra
  -- Bridge instances over the fully-reduced codomain forms, so typeclass synthesis
  -- finds them when `(sourceSystem R c).R B` etc. get unfolded.
  let instPhi' : Algebra ((sourceSystem R c).R A) (B.val) := instPhi
  let instPsi' : Algebra ((sourceSystem R c).R A) (targetRing c n gens A) := instPsi
  let instMix' : Algebra ((sourceSystem R c).R A) (targetRing c n gens B) := instMix
  let instPhi'' : Algebra (A.val) (B.val) := instPhi
  let instPsi'' : Algebra (A.val) (targetRing c n gens A) := instPsi
  let instMix'' : Algebra (A.val) (targetRing c n gens B) := instMix
  let instPsi3 : Algebra (A.val) ((targetSystem hc).R A) := instPsi
  let instMix3 : Algebra (A.val) ((targetSystem hc).R B) := instMix
  -- The two algebra homs assembled in `baseChange`.
  set fS : (targetSystem hc).R A →ₐ[(sourceSystem R c).R A] (targetSystem hc).R B :=
    { (targetSystem hc).φ h with
      commutes' := fun r => ((targetMapSystem hc).ψ_comm h r).symm } with hfS
  set fR : (sourceSystem R c).R B →ₐ[(sourceSystem R c).R A] (targetSystem hc).R B :=
    { (targetMapSystem hc).ψ B with commutes' := fun _ => rfl } with hfR
  show Function.Bijective (Algebra.TensorProduct.productMap fS fR).toRingHom
  set Φ := (Algebra.TensorProduct.productMap fS fR).toRingHom with hΦ
  -- The variable images of the inverse: `X i ↦ mk_A(X i) ⊗ 1`.
  set Xim : Fin n → TensorProduct ((sourceSystem R c).R A) ((targetSystem hc).R A) ((sourceSystem R
      c).R B) :=
    fun i => (Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.X i)) ⊗ₜ[(sourceSystem R
        c).R A] (1 : (sourceSystem R c).R B)
    with hXim
  -- The auxiliary ring hom `R_B[x] → T`.
  set aux_00r0 : MvPolynomial (Fin n) ((sourceSystem R c).R B) →+* TensorProduct ((sourceSystem R
      c).R A) ((targetSystem hc).R A) ((sourceSystem R c).R B) :=
    MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight.toRingHom) Xim with haux
  -- `aux_00r0 (C b) = 1 ⊗ b`.
  have haux_C : ∀ b : (sourceSystem R c).R B,
      aux_00r0 (MvPolynomial.C b) = (1 : (targetSystem hc).R A) ⊗ₜ[(sourceSystem R c).R A] b := by
    intro b
    rw [haux, MvPolynomial.eval₂Hom_C]
    simp [Algebra.TensorProduct.includeRight_apply]
  -- `aux_00r0 (X i) = mk_A(X i) ⊗ 1`.
  have haux_X : ∀ i, aux_00r0 (MvPolynomial.X i) = Xim i := by
    intro i; rw [haux, MvPolynomial.eval₂Hom_X']
  -- The key compatibility: `aux_00r0 ∘ map(inclusion) = includeLeft ∘ mk_A`.
  have hβ : aux_00r0.comp (MvPolynomial.map (Subalgebra.inclusion h).toRingHom)
      = (Algebra.TensorProduct.includeLeft (R := (sourceSystem R c).R A)
          (S := (sourceSystem R c).R A) (B := (sourceSystem R c).R B)
          (A := (targetSystem hc).R A)).toRingHom.comp
        (Ideal.Quotient.mk (targetIdeal c n gens A)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      -- both sides on `C a`
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_C, haux_C]
      -- RHS: includeLeft (mk_A (C a)) = includeLeft (ψ_A a) = ψ_A a ⊗ 1
      show (1 : (targetSystem hc).R A) ⊗ₜ[(sourceSystem R c).R A] ((Subalgebra.inclusion
          h).toRingHom a)
          = Algebra.TensorProduct.includeLeft
              (Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.C a))
      -- both equal `algebraMap R_A T a`.
      have e1 : (Subalgebra.inclusion h).toRingHom a
          = (algebraMap ((sourceSystem R c).R A) ((sourceSystem R c).R B)) a := rfl
      have e2 : Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.C a)
          = (algebraMap ((sourceSystem R c).R A) ((targetSystem hc).R A)) a := rfl
      rw [e1, e2, ← Algebra.TensorProduct.includeRight_apply]
      exact (Algebra.TensorProduct.includeRight.commutes a).trans
        (Algebra.TensorProduct.includeLeft.commutes a).symm
    · intro i
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_X, haux_X, hXim]
      show (Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.X i)) ⊗ₜ[(sourceSystem R
          c).R A] (1 : (sourceSystem R c).R B)
          = Algebra.TensorProduct.includeLeft
              (Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.X i))
      rw [Algebra.TensorProduct.includeLeft_apply]
  -- `aux_00r0` kills `I_B`, so it descends to `Ψ : S_B → T`.
  have haux_ker : ∀ q ∈ targetIdeal c n gens B, aux_00r0 q = 0 := by
    have hle : targetIdeal c n gens B ≤ RingHom.ker aux_00r0 := by
      rw [targetIdeal, Ideal.span_le]
      rintro _ ⟨p, hp, rfl⟩
      rw [Finset.mem_coe] at hp
      show aux_00r0 (liftPoly n B.val p) = 0
      have hco :=
        congrArg (fun (φ : MvPolynomial (Fin n) A.val →+* _) => φ (liftPoly n A.val p)) hβ
      simp only [RingHom.comp_apply] at hco
      have hmem : liftPoly n A.val p ∈ targetIdeal c n gens A :=
        Ideal.subset_span ⟨p, hp, rfl⟩
      calc aux_00r0 (liftPoly n B.val p)
          = aux_00r0 (MvPolynomial.map (Subalgebra.inclusion h).toRingHom
              (liftPoly n A.val p)) := by
            rw [← liftPoly_map_inclusion n h p (fun m => coeff_mem_of_coeffsIn hc A hp m)]
        _ = Algebra.TensorProduct.includeLeft
              (Ideal.Quotient.mk (targetIdeal c n gens A) (liftPoly n A.val p)) := hco
        _ = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem]; exact map_zero _
    intro q hq
    rw [← RingHom.mem_ker]; exact hle hq
  set Ψ : (targetSystem hc).R B →+* TensorProduct ((sourceSystem R c).R A) ((targetSystem hc).R A)
      ((sourceSystem R c).R B) :=
    Ideal.Quotient.lift (targetIdeal c n gens B) aux_00r0 haux_ker with hΨ
  have hΨ_mk : ∀ q, Ψ (Ideal.Quotient.mk (targetIdeal c n gens B) q) = aux_00r0 q := by
    intro q; rw [hΨ]; exact Ideal.Quotient.lift_mk _ _ _
  -- `Φ` applied to a pure tensor.
  have hΦ_tmul : ∀ (s : (targetSystem hc).R A) (r : (sourceSystem R c).R B),
      Φ (s ⊗ₜ[(sourceSystem R c).R A] r) = (targetTrans hc h s) * (targetPsi c n gens B r) := by
    intro s r
    rw [hΦ]
    show (Algebra.TensorProduct.productMap fS fR) (s ⊗ₜ[(sourceSystem R c).R A] r) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  -- Bijectivity via the explicit two-sided inverse `Ψ`.
  rw [Function.bijective_iff_has_inverse]
  refine ⟨Ψ, ?_, ?_⟩
  · -- LeftInverse Ψ Φ : ∀ x : T, Ψ (Φ x) = x
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s r =>
      -- s ⊗ r = (s ⊗ 1) * (1 ⊗ r)
      have hsplit : s ⊗ₜ[(sourceSystem R c).R A] r
          = (s ⊗ₜ[(sourceSystem R c).R A] (1 : (sourceSystem R c).R B))
            * ((1 : (targetSystem hc).R A) ⊗ₜ[(sourceSystem R c).R A] r) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit, map_mul, map_mul]
      -- Reduce s to mk_A qa
      obtain ⟨qa, rfl⟩ := Ideal.Quotient.mk_surjective
        (I := targetIdeal c n gens A) s
      congr 1
      · -- Ψ (Φ (mk_A qa ⊗ 1)) = mk_A qa ⊗ 1
        rw [hΦ_tmul]
        rw [show (targetPsi c n gens B) (1 : (sourceSystem R c).R B) = 1 from map_one _, mul_one]
        rw [targetTrans_mk hc h qa, hΨ_mk]
        have hco := congrArg (fun (φ : MvPolynomial (Fin n) A.val →+* _) => φ qa) hβ
        simp only [RingHom.comp_apply] at hco
        exact hco.trans (Algebra.TensorProduct.includeLeft_apply _)
      · -- Ψ (Φ (1 ⊗ r)) = 1 ⊗ r
        rw [hΦ_tmul]
        rw [show (targetTrans hc h) (1 : (targetSystem hc).R A) = 1 from map_one _, one_mul]
        show Ψ (Ideal.Quotient.mk (targetIdeal c n gens B) (MvPolynomial.C r)) = _
        rw [hΨ_mk]; exact haux_C r
  · -- RightInverse Ψ Φ : ∀ y : S_B, Φ (Ψ y) = y
    intro y
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := targetIdeal c n gens B) y
    rw [hΨ_mk]
    -- Φ (aux_00r0 q) = mk_B q ; prove via ring_hom_ext on `q`.
    have hring : Φ.comp aux_00r0 = Ideal.Quotient.mk (targetIdeal c n gens B) := by
      apply MvPolynomial.ringHom_ext
      · intro b
        rw [RingHom.comp_apply, haux_C, hΦ_tmul]
        rw [show (targetTrans hc h) (1 : (targetSystem hc).R A) = 1 from map_one _, one_mul]
        rfl
      · intro i
        rw [RingHom.comp_apply, haux_X, hXim, hΦ_tmul]
        rw [show (targetPsi c n gens B) (1 : (sourceSystem R c).R B) = 1 from map_one _, mul_one]
        rw [targetTrans_mk hc h (MvPolynomial.X i), MvPolynomial.map_X]
        rfl
    have := congrArg (fun (φ : MvPolynomial (Fin n) ((sourceSystem R c).R B) →+* _) => φ q) hring
    simp only [RingHom.comp_apply] at this
    exact this

/-- Helper for the injectivity direction of `targetColimitEquiv`: if a class
`mk q` in `S_A` is sent to `0` by the component map `g ∘ (map A.subtype)`, then its
image `ι_A (mk q)` in the colimit is already `0`.  The point is that the relation
`map A.subtype q ∈ ker g = span gens` lifts to a *larger* FG subalgebra `B ⊇ A`
(containing the coefficients of the witnessing combination), where `q` itself
becomes a combination of lifted generators, i.e. lands in `I_B`. -/
theorem targetColimit_ι_eq_zero {R S : Type u} [CommRing R] [CommRing S]
    {c : Finset R} {n : ℕ} {gens : Finset (MvPolynomial (Fin n) R)}
    (hc : CoeffsIn c n gens)
    (g : MvPolynomial (Fin n) R →+* S)
    (hker : RingHom.ker g = Ideal.span (gens : Set (MvPolynomial (Fin n) R)))
    (A : FGSubalg R c) (q : MvPolynomial (Fin n) A.1)
    (hq : g (MvPolynomial.map A.1.subtype q) = 0) :
    (targetSystem hc).ι A (Ideal.Quotient.mk (targetIdeal c n gens A) q) = 0 := by
  classical
  -- `map A.subtype q ∈ ker g = span gens`, so it is a finite combination of gens.
  have hmem : MvPolynomial.map A.val.subtype q ∈ Ideal.span (gens : Set (MvPolynomial (Fin n)
      R)) := by
    rw [← hker, RingHom.mem_ker]; exact hq
  rw [Ideal.span, Submodule.mem_span_finset] at hmem
  obtain ⟨fp, _, hcomb⟩ := hmem
  -- `D` := all coefficients of all witness multipliers `fp p` (for `p ∈ gens`).
  set D : Finset R := gens.biUnion (fun p => (fp p).support.image (fun m => (fp p).coeff m))
    with hD
  -- The enlarged FG subalgebra `B ⊇ A` containing `D`.
  set B0 : Subalgebra ℤ R := A.val ⊔ Algebra.adjoin ℤ (D : Set R) with hB0
  have hB0fg : B0.FG := A.property.left.sup (Subalgebra.fg_adjoin_finset D)
  have hAB0 : A.val ≤ B0 := le_sup_left
  have hcB0 : (c : Set R) ⊆ B0 := A.property.right.trans (SetLike.coe_subset_coe.mpr hAB0)
  set B : FGSubalg R c := ⟨B0, hB0fg, hcB0⟩ with hB
  have hAB : A ≤ B := hAB0
  -- Every coefficient of every `fp p` (for `p ∈ gens`) lies in `B`.
  have hfpB : ∀ p ∈ gens, ∀ m, (fp p).coeff m ∈ B.val := by
    intro p hp
    refine coeff_mem_of_forall_mem_support _ fun m hm => ?_
    refine (le_sup_right : Algebra.adjoin ℤ (D : Set R) ≤ _) ?_
    refine Algebra.subset_adjoin ?_
    rw [hD, Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_image_of_mem _ hm⟩
  -- Every coefficient of every generator `p` lies in `B`.
  have hpB : ∀ p ∈ gens, ∀ m, p.coeff m ∈ B.val := fun p hp m => coeff_mem_of_coeffsIn hc B hp m
  -- The lifted relation holds in `MvPolynomial (Fin n) B`.
  have hrel : MvPolynomial.map (Subalgebra.inclusion hAB).toRingHom q
      = ∑ p ∈ gens, liftPoly n B.val (fp p) * liftPoly n B.val p := by
    apply MvPolynomial.map_injective (B.val.subtype) Subtype.val_injective
    rw [map_sum]
    have hL : MvPolynomial.map (B.val.subtype)
        (MvPolynomial.map (Subalgebra.inclusion hAB).toRingHom q)
        = MvPolynomial.map A.val.subtype q := by
      rw [MvPolynomial.map_map]; rfl
    rw [hL, ← hcomb]
    apply Finset.sum_congr rfl
    intro p hp
    rw [map_mul, map_liftPoly n B.val (fp p) (hfpB p hp), map_liftPoly n B.val p (hpB p hp),
      smul_eq_mul]
  -- Hence `mk (map (inclusion) q) = 0` in `S_B`, because the RHS lies in `I_B`.
  have hzeroB : Ideal.Quotient.mk (targetIdeal c n gens B)
      (MvPolynomial.map (Subalgebra.inclusion hAB).toRingHom q) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, hrel]
    exact sum_mem fun p hp => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, hp, rfl⟩)
  -- Transport along the cocone: `ι_A (mk q) = ι_B (φ (mk q)) = ι_B 0 = 0`.
  rw [← (targetSystem hc).ι_comp_φ hAB (Ideal.Quotient.mk (targetIdeal c n gens A) q)]
  show (targetSystem hc).ι B (targetTrans hc hAB (Ideal.Quotient.mk (targetIdeal c n gens A) q))
      = 0
  rw [targetTrans_mk hc hAB q, hzeroB]
  exact map_zero _

/-- **Item 1 (target colimit isomorphism) `eS`.** `colim_A S_A ≃+* S`, for a
presentation `g : R[x_1,…,x_n] ↠ S` whose kernel is spanned by `gens`.

Proof outline.  Filtered colimits commute with `MvPolynomial`, quotients and ideal
generation, so `colim_A (R_A[x]/I_A) ≅ (colim_A R_A)[x]/(colim I_A) ≅ R[x]/(ker g) ≅ S`,
the last isomorphism being induced by `g`.  Concretely the ring hom
`colim S_A → S` is obtained from the component maps `S_A = R_A[x]/I_A → S`,
`mk q ↦ g (map A.val q)` (well-defined since `g` kills the images of `I_A`); it is
surjective because `g` is and the family is cofinal, and injective because every
relation already lives in some `R_A`. -/
noncomputable def targetColimitEquiv {R S : Type u} [CommRing R] [CommRing S]
    {c : Finset R} {n : ℕ} {gens : Finset (MvPolynomial (Fin n) R)}
    (hc : CoeffsIn c n gens)
    (g : MvPolynomial (Fin n) R →+* S) (hg_surj : Function.Surjective g)
    (hker : RingHom.ker g = Ideal.span (gens : Set (MvPolynomial (Fin n) R))) :
    (targetSystem hc).colimit ≃+* S := by
  classical
  -- Each generator of `ker g` lies in `ker g`.
  have hgen_ker : ∀ p ∈ gens, g p = 0 := by
    intro p hp
    rw [← RingHom.mem_ker, hker]
    exact Ideal.subset_span hp
  -- The component map `S_A → S` is well-defined: `g ∘ (map A.subtype)` kills `I_A`.
  have hwd : ∀ (A : FGSubalg R c), ∀ a ∈ targetIdeal c n gens A,
      (g.comp (MvPolynomial.map A.val.subtype)) a = 0 := by
    intro A a ha
    have hle :
        targetIdeal c n gens A ≤ RingHom.ker (g.comp (MvPolynomial.map A.val.subtype)) := by
      rw [targetIdeal, Ideal.span_le]
      rintro _ ⟨p, hp, rfl⟩
      rw [Finset.mem_coe] at hp
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change (g.comp (MvPolynomial.map A.val.subtype)) (liftPoly n A.val p) = 0
      rw [RingHom.comp_apply,
        map_liftPoly n A.val p (fun m => coeff_mem_of_coeffsIn hc A hp m)]
      exact hgen_ker p hp
    rw [← RingHom.mem_ker]
    exact hle ha
  -- Abbreviation for the component map `S_A → S`.
  set compMap : ∀ (A : FGSubalg R c), targetRing c n gens A →+* S :=
    fun A => Ideal.Quotient.lift (targetIdeal c n gens A)
      (g.comp (MvPolynomial.map A.val.subtype)) (hwd A) with hcompMap
  -- `compMap` on a class `mk q`.
  have hcompMap_mk : ∀ (A : FGSubalg R c) (q : MvPolynomial (Fin n) A.val),
      compMap A (Ideal.Quotient.mk (targetIdeal c n gens A) q)
        = g (MvPolynomial.map A.val.subtype q) := by
    intro A q
    simp only [hcompMap, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  -- The component maps are compatible with the transitions.
  have hcompat : ∀ (i j : FGSubalg R c) (hij : i ≤ j) (x : targetRing c n gens i),
      compMap j (targetTrans hc hij x) = compMap i x := by
    intro i j hij x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := targetIdeal c n gens i) x
    rw [targetTrans_mk hc hij q, hcompMap_mk, hcompMap_mk, MvPolynomial.map_map]
    congr 1
  -- Build `e : colim S_A → S` and package as an equivalence.
  refine RingEquiv.ofBijective
    (Ring.DirectLimit.lift (targetSystem hc).R (fun _ _ h => (targetSystem hc).φ h) S
      compMap hcompat) ⟨?_, ?_⟩
  · -- injectivity
    refine (injective_iff_map_eq_zero _).mpr ?_
    intro z hz
    obtain ⟨A, x, rfl⟩ := Ring.DirectLimit.exists_of (G := (targetSystem hc).R)
      (f := fun _ _ h => (targetSystem hc).φ h) z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := targetIdeal c n gens A) x
    -- `e (of_A (mk q)) = compMap A (mk q) = g (map A.subtype q) = 0`
    have hlo := @Ring.DirectLimit.lift_of (FGSubalg R c) _ (targetSystem hc).R _
      (fun _ _ h => (targetSystem hc).φ h) S _ compMap hcompat A
      (Ideal.Quotient.mk (targetIdeal c n gens A) q)
    have hval : g (MvPolynomial.map A.val.subtype q) = 0 :=
      (hcompMap_mk A q).symm.trans (hlo.symm.trans hz)
    change (targetSystem hc).ι A (Ideal.Quotient.mk (targetIdeal c n gens A) q) = 0
    exact targetColimit_ι_eq_zero hc g hker A q hval
  · -- surjectivity
    intro s
    obtain ⟨P, rfl⟩ := hg_surj s
    -- `A := adjoin ℤ (coeffs of P ∪ c)`.
    set D : Finset R := P.support.image (fun m => P.coeff m) with hD
    set A0 : Subalgebra ℤ R := Algebra.adjoin ℤ ((D ∪ c : Finset R) : Set R) with hA0
    have hA0fg : A0.FG := Subalgebra.fg_adjoin_finset _
    have hcA0 : (c : Set R) ⊆ A0 := by
      refine subset_trans ?_ Algebra.subset_adjoin
      intro x hx
      simp only [Finset.coe_union, Set.mem_union]
      right; exact hx
    set A : FGSubalg R c := ⟨A0, hA0fg, hcA0⟩ with hA
    -- coefficients of `P` lie in `A`.
    have hPA : ∀ m, P.coeff m ∈ A.val := by
      intro m
      by_cases h : m ∈ P.support
      · refine Algebra.subset_adjoin ?_
        simp only [Finset.coe_union, Set.mem_union]
        left
        rw [Finset.mem_coe, hD]
        exact Finset.mem_image_of_mem _ h
      · have : P.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using h
        rw [this]; exact Subalgebra.zero_mem _
    refine ⟨Ring.DirectLimit.of (targetSystem hc).R (fun _ _ h => (targetSystem hc).φ h) A
      (Ideal.Quotient.mk (targetIdeal c n gens A) (liftPoly n A.val P)), ?_⟩
    have hlo := @Ring.DirectLimit.lift_of (FGSubalg R c) _ (targetSystem hc).R _
      (fun _ _ h => (targetSystem hc).φ h) S _ compMap hcompat A
      (Ideal.Quotient.mk (targetIdeal c n gens A) (liftPoly n A.val P))
    exact hlo.trans ((hcompMap_mk A (liftPoly n A.val P)).trans
      (congrArg g (map_liftPoly n A.val P hPA)))

-- needed: `colimit_square`'s `rw` on `RingEquiv.ofBijective` only matches once the
-- `let`-bound `compMap` in the metavariable's type unfolds at `default` transparency
set_option backward.isDefEq.respectTransparency.types false in
/-- **Item 1 (commuting square).** Under `eR := sourceColimitEquiv` and `eS :=
targetColimitEquiv`, the square `f ∘ eR = eS ∘ colimitMap` commutes.

Both sides are ring homs out of the colimit `colim R_A`, so it suffices to check
them on each cocone image `ι_A x`, where both send `x : R_A` to
`f (A.val x) = g (C (A.val x))`: the structure maps agree. -/
theorem colimit_square {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {c : Finset R} {n : ℕ} {gens : Finset (MvPolynomial (Fin n) R)}
    (hc : CoeffsIn c n gens)
    (g : MvPolynomial (Fin n) R →+* S) (hg_surj : Function.Surjective g)
    (hker : RingHom.ker g = Ideal.span (gens : Set (MvPolynomial (Fin n) R)))
    (hfg : ∀ r, f r = g (MvPolynomial.C r)) (x : (targetMapSystem hc).source.colimit) :
    f (sourceColimitEquiv R c x)
      = targetColimitEquiv hc g hg_surj hker ((targetMapSystem hc).colimitMap x) := by
  classical
  obtain ⟨A, y, rfl⟩ := Ring.DirectLimit.exists_of (G := (sourceSystem R c).R)
    (f := fun _ _ h => (sourceSystem R c).φ h) x
  have hLleft : sourceColimitEquiv R c
      (Ring.DirectLimit.of (sourceSystem R c).R
        (fun _ _ h => (sourceSystem R c).φ h) A y) = A.val.val y :=
    @Ring.DirectLimit.lift_of (FGSubalg R c) _ (sourceSystem R c).R _
      (fun _ _ h => (sourceSystem R c).φ h) R _
      (fun A => A.val.val.toRingHom) (by intro i j hij x; rfl) A y
  have hRright : (targetMapSystem hc).colimitMap
      (Ring.DirectLimit.of (sourceSystem R c).R
        (fun _ _ h => (sourceSystem R c).φ h) A y)
      = (targetSystem hc).ι A (targetPsi c n gens A y) :=
    @Ring.DirectLimit.lift_of (FGSubalg R c) _ (sourceSystem R c).R _
      (fun _ _ h => (sourceSystem R c).φ h) (targetSystem hc).colimit _
      (fun i => ((targetSystem hc).ι i).comp (targetPsi c n gens i)) _ A y
  have hRE : targetColimitEquiv hc g hg_surj hker
      ((targetSystem hc).ι A (targetPsi c n gens A y))
      = g (MvPolynomial.C (A.val.val y)) := by
    have hψ : targetPsi c n gens A y
        = Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.C y) := rfl
    rw [hψ]
    have : targetColimitEquiv hc g hg_surj hker
        (Ring.DirectLimit.of (targetSystem hc).R
          (fun _ _ h => (targetSystem hc).φ h) A
          (Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.C y)))
        = g (MvPolynomial.map A.val.subtype (MvPolynomial.C y)) := by
      unfold targetColimitEquiv
      rw [RingEquiv.coe_ofBijective]
      refine (Ring.DirectLimit.lift_of _ _ _ _ _).trans ?_
      exact Ideal.Quotient.lift_mk _ _ _
    rw [show (targetSystem hc).ι A
          (Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.C y))
        = Ring.DirectLimit.of (targetSystem hc).R
          (fun _ _ h => (targetSystem hc).φ h) A
          (Ideal.Quotient.mk (targetIdeal c n gens A) (MvPolynomial.C y)) from rfl]
    rw [this, MvPolynomial.map_C]
    rfl
  calc f (sourceColimitEquiv R c
        (Ring.DirectLimit.of (sourceSystem R c).R
          (fun _ _ h => (sourceSystem R c).φ h) A y))
      = f (A.val.val y) := by rw [hLleft]
    _ = g (MvPolynomial.C (A.val.val y)) := hfg _
    _ = targetColimitEquiv hc g hg_surj hker
          ((targetSystem hc).ι A (targetPsi c n gens A y)) := (hRE).symm
    _ = targetColimitEquiv hc g hg_surj hker
          ((targetMapSystem hc).colimitMap
            (Ring.DirectLimit.of (sourceSystem R c).R
              (fun _ _ h => (sourceSystem R c).φ h) A y)) := by rw [hRright]

/-- **The construction, in full.**  Given the finitely presented map `f`, this
builds the witness package over the concrete index set `Λ = FGSubalg R c` (for a
suitable finite `c ⊆ R`, the coefficients of the chosen relations): a
`RingMapSystem 𝓟` whose source is `sourceSystem R c`, together with the colimit
isomorphisms `eR : colim R_A ≃+* R`, `eS : colim S_A ≃+* S`, and all four items.
The main theorem then follows by packaging `Λ` with its directed and nonempty
instances.

The witness data: `S_A = R_A[x_1,…,x_n]/I_A`, `ψ_A` the structure map, and
`eR := sourceColimitEquiv R c`.  Restricting `Λ` to `A ⊇ c` guarantees every
relation lifts to every `R_A`, so item 4 holds for *all* pairs (no degenerate
`S_A = 0`).  See the outline above for the full informal argument. -/
theorem exists_ringMapSystem_colimit_of_finitePresentation {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S)
    (hf : f.FinitePresentation) :
    ∃ (c : Finset R) (𝓟 : RingMapSystem.{u, u} (FGSubalg R c))
      (eR : 𝓟.source.colimit ≃+* R) (eS : 𝓟.target.colimit ≃+* S),
      (∀ x, f (eR x) = eS (𝓟.colimitMap x)) ∧
      (∀ i, Algebra.FiniteType ℤ (𝓟.source.R i)) ∧
      (∀ i, (𝓟.ψ i).FiniteType) ∧
      (∀ ⦃i j : FGSubalg R c⦄ (hij : i ≤ j), Function.Bijective (𝓟.baseChange hij)) := by
  -- for all pairs — `I_A·R_B[x] = I_B` exactly because `c ⊇` relation coefficients —
  -- and target colimit `colim S_A ≅ S`; no flatness/over-constraint issues).
  classical
  -- Extract the finite presentation: `n`, the surjection `g`, and finite generators
  -- of `ker g`.  Use `f.toAlgebra` so `S` is an `R`-algebra and `f r = g (C r)`.
  let := f.toAlgebra
  rw [RingHom.FinitePresentation] at hf
  obtain ⟨n, g, hg_surj, hker_fg⟩ := hf.out
  -- Finite generators of `ker g` as a `Finset` of polynomials.
  obtain ⟨gensFin, hgens⟩ := hker_fg
  set g' : MvPolynomial (Fin n) R →+* S := g.toRingHom with hg'
  -- `c` := all coefficients of all generators (a finite set).
  set gens : Finset (MvPolynomial (Fin n) R) := gensFin with hgensdef
  set c : Finset R :=
    gens.biUnion (fun p => p.support.image (fun m => p.coeff m)) with hc_def
  -- `CoeffsIn`: every coefficient of every generator lies in `c`.
  have hc : CoeffsIn c n gens := by
    intro p hpg m hm
    rw [hc_def]
    exact Finset.mem_biUnion.mpr ⟨p, hpg, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
  -- `f r = g (C r)`: the structure map of the algebra `S = R[x]/…` via `g`.
  have hfg : ∀ r, f r = g' (MvPolynomial.C r) := by
    intro r
    rw [hg']
    rw [show g.toRingHom (MvPolynomial.C r) = g (MvPolynomial.C r) from rfl]
    rw [MvPolynomial.algHom_C g r]
    rfl
  -- `ker g' = span gens`.
  have hker : RingHom.ker g' = Ideal.span (gens : Set (MvPolynomial (Fin n) R)) := by
    rw [hg', hgensdef]
    exact hgens.symm
  have hg'_surj : Function.Surjective g' := hg_surj
  -- Assemble the witness package.
  refine ⟨c, targetMapSystem hc, sourceColimitEquiv R c,
    targetColimitEquiv hc g' hg'_surj hker, ?_, ?_, ?_, ?_⟩
  · -- item 1: commuting square
    exact colimit_square f hc g' hg'_surj hker hfg
  · -- item 2: finite-type base
    exact sourceSystem_finiteType R c
  · -- item 3: finite-type fibers
    exact targetPsi_finiteType hc
  · -- item 4: cartesian transitions
    exact fun i j hij => baseChange_bijective hc hij

/-- Let `f : R →+* S` be a ring map with `S` of finite presentation over `R`. Then
there is a directed index set `Λ` and a system of ring maps `R_λ → S_λ`
(packaged as `𝓟 : RingMapSystem Λ`) such that:

1. there are ring isomorphisms `eR : colim R_λ ≃+* R` and `eS : colim S_λ ≃+* S`
   intertwining the colimit map `colim ψ` with the given map `f`
   (`f ∘ eR = eS ∘ colim ψ`);
2. each `R_λ` is of finite type over `ℤ`;
3. each `ψ_λ : R_λ →+* S_λ` is of finite type;
4. for each `λ ≤ μ` the base change map `S_λ ⊗_{R_λ} R_μ →+* S_μ` is bijective
   (an isomorphism of rings). -/
@[stacks 00R0]
theorem exists_ringMapSystem_of_finitePresentation {R S : Type u} [CommRing R] [CommRing S] (f : R
  →+* S)
    (hf : f.FinitePresentation) :
    ∃ (Λ : Type u) (_ : PartialOrder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (𝓟 : RingMapSystem.{u, u} Λ)
      (eR : 𝓟.source.colimit ≃+* R) (eS : 𝓟.target.colimit ≃+* S),
      -- (1) Colimit: the square commutes (`f ∘ eR = eS ∘ colim ψ`).
      (∀ x, f (eR x) = eS (𝓟.colimitMap x)) ∧
      -- (2) Finite type base: each `R_λ` is of finite type over `ℤ`.
      (∀ i, Algebra.FiniteType ℤ (𝓟.source.R i)) ∧
      -- (3) Finite type fibers: each `ψ_λ` is of finite type.
      (∀ i, (𝓟.ψ i).FiniteType) ∧
      -- (4) Cartesian transitions: the base change maps are isomorphisms.
      (∀ ⦃i j : Λ⦄ (hij : i ≤ j), Function.Bijective (𝓟.baseChange hij)) := by
  -- Assemble from the concrete index set/source system and the construction kernel.
  -- The construction supplies a finite `c ⊆ R` and the witness package over the
  -- nonempty directed poset `Λ := FGSubalg R c`; items 1–4 come along with it.
  obtain ⟨c, 𝓟, eR, eS, h1, h2, h3, h4⟩ := exists_ringMapSystem_colimit_of_finitePresentation f hf
  exact ⟨FGSubalg R c, inferInstance, inferInstance, inferInstance,
    𝓟, eR, eS, h1, h2, h3, h4⟩
