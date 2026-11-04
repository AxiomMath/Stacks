module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.RingTheory.AffineBlowup.DirectedSystem
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel

/-!
# Descent of flatness along the directed system of affine blowup charts

Let `(R, 𝔪)` be a local domain with fraction field `K`, let `A ⊆ K` be a valuation ring
dominating `R`, and let `𝔪 ≠ 0`.  By Stacks Tag 052M, `A` is the directed union of the affine
blowup charts `R[I/a] ⊆ K` attached to the admissible pairs `(I, a)`. For a quotient of a finite
free module over a polynomial ring with coefficients in a chart, flatness of its base change over
`A` implies flatness over some refining chart. This is the flatness-descent step of Stacks Tag
053I, and an instance of Stacks Tag 02JO (3) (`Module.Flat.eventually_flat_of_directed`).

## Main definitions

* `Stacks.Flatness.BlowupFlattening.vecMap`: componentwise `MvPolynomial.map` on `r`-tuples of
  polynomials.
* `Stacks.Flatness.BlowupFlattening.relSpan`, `Stacks.Flatness.BlowupFlattening.relSpanTop`: the
  span of the relation vectors pushed to a chart, and to `A`.

## Main results

* `Stacks.Flatness.BlowupFlattening.exists_flat_quotient_of_directed`: for a directed system of
  rings `Ar` with an injective jointly surjective cone `ρ : Ar i → Rr`, finitely many
  "relation" vectors over a base stage `i₀`, and the quotient of `(Rr[x₁ … xₙ])^r` by the span
  of their images at the top, flatness of that quotient over `Rr` implies flatness of the
  corresponding stage quotient over `Ar j` for some `j ≥ i₀`.
* `Stacks.Flatness.BlowupFlattening.exists_chart_flat_quotient`: the same statement for the
  system of admissible blowup charts of Stacks Tag 052M.
-/

@[expose] public section

open Stacks.AffineBlowup

universe v

namespace Stacks.Flatness.BlowupFlattening

/-! ### Componentwise application of `MvPolynomial.map` -/

section VecMap

variable {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z]

/-- Componentwise application of `MvPolynomial.map φ` to an `r`-tuple of polynomials, as a map
semilinear over the ring homomorphism `MvPolynomial.map φ`. -/
noncomputable def vecMap (n r : ℕ) (φ : X →+* Y) :
    (Fin r → MvPolynomial (Fin n) X) →ₛₗ[MvPolynomial.map (σ := Fin n) φ]
      (Fin r → MvPolynomial (Fin n) Y) where
  toFun p i := MvPolynomial.map φ (p i)
  map_add' p q := by funext i; simp
  map_smul' c p := by funext i; simp [smul_eq_mul]

/-- The `i`-th component of `vecMap n r φ p` is `MvPolynomial.map φ (p i)`. -/
@[simp]
theorem vecMap_apply (n r : ℕ) (φ : X →+* Y) (p : Fin r → MvPolynomial (Fin n) X) (i : Fin r) :
    vecMap n r φ p i = MvPolynomial.map φ (p i) :=
  rfl

/-- Componentwise `MvPolynomial.map` is functorial in the coefficient homomorphism. -/
theorem vecMap_vecMap (n r : ℕ) (φ : X →+* Y) (ψ : Y →+* Z)
    (p : Fin r → MvPolynomial (Fin n) X) :
    vecMap n r ψ (vecMap n r φ p) = vecMap n r (ψ.comp φ) p := by
  funext i
  simp [MvPolynomial.map_map]

/-- Componentwise `MvPolynomial.map` along the identity is the identity. -/
theorem vecMap_id (n r : ℕ) (p : Fin r → MvPolynomial (Fin n) X) :
    vecMap n r (RingHom.id X) p = p := by
  funext i
  exact MvPolynomial.map_id _

/-- Componentwise `MvPolynomial.map` along an injective coefficient homomorphism is injective. -/
theorem vecMap_injective (n r : ℕ) (φ : X →+* Y) (hφ : Function.Injective φ) :
    Function.Injective (vecMap n r φ) := fun _ _ h ↦
  funext fun i ↦ MvPolynomial.map_injective φ hφ (congrFun h i)

end VecMap

/-! ### Two ingredients of Stacks Tag 02JO (3) -/

/-- **The span of the image of a span.** If a semilinear map `f` carries a finite generating
family `G` of a submodule to a family `G'`, then the span over the target ring of the image of
that submodule is the span of `G'`. -/
theorem span_image_span_range {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {φ : R →+* S}
    (f : M →ₛₗ[φ] N) {m : ℕ} (G : Fin m → M) (G' : Fin m → N) (hG : ∀ x, f (G x) = G' x) :
    Submodule.span S (f '' Submodule.span R (Set.range G)) = Submodule.span S (Set.range G') := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rw [hG]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add u v _ _ ihu ihv =>
      rw [map_add]
      exact Submodule.add_mem _ ihu ihv
    | smul c u _ ihu =>
      rw [map_smulₛₗ]
      exact Submodule.smul_mem _ _ ihu
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact Submodule.subset_span ⟨G i, Submodule.subset_span ⟨i, rfl⟩, hG i⟩

/-- The span of finitely many vectors in a finite free module has finitely presented quotient. -/
private theorem finitePresentation_quotient_span_range {S : Type*} [CommRing S] {r m : ℕ}
    (g : Fin m → (Fin r → S)) :
    Module.FinitePresentation S ((Fin r → S) ⧸ Submodule.span S (Set.range g)) := by
  refine Module.finitePresentation_of_surjective (Submodule.span S (Set.range g)).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_span (Set.finite_range _)

/-- A semilinear map carrying a family `G` to a family `G'` maps `span G` into `span G'`. -/
private theorem span_range_le_comap_span {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {φ : R →+* S}
    (f : M →ₛₗ[φ] N) {m : ℕ} (G : Fin m → M) (G' : Fin m → N) (hG : ∀ x, f (G x) = G' x) :
    Submodule.span R (Set.range G) ≤ Submodule.comap f (Submodule.span S (Set.range G')) := by
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, hG]
  exact Submodule.subset_span ⟨x, rfl⟩

section Gate

variable {Bi Bj : Type*} [CommRing Bi] [CommRing Bj]

/-- If `Qj ⊆ Bj ^ r` is the `Bj`-span of the image of `Qi ⊆ Bi ^ r` along a ring homomorphism
`φ : Bi → Bj`, then the induced map of quotients exhibits `Bj ^ r / Qj` as the base change of
`Bi ^ r / Qi` along `φ`, for the `Bi`-module structure on `Bj ^ r / Qj` given by restriction of
scalars along `φ`. -/
theorem isBaseChange_quotient_gate {r : ℕ} (φ : Bi →+* Bj)
    (Qi : Submodule Bi (Fin r → Bi)) (Qj : Submodule Bj (Fin r → Bj))
    (hQ : Qj = Submodule.span Bj ((fun (p : Fin r → Bi) (i : Fin r) => φ (p i)) '' Qi))
    (g : ((Fin r → Bi) ⧸ Qi) →ₛₗ[φ] ((Fin r → Bj) ⧸ Qj))
    (hg : ∀ p, g (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (M := Fin r → Bj) fun i => φ (p i)) :
    letI algI : Algebra Bi Bj := φ.toAlgebra
    letI modI : Module Bi ((Fin r → Bj) ⧸ Qj) := Module.compHom _ φ
    @IsBaseChange Bi _ _ Bj _ _ _ _ algI _ modI _
      (IsScalarTower.of_algebraMap_smul fun _ _ => rfl)
      ⟨g.toAddHom, g.map_smulₛₗ⟩ := by
  let algI : Algebra Bi Bj := φ.toAlgebra
  have hQ' : Qj = Submodule.span Bj ((Algebra.linearMap Bi Bj).compLeft (Fin r) '' Qi) := hQ
  exact Stacks.QuasiregularSequence.FlatBaseChange.isBaseChange_of_quotient
    (IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap Bi Bj)) Qi Qj hQ'
    (g := ⟨g.toAddHom, g.map_smulₛₗ⟩) hg

end Gate

/-! ### The descent step, for an abstract directed system -/

section Descent

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {Rr : Type v} [CommRing Rr] {Ar : ι → Type v} [∀ i, CommRing (Ar i)]

/-- If the cone `ρ` of a directed system is jointly surjective, then every polynomial over `Rr` is
the image of a polynomial over some stage beyond any prescribed one. -/
theorem exists_stage_map_eq (a : ∀ i j, i ≤ j → Ar i →+* Ar j) (ρ : ∀ i, Ar i →+* Rr)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hρs : ∀ x, ∃ i y, ρ i y = x)
    {n : ℕ} (i₀ : ι) (p : MvPolynomial (Fin n) Rr) :
    ∃ (j : ι) (_ : i₀ ≤ j) (q : MvPolynomial (Fin n) (Ar j)), MvPolynomial.map (ρ j) q = p := by
  classical
  choose g y hg using hρs
  obtain ⟨j, hj⟩ := (insert i₀ (p.support.image fun d ↦ g (MvPolynomial.coeff d p))).exists_le
  have key : ∀ d, ∃ q : Ar j, d ∈ p.support → ρ j q = MvPolynomial.coeff d p := by
    intro d
    by_cases hd : d ∈ p.support
    · exact ⟨a (g (MvPolynomial.coeff d p)) j
        (hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd))) (y _),
          fun _ ↦ (hρ _ _ _ _).trans (hg _)⟩
    · exact ⟨0, fun h ↦ absurd h hd⟩
  choose q hq using key
  refine ⟨j, hj _ (Finset.mem_insert_self _ _), ∑ d ∈ p.support, MvPolynomial.monomial d (q d), ?_⟩
  rw [map_sum]
  refine (Finset.sum_congr rfl fun d hd ↦ ?_).trans (MvPolynomial.support_sum_monomial_coeff p)
  rw [MvPolynomial.map_monomial, hq d hd]

/-- If the cone `ρ` of a directed system is jointly surjective, then every finite family of
polynomials over `Rr` is the image of a family of polynomials over a single stage beyond any
prescribed one. -/
theorem exists_stage_map_eq_family (a : ∀ i j, i ≤ j → Ar i →+* Ar j) (ρ : ∀ i, Ar i →+* Rr)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hρs : ∀ x, ∃ i y, ρ i y = x)
    {n : ℕ} {κ : Type*} [Finite κ] (i₀ : ι) (p : κ → MvPolynomial (Fin n) Rr) :
    ∃ (j : ι) (_ : i₀ ≤ j) (q : κ → MvPolynomial (Fin n) (Ar j)),
      ∀ x, MvPolynomial.map (ρ j) (q x) = p x := by
  classical
  choose cc hcc qq hqq using fun x ↦ exists_stage_map_eq a ρ hρ hρs i₀ (p x)
  obtain ⟨j, hj⟩ := Finite.exists_le fun z : Option κ ↦ z.elim i₀ cc
  have hle : ∀ x, cc x ≤ j := fun x ↦ hj (some x)
  refine ⟨j, hj none, fun x ↦ MvPolynomial.map (a (cc x) j (hle x)) (qq x), fun x ↦ ?_⟩
  rw [MvPolynomial.map_map, show (ρ j).comp (a (cc x) j (hle x)) = ρ (cc x) from
    RingHom.ext (hρ (cc x) j (hle x))]
  exact hqq x

/-- Let `Ar` be a directed system of rings with a cone `ρ : Ar i → Rr` that is jointly
surjective and injective at each stage, so that `Rr` is the colimit and no stage element dies.
Fix `n r : ℕ`, a base stage `i₀` and finitely many relation vectors
`k : Fin m → (Fin r → Ar i₀[x₁ … xₙ])`.  Push them to each later stage `j` along the system and
to `Rr` along the cone, and quotient the finite free module by their span.  If the quotient at
the top is flat over `Rr`, then the quotient at some stage `j ≥ i₀` is flat over `Ar j`. -/
theorem exists_flat_quotient_of_directed (a : ∀ i j, i ≤ j → Ar i →+* Ar j)
    [DirectedSystem Ar fun i j h => a i j h] (ρ : ∀ i, Ar i →+* Rr)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hρs : ∀ x, ∃ i y, ρ i y = x)
    (hρi : ∀ i, Function.Injective (ρ i))
    {n r m : ℕ} (i₀ : ι) (k : Fin m → (Fin r → MvPolynomial (Fin n) (Ar i₀)))
    (hflat : Module.Flat Rr ((Fin r → MvPolynomial (Fin n) Rr) ⧸
      Submodule.span (MvPolynomial (Fin n) Rr) (Set.range fun x => vecMap n r (ρ i₀) (k x)))) :
    ∃ (j : ι) (h : i₀ ≤ j), Module.Flat (Ar j)
      ((Fin r → MvPolynomial (Fin n) (Ar j)) ⧸
        Submodule.span (MvPolynomial (Fin n) (Ar j))
          (Set.range fun x => vecMap n r (a i₀ j h) (k x))) := by
  classical
  have hcomp : ∀ (i j l : ι) (hij : i ≤ j) (hjl : j ≤ l),
      (a j l hjl).comp (a i j hij) = a i l (hij.trans hjl) := fun i j l hij hjl ↦
    RingHom.ext fun x ↦ DirectedSystem.map_map' (fun i j h ↦ a i j h) hij hjl x
  have hself : ∀ i : ι, a i i le_rfl = RingHom.id (Ar i) := fun i ↦
    RingHom.ext fun x ↦ DirectedSystem.map_self' (fun i j h ↦ a i j h) x
  have hρc : ∀ (i j : ι) (h : i ≤ j), (ρ j).comp (a i j h) = ρ i :=
    fun i j h ↦ RingHom.ext (hρ i j h)
  let gen : ∀ i : {j : ι // i₀ ≤ j}, Fin m → (Fin r → MvPolynomial (Fin n) (Ar i.1)) :=
    fun i x ↦ vecMap n r (a i₀ i.1 i.2) (k x)
  let gent : Fin m → (Fin r → MvPolynomial (Fin n) Rr) := fun x ↦ vecMap n r (ρ i₀) (k x)
  let Qf : ∀ i : {j : ι // i₀ ≤ j},
      Submodule (MvPolynomial (Fin n) (Ar i.1)) (Fin r → MvPolynomial (Fin n) (Ar i.1)) :=
    fun i ↦ Submodule.span _ (Set.range (gen i))
  let Qt : Submodule (MvPolynomial (Fin n) Rr) (Fin r → MvPolynomial (Fin n) Rr) :=
    Submodule.span _ (Set.range gent)
  have hgen : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j) (x : Fin m),
      vecMap n r (a i.1 j.1 h) (gen i x) = gen j x := by
    intro i j h x
    show vecMap n r (a i.1 j.1 h) (vecMap n r (a i₀ i.1 i.2) (k x)) = _
    rw [vecMap_vecMap, hcomp]
  have hgent : ∀ (i : {j : ι // i₀ ≤ j}) (x : Fin m),
      vecMap n r (ρ i.1) (gen i x) = gent x := by
    intro i x
    show vecMap n r (ρ i.1) (vecMap n r (a i₀ i.1 i.2) (k x)) = _
    rw [vecMap_vecMap, hρc]
  have hAsys : DirectedSystem (fun i : {j : ι // i₀ ≤ j} ↦ Ar i.1)
      (fun i j h ↦ (a i.1 j.1 h : Ar i.1 →+* Ar j.1)) := by
    refine ⟨?_, ?_⟩
    · intro i x
      exact DirectedSystem.map_self' (fun i j h ↦ a i j h) x
    · intro l j i hij hjl x
      exact DirectedSystem.map_map' (fun i j h ↦ a i j h) hij hjl x
  have hBsys : DirectedSystem
      (fun i : {j : ι // i₀ ≤ j} ↦ MvPolynomial (Fin n) (Ar i.1))
      (fun i j h ↦ (MvPolynomial.map (a i.1 j.1 h) :
        MvPolynomial (Fin n) (Ar i.1) →+* MvPolynomial (Fin n) (Ar j.1))) := by
    refine ⟨?_, ?_⟩
    · intro i p
      show MvPolynomial.map (a i.1 i.1 le_rfl) p = p
      rw [hself]
      exact MvPolynomial.map_id p
    · intro l j i hij hjl p
      show MvPolynomial.map (a j.1 l.1 hjl) (MvPolynomial.map (a i.1 j.1 hij) p) = _
      rw [MvPolynomial.map_map, hcomp]
  have hQle : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j),
      Qf i ≤ Submodule.comap (vecMap n r (a i.1 j.1 h)) (Qf j) := fun i j h ↦
    span_range_le_comap_span _ _ _ (hgen i j h)
  have hνle : ∀ i : {j : ι // i₀ ≤ j}, Qf i ≤ Submodule.comap (vecMap n r (ρ i.1)) Qt := fun i ↦
    span_range_le_comap_span _ _ _ (hgent i)
  let nv : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j),
      ((Fin r → MvPolynomial (Fin n) (Ar i.1)) ⧸ Qf i)
        →ₛₗ[MvPolynomial.map (a i.1 j.1 h)]
      ((Fin r → MvPolynomial (Fin n) (Ar j.1)) ⧸ Qf j) :=
    fun i j h ↦ Submodule.mapQ _ _ (vecMap n r (a i.1 j.1 h)) (hQle i j h)
  let νv : ∀ i : {j : ι // i₀ ≤ j},
      ((Fin r → MvPolynomial (Fin n) (Ar i.1)) ⧸ Qf i)
        →ₛₗ[MvPolynomial.map (ρ i.1)]
      ((Fin r → MvPolynomial (Fin n) Rr) ⧸ Qt) :=
    fun i ↦ Submodule.mapQ _ _ (vecMap n r (ρ i.1)) (hνle i)
  have hNsys : DirectedSystem
      (fun i : {j : ι // i₀ ≤ j} ↦ (Fin r → MvPolynomial (Fin n) (Ar i.1)) ⧸ Qf i)
      (fun i j h ↦ nv i j h) := by
    refine ⟨?_, ?_⟩
    · intro i x
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      show Submodule.Quotient.mk (vecMap n r (a i.1 i.1 le_rfl) p) = _
      rw [hself, vecMap_id]
    · intro l j i hij hjl x
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      show Submodule.Quotient.mk
        (vecMap n r (a j.1 l.1 hjl) (vecMap n r (a i.1 j.1 hij) p)) = _
      rw [vecMap_vecMap, hcomp]
      rfl
  have hσ : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j) (x : MvPolynomial (Fin n) (Ar i.1)),
      MvPolynomial.map (ρ j.1) (MvPolynomial.map (a i.1 j.1 h) x)
        = MvPolynomial.map (ρ i.1) x := fun i j h x ↦ by
    rw [MvPolynomial.map_map, hρc]
  have hν : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j) (x), νv j (nv i j h x) = νv i x := by
    intro i j h x
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (vecMap n r (ρ j.1) (vecMap n r (a i.1 j.1 h) p)) = _
    rw [vecMap_vecMap, hρc]
    rfl
  have hρs' : ∀ x : Rr, ∃ i : {j : ι // i₀ ≤ j}, ∃ y : Ar i.1, ρ i.1 y = x := by
    intro x
    obtain ⟨i, u, hu⟩ := hρs x
    obtain ⟨d, h1, h2⟩ := exists_ge_ge i₀ i
    exact ⟨⟨d, h1⟩, a i d h2 u, (hρ i d h2 u).trans hu⟩
  have hρz : ∀ (i : {j : ι // i₀ ≤ j}) (x : Ar i.1),
      ρ i.1 x = 0 → ∃ j, ∃ h : i ≤ j, a i.1 j.1 h x = 0 := fun i x hx ↦
    ⟨i, le_rfl, by rw [hρi i.1 (hx.trans (map_zero _).symm), map_zero]⟩
  have hσs : ∀ s : MvPolynomial (Fin n) Rr,
      ∃ i : {j : ι // i₀ ≤ j}, ∃ x : MvPolynomial (Fin n) (Ar i.1),
        MvPolynomial.map (ρ i.1) x = s := by
    intro s
    obtain ⟨c, hc, q, hq⟩ :=
      exists_stage_map_eq_family a ρ hρ hρs (κ := Unit) i₀ fun _ ↦ s
    exact ⟨⟨c, hc⟩, q (), hq ()⟩
  have hσz : ∀ (i : {j : ι // i₀ ≤ j}) (x : MvPolynomial (Fin n) (Ar i.1)),
      MvPolynomial.map (ρ i.1) x = 0 →
        ∃ j, ∃ h : i ≤ j, MvPolynomial.map (a i.1 j.1 h) x = 0 := fun i x hx ↦
    ⟨i, le_rfl, by
      rw [MvPolynomial.map_injective _ (hρi i.1) (hx.trans (map_zero _).symm), map_zero]⟩
  have hνs : ∀ x : (Fin r → MvPolynomial (Fin n) Rr) ⧸ Qt, ∃ i y, νv i y = x := by
    intro x
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨c, hc, q, hq⟩ := exists_stage_map_eq_family a ρ hρ hρs (κ := Fin r) i₀ p
    refine ⟨⟨c, hc⟩, Submodule.Quotient.mk q, ?_⟩
    show Submodule.Quotient.mk (vecMap n r (ρ c) q) = Submodule.Quotient.mk p
    congr 1
    exact funext hq
  have hνz : ∀ (i : {j : ι // i₀ ≤ j}) x,
      νv i x = 0 → ∃ j, ∃ h : i ≤ j, nv i j h x = 0 := by
    intro i x hx
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : Submodule.Quotient.mk (p := Qt) (vecMap n r (ρ i.1) p) = 0 := hx
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hx'
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨lam, hlam⟩ := hmem
    obtain ⟨c, hic, mu, hmu⟩ := exists_stage_map_eq_family a ρ hρ hρs i.1 lam
    refine ⟨⟨c, i.2.trans hic⟩, hic, ?_⟩
    have hkey : vecMap n r (a i.1 c hic) p = ∑ z, mu z • gen ⟨c, i.2.trans hic⟩ z := by
      apply vecMap_injective n r (ρ c) (hρi c)
      rw [vecMap_vecMap, hρc, map_sum, ← hlam]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [map_smulₛₗ, hmu z, hgent ⟨c, i.2.trans hic⟩ z]
    show Submodule.Quotient.mk (vecMap n r (a i.1 c hic) p) = 0
    rw [Submodule.Quotient.mk_eq_zero, hkey]
    exact Submodule.sum_mem _ fun z _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, rfl⟩)
  have hab : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j),
      (MvPolynomial.map (σ := Fin n) (a i.1 j.1 h)).comp
          (algebraMap (Ar i.1) (MvPolynomial (Fin n) (Ar i.1)))
        = (algebraMap (Ar j.1) (MvPolynomial (Fin n) (Ar j.1))).comp (a i.1 j.1 h) :=
    fun _ _ _ ↦ MvPolynomial.map_comp_C _
  have hρσ : ∀ i : {j : ι // i₀ ≤ j},
      (MvPolynomial.map (σ := Fin n) (ρ i.1)).comp
          (algebraMap (Ar i.1) (MvPolynomial (Fin n) (Ar i.1)))
        = (algebraMap Rr (MvPolynomial (Fin n) Rr)).comp (ρ i.1) :=
    fun _ ↦ MvPolynomial.map_comp_C _
  have hpush : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j),
      CategoryTheory.IsPushout (CommRingCat.ofHom (a i.1 j.1 h))
        (CommRingCat.ofHom (algebraMap (Ar i.1) (MvPolynomial (Fin n) (Ar i.1))))
        (CommRingCat.ofHom (algebraMap (Ar j.1) (MvPolynomial (Fin n) (Ar j.1))))
        (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) (a i.1 j.1 h))) := by
    intro i j h
    let : Algebra (Ar i.1) (Ar j.1) := (a i.1 j.1 h).toAlgebra
    let : Algebra (MvPolynomial (Fin n) (Ar i.1)) (MvPolynomial (Fin n) (Ar j.1)) :=
      MvPolynomial.algebraMvPolynomial
    exact CommRingCat.isPushout_iff_isPushout.mpr MvPolynomial.instIsPushout
  have hQspan : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j),
      Qf j = Submodule.span (MvPolynomial (Fin n) (Ar j.1))
        ((fun (p : Fin r → MvPolynomial (Fin n) (Ar i.1)) (z : Fin r) ↦
          MvPolynomial.map (a i.1 j.1 h) (p z)) '' Qf i) :=
    fun i j h ↦
      (span_image_span_range (vecMap n r (a i.1 j.1 h)) (gen i) (gen j) (hgen i j h)).symm
  have hfpN : ∀ i : {j : ι // i₀ ≤ j},
      Module.FinitePresentation (MvPolynomial (Fin n) (Ar i.1))
        ((Fin r → MvPolynomial (Fin n) (Ar i.1)) ⧸ Qf i) := fun i ↦
    finitePresentation_quotient_span_range _
  have hfpM : Module.FinitePresentation (MvPolynomial (Fin n) Rr)
      ((Fin r → MvPolynomial (Fin n) Rr) ⧸ Qt) := finitePresentation_quotient_span_range _
  have hflat' : Module.Flat Rr ((Fin r → MvPolynomial (Fin n) Rr) ⧸ Qt) := hflat
  have hbc : ∀ (i j : {j : ι // i₀ ≤ j}) (h : i ≤ j),
      let algI : Algebra (MvPolynomial (Fin n) (Ar i.1)) (MvPolynomial (Fin n) (Ar j.1)) :=
        (MvPolynomial.map (σ := Fin n) (a i.1 j.1 h)).toAlgebra
      let modI : Module (MvPolynomial (Fin n) (Ar i.1))
          ((Fin r → MvPolynomial (Fin n) (Ar j.1)) ⧸ Qf j) :=
        Module.compHom _ (MvPolynomial.map (a i.1 j.1 h))
      @IsBaseChange (MvPolynomial (Fin n) (Ar i.1)) _ _
        (MvPolynomial (Fin n) (Ar j.1)) _ _ _ _ algI _ modI _
        (IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl)
        ⟨(nv i j h).toAddHom, (nv i j h).map_smulₛₗ⟩ :=
    fun i j h ↦ isBaseChange_quotient_gate _ _ _ (hQspan i j h) _ fun _ ↦ rfl
  obtain ⟨i, hi⟩ := Module.Flat.eventually_flat_of_directed
      (R := Rr) (S := MvPolynomial (Fin n) Rr)
      ((Fin r → MvPolynomial (Fin n) Rr) ⧸ Qt)
      (A := fun i : {j : ι // i₀ ≤ j} ↦ Ar i.1)
      (B := fun i : {j : ι // i₀ ≤ j} ↦ MvPolynomial (Fin n) (Ar i.1))
      (N := fun i : {j : ι // i₀ ≤ j} ↦ (Fin r → MvPolynomial (Fin n) (Ar i.1)) ⧸ Qf i)
      (fun i j h ↦ a i.1 j.1 h) (fun i j h ↦ MvPolynomial.map (a i.1 j.1 h))
      nv hab (fun i ↦ ρ i.1) (fun i ↦ MvPolynomial.map (ρ i.1)) νv
      (fun i j h x ↦ hρ i.1 j.1 h x) hσ hν hρσ hρs' hρz hσs hσz hνs hνz hpush hbc
      (fun _ ↦ inferInstance) hfpN
  refine ⟨i.1, i.2, ?_⟩
  have hmod : Module.compHom ((Fin r → MvPolynomial (Fin n) (Ar i.1)) ⧸ Qf i)
      (algebraMap (Ar i.1) (MvPolynomial (Fin n) (Ar i.1)))
      = (inferInstance : Module (Ar i.1) _) :=
    Module.ext' _ _ fun x y ↦
      IsScalarTower.algebraMap_smul (MvPolynomial (Fin n) (Ar i.1)) x y
  have hi' : @Module.Flat (Ar i.1)
      ((Fin r → MvPolynomial (Fin n) (Ar i.1)) ⧸ Qf i) _ _
      (Module.compHom _ (algebraMap (Ar i.1) (MvPolynomial (Fin n) (Ar i.1)))) := hi i le_rfl
  rwa [hmod] at hi'

end Descent

/-! ### The descent step for the system of admissible blowup charts -/

section Chart

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {A : ValuationSubring K}

/-- The relation vectors of `Stacks.Flatness.BlowupFlattening.exists_chart_flat_quotient` pushed
from the base chart `c₀` to a chart `c` refining it. -/
noncomputable def relGen {n r m : ℕ} {c₀ c : AdmissibleChart R A} (h : c₀ ≤ c)
    (k : Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c₀))) :
    Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c)) :=
  fun x ↦ vecMap n r (chartMap c₀ c h) (k x)

/-- The relation vectors of `Stacks.Flatness.BlowupFlattening.exists_chart_flat_quotient` pushed
from the base chart `c₀` to the valuation ring `A` itself. -/
noncomputable def relGenTop {n r m : ℕ} {c₀ : AdmissibleChart R A}
    (k : Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c₀))) :
    Fin m → (Fin r → MvPolynomial (Fin n) (valRing A)) :=
  fun x ↦ vecMap n r (chartToVal c₀) (k x)

/-- The relation submodule at a chart `c` refining `c₀`: the span, over the polynomial ring on
`c`, of the images `Stacks.Flatness.BlowupFlattening.relGen` of the relation vectors. -/
noncomputable def relSpan {n r m : ℕ} {c₀ c : AdmissibleChart R A} (h : c₀ ≤ c)
    (k : Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c₀))) :
    Submodule (MvPolynomial (Fin n) (chartRing c)) (Fin r → MvPolynomial (Fin n) (chartRing c)) :=
  Submodule.span _ (Set.range (relGen h k))

/-- The relation submodule at the valuation ring `A`: the span, over the polynomial ring on `A`,
of the images `Stacks.Flatness.BlowupFlattening.relGenTop` of the relation vectors. -/
noncomputable def relSpanTop {n r m : ℕ} {c₀ : AdmissibleChart R A}
    (k : Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c₀))) :
    Submodule (MvPolynomial (Fin n) (valRing A)) (Fin r → MvPolynomial (Fin n) (valRing A)) :=
  Submodule.span _ (Set.range (relGenTop k))

/-- Let `(R, 𝔪)` be a local domain with fraction field `K` and `𝔪 ≠ 0`, and let `A ⊆ K` be a
valuation ring dominating `R`.  Fix `n r : ℕ`, an admissible chart `c₀` of Stacks Tag 052M and
finitely many relation vectors `k : Fin m → (Fin r → R[I₀/a₀][x₁ … xₙ])`.  Push them to each chart
`c` refining `c₀` and to `A` itself, and quotient the finite free module of rank `r` by their
span.  If the quotient over `A` is flat over `A`, then the quotient over some chart `c ≥ c₀` is
flat over that chart (not over `R`). -/
theorem exists_chart_flat_quotient {n r m : ℕ}
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (hdom : Dominates R A)
    (c₀ : AdmissibleChart R A) (k : Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c₀)))
    (hflat : Module.Flat (valRing A)
      ((Fin r → MvPolynomial (Fin n) (valRing A)) ⧸ relSpanTop k)) :
    ∃ (c : AdmissibleChart R A) (h : c₀ ≤ c),
      Module.Flat (chartRing c)
        ((Fin r → MvPolynomial (Fin n) (chartRing c)) ⧸ relSpan h k) := by
  have := AdmissibleChart.nonempty_of_maximalIdeal_ne_bot hm hdom
  have := AdmissibleChart.isDirected_of_dominates hdom
  exact exists_flat_quotient_of_directed chartMap chartToVal
    (fun _ _ h x ↦ chartToVal_chartMap h x) (chartToVal_surjective hm A hdom)
    chartToVal_injective c₀ k hflat

end Chart

end Stacks.Flatness.BlowupFlattening
