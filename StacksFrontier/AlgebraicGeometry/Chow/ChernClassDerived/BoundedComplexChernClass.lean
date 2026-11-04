module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero

/-!
# The total Chern class of a bounded complex of finite locally free modules

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let `P`
be a complex of `𝒪_Y`-modules whose `n`-th term is finite locally free of constant rank `ρ n`,
with `ρ n = 0` for all but finitely many `n`. Its total Chern class is the total Chow cohomology
class

  `c(P) = ∏_n c(P^n)^{(-1)^n}`,

the product of the total Chern classes of the terms and of their inverses, which is how
[Stacks, Tag 0FAF] and the section it belongs to compute the Chern classes of a perfect object
represented by such a complex. The ring of total classes is not claimed to be commutative, so the
product is taken in increasing order of degrees; it may be taken over any finite set of degrees
outside of which the ranks vanish (`Stacks.Chow.complexChernBounded_eq_prod`), the total Chern
class of a module of rank `0` being `1`.

## Main definitions

* `Stacks.Chow.totalChernUnit` — the total Chern class `c(ℰ)` as a unit.
* `Stacks.Chow.pullbackComplex` — the termwise pullback `h^*P` of a complex.
* `Stacks.Chow.complexChernFactor`, `Stacks.Chow.complexChernProd` — the factor
  `c(P^n)^{(-1)^n}` and the ordered product over a finite set of degrees.
* `Stacks.Chow.complexChernBounded` — the total Chern class `c(P)`.

## Main results

* `Stacks.Chow.TotalChowClass.subsingleton_of_isEmpty` — there is one total class on an empty
  scheme.
* `Stacks.Chow.totalChern_congr`, `Stacks.Chow.totalChern_of_rank_zero` — `c(ℰ)` depends only on
  the isomorphism class of `ℰ`, and is `1` in rank `0`.
* `Stacks.Chow.complexChernBounded_eq_prod` — independence of the finite set of degrees.
* `Stacks.Chow.complexChernBounded_congr_rank`, `Stacks.Chow.complexChernBounded_congr` —
  independence of the rank function and invariance under termwise isomorphism.
* `Stacks.Chow.TotalChowClass.res_complexChernBounded` — `res_h c(P) = c(h^*P)`.
* `Stacks.Chow.isUnit_complexChernBounded` — `c(P)` is a unit.

## References

* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Total classes on an empty scheme -/

section Empty

variable {C : ChowSituation.{u}}

/-- On an empty scheme there is only one total class: every test scheme over it is empty, and
so are its Chow groups. -/
theorem TotalChowClass.subsingleton_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] : Subsingleton (TotalChowClass C sY) := by
  refine ⟨fun c d ↦ TotalChowClass.ext_op fun {T} g _ ↦ ?_⟩
  have : IsEmpty T := ⟨fun t ↦ isEmptyElim (g.base t)⟩
  have := subsingleton_chowGroup_of_isEmpty C (g ≫ sY)
  funext k p
  exact AddMonoidHom.ext fun _ ↦ Subsingleton.elim _ _

end Empty

/-! ### The total Chern class as a unit -/

section TotalChern

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **Invariance of the total Chern class under isomorphism**: isomorphic finite locally free
modules, of ranks spelled differently but equal, have the same total Chern class. -/
theorem totalChern_congr {F F' : Y.Modules} {r r' : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r'] (e : F ≅ F')
    (h : r = r') : totalChern C sY F r = totalChern C sY F' r' := by
  refine TotalChowClass.ext_op fun g _ ↦ eq_of_heq ?_
  rw [op_totalChern, op_totalChern]
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F' r' g
  exact GenuineChern.chernFamily_heq C rfl ((Scheme.Modules.pullback g).mapIso e) h

/-- **The total Chern class in rank zero is `1`.** -/
theorem totalChern_of_rank_zero (F : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 0] :
    totalChern C sY F 0 = 1 := by
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  rw [op_totalChern, TotalChowClass.op_one]
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F 0 g
  exact GenuineChern.chernFamily_of_rank_zero C (g ≫ sY) _

/-- The total Chern class of a module of rank `r = 0` is `1`. -/
theorem totalChern_eq_one_of_rank_eq_zero (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (hr : r = 0) :
    totalChern C sY F r = 1 := by
  subst hr
  exact totalChern_of_rank_zero C sY F

/-- The total Chern class `c(ℰ)` of a finite locally free module of rank `r`, as a unit of the ring
of total classes. -/
def totalChernUnit (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    (TotalChowClass C sY)ˣ :=
  (isUnit_totalChern C sY F r).unit

/-- The unit `Stacks.Chow.totalChernUnit` is the total Chern class. -/
@[simp]
theorem val_totalChernUnit (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    (totalChernUnit C sY F r : TotalChowClass C sY) = totalChern C sY F r :=
  rfl

end TotalChern

/-! ### Products over the sorted members of a finite set -/

section ListProd

/-- Dropping from a list the members on which a function takes the value `1` does not change the
product of its values, in any monoid. -/
theorem list_prod_map_filter_of_eq_one {M α : Type*} [Monoid M] (l : List α) (p : α → Bool)
    (f : α → M) (h : ∀ a ∈ l, p a = false → f a = 1) :
    ((l.filter p).map f).prod = (l.map f).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun b hb ↦ h b (List.mem_cons_of_mem a hb)
    by_cases ha : p a = true
    · simp [ha, ih']
    · simp [ha, ih', h a List.mem_cons_self (by simpa using ha)]

/-- For `t ⊆ s`, the members of the sorted list of `s` lying in `t` form the sorted list of
`t`. -/
theorem filter_sort_eq_sort_of_subset {s t : Finset ℤ} (hts : t ⊆ s) :
    (s.sort (· ≤ ·)).filter (fun n ↦ decide (n ∈ t)) = t.sort (· ≤ ·) := by
  refine List.Perm.eq_of_pairwise' ((s.pairwise_sort _).filter _) (t.pairwise_sort _) ?_
  refine (List.perm_ext_iff_of_nodup ((s.sort_nodup _).filter _) (t.sort_nodup _)).2 fun n ↦ ?_
  simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hts h, h⟩⟩

end ListProd

/-! ### The termwise pullback of a complex -/

/-- The termwise pullback `h^*P` of a complex of `𝒪_Y`-modules along a morphism of schemes
`h : Y' ⟶ Y`. -/
abbrev pullbackComplex {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) (P : CochainComplex Y.Modules ℤ) :
    CochainComplex Y'.Modules ℤ :=
  ((Scheme.Modules.pullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-! ### The total Chern class of a bounded complex of constant ranks -/

section Bounded

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (P : CochainComplex Y.Modules ℤ)

/-- The factor `c(P^n)^{(-1)^n}` of the total Chern class of a complex whose `n`-th term is
finite locally free of rank `ρ n`, as a unit of the ring of total classes. -/
def complexChernFactor (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (n : ℤ) : (TotalChowClass C sY)ˣ :=
  let := hP n
  totalChernUnit C sY (P.X n) (ρ n) ^ ((n.negOnePow : ℤˣ) : ℤ)

/-- A factor of rank `0` is `1`. -/
theorem complexChernFactor_of_eq_zero (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    {n : ℤ} (hn : ρ n = 0) : complexChernFactor C sY P ρ hP n = 1 := by
  let := hP n
  have h1 : totalChernUnit C sY (P.X n) (ρ n) = 1 :=
    Units.ext (totalChern_eq_one_of_rank_eq_zero C sY (P.X n) (ρ n) hn)
  rw [complexChernFactor, h1, one_zpow]

/-- The ordered product `∏_{n ∈ s} c(P^n)^{(-1)^n}`, over the members of a finite set `s` of
degrees in increasing order, as a unit of the ring of total classes. -/
def complexChernProd (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (s : Finset ℤ) : (TotalChowClass C sY)ˣ :=
  ((s.sort (· ≤ ·)).map (complexChernFactor C sY P ρ hP)).prod

/-- Enlarging the finite set of degrees by degrees of rank `0` does not change the product. -/
theorem complexChernProd_eq_of_subset (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    {s t : Finset ℤ} (hts : t ⊆ s) (h : ∀ n ∈ s, n ∉ t → ρ n = 0) :
    complexChernProd C sY P ρ hP s = complexChernProd C sY P ρ hP t := by
  rw [complexChernProd, complexChernProd, ← filter_sort_eq_sort_of_subset hts,
    list_prod_map_filter_of_eq_one]
  intro n hn hnt
  exact complexChernFactor_of_eq_zero C sY P ρ hP
    (h n ((s.mem_sort _).1 hn) (by simpa using hnt))

/-- **The total Chern class of a bounded complex of finite locally free modules of constant
ranks**: for a complex `P` whose `n`-th term is finite locally free of rank `ρ n`, with `ρ`
finitely supported,

  `c(P) = ∏_n c(P^n)^{(-1)^n}`,

the product, in increasing order of degrees, over the degrees of nonzero rank. -/
def complexChernBounded (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n)) :
    TotalChowClass C sY :=
  (complexChernProd C sY P ρ hP ρ.support : TotalChowClass C sY)

/-- **Independence of the support**: the product may be taken over any finite set of degrees
outside of which the ranks vanish. -/
theorem complexChernBounded_eq_prod (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (s : Finset ℤ) (hs : ∀ n ∉ s, ρ n = 0) :
    complexChernBounded C sY P ρ hP = (complexChernProd C sY P ρ hP s : TotalChowClass C sY) := by
  rw [complexChernBounded, complexChernProd_eq_of_subset C sY P ρ hP (s := s) (t := ρ.support)
    (fun n hn ↦ by by_contra h; exact (Finsupp.mem_support_iff.1 hn) (hs n h))
    (fun n _ hn ↦ Finsupp.notMem_support_iff.1 hn)]

/-- The total Chern class of a bounded complex is a unit. -/
theorem isUnit_complexChernBounded (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n)) :
    IsUnit (complexChernBounded C sY P ρ hP) :=
  Units.isUnit _

/-- The ranks of the terms of a complex on a nonempty scheme are determined by the complex, and
on an empty scheme there is a single total class: so the total Chern class does not depend on the
rank function it is computed with. -/
theorem complexChernBounded_congr_rank (ρ σ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (σ n)) :
    complexChernBounded C sY P ρ hP = complexChernBounded C sY P σ hσ := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sY).elim _ _
  · obtain rfl : ρ = σ := Finsupp.ext fun n ↦
      Scheme.Modules.isFiniteLocallyFreeOfRank_unique (P.X n) (hP n) (hσ n) y
    rfl

/-- **Invariance under isomorphism**: complexes with isomorphic terms have the same total Chern
class. -/
theorem complexChernBounded_congr {P' : CochainComplex Y.Modules ℤ} (e : ∀ n, P.X n ≅ P'.X n)
    (ρ σ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hP' : ∀ n,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P'.X n) (σ n)) :
    complexChernBounded C sY P ρ hP = complexChernBounded C sY P' σ hP' := by
  have hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P'.X n)
      (ρ n) := fun n ↦
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (e n) (hP n)
  refine Eq.trans ?_ (complexChernBounded_congr_rank C sY P' ρ σ hρ hP')
  have hfac : complexChernFactor C sY P ρ hP = complexChernFactor C sY P' ρ hρ := by
    funext n
    let := hP n
    let := hρ n
    rw [complexChernFactor, complexChernFactor]
    congr 1
    exact Units.ext (totalChern_congr C sY (e n) rfl)
  simp only [complexChernBounded, complexChernProd, hfac]

/-- The termwise pullback of a complex whose `n`-th term is finite locally free of rank `ρ n` has
`n`-th term finite locally free of rank `ρ n`. -/
theorem isFiniteLocallyFreeOfRank_pullbackComplex_X {Y' : Scheme.{u}} (h : Y' ⟶ Y) (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex h P).X n)
      (ρ n) :=
  have := hP n
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback h (P.X n) (ρ n)

/-- **Restriction of the total Chern class of a bounded complex**: for `h : Y' ⟶ Y`, the
restriction of `c(P)` is the total Chern class of the termwise pullback `h^*P`. -/
theorem TotalChowClass.res_complexChernBounded {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n)) :
    TotalChowClass.res h hs (complexChernBounded C sY P ρ hP) =
      complexChernBounded C sY' (pullbackComplex h P) ρ
        (isFiniteLocallyFreeOfRank_pullbackComplex_X P h ρ hP) := by
  have hfac : ∀ n, Units.map (TotalChowClass.res h hs).toMonoidHom
      (complexChernFactor C sY P ρ hP n) =
        complexChernFactor C sY' _ ρ (isFiniteLocallyFreeOfRank_pullbackComplex_X P h ρ hP) n := by
    intro n
    let := hP n
    rw [complexChernFactor, complexChernFactor, map_zpow]
    congr 1
    exact Units.ext (TotalChowClass.res_totalChern C sY (P.X n) (ρ n) h hs)
  rw [complexChernBounded, complexChernBounded, complexChernProd, complexChernProd]
  show (TotalChowClass.res h hs).toMonoidHom _ = _
  rw [← Units.coe_map, map_list_prod, List.map_map]
  congr 2
  exact List.map_congr_left fun n _ ↦ hfac n

end Bounded

end Stacks.Chow

end
