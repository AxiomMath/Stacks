module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveExtension

/-!
# Filtered acyclic complexes against filtered injective complexes

## Filtered components, and filtered objects in a fixed degree

The machinery [Stacks, Tags 05TV, 05TX and 05TY] have in common. A filtered cochain complex `K^•`
has, in each degree `n`, an underlying filtered object `(K^n, F^• K^n)` of `𝒜` (`evalFil`), because
evaluation in degree `n` preserves monomorphisms; the degreewise finiteness that defines
`K(Fil^f(𝒜))` is exactly finiteness of each of those filtrations (`isFinite_eval`). And a single
morphism `f : K^i ⟶ I^j` between terms of two filtered complexes is *filtered*
(`IsFilteredComponent`) when each composite `F^p K^i → K^i → I^j` factors through `F^p I^j`; being
a filtered morphism of complexes, or a filtered homotopy, is that property of every component, and
the closure properties collected here are what the constructions below need in order to stay
inside `Fil^f(𝒜)`.

## Maps from a filtered acyclic complex into a bounded below filtered injective complex

Let `𝒜` be an abelian category, let `K^•` be a filtered acyclic filtered cochain complex of `𝒜`
whose terms have finite filtrations, and let `I^•` be a filtered complex which is bounded below
and whose terms are filtered injective with finite filtrations. Every morphism `α : K^• ⟶ I^•` of
filtered complexes is then homotopic to zero by a *filtered* homotopy, which is the source's
`Hom_{K(Fil^f(𝒜))}(K^•, I^•) = 0`.

The proof is the source's induction. The one step of it is `HasSteps`: given a filtered
`β : K^n ⟶ I^n` killed by `d_K^{n - 1}`, there is a filtered `h : K^{n + 1} ⟶ I^n` with
`d_K^n ≫ h = β`. Filtered acyclicity makes `d_K^n` strict and
`0 → Im(d_K^{n - 1}) → K^n → Im(d_K^n) → 0` exact in `Fil^f(𝒜)`, so `β` descends to `Im(d_K^n)`,
and it extends along the strict monomorphism `Im(d_K^n) → K^{n + 1}` because `I^n` is filtered
injective (`CategoryTheory.FilteredObject.factors_of_isFilteredInjective`). That strict
exactness ([Stacks, Tag 05QH]) is used through the property `RefinesInto`, membership in
`F^p K^n + d_K^{n - 1}(K^{n - 1})` up to refinements, which is what exactness of an abelian
category provides and which is proved by descending induction on the filtration. Granting the
step, the homotopy is assembled by recursion on the degree: `IsPartialHomotopy α n₀ k H` says that
the total family `H` is filtered, is supported in the degrees a homotopy is supported in, vanishes
in the degrees not yet constructed, and satisfies the homotopy identity below `n₀ + k`;
boundedness below of `I^•` starts the recursion, since `α^i = 0` for `i < n₀`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredComplexDegreewise

namespace CochainComplex.FilteredInjective.Degreewise

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

/-- The inclusion of a step of the filtration of a filtered cochain complex is a morphism of
complexes: `F^p K^• ⟶ K^•` commutes with the differentials. This is
`HomologicalComplex.Hom.comm` for `K.filtration.ι.app p`, with the target spelled `K^•` rather
than as a value of the constant functor. -/
private lemma d_comp_ι_f (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤᵒᵖ) (i j : ℤ) :
    (K.filtration.obj p).d i j ≫ ((K.filtration.ι.app p).f j :
        (K.filtration.obj p).X j ⟶ K.X.X j)
      = (K.filtration.ι.app p).f i ≫ K.X.d i j := by
  have h := (K.filtration.ι.app p).comm i j
  dsimp only [Functor.const_obj_obj] at h
  exact h.symm


attribute [local simp] evalFil_ι_app

/-- Membership of `Fil^f(𝒜)`, degree by degree. -/
public lemma isFinite_eval {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (hK : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n)) (n : ℤ) : (evalFil K n).filtration.IsFinite := by
  obtain ⟨p, q, h1, h2⟩ := hK n
  exact .of_exists ⟨p, h1⟩ ⟨q, h2⟩

/-- A morphism `f : K^i ⟶ I^j` between terms of two filtered cochain complexes is *filtered* if
each composite `F^p K^i → K^i → I^j` factors through `F^p I^j`. The factorisation is unique, since
`F^p I^j ⟶ I^j` is a monomorphism, so this is a property of `f` and not extra data. -/
def IsFilteredComponent (K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (i j : ℤ)
    (f : K.X.X i ⟶ I.X.X j) : Prop :=
  ∀ p : ℤ, ∃ hp : (K.filtration.obj (op p)).X i ⟶ (I.filtration.obj (op p)).X j,
    hp ≫ (I.filtration.ι.app (op p)).f j = (K.filtration.ι.app (op p)).f i ≫ f

namespace IsFilteredComponent

/-- Precomposing a filtered component with a morphism of filtered complexes gives a filtered
component. -/
lemma comp_left {M K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (u : M ⟶ K) {i j : ℤ}
    {f : K.X.X i ⟶ I.X.X j} (hf : IsFilteredComponent K I i j f) :
    IsFilteredComponent M I i j (u.hom.f i ≫ f) := by
  intro p
  obtain ⟨hp, hhp⟩ := hf p
  refine ⟨(u.natTrans.app (op p)).f i ≫ hp, ?_⟩
  rw [Category.assoc, hhp, ← Category.assoc, ← HomologicalComplex.comp_f, u.comm (op p),
    HomologicalComplex.comp_f, Category.assoc]

/-- The negative of a filtered component is filtered. -/
lemma neg {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {i j : ℤ}
    {f : K.X.X i ⟶ I.X.X j} (hf : IsFilteredComponent K I i j f) :
    IsFilteredComponent K I i j (-f) := fun p => by
  obtain ⟨hp, hhp⟩ := hf p
  exact ⟨-hp, by rw [Preadditive.neg_comp, hhp, Preadditive.comp_neg]⟩

/-- The zero morphism is a filtered component. -/
lemma zero (K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (i j : ℤ) :
    IsFilteredComponent K I i j (0 : K.X.X i ⟶ I.X.X j) := fun _ => ⟨0, by simp⟩

/-- Being a filtered component only depends on the morphism. -/
lemma of_eq {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {i j : ℤ}
    {f f' : K.X.X i ⟶ I.X.X j} (hff' : f = f') (hf : IsFilteredComponent K I i j f) :
    IsFilteredComponent K I i j f' := by
  subst hff'
  exact hf

/-- Precomposing a filtered component with a single term of a morphism of filtered complexes,
given as a compatible family of maps between the steps, gives a filtered component. This is the
version of `comp_left` for a map which shifts the degree, such as a term of the inclusion
`K^{i + 1} ⟶ C(α)^i` of a mapping cone. -/
lemma comp_left_component {M N I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    {i i' j : ℤ} (v : M.X.X i ⟶ N.X.X i')
    (vp : ∀ p : ℤ, (M.filtration.obj (op p)).X i ⟶ (N.filtration.obj (op p)).X i')
    (hv : ∀ p : ℤ, vp p ≫ (N.filtration.ι.app (op p)).f i'
      = (M.filtration.ι.app (op p)).f i ≫ v)
    {f : N.X.X i' ⟶ I.X.X j} (hf : IsFilteredComponent N I i' j f) :
    IsFilteredComponent M I i j (v ≫ f) := fun p => by
  obtain ⟨hp, hhp⟩ := hf p
  exact ⟨vp p ≫ hp, by rw [Category.assoc, hhp, ← Category.assoc, hv p, Category.assoc]⟩

/-- Being a filtered component is transported along an equality of target degrees. -/
lemma congr_tgt {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {i j j' : ℤ}
    (hjj' : j = j') {f : K.X.X i ⟶ I.X.X j} (hf : IsFilteredComponent K I i j f) :
    IsFilteredComponent K I i j' (f ≫ (I.X.XIsoOfEq hjj').hom) := by
  subst hjj'
  simpa using hf

/-- A sum of filtered components is filtered. -/
lemma add {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {i j : ℤ}
    {f g : K.X.X i ⟶ I.X.X j} (hf : IsFilteredComponent K I i j f)
    (hg : IsFilteredComponent K I i j g) : IsFilteredComponent K I i j (f + g) := fun p => by
  obtain ⟨hp, hhp⟩ := hf p
  obtain ⟨hq, hhq⟩ := hg p
  exact ⟨hp + hq, by rw [Preadditive.add_comp, hhp, hhq, Preadditive.comp_add]⟩

section

variable {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}

private lemma sub {i j : ℤ} {f g : K.X.X i ⟶ I.X.X j} (hf : IsFilteredComponent K I i j f)
    (hg : IsFilteredComponent K I i j g) : IsFilteredComponent K I i j (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Precomposing a filtered component with a differential of `K^•` gives a filtered component. -/
private lemma d_comp {i i' j : ℤ} {f : K.X.X i' ⟶ I.X.X j} (hf : IsFilteredComponent K I i' j f) :
    IsFilteredComponent K I i j (K.X.d i i' ≫ f) :=
  comp_left_component (K.X.d i i') (fun p => (K.filtration.obj (op p)).d i i')
    (fun p => d_comp_ι_f K (op p) i i') hf

/-- Postcomposing a filtered component with a differential of `I^•` gives a filtered component. -/
private lemma comp_d {i j j' : ℤ} {f : K.X.X i ⟶ I.X.X j} (hf : IsFilteredComponent K I i j f) :
    IsFilteredComponent K I i j' (f ≫ I.X.d j j') := by
  intro p
  obtain ⟨u, hu⟩ := hf p
  refine ⟨u ≫ (I.filtration.obj (op p)).d j j', ?_⟩
  dsimp only [Functor.const_obj_obj]
  rw [Category.assoc, d_comp_ι_f, ← Category.assoc, hu, Category.assoc]

/-- Every component of a morphism of filtered complexes is filtered. -/
private lemma hom_f (α : K ⟶ I) (i : ℤ) : IsFilteredComponent K I i i (α.hom.f i) := by
  intro p
  exact ⟨(α.natTrans.app (op p)).f i, HomologicalComplex.congr_hom (α.comm (op p)) i⟩

end

end IsFilteredComponent

end CochainComplex.FilteredInjective.Degreewise

end FilteredComplexDegreewise

section FilteredAcyclicHomotopy

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

namespace CochainComplex.FilteredInjective.Acyclic

open CochainComplex.FilteredInjective.Degreewise

/-- The family of morphisms supported in the single spot `(n + 1, n)`, where it is `h`. This is the
homotopy correction added at one step of the induction. -/
private noncomputable def single (K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ)
    (h : K.X.X (n + 1) ⟶ I.X.X n) : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j :=
  fun i j => if hij : i = n + 1 ∧ j = n then
      (K.X.XIsoOfEq hij.1).hom ≫ h ≫ (I.X.XIsoOfEq hij.2.symm).hom else 0

variable {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}

private lemma single_self (n : ℤ) (h : K.X.X (n + 1) ⟶ I.X.X n) :
    single K I n h (n + 1) n = h := by
  simp [single]

private lemma single_of_ne (n : ℤ) (h : K.X.X (n + 1) ⟶ I.X.X n) {i j : ℤ}
    (hij : ¬ (i = n + 1 ∧ j = n)) : single K I n h i j = 0 := dite_eq_right hij

/-- Adding the correction changes nothing away from the spot `(n + 1, n)`. -/
private lemma add_single_apply_of_ne (n : ℤ) (h : K.X.X (n + 1) ⟶ I.X.X n)
    (H : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j) {i j : ℤ} (hij : ¬ (i = n + 1 ∧ j = n)) :
    (H + single K I n h) i j = H i j := by
  simp [single_of_ne n h hij]

private lemma add_single_apply_of_ne_snd (n : ℤ) (h : K.X.X (n + 1) ⟶ I.X.X n)
    (H : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j) {i j : ℤ} (hj : j ≠ n) :
    (H + single K I n h) i j = H i j :=
  add_single_apply_of_ne n h H fun hij => hj hij.2

/-- At the spot `(n + 1, n)` the correction adds `h`. -/
private lemma add_single_apply_self (n : ℤ) (h : K.X.X (n + 1) ⟶ I.X.X n)
    (H : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j) :
    (H + single K I n h) (n + 1) n = H (n + 1) n + h := by
  simp [single_self]

private lemma single_isFilteredComponent (n : ℤ) (h : K.X.X (n + 1) ⟶ I.X.X n)
    (hh : IsFilteredComponent K I (n + 1) n h) (i j : ℤ) :
    IsFilteredComponent K I i j (single K I n h i j) := by
  by_cases hij : i = n + 1 ∧ j = n
  · obtain ⟨rfl, rfl⟩ := hij
    rw [single_self]
    exact hh
  · rw [single_of_ne n h hij]
    exact IsFilteredComponent.zero K I i j

/-- The inductive step of the source's argument: a filtered `β : K^n ⟶ I^n` killed by
`d_K^{n - 1}` is `d_K^n` followed by a filtered `h : K^{n + 1} ⟶ I^n`. -/
private def HasSteps (K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) : Prop :=
  ∀ (n : ℤ) (β : K.X.X n ⟶ I.X.X n), IsFilteredComponent K I n n β →
    K.X.d (n - 1) n ≫ β = 0 →
      ∃ h : K.X.X (n + 1) ⟶ I.X.X n,
        IsFilteredComponent K I (n + 1) n h ∧ K.X.d n (n + 1) ≫ h = β

/-- `H` is a homotopy from `α` to zero in the degrees below `n₀ + k`: it is filtered, supported
where a homotopy is supported, zero in the degrees `n₀ + k` and above, and satisfies the homotopy
identity in the degrees below `n₀ + k`. -/
private structure IsPartialHomotopy (α : K ⟶ I) (n₀ : ℤ) (k : ℕ)
    (H : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j) : Prop where
  filtered : ∀ i j : ℤ, IsFilteredComponent K I i j (H i j)
  offDiag : ∀ i j : ℤ, j + 1 ≠ i → H i j = 0
  vanishing : ∀ i j : ℤ, n₀ + k ≤ j → H i j = 0
  comm : ∀ i : ℤ, i < n₀ + k →
    α.hom.f i = K.X.d i (i + 1) ≫ H (i + 1) i + H i (i - 1) ≫ I.X.d (i - 1) i

private lemma isPartialHomotopy_zero (α : K ⟶ I) (n₀ : ℤ) [I.X.IsStrictlyGE n₀] :
    IsPartialHomotopy α n₀ 0 0 where
  filtered i j := IsFilteredComponent.zero K I i j
  offDiag _ _ _ := rfl
  vanishing _ _ _ := rfl
  comm i hi := by
    have h := I.X.isZero_of_isStrictlyGE n₀ i (by simpa using hi)
    simp [h.eq_of_tgt (α.hom.f i) 0]

/-- **The obstruction is a cocycle.** In a degree `n` in which a partial homotopy already satisfies
the homotopy identity one step below, the *obstruction* `β = α^n - H^{n, n - 1} ≫ d_I^{n - 1}`, the
part of `α^n` not yet accounted for by `H`, is killed by `d_K^{n - 1}`. This is the only use of the
homotopy identity in degree `n - 1`, and it is what makes `HasSteps` applicable to the
obstruction. -/
private lemma IsPartialHomotopy.d_comp_obstruction {α : K ⟶ I} {n₀ : ℤ} {k : ℕ}
    {H : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j} (hH : IsPartialHomotopy α n₀ k H) (n : ℤ)
    (hn : n - 1 < n₀ + k) :
    K.X.d (n - 1) n ≫ (α.hom.f n - H n (n - 1) ≫ I.X.d (n - 1) n) = 0 := by
  have hc := hH.comm (n - 1) hn
  rw [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] at hc
  have key : K.X.d (n - 1) n ≫ H n (n - 1) = α.hom.f (n - 1) - H (n - 1) (n - 2) ≫
      I.X.d (n - 2) (n - 1) := by rw [hc]; abel
  rw [Preadditive.comp_sub, ← Category.assoc, key, ← α.hom.comm (n - 1) n,
    Preadditive.sub_comp, Category.assoc, HomologicalComplex.d_comp_d]
  simp

/-- One step of the recursion: a partial homotopy up to `n₀ + k` extends to one up to
`n₀ + k + 1`, without changing the components already constructed. The new component is the one
the inductive step provides for the obstruction in degree `n₀ + k`; the rest is bookkeeping. -/
private lemma exists_next (α : K ⟶ I) (n₀ : ℤ) (k : ℕ) (hstep : HasSteps K I)
    (H : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j) (hH : IsPartialHomotopy α n₀ k H) :
    ∃ H' : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j, IsPartialHomotopy α n₀ (k + 1) H' ∧
      ∀ i j : ℤ, j ≠ n₀ + k → H' i j = H i j := by
  set n : ℤ := n₀ + k with hn
  obtain ⟨h, hhfil, hhd⟩ := hstep n _ ((IsFilteredComponent.hom_f α n).sub
    ((hH.filtered n (n - 1)).comp_d)) (hH.d_comp_obstruction n (by omega))
  refine ⟨H + single K I n h, ⟨fun i j => (hH.filtered i j).add
      (single_isFilteredComponent n h hhfil i j), fun i j hij => ?_, fun i j hij => ?_,
    fun i hi => ?_⟩, fun i j hj => add_single_apply_of_ne_snd n h H hj⟩
  · rw [add_single_apply_of_ne n h H fun hh => hij (by rw [hh.1, hh.2]), hH.offDiag i j hij]
  · push_cast at hij
    rw [add_single_apply_of_ne_snd n h H (by omega), hH.vanishing i j (by omega)]
  · push_cast at hi
    rcases eq_or_lt_of_le (show i ≤ n by omega) with rfl | hlt
    · rw [add_single_apply_self, add_single_apply_of_ne_snd n h H (by omega),
        hH.vanishing (n + 1) n (by omega), zero_add, hhd]
      abel
    · rw [add_single_apply_of_ne_snd n h H (by omega), add_single_apply_of_ne_snd n h H (by omega)]
      exact hH.comm i (by omega)

/-- The sequence of partial homotopies produced by the recursion. -/
private noncomputable def hseq (α : K ⟶ I) (n₀ : ℤ) [I.X.IsStrictlyGE n₀] (hstep : HasSteps K I) :
    (k : ℕ) → {H : ∀ i j : ℤ, K.X.X i ⟶ I.X.X j // IsPartialHomotopy α n₀ k H}
  | 0 => ⟨0, isPartialHomotopy_zero α n₀⟩
  | (k + 1) =>
      ⟨(exists_next α n₀ k hstep _ (hseq α n₀ hstep k).2).choose,
        (exists_next α n₀ k hstep _ (hseq α n₀ hstep k).2).choose_spec.1⟩

private lemma hseq_succ (α : K ⟶ I) (n₀ : ℤ) [I.X.IsStrictlyGE n₀] (hstep : HasSteps K I) (k : ℕ)
    (i j : ℤ) (hj : j ≠ n₀ + k) :
    (hseq α n₀ hstep (k + 1)).1 i j = (hseq α n₀ hstep k).1 i j :=
  (exists_next α n₀ k hstep _ (hseq α n₀ hstep k).2).choose_spec.2 i j hj

private lemma hseq_stable (α : K ⟶ I) (n₀ : ℤ) [I.X.IsStrictlyGE n₀] (hstep : HasSteps K I) :
    ∀ (l k : ℕ), k ≤ l → ∀ i j : ℤ, j < n₀ + k →
      (hseq α n₀ hstep l).1 i j = (hseq α n₀ hstep k).1 i j := by
  intro l
  induction l with
  | zero => intro k hk i j _; rw [Nat.le_zero.mp hk]
  | succ l ih =>
      intro k hk i j hj
      rcases Nat.lt_or_ge k (l + 1) with h | h
      · have hkl : k ≤ l := by omega
        rw [hseq_succ α n₀ hstep l i j (by omega), ih k hkl i j hj]
      · rw [Nat.le_antisymm hk h]

/-- The source's induction: granting the inductive step, `α` is homotopic to zero by a filtered
homotopy. -/
private lemma exists_homotopy (α : K ⟶ I) (n₀ : ℤ) [I.X.IsStrictlyGE n₀] (hstep : HasSteps K I) :
    ∃ h : Homotopy α.hom 0, ∀ i j p : ℤ,
      ∃ hp : (K.filtration.obj (op p)).X i ⟶ (I.filtration.obj (op p)).X j,
        hp ≫ (I.filtration.ι.app (op p)).f j
          = (K.filtration.ι.app (op p)).f i ≫ h.hom i j := by
  refine ⟨⟨fun i j => (hseq α n₀ hstep ((j - n₀).toNat + 1)).1 i j, ?_, ?_⟩, ?_⟩
  · intro i j hij
    exact (hseq α n₀ hstep ((j - n₀).toNat + 1)).2.offDiag i j hij
  · intro i
    have hb := (hseq α n₀ hstep ((i - n₀).toNat + 1)).2.comm i (by omega)
    have h2 : (hseq α n₀ hstep ((i - n₀).toNat + 1)).1 i (i - 1)
        = (hseq α n₀ hstep ((i - 1 - n₀).toNat + 1)).1 i (i - 1) :=
      hseq_stable α n₀ hstep _ _ (by omega) i (i - 1) (by omega)
    rw [h2] at hb
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    simpa using hb
  · intro i j p
    exact (hseq α n₀ hstep ((j - n₀).toNat + 1)).2.filtered i j p


/-- The degreewise form of `Filtration.diagram_map_comp_ι_app` for a filtered cochain complex:
`F^q K^n ⟶ F^p K^n ⟶ K^n` is `F^q K^n ⟶ K^n`. -/
private lemma diagram_map_f_comp_ι_f (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) {i j : ℤᵒᵖ}
    (f : i ⟶ j) (n : ℤ) :
    (K.filtration.diagram.map f).f n ≫ ((K.filtration.ι.app j).f n :
        (K.filtration.obj j).X n ⟶ K.X.X n) = (K.filtration.ι.app i).f n :=
  HomologicalComplex.congr_hom (Filtration.diagram_map_comp_ι_app K.filtration f) n

/-- Filtered injectivity of `I^n`, in the form Lemma 05TR consumes: the graded pieces of the
filtered object `(I^n, F^• I^n)` are the terms in degree `n` of the graded pieces of `I^•`, because
cokernels of complexes are computed termwise. -/
private lemma injective_gradedPiece_eval {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (hI : ∀ p n : ℤ,
      Injective (((FilteredObject.gr p).obj I).X n)) (n p : ℤ) :
    Injective ((FilteredObject.gr p).obj (evalFil I n)) :=
  Injective.of_iso (PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
    (I.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)) (hI p n)

/-! ### Cokernels of morphisms of complexes, degree by degree -/

/-- Evaluation in degree `n` preserves cokernels, so the cokernel projection of a morphism of
cochain complexes is an epimorphism in each degree. -/
private lemma epi_cokernel_π_f {X Y : CochainComplex 𝒜 ℤ} (φ : X ⟶ Y) (n : ℤ) :
    Epi ((cokernel.π φ).f n) :=
  inferInstance

private lemma comp_cokernel_π_f {X Y : CochainComplex 𝒜 ℤ} (φ : X ⟶ Y) (n : ℤ) :
    φ.f n ≫ (cokernel.π φ).f n = 0 := by
  rw [← HomologicalComplex.comp_f, cokernel.condition]
  simp

/-- In each degree, the cokernel projection of a morphism of cochain complexes is a cokernel. -/
private lemma exact_cokernel_π_f {X Y : CochainComplex 𝒜 ℤ} (φ : X ⟶ Y) (n : ℤ) :
    (ShortComplex.mk (φ.f n) ((cokernel.π φ).f n) (comp_cokernel_π_f φ n)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) φ)

/-- A monomorphism is the kernel of its own cokernel. -/
private lemma exact_cokernel_π {X Y : 𝒜} (m : X ⟶ Y) :
    (ShortComplex.mk m (cokernel.π m) (cokernel.condition m)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel m)

/-! ### Strictness and exactness of a filtered acyclic complex -/

/-- `x : W ⟶ K^n` *refines into* a subcomplex `ι : F^• ⟶ K^•` if, up to an epimorphism `W' ↠ W`,
it is the sum of a map through `F^n` and a coboundary of `K^•`. This is membership of `x` in
`F^n + d_K^{n - 1}(K^{n - 1})`, in the "up to refinements" form in which the exactness of an
abelian category is available (`HomologicalComplex.exactAt_iff_exact_up_to_refinements`), and it is
the invariant of the induction on the filtration below. -/
private def RefinesInto {K F : CochainComplex 𝒜 ℤ} (ι : F ⟶ K) (n : ℤ) {W : 𝒜}
    (x : W ⟶ K.X n) : Prop :=
  ∃ (W' : 𝒜) (e : W' ⟶ W) (_ : Epi e) (a : W' ⟶ F.X n) (b : W' ⟶ K.X (n - 1)),
    e ≫ x = a ≫ ι.f n + b ≫ K.d (n - 1) n

/-- Every map refines into a subcomplex which is everything in the degree in question. -/
private lemma refinesInto_of_isIso {K F : CochainComplex 𝒜 ℤ} (ι : F ⟶ K) (n : ℤ)
    [IsIso (ι.f n)] {W : 𝒜} (x : W ⟶ K.X n) : RefinesInto ι n x :=
  ⟨W, 𝟙 W, inferInstance, x ≫ inv (ι.f n), 0, by simp⟩

/-- **One step of the strict exactness of a filtered acyclic complex.** Let `ιF : F^• ⟶ K^•` and
`ιG : G^• ⟶ K^•` be subcomplexes of a cochain complex `K^•` with `G^• ⊆ F^•`, say `φ ≫ ιF = ιG`,
and assume `F^•/G^•` is exact in degree `n`. Then a map `x : W ⟶ K^n` whose composite with `d_K^n`
factors through `G^{n + 1}` and which refines into `F^•` already refines into `G^•`. -/
private lemma refinesInto_of_exactAt {K F G : CochainComplex 𝒜 ℤ} (ιF : F ⟶ K) (ιG : G ⟶ K)
    (φ : G ⟶ F) (hφ : φ ≫ ιF = ιG) (hιF : ∀ m : ℤ, Mono (ιF.f m)) (hιG : ∀ m : ℤ, Mono (ιG.f m))
    (n : ℤ) (hex : (cokernel φ).ExactAt n) {W : 𝒜} (x : W ⟶ K.X n) (yG : W ⟶ G.X (n + 1))
    (hxy : x ≫ K.d n (n + 1) = yG ≫ ιG.f (n + 1)) (hx : RefinesInto ιF n x) :
    RefinesInto ιG n x := by
  obtain ⟨W₁, e₁, he₁, a₀, b₀, h₁⟩ := hx
  have hfac : ∀ m : ℤ, φ.f m ≫ ιF.f m = ιG.f m := fun m =>
    HomologicalComplex.congr_hom hφ m
  have := hιF n
  have := hιF (n + 1)
  have := he₁
  have ha₀ : a₀ ≫ ιF.f n = e₁ ≫ x - b₀ ≫ K.d (n - 1) n := by rw [h₁]; abel
  -- `a₀` is a cocycle of `F^•` modulo `G^•`
  have hcocycle : a₀ ≫ F.d n (n + 1) = e₁ ≫ yG ≫ φ.f (n + 1) := by
    rw [← cancel_mono (ιF.f (n + 1)), Category.assoc, ← ιF.comm n (n + 1), ← Category.assoc, ha₀]
    simp [Preadditive.sub_comp, hxy, hfac (n + 1)]
  have hπ : (a₀ ≫ (cokernel.π φ).f n) ≫ (cokernel φ).d n (n + 1) = 0 := by
    rw [Category.assoc, (cokernel.π φ).comm n (n + 1), ← Category.assoc, hcocycle]
    simp [comp_cokernel_π_f]
  -- exactness of `F^•/G^•` in degree `n` refines `a₀` to a coboundary
  obtain ⟨W₂, e₂, he₂, c, h₂⟩ := (HomologicalComplex.exactAt_iff_exact_up_to_refinements
    (cokernel φ) (n - 1) n (n + 1) (by simp) (by simp)).1 hex (a₀ ≫ (cokernel.π φ).f n) hπ
  have := epi_cokernel_π_f φ (n - 1)
  obtain ⟨W₃, e₃, he₃, a₁, h₃⟩ :=
    surjective_up_to_refinements_of_epi ((cokernel.π φ).f (n - 1)) c
  have := he₂
  have := he₃
  have hdiff : (e₃ ≫ e₂ ≫ a₀ - a₁ ≫ F.d (n - 1) n) ≫ (cokernel.π φ).f n = 0 := by
    have h4 : e₃ ≫ e₂ ≫ a₀ ≫ (cokernel.π φ).f n
        = a₁ ≫ F.d (n - 1) n ≫ (cokernel.π φ).f n := by
      rw [h₂, ← Category.assoc, h₃, Category.assoc, (cokernel.π φ).comm (n - 1) n]
    simp [Preadditive.sub_comp, h4]
  have := hιG n
  have : Mono (φ.f n) := mono_of_mono_fac (hfac n)
  -- the descent of `a₀` to `G^n`, made opaque so that it carries no proof of `hdiff`
  obtain ⟨L, hL⟩ : ∃ L : W₃ ⟶ G.X n, L ≫ φ.f n = e₃ ≫ e₂ ≫ a₀ - a₁ ≫ F.d (n - 1) n :=
    ⟨_, (exact_cokernel_π_f φ n).lift_f _ hdiff⟩
  have hsum : e₃ ≫ e₂ ≫ a₀ = L ≫ φ.f n + a₁ ≫ F.d (n - 1) n := by rw [hL]; abel
  refine ⟨W₃, e₃ ≫ e₂ ≫ e₁, inferInstance, L, e₃ ≫ e₂ ≫ b₀ + a₁ ≫ ιF.f (n - 1), ?_⟩
  calc (e₃ ≫ e₂ ≫ e₁) ≫ x = (e₃ ≫ e₂) ≫ e₁ ≫ x := by simp
    _ = (e₃ ≫ e₂) ≫ (a₀ ≫ ιF.f n + b₀ ≫ K.d (n - 1) n) := by rw [h₁]
    _ = (e₃ ≫ e₂ ≫ a₀) ≫ ιF.f n + (e₃ ≫ e₂ ≫ b₀) ≫ K.d (n - 1) n := by
        simp [Preadditive.comp_add]
    _ = (L ≫ φ.f n + a₁ ≫ F.d (n - 1) n) ≫ ιF.f n
          + (e₃ ≫ e₂ ≫ b₀) ≫ K.d (n - 1) n := by rw [hsum]
    _ = _ := by
        simp only [Preadditive.add_comp, Category.assoc, hfac n, ← ιF.comm (n - 1) n]
        abel

/-- **The strict exactness of a filtered acyclic complex** (Homology, Lemma 05QH), in the form
"up to refinements". Let `K^•` be a filtered cochain complex whose graded pieces are acyclic and
whose filtration exhausts `K^n`. If `x : W ⟶ K^n` has `d_K^n ∘ x` factoring through `F^p K^{n + 1}`
then `x` refines into `F^p K^•`; the case of `p` with `F^p K^{n + 1} = 0` is the exactness of `K^•`
in degree `n`, and the general case is the strictness of `d_K^n`. The induction is on the number of
steps of the filtration between `p` and an index at which the filtration exhausts `K^n`, the step
being `refinesInto_of_exactAt`. -/
private lemma refinesInto_filtration {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (hK : CochainComplex.filteredAcyclic 𝒜 K) (n : ℤ)
    (hexh : ∃ r : ℤ, IsIso ((K.filtration.ι.app (op r)).f n)) (p : ℤ) {W : 𝒜}
    (x : W ⟶ K.X.X n) (y : W ⟶ (K.filtration.obj (op p)).X (n + 1))
    (hxy : x ≫ K.X.d n (n + 1) = y ≫ (K.filtration.ι.app (op p)).f (n + 1)) :
    RefinesInto (K.filtration.ι.app (op p)) n x := by
  obtain ⟨r, hr⟩ := hexh
  suffices H : ∀ (k : ℕ) (q : ℤ), q ≤ r + k → ∀ {W : 𝒜} (x : W ⟶ K.X.X n)
      (y : W ⟶ (K.filtration.obj (op q)).X (n + 1)),
      x ≫ K.X.d n (n + 1) = y ≫ (K.filtration.ι.app (op q)).f (n + 1) →
      RefinesInto (K.filtration.ι.app (op q)) n x from H (p - r).toNat p (by omega) x y hxy
  intro k
  induction k with
  | zero =>
      intro q hq W x y _
      have : IsIso ((K.filtration.ι.app (op q)).f n) :=
        Filtration.isIso_ι_app_of_le (evalFil K n).filtration (by simpa using hq) hr
      exact refinesInto_of_isIso _ n x
  | succ k ih =>
      intro q hq W x y hxy
      rcases le_or_gt q (r + k) with h | h
      · exact ih q h x y hxy
      · obtain rfl : q = r + k + 1 := by push_cast at hq ⊢; omega
        exact refinesInto_of_exactAt (K.filtration.ι.app (op (r + k)))
          (K.filtration.ι.app (op (r + k + 1))) _
          (Filtration.diagram_map_comp_ι_app K.filtration _) (mono_ι_app_f K (op (r + k)))
          (mono_ι_app_f K (op (r + k + 1))) n (hK (r + k) n) x y hxy
          (ih (r + k) le_rfl x (y ≫ (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : ((r + k : ℤ)) ⟶ r + k + 1).op).f (n + 1))
            (by rw [hxy, Category.assoc, diagram_map_f_comp_ι_f]))

/-! ### The preimage filtration -/

/-- The filtered object `(K^n, (d_K^n)^{-1} F^• K^{n + 1})` of `𝒜`, i.e. `K^n` filtered by the
preimages under `d_K^n` of the steps of the filtration of `K^{n + 1}`. The differential `d_K^n` is
a *strict* morphism out of it by construction (`isStrictHom_preimageD`). -/
private noncomputable def preimage (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) :
    FilteredObject 𝒜 ℤᵒᵖ where
  X := K.X.X n
  filtration := ⟨(evalFil K (n + 1)).filtration.toMonoOver ⋙
    MonoOver.pullback (K.X.d n (n + 1))⟩

/-- The differential `d_K^n`, as a morphism from the preimage filtration of `K^n` to
`K^{n + 1}`. -/
private noncomputable def preimageD (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) :
    preimage K n ⟶ evalFil K (n + 1) :=
  FilteredObject.homMk (K.X.d n (n + 1))
    (fun i => pullback.fst ((K.filtration.ι.app i).f (n + 1)) (K.X.d n (n + 1)))
    (fun _ => pullback.condition)

/-- The differential is strict for the preimage filtration: its filtration squares are pullbacks
by construction. -/
private lemma isStrictHom_preimageD (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) :
    FilteredObject.IsStrictHom (preimageD K n) :=
  ⟨fun i => IsPullback.of_hasPullback ((K.filtration.ι.app i).f (n + 1)) (K.X.d n (n + 1))⟩

/-- A filtered `β : K^n ⟶ I^n` killed by `d_K^{n - 1}` is filtered for the preimage filtration of
`K^n`: it carries `(d_K^n)^{-1} F^p K^{n + 1}` into `F^p I^n`. This is where filtered acyclicity of
`K^•` enters. -/
private lemma exists_filtered_descent {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (hK : CochainComplex.filteredAcyclic 𝒜 K) (n : ℤ)
    (hexh : ∃ r : ℤ, IsIso ((K.filtration.ι.app (op r)).f n))
    {β : K.X.X n ⟶ I.X.X n} (hβ : IsFilteredComponent K I n n β)
    (hβd : K.X.d (n - 1) n ≫ β = 0) (p : ℤ) {W : 𝒜}
    (x : W ⟶ K.X.X n) (y : W ⟶ (K.filtration.obj (op p)).X (n + 1))
    (hxy : x ≫ K.X.d n (n + 1) = y ≫ (K.filtration.ι.app (op p)).f (n + 1)) :
    ∃ t : W ⟶ (I.filtration.obj (op p)).X n,
      t ≫ (I.filtration.ι.app (op p)).f n = x ≫ β := by
  obtain ⟨W', e, he, a, b, hab⟩ := refinesInto_filtration hK n hexh p x y hxy
  obtain ⟨u, hu⟩ := hβ p
  have := he
  have := mono_ι_app_f I (op p) n
  have h1 : (K.filtration.ι.app (op p)).f n ≫ β
      ≫ cokernel.π ((I.filtration.ι.app (op p)).f n) = 0 := by
    rw [← Category.assoc, ← hu, Category.assoc, cokernel.condition, comp_zero]
  have h2 : K.X.d (n - 1) n ≫ β ≫ cokernel.π ((I.filtration.ι.app (op p)).f n) = 0 := by
    rw [← Category.assoc, hβd, zero_comp]
  have hker : (x ≫ β) ≫ cokernel.π ((I.filtration.ι.app (op p)).f n) = 0 := by
    rw [← cancel_epi e, comp_zero]
    simp only [← Category.assoc]
    rw [hab]
    simp [Preadditive.add_comp, h1, h2]
  exact ⟨(exact_cokernel_π ((I.filtration.ι.app (op p)).f n)).lift (x ≫ β) hker,
    (exact_cokernel_π ((I.filtration.ι.app (op p)).f n)).lift_f (x ≫ β) hker⟩

/-- **The inductive step.** Let `K^•` be filtered acyclic with terms of finite filtration and let
`I^n` be filtered injective with finite filtration. A filtered `β : K^n ⟶ I^n` killed by
`d_K^{n - 1}` factors as `d_K^n` followed by a filtered `h : K^{n + 1} ⟶ I^n`. -/
private lemma hasSteps (K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hK : CochainComplex.filteredAcyclic 𝒜 K)
    (hKfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n))
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hI : ∀ p n : ℤ,
      Injective (((CategoryTheory.FilteredObject.gr p).obj I).X n)) :
    HasSteps K I := by
  intro n β hβ hβd
  obtain ⟨r, q, hr, -⟩ := hKfin n
  have hdesc : ∀ i : ℤᵒᵖ, ∃ t : (preimage K n).filtration.obj i ⟶ (evalFil I n).filtration.obj i,
      t ≫ (evalFil I n).filtration.ι.app i = (preimage K n).filtration.ι.app i ≫ β := fun i =>
    exists_filtered_descent hK n ⟨r, hr⟩ hβ hβd i.unop
      (pullback.snd ((K.filtration.ι.app i).f (n + 1)) (K.X.d n (n + 1)))
      (pullback.fst ((K.filtration.ι.app i).f (n + 1)) (K.X.d n (n + 1)))
      pullback.condition.symm
  have := isStrictHom_preimageD K n
  obtain ⟨g, hg⟩ := CategoryTheory.FilteredObject.factors_of_isFilteredInjective
    (FilteredObject.homMk β (fun i => (hdesc i).choose) (fun i => (hdesc i).choose_spec))
    (preimageD K n) ⟨isFinite_eval hIfin n, injective_gradedPiece_eval hI n⟩
  refine ⟨g.hom, fun p => ⟨g.natTrans.app (op p), g.comm (op p)⟩, ?_⟩
  exact congrArg FilteredObject.Hom.hom hg

end CochainComplex.FilteredInjective.Acyclic

namespace CochainComplex

open FilteredInjective.Acyclic in
/-- **Stacks 05TX.** Let `𝒜` be an abelian category and let `K^•`, `I^•` be filtered cochain
complexes of `𝒜` whose terms have finite filtrations, i.e. objects of `K(Fil^f(𝒜))`. Assume `K^•`
is filtered acyclic, that is every `gr^p K^• = F^p K^•/F^{p + 1} K^•` is acyclic, and that `I^•`
is bounded below, `I^n = 0` for `n < n₀`, and consists of filtered injective objects of
`Fil^f(𝒜)`: every term `(I^n, F^• I^n)` is filtered injective. Then every morphism
`α : K^• ⟶ I^•` of filtered complexes is homotopic to zero by a filtered homotopy: there is a
homotopy `h` from `α` to `0` on the underlying complexes each of whose components
`h^{i,j} : K^i ⟶ I^j` carries `F^p K^i` into `F^p I^j`. Equivalently
`Hom_{K(Fil^f(𝒜))}(K^•, I^•) = 0`. -/
@[stacks 05TX]
public theorem exists_homotopy_zero_of_filteredAcyclic_of_injective_gradedPiece
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ I) (n₀ : ℤ) [I.X.IsStrictlyGE n₀]
    (hK : filteredAcyclic 𝒜 K)
    (hKfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n))
    (hI : ∀ n : ℤ, (evalFil I n).IsFilteredInjective) :
    ∃ h : Homotopy α.hom 0, ∀ i j p : ℤ,
      ∃ hp : (K.filtration.obj (op p)).X i ⟶ (I.filtration.obj (op p)).X j,
        hp ≫ (I.filtration.ι.app (op p)).f j
          = (K.filtration.ι.app (op p)).f i ≫ h.hom i j :=
  exists_homotopy α n₀ (hasSteps K I hK hKfin
    (fun n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1)
    (fun p n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).2 p))

end CochainComplex

end FilteredAcyclicHomotopy

end
