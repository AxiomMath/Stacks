module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FiniteCoproductsOfRepresentables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The finite-covering criterion on a site that is not small

Stacks 0GN4 reduces the five hypotheses of Stacks 0GN3 — a set `S` of quasi-compact sheaves of
sets covering the final sheaf and stable in four senses — to four conditions on a collection
`B ⊆ Ob(C)` of objects of the site, taking for `S` the set of finite coproducts
`∐_{i = 1, …, n} h_{U_i}^#` of sheafified representables of objects of `B`.

The library's form of that reduction, `Stacks.Cohomology.ColimitsOfCohomology`
`.isIso_colimit_post_rightDerived_globalSections_of_finite_covers`, asks for
`{C : Type u} [SmallCategory C]`, that is for a site whose objects and morphisms share a
universe. The sites of algebraic geometry do not: the small étale site of an algebraic space and
the fppf, flat-fppf and lisse-étale sites of an algebraic stack all have objects in `Type (u + 1)`
and morphisms in `Type u`.

This file removes that restriction, as
`StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite` did
for Stacks 0GN3. For an arbitrary site `C : Type u₁` with morphisms in `Type v`, every object the
criterion mentions lives at the join `max u₁ v`: that is the universe of the sheaves of sets whose
sheafification `CategoryTheory.Sheaf.sheafifiedYoneda` lands in, of `CategoryTheory.Sheaf`
`.IsQuasiCompact`, and of the abelian coefficients, so all four conditions and the conclusion read
verbatim at that universe.

## Main results

In the namespace `Stacks.Cohomology.ColimitsOfCohomology`:

* `isIso_colimit_post_rightDerived_globalSections_of_covers`:
  **Stacks 0GN4 for an arbitrary site.** Conditions (1)–(4) on `B` give the conclusion of
  Stacks 0GN3, that `colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism.

## Implementation notes

Nothing in the argument of Stacks 0GN4 uses smallness of the site: the small-site hypothesis of
the library's form is inherited from the section variable of the file it lives in and from the
small-site convention of the library's Stacks 0GN3. The private lemmas of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FiniteCoproductsOfRepresentables`
that the argument consumes are therefore re-proved here at the join universe, with the same
proofs; they are private there, so they cannot be imported. The two definitions
`CategoryTheory.Sheaf.FiniteCoproductSheafifiedYoneda`-style set `S` and the refinement condition,
and the quasi-compactness assertion of Stacks 0GN4, are already general in that file and are
imported rather than restated:
`Stacks.Cohomology.ColimitsOfCohomology.FiniteCoproductSheafifiedYoneda`,
`Stacks.Cohomology.ColimitsOfCohomology.HasFiniteCoverRefinementsFrom` and
`Stacks.Cohomology.ColimitsOfCohomology.isQuasiCompact_of_finiteCoproductSheafifiedYoneda`.
The one lemma of the nine that already exists publicly at this generality is Stacks 00WT for
sheafified representables,
`Stacks.Sites.QuasiCompactCriterion.isLocallySurjective_sigmaDesc_sheafifiedYoneda_map_iff`, and
it is used in place of a restatement.

The four facts about abelian sheaves at the join universe that make the conclusion a well-formed
statement — essential smallness of the site, left exact sheafification, enough injectives, and
additivity of global sections — are `essentiallySmall_join`, `hasSheafify_ab_join`,
`enoughInjectives_sheaf_join` and `globalSections_additive_join` of the Stacks 0GN3 file, and are
installed here with `attribute [local instance]` exactly as a consumer of that file should.

The index category of the filtered diagram lives at the join universe, as in Stacks 0GN3 for an
arbitrary site.

## References

* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 00WT](https://stacks.math.columbia.edu/tag/00WT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.QuasiCompactCriterion

namespace Stacks.Cohomology.ColimitsOfCohomology

universe v u₁

attribute [local instance] essentiallySmall_join hasSheafify_ab_join enoughInjectives_sheaf_join
  globalSections_additive_join

attribute [local instance] sheafOfTypes_hasColimitsOfSize

/-! ### The four stability properties of finite coproducts of sheafified representables -/

/-- A covering family indexed by `Fin m` induces an epimorphism out of the coproduct of its
sheafified representables, indexed by `ULift (Fin m)`. -/
private theorem epi_sigmaDesc_sheafifiedYoneda_map_uLift {C : Type u₁} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C} {m : ℕ} {V : Fin m → C} (p : ∀ j, V j ⟶ U)
    (hp : Sieve.ofArrows V p ∈ J U) :
    Epi (Sigma.desc fun j : ULift.{max u₁ v} (Fin m) =>
      (Sheaf.sheafifiedYoneda J).map (p j.down)) := by
  have heq : Sieve.ofArrows (fun j : ULift.{max u₁ v} (Fin m) => V j.down) (fun j => p j.down) =
      Sieve.ofArrows V p := by
    ext W f
    rw [Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    exact ⟨fun ⟨j, a, h⟩ => ⟨j.down, a, h⟩, fun ⟨j, a, h⟩ => ⟨ULift.up j, a, h⟩⟩
  exact (Sheaf.isLocallySurjective_iff_epi _).1
    ((isLocallySurjective_sigmaDesc_sheafifiedYoneda_map_iff (J := J) (S := U)
      (X := fun j : ULift.{max u₁ v} (Fin m) => V j.down) (fun j => p j.down)).2
      (by rw [heq]; exact hp))

/-- Hypothesis (2) of Stacks 0GN3 for finite coproducts of sheafified representables of objects
of `B`: a local surjection onto such a coproduct is refined by one out of another. -/
private theorem exists_isLocallySurjective_comp_of_mem_finiteCoproductSheafifiedYoneda
    {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C) {B : Set C}
    (h_refine : ∀ U ∈ B, HasFiniteCoverRefinementsFrom J B U)
    {G K : Sheaf J (Type max u₁ v)} (f : G ⟶ K) (hK : K ∈ FiniteCoproductSheafifiedYoneda J B)
    (hsurj : Sheaf.IsLocallySurjective f) :
    ∃ K' ∈ FiniteCoproductSheafifiedYoneda J B, ∃ g : K' ⟶ G,
      Sheaf.IsLocallySurjective (g ≫ f) := by
  classical
  obtain ⟨n, U, hU, ⟨e⟩⟩ := hK
  let O := ULift.{max u₁ v} (Fin n)
  let R := ∐ fun i : O => (Sheaf.sheafifiedYoneda J).obj (U i.down)
  let e' : K ≅ R := e.trans (Sigma.reindex Equiv.ulift.symm
    (fun i : O => (Sheaf.sheafifiedYoneda J).obj (U i.down)))
  let f' : G ⟶ R := f ≫ e'.hom
  have : Epi f := (Sheaf.isLocallySurjective_iff_epi f).1 hsurj
  have hf' : Sheaf.IsLocallySurjective f' :=
    (Sheaf.isLocallySurjective_iff_epi _).2 (epi_comp f e'.hom)
  have hRef : ∀ i : Fin n, ∃ (m : ℕ) (V : Fin m → C) (p : ∀ j, V j ⟶ U i),
      (∀ j, V j ∈ B) ∧ Sieve.ofArrows V p ∈ J (U i) ∧
        Sieve.ofArrows V p ≤ Presheaf.imageSieve f'.hom
          ((Sigma.ι (fun k : O => (Sheaf.sheafifiedYoneda J).obj (U k.down))
            (ULift.up i)).hom.app (op (U i)) (Sheaf.tautologicalSection J (U i))) :=
    fun i => h_refine (U i) (hU i) _ (Presheaf.imageSieve_mem J f'.hom _)
  choose m V p hV hVcov hVle using hRef
  let β : O → Type max u₁ v := fun i => ULift.{max u₁ v} (Fin (m i.down))
  let α := Σ i : O, β i
  have hSections : ∀ a : α, ∃ t : G.obj.obj (op (V a.1.down a.2.down)),
      f'.hom.app (op (V a.1.down a.2.down)) t =
        R.obj.map (p a.1.down a.2.down).op
          ((Sigma.ι (fun k : O => (Sheaf.sheafifiedYoneda J).obj (U k.down)) a.1).hom.app
            (op (U a.1.down)) (Sheaf.tautologicalSection J (U a.1.down))) :=
    fun a => hVle a.1.down _ (Sieve.ofArrows_mk (V a.1.down) (p a.1.down) a.2.down)
  choose t ht using hSections
  let X : α → Sheaf J (Type max u₁ v) := fun a =>
    (Sheaf.sheafifiedYoneda J).obj (V a.1.down a.2.down)
  let g₀ : ∀ a : α, X a ⟶ G := fun a => (Sheaf.sectionEquiv J).symm (t a)
  let q₀ : ∀ a : α, X a ⟶ R := fun a =>
    (Sheaf.sheafifiedYoneda J).map (p a.1.down a.2.down) ≫
      Sigma.ι (fun k : O => (Sheaf.sheafifiedYoneda J).obj (U k.down)) a.1
  have hfac₀ (a : α) : g₀ a ≫ f' = q₀ a := by
    apply (Sheaf.sectionEquiv J).injective
    simpa only [g₀, q₀, Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply,
      Sheaf.sectionEquiv_sheafifiedYoneda_map, ← NatTrans.naturality_apply,
      Sheaf.map_op_tautologicalSection] using ht a
  let gᵢ : ∀ i : O, (∐ fun j : β i => X ⟨i, j⟩) ⟶ G :=
    fun i => Sigma.desc fun j => g₀ ⟨i, j⟩
  let hᵢ : ∀ i : O, (∐ fun j : β i => X ⟨i, j⟩) ⟶
      (Sheaf.sheafifiedYoneda J).obj (U i.down) :=
    fun i => Sigma.desc (f := fun j : β i => X ⟨i, j⟩) fun j =>
      (Sheaf.sheafifiedYoneda J).map (p i.down j.down)
  have hᵢepi (i : O) : Epi (hᵢ i) :=
    epi_sigmaDesc_sheafifiedYoneda_map_uLift J (p i.down) (hVcov i.down)
  let K' := ∐ fun i : O => ∐ fun j : β i => X ⟨i, j⟩
  let g : K' ⟶ G := Sigma.desc gᵢ
  let q : K' ⟶ R := Sigma.desc fun i => hᵢ i ≫
    Sigma.ι (fun k : O => (Sheaf.sheafifiedYoneda J).obj (U k.down)) i
  have hq : q = Limits.Sigma.map hᵢ := rfl
  have hqepi : Epi q := by
    rw [hq]
    exact Limits.Sigma.map_epi hᵢ
  have hfac : g ≫ f' = q := by
    refine Sigma.hom_ext _ _ fun i => Sigma.hom_ext _ _ fun j => ?_
    calc
      Sigma.ι (fun j : β i => X ⟨i, j⟩) j ≫
          Sigma.ι (fun k : O => ∐ fun j : β k => X ⟨k, j⟩) i ≫
            g ≫ f' = g₀ ⟨i, j⟩ ≫ f' := by simp [g, gᵢ]
      _ = q₀ ⟨i, j⟩ := hfac₀ ⟨i, j⟩
      _ = Sigma.ι (fun j : β i => X ⟨i, j⟩) j ≫
          Sigma.ι (fun k : O => ∐ fun j : β k => X ⟨k, j⟩) i ≫
            q := by simp only [q, q₀, hᵢ, ← Category.assoc, Sigma.ι_comp_desc]
  have hmem : K' ∈ FiniteCoproductSheafifiedYoneda J B := by
    simpa [K', X, α, β] using
      (nestedFiniteCoproduct_mem (B := B) (α := O) (β := β)
        (X := fun i j => V i.down j.down) (fun i j => hV i.down j.down))
  refine ⟨K', hmem, g, (Sheaf.isLocallySurjective_iff_epi _).2 ?_⟩
  have hgf : g ≫ f = q ≫ e'.inv := by
    rw [← hfac]
    simp [f']
  rw [hgf]
  exact epi_comp q e'.inv

/-- In sheaves of sets, a finite coproduct of binary products of sheaves is the binary product of
their finite coproducts. -/
private theorem nonempty_sigma_prod_iso_prod_sigma {C : Type u₁} [Category.{v} C]
    (J : GrothendieckTopology C) {n n' : ℕ} (A : Fin n → Sheaf J (Type max u₁ v))
    (A' : Fin n' → Sheaf J (Type max u₁ v)) :
    Nonempty ((∐ fun z : Fin n × Fin n' => A z.1 ⨯ A' z.2) ≅ (∐ A) ⨯ (∐ A')) := by
  let tA : ∀ i : Fin n, A i ⟶ ⊤_ (Sheaf J (Type max u₁ v)) := fun i => terminal.from (A i)
  let tA' : ∀ i : Fin n', A' i ⟶ ⊤_ (Sheaf J (Type max u₁ v)) := fun i => terminal.from (A' i)
  let compPull : (z : Fin n × Fin n') → pullback (terminal.from (A z.1))
      (terminal.from (A' z.2)) ⟶ pullback (Sigma.desc tA) (Sigma.desc tA') := fun z =>
    pullback.map (terminal.from (A z.1)) (terminal.from (A' z.2))
      (Sigma.desc tA) (Sigma.desc tA')
      (Sigma.ι A z.1) (Sigma.ι A' z.2) (𝟙 _)
      (by apply Subsingleton.elim) (by apply Subsingleton.elim)
  have : IsIso (Sigma.desc compPull) := FinitaryPreExtensive.isIso_sigmaDesc_map tA tA'
  have htA : Sigma.desc tA = terminal.from (∐ A) := Subsingleton.elim _ _
  have htA' : Sigma.desc tA' = terminal.from (∐ A') := Subsingleton.elim _ _
  exact ⟨(((Sigma.mapIso fun z : Fin n × Fin n' => prodIsoPullback (A z.1) (A' z.2)).trans
    (asIso (Sigma.desc compPull))).trans (pullback.congrHom htA htA')).trans
      (prodIsoPullback (∐ A) (∐ A')).symm⟩

/-- An object isomorphic to a coproduct, indexed by a finite type, of sheafified representables
of objects of `B` lies in `FiniteCoproductSheafifiedYoneda J B`. -/
private theorem mem_finiteCoproductSheafifiedYoneda_of_iso {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {B : Set C} {α : Type*} [Finite α]
    {K : Sheaf J (Type max u₁ v)} (X : α → C) (hX : ∀ a, X a ∈ B)
    (e : K ≅ ∐ fun a => (Sheaf.sheafifiedYoneda J).obj (X a)) :
    K ∈ FiniteCoproductSheafifiedYoneda J B := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let E : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  exact ⟨Fintype.card α, fun i => X (E i), fun i => hX (E i),
    ⟨e.trans (Sigma.reindex E (fun a : α => (Sheaf.sheafifiedYoneda J).obj (X a))).symm⟩⟩

/-- Hypothesis (3) of Stacks 0GN3 for finite coproducts of sheafified representables of objects
of `B`: the product of two of them receives a local surjection from a third. -/
private theorem exists_isLocallySurjective_prod_of_mem_finiteCoproductSheafifiedYoneda
    {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C) {B : Set C}
    (h_product : ∀ U ∈ B, ∀ U' ∈ B,
      ∃ (m : ℕ) (V : Fin m → C),
        (∀ i, V i ∈ B) ∧ ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
          Sheaf.IsLocallySurjective (Sigma.desc fun i =>
            prod.lift ((Sheaf.sheafifiedYoneda J).map (p i))
              ((Sheaf.sheafifiedYoneda J).map (q i))))
    {K K' : Sheaf J (Type max u₁ v)} (hK : K ∈ FiniteCoproductSheafifiedYoneda J B)
    (hK' : K' ∈ FiniteCoproductSheafifiedYoneda J B) :
    ∃ K'' ∈ FiniteCoproductSheafifiedYoneda J B, ∃ f : K'' ⟶ K ⨯ K',
      Sheaf.IsLocallySurjective f := by
  classical
  obtain ⟨n, U, hU, ⟨e⟩⟩ := hK
  obtain ⟨n', U', hU', ⟨e'⟩⟩ := hK'
  let α := Fin n × Fin n'
  have choices : ∀ z : α, ∃ (m : ℕ) (V : Fin m → C),
      (∀ k, V k ∈ B) ∧ ∃ (p : ∀ k, V k ⟶ U z.1) (q : ∀ k, V k ⟶ U' z.2),
        Sheaf.IsLocallySurjective (Sigma.desc fun k =>
          prod.lift ((Sheaf.sheafifiedYoneda J).map (p k))
            ((Sheaf.sheafifiedYoneda J).map (q k))) :=
    fun z => h_product (U z.1) (hU z.1) (U' z.2) (hU' z.2)
  choose m V hV p q hsurj using choices
  let A : Fin n → Sheaf J (Type max u₁ v) := fun i => (Sheaf.sheafifiedYoneda J).obj (U i)
  let A' : Fin n' → Sheaf J (Type max u₁ v) := fun i => (Sheaf.sheafifiedYoneda J).obj (U' i)
  let P : α → Sheaf J (Type max u₁ v) := fun z => A z.1 ⨯ A' z.2
  let β : α → Type max u₁ v := fun z => ULift.{max u₁ v} (Fin (m z))
  let E : α → Sheaf J (Type max u₁ v) := fun z => ∐ fun k : β z =>
    (Sheaf.sheafifiedYoneda J).obj (V z k.down)
  let E₀ : α → Sheaf J (Type max u₁ v) := fun z => ∐ fun k : Fin (m z) =>
    (Sheaf.sheafifiedYoneda J).obj (V z k)
  let eInner : ∀ z : α, E z ≅ E₀ z := fun z =>
    (Sigma.reindex Equiv.ulift.symm
      (fun k : ULift.{max u₁ v} (Fin (m z)) =>
        (Sheaf.sheafifiedYoneda J).obj (V z k.down))).symm
  let ep₀ : ∀ z : α, E₀ z ⟶ P z := fun z => Sigma.desc fun k =>
    prod.lift ((Sheaf.sheafifiedYoneda J).map (p z k))
      ((Sheaf.sheafifiedYoneda J).map (q z k))
  let ep : ∀ z : α, E z ⟶ P z := fun z => (eInner z).hom ≫ ep₀ z
  let K'' := ∐ E
  let hpair : K'' ⟶ ∐ P := Limits.Sigma.map ep
  have hepiPair : Epi hpair := by
    have (z : α) : Epi (ep z) := by
      have := (Sheaf.isLocallySurjective_iff_epi (ep₀ z)).1 (hsurj z)
      exact epi_comp (eInner z).hom (ep₀ z)
    exact Limits.Sigma.map_epi ep
  obtain ⟨dist⟩ := nonempty_sigma_prod_iso_prod_sigma J A A'
  let g : K'' ⟶ K ⨯ K' := hpair ≫ dist.hom ≫ (prod.mapIso e.symm e'.symm).hom
  have hg : Epi g := epi_comp _ _
  have hmem : K'' ∈ FiniteCoproductSheafifiedYoneda J B :=
    mem_finiteCoproductSheafifiedYoneda_of_iso (α := Σ z : α, β z) (fun t => V t.1 t.2.down)
      (fun t => hV t.1 t.2.down) (sigmaSigmaIso β fun z k => (Sheaf.sheafifiedYoneda J).obj
        (V z k.down))
  exact ⟨K'', hmem, g, (Sheaf.isLocallySurjective_iff_epi g).2 hg⟩

/-- A section `x` of `Y` over `Z` lifts locally along `f : L ⟶ Y` when, after a monomorphism `m`,
it factors as `w ≫ g` through a sheaf `E` receiving a local surjection `qE` whose composite with
`g` factors through `f ≫ m`. -/
private theorem imageSieve_sectionEquiv_mem_of_comp_eq {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {L Y M Q E : Sheaf J (Type max u₁ v)} {Z : C}
    (f : L ⟶ Y) (m : Y ⟶ M) [Mono m] (qE : Q ⟶ E) [Sheaf.IsLocallySurjective qE]
    (jL : Q ⟶ L) (g : E ⟶ M) (x : (Sheaf.sheafifiedYoneda J).obj Z ⟶ Y)
    (w : (Sheaf.sheafifiedYoneda J).obj Z ⟶ E) (hjL : jL ≫ f ≫ m = qE ≫ g)
    (hx : x ≫ m = w ≫ g) :
    Presheaf.imageSieve f.hom (Sheaf.sectionEquiv J x) ∈ J Z := by
  apply J.superset_covering _ (Presheaf.imageSieve_mem J qE.hom (Sheaf.sectionEquiv J w))
  intro Z₄ t₄ ht₄
  obtain ⟨w₄, hw₄⟩ := (mem_imageSieve_sectionEquiv_iff qE w t₄).1 ht₄
  refine (mem_imageSieve_sectionEquiv_iff f x t₄).2 ⟨w₄ ≫ jL, (cancel_mono m).1 ?_⟩
  simp only [Category.assoc, hjL, reassoc_of% hw₄, hx]

/-- Hypothesis (4) of Stacks 0GN3 for finite coproducts of sheafified representables of objects
of `B`: the equalizer of two maps between them receives a local surjection from a third. -/
private theorem exists_isLocallySurjective_equalizer_of_mem_finiteCoproductSheafifiedYoneda
    {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C) {B : Set C}
    (h_refine : ∀ U ∈ B, HasFiniteCoverRefinementsFrom J B U)
    (h_equalizer : ∀ {U U' : C} (a b : U ⟶ U'), U ∈ B → U' ∈ B →
      ∃ (m : ℕ) (V : Fin m → C),
        (∀ i, V i ∈ B) ∧ ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Sigma.desc fun i =>
            equalizer.lift (f := (Sheaf.sheafifiedYoneda J).map a)
              (g := (Sheaf.sheafifiedYoneda J).map b)
              ((Sheaf.sheafifiedYoneda J).map (p i)) (by
              simpa only [Functor.map_comp] using congrArg (Sheaf.sheafifiedYoneda J).map (hp i))))
    {K K' : Sheaf J (Type max u₁ v)} (a b : K ⟶ K')
    (hK : K ∈ FiniteCoproductSheafifiedYoneda J B)
    (hK' : K' ∈ FiniteCoproductSheafifiedYoneda J B) :
    ∃ K'' ∈ FiniteCoproductSheafifiedYoneda J B, ∃ f : K'' ⟶ equalizer a b,
      Sheaf.IsLocallySurjective f := by
  classical
  obtain ⟨n, U, hU, ⟨e⟩⟩ := hK
  obtain ⟨n', U', hU', ⟨e'⟩⟩ := hK'
  let A : Fin n → Sheaf J (Type max u₁ v) := fun i => (Sheaf.sheafifiedYoneda J).obj (U i)
  let A' : Fin n' → Sheaf J (Type max u₁ v) := fun i => (Sheaf.sheafifiedYoneda J).obj (U' i)
  let a' : ∐ A ⟶ ∐ A' := e.inv ≫ a ≫ e'.hom
  let b' : ∐ A ⟶ ∐ A' := e.inv ≫ b ≫ e'.hom
  have hLocal : ∀ i : Fin n, ∃ (S T : Sieve (U i)), S ∈ J (U i) ∧ T ∈ J (U i) ∧
      (∀ ⦃W : C⦄ (p : W ⟶ U i), S p →
        ∃ (j : Fin n') (r : W ⟶ U' j),
          (Sheaf.sheafifiedYoneda J).map p ≫ Sigma.ι A i ≫ a' =
            (Sheaf.sheafifiedYoneda J).map r ≫ Sigma.ι A' j) ∧
      (∀ ⦃W : C⦄ (p : W ⟶ U i), T p →
        ∃ (j : Fin n') (r : W ⟶ U' j),
          (Sheaf.sheafifiedYoneda J).map p ≫ Sigma.ι A i ≫ b' =
            (Sheaf.sheafifiedYoneda J).map r ≫ Sigma.ι A' j) := by
    intro i
    obtain ⟨S, hS, hfa⟩ :=
      exists_local_factor_through_finite_coproduct (V := U') (Sigma.ι A i ≫ a')
    obtain ⟨T, hT, hfb⟩ :=
      exists_local_factor_through_finite_coproduct (V := U') (Sigma.ι A i ≫ b')
    exact ⟨S, T, hS, hT, hfa, hfb⟩
  choose S₁ T₁ hS hT hfa hfb using hLocal
  have hCover : ∀ i : Fin n, ∃ (r : ℕ) (V : Fin r → C) (p : ∀ k, V k ⟶ U i),
      (∀ k, V k ∈ B) ∧ Sieve.ofArrows V p ∈ J (U i) ∧ Sieve.ofArrows V p ≤ S₁ i ⊓ T₁ i :=
    fun i => h_refine (U i) (hU i) (S₁ i ⊓ T₁ i) (J.intersection_covering (hS i) (hT i))
  choose r V p hV hVcov hVle using hCover
  have hAFactors : ∀ (i : Fin n) (k : Fin (r i)),
      ∃ (j : Fin n') (c : V i k ⟶ U' j),
        (Sheaf.sheafifiedYoneda J).map (p i k) ≫ Sigma.ι A i ≫ a' =
          (Sheaf.sheafifiedYoneda J).map c ≫ Sigma.ι A' j :=
    fun i k => hfa i (p i k) (hVle i (p i k) (Sieve.ofArrows_mk (V i) (p i) k)).1
  choose ja ca hca using hAFactors
  have hBFactors : ∀ (i : Fin n) (k : Fin (r i)),
      ∃ (j : Fin n') (c : V i k ⟶ U' j),
        (Sheaf.sheafifiedYoneda J).map (p i k) ≫ Sigma.ι A i ≫ b' =
          (Sheaf.sheafifiedYoneda J).map c ≫ Sigma.ι A' j :=
    fun i k => hfb i (p i k) (hVle i (p i k) (Sieve.ofArrows_mk (V i) (p i) k)).2
  choose jb cb hcb using hBFactors
  let δ := {z : Σ i : Fin n, Fin (r i) // ja z.1 z.2 = jb z.1 z.2}
  let cb' (z : δ) : V z.1.1 z.1.2 ⟶ U' (ja z.1.1 z.1.2) :=
    Eq.mp (congrArg (fun j : Fin n' => V z.1.1 z.1.2 ⟶ U' j) z.2.symm) (cb z.1.1 z.1.2)
  have hEqChoices : ∀ z : δ,
      ∃ (s : ℕ) (W : Fin s → C), (∀ l, W l ∈ B) ∧
        ∃ (q : ∀ l, W l ⟶ V z.1.1 z.1.2),
        ∃ hq : ∀ l, q l ≫ ca z.1.1 z.1.2 = q l ≫ cb' z,
          Sheaf.IsLocallySurjective (Sigma.desc fun l =>
            equalizer.lift (f := (Sheaf.sheafifiedYoneda J).map (ca z.1.1 z.1.2))
              (g := (Sheaf.sheafifiedYoneda J).map (cb' z))
              ((Sheaf.sheafifiedYoneda J).map (q l)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda J).map (hq l))) :=
    fun z => h_equalizer (ca z.1.1 z.1.2) (cb' z) (hV z.1.1 z.1.2) (hU' (ja z.1.1 z.1.2))
  choose s W hW q hq hqsurj using hEqChoices
  have hcb' (z : δ) :
      (Sheaf.sheafifiedYoneda J).map (p z.1.1 z.1.2) ≫ Sigma.ι A z.1.1 ≫ b' =
        (Sheaf.sheafifiedYoneda J).map (cb' z) ≫ Sigma.ι A' (ja z.1.1 z.1.2) := by
    rw [show (Sheaf.sheafifiedYoneda J).map (cb' z) ≫ Sigma.ι A' (ja z.1.1 z.1.2) =
        (Sheaf.sheafifiedYoneda J).map (cb z.1.1 z.1.2) ≫ Sigma.ι A' (jb z.1.1 z.1.2) from
        sheafifiedYoneda_map_cast_comp_sigma_ι U' z.2 (cb z.1.1 z.1.2)]
    exact hcb z.1.1 z.1.2
  let Tidx := Σ z : δ, Fin (s z)
  let X : Tidx → C := fun t => W t.1 t.2
  let L := ∐ fun t : Tidx => (Sheaf.sheafifiedYoneda J).obj (X t)
  let pK (t : Tidx) : X t ⟶ U t.1.1.1 := q t.1 t.2 ≫ p t.1.1.1 t.1.1.2
  let vK (t : Tidx) : (Sheaf.sheafifiedYoneda J).obj (X t) ⟶ K :=
    (Sheaf.sheafifiedYoneda J).map (pK t) ≫ Sigma.ι A t.1.1.1 ≫ e.inv
  have hvEq (t : Tidx) : vK t ≫ a = vK t ≫ b := by
    apply (cancel_mono e'.hom).1
    change (Sheaf.sheafifiedYoneda J).map (pK t) ≫ Sigma.ι A t.1.1.1 ≫ a' =
      (Sheaf.sheafifiedYoneda J).map (pK t) ≫ Sigma.ι A t.1.1.1 ≫ b'
    rcases t with ⟨z, l⟩
    dsimp only [pK]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    calc
      (Sheaf.sheafifiedYoneda J).map (q z l) ≫
          ((Sheaf.sheafifiedYoneda J).map (p z.1.1 z.1.2) ≫ Sigma.ι A z.1.1 ≫ a') =
        (Sheaf.sheafifiedYoneda J).map (q z l) ≫
          ((Sheaf.sheafifiedYoneda J).map (ca z.1.1 z.1.2) ≫
            Sigma.ι A' (ja z.1.1 z.1.2)) := by rw [hca]
      _ = (Sheaf.sheafifiedYoneda J).map (q z l) ≫
          ((Sheaf.sheafifiedYoneda J).map (cb' z) ≫ Sigma.ι A' (ja z.1.1 z.1.2)) := by
            simp only [← Functor.map_comp_assoc, hq]
      _ = (Sheaf.sheafifiedYoneda J).map (q z l) ≫
          ((Sheaf.sheafifiedYoneda J).map (p z.1.1 z.1.2) ≫
            Sigma.ι A z.1.1 ≫ b') := by rw [hcb']
  let v (t : Tidx) : (Sheaf.sheafifiedYoneda J).obj (X t) ⟶ equalizer a b :=
    equalizer.lift (vK t) (hvEq t)
  let f : L ⟶ equalizer a b := Sigma.desc v
  have hLmem : L ∈ FiniteCoproductSheafifiedYoneda J B :=
    mem_finiteCoproductSheafifiedYoneda_of_iso X (fun t => hW t.1 t.2) (Iso.refl _)
  refine ⟨L, hLmem, f, ?_⟩
  change Presheaf.IsLocallySurjective J f.hom
  constructor
  intro Z y
  obtain ⟨x, rfl⟩ := (Sheaf.sectionEquiv J).surjective y
  obtain ⟨T, hT, hfactor⟩ := exists_local_factor_through_finite_coproduct
    U (x ≫ equalizer.ι a b ≫ e.hom)
  apply J.transitive hT
  intro Z₁ t ht
  rw [pullback_imageSieve_sectionEquiv]
  let x₁ : (Sheaf.sheafifiedYoneda J).obj Z₁ ⟶ equalizer a b :=
    (Sheaf.sheafifiedYoneda J).map t ≫ x
  obtain ⟨i, d, hd⟩ := hfactor t ht
  have hx₁ : x₁ ≫ equalizer.ι a b ≫ e.hom = (Sheaf.sheafifiedYoneda J).map d ≫ Sigma.ι A i := hd
  apply J.transitive (J.pullback_stable d (hVcov i))
  intro Z₂ t₂ ht₂
  rw [pullback_imageSieve_sectionEquiv]
  let x₂ : (Sheaf.sheafifiedYoneda J).obj Z₂ ⟶ equalizer a b :=
    (Sheaf.sheafifiedYoneda J).map t₂ ≫ x₁
  change Presheaf.imageSieve f.hom (Sheaf.sectionEquiv J x₂) ∈ J Z₂
  obtain ⟨k, c, hc⟩ := (Sieve.mem_ofArrows_iff (V i) (p i) (t₂ ≫ d)).1 ht₂
  have hx₂ : x₂ ≫ equalizer.ι a b ≫ e.hom =
      (Sheaf.sheafifiedYoneda J).map c ≫
        (Sheaf.sheafifiedYoneda J).map (p i k) ≫ Sigma.ι A i := by
    calc
      x₂ ≫ equalizer.ι a b ≫ e.hom =
          (Sheaf.sheafifiedYoneda J).map t₂ ≫ (x₁ ≫ equalizer.ι a b ≫ e.hom) := by
            simp only [x₂, Category.assoc]
      _ = (Sheaf.sheafifiedYoneda J).map t₂ ≫
          (Sheaf.sheafifiedYoneda J).map d ≫ Sigma.ι A i := by rw [hx₁]
      _ = (Sheaf.sheafifiedYoneda J).map c ≫
          (Sheaf.sheafifiedYoneda J).map (p i k) ≫ Sigma.ι A i := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun g => (Sheaf.sheafifiedYoneda J).map g ≫ Sigma.ι A i) hc
  have heq : (Sheaf.sheafifiedYoneda J).map (c ≫ ca i k) ≫ Sigma.ι A' (ja i k) =
      (Sheaf.sheafifiedYoneda J).map (c ≫ cb i k) ≫ Sigma.ι A' (jb i k) := by
    have heq' : (x₂ ≫ equalizer.ι a b ≫ e.hom) ≫ a' =
        (x₂ ≫ equalizer.ι a b ≫ e.hom) ≫ b' := by
      dsimp only [a', b']
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      simpa only [Category.assoc] using
        congrArg (fun g => x₂ ≫ g ≫ e'.hom) (equalizer.condition a b)
    rw [hx₂] at heq'
    simp only [Category.assoc] at heq'
    rw [hca, hcb] at heq'
    simpa only [Functor.map_comp, Category.assoc] using heq'
  obtain ⟨T₂, hT₂, hequal⟩ := exists_local_eq_through_finite_coproduct U' heq
  apply J.transitive hT₂
  intro Z₃ t₃ ht₃
  rw [pullback_imageSieve_sectionEquiv]
  let x₃ : (Sheaf.sheafifiedYoneda J).obj Z₃ ⟶ equalizer a b :=
    (Sheaf.sheafifiedYoneda J).map t₃ ≫ x₂
  change Presheaf.imageSieve f.hom (Sheaf.sectionEquiv J x₃) ∈ J Z₃
  obtain ⟨hij, hab⟩ := hequal t₃ ht₃
  let z : δ := ⟨⟨i, k⟩, hij⟩
  have hdEq : (t₃ ≫ c) ≫ ca i k = (t₃ ≫ c) ≫ cb' z :=
    comp_eq_cast_of_heq hij (t₃ ≫ c) (by simpa only [Category.assoc] using hab)
  let E := equalizer ((Sheaf.sheafifiedYoneda J).map (ca i k))
    ((Sheaf.sheafifiedYoneda J).map (cb' z))
  let w : (Sheaf.sheafifiedYoneda J).obj Z₃ ⟶ E :=
    equalizer.lift ((Sheaf.sheafifiedYoneda J).map (t₃ ≫ c)) (by
      simpa only [Functor.map_comp] using congrArg (Sheaf.sheafifiedYoneda J).map hdEq)
  let Q := ∐ fun l : Fin (s z) => (Sheaf.sheafifiedYoneda J).obj (W z l)
  let qE : Q ⟶ E := Sigma.desc fun l =>
    equalizer.lift ((Sheaf.sheafifiedYoneda J).map (q z l)) (by
      simpa only [Functor.map_comp] using congrArg (Sheaf.sheafifiedYoneda J).map (hq z l))
  have hqE : Sheaf.IsLocallySurjective qE := hqsurj z
  let jL : Q ⟶ L := Sigma.desc fun l =>
    Sigma.ι (fun t : Tidx => (Sheaf.sheafifiedYoneda J).obj (X t)) ⟨z, l⟩
  have hjL : jL ≫ f ≫ equalizer.ι a b ≫ e.hom =
      qE ≫ equalizer.ι ((Sheaf.sheafifiedYoneda J).map (ca i k))
        ((Sheaf.sheafifiedYoneda J).map (cb' z)) ≫
        (Sheaf.sheafifiedYoneda J).map (p i k) ≫ Sigma.ι A i := by
    refine Sigma.hom_ext _ _ fun l => ?_
    dsimp only [jL, f, qE]
    simp only [Sigma.ι_comp_desc_assoc, v, equalizer.lift_ι_assoc]
    simp only [vK, pK, z, Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hx₃ : x₃ ≫ equalizer.ι a b ≫ e.hom =
      w ≫ equalizer.ι ((Sheaf.sheafifiedYoneda J).map (ca i k))
        ((Sheaf.sheafifiedYoneda J).map (cb' z)) ≫
        (Sheaf.sheafifiedYoneda J).map (p i k) ≫ Sigma.ι A i := by
    simp only [w, equalizer.lift_ι_assoc, Functor.map_comp]
    simpa only [x₃, Category.assoc] using
      congrArg (fun g => (Sheaf.sheafifiedYoneda J).map t₃ ≫ g) hx₂
  exact imageSieve_sectionEquiv_mem_of_comp_eq f (equalizer.ι a b ≫ e.hom) qE jL _ x₃ w hjL hx₃

/-! ### The criterion on an arbitrary site -/

/-- **Stacks 0GN4 for an arbitrary site.** Let `C` be a site with objects in `Type u₁` and
morphisms in `Type v`, let `B ⊆ Ob(C)`, and assume

1. for some `n ≥ 0` and `U_1, …, U_n ∈ B` the map `∐_i h_{U_i}^# ⟶ *` is surjective,
2. every covering of a `U ∈ B` is refined by a finite covering family with sources in `B`,
3. for any `U, U' ∈ B` there are finitely many `V_i ∈ B` with maps to both for which
   `∐_i h_{V_i}^# ⟶ h_U^# ⨯ h_{U'}^#` is surjective, and
4. for any `a, b : U ⟶ U'` between members of `B` there are finitely many `V_i ∈ B` with maps to
   `U` equalizing `a` and `b` for which `∐_i h_{V_i}^# ⟶ Equalizer(h_a^#, h_b^#)` is surjective.

Then `colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism in every degree, for every
filtered diagram of abelian sheaves with sections at the join `max u₁ v` of the two universes of
the site.

The small-site form of the tag asks for `SmallCategory C`, that is for the objects and the morphisms
of the site to live in one universe, which the sites of algebraic geometry do not satisfy. Here
the site is arbitrary, every sheaf of sets and every abelian coefficient living at the join of its
two universes.

The proof is the source's: it checks the five hypotheses of Stacks 0GN3 for the set `S` of finite
coproducts of sheafified representables of objects of `B`, and concludes by
`isIso_colimit_post_rightDerived_globalSections_of_coveringSet`, the form of Stacks 0GN3 for an
arbitrary site. Hypotheses (1), (3) and (4) of Stacks 0GN3 come from (1), (3) and (4) here, after
rewriting a coproduct of pairings as a map out of a coproduct and distributing a coproduct over a
product. Hypothesis (2), the lifting property for a surjection `G ⟶ K` with `K ∈ S`, is obtained
by applying (2) to the sieve of local liftings of the tautological section of each summand of `K`:
this produces a finite covering of each summand by objects of `B` over which the surjection
splits, and the resulting coproduct is again in `S`. Hypothesis (5) is
`isQuasiCompact_of_finiteCoproductSheafifiedYoneda`, which is already general. -/
@[stacks 0GN4 "criterion, for a site whose objects and morphisms need not share a universe"]
theorem isIso_colimit_post_rightDerived_globalSections_of_covers
    {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C) (B : Set C)
    (h_terminal : ∃ (m : ℕ) (U : Fin m → C),
      (∀ i, U i ∈ B) ∧
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i => terminal.from ((Sheaf.sheafifiedYoneda J).obj (U i))))
    (h_refine : ∀ U ∈ B, HasFiniteCoverRefinementsFrom J B U)
    (h_product : ∀ U ∈ B, ∀ U' ∈ B,
      ∃ (m : ℕ) (V : Fin m → C),
        (∀ i, V i ∈ B) ∧ ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
          Sheaf.IsLocallySurjective (Sigma.desc fun i =>
            prod.lift ((Sheaf.sheafifiedYoneda J).map (p i))
              ((Sheaf.sheafifiedYoneda J).map (q i))))
    (h_equalizer : ∀ {U U' : C} (a b : U ⟶ U'), U ∈ B → U' ∈ B →
      ∃ (m : ℕ) (V : Fin m → C),
        (∀ i, V i ∈ B) ∧ ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Sigma.desc fun i =>
            equalizer.lift (f := (Sheaf.sheafifiedYoneda J).map a)
              (g := (Sheaf.sheafifiedYoneda J).map b)
              ((Sheaf.sheafifiedYoneda J).map (p i)) (by
              simpa only [Functor.map_comp] using congrArg (Sheaf.sheafifiedYoneda J).map (hp i))))
    (n : ℕ) {I : Type max u₁ v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J (Ab.{max u₁ v})) :
    IsIso (colimit.post F ((Sheaf.Γ J (Ab.{max u₁ v})).rightDerived n)) := by
  apply isIso_colimit_post_rightDerived_globalSections_of_coveringSet J
    (FiniteCoproductSheafifiedYoneda J B)
  · obtain ⟨m, U, hU, hsurj⟩ := h_terminal
    let K := ∐ fun i : Fin m => (Sheaf.sheafifiedYoneda J).obj (U i)
    exact ⟨K, ⟨m, U, hU, ⟨Iso.refl _⟩⟩, (Subsingleton.elim (Sigma.desc fun i : Fin m =>
      terminal.from ((Sheaf.sheafifiedYoneda J).obj (U i))) (terminal.from K)) ▸ hsurj⟩
  · exact fun f hK hsurj =>
      exists_isLocallySurjective_comp_of_mem_finiteCoproductSheafifiedYoneda J h_refine f hK hsurj
  · exact fun _ hK _ hK' =>
      exists_isLocallySurjective_prod_of_mem_finiteCoproductSheafifiedYoneda J h_product hK hK'
  · exact fun a b hK hK' =>
      exists_isLocallySurjective_equalizer_of_mem_finiteCoproductSheafifiedYoneda J h_refine
        h_equalizer a b hK hK'
  · exact fun _ hK => isQuasiCompact_of_finiteCoproductSheafifiedYoneda J B h_refine hK

end Stacks.Cohomology.ColimitsOfCohomology

end
