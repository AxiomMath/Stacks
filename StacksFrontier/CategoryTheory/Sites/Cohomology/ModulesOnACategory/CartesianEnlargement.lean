module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallNonzeroMaps
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallSubcomplexEnlargements

/-!
# Unions of increasing chains of subcomplexes of a complex of modules

Let `C` be a category, regarded as a site with the chaotic topology, and let `O` be a presheaf
of rings on `C`. This file constructs the union of an increasing chain of subcomplexes
`S^• = G_0^• ⊆ G_1^• ⊆ G_2^• ⊆ ⋯ ⊆ F^•` of a complex of `O`-modules, and the chain obtained by
iterating a one-step enlargement with a prescribed property, as in the enlargement argument of
Stacks 0GYZ.

A subcomplex of a complex `F^•` of `O`-modules in the strict sense — a degreewise family of
submodules of the terms of `F^•` stable under the differentials — is recorded as
`ComplexSubmodule F`, and `ComplexSubmodule.toComplex` realizes it as a complex with a
monomorphism into `F^•`. The union of a chain of subcomplexes is the degreewise sectionwise
supremum of the ranges of the inclusions; it is stable under the differentials because the chain
is directed, so every section of the union already lies in one stage, and the number of its
sections is bounded by `ℵ₀` times the supremum of the numbers of sections of the stages.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.ComplexSubmodule`: a degreewise family of
  submodules of the terms of a complex of `O`-modules, stable under the differentials.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.ComplexSubmodule.toComplex`: the subcomplex
  such a family cuts out, together with `ComplexSubmodule.ι`, its inclusion.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BoundedSubcomplex`: a subcomplex of a
  complex of `O`-modules with at most a prescribed number of sections.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.EnlargementProperty`: a property of a
  one-step enlargement of such a subcomplex.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.Enlargement`: a one-step enlargement of
  such a subcomplex, satisfying a prescribed property.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_union_of_chain`: the union of an
  increasing chain of subcomplexes of `F^•`, each with at most `Λ` sections, is a subcomplex of
  `F^•` with at most `Λ` sections through which every stage factors, and each of its sections
  comes from a stage.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_union_of_iterated_enlargement`: the
  subcomplex obtained by iterating a one-step enlargement countably often and taking the union,
  with the enlargement property available at every stage.
* `exists_iterated_enlargement_containing_sections`, in the same namespace: the same iteration
  run with the step of Stacks 0GYX, so that each stage contains a family of sections of `F^•`
  prescribed in terms of the preceding stage.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYX](https://stacks.math.columbia.edu/tag/0GYX)
* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-! ### Subcomplexes cut out by a degreewise family of submodules -/

/-- A degreewise family of submodules of the terms of a complex `F` of `O`-modules which is
stable under the differentials of `F`. This is the data of a subcomplex of `F` in the strict
sense: the terms are submodules of the terms of `F` and the differentials are restrictions of
the differentials of `F`. -/
structure ComplexSubmodule (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) where
  /-- The submodule of the term of `F` in degree `i`. -/
  obj (i : ℤ) : (F.X i).Submodule
  /-- The family is stable under the differentials of `F`. -/
  d_mem : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (F.X i).obj X), x ∈ (obj i).obj X →
    (F.d i j).app X x ∈ (obj j).obj X

namespace ComplexSubmodule

variable {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
  (N : ComplexSubmodule.{w} F)

/-- The restriction of a differential of `F` to a stable family of submodules has range in the
next member of the family. -/
lemma range_le (i j : ℤ) :
    PresheafOfModules.Submodule.range ((N.obj i).ι ≫ F.d i j) ≤
      PresheafOfModules.Submodule.range (N.obj j).ι := by
  rw [PresheafOfModules.Submodule.range_ι, PresheafOfModules.Submodule.le_iff]
  rintro X y ⟨x, rfl⟩
  rw [PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  exact N.d_mem i j X _ x.property

/-- The subcomplex of `F` cut out by a stable family of submodules: in degree `i` its term is
the given submodule of `F.X i`, and its differential is the restriction of the differential
of `F`. -/
def toComplex : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ where
  X i := (N.obj i).toPresheafOfModules
  d i j := PresheafOfModules.factorThru ((N.obj i).ι ≫ F.d i j) (N.obj j).ι (N.range_le i j)
  shape i j hij := by
    rw [← cancel_mono (N.obj j).ι, zero_comp, PresheafOfModules.factorThru_comp,
      F.shape i j hij, comp_zero]
  d_comp_d' i j k _ _ := by
    rw [← cancel_mono (N.obj k).ι, zero_comp, Category.assoc,
      PresheafOfModules.factorThru_comp, PresheafOfModules.factorThru_comp_assoc,
      Category.assoc, HomologicalComplex.d_comp_d, comp_zero]

/-- The inclusion of the subcomplex cut out by a stable family of submodules. -/
def ι : N.toComplex ⟶ F where
  f i := (N.obj i).ι
  comm' i j _ :=
    (PresheafOfModules.factorThru_comp ((N.obj i).ι ≫ F.d i j) (N.obj j).ι
      (N.range_le i j)).symm

/-- The inclusion `N.ι` is, in degree `i`, the inclusion of the submodule `N.obj i`. -/
@[simp]
lemma ι_f (i : ℤ) : N.ι.f i = (N.obj i).ι := rfl

/-- The inclusion of the subcomplex cut out by a stable family of submodules is a
monomorphism. -/
instance mono_ι : Mono N.ι :=
  HomologicalComplex.mono_of_mono_f N.ι (fun i => inferInstanceAs (Mono (N.obj i).ι))

end ComplexSubmodule

/-! ### The union of an increasing chain of subcomplexes -/

section Chain

variable {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
  {G : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}

/-- The range, in degree `i`, of the `n`-th map into `F` of a chain of complexes over `F`. -/
def chainRange (γ : ∀ n, G n ⟶ F) (i : ℤ) (n : ℕ) : (F.X i).Submodule :=
  PresheafOfModules.Submodule.range ((γ n).f i)

variable (γ : ∀ n, G n ⟶ F) {q : ∀ n, G n ⟶ G (n + 1)} (hq : ∀ n, q n ≫ γ (n + 1) = γ n)

include hq

/-- A compatible chain has increasing ranges: the `n`-th map into `F` factors through the
`(n+1)`-st. -/
lemma chainRange_monotone (i : ℤ) : Monotone (chainRange.{w} γ i) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have h : (γ n).f i = (q n).f i ≫ (γ (n + 1)).f i := by
    rw [← HomologicalComplex.comp_f, hq n]
  rw [chainRange, chainRange, h]
  exact PresheafOfModules.Submodule.range_comp_le _ _

/-- The sections of the union of a compatible chain, in degree `i` over an object `X`, are the
sections of the stages: the family of ranges is directed. -/
lemma mem_iSup_chainRange_iff (i : ℤ) (X : Cᵒᵖ) (x : (F.X i).obj X) :
    x ∈ ⨆ n, (chainRange.{w} γ i n).obj X ↔ ∃ n, x ∈ (chainRange.{w} γ i n).obj X :=
  Submodule.mem_iSup_of_directed _
    (Monotone.directed_le (fun _ _ hab => chainRange_monotone.{w} γ hq i hab X))

/-- The union of a compatible chain of subcomplexes, as a stable family of submodules of the
terms of `F`: in degree `i` over an object `X` it is the supremum of the ranges of the maps of
the chain. -/
def chainUnion : ComplexSubmodule.{w} F where
  obj i :=
    { obj X := ⨆ n, (chainRange.{w} γ i n).obj X
      map {X Y} f := iSup_le fun n => ((chainRange.{w} γ i n).map f).trans
        (Submodule.comap_mono (le_iSup (fun m => (chainRange.{w} γ i m).obj Y) n)) }
  d_mem i j X x hx := by
    obtain ⟨n, y, hy⟩ := (mem_iSup_chainRange_iff.{w} γ hq i X x).1 hx
    refine Submodule.mem_iSup_of_mem n ⟨((G n).d i j).app X y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
      ← HomologicalComplex.Hom.comm, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply, hy]

/-- A stage of a compatible chain has its sections among those of the union. -/
lemma chainRange_le_chainUnion (n : ℕ) (i : ℤ) :
    chainRange.{w} γ i n ≤ (chainUnion.{w} γ hq).obj i :=
  fun X => le_iSup (fun m => (chainRange.{w} γ i m).obj X) n

/-- Let `F^•` be a complex of `O`-modules
and let `G_0^• ⟶ G_1^• ⟶ ⋯` be a chain of complexes over `F^•`, each with at most `Λ` sections,
where `Λ` is infinite. Then there is a subcomplex `H^• ⊆ F^•` with at most `Λ` sections through
which every map `G_n^• ⟶ F^•` factors, and every section of `H^•` is the image of a section of
some `G_n^•`. -/
theorem exists_union_of_chain {Λ : Cardinal.{max u v r w}} (hΛ : Cardinal.aleph0 ≤ Λ)
    (hsize : ∀ n, complexSectionSize.{w} O (G n) ≤ Λ) :
    ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F)
      (k : ∀ n, G n ⟶ H),
      Mono h ∧ (∀ n, k n ≫ h = γ n) ∧ complexSectionSize.{w} O H ≤ Λ ∧
        ∀ (i : ℤ) (X : Cᵒᵖ) (x : (H.X i).obj X),
          ∃ (n : ℕ) (y : ((G n).X i).obj X), ((k n).f i).app X y = x := by
  classical
  set N := chainUnion.{w} γ hq
  have hfac : ∀ n, ∃ kn : G n ⟶ N.toComplex, kn ≫ N.ι = γ n := fun n =>
    exists_hom_of_sectionwise_mem_range.{w} (γ n) N.ι fun i X x =>
      ⟨⟨((γ n).f i).app X x, chainRange_le_chainUnion.{w} γ hq n i X ⟨x, rfl⟩⟩, rfl⟩
  choose k hk using hfac
  have hexh : ∀ (i : ℤ) (X : Cᵒᵖ) (x : (N.toComplex.X i).obj X),
      ∃ (n : ℕ) (y : ((G n).X i).obj X), ((k n).f i).app X y = x := by
    intro i X x
    obtain ⟨n, y, hy⟩ := (mem_iSup_chainRange_iff.{w} γ hq i X x.val).1 x.property
    refine ⟨n, y, Subtype.ext ?_⟩
    have h : ((k n).f i ≫ (N.obj i).ι).app X y = ((γ n).f i).app X y := by
      rw [← N.ι_f i, ← HomologicalComplex.comp_f, hk n]
    exact h.trans hy
  refine ⟨N.toComplex, N.ι, k, inferInstance, hk, ?_, hexh⟩
  let A : ℕ → Type (max u v r w) := fun n => Σ i : ℤ, Σ U : C, ((G n).X i).obj (op U)
  let B : Type (max u v r w) := Σ i : ℤ, Σ U : C, (N.toComplex.X i).obj (op U)
  let e : (Σ n : ℕ, A n) → B := fun p =>
    ⟨p.2.1, p.2.2.1, ((k p.1).f p.2.1).app (op p.2.2.1) p.2.2.2⟩
  have he : Function.Surjective e := by
    rintro ⟨i, U, x⟩
    obtain ⟨n, y, hy⟩ := hexh i (op U) x
    exact ⟨⟨n, i, U, y⟩, congrArg (fun z : (N.toComplex.X i).obj (op U) =>
      (⟨i, U, z⟩ : B)) hy⟩
  have hA : ∀ n, Cardinal.mk (A n) ≤ Λ := hsize
  calc complexSectionSize.{w} O N.toComplex
      = Cardinal.mk B := rfl
    _ ≤ Cardinal.sum (fun n => Cardinal.mk (A n)) := by
        rw [← Cardinal.mk_sigma]
        exact Cardinal.mk_le_of_surjective he
    _ ≤ Cardinal.lift.{max u v r w, 0} (Cardinal.mk ℕ) *
          ⨆ n, Cardinal.mk (A n) := Cardinal.sum_le_lift_mk_mul_iSup _
    _ = Cardinal.aleph0 * ⨆ n, Cardinal.mk (A n) := by
        simp only [Cardinal.mk_nat, Cardinal.lift_aleph0]
    _ ≤ Cardinal.aleph0 * Λ := mul_le_mul_right (ciSup_le' hA) Cardinal.aleph0
    _ ≤ Λ := Cardinal.mul_le_of_le hΛ hΛ le_rfl

end Chain

/-! ### Iterating a one-step enlargement -/

/-- A subcomplex of a complex `F` of `O`-modules with at most `Λ` sections, presented by a
monomorphism into `F`. -/
structure BoundedSubcomplex (O : Cᵒᵖ ⥤ RingCat.{r})
    (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
    (Λ : Cardinal.{max u v r w}) where
  /-- The subcomplex. -/
  H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ
  /-- Its inclusion into `F`. -/
  inc : H ⟶ F
  /-- The inclusion is a monomorphism. -/
  mono_inc : Mono inc
  /-- The subcomplex has at most `Λ` sections. -/
  size_le : complexSectionSize.{w} O H ≤ Λ

/-- A property of a one-step enlargement of a subcomplex of `F`: it is a property of the two
subcomplexes, presented by their inclusions into `F`, and of the map between them. -/
abbrev EnlargementProperty (O : Cᵒᵖ ⥤ RingCat.{r})
    (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) : Type _ :=
  ∀ G₁ : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ, (G₁ ⟶ F) →
    ∀ G₂ : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ, (G₂ ⟶ F) → (G₁ ⟶ G₂) → Prop

/-- A one-step enlargement of a bounded subcomplex `B` of `F` with the property `P`: a bounded
subcomplex of `F` containing `B`, together with the witness that `P` holds of the pair. -/
structure Enlargement {O : Cᵒᵖ ⥤ RingCat.{r}}
    {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    {Λ : Cardinal.{max u v r w}} (P : EnlargementProperty.{w} O F)
    (B : BoundedSubcomplex.{w} O F Λ) where
  /-- The enlarged subcomplex. -/
  next : BoundedSubcomplex.{w} O F Λ
  /-- The inclusion of `B` into the enlargement. -/
  map : B.H ⟶ next.H
  /-- The inclusion of `B` into the enlargement is compatible with the inclusions into `F`. -/
  factor : map ≫ next.inc = B.inc
  /-- The enlargement has the prescribed property. -/
  prop : P B.H B.inc next.H next.inc map

namespace Enlargement

variable {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
  {Λ : Cardinal.{max u v r w}} {P : EnlargementProperty.{w} O F}

/-- An existential one-step enlargement statement, read as a function on bounded subcomplexes. -/
def ofExists
    (hstep : ∀ (G₁ : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g₁ : G₁ ⟶ F),
      Mono g₁ → complexSectionSize.{w} O G₁ ≤ Λ →
      ∃ (G₂ : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g₂ : G₂ ⟶ F)
        (p : G₁ ⟶ G₂), Mono g₂ ∧ p ≫ g₂ = g₁ ∧ complexSectionSize.{w} O G₂ ≤ Λ ∧
          P G₁ g₁ G₂ g₂ p)
    (B : BoundedSubcomplex.{w} O F Λ) : Enlargement.{w} P B := by
  refine Classical.choice ?_
  obtain ⟨G₂, g₂, p, hg₂, hp, hsize, hprop⟩ := hstep B.H B.inc B.mono_inc B.size_le
  exact ⟨⟨G₂, g₂, hg₂, hsize⟩, p, hp, hprop⟩

end Enlargement

section Iteration

variable {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
  {Λ : Cardinal.{max u v r w}} {P : EnlargementProperty.{w} O F}

/-- The stages of the iteration of a one-step enlargement, starting from a given bounded
subcomplex. -/
def enlargementSequence (step : ∀ B : BoundedSubcomplex.{w} O F Λ, Enlargement.{w} P B)
    (B₀ : BoundedSubcomplex.{w} O F Λ) : ℕ → BoundedSubcomplex.{w} O F Λ
  | 0 => B₀
  | n + 1 => (step (enlargementSequence step B₀ n)).next

/-- The inclusion of one stage of the iteration into the next. -/
def enlargementSequenceMap (step : ∀ B : BoundedSubcomplex.{w} O F Λ, Enlargement.{w} P B)
    (B₀ : BoundedSubcomplex.{w} O F Λ) (n : ℕ) :
    (enlargementSequence.{w} step B₀ n).H ⟶ (enlargementSequence.{w} step B₀ (n + 1)).H :=
  (step (enlargementSequence.{w} step B₀ n)).map

/-- The inclusions of the stages of the iteration into `F` are compatible. -/
lemma enlargementSequenceMap_factor
    (step : ∀ B : BoundedSubcomplex.{w} O F Λ, Enlargement.{w} P B)
    (B₀ : BoundedSubcomplex.{w} O F Λ) (n : ℕ) :
    enlargementSequenceMap.{w} step B₀ n ≫ (enlargementSequence.{w} step B₀ (n + 1)).inc =
      (enlargementSequence.{w} step B₀ n).inc :=
  (step (enlargementSequence.{w} step B₀ n)).factor

/-- Each stage of the iteration has the prescribed property relative to the next. -/
lemma enlargementSequence_prop
    (step : ∀ B : BoundedSubcomplex.{w} O F Λ, Enlargement.{w} P B)
    (B₀ : BoundedSubcomplex.{w} O F Λ) (n : ℕ) :
    P (enlargementSequence.{w} step B₀ n).H (enlargementSequence.{w} step B₀ n).inc
      (enlargementSequence.{w} step B₀ (n + 1)).H
      (enlargementSequence.{w} step B₀ (n + 1)).inc
      (enlargementSequenceMap.{w} step B₀ n) :=
  (step (enlargementSequence.{w} step B₀ n)).prop

/-- Let `F^•` be a complex of
`O`-modules, let `Λ` be an infinite cardinal, and suppose every subcomplex of `F^•` with at most
`Λ` sections admits a one-step enlargement with the property `P`, again with at most `Λ`
sections. Then every subcomplex `S^• ⊆ F^•` with at most `Λ` sections is contained in a
subcomplex `H^• ⊆ F^•` with at most `Λ` sections which is the union of a chain of stages
`S^• = G_0^• ⊆ G_1^• ⊆ ⋯ ⊆ H^•`, where `P` holds of each consecutive pair of stages, each stage
includes into `F^•` by a monomorphism, and every section of `H^•` comes from a stage. -/
theorem exists_union_of_iterated_enlargement (hΛ : Cardinal.aleph0 ≤ Λ)
    (step : ∀ B : BoundedSubcomplex.{w} O F Λ, Enlargement.{w} P B)
    (S : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : S ⟶ F) (hg : Mono g)
    (hS : complexSectionSize.{w} O S ≤ Λ) :
    ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F) (kS : S ⟶ H)
      (G : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (γ : ∀ n, G n ⟶ F)
      (p : ∀ n, G n ⟶ G (n + 1)) (k : ∀ n, G n ⟶ H),
      G 0 = S ∧ Mono h ∧ kS ≫ h = g ∧ complexSectionSize.{w} O H ≤ Λ ∧
        (∀ n, Mono (γ n)) ∧
        (∀ n, p n ≫ γ (n + 1) = γ n) ∧ (∀ n, k n ≫ h = γ n) ∧
        (∀ n, P (G n) (γ n) (G (n + 1)) (γ (n + 1)) (p n)) ∧
        (∀ (i : ℤ) (X : Cᵒᵖ) (x : (H.X i).obj X),
          ∃ (n : ℕ) (y : ((G n).X i).obj X), ((k n).f i).app X y = x) := by
  classical
  let B₀ : BoundedSubcomplex.{w} O F Λ := ⟨S, g, hg, hS⟩
  let B : ℕ → BoundedSubcomplex.{w} O F Λ := enlargementSequence.{w} step B₀
  obtain ⟨H, h, k, hmono, hk, hsizeH, hexh⟩ :=
    exists_union_of_chain.{w} (G := fun n => (B n).H) (fun n => (B n).inc)
      (q := enlargementSequenceMap.{w} step B₀)
      (enlargementSequenceMap_factor.{w} step B₀) hΛ (fun n => (B n).size_le)
  exact ⟨H, h, k 0, fun n => (B n).H, fun n => (B n).inc,
    enlargementSequenceMap.{w} step B₀, k, rfl, hmono, hk 0, hsizeH,
    fun n => (B n).mono_inc,
    enlargementSequenceMap_factor.{w} step B₀, hk,
    enlargementSequence_prop.{w} step B₀, hexh⟩

end Iteration

/-! ### Iterated enlargements containing prescribed sections -/

section SectionRule

variable (O)

/-- There is a cardinal `κ₀`, depending only on the
category and its presheaf of rings, with the following property. Let `F^•` be a complex of
`O`-modules, let `Λ` be an infinite cardinal at least `κ₀`, and let there be given a rule
assigning to every subcomplex `G^• ⊆ F^•` a family `Ω(G^•)` of sections of `F^•`, of at most `Λ`
of them whenever `G^•` itself has at most `Λ` sections.
Then every subcomplex `S^• ⊆ F^•` with at most `Λ` sections is contained in a subcomplex
`H^• ⊆ F^•` with at most `Λ` sections which is the union of a chain of stages
`S^• = G_0^• ⊆ G_1^• ⊆ ⋯`, where `G_{n+1}^•` contains every section of `Ω(G_n^•)`, each stage
includes into `F^•` by a monomorphism, and every section of `H^•` comes from a stage. The
cardinal `κ₀` is the one of Stacks 0GYX (`exists_enlargement_containing_sections`). -/
theorem exists_iterated_enlargement_containing_sections :
    ∃ kappa : Cardinal.{max u v r w},
      ∀ (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
        {Λ : Cardinal.{max u v r w}}, max Cardinal.aleph0 kappa ≤ Λ →
        ∀ Omega : ∀ G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ, (G ⟶ F) →
            ∀ (i : ℤ) (U : C), Set ((F.X i).obj (op U)),
          (∀ (G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : G ⟶ F),
            complexSectionSize.{w} O G ≤ Λ → presheafSectionFamilySize.{w} (Omega G g) ≤ Λ) →
          ∀ (S : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : S ⟶ F), Mono g →
            complexSectionSize.{w} O S ≤ Λ →
            ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F)
              (kS : S ⟶ H) (G : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
              (γ : ∀ n, G n ⟶ F) (p : ∀ n, G n ⟶ G (n + 1)) (k : ∀ n, G n ⟶ H),
              G 0 = S ∧ Mono h ∧ kS ≫ h = g ∧ complexSectionSize.{w} O H ≤ Λ ∧
                (∀ n, Mono (γ n)) ∧
                (∀ n, p n ≫ γ (n + 1) = γ n) ∧ (∀ n, k n ≫ h = γ n) ∧
                (∀ (n : ℕ) (i : ℤ) (U : C) (x : (F.X i).obj (op U)),
                  x ∈ Omega (G n) (γ n) i U →
                    ∃ y : ((G (n + 1)).X i).obj (op U), ((γ (n + 1)).f i).app (op U) y = x) ∧
                (∀ (i : ℤ) (X : Cᵒᵖ) (x : (H.X i).obj X),
                  ∃ (n : ℕ) (y : ((G n).X i).obj X), ((k n).f i).app X y = x) := by
  classical
  obtain ⟨kappa, hkappa⟩ := exists_enlargement_containing_sections.{w} O
  refine ⟨kappa, fun F Λ hΛ Omega hOmega S g hg hS => ?_⟩
  have hℵ : Cardinal.aleph0 ≤ Λ := (le_max_left _ _).trans hΛ
  have hκ : kappa ≤ Λ := (le_max_right _ _).trans hΛ
  set P : EnlargementProperty.{w} O F := fun G₁ g₁ _ g₂ _ =>
    ∀ (i : ℤ) (U : C) (x : (F.X i).obj (op U)), x ∈ Omega G₁ g₁ i U →
      ∃ y, (g₂.f i).app (op U) y = x
  have hstep : ∀ (G₁ : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g₁ : G₁ ⟶ F),
      Mono g₁ → complexSectionSize.{w} O G₁ ≤ Λ →
      ∃ (G₂ : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g₂ : G₂ ⟶ F)
        (q : G₁ ⟶ G₂), Mono g₂ ∧ q ≫ g₂ = g₁ ∧ complexSectionSize.{w} O G₂ ≤ Λ ∧
          P G₁ g₁ G₂ g₂ q := by
    intro G₁ g₁ _ hsize
    obtain ⟨G₂, g₂, q, hg₂, hq, hcontain, hsize₂⟩ := hkappa F G₁ g₁ (Omega G₁ g₁)
    exact ⟨G₂, g₂, q, hg₂, hq,
      hsize₂.trans (max_le hκ (max_le hsize (hOmega G₁ g₁ hsize))), hcontain⟩
  exact exists_union_of_iterated_enlargement.{w} (P := P) hℵ (Enlargement.ofExists.{w} hstep)
    S g hg hS

end SectionRule

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
