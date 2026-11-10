module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan

/-!
# Criteria for the section projections of an affine presentation

McQuillan's criterion for an affine formal algebraic space `X`, condition (4) of Stacks 0AIC,
asks for a presentation `X = colim Xᵢ` by affine thickenings whose section projections
`lim Γ(Xⱼ, 𝒪) → Γ(Xᵢ, 𝒪)` are all surjective; in this library that condition is
`AlgebraicGeometry.FormalSpace.HasSurjectiveSectionProjections`. This file isolates the two
reasons the discussion of Stacks 0CBE gives for a presentation to satisfy, respectively to
fail, that condition.

*The projections are surjective* as soon as one fixed set surjects compatibly onto every
stage ring — in the situation of Stacks 0CBE the target of the morphism is `Spf(lim Λ/Jᵢ)`,
whose stage rings are the quotients `Λ/Jᵢ` of a single ring `Λ`, so the surjections
`Λ → Λ/Jᵢ` form such a family and the target is McQuillan for this reason alone.

*The projections are not surjective* as soon as the stage rings surject compatibly onto an
inverse system whose own limit projections are not surjective — in the situation of Stacks
0CBE the source of the morphism has stage rings `Λ/Jᵢ ⊕ Mᵢ` surjecting onto the vector spaces
`Vᵢ` of a directed inverse system with surjective transition maps and vanishing limit, so the
source fails McQuillan's criterion for this reason alone.

The second hypothesis is not empty: Waterhouse's system of injections of the finite subsets
of an uncountable set into `ℕ`, which is the system underlying the vector spaces `Vᵢ` above,
is built here and shown to have surjective transition maps, nonempty stages and no sections
at all, so none of its limit projections is surjective.

Both criteria are used in the proof of the lemma of Stacks 0CBE, the *existence* of a
representable morphism `f : X ⟶ Y` of affine formal algebraic spaces with `Y` McQuillan and `X`
not, in `StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverMcQuillan`.

## Main definitions

* `Stacks.EmptyLimit.FiniteSubset` and `Stacks.EmptyLimit.restrict`: the finite subsets of a
  type, ordered by inclusion, and restriction of an injection into `ℕ` along an inclusion.
* `Stacks.EmptyLimit.system`: Waterhouse's inverse system of those injections.

The two conditions the criteria are about, `AlgebraicGeometry.FormalSpace.sectionDiagram` and
`AlgebraicGeometry.FormalSpace.HasSurjectiveSectionProjections`, are already in
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan` and are not restated.

## Main results

* `CategoryTheory.Functor.surjective_sections_eval_of_surjective_family`: a functor to `Type`
  receiving compatible surjections from one fixed type has surjective evaluation maps on its
  sections.
* `CategoryTheory.Functor.surjective_sections_eval_of_natTrans` and
  `CategoryTheory.Functor.not_surjective_sections_eval_of_natTrans`: surjectivity of an
  evaluation map on sections passes along a componentwise surjective natural transformation,
  hence non-surjectivity passes back along one.
* `CategoryTheory.Functor.not_surjective_sections_eval_of_subsingleton_sections`: a functor
  with at most one section and a stage with at least two elements has a non-surjective
  evaluation map; this is how a vanishing inverse limit obstructs its projections.
* `Stacks.EmptyLimit.surjective_restrict`, `Stacks.EmptyLimit.nonempty_obj_system` and
  `Stacks.EmptyLimit.isEmpty_sections_system`: Waterhouse's system has surjective transition
  maps and nonempty stages but no sections, whence
  `Stacks.EmptyLimit.not_surjective_sections_eval_system`.
* `AlgebraicGeometry.FormalSpace.hasSurjectiveSectionProjections_of_surjective_family`:
  a presentation whose stage rings receive compatible surjections from one fixed set has
  surjective section projections.
* `AlgebraicGeometry.FormalSpace.not_hasSurjectiveSectionProjections_of_natTrans`: a
  presentation whose stage rings surject compatibly onto an inverse system with a
  non-surjective limit projection has a non-surjective section projection.

## Implementation notes

The inverse limit of the section rings is presented, as in
`AlgebraicGeometry.FormalSpace.HasSurjectiveSectionProjections` itself, by
`CategoryTheory.Functor.sections` of the section diagram composed with the forgetful functor,
so the statements are about a functor to `Type` and no `HasLimit` instance is needed. The
surjecting object of the first criterion is therefore a bare type and the surjections bare
functions: a ring `Λ` with surjections `Λ → Γ(Xᵢ, 𝒪)` is one instance of the hypothesis, and
nothing in the argument uses the ring structure, since a section is produced by pushing a
single preimage forward to every stage.

The second criterion is the contrapositive of the first transfer lemma and is stated for an
arbitrary target functor to `Type`, not for a system of vector spaces: the surjection from a
stage ring onto its `Vᵢ` is additive in the intended application but only its surjectivity is
used, and the system `(Vᵢ)` of Stacks 0CBE is not constructed here.

Waterhouse's system is indexed by the subtype of finite sets rather than by `Finset`, so that
no `DecidableEq` assumption is needed on the ambient type, and its stages are
`Function.Embedding`s rather than subtypes of functions, which is what makes restriction
definitionally associative. Surjectivity of restriction extends a given injection by sending
the new points past an upper bound for its image, which exists because the subsets are finite.

The ring theory of the stage rings `Λ/Jᵢ ⊕ Mᵢ` of a system `Φ` — their transition
morphisms, and the identity `Rⱼ = Rᵢ ⊗_{Λ/Jᵢ} Λ/Jⱼ` that makes the morphism representable — is
in `StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanRepresentableSystem`.

## References

* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

universe w v v'

variable {K : Type v} [Category.{v'} K]

/-- A functor to `Type` which receives compatible surjections from one fixed type has
surjective evaluation maps on sections: a preimage of the given element at the chosen stage is
pushed forward to a section by the given family. -/
theorem surjective_sections_eval_of_surjective_family {F : K ⥤ Type w} {X : Type w}
    (π : ∀ k : K, X → F.obj k)
    (hπ : ∀ ⦃k l : K⦄ (f : k ⟶ l) (x : X), F.map f (π k x) = π l x)
    (hsurj : ∀ k : K, Function.Surjective (π k)) (k₀ : K) :
    Function.Surjective fun s : F.sections ↦ s.1 k₀ := by
  intro y
  obtain ⟨x, hx⟩ := hsurj k₀ y
  exact ⟨⟨fun k ↦ π k x, fun {_ _} f ↦ hπ f x⟩, hx⟩

/-- Surjectivity of an evaluation map on sections passes along a natural transformation all of
whose components are surjective: the image of a section is a section, and a preimage of the
given element under the component at the chosen stage is lifted to a section of the source. -/
theorem surjective_sections_eval_of_natTrans {F G : K ⥤ Type w} (α : F ⟶ G)
    (hα : ∀ k : K, Function.Surjective (α.app k)) {k₀ : K}
    (hF : Function.Surjective fun s : F.sections ↦ s.1 k₀) :
    Function.Surjective fun s : G.sections ↦ s.1 k₀ := by
  intro y
  obtain ⟨x, hx⟩ := hα k₀ y
  obtain ⟨s, hs⟩ := hF x
  refine ⟨⟨fun k ↦ α.app k (s.1 k), fun {k l} f ↦ ?_⟩, (congrArg (α.app k₀) hs).trans hx⟩
  rw [← NatTrans.naturality_apply α f (s.1 k), s.2 f]

/-- Non-surjectivity of an evaluation map on sections passes back along a natural
transformation all of whose components are surjective. -/
theorem not_surjective_sections_eval_of_natTrans {F G : K ⥤ Type w} (α : F ⟶ G)
    (hα : ∀ k : K, Function.Surjective (α.app k)) {k₀ : K}
    (hG : ¬ Function.Surjective fun s : G.sections ↦ s.1 k₀) :
    ¬ Function.Surjective fun s : F.sections ↦ s.1 k₀ :=
  fun hF ↦ hG (surjective_sections_eval_of_natTrans α hα hF)

/-- A functor to `Type` with at most one section cannot evaluate onto a stage with more than
one element. This is how a vanishing inverse limit obstructs surjectivity of its projections.
-/
theorem not_surjective_sections_eval_of_subsingleton_sections {F : K ⥤ Type w} {k₀ : K}
    (hF : Subsingleton F.sections) (hk : ¬ Subsingleton (F.obj k₀)) :
    ¬ Function.Surjective fun s : F.sections ↦ s.1 k₀ := by
  intro h
  refine hk ⟨fun a b ↦ ?_⟩
  obtain ⟨s, hs⟩ := h a
  obtain ⟨t, ht⟩ := h b
  rw [← hs, ← ht, hF.elim s t]

end CategoryTheory.Functor

namespace Stacks.EmptyLimit

universe u

variable {α : Type u}

/-- The finite subsets of a type, ordered by inclusion. This is the index of Waterhouse's
inverse system with surjective transition maps and empty limit. -/
abbrev FiniteSubset (α : Type u) := {s : Set α // s.Finite}

/-- Restriction of an injection into `ℕ` along an inclusion of finite subsets. -/
def restrict {s t : FiniteSubset α} (h : s ≤ t) (e : t.val ↪ ℕ) : s.val ↪ ℕ :=
  ⟨fun a ↦ e ⟨a.val, h a.property⟩, fun _ _ hab ↦
    Subtype.ext (congrArg (fun a : t.val ↦ a.val) (e.injective hab))⟩

/-- Restriction is transitive: restricting twice is restricting along the composite
inclusion. This holds definitionally, which is what makes `Stacks.EmptyLimit.system` a
functor without any transport. -/
theorem restrict_comp {s t r : FiniteSubset α} (h : s ≤ t) (k : t ≤ r) (e : r.val ↪ ℕ) :
    restrict h (restrict k e) = restrict (h.trans k) e := rfl

/-- Restriction along an inclusion of finite subsets is surjective: an injection of a finite
subset into `ℕ` extends to any larger finite subset, using natural numbers beyond its image.
-/
theorem surjective_restrict {s t : FiniteSubset α} (h : s ≤ t) :
    Function.Surjective (restrict (α := α) h) := by
  classical
  intro e
  have hs : Finite s.val := s.property.to_subtype
  have ht : Finite t.val := t.property.to_subtype
  obtain ⟨M, hM⟩ := (Set.finite_range e).bddAbove
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat {a : t.val // a.val ∉ s.val}
  have hlt (x : s.val) : e x < M + 1 := Nat.lt_succ_of_le (hM (Set.mem_range_self x))
  refine ⟨⟨fun a ↦ if ha : a.val ∈ s.val then e ⟨a.val, ha⟩ else M + 1 + c ⟨a, ha⟩, ?_⟩, ?_⟩
  · intro a b hab
    by_cases ha : a.val ∈ s.val <;> by_cases hb : b.val ∈ s.val
    · simp only [dite_eq_left ha, dite_eq_left hb] at hab
      exact Subtype.ext (congrArg (fun x : s.val ↦ x.val) (e.injective hab))
    · simp only [dite_eq_left ha, dite_eq_right hb] at hab
      have := hlt ⟨a.val, ha⟩
      omega
    · simp only [dite_eq_right ha, dite_eq_left hb] at hab
      have := hlt ⟨b.val, hb⟩
      omega
    · simp only [dite_eq_right ha, dite_eq_right hb] at hab
      exact congrArg Subtype.val (hc (by omega : c ⟨a, ha⟩ = c ⟨b, hb⟩))
  · refine Function.Embedding.ext fun a ↦ ?_
    change (if ha : (a.val : α) ∈ s.val then _ else _) = e a
    rw [dite_eq_left a.property]

/-- There is no compatible family of injections of all finite subsets of an uncountable set
into `ℕ`: such a family would inject the whole set into `ℕ`. -/
theorem not_exists_compatible_restrict (α : Type u) [Uncountable α]
    (p : ∀ s : FiniteSubset α, s.val ↪ ℕ)
    (hp : ∀ (s t : FiniteSubset α) (h : s ≤ t), restrict h (p t) = p s) : False := by
  let sing (a : α) : FiniteSubset α := ⟨{a}, Set.finite_singleton a⟩
  have hpair (a b : α) :
      p (sing a) ⟨a, Set.mem_singleton a⟩ = p (sing b) ⟨b, Set.mem_singleton b⟩ → a = b := by
    intro hab
    let t : FiniteSubset α := ⟨{a, b}, Set.toFinite _⟩
    have hle (c : α) (hc : c ∈ t.val) :
        p t ⟨c, hc⟩ = p (sing c) ⟨c, rfl⟩ := by
      rw [← hp (sing c) t (Set.singleton_subset_iff.2 hc)]; rfl
    have heq := (hle a (.inl rfl)).trans (hab.trans (hle b (.inr rfl)).symm)
    exact congrArg Subtype.val ((p t).injective heq)
  exact not_countable (α := α) (Function.Injective.countable hpair)

/-- Waterhouse's inverse system: over a finite subset of `α` sit the injections of that subset
into `ℕ`, and the transition maps are restrictions. -/
def system (α : Type u) : (FiniteSubset α)ᵒᵖ ⥤ Type u where
  obj s := s.unop.val ↪ ℕ
  map f := ↾fun e ↦ restrict (leOfHom f.unop) e
  map_id _ := by ext e a; rfl
  map_comp _ _ := by ext e a; rfl

/-- A transition map of Waterhouse's system is restriction along the underlying inclusion. -/
@[simp]
theorem map_system_apply {j k : (FiniteSubset α)ᵒᵖ} (g : j ⟶ k) (e : (system α).obj j) :
    (system α).map g e = restrict (leOfHom g.unop) e := rfl

/-- Every stage of Waterhouse's system is nonempty: a finite set injects into `ℕ`. -/
theorem nonempty_obj_system (j : (FiniteSubset α)ᵒᵖ) : Nonempty ((system α).obj j) := by
  have : Countable j.unop.val := (j.unop.property.countable).to_subtype
  exact nonempty_embedding_nat _

/-- The transition maps of Waterhouse's system are surjective. -/
theorem surjective_map_system {j k : (FiniteSubset α)ᵒᵖ} (g : j ⟶ k) :
    Function.Surjective ((system α).map g) :=
  surjective_restrict (leOfHom g.unop)

/-- Waterhouse's system has no sections. -/
theorem isEmpty_sections_system (α : Type u) [Uncountable α] :
    IsEmpty (system α).sections :=
  ⟨fun q ↦ not_exists_compatible_restrict α (fun s ↦ q.1 (op s)) fun _ _ h ↦ q.2 (homOfLE h).op⟩

/-- **The hypothesis of `not_hasSurjectiveSectionProjections_of_natTrans` is satisfiable.**
Waterhouse's system has surjective transition maps and nonempty stages, yet no sections at
all, so none of its evaluation maps on sections is surjective. -/
theorem not_surjective_sections_eval_system (α : Type u) [Uncountable α]
    (j : (FiniteSubset α)ᵒᵖ) :
    ¬ Function.Surjective fun s : (system α).sections ↦ s.1 j := by
  intro h
  obtain ⟨e⟩ := nonempty_obj_system j
  obtain ⟨s, -⟩ := h e
  exact (isEmpty_sections_system α).elim s

end Stacks.EmptyLimit

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The McQuillan target of Stacks 0CBE.** A presentation of an affine formal algebraic space
by affine schemes whose rings of global sections receive compatible surjections from one fixed
set has all its section projections surjective, so it witnesses condition (4) of Stacks 0AIC.
In Stacks 0CBE the target of the morphism is the formal spectrum of `lim Λ/Jᵢ` and the fixed
set is `Λ`, whose quotient maps `Λ → Λ/Jᵢ` form the cone. -/
theorem hasSurjectiveSectionProjections_of_surjective_family {I : Type (u + 1)} [Category I]
    {D : I ⥤ BigAffineFppf B S hS} {Λ : Type u}
    (π : ∀ j : Iᵒᵖ, Λ → (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj j)
    (hπ : ∀ ⦃j k : Iᵒᵖ⦄ (g : j ⟶ k) (x : Λ),
      (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).map g (π j x) = π k x)
    (hsurj : ∀ j : Iᵒᵖ, Function.Surjective (π j)) :
    HasSurjectiveSectionProjections B S hS D :=
  fun i ↦ Functor.surjective_sections_eval_of_surjective_family π hπ hsurj (op i)

/-- **The non-McQuillan source of Stacks 0CBE.** A presentation of an affine formal algebraic
space by affine schemes whose rings of global sections surject compatibly onto an inverse
system one of whose limit projections is not surjective fails condition (4) of Stacks 0AIC at
the same stage. In Stacks 0CBE the source of the morphism has stage rings `Λ/Jᵢ ⊕ Mᵢ`
surjecting onto the modules `Mᵢ`, and those onto the vector spaces `Vᵢ` of a directed inverse
system with surjective transition maps and vanishing limit. -/
theorem not_hasSurjectiveSectionProjections_of_natTrans {I : Type (u + 1)} [Category I]
    {D : I ⥤ BigAffineFppf B S hS} {G : Iᵒᵖ ⥤ Type u}
    (α : sectionDiagram B S hS D ⋙ forget CommRingCat.{u} ⟶ G)
    (hα : ∀ j : Iᵒᵖ, Function.Surjective (α.app j)) {i₀ : I}
    (hG : ¬ Function.Surjective fun s : G.sections ↦ s.1 (op i₀)) :
    ¬ HasSurjectiveSectionProjections B S hS D :=
  fun h ↦ Functor.not_surjective_sections_eval_of_natTrans α hα hG (h i₀)

end AlgebraicGeometry.FormalSpace

end
