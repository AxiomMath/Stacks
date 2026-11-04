module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.TruncatedTower
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# Truncated hypercoverings by objects in a prescribed collection

Let `C` be a site with fibre products given by a pretopology `J`, let `X : C` and let
`B ⊂ Ob(C)` be a collection of objects. A *hypercovering of `X` by objects of `B`* is a
hypercovering `K` of `X`, in the sense of Tag 01G5, such that every summand of every term
`K_n` of the simplicial semi-representable object `K` has its underlying object of `C` in `B`.
Tag 0DAV asserts that such a hypercovering exists for every `X`, as soon as `B` supplies a
covering of every object of `C` and a covering by objects of `B` stays a covering after one
more morphism out of an object of `B` is adjoined.

This file sets up the induction on the truncation level by which that is proved and carries out
every part of it except the simplicial half of the one-step extension. Concretely it supplies

* the *truncated* form of the coskeleton clause of a hypercovering, which is what an induction
  on the truncation level can propagate, together with the identification of the truncated
  clause with the untruncated one (`truncCoskUnit_eq`);
* the reduction of Tag 0DAV to a single one-step extension statement
  (`exists_hypercovering_of_objects_in_of_step`), with the base case discharged from the
  hypothesis that `B` covers every object; and
* the covering half of that one-step extension
  (`exists_isCoveringOver_objects_in`): given a morphism `v : V ⟶ W` of semi-representable
  objects over `X` with the summands of `V` in `B` and injective index map, the object `W`
  admits a covering by objects of `B` through which `v` factors. This is where both hypotheses
  on `B` are consumed, the second one exactly at the summands of `W` that `v` hits.

What remains of the one-step extension is the *simplicial* half: assembling that covering into
an `(M + 1)`-truncated simplicial object extending the given `M`-truncated one. See the
implementation notes.

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.truncCoskUnit`: for `n ≤ M`, the canonical
  morphism from an `M`-truncated simplicial object `Y` to the `M`-truncation of the `n`-th
  coskeleton of the `n`-truncation of `Y`. This is the truncated avatar of the unit of the
  truncation–coskeleton adjunction.
* `Stacks.CategoryTheory.Hypercovering.IsTruncatedHypercoveringOver`: the predicate that an
  `M`-truncated simplicial object of `SR(C, X)` is an `M`-truncated hypercovering of `X` all of
  whose summands lie in `B`.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.truncCoskUnit_eq` and
  `truncCoskUnit_app_eq_coskAdj_unit_app`: on the `M`-truncation of a genuine simplicial object
  `K`, the truncated canonical morphism is the `M`-truncation of the unit
  `K ⟶ cosk_n sk_n K`, hence agrees with it in degree `n + 1`. This is what makes the truncated
  coskeleton clause equivalent to the clause appearing in `IsHypercovering`.
* `Stacks.CategoryTheory.Hypercovering.isCoveringOver_sigma`: a family of covering families of
  the summands of `W`, one for each index, assembles into a covering morphism of
  semi-representable objects over `X`.
* `Stacks.CategoryTheory.Hypercovering.exists_ofArrows_sum_mem`: the two hypotheses on `B`
  packaged — a covering family of `P` by objects of `B` can be chosen so that it remains a
  covering family after adjoining a prescribed subsingleton-indexed family of morphisms out of
  objects of `B`.
* `Stacks.CategoryTheory.Hypercovering.exists_isCoveringOver_objects_in`: the covering half of
  the one-step extension, as described above.
* `Stacks.CategoryTheory.Hypercovering.isCoveringOver_terminal_of_hom_mem`: the unique morphism
  from a semi-representable object `Z` to the terminal object of `SR(C, X)` is covering as soon
  as the family of structure morphisms of the summands of `Z` is a covering family of `X`.
* `Stacks.CategoryTheory.Hypercovering.exists_isTruncatedHypercoveringOver_zero`: a covering of
  `X` by objects of `B` is a `0`-truncated hypercovering of `X` by objects of `B`.
* `Stacks.CategoryTheory.Hypercovering.exists_hypercovering_of_objects_in_of_step`: Tag 0DAV
  granted the one-step extension of truncated hypercoverings by objects of `B`.

## Implementation notes

The induction is run through the *strict* tower
`CategoryTheory.SimplicialObject.TruncatedTower.exists_simplicialObject_of_step` rather than
through its isomorphism-compatible variant. This is forced, not a preference: `B` is an
arbitrary subset of `Ob(C)` and is therefore *not* assumed closed under isomorphism, so the
clause "every summand of `Y` lies in `B`" is not invariant under an isomorphism of truncated
simplicial objects, and the isomorphism-compatible induction principle cannot carry it. Running
the isomorphism-compatible variant would require either replacing `∈ B` by "isomorphic in
`C/X` to an object of `B`" — a weaker conclusion than Tag 0DAV states — or an extra transport
of the resulting simplicial object along degreewise isomorphisms. The strict tower avoids both.

`truncCoskUnit` is obtained from the universal property of `sk_M cosk_n U` as a right Kan
extension of `U` along the inclusion of truncated simplex categories. The restriction of a
pointwise right Kan extension along a composite, and that universal property itself, are
reproved here rather than reused: the corresponding statements in
`StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal` are `private`. Everything is stated
at a free index universe `w` for the formal coproducts and at `C : Type u` with
`[Category.{v} C]`; no universe is narrowed.

**What is missing.** `exists_hypercovering_of_objects_in_of_step` takes as a hypothesis the
one-step extension: every `M`-truncated hypercovering of `X` by objects of `B` extends to an
`(M + 1)`-truncated one. Its covering half is `exists_isCoveringOver_objects_in`, proved here,
and that is where the second hypothesis on `B` is consumed — at the *degenerate* summands of
`K_{M + 1} ⟶ (cosk_M sk_M K)_{M + 1}`, where a covering by objects of `B` has to be enlarged by
one more object of `B` and must stay a covering. What is not done is the simplicial half:
turning the resulting covering into an `(M + 1)`-truncated simplicial object restricting to the
given `M`-truncated one. The source constructs that by hand from explicit splitting data and
calls its compatibilities "straightforward but cumbersome"; in Lean it needs a one-step
extension constructor for truncated simplicial objects from faces and degeneracies subject to
the simplicial identities, which neither Mathlib nor this library has — the existing one-step
extension `exists_isRightKanExtension_of_matchingFamily` (Tag 0187) builds the *coskeleton*,
whose degree-`M + 1` term is not free to choose. Accordingly no declaration here carries the
tag `0DAV`.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 0187](https://stacks.math.columbia.edu/tag/0187)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject

namespace CategoryTheory.SimplicialObject.Truncated

section Restrict

variable {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]

/-- If `L₂` is fully faithful and `Z` is a right Kan extension of `F` along `L₁ ⋙ L₂`, then
`L₂ ⋙ Z` is a right Kan extension of `F` along `L₁`, with the same structure map. -/
theorem isRightKanExtension_restrict_comp (L₁ : A ⥤ B) (L₂ : B ⥤ D) [L₂.Full] [L₂.Faithful]
    {F : A ⥤ H} (Z : D ⥤ H) (α : (L₁ ⋙ L₂) ⋙ Z ⟶ F)
    [(L₁ ⋙ L₂).HasPointwiseRightKanExtension F] [Z.IsRightKanExtension α] :
    (L₂ ⋙ Z).IsRightKanExtension (L := L₁) α :=
  Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (E := Functor.RightExtension.mk (L := L₁) (L₂ ⋙ Z) α) fun Y ↦
      restrictIsPointwiseRightKanExtensionAt (Functor.RightExtension.mk Z α) Y
        (Functor.isPointwiseRightKanExtensionOfIsRightKanExtension Z α _)

end Restrict

variable {C : Type u} [Category.{v} C]
  [∀ (k : ℕ) (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]

/-- The inclusion `(Δ_{≤n} ⊆ Δ)ᵒᵖ` is the composite of `(Δ_{≤n} ⊆ Δ_{≤M})ᵒᵖ` and
`(Δ_{≤M} ⊆ Δ)ᵒᵖ`, so the coskeleton hypothesis at level `n` provides pointwise right Kan
extensions along that composite. -/
theorem hasPointwiseRightKanExtension_incl_comp {n M : ℕ} (h : n ≤ M)
    (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    ((SimplexCategory.Truncated.incl n M h).op ⋙
      (SimplexCategory.Truncated.inclusion M).op).HasPointwiseRightKanExtension F :=
  inferInstanceAs ((SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F)

/-- For `n ≤ M`, the `M`-truncation `sk_M cosk_n U` of the `n`-th coskeleton of an `n`-truncated
simplicial object `U` is a right Kan extension of `U` along the inclusion of truncated simplex
categories, with structure map the counit of `cosk_n`. -/
theorem isRightKanExtension_truncation_cosk {n M : ℕ} (h : n ≤ M)
    (U : SimplicialObject.Truncated C n) :
    ((Truncated.cosk n ⋙ truncation M).obj U).IsRightKanExtension
      (L := (SimplexCategory.Truncated.incl n M h).op) (F := U)
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U) :=
  have := hasPointwiseRightKanExtension_incl_comp (C := C) h U
  have : ((Truncated.cosk n).obj U).IsRightKanExtension
      (L := (SimplexCategory.Truncated.incl n M h).op ⋙
        (SimplexCategory.Truncated.inclusion M).op)
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U) :=
    inferInstanceAs ((((SimplexCategory.Truncated.inclusion n).op.ran).obj U).IsRightKanExtension
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U))
  isRightKanExtension_restrict_comp _ _ ((Truncated.cosk n).obj U) _

/-- For `n ≤ M`, the canonical morphism from an `M`-truncated simplicial object `Y` to the
`M`-truncation of the `n`-th coskeleton of the `n`-truncation of `Y`: the unique morphism whose
restriction to the `n`-truncated simplex category is the identity, read through the universal
property of `sk_M cosk_n` as a right Kan extension. -/
noncomputable def truncCoskUnit {n M : ℕ} (h : n ≤ M) (Y : SimplicialObject.Truncated C M) :
    Y ⟶ (Truncated.cosk n ⋙ truncation M).obj ((Truncated.trunc C M n h).obj Y) :=
  have := isRightKanExtension_truncation_cosk h ((Truncated.trunc C M n h).obj Y)
  Functor.liftOfIsRightKanExtension
    (L := (SimplexCategory.Truncated.incl n M h).op)
    (F := (Truncated.trunc C M n h).obj Y)
    ((Truncated.cosk n ⋙ truncation M).obj ((Truncated.trunc C M n h).obj Y))
    ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app _) Y (𝟙 _)

/-- On the `M`-truncation of a simplicial object `K`, the canonical morphism `truncCoskUnit` is
the `M`-truncation of the unit `K ⟶ cosk_n sk_n K` of the truncation–coskeleton adjunction. -/
theorem truncCoskUnit_eq {n M : ℕ} (h : n ≤ M) (K : SimplicialObject C) :
    truncCoskUnit h ((truncation M).obj K) = (truncation M).map ((coskAdj n).unit.app K) := by
  have hR := isRightKanExtension_truncation_cosk h
    ((Truncated.trunc C M n h).obj ((truncation M).obj K))
  have h₂ : Functor.whiskerLeft (SimplexCategory.Truncated.incl n M h).op
        ((truncation M).map ((coskAdj n).unit.app K)) ≫
      (SimplexCategory.Truncated.inclusion n).op.ranCounit.app
        ((Truncated.trunc C M n h).obj ((truncation M).obj K)) = 𝟙 _ := by
    ext a
    exact Functor.ranCounit_app_app_ranAdjunction_unit_app_app
      (SimplexCategory.Truncated.inclusion n).op K a
  exact Functor.hom_ext_of_isRightKanExtension _ _ _ _
    ((Functor.liftOfIsRightKanExtension_fac _ _ _ _).trans h₂.symm)

/-- In degree `n + 1`, the canonical morphism `truncCoskUnit` of the `M`-truncation of a
simplicial object `K` is the degree-`n + 1` component of the unit `K ⟶ cosk_n sk_n K`. -/
theorem truncCoskUnit_app_eq_coskAdj_unit_app {n M : ℕ} (h : n ≤ M) (hn : n + 1 ≤ M)
    (K : SimplicialObject C) :
    (truncCoskUnit h ((truncation M).obj K)).app (op ⟨⦋n + 1⦌, hn⟩) =
      ((coskAdj n).unit.app K).app (op ⦋n + 1⦌) :=
  congrArg (fun t ↦ NatTrans.app t (op ⟨⦋n + 1⦌, hn⟩)) (truncCoskUnit_eq h K)

end CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Two presieves that are equal are covering families together. -/
theorem mem_coverings_of_eq {J : Pretopology C} {P : C} {R S : Presieve P} (h : R = S)
    (hS : S ∈ J P) : R ∈ J P := h ▸ hS

/-- A family of covering families of the summands of `W`, one for each index, assembles into a
covering morphism of semi-representable objects over `X`: the source has index set the sigma
type of the chosen index sets, and its summand at `(i, k)` is the `k`-th member of the chosen
covering of the summand of `W` at `i`, viewed over `X`. -/
theorem isCoveringOver_sigma (J : Pretopology C) {X : C} (W : FormalCoproduct.{w} (Over X))
    (κ : W.I → Type w) (D : ∀ i, κ i → C) (d : ∀ i k, D i k ⟶ (W.obj i).left)
    (hJ : ∀ i, Presieve.ofArrows (D i) (d i) ∈ J (W.obj i).left) :
    IsCoveringOver J (⟨fun z ↦ z.1, fun z ↦ Over.homMk (d z.1 z.2)⟩ :
      (⟨Σ i : W.I, κ i, fun z ↦ Over.mk (d z.1 z.2 ≫ (W.obj z.1).hom)⟩ :
        FormalCoproduct.{w} (Over X)) ⟶ W) := by
  intro j
  refine mem_coverings_of_eq ?_ (hJ j)
  funext Y
  ext f
  constructor
  · rintro ⟨⟨⟨i, k⟩, rfl⟩⟩
    simpa using Presieve.ofArrows.mk k
  · rintro ⟨k⟩
    exact Presieve.ofArrows.mk' (⟨⟨j, k⟩, rfl⟩ : { z : Σ i : W.I, κ i // z.1 = j }) rfl (by simp)

/-- **The two hypotheses on `B` of Tag 0DAV, packaged.** Given a family of morphisms `dr` into
`P` indexed by a subsingleton and with sources in `B`, there is a covering family of `P` by
objects of `B` which, taken together with that family, is still a covering family of `P`. The
first hypothesis on `B` supplies the covering family and the second one allows the at most one
extra morphism to be adjoined to it. -/
theorem exists_ofArrows_sum_mem (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (A : ι → C) (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) ∧ Presieve.ofArrows A a ∈ J U)
    (hadjoin : ∀ {ι : Type w} (A : ι → C) {U : C} (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) → Presieve.ofArrows A a ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ b : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows A a h ∨ Presieve.singleton b h) ∈ J U)
    {P : C} {κ : Type w} (hκ : Subsingleton κ) (D : κ → C) (dr : ∀ k, D k ⟶ P)
    (hD : ∀ k, D k ∈ B) :
    ∃ (ι : Type w) (A : ι → C) (a : ∀ i, A i ⟶ P), (∀ i, A i ∈ B) ∧
      Presieve.ofArrows (Sum.elim A D)
        (fun z ↦ match z with | .inl i => a i | .inr k => dr k) ∈ J P := by
  obtain ⟨ι, A, a, hAB, hAJ⟩ := hcover P
  refine ⟨ι, A, a, hAB, mem_coverings_of_eq ?_ (?_ : (fun {_} h ↦ Presieve.ofArrows A a h ∨
    Presieve.ofArrows D dr h) ∈ J P)⟩
  · funext Y
    ext f
    constructor
    · rintro ⟨i | k⟩ <;> simp [Presieve.ofArrows.mk]
    · rintro (⟨⟨i⟩⟩ | ⟨⟨k⟩⟩)
      exacts [Presieve.ofArrows.mk (Sum.inl i), Presieve.ofArrows.mk (Sum.inr k)]
  · rcases isEmpty_or_nonempty κ with _ | ⟨⟨k₀⟩⟩
    · simpa [Presieve.ofArrows_of_isEmpty] using hAJ
    · have := uniqueOfSubsingleton k₀
      simpa [Presieve.ofArrows_of_unique] using hadjoin A a hAB hAJ (hD default) (dr default)

/-- **The covering half of the one-step extension of Tag 0DAV.** Let `v : V ⟶ W` be a morphism
of semi-representable objects over `X` whose summands on the source lie in `B` and whose index
map is injective. Then `W` admits a covering `u : Z ⟶ W` with all summands of `Z` in `B` through
which `v` factors. Both hypotheses on `B` are used: the first covers each summand of `W` by
objects of `B`, the second adjoins to that covering the at most one component of `v` lying over
the summand. In the induction of Tag 0DAV, `W` is the matching object
`(cosk_M sk_M K)_{M + 1}`, `V` is the degenerate part of degree `M + 1` and `v` carries the
degeneracies, so the factorization through `u` is what supplies them. -/
theorem exists_isCoveringOver_objects_in (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (A : ι → C) (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) ∧ Presieve.ofArrows A a ∈ J U)
    (hadjoin : ∀ {ι : Type w} (A : ι → C) {U : C} (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) → Presieve.ofArrows A a ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ b : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows A a h ∨ Presieve.singleton b h) ∈ J U)
    {X : C} (W V : FormalCoproduct.{w} (Over X)) (hV : ∀ k, (V.obj k).left ∈ B)
    (v : V ⟶ W) (hv : Function.Injective v.f) :
    ∃ (Z : FormalCoproduct.{w} (Over X)) (u : Z ⟶ W) (s : V ⟶ Z),
      (∀ k, (Z.obj k).left ∈ B) ∧ IsCoveringOver J u ∧ s ≫ u = v := by
  have hsub : ∀ i : W.I, Subsingleton { k : V.I // v.f k = i } :=
    fun i ↦ ⟨fun k k' ↦ Subtype.ext (hv (k.2.trans k'.2.symm))⟩
  choose ι A a hAB hAJ using fun i : W.I ↦
    exists_ofArrows_sum_mem J B hcover hadjoin (hsub i)
      (fun k : { k : V.I // v.f k = i } ↦ (V.obj k.1).left)
      (fun k ↦ (v.φ k.1).left ≫ eqToHom (congrArg (fun m ↦ (W.obj m).left) k.2))
      (fun k ↦ hV k.1)
  have hcov := isCoveringOver_sigma J W (fun i ↦ ι i ⊕ { k : V.I // v.f k = i })
    (fun i ↦ Sum.elim (A i) (fun k : { k : V.I // v.f k = i } ↦ (V.obj k.1).left)) _ hAJ
  refine ⟨_, _, ?_, ?_, hcov, ?_⟩
  · exact ⟨fun k ↦ ⟨v.f k, Sum.inr ⟨k, rfl⟩⟩, fun k ↦ Over.homMk (𝟙 _) (by simp)⟩
  · rintro ⟨i, m | k⟩
    exacts [hAB i m, hV k.1]
  · refine FormalCoproduct.hom_ext rfl (fun k ↦ ?_)
    ext
    simp only [Sum.elim_inr, eqToHom_refl, FormalCoproduct.category_comp_f,
      FormalCoproduct.category_comp_φ, Category.comp_id, Over.comp_left, Over.mk_left,
      Over.homMk_left]
    exact Category.id_comp _

/-- The unique morphism from a semi-representable object `Z` over `X` to the terminal object of
`SR(C, X)` is covering as soon as the structure morphisms of the summands of `Z` form a covering
family of `X`. -/
theorem isCoveringOver_terminal_of_hom_mem (J : Pretopology C) {X : C}
    (Z : FormalCoproduct.{w} (Over X))
    (hZ : Presieve.ofArrows (fun i : Z.I ↦ (Z.obj i).left) (fun i ↦ (Z.obj i).hom) ∈ J X) :
    IsCoveringOver J (terminal.from Z) := by
  let T : FormalCoproduct.{w} (Over X) := ⟨PUnit.{w + 1}, fun _ ↦ Over.mk (𝟙 X)⟩
  have hT : IsTerminal T := FormalCoproduct.isTerminalIncl (Over.mk (𝟙 X)) Over.mkIdTerminal
  let g : Z ⟶ T := { f := fun _ ↦ PUnit.unit, φ := fun i ↦ Over.homMk (Z.obj i).hom }
  have hg : IsCoveringOver J g := fun j ↦ by
    simp only [eqToHom_refl, Category.comp_id]
    exact ofArrows_reindex (Equiv.subtypeUnivEquiv fun _ ↦ Subsingleton.elim _ j)
      (fun i : Z.I ↦ (Z.obj i).left) (fun i ↦ (Z.obj i).hom) ▸ hZ
  rw [terminal.hom_ext (terminal.from Z) (g ≫ (hT.uniqueUpToIso terminalIsTerminal).hom)]
  exact hg.comp_isIso J _

variable (J : Pretopology C) (B : Set C)

/-- An `M`-truncated hypercovering of `X` by objects of `B`: an `M`-truncated simplicial object
of `SR(C, X)` all of whose summands lie in `B`, whose degree-zero term covers `X`, and whose
canonical morphism to the `n`-th coskeleton of its `n`-truncation is covering in degree `n + 1`
for every `n` with `n + 1 ≤ M`. This is the truncated notion the source inducts over. -/
def IsTruncatedHypercoveringOver {X : C} (M : ℕ)
    (Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M) : Prop :=
  (∀ (a : (SimplexCategory.Truncated M)ᵒᵖ) (i : (Y.obj a).I), ((Y.obj a).obj i).left ∈ B) ∧
    IsCoveringOver J (terminal.from (Y.obj (op ⟨⦋0⦌, Nat.zero_le M⟩))) ∧
      ∀ (n : ℕ) (hn : n + 1 ≤ M),
        IsCoveringOver J
          ((Truncated.truncCoskUnit (Nat.le_of_succ_le hn) Y).app (op ⟨⦋n + 1⦌, hn⟩))

/-- A covering of `X` by objects of `B` is a `0`-truncated hypercovering of `X` by objects of
`B`: take the constant `0`-truncated simplicial object on the corresponding semi-representable
object. -/
theorem exists_isTruncatedHypercoveringOver_zero {X : C} {ι : Type w} (V : ι → C)
    (f : ∀ i, V i ⟶ X) (hV : ∀ i, V i ∈ B) (hf : Presieve.ofArrows V f ∈ J X) :
    ∃ Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) 0,
      IsTruncatedHypercoveringOver.{w} J B 0 Y :=
  ⟨(Functor.const _).obj ⟨ι, fun i ↦ Over.mk (f i)⟩,
    fun _ i ↦ hV i, isCoveringOver_terminal_of_hom_mem J _ hf, fun _ hn ↦ by omega⟩

/-- **Stacks Project, Tag 0DAV**, granted the one-step extension of truncated hypercoverings.
If the objects of `B` cover every object of the site, and if every `M`-truncated hypercovering
of `X` by objects of `B` extends to an `(M + 1)`-truncated one, then `X` admits a hypercovering
all of whose summands lie in `B`. The one-step extension is exactly the part of the source's
proof that consumes its second hypothesis on `B`, and it is not proved here. -/
theorem exists_hypercovering_of_objects_in_of_step
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (X : C)
    (step : ∀ (M : ℕ) (Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M),
      IsTruncatedHypercoveringOver.{w} J B M Y →
      ∃ Z : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) (M + 1),
        (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} (Over X)) (M + 1) M).obj Z = Y ∧
          IsTruncatedHypercoveringOver.{w} J B (M + 1) Z) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering J K ∧
        ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), ((K.obj (op ⦋n⦌)).obj i).left ∈ B := by
  obtain ⟨ι, V, f, hV, hf⟩ := hcover X
  obtain ⟨Y₀, hY₀⟩ := exists_isTruncatedHypercoveringOver_zero J B V f hV hf
  obtain ⟨K, hK⟩ := SimplicialObject.TruncatedTower.exists_simplicialObject_of_step
    (P := IsTruncatedHypercoveringOver.{w} J B) Y₀ hY₀ step
  refine ⟨K, ⟨(hK 0).2.1, fun n ↦ ?_⟩, fun n i ↦ (hK n).1 (op ⟨⦋n⦌, le_rfl⟩) i⟩
  have h := (hK (n + 1)).2.2 n le_rfl
  rwa [Truncated.truncCoskUnit_app_eq_coskAdj_unit_app] at h

end Stacks.CategoryTheory.Hypercovering

end
