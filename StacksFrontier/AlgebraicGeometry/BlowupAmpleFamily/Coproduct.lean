module

public import StacksFrontier.AlgebraicGeometry.AmpleFamilyRelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AmpleFamilyCartier.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing

/-!
# Ample families of invertible modules on a disjoint union

If schemes `A` and `B` carry ample families of invertible modules and `A ⨿ B` is reduced, then
`A ⨿ B` carries an ample family of invertible modules. This is the step of the proof of
[Stacks, Tag 0GTU] in which the source of the morphism is assembled as a disjoint union.

## Main results

* `Stacks.BlowupAmpleFamily.isAmpleFamily_of_isEmpty`: the empty family is ample on the empty
  scheme.
* `Stacks.BlowupAmpleFamily.exists_glue`: invertible modules with global sections on the two
  summands of a reduced `A ⨿ B` glue to an invertible module with a global section whose
  nonvanishing locus meets each summand in the nonvanishing locus of the given section.
* `Stacks.BlowupAmpleFamily.exists_isAmpleFamily_coprod`: the statement above.

## The argument

Let `x` be a point of `A`. The ample family on `A` gives an invertible module `N` on `A` (a
tensor power of a member of the family) and a global section `s` of it whose nonvanishing locus
`V` is an affine open containing `x`. Glue `N` on `A` and the structure sheaf on `B` to an
invertible module `M` on `A ⨿ B`, together with the sections `s` and `0`; the nonvanishing locus
of the glued section `t` is then `V` on `A` and empty on `B`, so it is the image of `V`, an affine
open of `A ⨿ B` containing `x`. Points of `B` are treated symmetrically, and the family of all the
`M` so obtained, indexed by the points of `A ⨿ B`, is ample
(`Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_pointwise_affine_nonvanishing`), `A ⨿ B`
being quasi-compact.

## Implementation notes

The glueing is [Stacks, Tag 09NE] with prescribed sections,
`StacksTag09NE.exists_invertible_with_sections_of_closed_cover_discrete_intersections`, applied
to the closed cover of `A ⨿ B` by its two summands, whose pairwise intersections are empty. That
result is stated for a reduced scheme, which is why `A ⨿ B` is assumed reduced. The identification
of the nonvanishing locus of the glued section on each summand is [Stacks, Tag 0H78]
(`Stacks.NonvanishingPullback.preimage_nonvanishingLocus`) followed by invariance of the
nonvanishing locus under an isomorphism of modules (`Stacks.Ample.nonvanishingLocus_congr`).

The summands are indexed by `WalkingPair` through `CategoryTheory.Limits.pair`, so that
`summand A B .left` is `A` and `summandι A B .left` is `coprod.inl` by definition.

## References

* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0GTU](https://stacks.math.columbia.edu/tag/0GTU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u v w

namespace Stacks.BlowupAmpleFamily

/-- The empty scheme carries an ample family of invertible modules, the empty one. -/
theorem isAmpleFamily_of_isEmpty (Y : Scheme.{u}) [IsEmpty Y] :
    Y.IsAmpleFamily (fun i : PEmpty.{u + 1} => i.elim) :=
  ⟨fun i => i.elim, inferInstance, fun y => isEmptyElim y⟩

section Coprod

variable (A B : Scheme.{u})

/-- The first inclusion of a binary coproduct of schemes is a closed immersion. -/
theorem isClosedImmersion_inl : IsClosedImmersion (coprod.inl : A ⟶ A ⨿ B) :=
  .of_isPreimmersion _ <| (isCompl_range_inl_inr A B).eq_compl ▸
    (IsOpenImmersion.isOpen_range (coprod.inr : B ⟶ A ⨿ B)).isClosed_compl

/-- The second inclusion of a binary coproduct of schemes is a closed immersion. -/
theorem isClosedImmersion_inr : IsClosedImmersion (coprod.inr : B ⟶ A ⨿ B) :=
  .of_isPreimmersion _ <| (isCompl_range_inl_inr A B).symm.eq_compl ▸
    (IsOpenImmersion.isOpen_range (coprod.inl : A ⟶ A ⨿ B)).isClosed_compl

/-- The summands of `A ⨿ B`, indexed by `WalkingPair`. -/
abbrev summand (j : WalkingPair) : Scheme.{u} := (pair A B).obj ⟨j⟩

/-- The inclusion of a summand of `A ⨿ B`. -/
abbrev summandι (j : WalkingPair) : summand A B j ⟶ A ⨿ B := colimit.ι (pair A B) ⟨j⟩

/-- The inclusion of a summand of `A ⨿ B` is a closed immersion. -/
instance isClosedImmersion_summandι (j : WalkingPair) : IsClosedImmersion (summandι A B j) := by
  cases j
  · exact isClosedImmersion_inl A B
  · exact isClosedImmersion_inr A B

/-- Every point of `A ⨿ B` comes from one of the two summands. -/
theorem mem_range_inl_or_inr (y : (A ⨿ B : Scheme.{u})) :
    (∃ a : A, (coprod.inl : A ⟶ A ⨿ B) a = y) ∨ ∃ b : B, (coprod.inr : B ⟶ A ⨿ B) b = y := by
  have h : y ∈ (Set.range (coprod.inl : A ⟶ A ⨿ B) ⊔ Set.range (coprod.inr : B ⟶ A ⨿ B) :
      Set (A ⨿ B : Scheme.{u})) := by
    rw [(isCompl_range_inl_inr A B).sup_eq_top]; trivial
  exact h

/-- The nonvanishing locus of the zero global section is empty. -/
theorem nonvanishingSet_zero (X : Scheme.{u}) (M : X.Modules) :
    X.nonvanishingSet M (Stacks.SheafOfModules.sectionsOfTop M 0) = ∅ :=
  (Stacks.AmpleFamilyRelativeAmple.nonvanishingSet_sectionsOfTop M 0).trans
    (Stacks.Ample.nonvanishingLocus_zero M)

/-- **Glueing invertible modules and sections along the two summands of a reduced disjoint
union.** Invertible modules `L j` with global sections `s j` on the summands of a reduced
`A ⨿ B` glue to an invertible module `M` on `A ⨿ B` with a global section `t` whose nonvanishing
locus meets each summand in the nonvanishing locus of `s j`. -/
theorem exists_glue [IsReduced (A ⨿ B : Scheme.{u})] (L : ∀ j, (summand A B j).Modules)
    [hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (summand A B j).presheaf
      (summand A B j).ringCatSheaf.2 (L j)]
    (s : ∀ j, (L j).sections) :
    ∃ (M : (A ⨿ B : Scheme.{u}).Modules)
      (_ : Stacks.SheafOfModules.IsInvertible (A ⨿ B : Scheme.{u}).presheaf
        (A ⨿ B : Scheme.{u}).ringCatSheaf.2 M) (t : M.sections),
      ∀ j, summandι A B j ⁻¹' (A ⨿ B : Scheme.{u}).nonvanishingSet M t =
        (summand A B j).nonvanishingSet (L j) (s j) := by
  have hcover : ∀ y : (A ⨿ B : Scheme.{u}), ∃ j z, summandι A B j z = y := by
    intro y
    rcases mem_range_inl_or_inr A B y with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨.left, a, rfl⟩
    · exact ⟨.right, b, rfl⟩
  have hdisj : ∀ j k : WalkingPair, j ≠ k →
      Set.range (summandι A B j) ∩ Set.range (summandι A B k) = ∅ := by
    intro j k hjk
    cases j <;> cases k
    · exact absurd rfl hjk
    · exact (isCompl_range_inl_inr A B).inf_eq_bot
    · exact (isCompl_range_inl_inr A B).symm.inf_eq_bot
    · exact absurd rfl hjk
  obtain ⟨M, hM, t, ht⟩ :=
    StacksTag09NE.exists_invertible_with_sections_of_closed_cover_discrete_intersections
      (A ⨿ B : Scheme.{u}) (summand A B) (summandι A B) hcover L s
      (fun j k hjk z hz => absurd (show summandι A B j z ∈ (∅ : Set _) from
        hdisj j k hjk ▸ ⟨⟨z, rfl⟩, hz⟩) id)
  refine ⟨M, (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr hM, t,
    fun j => ?_⟩
  obtain ⟨e, he⟩ := ht j
  rw [Stacks.AmpleFamilyRelativeAmple.nonvanishingSet_eq_nonvanishingLocus,
    Stacks.AmpleFamilyRelativeAmple.nonvanishingSet_eq_nonvanishingLocus]
  have h1 := Stacks.NonvanishingPullback.preimage_nonvanishingLocus (summandι A B j) M
    (t.eval (op ⊤))
  have h2 := Stacks.Ample.nonvanishingLocus_congr e
    (Stacks.NonvanishingPullback.pullbackGlobalSection (summandι A B j) M (t.eval (op ⊤)))
  refine h1.trans (h2.symm.trans ?_)
  exact congrArg _ he

/-- If two maps cover `X` with disjoint ranges and `f` is injective, a subset of `X` meeting the
image of `g` in nothing and pulling back to `V` along `f` is the image of `V`. -/
private theorem eq_image_of_preimage_eq {X P Q : Type*} (f : P → X) (g : Q → X)
    (hf : Function.Injective f) (hfg : ∀ p q, f p ≠ g q) (hcov : ∀ y, (∃ p, f p = y) ∨ ∃ q, g q = y)
    (S : Set X) (V : Set P) (hl : f ⁻¹' S = V) (hr : g ⁻¹' S = ∅) : S = f '' V := by
  ext y
  rcases hcov y with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · rw [hf.mem_set_image, ← hl]
    rfl
  · exact iff_of_false (fun h => hr.subset h) (by rintro ⟨p, -, hp⟩; exact hfg p q hp)

/-- A subset of `A ⨿ B` meeting the first summand in `V` and the second not at all is the image
of `V`. -/
theorem eq_image_inl_of_preimage (S : Set (A ⨿ B : Scheme.{u})) (V : Set A)
    (hl : (coprod.inl : A ⟶ A ⨿ B) ⁻¹' S = V) (hr : (coprod.inr : B ⟶ A ⨿ B) ⁻¹' S = ∅) :
    S = (coprod.inl : A ⟶ A ⨿ B) '' V :=
  eq_image_of_preimage_eq _ (⇑(coprod.inr : B ⟶ A ⨿ B))
    (coprod.inl : A ⟶ A ⨿ B).isOpenEmbedding.injective (inl_ne_inr A B)
    (mem_range_inl_or_inr A B) S V hl hr

/-- A subset of `A ⨿ B` meeting the second summand in `V` and the first not at all is the image
of `V`. -/
theorem eq_image_inr_of_preimage (S : Set (A ⨿ B : Scheme.{u})) (V : Set B)
    (hl : (coprod.inl : A ⟶ A ⨿ B) ⁻¹' S = ∅) (hr : (coprod.inr : B ⟶ A ⨿ B) ⁻¹' S = V) :
    S = (coprod.inr : B ⟶ A ⨿ B) '' V :=
  eq_image_of_preimage_eq _ (⇑(coprod.inl : A ⟶ A ⨿ B))
    (coprod.inr : B ⟶ A ⨿ B).isOpenEmbedding.injective (fun b a => inr_ne_inl A B a b)
    (fun y => (mem_range_inl_or_inr A B y).symm) S V hr hl

/-- The disjoint union of two quasi-compact schemes is quasi-compact. -/
theorem compactSpace_coprod [CompactSpace A] [CompactSpace B] :
    CompactSpace (A ⨿ B : Scheme.{u}) := by
  refine ⟨?_⟩
  have h : (Set.univ : Set (A ⨿ B : Scheme.{u})) =
      Set.range (coprod.inl : A ⟶ A ⨿ B) ∪ Set.range (coprod.inr : B ⟶ A ⨿ B) :=
    (isCompl_range_inl_inr A B).sup_eq_top.symm
  rw [h]
  exact (isCompact_range (coprod.inl : A ⟶ A ⨿ B).continuous).union
    (isCompact_range (coprod.inr : B ⟶ A ⨿ B).continuous)

/-- **An ample family on a disjoint union of reduced schemes.** If `A` and `B` carry ample
families of invertible modules and `A ⨿ B` is reduced, then `A ⨿ B` carries an ample family of
invertible modules. -/
theorem exists_isAmpleFamily_coprod [IsReduced (A ⨿ B : Scheme.{u})] {I : Type v} {J : Type w}
    {LA : I → A.Modules} {LB : J → B.Modules} (hA : A.IsAmpleFamily LA)
    (hB : B.IsAmpleFamily LB) :
    ∃ (K : Type u) (M : K → (A ⨿ B : Scheme.{u}).Modules),
      (A ⨿ B : Scheme.{u}).IsAmpleFamily M := by
  classical
  have := hA.compactSpace
  have := hB.compactSpace
  have := compactSpace_coprod A B
  refine Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_pointwise_affine_nonvanishing _
    fun y => ?_
  rcases mem_range_inl_or_inr A B y with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨i, n, -, s, U, hU, ha, haff⟩ := hA.exists_affine_nonvanishing a
    have hN := Stacks.AmpleFamilyRelativeAmple.isInvertible_tensorPow A (LA i)
      (hA.isInvertible i) n
    let L : ∀ k, (summand A B k).Modules := fun k => match k with
      | .left => A.tensorPow (LA i) n
      | .right => SheafOfModules.unit B.ringCatSheaf
    have hL : ∀ k, AlgebraicGeometry.SheafOfModules.IsInvertible (summand A B k).presheaf
        (summand A B k).ringCatSheaf.2 (L k) := fun k => match k with
      | .left => (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hN
      | .right => (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
          (Stacks.SheafOfModules.isInvertible_unit _ _)
    let σ : ∀ k, (L k).sections := fun k => match k with
      | .left => s
      | .right => Stacks.SheafOfModules.sectionsOfTop _ 0
    obtain ⟨M, hM, t, ht⟩ := exists_glue A B L σ
    refine ⟨M, hM, t, (coprod.inl : A ⟶ A ⨿ B) ''ᵁ U, ?_, ⟨a, ha, rfl⟩,
      haff.image_of_isOpenImmersion _⟩
    refine (eq_image_inl_of_preimage A B _ _ ((ht .left).trans hU.symm) ?_).symm
    exact (ht .right).trans (nonvanishingSet_zero B _)
  · obtain ⟨i, n, -, s, U, hU, hb, haff⟩ := hB.exists_affine_nonvanishing b
    have hN := Stacks.AmpleFamilyRelativeAmple.isInvertible_tensorPow B (LB i)
      (hB.isInvertible i) n
    let L : ∀ k, (summand A B k).Modules := fun k => match k with
      | .left => SheafOfModules.unit A.ringCatSheaf
      | .right => B.tensorPow (LB i) n
    have hL : ∀ k, AlgebraicGeometry.SheafOfModules.IsInvertible (summand A B k).presheaf
        (summand A B k).ringCatSheaf.2 (L k) := fun k => match k with
      | .left => (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
          (Stacks.SheafOfModules.isInvertible_unit _ _)
      | .right => (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hN
    let σ : ∀ k, (L k).sections := fun k => match k with
      | .left => Stacks.SheafOfModules.sectionsOfTop _ 0
      | .right => s
    obtain ⟨M, hM, t, ht⟩ := exists_glue A B L σ
    refine ⟨M, hM, t, (coprod.inr : B ⟶ A ⨿ B) ''ᵁ U, ?_, ⟨b, hb, rfl⟩,
      haff.image_of_isOpenImmersion _⟩
    refine (eq_image_inr_of_preimage A B _ _ ?_ ((ht .right).trans hU.symm)).symm
    exact (ht .left).trans (nonvanishingSet_zero A _)

end Coprod

end Stacks.BlowupAmpleFamily

end
