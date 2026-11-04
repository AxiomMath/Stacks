module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageOverOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct

/-!
# Making a proper morphism surjective by glueing on the complement

A morphism `π₀ : V₀ ⟶ U` which is proper and whose image contains an open `O ⊆ U` is made
*surjective* by adding to `V₀` a closed subscheme of `U` supported on the complement of `O`:
the resulting morphism out of the binary coproduct is still proper, is surjective, and its
part over `O` is unchanged.

This is the last step of stage 1 of the proof of Stacks 0DBF part (2) — "and glueing on a
closed subscheme structure on `U ∖ U_i` makes it surjective" — and it is the only part of that
stage which needs no input from Chow's lemma. See
`StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementFibreProduct` for the hypothesis
these results are built to discharge.

## Main results

* `AlgebraicGeometry.isProper_coprodDesc`: a *binary* coproduct of proper morphisms with a
  common target is proper. The finite-coproduct statement is
  `AlgebraicGeometry.isProper_sigmaDesc`; the binary one is not an instance of it on the nose,
  because the binary and the indexed coproduct of two schemes are two different colimits of
  one and the same functor.
* `AlgebraicGeometry.range_coprodDesc` and `AlgebraicGeometry.surjective_coprodDesc`: the image
  of a morphism out of a binary coproduct is the union of the images of its two restrictions.
* `AlgebraicGeometry.exists_isClosedImmersion_range_eq`: every closed subset of a scheme is the
  image of a closed immersion. The reduced induced structure is not needed; the subscheme cut
  out by the vanishing ideal sheaf of the closed set already has the prescribed support.
* `AlgebraicGeometry.exists_isProper_surjective_of_subset_range`: the statement described
  above.
* `AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_isProper`: the same statement
  with an affine open covering of the part over `O` carried along, which is the form in which
  the fibre-product stage of Stacks 0DBF part (2) consumes it.
* `AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_isClosedImmersion`: the whole
  of stage 1 of Stacks 0DBF part (2) *after* Chow's lemma. Given a scheme proper over the base
  `U` — in the application `ℙⁿ_U` — a closed immersion of `W` into its part over an open `O`,
  and an affine open covering of `W` mapping into a prescribed family, one obtains a proper
  *surjection* onto `U` whose part over `O` is `W` with that same covering.

## Implementation notes

`AlgebraicGeometry.coprodIsoSigma` identifies `X ⨿ Y` with the coproduct of the family
`ULift WalkingPair → Scheme` taking the two values `X` and `Y`, and that index type is finite,
so `AlgebraicGeometry.isProper_sigmaDesc` applies to it. Only the two component equations
`AlgebraicGeometry.ι_left_coprodIsoSigma_inv` and
`AlgebraicGeometry.ι_right_coprodIsoSigma_inv` are needed to transport the statement across.

## References

* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace AlgebraicGeometry

section Coprod

variable {T X Y : Scheme.{u}} (a : X ⟶ T) (b : Y ⟶ T)

/-- The two morphisms `a : X ⟶ T` and `b : Y ⟶ T` as a family indexed by the two-element type
`ULift WalkingPair` over which `AlgebraicGeometry.coprodIsoSigma` presents `X ⨿ Y`. -/
abbrev coprodDescFamily :
    ∀ i : ULift.{u} WalkingPair, (WalkingPair.casesOn i.down X Y : Scheme.{u}) ⟶ T :=
  fun i => i.down.casesOn a b

/-- A morphism out of a binary coproduct, read through `AlgebraicGeometry.coprodIsoSigma` as a
morphism out of the coproduct of a two-element family. -/
theorem coprodIsoSigma_inv_comp_coprodDesc :
    (coprodIsoSigma X Y).inv ≫ coprod.desc a b = Sigma.desc (coprodDescFamily a b) := by
  refine Sigma.hom_ext _ _ fun i => ?_
  obtain ⟨i⟩ := i
  rw [← Category.assoc]
  cases i
  · rw [ι_left_coprodIsoSigma_inv, coprod.inl_desc, Sigma.ι_desc]
  · rw [ι_right_coprodIsoSigma_inv, coprod.inr_desc, Sigma.ι_desc]

/-- A property holding for `a` and `b` holds for every member of `coprodDescFamily a b`. -/
private theorem prop_coprodDescFamily (P : MorphismProperty Scheme.{u}) (ha : P a) (hb : P b)
    (i : ULift.{u} WalkingPair) : P (coprodDescFamily a b i) := by
  obtain ⟨i⟩ := i
  cases i
  exacts [ha, hb]

/-- `coprod.desc a b` is `coprodIsoSigma X Y` followed by `Sigma.desc` of the family. -/
private theorem coprodDesc_eq_hom_comp_sigmaDesc :
    coprod.desc a b = (coprodIsoSigma X Y).hom ≫ Sigma.desc (coprodDescFamily a b) := by
  rw [← coprodIsoSigma_inv_comp_coprodDesc, Iso.hom_inv_id_assoc]

/-- **A binary coproduct of proper morphisms with a common target is proper.** -/
theorem isProper_coprodDesc [IsProper a] [IsProper b] : IsProper (coprod.desc a b) := by
  have h := prop_coprodDescFamily a b (P := @IsProper) inferInstance inferInstance
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper (coprodIsoSigma X Y).inv,
    coprodIsoSigma_inv_comp_coprodDesc]
  exact isProper_sigmaDesc _

/-- **A binary coproduct of flat morphisms with a common target is flat.** The coproduct is
rewritten as `(coprodIsoSigma X Y).hom ≫ Sigma.desc _` (rather than cancelled against the
inverse, which would need `MorphismProperty.RespectsIso @Flat` as a bare typeclass-search goal)
so that `Flat` of the composite follows from `Flat.comp`, with the already-registered instance
`Flat (Sigma.desc _)` on the second factor and `IsOpenImmersion → Flat` on the isomorphism. -/
theorem flat_coprodDesc [Flat a] [Flat b] : Flat (coprod.desc a b) := by
  have h := prop_coprodDescFamily a b (P := @Flat) inferInstance inferInstance
  have heq := coprodDesc_eq_hom_comp_sigmaDesc a b
  rw [heq]
  infer_instance

/-- **A binary coproduct of morphisms locally of finite presentation with a common target is
locally of finite presentation.** As in `AlgebraicGeometry.flat_coprodDesc`, the coproduct is
rewritten as a composite with the comparison isomorphism `coprodIsoSigma X Y` rather than
cancelled against it, to avoid a bare `MorphismProperty.RespectsIso` typeclass-search goal.
Unlike `Flat`, `LocallyOfFinitePresentation` has no ready-made instance for `Sigma.desc`, so the
witness for the second factor is built from `IsZariskiLocalAtSource.sigmaDesc`, supplying its
`IsZariskiLocalAtSource` instance argument by the explicit term
`HasRingHomProperty.instIsZariskiLocalAtSource` instead of through typeclass search: search
would need to unify that instance's generic conclusion against the concrete property
`@LocallyOfFinitePresentation`, which only succeeds at a transparency setting unavailable here. -/
theorem locallyOfFinitePresentation_coprodDesc [LocallyOfFinitePresentation a]
    [LocallyOfFinitePresentation b] : LocallyOfFinitePresentation (coprod.desc a b) := by
  have h := prop_coprodDescFamily a b (P := @LocallyOfFinitePresentation) inferInstance
    inferInstance
  have heq := coprodDesc_eq_hom_comp_sigmaDesc a b
  rw [heq]
  have hz : IsZariskiLocalAtSource (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource (@LocallyOfFinitePresentation) _ _
  have : LocallyOfFinitePresentation (Sigma.desc (coprodDescFamily a b)) :=
    @IsZariskiLocalAtSource.sigmaDesc _ hz _ _ _ _ _ h
  infer_instance

/-- The two summands of a binary coproduct of schemes cover it. -/
theorem union_range_coprod_inl_inr (X Y : Scheme.{u}) :
    Set.range (coprod.inl : X ⟶ X ⨿ Y) ∪ Set.range (coprod.inr : Y ⟶ X ⨿ Y) = Set.univ := by
  simpa using (isCompl_range_inl_inr X Y).sup_eq_top

/-- The image of a morphism out of a binary coproduct is the union of the images of its two
restrictions. -/
theorem range_coprodDesc :
    Set.range (coprod.desc a b) = Set.range a ∪ Set.range b := by
  refine Set.eq_of_subset_of_subset ?_ (Set.union_subset ?_ ?_)
  · rintro _ ⟨x, rfl⟩
    rcases Set.eq_univ_iff_forall.mp (union_range_coprod_inl_inr X Y) x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨y, by rw [← hy, ← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact Or.inr ⟨y, by rw [← hy, ← Scheme.Hom.comp_apply, coprod.inr_desc]⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(coprod.inl : X ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

/-- A morphism out of a binary coproduct is surjective as soon as the images of its two
restrictions cover the target. -/
theorem surjective_coprodDesc (h : Set.range a ∪ Set.range b = Set.univ) :
    Surjective (coprod.desc a b) :=
  ⟨Set.range_eq_univ.mp ((range_coprodDesc a b).trans h)⟩

end Coprod

/-- **Every closed subset of a scheme is the image of a closed immersion.** The subscheme cut
out by the vanishing ideal sheaf of the closed set does the job; the reduced induced structure
is not needed, since only the support of the ideal sheaf is being prescribed. -/
theorem exists_isClosedImmersion_range_eq {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) :
    ∃ (C : Scheme.{u}) (c : C ⟶ X), IsClosedImmersion c ∧ Set.range c = Z := by
  refine ⟨(Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme,
    (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subschemeι, inferInstance, ?_⟩
  simp

/-- **A proper morphism whose image contains an open `O` extends to a proper surjection whose
part over `O` is unchanged.** One adds to the source a closed subscheme of the base supported
on the complement of `O`; it is proper because closed immersions are, and a binary coproduct
of proper morphisms is proper by `AlgebraicGeometry.isProper_coprodDesc`.

This is the glueing step at the end of stage 1 of the proof of Stacks 0DBF part (2). -/
theorem exists_isProper_surjective_of_subset_range {U V₀ : Scheme.{u}} (π₀ : V₀ ⟶ U)
    [IsProper π₀] {O : Set U} (hO : IsOpen O) (hsub : O ⊆ Set.range π₀) :
    ∃ (V : Scheme.{u}) (ι₀ : V₀ ⟶ V) (π : V ⟶ U), IsOpenImmersion ι₀ ∧ IsProper π ∧
      Surjective π ∧ ι₀ ≫ π = π₀ ∧ π ⁻¹' O ⊆ Set.range ι₀ := by
  obtain ⟨C, c, hc, hcrange⟩ := exists_isClosedImmersion_range_eq Oᶜ hO.isClosed_compl
  have hcp : IsProper c := inferInstance
  refine ⟨V₀ ⨿ C, coprod.inl, coprod.desc π₀ c, inferInstance, isProper_coprodDesc π₀ c,
    surjective_coprodDesc π₀ c ?_, coprod.inl_desc _ _, ?_⟩
  · rw [hcrange, Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ O
    · exact Or.inl (hsub hx)
    · exact Or.inr hx
  · intro x hx
    rcases Set.eq_univ_iff_forall.mp (union_range_coprod_inl_inr V₀ C) x with hl | ⟨y, rfl⟩
    · exact hl
    · refine absurd hx ?_
      have hmem : (coprod.desc π₀ c) ((coprod.inr : C ⟶ V₀ ⨿ C) y) ∈ Oᶜ := by
        rw [← hcrange, ← Scheme.Hom.comp_apply, coprod.inr_desc]
        exact Set.mem_range_self y
      exact hmem

/-- **The form in which the fibre-product stage of Stacks 0DBF part (2) consumes
`AlgebraicGeometry.exists_isProper_surjective_of_subset_range`.** A proper morphism
`π₀ : V₀ ⟶ U` whose image contains an open `O`, together with finitely many affine opens of
`V₀` covering the part of `V₀` over `O` and mapping over `U` into a prescribed family `Z`,
yields a proper *surjection* `π : V ⟶ U` with the same affine opens, still covering the part
of `V` over `O` and still mapping into `Z`.

Only surjectivity is gained; nothing else about the morphism changes. The scheme glued on over
the complement of `O` carries no affine open of the family, which is exactly why the covering
condition survives. -/
theorem exists_isProper_surjective_affine_cover_of_isProper {U : Scheme.{u}} {S : Type w}
    {Z : S → Scheme.{u}} (zz : ∀ s, Z s ⟶ U) {O : Set U} (hO : IsOpen O) {V₀ : Scheme.{u}}
    (π₀ : V₀ ⟶ U) [IsProper π₀] (hsub : O ⊆ Set.range π₀) {n : ℕ} {A : Fin n → Scheme.{u}}
    (α : ∀ k, A k ⟶ V₀) {σ : Fin n → S} (b : ∀ k, A k ⟶ Z (σ k))
    (hopen : ∀ k, IsOpenImmersion (α k)) (hfac : ∀ k, α k ≫ π₀ = b k ≫ zz (σ k))
    (hcov : π₀ ⁻¹' O ⊆ ⋃ k, Set.range (α k)) :
    ∃ (V : Scheme.{u}) (π : V ⟶ U), IsProper π ∧ Surjective π ∧
      ∃ α' : ∀ k, A k ⟶ V, (∀ k, IsOpenImmersion (α' k)) ∧
        (∀ k, α' k ≫ π = b k ≫ zz (σ k)) ∧ π ⁻¹' O ⊆ ⋃ k, Set.range (α' k) := by
  obtain ⟨V, ι₀, π, hι₀, hπ, hπs, hfacι, hpre⟩ :=
    exists_isProper_surjective_of_subset_range π₀ hO hsub
  refine ⟨V, π, hπ, hπs, fun k => α k ≫ ι₀, fun k => have := hopen k; inferInstance,
    fun k => ?_, ?_⟩
  · rw [Category.assoc, hfacι]
    exact hfac k
  · intro x hx
    obtain ⟨y, rfl⟩ := hpre hx
    have hy : y ∈ π₀ ⁻¹' O := by
      rw [Set.mem_preimage, ← hfacι, Scheme.Hom.comp_apply]
      exact hx
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp (hcov hy)
    exact Set.mem_iUnion.mpr ⟨k, z, by rw [Scheme.Hom.comp_apply, hz]⟩

/-- **Stage 1 of the proof of Stacks 0DBF part (2), after Chow's lemma.** Let `p : P ⟶ U` be
proper, let `j : Q ⟶ P` be the part of `P` lying over an open `O ⊆ U`, and let `w : W ⟶ Q` be
a closed immersion whose composite to `U` hits all of `O`. Let `W` be covered by finitely many
affine opens mapping over `U` into a prescribed family `Z`. Then there is a proper surjection
`π : V ⟶ U` whose part over `O` is `W`, carrying the same affine opens and the same
factorisations through `Z`.

In the application `P = ℙⁿ_U`, `Q = ℙⁿ_{U_i}`, and `w` is the closed immersion produced from
Chow's lemma by
`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpace_of_hasChowModification`. The
scheme `V` is the scheme-theoretic closure of `W` in `P` with a closed subscheme of `U`
supported on `U ∖ O` glued on; the two steps are
`AlgebraicGeometry.range_toImage_comp_isOpenImmersion`, which says that the part of the
closure over `O` is again `W` (Stacks 01R8), and
`AlgebraicGeometry.exists_isProper_surjective_of_subset_range`, which supplies surjectivity. -/
theorem exists_isProper_surjective_affine_cover_of_isClosedImmersion {U P Q W : Scheme.{u}}
    {S : Type w} {Z : S → Scheme.{u}} (zz : ∀ s, Z s ⟶ U) (p : P ⟶ U) [IsProper p] (j : Q ⟶ P)
    [IsOpenImmersion j] (w : W ⟶ Q) [IsClosedImmersion w] [QuasiCompact (w ≫ j)] {O : Set U}
    (hO : IsOpen O) (hj : Set.range j = p ⁻¹' O) (hsurj : O ⊆ Set.range (w ≫ j ≫ p))
    {n : ℕ} {A : Fin n → Scheme.{u}} (α : ∀ k, A k ⟶ W) {σ : Fin n → S}
    (b : ∀ k, A k ⟶ Z (σ k)) (hopen : ∀ k, IsOpenImmersion (α k))
    (hfac : ∀ k, α k ≫ w ≫ j ≫ p = b k ≫ zz (σ k))
    (hcov : (⋃ k, Set.range (α k)) = Set.univ) :
    ∃ (V : Scheme.{u}) (π : V ⟶ U), IsProper π ∧ Surjective π ∧
      ∃ α' : ∀ k, A k ⟶ V, (∀ k, IsOpenImmersion (α' k)) ∧
        (∀ k, α' k ≫ π = b k ≫ zz (σ k)) ∧ π ⁻¹' O ⊆ ⋃ k, Set.range (α' k) := by
  have himm : IsImmersion (w ≫ j) := inferInstance
  have hoi : IsOpenImmersion (w ≫ j).toImage := inferInstance
  have hπ₀ : IsProper ((w ≫ j).imageι ≫ p) := inferInstance
  have hcomp : (w ≫ j).toImage ≫ (w ≫ j).imageι ≫ p = w ≫ j ≫ p := by
    rw [← Category.assoc, (w ≫ j).toImage_imageι, Category.assoc]
  have hrange : Set.range (w ≫ j).toImage = ((w ≫ j).imageι ≫ p) ⁻¹' O := by
    rw [range_toImage_comp_isOpenImmersion, hj]
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_preimage, Scheme.Hom.comp_apply]
  refine exists_isProper_surjective_affine_cover_of_isProper zz hO ((w ≫ j).imageι ≫ p)
    (fun x hx => ?_) (fun k => α k ≫ (w ≫ j).toImage) b (fun k => inferInstance)
    (fun k => ?_) ?_
  · obtain ⟨y, hy⟩ := hsurj hx
    refine ⟨(w ≫ j).toImage y, ?_⟩
    rw [← hy, ← hcomp]
    simp only [Scheme.Hom.comp_apply]
  · rw [Category.assoc, hcomp]
    exact hfac k
  · rw [← hrange]
    rintro _ ⟨y, rfl⟩
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ y)
    exact Set.mem_iUnion.mpr ⟨k, z, by rw [Scheme.Hom.comp_apply, hz]⟩

end AlgebraicGeometry

end
