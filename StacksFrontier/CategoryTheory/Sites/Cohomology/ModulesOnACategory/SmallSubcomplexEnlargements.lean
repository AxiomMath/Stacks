module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.WellPowered
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticModelTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallSubcomplexesOfSections
import StacksCore.Tactic.StacksAttribute

/-!
# Small subcomplexes containing prescribed sections, in the presheaf model

Let `C` be a category, regarded as a site with the chaotic topology, and let `O` be a presheaf
of rings on `C`. Stacks 0GYX produces a cardinal `κ`, depending only on `C` and `O`, such that
every family of prescribed sections `Ω^i_U ⊆ F^i(U)` of a complex `F^•` of `O`-modules is
contained in a subcomplex `H^• ⊆ F^•` with at most `max κ |⋃ Ω^i_U|` sections. That statement is
available for sheaves of modules on the chaotic site
(`Stacks.ModulesOnACategory.exists_subcomplex_containing_sections_of_size_le`); here it is carried
across the equivalence of the two models of modules on a chaotic site, so that it applies to the
complexes of presheaves of modules which the derived category `D(O)` of
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod` is built from.

The transported statement is then upgraded to the form in which the proof of Stacks 0GYZ consumes
it. There the subcomplex to be enlarged is given as a subcomplex `S^• ⊆ F^•`, and one needs not
merely that the sections of `S^•` lie in the enlargement `H^•` but an actual factorization
`S^• ⟶ H^• ⟶ F^•` of the inclusion. Taking for the prescribed family the sections of `F^•` in the
image of `S^•`, together with any further family `Ω`, the factorization is produced from the
sectionwise containment because a monomorphism of presheaves of modules is sectionwise injective:
this is `PresheafOfModules.factorThru`, applied degreewise and shown to commute with the
differentials by cancelling the monomorphism.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.presheafSectionFamilySize`: the number of
  prescribed sections of a complex of `O`-modules, counted over all degrees and all objects
  of `C`.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_subcomplex_containing_sections`:
  Stacks 0GYX in the presheaf model, the uniformly bounded subcomplex containing every prescribed
  section.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_hom_of_sectionwise_mem_range`: a map
  of complexes of `O`-modules whose sections lie sectionwise in the image of a monomorphism
  factors through that monomorphism.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_enlargement_containing_sections`:
  the form of Stacks 0GYX used in Stacks 0GYZ — a map `S^• ⟶ F^•` factors through a subcomplex of
  `F^•` which contains a prescribed family of sections and has at most
  `max κ (max |S^•| |⋃ Ω^i_U|)` sections.

## Implementation notes

For the chaotic topology a presheaf of rings `O` and the sheaf of rings `⟨O, _⟩` carry the same
data, and the two categories of modules are identified by a functor which is the identity on
objects and morphisms; consequently the sheaf-side count of sections of a complex and the count
used in the presheaf model differ only by a `Cardinal.lift` which is the identity, and a family of
prescribed sections of a complex of presheaves of modules *is* a family of prescribed sections of
the corresponding complex of sheaves of modules. The transport therefore changes nothing but the
`Cardinal.lift`, which is why the comparison of the two counts of a family of sections is proved
exactly as `Stacks.ModulesOnACategory.complexSectionSize_eq_presheaf` is.

The prescribed family used for the enlargement is `Ω^i_U ∪ (image of S^i(U))`; its size is bounded
by a disjoint sum of the two indexed families, so the cardinal `κ` of the enlargement statement is
taken to contain `ℵ₀`, the sheaf-side cardinal of Stacks 0GYX carrying no such guarantee in its
statement.

## References

* [Stacks Project, Tag 0GYX](https://stacks.math.columbia.edu/tag/0GYX)
* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C]

/-! ### Counting a family of prescribed sections -/

/-- The number of prescribed sections of a complex of `O`-modules, counted over all degrees and
all objects of `C`. This is the `|⋃ Ω^i_U|` of Stacks 0GYX in the presheaf model. -/
def presheafSectionFamilySize {O : Cᵒᵖ ⥤ RingCat.{r}}
    {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).obj (op U))) : Cardinal.{max u v r w} :=
  Cardinal.mk (Σ i : ℤ, Σ U : C, {x // x ∈ Omega i U})

/-- The presheaf of rings `O` read as a sheaf of rings for the chaotic topology, under which
every presheaf is a sheaf. -/
def chaoticRingSheaf (O : Cᵒᵖ ⥤ RingCat.{r}) :
    Sheaf (⊥ : GrothendieckTopology C) RingCat.{r} :=
  ⟨O, Presheaf.isSheaf_bot O⟩

/-- Counting a family of prescribed sections of a complex of presheaves of modules agrees with
counting it in the sheaf model: the two counts are the cardinality of the same type, and the
sheaf-side count carries a `Cardinal.lift` which is the identity once the module universe absorbs
the site and ring universes. -/
lemma sectionFamilySize_eq_presheaf (O : Cᵒᵖ ⥤ RingCat.{r})
    (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).obj (op U))) :
    Stacks.ModulesOnACategory.sectionFamilySize
        (R := chaoticRingSheaf.{u, v, r} O)
        (F := (chaoticComplexEquivalence (chaoticRingSheaf.{u, v, r} O)).inverse.obj F) Omega =
      presheafSectionFamilySize.{w} Omega := by
  change Cardinal.lift.{max v r} (Cardinal.mk (Σ i : ℤ, Σ U : C, {x // x ∈ Omega i U})) =
    Cardinal.mk (Σ i : ℤ, Σ U : C, {x // x ∈ Omega i U})
  exact Cardinal.lift_id'.{max v r, max u w} _

/-! ### Stacks 0GYX in the presheaf model -/

/-- **Stacks 0GYX in the presheaf model.** There is a cardinal, depending only on the category
and its presheaf of rings, such that every family of prescribed sections of a complex of
`O`-modules is contained in a subcomplex whose number of sections is bounded by the maximum of
that cardinal and the size of the family.

This is the transport of
`Stacks.ModulesOnACategory.exists_subcomplex_containing_sections_of_size_le` across the
equivalence between sheaves of modules on the chaotic site and presheaves of modules, which
preserves monomorphisms and identifies the two counts of sections. -/
@[stacks 0GYX "presheaf model"]
theorem exists_subcomplex_containing_sections (O : Cᵒᵖ ⥤ RingCat.{r}) :
    ∃ kappa : Cardinal.{max u v r w},
      ∀ (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
        (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).obj (op U))),
        ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (inclusion : H ⟶ F),
          Mono inclusion ∧
            (∀ (i : ℤ) (U : C) (x : (F.X i).obj (op U)), x ∈ Omega i U →
              ∃ y : (H.X i).obj (op U), (inclusion.f i).app (op U) y = x) ∧
            complexSectionSize.{w} O H ≤ max kappa (presheafSectionFamilySize.{w} Omega) := by
  obtain ⟨kappa, hkappa⟩ :=
    Stacks.ModulesOnACategory.exists_subcomplex_containing_sections_of_size_le.{v,
      max u v r w, r, u} (chaoticRingSheaf.{u, v, r} O)
  refine ⟨kappa, fun F Omega => ?_⟩
  set R := chaoticRingSheaf.{u, v, r} O with hR
  obtain ⟨Hs, incl, hmono, hcontain, hsize⟩ :=
    hkappa ((chaoticComplexEquivalence R).inverse.obj F) Omega
  refine ⟨(chaoticComplexEquivalence R).functor.obj Hs,
    (chaoticComplexEquivalence R).functor.map incl,
    mono_chaoticComplexEquivalence_functor_map R incl, fun i U x hx => hcontain i U x hx, ?_⟩
  have hcx : complexSectionSize.{w} O ((chaoticComplexEquivalence R).functor.obj Hs) =
      Stacks.ModulesOnACategory.complexSectionSize Hs :=
    (Stacks.ModulesOnACategory.complexSectionSize_eq_presheaf R Hs).symm
  have hfam : presheafSectionFamilySize.{w} Omega =
      Stacks.ModulesOnACategory.sectionFamilySize
        (F := (chaoticComplexEquivalence R).inverse.obj F) Omega :=
    (sectionFamilySize_eq_presheaf.{w} O F Omega).symm
  rw [hcx, hfam]
  exact hsize

/-! ### Factoring through a subcomplex that contains the sections -/

/-- A map of complexes of `O`-modules whose sections lie sectionwise in the image of a
monomorphism factors through that monomorphism. The factorization is built degreewise from
`PresheafOfModules.factorThru`, which exists because a monomorphism of presheaves of modules is
sectionwise injective, and it commutes with the differentials because the monomorphism can be
cancelled. -/
theorem exists_hom_of_sectionwise_mem_range {O : Cᵒᵖ ⥤ RingCat.{r}}
    {S H F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    (g : S ⟶ F) (h : H ⟶ F) [Mono h]
    (hrange : ∀ (i : ℤ) (X : Cᵒᵖ) (x : (S.X i).obj X),
      ∃ y : (H.X i).obj X, (h.f i).app X y = (g.f i).app X x) :
    ∃ k : S ⟶ H, k ≫ h = g := by
  have hle (i : ℤ) : PresheafOfModules.Submodule.range (g.f i) ≤
      PresheafOfModules.Submodule.range (h.f i) := by
    rw [PresheafOfModules.Submodule.le_iff]
    intro X
    rintro y ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hrange i X x
    exact ⟨z, hz⟩
  refine ⟨{ f := fun i => PresheafOfModules.factorThru (g.f i) (h.f i) (hle i)
            comm' := fun i j _ => ?_ }, ?_⟩
  · rw [← cancel_mono (h.f j)]
    simp only [Category.assoc, PresheafOfModules.factorThru_comp]
    rw [← h.comm i j]
    simp only [PresheafOfModules.factorThru_comp_assoc]
    exact g.comm i j
  · refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
    exact PresheafOfModules.factorThru_comp (g.f i) (h.f i) (hle i)

/-- **The enlargement statement used in Stacks 0GYZ.** There is a cardinal `κ`, depending only on
the category and its presheaf of rings, with the following property: any map `S^• ⟶ F^•` of
complexes of `O`-modules factors through a subcomplex `H^• ⊆ F^•` which contains every section in
a prescribed family `Ω` and has at most `max κ (max |S^•| |⋃ Ω^i_U|)` sections.

The subcomplex is the one Stacks 0GYX produces for the family `Ω` enlarged by the sections of
`F^•` in the image of `S^•`; that enlargement at most doubles the index type, hence does not
exceed the stated bound, and the containment of the image of `S^•` is exactly the hypothesis of
`exists_hom_of_sectionwise_mem_range`. -/
theorem exists_enlargement_containing_sections (O : Cᵒᵖ ⥤ RingCat.{r}) :
    ∃ kappa : Cardinal.{max u v r w},
      ∀ (F S : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : S ⟶ F)
        (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).obj (op U))),
        ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F) (k : S ⟶ H),
          Mono h ∧ k ≫ h = g ∧
            (∀ (i : ℤ) (U : C) (x : (F.X i).obj (op U)), x ∈ Omega i U →
              ∃ y : (H.X i).obj (op U), (h.f i).app (op U) y = x) ∧
            complexSectionSize.{w} O H ≤
              max kappa (max (complexSectionSize.{w} O S)
                (presheafSectionFamilySize.{w} Omega)) := by
  classical
  obtain ⟨kappa, hkappa⟩ := exists_subcomplex_containing_sections.{w} O
  refine ⟨max Cardinal.aleph0 kappa, fun F S g Omega => ?_⟩
  obtain ⟨H, h, hmono, hcontain, hsize⟩ := hkappa F
    (fun i U => Omega i U ∪ Set.range (fun x : (S.X i).obj (op U) => (g.f i).app (op U) x))
  obtain ⟨k, hk⟩ := exists_hom_of_sectionwise_mem_range.{w} g h
    (fun i X x => hcontain i X.unop ((g.f i).app X x)
      (Set.mem_union_right _ ⟨x, rfl⟩))
  -- the enlarged family is covered by the disjoint sum of the two indexed families
  have hfam : presheafSectionFamilySize.{w}
      (F := F) (fun i U => Omega i U ∪
        Set.range (fun x : (S.X i).obj (op U) => (g.f i).app (op U) x)) ≤
      max (max (presheafSectionFamilySize.{w} Omega) (complexSectionSize.{w} O S))
        Cardinal.aleph0 := by
    refine le_trans (Cardinal.mk_le_of_surjective
      (f := fun p : (Σ i : ℤ, Σ U : C, {x // x ∈ Omega i U}) ⊕
          (Σ i : ℤ, Σ U : C, (S.X i).obj (op U)) =>
        (match p with
          | Sum.inl q => ⟨q.1, q.2.1, q.2.2.1, Set.mem_union_left _ q.2.2.2⟩
          | Sum.inr q => ⟨q.1, q.2.1, (g.f q.1).app (op q.2.1) q.2.2,
              Set.mem_union_right _ (Set.mem_range_self _)⟩ :
          Σ i : ℤ, Σ U : C, {x // x ∈ Omega i U ∪
            Set.range (fun y : (S.X i).obj (op U) => (g.f i).app (op U) y)})) ?_) ?_
    · rintro ⟨i, U, x, hx⟩
      rcases hx with hx | ⟨y, hy⟩
      · exact ⟨Sum.inl ⟨i, U, x, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨i, U, y⟩, by simp only [hy]⟩
    · rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_le_max _ _
  refine ⟨H, h, k, hmono, hk, fun i U x hx => hcontain i U x (Set.mem_union_left _ hx), ?_⟩
  refine hsize.trans (max_le (le_max_of_le_left (le_max_right _ _)) (hfam.trans ?_))
  exact max_le (max_le (le_max_of_le_right (le_max_right _ _))
      (le_max_of_le_right (le_max_left _ _))) (le_max_of_le_left (le_max_left _ _))

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
