module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyDimensionShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact

/-!
# Filtered colimits of global cohomology on a site that is not small

Stacks 0GN3 says that if a site `C` carries a set `S` of quasi-compact sheaves of sets which
covers the final sheaf and is stable in the four senses (1)-(4) of the source, then
`colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism in every degree `p`, for every
filtered diagram of abelian sheaves. The forms
`isIso_colimit_post_rightDerived_globalSections` and its four-condition specialisation
`isIso_colimit_post_rightDerived_globalSections_of_finite_covers` (Stacks 0GN4) both take
`{C : Type u} [SmallCategory C]`, that is a site whose objects and morphisms live in one
universe. The sites of algebraic geometry do not: the small étale site of an algebraic space,
and the fppf, flat-fppf and lisse-étale sites of an algebraic stack, all have objects in
`Type (u + 1)` and morphisms in `Type u`.

This file removes that restriction. For an arbitrary site `C : Type u₁` with morphisms in
`Type v`, the natural universe for both sheaves of sets and abelian coefficients is the join
`max u₁ v`: that is where the sheafification of `Mathlib.CategoryTheory.Sites.LeftExact` lives and
where `CategoryTheory.Sheaf.IsQuasiCompact` is stated. At that universe every hypothesis and the
conclusion of Stacks 0GN3 read verbatim, and the first main result below is that statement.

## Main results

* `isIso_colimit_post_rightDerived_globalSections_of_coveringSet`: **Stacks 0GN3 for an
  arbitrary site**, at coefficients in the join of the two universes of the site.
* `exists_coveringSet_of_sheafEquivalence`: the five hypotheses of Stacks 0GN3 travel along an
  equivalence of the two categories of sheaves of sets.
* `isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite`: the conclusion travels
  back along the inclusion of a dense subsite.
* `isIso_colimit_post_of_equivalence_comp`, `isIso_colimit_post_of_equivalence_reindex` and
  `isIso_colimit_post_rightDerived_of_equivalences`: the generic transports of the comparison
  map `CategoryTheory.Limits.colimit.post` — along an equivalence of the source category of the
  functor, along an equivalence of the index category of the diagram, and along a pair of
  equivalences conjugating two right derived functors.
* `denseSubsite_globalSectionsIso` and `rightDerivedCompExactIso`: the two natural isomorphisms
  those transports consume.
* `essentiallySmall_join`, `hasSheafify_ab_join`, `enoughInjectives_sheaf_join` and
  `globalSections_additive_join`: the four facts, true of every site at the join universe, that
  make the conclusion of the criterion a well-formed statement. They are installed as local
  instances here.

## Implementation notes

The small model used is `CategoryTheory.AsSmall.{max u₁ v} C`, whose objects and morphisms both
live in `Type (max u₁ v)`, so that it is a `SmallCategory` at that universe. This is the reason
no essential smallness of `C` is assumed: `AsSmall` shrinks nothing, it enlarges the morphisms
until they match the objects, and that is already enough to meet `SmallCategory`. The two
universes of the small model being equal to the join also makes its sheaves of sets and its
abelian coefficients land in `Type (max u₁ v)` and `Ab.{max u₁ v}`, the same universes as on `C`,
so the comparison needs no change of coefficients — only the change of site.

The five hypotheses are transported by replacing local surjectivity with epimorphy
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`), which an equivalence preserves and reflects.
Hypothesis (5), quasi-compactness, is restated through `epi_sigmaDesc_iff` as the statement that a
family of maps into a sheaf is jointly epimorphic.

The index category of the diagram is at the join universe `max u₁ v` as well.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0D07](https://stacks.math.columbia.edu/tag/0D07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.ColimitsOfCohomology

/-! ### Jointly epimorphic families -/

/-- The map out of a coproduct induced by a family of morphisms with a common target is an
epimorphism exactly when the family is jointly epimorphic. -/
lemma epi_sigmaDesc_iff {A : Type*} [Category* A] {ι : Type*} {X : ι → A} {Y : A}
    (f : ∀ i, X i ⟶ Y) [HasCoproduct X] :
    Epi (Sigma.desc f) ↔ ∀ ⦃Z : A⦄ (g h : Y ⟶ Z), (∀ i, f i ≫ g = f i ≫ h) → g = h := by
  refine ⟨fun _ Z g h hgh => (cancel_epi (Sigma.desc f)).1 (Sigma.hom_ext _ _ fun i => by
    simpa using hgh i), fun h => ⟨fun g g' hg => h g g' fun i => ?_⟩⟩
  rw [← Sigma.ι_desc f i, Category.assoc, Category.assoc, hg]

/-- A morphism to the terminal object is an epimorphism as soon as some epimorphism from the same
source to some terminal object exists. -/
lemma epi_terminal_from_of_epi {A : Type*} [Category* A] [HasTerminal A] {X Y : A}
    (hY : IsTerminal Y) (f : X ⟶ Y) [Epi f] : Epi (terminal.from X) := by
  have : IsIso (terminal.from Y) := ⟨⟨hY.from _, hY.hom_ext _ _, terminal.hom_ext _ _⟩⟩
  have h : f ≫ terminal.from Y = terminal.from X := terminal.hom_ext _ _
  rw [← h]
  infer_instance

/-! ### Transport of the comparison map along equivalences -/

/-- An exact additive functor may be moved past a right derived functor:
`(F ⋙ G).rightDerived n ≅ F.rightDerived n ⋙ G` when `G` preserves finite limits and finite
colimits. -/
def rightDerivedCompExactIso
    {A D E : Type*} [Category* A] [Category* D] [Category* E]
    [Abelian A] [HasInjectiveResolutions A] [Abelian D] [Abelian E]
    (F : A ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F.rightDerived n ⋙ G := by
  haveI : G.PreservesHomology := inferInstance
  symm
  refine NatIso.ofComponents (fun X => ?_) ?_
  · unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
      HomotopyCategory.homologyFunctor
    exact (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((injectiveResolutions A).obj X).as).sc n).mapHomologyIso G |>.symm
  · intro X Y f
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℕ)).map_surjective
      ((injectiveResolutions A).map f)
    unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
    simp only [Functor.comp_map]
    rw [← hg]
    unfold HomotopyCategory.homologyFunctor
    dsimp [Functor.comp_map, Functor.mapHomotopyCategory,
      HomologicalComplex.homologyFunctor]
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)) G

/-- The comparison `colimit.post` for a functor precomposed with an equivalence is an
isomorphism as soon as the comparisons for the equivalence and for the functor are. -/
lemma isIso_colimit_post_of_equivalence_comp
    {I : Type*} [Category* I] {A B D : Type*}
    [Category* A] [Category* B] [Category* D]
    (F : I ⥤ A) (e : A ≌ B) (G : B ⥤ D)
    [HasColimitsOfShape I B] [HasColimitsOfShape I D]
    [HasColimit F] [HasColimit (F ⋙ e.functor)]
    [HasColimit ((F ⋙ e.functor) ⋙ G)]
    [IsIso (colimit.post F e.functor)]
    [IsIso (colimit.post (F ⋙ e.functor) G)] :
    IsIso (colimit.post F (e.functor ⋙ G)) := by
  rw [← colimit.post_post F e.functor G]
  infer_instance

/-- Reindexing a diagram along an equivalence of index categories does not change whether the
comparison `colimit.post` is an isomorphism. -/
lemma isIso_colimit_post_of_equivalence_reindex
    {I J : Type*} [Category* I] [Category* J]
    {A D : Type*} [Category* A] [Category* D]
    (e : I ≌ J) (F : J ⥤ A) (G : A ⥤ D)
    [HasColimit F] [HasColimit (e.functor ⋙ F)]
    [HasColimit (F ⋙ G)] [HasColimit ((e.functor ⋙ F) ⋙ G)]
    [IsIso (colimit.post (e.functor ⋙ F) G)] :
    IsIso (colimit.post F G) := by
  have hform : colimit.post F G = inv (colimit.pre (F ⋙ G) e.functor) ≫
      colimit.post (e.functor ⋙ F) G ≫ G.map (colimit.pre F e.functor) := by
    rw [colimit.pre_post, IsIso.inv_hom_id_assoc]
  rw [hform]
  infer_instance

/-- Whether the comparison `colimit.post` for a right derived functor is an isomorphism is
carried along equivalences of the source and the target: if `G' : A' ⥤ D'` and `G : A ⥤ D` are
compared by `α : eA.functor ⋙ G' ≅ G ⋙ eD.functor` across equivalences `eA : A ≌ A'` and
`eD : D ≌ D'`, then the comparison for `G'` at a diagram `F` is an isomorphism as soon as the
comparison for `G` at `F ⋙ eA.inverse` is. -/
lemma isIso_colimit_post_rightDerived_of_equivalences
    {I : Type*} [Category* I] {A A' D D' : Type*}
    [Category* A] [Category* A'] [Category* D] [Category* D']
    [Abelian A] [Abelian A'] [Abelian D] [Abelian D']
    [HasInjectiveResolutions A] [HasInjectiveResolutions A']
    [HasColimitsOfShape I A] [HasColimitsOfShape I A']
    [HasColimitsOfShape I D] [HasColimitsOfShape I D']
    (eA : A ≌ A') (eD : D ≌ D') (G : A ⥤ D) (G' : A' ⥤ D') [G.Additive] [G'.Additive]
    (α : eA.functor ⋙ G' ≅ G ⋙ eD.functor) (p : ℕ) (F : I ⥤ A')
    (hF : IsIso (colimit.post (F ⋙ eA.symm.functor) (G.rightDerived p))) :
    IsIso (colimit.post F (G'.rightDerived p)) := by
  have : eD.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eA.symm.functor.Additive := Functor.additive_of_preserves_binary_products _
  let β : G' ≅ eA.symm.functor ⋙ G ⋙ eD.functor :=
    (Functor.leftUnitor G').symm ≪≫ Functor.isoWhiskerRight eA.counitIso.symm G' ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft eA.symm.functor α
  let γ : G'.rightDerived p ≅ eA.symm.functor ⋙ (G.rightDerived p ⋙ eD.functor) :=
    Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso β p ≪≫
      Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso eA.symm.functor
        (G ⋙ eD.functor) p ≪≫
      Functor.isoWhiskerLeft eA.symm.functor (rightDerivedCompExactIso G eD.functor p)
  have : IsIso (colimit.post (F ⋙ eA.symm.functor) (G.rightDerived p ⋙ eD.functor)) := by
    rw [← colimit.post_post]
    infer_instance
  have : IsIso (colimit.post F (eA.symm.functor ⋙ (G.rightDerived p ⋙ eD.functor))) :=
    isIso_colimit_post_of_equivalence_comp F eA.symm (G.rightDerived p ⋙ eD.functor)
  exact isIso_colimit_post_of_iso F γ.symm

/-- Pushforward of sheaves along the inclusion of a dense subsite commutes with global
sections. -/
def denseSubsite_globalSectionsIso
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    (A : Type*) [Category* A] [G.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A] :
    G.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A ≅ Sheaf.Γ K A := by
  let R := G.sheafPushforwardContinuous A J K
  let e := R.asEquivalence
  let W := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op
  let c : Functor.const Dᵒᵖ ⋙ W ≅ Functor.const Cᵒᵖ := Iso.refl _
  let a : constantSheaf K A ⋙ R ≅ constantSheaf J A :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Functor.const Dᵒᵖ)
        (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility J K G A).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c _
  let b : Sheaf.Γ J A ≅ e.inverse ⋙ Sheaf.Γ K A :=
    (constantSheafΓAdj J A).rightAdjointUniq
      (((constantSheafΓAdj K A).comp e.toAdjunction).ofNatIsoLeft a)
  exact Functor.isoWhiskerLeft R b ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e.unitIso.symm _ ≪≫ Functor.leftUnitor _

/-- The colimit comparison for cohomology travels back along the inclusion `G` of a dense
subsite: if it is an isomorphism for the diagram transported to the larger site `(D, K)`, then it
is an isomorphism on the subsite `(C, J)`. -/
lemma isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    (A : Type*) [Category* A] [Abelian A] [G.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]
    [HasSheafify J A] [HasSheafify K A]
    [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]
    [HasInjectiveResolutions (Sheaf J A)] [HasInjectiveResolutions (Sheaf K A)]
    [(Sheaf.Γ J A).Additive] [(Sheaf.Γ K A).Additive]
    {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [HasColimitsOfShape I (Sheaf J A)] [HasColimitsOfShape I (Sheaf K A)]
    (p : ℕ) (F : I ⥤ Sheaf J A)
    (hF : IsIso (colimit.post
      (F ⋙ (G.sheafPushforwardContinuous A J K).asEquivalence.symm.functor)
      ((Sheaf.Γ K A).rightDerived p))) :
    IsIso (colimit.post F ((Sheaf.Γ J A).rightDerived p)) := by
  refine isIso_colimit_post_rightDerived_of_equivalences
    (G.sheafPushforwardContinuous A J K).asEquivalence CategoryTheory.Equivalence.refl
    (Sheaf.Γ K A) (Sheaf.Γ J A) ?_ p F hF
  exact denseSubsite_globalSectionsIso J K G A ≪≫ (Functor.rightUnitor _).symm

/-! ### Transport of a covering set of sheaves of sets -/

section CoveringSet

universe t v u₁

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  {C₀ : Type max u₁ v} [SmallCategory C₀] (J₀ : GrothendieckTopology C₀)

/-- Sheaves of sets at the join of the two universes of a site have coproducts of families
indexed by a type at that universe, coproducts of sheaves being the sheafification of the
coproducts of the underlying presheaves. -/
local instance hasDiscreteColimits_sheafType (ι : Type max u₁ v) :
    HasColimitsOfShape (Discrete ι) (Sheaf J (Type max u₁ v)) :=
  ⟨fun _ => HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
    Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- The same instance on a small site, where the join of the two universes is the single
universe of the site. -/
local instance hasDiscreteColimits_sheafTypeSmall {D : Type t} [SmallCategory D]
    (K : GrothendieckTopology D) (ι : Type t) :
    HasColimitsOfShape (Discrete ι) (Sheaf K (Type t)) :=
  ⟨fun _ => HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
    Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- **The five hypotheses of Stacks 0GN3 travel along an equivalence of sheaf topoi.** Let
`(C, J)` be a site with morphisms in `Type v` and objects in `Type u₁`, let `(C₀, J₀)` be a site
whose two universes are both the join `max u₁ v`, and let the two categories of sheaves of sets at
that universe be equivalent. Then a set `S` of sheaves of sets on `C` satisfying

1. some `K ∈ S` surjects onto the final sheaf,
2. every surjection `G ⟶ K` onto a member of `S` admits a map `K' ⟶ G` from a member of `S` whose
   composite to `K` is surjective,
3. every pair of members of `S` is covered by a member of `S` mapping onto their product,
4. the equalizer of every pair of maps between members of `S` is covered by a member of `S`, and
5. every member of `S` is quasi-compact,

gives rise to a set `S₀` of sheaves of sets on `C₀` with the same five properties, namely the
image of `S` under the inverse of the equivalence. -/
lemma exists_coveringSet_of_sheafEquivalence
    (E : Sheaf J₀ (Type max u₁ v) ≌ Sheaf J (Type max u₁ v))
    (S : Set (Sheaf J (Type max u₁ v)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type max u₁ v)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_equalizer : ∀ {K K' : Sheaf J (Type max u₁ v)} (a b : K ⟶ K'), K ∈ S → K' ∈ S →
      ∃ K'' ∈ S, ∃ f : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K) :
    ∃ S₀ : Set (Sheaf J₀ (Type max u₁ v)),
      (∃ K ∈ S₀, Sheaf.IsLocallySurjective (terminal.from K)) ∧
      (∀ {G K : Sheaf J₀ (Type max u₁ v)} (f : G ⟶ K), K ∈ S₀ →
        Sheaf.IsLocallySurjective f →
          ∃ K' ∈ S₀, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f)) ∧
      (∀ K ∈ S₀, ∀ K' ∈ S₀,
        ∃ K'' ∈ S₀, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f) ∧
      (∀ {K K' : Sheaf J₀ (Type max u₁ v)} (a b : K ⟶ K'), K ∈ S₀ → K' ∈ S₀ →
        ∃ K'' ∈ S₀, ∃ f : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective f) ∧
      (∀ K ∈ S₀, Sheaf.IsQuasiCompact K) := by
  classical
  have hepi : ∀ {X Y : Sheaf J (Type max u₁ v)} (f : X ⟶ Y),
      Sheaf.IsLocallySurjective f ↔ Epi f := fun f => Sheaf.isLocallySurjective_iff_epi f
  have hepi₀ : ∀ {X Y : Sheaf J₀ (Type max u₁ v)} (f : X ⟶ Y),
      Sheaf.IsLocallySurjective f ↔ Epi f := fun f => Sheaf.isLocallySurjective_iff_epi f
  refine ⟨E.inverse.obj '' S, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨K, hKS, hK⟩ := h_terminal
    rw [hepi] at hK
    refine ⟨E.inverse.obj K, ⟨K, hKS, rfl⟩, ?_⟩
    rw [hepi₀]
    exact epi_terminal_from_of_epi (IsTerminal.isTerminalObj E.inverse _ terminalIsTerminal)
      (E.inverse.map (terminal.from K))
  · intro G₀ K₀ f hK₀ hf
    obtain ⟨K, hKS, rfl⟩ := hK₀
    rw [hepi₀] at hf
    obtain ⟨f₂, hmap⟩ := E.inverse.map_surjective ((E.unitIso.app G₀).inv ≫ f)
    have hf₂epi : Epi f₂ := E.inverse.epi_of_epi_map (by rw [hmap]; infer_instance)
    obtain ⟨K'', hK''S, g, hg⟩ := h_lift f₂ hKS ((hepi _).2 hf₂epi)
    rw [hepi] at hg
    refine ⟨E.inverse.obj K'', ⟨K'', hK''S, rfl⟩,
      E.inverse.map g ≫ (E.unitIso.app G₀).inv, ?_⟩
    rw [hepi₀]
    have heq : (E.inverse.map g ≫ (E.unitIso.app G₀).inv) ≫ f = E.inverse.map (g ≫ f₂) := by
      rw [E.inverse.map_comp, hmap, Category.assoc]
    rw [heq]
    infer_instance
  · intro K₁₀ hK₁₀ K₂₀ hK₂₀
    obtain ⟨K₁, hK₁, rfl⟩ := hK₁₀
    obtain ⟨K₂, hK₂, rfl⟩ := hK₂₀
    obtain ⟨K₃, hK₃, f, hf⟩ := h_product K₁ hK₁ K₂ hK₂
    rw [hepi] at hf
    refine ⟨E.inverse.obj K₃, ⟨K₃, hK₃, rfl⟩,
      E.inverse.map f ≫ (PreservesLimitPair.iso E.inverse K₁ K₂).hom, ?_⟩
    rw [hepi₀]
    infer_instance
  · intro K₁₀ K₂₀ a b hK₁₀ hK₂₀
    obtain ⟨K₁, hK₁, rfl⟩ := hK₁₀
    obtain ⟨K₂, hK₂, rfl⟩ := hK₂₀
    rw [← Functor.map_preimage E.inverse a, ← Functor.map_preimage E.inverse b]
    obtain ⟨K₃, hK₃, f, hf⟩ :=
      h_equalizer (E.inverse.preimage a) (E.inverse.preimage b) hK₁ hK₂
    rw [hepi] at hf
    refine ⟨E.inverse.obj K₃, ⟨K₃, hK₃, rfl⟩,
      E.inverse.map f ≫ (PreservesEqualizer.iso E.inverse
        (E.inverse.preimage a) (E.inverse.preimage b)).hom, ?_⟩
    rw [hepi₀]
    infer_instance
  · intro K₀ hK₀
    obtain ⟨K, hKS, rfl⟩ := hK₀
    intro ι G₀ f₀ hf₀
    rw [hepi₀, epi_sigmaDesc_iff] at hf₀
    choose f hmap using fun i => E.inverse.map_surjective ((E.unitIso.app (G₀ i)).inv ≫ f₀ i)
    have hback (i) : (E.unitIso.app (G₀ i)).hom ≫ E.inverse.map (f i) = f₀ i := by
      rw [hmap i, Iso.hom_inv_id_assoc]
    have hjoint : Epi (Sigma.desc f) := by
      rw [epi_sigmaDesc_iff]
      intro Z g h hgh
      apply E.inverse.map_injective
      refine hf₀ (E.inverse.map g) (E.inverse.map h) fun i => ?_
      rw [← hback i, Category.assoc, Category.assoc, ← E.inverse.map_comp,
        ← E.inverse.map_comp, hgh i]
    obtain ⟨T, hT, hTepi⟩ :=
      h_quasiCompact K hKS ι (fun i => E.functor.obj (G₀ i)) f ((hepi _).2 hjoint)
    refine ⟨T, hT, ?_⟩
    rw [hepi, epi_sigmaDesc_iff] at hTepi
    rw [hepi₀, epi_sigmaDesc_iff]
    intro Z₀ g h hgh
    obtain ⟨g₂, hg₂⟩ := E.inverse.map_surjective (g ≫ (E.unitIso.app Z₀).hom)
    obtain ⟨h₂, hh₂⟩ := E.inverse.map_surjective (h ≫ (E.unitIso.app Z₀).hom)
    have key : g₂ = h₂ := by
      refine hTepi g₂ h₂ fun j => ?_
      apply E.inverse.map_injective
      rw [E.inverse.map_comp, E.inverse.map_comp, hg₂, hh₂, hmap, Category.assoc,
        Category.assoc, ← Category.assoc (f₀ j.1), ← Category.assoc (f₀ j.1), hgh j]
    exact (cancel_mono (E.unitIso.app Z₀).hom).1 (by rw [← hg₂, ← hh₂, key])

end CoveringSet

/-! ### The criterion on an arbitrary site -/

section LargeSite

universe v u₁

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)

/-- Any category is essentially small at the join of its two universes. -/
theorem essentiallySmall_join : EssentiallySmall.{max u₁ v} C :=
  EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{max u₁ v} C)

attribute [local instance] essentiallySmall_join

/-- Presheaves of abelian groups with sections at the join of the two universes of the site admit
a left exact sheafification, the site being essentially small at that universe. -/
theorem hasSheafify_ab_join : HasSheafify J Ab.{max u₁ v} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u₁ v, v, u₁} J

attribute [local instance] hasSheafify_ab_join

/-- Abelian sheaves with sections at the join of the two universes of the site form a
Grothendieck abelian category, hence have enough injectives. -/
@[sga "4 V 2.5.2" "special case", sga "4½ Arcata 1.6.3"]
theorem enoughInjectives_sheaf_join : EnoughInjectives (Sheaf J Ab.{max u₁ v}) :=
  (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u₁ v} J Ab.{max u₁ v}).enoughInjectives

attribute [local instance] enoughInjectives_sheaf_join

/-- Global sections of abelian sheaves is additive, being a right adjoint. -/
theorem globalSections_additive_join : (Sheaf.Γ J (Ab.{max u₁ v})).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] globalSections_additive_join

/-- **Stacks 0GN3 for an arbitrary site.** Let `C` be a site with objects in `Type u₁` and
morphisms in `Type v`, and let `S` be a set of sheaves of sets on `C` with sections at the join
`max u₁ v` of those two universes, such that

1. some `K ∈ S` surjects onto the final sheaf,
2. every surjection `G ⟶ K` onto a member of `S` admits a map `K' ⟶ G` from a member of `S` whose
   composite to `K` is surjective,
3. every pair of members of `S` is covered by a member of `S` mapping onto their product,
4. the equalizer of every pair of maps between members of `S` is covered by a member of `S`, and
5. every member of `S` is quasi-compact.

Then `colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism in every degree `p`, for every
filtered diagram `F` of abelian sheaves with sections at that same universe.

Unlike `isIso_colimit_post_rightDerived_globalSections`, the site need not be a `SmallCategory`:
its objects and morphisms may live in different universes. -/
@[stacks 0GN3 "for a site whose objects and morphisms need not share a universe"]
theorem isIso_colimit_post_rightDerived_globalSections_of_coveringSet
    (S : Set (Sheaf J (Type max u₁ v)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type max u₁ v)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_equalizer : ∀ {K K' : Sheaf J (Type max u₁ v)} (a b : K ⟶ K'), K ∈ S → K' ∈ S →
      ∃ K'' ∈ S, ∃ f : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    (p : ℕ) {I : Type max u₁ v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J (Ab.{max u₁ v})) :
    IsIso (colimit.post F ((Sheaf.Γ J (Ab.{max u₁ v})).rightDerived p)) := by
  let e : C ≌ AsSmall.{max u₁ v} C := AsSmall.equiv
  let J₀ : GrothendieckTopology (AsSmall.{max u₁ v} C) := e.inverse.inducedTopology J
  have hinv : e.inverse.IsEquivalence := e.isEquivalence_inverse
  obtain ⟨S₀, ht, hl, hp, heq, hqc⟩ :=
    exists_coveringSet_of_sheafEquivalence J J₀
      (e.functor.sheafPushforwardContinuous (Type max u₁ v) J J₀).asEquivalence S
      h_terminal h_lift h_product h_equalizer h_quasiCompact
  refine isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite J J₀ e.functor
    Ab.{max u₁ v} p F ?_
  exact isIso_colimit_post_rightDerived_globalSections J₀ S₀ ht hl hp heq hqc p _

end LargeSite

end Stacks.Cohomology.ColimitsOfCohomology

end
