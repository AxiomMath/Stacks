module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Reducing AB5 to filtered shapes small relative to the hom universe

Grothendieck's axiom AB5 quantifies over filtered index categories of a fixed size, and the size
is usually larger than the hom universe of the category it is asked about. This file reduces the
general statement to the small case: an abelian category with filtered colimits of size `(s, s')`
satisfies AB5 at that size as soon as its filtered colimits are exact for shapes whose objects
are small relative to its hom universe.

## Main results

* `CategoryTheory.ab5OfSize_of_exactSmallFilteredColimits`: AB5 at an arbitrary size follows from
  exactness of filtered colimits over shapes with homs in the hom universe and objects small
  relative to it.

## Implementation notes

There are two reductions, and the morphism universe is the easy one: for a monomorphism
`α : F ⟶ G` of diagrams on a filtered shape `S`, the category of pairs of values of `F` and `G`
— objects of `S`, with a morphism a pair of arrows in the image of a single arrow of `S` — is
filtered, has homs in the ambient hom universe, and receives a final functor from `S`, so the
colimits of `F` and `G` are unchanged and the question is transported to a shape with small homs.

Bounding the *object* universe is where a hypothesis is needed, and the hypothesis is simply that
the category has a nonzero object: the finite coproducts of a fixed object `M` with `𝟙 M ≠ 0`
form a filtered diagram whose colimit carries, for each element of an index type `α`, a distinct
map to `M`, so `α` injects into the hom type and the object universe is bounded by the hom
universe. The degenerate alternative, that every identity vanishes, is handled directly: there
every morphism is a monomorphism, so the colimit functor trivially preserves them.

Both reductions are applied to the criterion that AB5 holds as soon as the colimit functor
preserves monomorphisms, `CategoryTheory.hasExactColimitsOfShape_of_preservesMono`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe s s' r z

noncomputable section

private abbrev FiniteSubsets (α : Type s') := Finset (Discrete α)

private instance finiteSubsetsCategory (α : Type s') : Category.{s, s'} (FiniteSubsets α) where
  Hom S T := ULift.{s} (PLift (S ≤ T))
  id S := ⟨⟨le_rfl⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩
  id_comp := by intro X Y f; cases f; rfl
  comp_id := by intro X Y f; cases f; rfl
  assoc := by intro W X Y Z f g h; cases f; cases g; cases h; rfl

private instance finiteSubsetsFiltered (α : Type s') : IsFiltered (FiniteSubsets α) := by
  classical
  let : DecidableEq (Discrete α) := Classical.decEq _
  exact {
    nonempty := ⟨∅⟩
    cocone_objs X Y := ⟨X ∪ Y, ⟨⟨Finset.subset_union_left⟩⟩,
      ⟨⟨Finset.subset_union_right⟩⟩, trivial⟩
    cocone_maps := by
      intro X Y f g
      exact ⟨Y, 𝟙 _, by cases f; cases g; rfl⟩
  }

private def finiteCoproductDiagram {E : Type z} [Category.{r, z} E]
    [HasFiniteCoproducts E] (α : Type s') (M : E) : FiniteSubsets α ⥤ E where
  obj S := ∐ fun _ : S => M
  map {S T} f := Sigma.desc fun x => Sigma.ι (fun _ : T => M) ⟨x.1, f.down.down x.2⟩
  map_id S := by apply Sigma.hom_ext; intro x; simp
  map_comp f g := by apply Sigma.hom_ext; intro x; simp

private def finiteCoproductDeltaCocone {E : Type z} [Category.{r, z} E] [Preadditive E]
    [HasFiniteCoproducts E] (α : Type s') (M : E) (i : α) :
    Cocone (finiteCoproductDiagram.{s', r, z, s} α M) := by
  classical
  exact {
    pt := M
    ι := {
      app := fun S => Sigma.desc fun x => if x.1 = (Discrete.mk i) then 𝟙 M else 0
      naturality := by intro S T f; apply Sigma.hom_ext; intro x; simp [finiteCoproductDiagram]
    }
  }

private def finiteCoproductDeltaMap {E : Type z} [Category.{r, z} E] [Preadditive E]
    [HasFiniteCoproducts E] [HasFilteredColimitsOfSize.{s, s'} E]
    (α : Type s') (M : E) (i : α) :
    colimit (finiteCoproductDiagram.{s', r, z, s} α M) ⟶ M :=
  colimit.desc _ (finiteCoproductDeltaCocone α M i)

private def finiteCoproductSingletonMap {E : Type z} [Category.{r, z} E]
    [HasFiniteCoproducts E] [HasFilteredColimitsOfSize.{s, s'} E]
    (α : Type s') (M : E) (i : α) :
    M ⟶ colimit (finiteCoproductDiagram.{s', r, z, s} α M) := by
  let S : FiniteSubsets α := {Discrete.mk i}
  exact Sigma.ι (fun _ : S => M) ⟨Discrete.mk i, by simp [S]⟩ ≫
    eqToHom (by rfl) ≫ colimit.ι (finiteCoproductDiagram.{s', r, z, s} α M) S

private theorem finiteCoproductSingletonDelta_same {E : Type z} [Category.{r, z} E]
    [Preadditive E] [HasFiniteCoproducts E] [HasFilteredColimitsOfSize.{s, s'} E]
    (α : Type s') (M : E) (i : α) :
    finiteCoproductSingletonMap α M i ≫ finiteCoproductDeltaMap α M i = 𝟙 M := by
  unfold finiteCoproductSingletonMap finiteCoproductDeltaMap finiteCoproductDeltaCocone
  simp only [Category.assoc, colimit.ι_desc]
  simp [finiteCoproductDiagram]

private theorem finiteCoproductSingletonDelta_ne {E : Type z} [Category.{r, z} E]
    [Preadditive E] [HasFiniteCoproducts E] [HasFilteredColimitsOfSize.{s, s'} E]
    (α : Type s') (M : E) {i j : α} (h : i ≠ j) :
    finiteCoproductSingletonMap α M i ≫ finiteCoproductDeltaMap α M j = 0 := by
  unfold finiteCoproductSingletonMap finiteCoproductDeltaMap finiteCoproductDeltaCocone
  simp only [Category.assoc, colimit.ι_desc]
  simp [finiteCoproductDiagram, h]

private theorem univLE_of_filtered_coproducts {E : Type z} [Category.{r, z} E]
    [Preadditive E] [HasFiniteCoproducts E] [HasFilteredColimitsOfSize.{s, s'} E]
    [LocallySmall.{r} E] (M : E) (hM : (𝟙 M : M ⟶ M) ≠ 0) : UnivLE.{s', r} := by
  refine ⟨fun α => ?_⟩
  let P := colimit (finiteCoproductDiagram.{s', r, z, s} α M)
  let f : α → (P ⟶ M) := fun i => finiteCoproductDeltaMap α M i
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hh := congrArg (fun g : P ⟶ M => finiteCoproductSingletonMap α M i ≫ g) hij
    rw [finiteCoproductSingletonDelta_same, finiteCoproductSingletonDelta_ne α M hne] at hh
    exact hM hh
  exact small_of_injective hf

private structure FilteredImagePair {S : Type s'} [Category.{s, s'} S]
    {E : Type z} [Category.{r, z} E] (F G : S ⥤ E) where
  obj : S

private instance filteredImagePairCategory {S : Type s'} [Category.{s, s'} S]
    {E : Type z} [Category.{r, z} E] (F G : S ⥤ E) :
    Category.{r, s'} (FilteredImagePair F G) where
  Hom x y := {p : (F.obj x.obj ⟶ F.obj y.obj) × (G.obj x.obj ⟶ G.obj y.obj) //
    ∃ f : x.obj ⟶ y.obj, p = (F.map f, G.map f)}
  id x := ⟨(𝟙 (F.obj x.obj), 𝟙 (G.obj x.obj)), ⟨𝟙 x.obj, by simp⟩⟩
  comp f g := by
    refine ⟨(f.1.1 ≫ g.1.1, f.1.2 ≫ g.1.2), ?_⟩
    rcases f.2 with ⟨f', hf⟩
    rcases g.2 with ⟨g', hg⟩
    refine ⟨f' ≫ g', ?_⟩
    rw [hf, hg]
    simp
  id_comp := by intros; apply Subtype.ext; simp
  comp_id := by intros; apply Subtype.ext; simp
  assoc := by intros; apply Subtype.ext; simp [Category.assoc]

private def filteredImagePairQuotient {S : Type s'} [Category.{s, s'} S]
    {E : Type z} [Category.{r, z} E] (F G : S ⥤ E) : S ⥤ FilteredImagePair F G where
  obj j := ⟨j⟩
  map f := ⟨(F.map f, G.map f), ⟨f, rfl⟩⟩
  map_id := by
    intro X
    apply Subtype.ext
    change (F.map (𝟙 X), G.map (𝟙 X)) = (𝟙 (F.obj X), 𝟙 (G.obj X))
    simp
  map_comp := by
    intro X Y Z f g
    apply Subtype.ext
    change (F.map (f ≫ g), G.map (f ≫ g)) = (F.map f ≫ F.map g, G.map f ≫ G.map g)
    simp

private abbrev filteredImagePairLeft {S : Type s'} [Category.{s, s'} S]
    {E : Type z} [Category.{r, z} E] (F G : S ⥤ E) : FilteredImagePair F G ⥤ E where
  obj j := F.obj j.obj
  map f := f.1.1
  map_id := by intros; rfl
  map_comp := by intros; rfl

private abbrev filteredImagePairRight {S : Type s'} [Category.{s, s'} S]
    {E : Type z} [Category.{r, z} E] (F G : S ⥤ E) : FilteredImagePair F G ⥤ E where
  obj j := G.obj j.obj
  map f := f.1.2
  map_id := by intros; rfl
  map_comp := by intros; rfl

private theorem filteredImagePair_exists_coeq {S : Type s'} [Category.{s, s'} S]
    [IsFilteredOrEmpty S] {E : Type z} [Category.{r, z} E] {F G : S ⥤ E}
    {x y : FilteredImagePair F G} (f g : x ⟶ y) :
    ∃ (c : S) (k : y.obj ⟶ c),
      f ≫ (filteredImagePairQuotient F G).map k = g ≫ (filteredImagePairQuotient F G).map k := by
  obtain ⟨f', hf⟩ := f.2
  obtain ⟨g', hg⟩ := g.2
  obtain ⟨c, k, hk⟩ := IsFilteredOrEmpty.cocone_maps f' g'
  refine ⟨c, k, Subtype.ext ?_⟩
  change (f.1.1 ≫ F.map k, f.1.2 ≫ G.map k) = (g.1.1 ≫ F.map k, g.1.2 ≫ G.map k)
  rw [hf, hg]
  simpa only [Functor.map_comp] using congrArg (fun q => (F.map q, G.map q)) hk

private instance filteredImagePairFiltered {S : Type s'} [Category.{s, s'} S] [IsFiltered S]
    {E : Type z} [Category.{r, z} E] (F G : S ⥤ E) : IsFiltered (FilteredImagePair F G) where
  nonempty := let ⟨j⟩ := IsFiltered.nonempty (C := S); ⟨⟨j⟩⟩
  cocone_objs x y :=
    let ⟨z, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs x.obj y.obj
    ⟨⟨z⟩, (filteredImagePairQuotient F G).map f, (filteredImagePairQuotient F G).map g, trivial⟩
  cocone_maps _ _ f g :=
    let ⟨c, _k, hk⟩ := filteredImagePair_exists_coeq f g
    ⟨⟨c⟩, _, hk⟩

private theorem filteredImagePairQuotient_final {S : Type s'} [Category.{s, s'} S] [IsFiltered S]
    {E : Type z} [Category.{r, z} E] (F G : S ⥤ E) :
    Functor.Final (filteredImagePairQuotient F G) := by
  rw [Functor.final_iff_of_isFiltered]
  exact ⟨fun d => ⟨d.obj, ⟨(filteredImagePairQuotient F G).map (𝟙 d.obj)⟩⟩,
    fun f g => filteredImagePair_exists_coeq f g⟩

private def filteredImagePairMap {S : Type s'} [Category.{s, s'} S]
    {E : Type z} [Category.{r, z} E] {F G : S ⥤ E} (α : F ⟶ G) :
    filteredImagePairLeft F G ⟶ filteredImagePairRight F G where
  app j := α.app j.obj
  naturality := by
    intro i j f
    change f.1.1 ≫ α.app j.obj = α.app i.obj ≫ f.1.2
    rcases f.2 with ⟨k, hk⟩
    rw [hk]
    exact α.naturality k

private theorem filteredImagePairMap_mono {S : Type s'} [Category.{s, s'} S]
    {E : Type z} [Category.{r, z} E] [HasPullbacks E] {F G : S ⥤ E} (α : F ⟶ G) [Mono α] :
    Mono (filteredImagePairMap α) := by
  have (j : FilteredImagePair F G) : Mono ((filteredImagePairMap α).app j) :=
    (NatTrans.mono_iff_mono_app α).mp ‹_› j.obj
  exact NatTrans.mono_of_mono_app _

private theorem colim_preservesMono_of_univLE {E : Type z} [Category.{r, z} E] [Abelian E]
    (hsmall : ∀ (K : Type s') [Category.{r, s'} K] [IsFiltered K] [UnivLE.{s', r}]
      [HasColimitsOfShape K E], HasExactColimitsOfShape K E)
    [UnivLE.{s', r}] (S : Type s') [Category.{s, s'} S] [IsFiltered S]
    [HasColimitsOfShape S E] : Functor.PreservesMonomorphisms (colim (J := S) (C := E)) := by
  refine ⟨fun {F G} α hα => ?_⟩
  let K := FilteredImagePair F G
  let : Category.{r, s'} K := filteredImagePairCategory F G
  let : IsFiltered K := inferInstance
  let q := filteredImagePairQuotient F G
  let : Functor.Final q := filteredImagePairQuotient_final F G
  let : HasColimitsOfShape K E := Functor.Final.hasColimitsOfShape_of_final q
  let : HasExactColimitsOfShape K E := hsmall K
  let αK := filteredImagePairMap α
  have : Mono αK := filteredImagePairMap_mono α
  let ηF : colimit F ≅ colimit (filteredImagePairLeft F G) :=
    Functor.Final.colimitIso q (filteredImagePairLeft F G)
  let ηG : colimit G ≅ colimit (filteredImagePairRight F G) :=
    Functor.Final.colimitIso q (filteredImagePairRight F G)
  have hηF (j : S) : colimit.ι F j ≫ ηF.hom = colimit.ι (filteredImagePairLeft F G) ⟨j⟩ :=
    Functor.Final.ι_colimitIso_hom q (filteredImagePairLeft F G) j
  have hηG (j : S) : colimit.ι G j ≫ ηG.hom = colimit.ι (filteredImagePairRight F G) ⟨j⟩ :=
    Functor.Final.ι_colimitIso_hom q (filteredImagePairRight F G) j
  have hsquare : colim.map α ≫ ηG.hom = ηF.hom ≫ (colim (J := K) (C := E)).map αK := by
    apply colimit.hom_ext
    intro j
    rw [colimit.ι_map_assoc, hηG, ← Category.assoc, hηF, colimit.ι_map]
    simp [αK, filteredImagePairMap, filteredImagePairLeft, filteredImagePairRight]
  have hfac : colim.map α = ηF.hom ≫ (colim (J := K) (C := E)).map αK ≫ ηG.inv := by
    rw [← Category.assoc, ← hsquare]
    simp
  rw [hfac]
  infer_instance

private theorem colim_preservesMono_of_id_eq_zero {E : Type z} [Category.{r, z} E] [Abelian E]
    (S : Type s') [Category.{s, s'} S] [HasColimitsOfShape S E]
    (h : ∀ X : E, (𝟙 X : X ⟶ X) = 0) :
    Functor.PreservesMonomorphisms (colim (J := S) (C := E)) := by
  have hzero {X Y : E} (f : X ⟶ Y) : f = 0 := by rw [← Category.id_comp f, h, zero_comp]
  have : ∀ {X Y : E} (f : X ⟶ Y), Mono f := fun _ => ⟨fun g h _ => (hzero g).trans (hzero h).symm⟩
  exact ⟨fun _ _ => inferInstance⟩

end

/-- An abelian category `E` with filtered colimits of size `(s, s')` satisfies AB5 at that size,
provided colimits are exact over every filtered category with homs in `E`'s hom universe `r` and
objects in a universe `s'` with `UnivLE.{s', r}`. -/
theorem ab5OfSize_of_exactSmallFilteredColimits {E : Type z} [Category.{r, z} E] [Abelian E]
    (hsmall : ∀ (K : Type s') [Category.{r, s'} K] [IsFiltered K] [UnivLE.{s', r}]
      [HasColimitsOfShape K E], HasExactColimitsOfShape K E)
    [HasFilteredColimitsOfSize.{s, s'} E] : AB5OfSize.{s, s'} E := by
  refine ⟨fun S _ _ => ?_⟩
  suffices Functor.PreservesMonomorphisms (colim (J := S) (C := E)) from
    hasExactColimitsOfShape_of_preservesMono (C := E) S
  by_cases hNonzero : ∃ M : E, (𝟙 M : M ⟶ M) ≠ 0
  · obtain ⟨M, hM⟩ := hNonzero
    have : UnivLE.{s', r} := univLE_of_filtered_coproducts M hM
    exact colim_preservesMono_of_univLE hsmall S
  · push Not at hNonzero
    exact colim_preservesMono_of_id_eq_zero S hNonzero

end CategoryTheory

end
