module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksFrontier.Algebra.Module.ProjResComplexFlat
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat
public import StacksFrontier.Homology.DerivedCategory.SubcomplexEnlargement.DerivedBaseChangeHomology
public import StacksFrontier.Homology.DerivedCategory.SubcomplexEnlargement.UnionOfSubcomplexes

@[expose] public noncomputable section

/-!
# Enlarging subcomplexes compatibly with derived base change

For a ring homomorphism `A →+* B`, there is a cardinal bound with the following property.
Given a morphism from the derived base change of a complex of `A`-modules to a complex of
`B`-modules which is an isomorphism, compatible subcomplexes can be enlarged so that the kernel
and image defects on cohomology disappear, without exceeding the prescribed cardinal bound.

## Main results

* `Stacks.SubcomplexEnlargement.exists_enlargements_killing_kernel_and_covering_image`: compatible
  subcomplexes can be enlarged with controlled cardinality so as to kill the kernel and cover the
  image on every cohomology module.

`familyIsColimit`, `derivedBaseChangeHomology_preservesFilteredColimits_ulift` and
`isColimit_familyCocone_sequence` are the ingredients by which a statement about each stage of an
increasing chain of subcomplexes becomes a statement about the union: the union is the filtered
colimit of the stages, and the cohomology of its derived base change is the colimit of theirs.
They are used that way in the proof of the main result above, and they are stated for their own
sake because the enlargement argument of Stacks 0GYZ consumes them in the opposite direction,
deducing invertibility at the union from the stagewise kernel and image conditions — which is
what `isIso_of_stagewise_kernel_and_image` packages.

## Implementation notes

The derived tensor product with `B` is the total left-derived functor of termwise extension of
scalars, followed by localization at quasi-isomorphisms. A map of complexes of `A`-modules into
the restriction of a complex of `B`-modules is expressed, by adjunction, as the corresponding
`B`-linear map out of termwise extension of scalars. Subcomplexes are represented by complexes
equipped with monomorphisms into the ambient complexes. The cardinality of a complex is
represented by the cardinality of the disjoint union of its terms.

## References

* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SubcomplexEnlargement

universe u v w t

attribute [local instance] HasDerivedCategory.standard

open Cardinal

attribute [local instance] toRangeFamily_isIso complexOfSubmodulesι_mono

/-- The total size of the image family is at most the size of its source complex. -/
private lemma mk_rangeFamily_le
    {R : Type u} [Ring R] {K M : CochainComplex (ModuleCat.{v} R) ℤ} (φ : K ⟶ M) :
    #(Σ i, (rangeFamily φ).toComplex.X i) ≤ #(Σ i, K.X i) := by
  rw [mk_sigma, mk_sigma]
  exact sum_le_sum _ _ (mk_rangeFamily_term_le φ)

/-- The total size of a pair of image families is at most the size of their source complexes. -/
private lemma mk_sum_rangeFamily_le
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    {M₁ M : CochainComplex (ModuleCat.{w} A) ℤ} {N₁ N : CochainComplex (ModuleCat.{w} B) ℤ}
    (m : M₁ ⟶ M) (n : N₁ ⟶ N) :
    #((Σ i, (rangeFamily m).toComplex.X i) ⊕ (Σ i, (rangeFamily n).toComplex.X i)) ≤
      #((Σ i, M₁.X i) ⊕ (Σ i, N₁.X i)) := by
  rw [mk_sum, mk_sum, lift_id, lift_id, lift_id, lift_id]
  exact add_le_add (mk_rangeFamily_le m) (mk_rangeFamily_le n)

/-- A compatible pair of subcomplexes is specified by the existence of the restricted map. -/
private abbrev CompatiblePair
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    {M : CochainComplex (ModuleCat.{w} A) ℤ} {N : CochainComplex (ModuleCat.{w} B) ℤ}
    (E : CochainComplex (ModuleCat.{w} A) ℤ ⥤ CochainComplex (ModuleCat.{w} B) ℤ)
    (b : E.obj M ⟶ N) (P : SubcomplexFamily M × SubcomplexFamily N) : Prop :=
  ∃ b' : E.obj P.1.toComplex ⟶ P.2.toComplex, E.map P.1.ι ≫ b = b' ≫ P.2.ι

/-- Bounded compatible pairs containing fixed initial subcomplexes. -/
private abbrev BoundedCompatiblePairs
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    {M : CochainComplex (ModuleCat.{w} A) ℤ} {N : CochainComplex (ModuleCat.{w} B) ℤ}
    (E : CochainComplex (ModuleCat.{w} A) ℤ ⥤ CochainComplex (ModuleCat.{w} B) ℤ)
    (b : E.obj M ⟶ N) (P₀ : SubcomplexFamily M) (Q₀ : SubcomplexFamily N) (κ : Cardinal.{w}) :=
  {P : SubcomplexFamily M × SubcomplexFamily N //
    P₀ ≤ P.1 ∧ Q₀ ≤ P.2 ∧ CompatiblePair E b P ∧
      #((Σ i, P.1.toComplex.X i) ⊕ (Σ i, P.2.toComplex.X i)) ≤ κ}

/-- An infinite cardinal bounds the union of at most that many sets of bounded size. -/
private lemma mk_iUnion_le_of_le
    {α ι : Type u} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hι : #ι ≤ κ)
    (S : ι → Set α) (hS : ∀ i, #(S i) ≤ κ) : #(⋃ i, S i) ≤ κ := by
  apply mk_iUnion_le_sum_mk.trans
  apply (sum_le_sum _ _ hS).trans
  rw [sum_const, lift_id, lift_id]
  exact mul_le_of_le hκ hι le_rfl

/-- Bounded generators are contained in a bounded compatible pair of image families. -/
private lemma exists_boundedCompatiblePairs_containing
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (M M₁ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (N N₁ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
    (m₁ : M₁ ⟶ M) (n₁ : N₁ ⟶ N) [Mono m₁] [Mono n₁]
    (b : ((ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    (s : ∀ i, Set (M.X i)) (t : ∀ i, Set (N.X i))
    (hm₁ : ∀ i x, (m₁.f i) x ∈ s i) (hn₁ : ∀ i x, (n₁.f i) x ∈ t i)
    {κ : Cardinal.{max u v w}} (hκ : ℵ₀ ≤ κ)
    (hA : lift.{max v w} #A ≤ κ) (hB : lift.{max u w} #B ≤ κ)
    (hs : ∀ i, #(s i) ≤ κ) (ht : ∀ i, #(t i) ≤ κ) :
    ∃ P : BoundedCompatiblePairs
        ((ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
          (ComplexShape.up ℤ)) b (rangeFamily m₁) (rangeFamily n₁) κ,
      (∀ i, s i ⊆ (P.1.1.1 i : Set (M.X i))) ∧
      (∀ i, t i ⊆ (P.1.2.1 i : Set (N.X i))) := by
  obtain ⟨M₂, N₂, m₂, n₂, hm₂, hn₂, m₁₂, n₁₂, hm₁₂, hn₁₂, b₂,
    hmf, hnf, hb, hms, hns, hsize⟩ :=
    exists_compatible_enlargement_cardinal_le f M M₁ N N₁ m₁ n₁ b s t hm₁ hn₁
      hκ hA hB hs ht
  let := hm₂
  let := hn₂
  refine ⟨⟨⟨rangeFamily m₂, rangeFamily n₂⟩, ?_, ?_, ?_, ?_⟩, hms, hns⟩
  · intro i x hx
    obtain ⟨y, rfl⟩ := hx
    exact hms i (hm₁ i y)
  · intro i x hx
    obtain ⟨y, rfl⟩ := hx
    exact hns i (hn₁ i y)
  · exact rangeFamily_compatible _ m₂ n₂ b b₂ hb
  · exact (mk_sum_rangeFamily_le m₂ n₂).trans hsize

/-- The size of a term on either side is bounded by the total size of a pair of complexes. -/
private lemma mk_term_le_mk_sum_left {X Y : ℤ → Type u} (i : ℤ) :
    #(X i) ≤ #((Σ j, X j) ⊕ (Σ j, Y j)) :=
  (mk_term_le_mk_sigma i).trans (mk_le_of_injective Sum.inl_injective)

private lemma mk_term_le_mk_sum_right {X Y : ℤ → Type u} (i : ℤ) :
    #(Y i) ≤ #((Σ j, X j) ⊕ (Σ j, Y j)) :=
  (mk_term_le_mk_sigma i).trans (mk_le_of_injective Sum.inr_injective)

/-- Bounded compatible pairs are directed even for families of bounded cardinality. -/
private lemma boundedCompatiblePairs_directed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (M M₁ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (N N₁ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
    (m₁ : M₁ ⟶ M) (n₁ : N₁ ⟶ N) [Mono m₁] [Mono n₁]
    (b : ((ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    {κ : Cardinal.{max u v w}} (hκ : ℵ₀ ≤ κ)
    (hA : lift.{max v w} #A ≤ κ) (hB : lift.{max u w} #B ≤ κ)
    (hM₁ : ∀ i, #(M₁.X i) ≤ κ) (hN₁ : ∀ i, #(N₁.X i) ≤ κ) :
    let J := BoundedCompatiblePairs
      ((ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
        (ComplexShape.up ℤ)) b (rangeFamily m₁) (rangeFamily n₁) κ
    ∀ s : Set J, #s ≤ κ → ∃ k, ∀ j ∈ s, j ≤ k := by
  intro J s hs
  let sM (i : ℤ) : Set (M.X i) := Set.range (m₁.f i) ∪ ⋃ p : s, (p.1.1.1.1 i : Set (M.X i))
  let sN (i : ℤ) : Set (N.X i) := Set.range (n₁.f i) ∪ ⋃ p : s, (p.1.1.2.1 i : Set (N.X i))
  have hsM (i : ℤ) : #(sM i) ≤ κ := by
    exact (mk_union_le _ _).trans (add_le_of_le hκ ((mk_range_le (f := m₁.f i)).trans (hM₁ i))
      (mk_iUnion_le_of_le hκ hs _ fun p => (mk_term_le_mk_sum_left i).trans p.1.2.2.2.2))
  have hsN (i : ℤ) : #(sN i) ≤ κ := by
    exact (mk_union_le _ _).trans (add_le_of_le hκ ((mk_range_le (f := n₁.f i)).trans (hN₁ i))
      (mk_iUnion_le_of_le hκ hs _ fun p => (mk_term_le_mk_sum_right i).trans p.1.2.2.2.2))
  obtain ⟨P, hPM, hPN⟩ := exists_boundedCompatiblePairs_containing f M M₁ N N₁ m₁ n₁ b
    sM sN (fun i x => Or.inl ⟨x, rfl⟩) (fun i x => Or.inl ⟨x, rfl⟩) hκ hA hB hsM hsN
  refine ⟨P, fun j hj => ⟨?_, ?_⟩⟩
  · intro i x hx
    exact hPM i (Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩))
  · intro i x hx
    exact hPN i (Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩))

private lemma isFiltered_of_bounded_directed
    {J : Type u} [Preorder J] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hdir : ∀ s : Set J, #s ≤ κ → ∃ k, ∀ j ∈ s, j ≤ k) : IsFiltered J := by
  obtain ⟨j, _⟩ := hdir ∅ (by simp)
  have : Nonempty J := ⟨j⟩
  have : IsDirectedOrder J := ⟨fun a b => by
    have hab : #({a, b} : Set J) ≤ κ := by
      apply mk_insert_le.trans
      simpa only [mk_singleton] using add_le_of_le hκ
        (one_le_aleph0.trans hκ) (one_le_aleph0.trans hκ)
    obtain ⟨k, hk⟩ := hdir {a, b} hab
    exact ⟨k, hk a (by simp), hk b (by simp)⟩⟩
  infer_instance

/-- Every ambient element lies in a bounded compatible pair. -/
private lemma boundedCompatiblePairs_cover
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (M M₁ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (N N₁ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
    (m₁ : M₁ ⟶ M) (n₁ : N₁ ⟶ N) [Mono m₁] [Mono n₁]
    (b : ((ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    {κ : Cardinal.{max u v w}} (hκ : ℵ₀ ≤ κ)
    (hA : lift.{max v w} #A ≤ κ) (hB : lift.{max u w} #B ≤ κ)
    (hM₁ : ∀ i, #(M₁.X i) ≤ κ) (hN₁ : ∀ i, #(N₁.X i) ≤ κ) :
    let J := BoundedCompatiblePairs
      ((ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
        (ComplexShape.up ℤ)) b (rangeFamily m₁) (rangeFamily n₁) κ
    (∀ i (x : M.X i), ∃ P : J, x ∈ P.1.1.1 i) ∧
      (∀ i (x : N.X i), ∃ P : J, x ∈ P.1.2.1 i) := by
  classical
  intro J
  constructor
  · intro i x
    let x' (j : ℤ) : M.X j := if h : i = j then h ▸ x else 0
    let s (j : ℤ) : Set (M.X j) := Set.range (m₁.f j) ∪ {x' j}
    have hs (j : ℤ) : #(s j) ≤ κ := by
      apply (mk_union_le _ _).trans
      apply add_le_of_le hκ ((mk_range_le (f := m₁.f j)).trans (hM₁ j))
      simpa only [mk_singleton] using one_le_aleph0.trans hκ
    obtain ⟨P, hPM, _⟩ := exists_boundedCompatiblePairs_containing f M M₁ N N₁ m₁ n₁ b
      s (fun j => Set.range (n₁.f j)) (fun j y => Or.inl ⟨y, rfl⟩)
      (fun j y => ⟨y, rfl⟩) hκ hA hB hs
      (fun j => (mk_range_le (f := n₁.f j)).trans (hN₁ j))
    exact ⟨P, hPM i (Or.inr (by simp [x']))⟩
  · intro i x
    let x' (j : ℤ) : N.X j := if h : i = j then h ▸ x else 0
    let s (j : ℤ) : Set (N.X j) := Set.range (n₁.f j) ∪ {x' j}
    have hs (j : ℤ) : #(s j) ≤ κ := by
      apply (mk_union_le _ _).trans
      apply add_le_of_le hκ ((mk_range_le (f := n₁.f j)).trans (hN₁ j))
      simpa only [mk_singleton] using one_le_aleph0.trans hκ
    obtain ⟨P, _, hPN⟩ := exists_boundedCompatiblePairs_containing f M M₁ N N₁ m₁ n₁ b
      (fun j => Set.range (m₁.f j)) s (fun j y => ⟨y, rfl⟩)
      (fun j y => Or.inl ⟨y, rfl⟩) hκ hA hB
      (fun j => (mk_range_le (f := m₁.f j)).trans (hM₁ j)) hs
    exact ⟨P, hPN i (Or.inr (by simp [x']))⟩

/-- One stage realizes all kernel and image witnesses in all integer degrees. -/
private lemma exists_stage_all_degrees_killing_kernel_and_covering_image
    {R : Type u} [Ring R] {J : Type v} [Preorder J] [IsFiltered J]
    (F G : ℤ → J ⥤ ModuleCat.{v} R) (α : ∀ i, F i ⟶ G i)
    (cF : ∀ i, Cocone (F i)) (cG : ∀ i, Cocone (G i))
    (hF : ∀ i, IsColimit (cF i)) (hG : ∀ i, IsColimit (cG i))
    (g : ∀ i, (cF i).pt ⟶ (cG i).pt) [∀ i, IsIso (g i)]
    (hg : ∀ i j, (cF i).ι.app j ≫ g i = (α i).app j ≫ (cG i).ι.app j)
    {κ : Cardinal.{v}} (hκ : ℵ₀ ≤ κ)
    (hdir : ∀ s : Set J, #s ≤ κ → ∃ k, ∀ j ∈ s, j ≤ k)
    (j : J) (hFj : ∀ i, #((F i).obj j) ≤ κ) (hGj : ∀ i, #((G i).obj j) ≤ κ) :
    ∃ (k : J) (p : j ⟶ k),
      (∀ i (x : (F i).obj j), ((α i).app j) x = 0 → ((F i).map p) x = 0) ∧
      (∀ i (y : (G i).obj j), ∃ x : (F i).obj k, ((α i).app k) x = ((G i).map p) y) := by
  classical
  have hJ : ∀ s : Set J, #s ≤ κ → ∃ k, ∀ j ∈ s, Nonempty (j ⟶ k) := by
    intro s hs
    obtain ⟨k, hk⟩ := hdir s hs
    exact ⟨k, fun j hj => ⟨homOfLE (hk j hj)⟩⟩
  choose k p hk hsurj using fun i =>
    exists_stage_killing_kernel_and_covering_image (α i) (hF i) (hG i) (g i)
      (hg i) hκ hJ j (hFj i) (hGj i)
  have hsize : #(Set.range k) ≤ κ := by
    have h := mk_range_le_lift (f := k)
    rw [lift_uzero, mk_int, lift_aleph0] at h
    exact h.trans hκ
  obtain ⟨l, hl⟩ := hdir (Set.range k) hsize
  let q (i : ℤ) : k i ⟶ l := homOfLE (hl _ ⟨i, rfl⟩)
  let p' : j ⟶ l := p 0 ≫ q 0
  have hp (i : ℤ) : p' = p i ≫ q i := Subsingleton.elim _ _
  refine ⟨l, p', ?_, ?_⟩
  · intro i x hx
    rw [hp i, (F i).map_comp]
    show ((F i).map (q i)) (((F i).map (p i)) x) = 0
    rw [hk i x hx, map_zero]
  · intro i y
    obtain ⟨x, hx⟩ := hsurj i y
    refine ⟨((F i).map (q i)) x, ?_⟩
    calc
      _ = ((G i).map (q i)) (((α i).app (k i)) x) :=
        congrArg (fun h : (F i).obj (k i) ⟶ (G i).obj l => h x) ((α i).naturality (q i))
      _ = ((G i).map (q i)) (((G i).map (p i)) y) := by rw [hx]
      _ = ((G i).map p') y := by rw [hp i, (G i).map_comp]; rfl

/-- The module corresponding to a categorical image is the linear range. -/
private alias subobjectModule_imageSubobject :=
  CochainComplex.Tor.subobjectModule_imageSubobject

/-- Elementwise lifting implies containment of categorical images. -/
private lemma imageSubobject_le_of_forall_exists
    {R : Type u} [Ring R] {X Y Z : ModuleCat.{v} R} (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : ∀ x, ∃ y, g y = f x) : imageSubobject f ≤ imageSubobject g := by
  apply (ModuleCat.subobjectModule Z).le_iff_le.mp
  rw [subobjectModule_imageSubobject, subobjectModule_imageSubobject]
  rintro z ⟨x, rfl⟩
  exact h x

/-- Elementwise vanishing on a kernel is the corresponding zero composite. -/
private lemma kernel_comp_eq_zero_of_forall
    {R : Type u} [Ring R] {X Y Z : ModuleCat.{v} R} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ x, f x = 0 → g x = 0) : kernel.ι f ≫ g = 0 := by
  ext x
  apply h
  exact congrArg (fun k : kernel f ⟶ Y => k x) (kernel.condition f)

/-- The elementwise reading of a vanishing composite with a kernel inclusion: an element killed
by `f` is killed by `g`. The kernel of a map of modules is its linear kernel, through
`ModuleCat.kernelIsoKer`, so the element itself is a value of the kernel inclusion.

This is the converse of `kernel_comp_eq_zero_of_forall`, and it is the form in which the kernel
condition of Stacks 0GYI is consumed: the elementwise statement is the one that transports along
an isomorphism of the modules involved, which is what identifying a stage of an increasing chain
with its image in the union requires. -/
public lemma forall_of_kernel_comp_eq_zero
    {R : Type u} [Ring R] {X Y Z : ModuleCat.{v} R} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : kernel.ι f ≫ g = 0) (x : X) (hx : f x = 0) : g x = 0 := by
  have hz : ModuleCat.ofHom f.hom.ker.subtype ≫ g = 0 := by
    rw [← ModuleCat.kernelIsoKer_inv_kernel_ι f, Category.assoc, h, comp_zero]
  have := congrArg
    (fun k : ModuleCat.of R (LinearMap.ker f.hom) ⟶ Z => k (⟨x, hx⟩ : LinearMap.ker f.hom)) hz
  simpa using this

/-- The elementwise reading of a containment of categorical images: every value of `f` is a
value of `g`. This is the converse of `imageSubobject_le_of_forall_exists`, and is used for the
same reason as `forall_of_kernel_comp_eq_zero`. -/
public lemma forall_exists_of_imageSubobject_le
    {R : Type u} [Ring R] {X Y Z : ModuleCat.{v} R} (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : imageSubobject f ≤ imageSubobject g) (x : X) : ∃ y, g y = f x := by
  have hle := (ModuleCat.subobjectModule Z).le_iff_le.mpr h
  rw [subobjectModule_imageSubobject, subobjectModule_imageSubobject] at hle
  exact hle ⟨x, rfl⟩

section PairComparison

variable {A : Type u} {B : Type v} [Ring A] [Ring B]
  {M : CochainComplex (ModuleCat.{w} A) ℤ} {N : CochainComplex (ModuleCat.{w} B) ℤ}
  {E : CochainComplex (ModuleCat.{w} A) ℤ ⥤ CochainComplex (ModuleCat.{w} B) ℤ}
  {b : E.obj M ⟶ N} {P₀ : SubcomplexFamily M} {Q₀ : SubcomplexFamily N} {κ : Cardinal.{w}}

/-- The restricted map attached to a bounded compatible pair. -/
private noncomputable def pairComparison {P₀ : SubcomplexFamily M} {Q₀ : SubcomplexFamily N}
    (P : BoundedCompatiblePairs E b P₀ Q₀ κ) :
    E.obj P.1.1.toComplex ⟶ P.1.2.toComplex := P.2.2.2.1.choose

private lemma pairComparison_ι {P₀ : SubcomplexFamily M} {Q₀ : SubcomplexFamily N}
    (P : BoundedCompatiblePairs E b P₀ Q₀ κ) :
    E.map P.1.1.ι ≫ b = pairComparison P ≫ P.1.2.ι := P.2.2.2.1.choose_spec

private lemma pairComparison_naturality {P₀ : SubcomplexFamily M} {Q₀ : SubcomplexFamily N}
    {P Q : BoundedCompatiblePairs E b P₀ Q₀ κ}
    (h : P ≤ Q) :
    E.map (SubcomplexFamily.map h.1) ≫ pairComparison Q =
      pairComparison P ≫ SubcomplexFamily.map h.2 := by
  rw [← cancel_mono Q.1.2.ι, Category.assoc, ← pairComparison_ι,
    ← Category.assoc, ← E.map_comp, SubcomplexFamily.map_ι,
    Category.assoc, SubcomplexFamily.map_ι, pairComparison_ι]

end PairComparison

set_option backward.isDefEq.respectTransparency false in
/-- Compatible subcomplexes of quasi-isomorphic complexes after derived base change can be
enlarged, with a bound depending only on the ring map, so that the kernel defect vanishes and the
image defect is covered in every degree. -/
@[stacks 0GYI]
public theorem exists_enlargements_killing_kernel_and_covering_image
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃ κ : Cardinal.{max u v},
      letI : (ModuleCat.extendScalars.{u, v, max v (max u w)} f).IsLeftAdjoint :=
        ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u w} f
      let E : CochainComplex (ModuleCat.{max u v w} A) ℤ ⥤
          CochainComplex (ModuleCat.{max u v w} B) ℤ :=
        (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
          (ComplexShape.up ℤ)
      let G : CochainComplex (ModuleCat.{max u v w} A) ℤ ⥤
          DerivedCategory (ModuleCat.{max u v w} B) :=
        E ⋙ DerivedCategory.Q (C := ModuleCat.{max u v w} B)
      ∀ (T : DerivedCategory (ModuleCat.{max u v w} A) ⥤
          DerivedCategory (ModuleCat.{max u v w} B))
        (α : DerivedCategory.Q (C := ModuleCat.{max u v w} A) ⋙ T ⟶ G)
        [T.IsLeftDerivedFunctor α
          (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ))]
        (M : CochainComplex (ModuleCat.{max u v w} A) ℤ)
        (N : CochainComplex (ModuleCat.{max u v w} B) ℤ),
      ∀ (b : E.obj M ⟶ N),
      IsIso (α.app M ≫
        (DerivedCategory.Q (C := ModuleCat.{max u v w} B)).map b) →
      ∀ (M₁ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
        (N₁ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
        (m₁ : M₁ ⟶ M) (n₁ : N₁ ⟶ N) [Mono m₁] [Mono n₁]
        (b₁ : E.obj M₁ ⟶ N₁),
      E.map m₁ ≫ b = b₁ ≫ n₁ →
      ∃ (M₂ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
        (N₂ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
        (m₂ : M₂ ⟶ M) (n₂ : N₂ ⟶ N) (_ : Mono m₂) (_ : Mono n₂)
        (m₁₂ : M₁ ⟶ M₂) (n₁₂ : N₁ ⟶ N₂) (_ : Mono m₁₂) (_ : Mono n₁₂)
        (b₂ : E.obj M₂ ⟶ N₂),
      m₁₂ ≫ m₂ = m₁ ∧ n₁₂ ≫ n₂ = n₁ ∧ E.map m₂ ≫ b = b₂ ≫ n₂ ∧
      (∀ i : ℤ,
        let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i
        kernel.ι (H.map (α.app M₁ ≫
          (DerivedCategory.Q (C := ModuleCat.{max u v w} B)).map b₁)) ≫
          H.map (T.map
            ((DerivedCategory.Q (C := ModuleCat.{max u v w} A)).map m₁₂)) = 0) ∧
      (∀ i : ℤ,
        let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i
        imageSubobject (H.map
          ((DerivedCategory.Q (C := ModuleCat.{max u v w} B)).map n₁₂)) ≤
          imageSubobject (H.map (α.app M₂ ≫
            (DerivedCategory.Q (C := ModuleCat.{max u v w} B)).map b₂))) ∧
      Cardinal.mk ((Σ i : ℤ, M₂.X i) ⊕ (Σ i : ℤ, N₂.X i)) ≤
        max (Cardinal.lift.{w} κ)
          (Cardinal.mk ((Σ i : ℤ, M₁.X i) ⊕ (Σ i : ℤ, N₁.X i))) := by
  classical
  let κ₀ : Cardinal.{max u v} := max (max (lift.{v} #A) (lift.{u} #B)) ℵ₀
  refine ⟨κ₀, ?_⟩
  dsimp only
  intro T α hT M N b hb M₁ N₁ m₁ n₁ hm₁ hn₁ b₁ hcomm
  let E := (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let QA := DerivedCategory.Q (C := ModuleCat.{max u v w} A)
  let QB := DerivedCategory.Q (C := ModuleCat.{max u v w} B)
  let H (i : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i
  let κ : Cardinal.{max u v w} := max (lift.{w} κ₀)
    #((Σ i, M₁.X i) ⊕ (Σ i, N₁.X i))
  have hκ : ℵ₀ ≤ κ := by
    have h : ℵ₀ ≤ κ₀ := le_max_right _ _
    have h' : ℵ₀ ≤ lift.{w} κ₀ := by
      simpa only [lift_aleph0] using (lift_le.mpr h : lift.{w} ℵ₀ ≤ lift.{w} κ₀)
    exact h'.trans (le_max_left _ _)
  have hA : lift.{max v w} #A ≤ κ := by
    have h : lift.{v} #A ≤ κ₀ := (le_max_left _ _).trans (le_max_left _ _)
    have h' : lift.{max v w} #A ≤ lift.{w} κ₀ := by
      simpa only [lift_lift] using (lift_le.mpr h : lift.{w} (lift.{v} #A) ≤ lift.{w} κ₀)
    exact h'.trans (le_max_left _ _)
  have hB : lift.{max u w} #B ≤ κ := by
    have h : lift.{u} #B ≤ κ₀ := (le_max_right _ _).trans (le_max_left _ _)
    have h' : lift.{max u w} #B ≤ lift.{w} κ₀ := by
      simpa only [lift_lift] using (lift_le.mpr h : lift.{w} (lift.{u} #B) ≤ lift.{w} κ₀)
    exact h'.trans (le_max_left _ _)
  have hsize₁ : #((Σ i, M₁.X i) ⊕ (Σ i, N₁.X i)) ≤ κ := le_max_right _ _
  have hM₁ (i : ℤ) : #(M₁.X i) ≤ κ := (mk_term_le_mk_sum_left i).trans hsize₁
  have hN₁ (i : ℤ) : #(N₁.X i) ≤ κ := (mk_term_le_mk_sum_right i).trans hsize₁
  let J := BoundedCompatiblePairs E b (rangeFamily m₁) (rangeFamily n₁) κ
  have hdir : ∀ s : Set J, #s ≤ κ → ∃ k, ∀ j ∈ s, j ≤ k :=
    boundedCompatiblePairs_directed f M M₁ N N₁ m₁ n₁ b hκ hA hB hM₁ hN₁
  have : IsFiltered J := isFiltered_of_bounded_directed hκ hdir
  obtain ⟨hcoverM, hcoverN⟩ :=
    boundedCompatiblePairs_cover f M M₁ N N₁ m₁ n₁ b hκ hA hB hM₁ hN₁
  let P (j : J) := j.1.1
  let Q (j : J) := j.1.2
  have hP : Monotone P := fun _ _ h => h.1
  have hQ : Monotone Q := fun _ _ h => h.2
  let DM := familyDiagram P hP
  let DN := familyDiagram Q hQ
  let cM := familyCocone P hP
  let cN := familyCocone Q hQ
  have hcM : IsColimit cM := familyIsColimit P hP hcoverM
  have hcN : IsColimit cN := familyIsColimit Q hQ hcoverN
  let F (i : ℤ) := DM ⋙ QA ⋙ T ⋙ H i
  let G (i : ℤ) := DN ⋙ QB ⋙ H i
  let cF (i : ℤ) := (QA ⋙ T ⋙ H i).mapCocone cM
  let cG (i : ℤ) := (QB ⋙ H i).mapCocone cN
  have hcF (i : ℤ) : IsColimit (cF i) := by
    have := derivedBaseChangeHomology_preservesFilteredColimits_ulift f T α (J := J) i
    exact isColimitOfPreserves (QA ⋙ T ⋙ H i) hcM
  have hcG (i : ℤ) : IsColimit (cG i) := by
    have := homology_preservesFilteredColimits.{v, max u w} (R := B) (J := J) i
    have : PreservesColimitsOfShape J (QB ⋙ H i) :=
      preservesColimitsOfShape_of_natIso
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} B) i).symm
    exact isColimitOfPreserves (QB ⋙ H i) hcN
  let γ (i : ℤ) : F i ⟶ G i :=
    { app := fun j => (H i).map (α.app (P j).toComplex ≫ QB.map (pairComparison j))
      naturality := by
        intro j k p
        show (H i).map ((QA ⋙ T).map (SubcomplexFamily.map (leOfHom p).1)) ≫ _ =
          _ ≫ (H i).map (QB.map (SubcomplexFamily.map (leOfHom p).2))
        rw [← (H i).map_comp, ← (H i).map_comp]
        exact congrArg (H i).map (comparison_square α
          (SubcomplexFamily.map (leOfHom p).1) (SubcomplexFamily.map (leOfHom p).2)
          (pairComparison j) (pairComparison k) (pairComparison_naturality (leOfHom p))) }
  let g (i : ℤ) : (cF i).pt ⟶ (cG i).pt := (H i).map (α.app M ≫ QB.map b)
  have : IsIso (α.app M ≫ QB.map b) := hb
  have : ∀ i, IsIso (g i) := fun i => by dsimp [g]; infer_instance
  have hg (i : ℤ) (j : J) :
      (cF i).ι.app j ≫ g i = (γ i).app j ≫ (cG i).ι.app j := by
    show (H i).map ((QA ⋙ T).map (P j).ι) ≫ _ = _ ≫ (H i).map (QB.map (Q j).ι)
    rw [← (H i).map_comp, ← (H i).map_comp]
    exact congrArg (H i).map (comparison_square α (P j).ι (Q j).ι
      (pairComparison j) b (pairComparison_ι j))
  let j₀ : J := ⟨⟨rangeFamily m₁, rangeFamily n₁⟩, le_rfl, le_rfl,
    rangeFamily_compatible E m₁ n₁ b b₁ hcomm,
    (mk_sum_rangeFamily_le m₁ n₁).trans hsize₁⟩
  have hF₀ (i : ℤ) : #((F i).obj j₀) ≤ κ :=
    mk_derivedBaseChange_homology_le_ulift f T α (P j₀).toComplex hκ hA hB
      (fun j => (mk_term_le_mk_sum_left j).trans j₀.2.2.2.2) i
  have hG₀ (i : ℤ) : #((G i).obj j₀) ≤ κ := by
    have e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} B) i).app
      (Q j₀).toComplex
    exact (mk_congr e.toLinearEquiv.toEquiv).le.trans
      ((mk_homology_le_mk_term _ i).trans ((mk_term_le_mk_sum_right i).trans j₀.2.2.2.2))
  obtain ⟨k, p, hkill, hlift⟩ :=
    exists_stage_all_degrees_killing_kernel_and_covering_image F G γ cF cG hcF hcG g hg
      hκ hdir j₀ hF₀ hG₀
  let m₀₁ := toRangeFamily m₁
  let n₀₁ := toRangeFamily n₁
  let m₁₂ : M₁ ⟶ (P k).toComplex := m₀₁ ≫ SubcomplexFamily.map (leOfHom p).1
  let n₁₂ : N₁ ⟶ (Q k).toComplex := n₀₁ ≫ SubcomplexFamily.map (leOfHom p).2
  have hmfac : m₁₂ ≫ (P k).ι = m₁ := by
    rw [Category.assoc, SubcomplexFamily.map_ι, toRangeFamily_ι]
  have hnfac : n₁₂ ≫ (Q k).ι = n₁ := by
    rw [Category.assoc, SubcomplexFamily.map_ι, toRangeFamily_ι]
  have h₀₁ : E.map m₀₁ ≫ pairComparison j₀ = b₁ ≫ n₀₁ := by
    rw [← cancel_mono (Q j₀).ι, Category.assoc, ← pairComparison_ι,
      ← Category.assoc, ← E.map_comp, toRangeFamily_ι,
      Category.assoc, toRangeFamily_ι]
    exact hcomm
  refine ⟨(P k).toComplex, (Q k).toComplex, (P k).ι, (Q k).ι, inferInstance, inferInstance,
    m₁₂, n₁₂, mono_of_mono_fac hmfac, mono_of_mono_fac hnfac, pairComparison k,
    hmfac, hnfac, pairComparison_ι k, ?_, ?_, k.2.2.2.2⟩
  · intro i
    apply kernel_comp_eq_zero_of_forall
    intro x hx
    have hz : ((γ i).app j₀) (((QA ⋙ T ⋙ H i).map m₀₁) x) = 0 := by
      calc
        _ = ((H i).map (QB.map n₀₁)) (((H i).map (α.app M₁ ≫ QB.map b₁)) x) := by
          have hsq :
              (H i).map ((QA ⋙ T).map m₀₁) ≫
                (H i).map (α.app (P j₀).toComplex ≫ QB.map (pairComparison j₀)) =
              (H i).map (α.app M₁ ≫ QB.map b₁) ≫ (H i).map (QB.map n₀₁) := by
            rw [← (H i).map_comp, ← (H i).map_comp]
            exact congrArg (H i).map
              (comparison_square α m₀₁ n₀₁ b₁ (pairComparison j₀) h₀₁)
          exact congrArg
            (fun q : (H i).obj (T.obj (QA.obj M₁)) ⟶
              (H i).obj (QB.obj (Q j₀).toComplex) => q x) hsq
        _ = 0 := by rw [hx, map_zero]
    show ((H i).map (T.map (QA.map m₁₂))) x = 0
    dsimp only [m₁₂]
    rw [QA.map_comp, T.map_comp, (H i).map_comp]
    exact hkill i _ hz
  · intro i
    apply imageSubobject_le_of_forall_exists
    intro y
    obtain ⟨x, hx⟩ := hlift i (((H i).map (QB.map n₀₁)) y)
    refine ⟨x, ?_⟩
    show ((γ i).app k) x = ((H i).map (QB.map n₁₂)) y
    dsimp only [n₁₂]
    rw [QB.map_comp, (H i).map_comp]
    exact hx

end Stacks.SubcomplexEnlargement

end
