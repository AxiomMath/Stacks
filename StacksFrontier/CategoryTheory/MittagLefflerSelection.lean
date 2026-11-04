module

public import StacksFrontier.CategoryTheory.MittagLefflerSections

/-!
# Choosing a compatible family of good morphisms through the Mittag-Leffler condition

Let `Y` and `Z` be towers (functors `ℕᵒᵖ ⥤ K`) in a category `K`, and suppose that for every `n`
there are morphisms `Y_j ⟶ Z_j`, for `j ≤ n`, which are compatible with the transition maps and
"good" (they lie in a class `W`), the family depending on `n`. When are there good morphisms
`Y_j ⟶ Z_j` compatible for all `j` at once, that is a natural transformation `Y ⟶ Z` with good
components? This is the argument of Stacks 09C6: if `Y` is a tower of quotients of a fixed object
`X` (maps out of `Y_j` into the relevant targets are the maps out of `X`), if postcomposition with
good morphisms is bijective on maps out of `X`, and if the system of sets `j ↦ Hom(X, Y_j)` is
Mittag-Leffler, then so is `j ↦ Hom(X, Z_j)`; its eventual image at one level contains a good
morphism, which therefore lifts to a compatible family; and a Nakayama-type hypothesis upgrades
goodness at one level to goodness at all levels.

## Main results

* `CategoryTheory.Functor.isMittagLeffler_of_forall_le_surjective`: the Mittag-Leffler condition
  for systems of sets passes along levelwise surjections of truncations.
* `CategoryTheory.Functor.exists_mem_sections_of_mem_eventualRange`: for a Mittag-Leffler system
  over `ℕᵒᵖ`, every element of an eventual range is the value of a section.
* `CategoryTheory.Functor.exists_natTrans_forall_of_isMittagLeffler`: the selection argument.

## References

* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
* [Stacks Project, Tag 0598](https://stacks.math.columbia.edu/tag/0598)
-/

@[expose] public section

universe u v u' v'

open CategoryTheory Opposite

namespace CategoryTheory.Functor

/-- Every morphism in `ℕᵒᵖ` is `(homOfLE h).op` for a proof `h` of the corresponding inequality. -/
private theorem exists_eq_homOfLE_op {a b : ℕᵒᵖ} (f : a ⟶ b) :
    ∃ h : b.unop ≤ a.unop, f = (homOfLE h).op :=
  ⟨leOfHom f.unop, Subsingleton.elim _ _⟩

/-- **The Mittag-Leffler condition through levelwise surjections.** If `G` is a Mittag-Leffler
system of sets and for every `n` there are surjections from the truncation of `G` to the indices
`j ≤ n` onto that of `F`, compatible with the transition maps (the surjections depending on `n`),
then `F` is Mittag-Leffler. -/
theorem isMittagLeffler_of_forall_le_surjective {F : ℕᵒᵖ ⥤ Type u} {G : ℕᵒᵖ ⥤ Type v}
    (hG : G.IsMittagLeffler)
    (h : ∀ n : ℕ, ∃ e : ∀ j : ℕ, j ≤ n → G.obj (op j) → F.obj (op j),
      (∀ j hj, Function.Surjective (e j hj)) ∧
        ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) (x : G.obj (op j)),
          e i (hij.trans hjn) (G.map (homOfLE hij).op x) = F.map (homOfLE hij).op (e j hjn x)) :
    F.IsMittagLeffler := by
  intro a
  obtain ⟨c, f, hf⟩ := hG a
  obtain ⟨hac, rfl⟩ := exists_eq_homOfLE_op f
  refine ⟨c, (homOfLE hac).op, fun k g => ?_⟩
  obtain ⟨had, rfl⟩ := exists_eq_homOfLE_op g
  rintro x ⟨y, rfl⟩
  obtain ⟨e, he, hcomm⟩ := h (max c.unop k.unop)
  have hcn : c.unop ≤ max c.unop k.unop := le_max_left _ _
  have hkn : k.unop ≤ max c.unop k.unop := le_max_right _ _
  obtain ⟨y', rfl⟩ := he c.unop hcn y
  obtain ⟨z, hz⟩ := hf (homOfLE had).op ⟨y', rfl⟩
  refine ⟨e k.unop hkn z, ?_⟩
  change F.map (homOfLE had).op (e k.unop hkn z) = F.map (homOfLE hac).op (e c.unop hcn y')
  rw [← hcomm a.unop k.unop had hkn z, ← hcomm a.unop c.unop hac hcn y']
  exact congrArg _ hz

/-- **Elements of the eventual range lift to sections.** For a Mittag-Leffler system of sets
indexed by `ℕᵒᵖ`, every element of the eventual range at some level is the value at that level
of a section. -/
theorem exists_mem_sections_of_mem_eventualRange {F : ℕᵒᵖ ⥤ Type u} (hF : F.IsMittagLeffler)
    {i : ℕᵒᵖ} {x : F.obj i} (hx : x ∈ F.eventualRange i) :
    ∃ s ∈ F.sections, s i = x := by
  let G := F.toEventualRanges
  have hGsurj : ∀ ⦃j k : ℕᵒᵖ⦄ (g : j ⟶ k), Function.Surjective (G.map g) :=
    fun _ _ g => F.surjective_toEventualRanges hF g
  let x' : G.obj i := ⟨x, hx⟩
  have : ∀ j : ℕᵒᵖ, Nonempty (G.obj j) := by
    intro j
    rcases le_total j.unop i.unop with h | h
    · exact ⟨G.map (homOfLE h).op x'⟩
    · exact ⟨(hGsurj (homOfLE h).op x').choose⟩
  let sx : Set (G.obj i) := {x'}
  obtain ⟨s⟩ := nonempty_sections_of_isMittagLeffler
    (IsMittagLeffler.toPreimages G sx (isMittagLeffler_of_surjective G hGsurj))
    (G.toPreimages_nonempty_of_surjective sx hGsurj (Set.singleton_nonempty x'))
  refine ⟨fun j => ((s.1 j).1).1, fun {j k} g => ?_, ?_⟩
  · exact congrArg (fun y => y.1.1) (s.2 g)
  · have hmem := (s.1 i).2
    simp only [sx, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hmem
    have := hmem (𝟙 i)
    rw [G.map_id] at this
    exact congrArg Subtype.val this

/-- **Selection of a compatible family of good morphisms.** Let `W` be a class of morphisms of
`K`, let `Y`, `Z` be towers in `K` and `p : X ⟶ Y` a cone such that every map `Y_j ⟶ Z_i`,
`i ≤ j`, is determined by its composite with `p_j`, and every map `X ⟶ Z_j` factors through
`p_j`. Suppose postcomposition with a morphism of `W` is bijective on maps out of `X`; for every
`n` there is a compatible family of morphisms `Y_j ⟶ Z_j` in `W` for `j ≤ n`; the system
`j ↦ Hom(X, Y_j)` is Mittag-Leffler; every morphism `Y_j ⟶ Z_j` is in `W` for `j < i₀`; and a
morphism `Y_j ⟶ Z_j`, `j ≥ i₀`, compatible with a morphism of `W` at the level `i₀` is in `W`.
Then there is a natural transformation `Y ⟶ Z` all of whose components are in `W`. -/
theorem exists_natTrans_forall_of_isMittagLeffler {K : Type u'} [Category.{v'} K]
    (W : MorphismProperty K) {X : K} {Y Z : ℕᵒᵖ ⥤ K} (p : (Functor.const ℕᵒᵖ).obj X ⟶ Y)
    (hp : ∀ i j : ℕ, i ≤ j → Function.Bijective
      (fun φ : Y.obj (op j) ⟶ Z.obj (op i) => p.app (op j) ≫ φ))
    (hX : ∀ {V V' : K} (w : V ⟶ V'), W w → Function.Bijective (fun ψ : X ⟶ V => ψ ≫ w))
    (hw : ∀ n : ℕ, ∃ w : ∀ j : ℕ, j ≤ n → (Y.obj (op j) ⟶ Z.obj (op j)),
      (∀ j hj, W (w j hj)) ∧ ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n),
        Y.map (homOfLE hij).op ≫ w i (hij.trans hjn) = w j hjn ≫ Z.map (homOfLE hij).op)
    (hML : (Y ⋙ coyoneda.obj (op X)).IsMittagLeffler) (i₀ : ℕ)
    (hlow : ∀ j < i₀, ∀ φ : Y.obj (op j) ⟶ Z.obj (op j), W φ)
    (hNak : ∀ (j : ℕ) (h : i₀ ≤ j) (φ : Y.obj (op j) ⟶ Z.obj (op j))
      (ψ : Y.obj (op i₀) ⟶ Z.obj (op i₀)), W ψ →
        Y.map (homOfLE h).op ≫ ψ = φ ≫ Z.map (homOfLE h).op → W φ) :
    ∃ φ : Y ⟶ Z, ∀ j, W (φ.app (op j)) := by
  let FZ := Z ⋙ coyoneda.obj (op X)
  have hpnat : ∀ {a b : ℕ} (h : a ≤ b), p.app (op b) ≫ Y.map (homOfLE h).op = p.app (op a) :=
    fun h => by simpa using (p.naturality (homOfLE h).op).symm
  have hFZ : FZ.IsMittagLeffler := by
    refine isMittagLeffler_of_forall_le_surjective (F := FZ) (G := Y ⋙ coyoneda.obj (op X))
      hML fun n => ?_
    obtain ⟨w, hwW, hwc⟩ := hw n
    refine ⟨fun j hj ψ => ψ ≫ w j hj, fun j hj => (hX _ (hwW j hj)).2, ?_⟩
    intro i j hij hjn ψ
    change (ψ ≫ Y.map (homOfLE hij).op) ≫ w i (hij.trans hjn) =
      (ψ ≫ w j hjn) ≫ Z.map (homOfLE hij).op
    rw [Category.assoc, Category.assoc, hwc i j hij hjn]
  obtain ⟨c, f, hc⟩ := (FZ.isMittagLeffler_iff_eventualRange).1 hFZ (op i₀)
  obtain ⟨hic, rfl⟩ := exists_eq_homOfLE_op f
  obtain ⟨w, hwW, hwc⟩ := hw c.unop
  have hmem : p.app (op i₀) ≫ w i₀ hic ∈ FZ.eventualRange (op i₀) := by
    rw [hc]
    refine ⟨p.app c ≫ w c.unop le_rfl, ?_⟩
    change (p.app c ≫ w c.unop le_rfl) ≫ Z.map (homOfLE hic).op = _
    rw [Category.assoc, ← hwc i₀ c.unop hic le_rfl, ← Category.assoc]
    exact congrArg (· ≫ _) (hpnat hic)
  obtain ⟨s, hs, hsi⟩ := exists_mem_sections_of_mem_eventualRange hFZ hmem
  have hfac : ∀ j : ℕ, ∃ φ : Y.obj (op j) ⟶ Z.obj (op j), p.app (op j) ≫ φ = s (op j) :=
    fun j => (hp j j le_rfl).2 (s (op j))
  choose φ hφ using hfac
  have hnat : ∀ (i j : ℕ) (hij : i ≤ j),
      Y.map (homOfLE hij).op ≫ φ i = φ j ≫ Z.map (homOfLE hij).op := by
    intro i j hij
    refine (hp i j hij).1 ?_
    change p.app (op j) ≫ Y.map (homOfLE hij).op ≫ φ i =
      p.app (op j) ≫ φ j ≫ Z.map (homOfLE hij).op
    rw [← Category.assoc, hpnat hij, hφ, ← Category.assoc, hφ]
    exact (hs (homOfLE hij).op).symm
  refine ⟨{ app := fun j => φ j.unop, naturality := fun j k g => ?_ }, fun j => ?_⟩
  · obtain ⟨hkj, rfl⟩ := exists_eq_homOfLE_op g
    exact hnat k.unop j.unop hkj
  · change W (φ j)
    rcases lt_or_ge j i₀ with h | h
    · exact hlow j h _
    · have hi₀ : W (φ i₀) := by
        rw [(hp i₀ i₀ le_rfl).1 ((hφ i₀).trans hsi)]
        exact hwW i₀ hic
      exact hNak j h (φ j) (φ i₀) hi₀ (hnat i₀ j h)

end CategoryTheory.Functor
