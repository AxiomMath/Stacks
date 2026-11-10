module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGraphSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EventualIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremFiniteFactorization
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Zariski's main theorem for algebraic spaces with a finitely presented compactification

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, with `Y` quasi-compact and
quasi-separated, and let `X --j--> T --π--> Y` be a factorization of `f` with `j` a
quasi-compact open immersion and `π` finite, as Zariski's main theorem (Stacks 082K) provides
for `f` quasi-finite and separated.  Stacks 0874 says that when `f` is moreover locally of
finite presentation the factorization can be chosen with `T` finite *and of finite
presentation* over `Y`.

The proof is the source's.  By Stacks 07VR, `T = lim T_i` for a directed inverse system of
algebraic spaces `T_i` finite and of finite presentation over `Y`, with closed immersions as
transition morphisms.  The quasi-compact open `j(X) ⊆ T` is the inverse image of a
quasi-compact open `U_i ⊆ T_i`, the inverse images `U_{i'} ⊆ T_{i'}` for `i' ≥ i` form an
inverse system with limit `j(X) ≅ X`, and Stacks 0828, part (3), makes `X ⟶ U_{i'}` an
isomorphism for large `i'`.  Then `X ⟶ T_{i'}` is a quasi-compact open immersion and
`T_{i'} ⟶ Y` is finite and of finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_isOpen_isCompact_preimage_eq_of_isClosedEmbedding`: a compact
  open subset of the source of a closed embedding into a space with a basis of compact open
  neighbourhoods is the preimage of a compact open subset of the target.
* `AlgebraicGeometry.Space.mono_π_of_mono_map`: the projections out of a cofiltered limit along
  monomorphisms are monomorphisms.
* `AlgebraicGeometry.Space.final_subtype_le`: the stages of a directed preorder above a fixed
  one are final.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isFinitePresentation_of_factorization`:
  **Stacks 0874**, granted Stacks 07VR, for a given factorization of Stacks 082K.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite`:
  **Stacks 0874** as stated, granted Stacks 07VR.

## Implementation notes

The descent of the open `j(X)` to a stage is done on points rather than by Stacks 0827, whose
statement bounds the size of the index category: the index set of Stacks 07VR carries no such
bound.  It is not needed here, because the projection `T ⟶ T_i` is a closed immersion — it is
finite, as `T ⟶ T_i ⟶ Y` is finite and `T_i ⟶ Y` is separated, and a monomorphism, as a limit
of monomorphisms — so `|T| ⟶ |T_i|` is a closed embedding and the complement of the image of
`|T| ∖ |j(X)|` is an open subset of `|T_i|` with preimage `|j(X)|`; it is shrunk to a
quasi-compact one around the compact image of `|j(X)|`.

The limit of the inverse system `(U_{i'})_{i' ≥ i}` is identified with `j(X)` by restricting
the limit presentation of `T` to the stages above `i`, which is again a limit presentation
because that inclusion of index categories is initial.

## References

* [Stacks Project, Tag 0874](https://stacks.math.columbia.edu/tag/0874)
* [Stacks Project, Tag 082K](https://stacks.math.columbia.edu/tag/082K)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Filter Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### A compact open set descends along a closed embedding -/

/-- **A compact open subset of the source of a closed embedding is the preimage of a compact
open subset of the target**, when every point of the target has a basis of compact open
neighbourhoods.  The complement of the image of the complement is an open subset of the target
with the given preimage; it is shrunk around the compact image of the given set to a finite
union of compact open neighbourhoods. -/
theorem exists_isOpen_isCompact_preimage_eq_of_isClosedEmbedding {P Q : Type*}
    [TopologicalSpace P] [TopologicalSpace Q] {g : P → Q} (hg : IsClosedEmbedding g)
    (hbasis : ∀ q : Q, (𝓝 q).HasBasis (fun W : Set Q ↦ IsOpen W ∧ IsCompact W ∧ q ∈ W) id)
    {A : Set P} (hAo : IsOpen A) (hAc : IsCompact A) :
    ∃ V : Set Q, IsOpen V ∧ IsCompact V ∧ g ⁻¹' V = A := by
  classical
  set O : Set Q := (g '' Aᶜ)ᶜ with hOdef
  have hOo : IsOpen O := (hg.isClosedMap _ hAo.isClosed_compl).isOpen_compl
  have hgO : g ⁻¹' O = A := by
    rw [hOdef, Set.preimage_compl, hg.injective.preimage_image, compl_compl]
  have hgA : g '' A ⊆ O := Set.image_subset_iff.mpr hgO.ge
  have hshrink : ∀ q ∈ g '' A, ∃ K : Set Q, (IsOpen K ∧ IsCompact K ∧ q ∈ K) ∧ K ⊆ O :=
    fun q hq ↦ (hbasis q).mem_iff.mp (hOo.mem_nhds (hgA hq))
  choose! K hK hKO using hshrink
  obtain ⟨t, htA, htcover⟩ := (hAc.image hg.continuous).elim_nhds_subcover K
    fun q hq ↦ (hK q hq).1.mem_nhds (hK q hq).2.2
  refine ⟨⋃ q ∈ t, K q, isOpen_biUnion fun q hq ↦ (hK q (htA q hq)).1,
    t.isCompact_biUnion fun q hq ↦ (hK q (htA q hq)).2.1, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rw [← hgO]
    exact Set.preimage_mono (Set.iUnion₂_subset fun q hq ↦ hKO q (htA q hq))
  · exact Set.image_subset_iff.mp htcover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Monomorphisms and closed immersions -/

/-- If every transition morphism of a cofiltered inverse system is a monomorphism, so is every
projection out of a limit of it. -/
theorem mono_π_of_mono_map {J : Type*} [Category J] [IsCofiltered J] {C : Type*} [Category C]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) (hmono : ∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (D.map f))
    (i : J) : Mono (c.π.app i) := by
  refine ⟨fun a b hab ↦ hc.hom_ext fun j ↦ ?_⟩
  have := hmono (IsCofiltered.minToLeft i j)
  have hk : a ≫ c.π.app (IsCofiltered.min i j) = b ≫ c.π.app (IsCofiltered.min i j) := by
    apply (cancel_mono (D.map (IsCofiltered.minToLeft i j))).1
    simpa only [Category.assoc, c.w] using hab
  simpa only [← c.w (IsCofiltered.minToRight i j), Category.assoc] using
    congrArg (fun z => z ≫ D.map (IsCofiltered.minToRight i j)) hk

/-- The projections out of a limit presentation of a finite morphism along closed immersions are
closed immersions: they are finite, and monomorphisms as limits of monomorphisms. -/
theorem isClosedImmersion_limitCone_app {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (P : IntegralFiniteSystem B S hS f)
    (hcl : letI := P.indexPreorder
      ∀ (i j : P.indexType) (h : i ≤ j), IsClosedImmersion B S hS (P.diagram.map (homOfLE h).op))
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (hf : IsFinite B S hS f)
    (i : P.indexTypeᵒᵖ) :
    letI := P.indexPreorder
    IsClosedImmersion B S hS (P.limitCone.app i) := by
  let := P.indexPreorder
  let := P.indexNonempty
  let := P.indexDirected
  have hmonoD : ∀ ⦃a b : P.indexTypeᵒᵖ⦄ (g : a ⟶ b), Mono (P.diagram.map g) := by
    intro a b g
    have hle : b.unop ≤ a.unop := leOfHom g.unop
    rw [show g = (homOfLE hle).op from Subsingleton.elim _ _]
    exact mono_of_isClosedImmersion B S hS _ (hcl _ _ hle)
  have : Mono (P.limitCone.app i) := mono_π_of_mono_map P.isLimit hmonoD i
  have hsep : IsSeparated B S hS (P.structureMap.app i) :=
    isSeparated_of_isFinite B S hS _ (P.stageAlgebraicSpace i) hY (P.stageFinite i)
  have hfin : IsFinite B S hS (P.limitCone.app i) :=
    isFinite_of_comp_of_isSeparated B S hS _ _ (by rwa [← P.compatible i]) hsep
  have hr := ((isFinite_iff_representable B S hS _ hX (P.stageAlgebraicSpace i)).mp hfin).2
  refine isClosedImmersion_of_mono_of_charts B S hS _ inferInstance ?_ ?_ <;>
    exact MorphismProperty.relative_monotone (F := yoneda)
      (fun _ _ g (_ : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g)) =>
        by dsimp only [MorphismProperty.inverseImage]; infer_instance) _ hr

/-- The corestriction of a monomorphism of presheaves of types to a subfunctor equal to its range
is an isomorphism. -/
theorem isIso_subfunctorLift_of_range_eq {C : Type*} [Category C] {F G : C ⥤ Type u} (j : F ⟶ G)
    [Mono j] {W : Subfunctor G} (h : Subfunctor.range j = W) : IsIso (Subfunctor.lift j h.le) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro a
  rw [isIso_iff_bijective]
  refine ⟨fun x y hxy => ?_, fun w => ?_⟩
  · have hinj := (NatTrans.mono_iff_mono_app j).1 inferInstance a
    rw [mono_iff_injective] at hinj
    exact hinj (congrArg Subtype.val hxy)
  · obtain ⟨x, hx⟩ : w.1 ∈ (Subfunctor.range j).obj a := by rw [h]; exact w.2
    exact ⟨x, Subtype.ext hx⟩

/-! ### The stages above a fixed stage -/

/-- The stages of a directed preorder above a fixed one form a directed preorder. -/
instance isDirected_subtype_le {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I) :
    IsDirected {k : I // i₀ ≤ k} (· ≤ ·) where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-- The inclusion of the stages above a fixed one into a directed preorder is final. -/
theorem final_subtype_le {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I) :
    (Subtype.mono_coe (fun k : I ↦ i₀ ≤ k)).functor.Final := by
  have : Nonempty {k : I // i₀ ≤ k} := ⟨⟨i₀, le_rfl⟩⟩
  refine Functor.final_of_exists_of_isFiltered _ (fun d ↦ ?_) (fun {d c} s s' ↦ ?_)
  · obtain ⟨c, hd, h₀⟩ := directed_of (· ≤ ·) d i₀
    exact ⟨⟨c, h₀⟩, ⟨homOfLE hd⟩⟩
  · exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

/-! ### Subfunctors cut out as inverse images -/

/-- The corestriction to `B` of the composite of the inclusion of `A` with `g` is a base change
of the inclusion of `B` along `g`, when `A` is the inverse image of `B` along `g`. -/
theorem isPullback_lift_of_eq_preimage {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G)
    {A : Subfunctor F} {B' : Subfunctor G} (h : A = B'.preimage g) :
    IsPullback (Subfunctor.lift (A.ι ≫ g) (by
        subst h
        rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff])) A.ι B'.ι g := by
  subst h
  exact CategoryTheory.Subfunctor.isPullback_preimage g B'

/-- The point set of a subfunctor equal to the one cut out by a set of points is that set. -/
theorem range_pointsMap_ι_of_eq_openSubspaceOfPoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : Subfunctor F} {W : Set (points B S hS F)} (h : G = openSubspaceOfPoints B S hS F W) :
    Set.range (pointsMap B S hS G.toFunctor G.ι) = W := by
  subst h
  exact range_pointsMap_ι_openSubspaceOfPoints B S hS W

/-! ### Stacks 0874 -/

/-- **Stacks 0874, granted Stacks 07VR.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is locally of finite presentation, with `Y` quasi-compact and quasi-separated,
and let `f = π ∘ j` with `j : X ⟶ T` a quasi-compact open immersion and `π : T ⟶ Y` finite, as
in Stacks 082K.  Then `f` also factors as `π' ∘ j'` with `j' : X ⟶ T'` a quasi-compact open
immersion and `π' : T' ⟶ Y` finite and of finite presentation.

The hypothesis `h07VR` is the statement of Stacks 07VR: a finite morphism to a quasi-compact
quasi-separated algebraic space presents its source as a directed limit of spaces finite and of
finite presentation over the target, along closed immersions.  `T'` is one of the stages of that
presentation of `T`. -/
theorem exists_isOpenImmersion_isFinitePresentation_of_factorization
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (j : X ⟶ T) (π : T ⟶ Y) (hj : IsOpenImmersion B S hS j) (hjqc : IsQuasiCompact B S hS j)
    (hπ : IsFinite B S hS π) (hfac : j ≫ π = f) :
    ∃ (T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j' : X ⟶ T') (π' : T' ⟶ Y),
      IsAlgebraicSpace B S hS T' ∧ IsOpenImmersion B S hS j' ∧ IsQuasiCompact B S hS j' ∧
        IsFinite B S hS π' ∧ IsFinitePresentation B S hS π' ∧ j' ≫ π' = f := by
  classical
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  -- Stacks 07VR: `T = lim T_i` along closed immersions.
  obtain ⟨P, hcl⟩ := h07VR π hT hY hπ hYqc hYqs
  let := P.indexPreorder
  let := P.indexNonempty
  let := P.indexDirected
  set D := P.diagram
  set lc := P.limitCone
  have hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i) := P.stageAlgebraicSpace
  -- The projections `T ⟶ T_i` are closed immersions.
  have hclπ : ∀ i, IsClosedImmersion B S hS (lc.app i) :=
    isClosedImmersion_limitCone_app P hcl hT hY hπ
  have hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (D.obj i) := fun i =>
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (hDalg i) hYqs
      (P.stageFinitePresentation i).2.2
  -- Quasi-compactness of `X`.
  let i₀ : P.indexType := Classical.arbitrary _
  have hTi₀qc : IsQuasiCompactSpace B S hS (D.obj (op i₀)) :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc
      (P.stageFinitePresentation (op i₀)).2.1
  have hTqc : IsQuasiCompactSpace B S hS T :=
    isQuasiCompactSpace_of_isClosedImmersion B S hS hTi₀qc _ (hclπ (op i₀))
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hT hTqc hjqc
  -- The open `j(X)` descends to a quasi-compact open `U ⊆ T_{i₀}`.
  have : CompactSpace (points B S hS X) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).mp hXqc
  obtain ⟨U₁, hU₁o, hU₁c, hU₁pre⟩ := exists_isOpen_isCompact_preimage_eq_of_isClosedEmbedding
    (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS (hDalg _) (hclπ (op i₀)))
    (hasBasis_nhds_isOpen_isCompact B S hS _ (hDalg (op i₀)))
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS j hj)
    (isCompact_range (continuous_pointsMap B S hS j))
  set U := openSubspaceOfPoints B S hS (D.obj (op i₀)) U₁ with hUdef
  set W := U.preimage (lc.app (op i₀)) with hWdef
  have hW : W = Subfunctor.range j := by
    rw [hWdef, hUdef, preimage_openSubspaceOfPoints, hU₁pre,
      range_eq_openSubspaceOfPoints_of_isOpenImmersion_of_isAlgebraicSpace B S hS hX hj]
    rfl
  -- The inverse system `(U_k)_{k ≥ i₀}` of the inverse images of `U`.
  let tr : ∀ k : {k : P.indexType // i₀ ≤ k}, op k.1 ⟶ op i₀ := fun k => (homOfLE k.2).op
  let V : ∀ k : {k : P.indexType // i₀ ≤ k}, Subfunctor (D.obj (op k.1)) :=
    fun k => U.preimage (D.map (tr k))
  have hVpts : ∀ k, V k = openSubspaceOfPoints B S hS (D.obj (op k.1))
      (pointsMap B S hS _ (D.map (tr k)) ⁻¹' U₁) := fun k =>
    preimage_openSubspaceOfPoints B S hS _ _
  have hVopen : ∀ k, IsOpenSubspace B S hS (V k) := fun k => by
    rw [hVpts k]
    exact isOpenSubspace_openSubspaceOfPoints B S hS (hDalg _) _
      (hU₁o.preimage (continuous_pointsMap B S hS _))
  have hVpre : ∀ {k l : {k : P.indexType // i₀ ≤ k}} (h : l ≤ k),
      V k = (V l).preimage (D.map (homOfLE h).op) := by
    intro k l h
    change U.preimage (D.map (tr k)) = (U.preimage (D.map (tr l))).preimage _
    rw [← Subfunctor.preimage_comp, ← D.map_comp]
    congr 2
  let Dm : ∀ {k l : {k : P.indexType // i₀ ≤ k}} (_ : l ≤ k),
      (V k).toFunctor ⟶ (V l).toFunctor := fun {k l} h =>
    Subfunctor.lift ((V k).ι ≫ D.map (homOfLE h).op) (by
      rw [hVpre h, Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff])
  have hDm : ∀ {k l : {k : P.indexType // i₀ ≤ k}} (h : l ≤ k),
      Dm h ≫ (V l).ι = (V k).ι ≫ D.map (homOfLE h).op := fun _ => rfl
  let D' : {k : P.indexType // i₀ ≤ k}ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    { obj := fun k => (V k.unop).toFunctor
      map := fun {k l} g => Dm (leOfHom g.unop)
      map_id := fun k => by
        rw [← cancel_mono (V k.unop).ι, hDm, Category.id_comp]
        rw [show (homOfLE (leOfHom (𝟙 k).unop)).op = 𝟙 (op k.unop.1) from
          Subsingleton.elim _ _, D.map_id, Category.comp_id]
      map_comp := fun {k l m} g g' => by
        rw [← cancel_mono (V m.unop).ι, Category.assoc, hDm, hDm, ← Category.assoc, hDm,
          Category.assoc, ← D.map_comp]
        congr 2 }
  -- The cone over the system with apex `W = j(X)`.
  have hlcw : ∀ {a b : P.indexTypeᵒᵖ} (g : a ⟶ b), lc.app a ≫ D.map g = lc.app b :=
    fun g ↦ (Cone.mk T lc).w g
  have hWV : ∀ k : {k : P.indexType // i₀ ≤ k},
      Subfunctor.range (W.ι ≫ lc.app (op k.1)) ≤ V k := by
    intro k
    rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff]
    change U.preimage (lc.app (op i₀)) ≤ (U.preimage (D.map (tr k))).preimage (lc.app (op k.1))
    rw [← Subfunctor.preimage_comp, hlcw]
  let cW : Cone D' :=
    { pt := W.toFunctor
      π :=
        { app := fun k => Subfunctor.lift (W.ι ≫ lc.app (op k.unop.1)) (hWV k.unop)
          naturality := fun {k l} g => by
            rw [← cancel_mono (V l.unop).ι]
            change _ = _ ≫ Dm (leOfHom g.unop) ≫ (V l.unop).ι
            rw [hDm]
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Subfunctor.lift_ι, Subfunctor.lift_ι_assoc, Category.assoc, hlcw] } }
  -- It is a limit cone: the restriction of the limit presentation of `T` to the stages above
  -- `i₀` is a limit presentation, and a cone over `D'` lands in `W`.
  let incl := (Subtype.mono_coe (fun k : P.indexType ↦ i₀ ≤ k)).functor
  have : incl.Final := final_subtype_le i₀
  have hlimR : IsLimit ((Cone.mk T lc).whisker incl.op) :=
    (Functor.Initial.isLimitWhiskerEquiv incl.op (Cone.mk T lc)).symm P.isLimit
  let ιN : D' ⟶ incl.op ⋙ D :=
    { app := fun k => (V k.unop).ι
      naturality := fun {k l} g => hDm (leOfHom g.unop) }
  have hlift : ∀ s : Cone D', Subfunctor.range
      (hlimR.lift (Cone.mk s.pt (s.π ≫ ιN))) ≤ W := by
    intro s
    let k₀ : {k : P.indexType // i₀ ≤ k} := ⟨i₀, le_rfl⟩
    rw [hWdef, ← Subfunctor.preimage_eq_top_iff, ← Subfunctor.preimage_comp]
    have hfac' : hlimR.lift (Cone.mk s.pt (s.π ≫ ιN)) ≫ lc.app (op i₀) =
        s.π.app (op k₀) ≫ (V k₀).ι := hlimR.fac (Cone.mk s.pt (s.π ≫ ιN)) (op k₀)
    have htop : U.preimage (V k₀).ι = ⊤ := by
      rw [Subfunctor.preimage_eq_top_iff, Subfunctor.range_ι]
      change U.preimage (D.map (homOfLE (le_refl i₀)).op) ≤ U
      rw [show (homOfLE (le_refl i₀)).op = 𝟙 (op i₀) from Subsingleton.elim _ _, D.map_id,
        Subfunctor.preimage_id]
    rw [hfac', Subfunctor.preimage_comp, htop, Subfunctor.preimage_eq_top_iff]
    exact le_top
  have hlim : IsLimit cW :=
    { lift := fun s => Subfunctor.lift (hlimR.lift (Cone.mk s.pt (s.π ≫ ιN))) (hlift s)
      fac := fun s k => by
        rw [← cancel_mono (V k.unop).ι]
        have := hlimR.fac (Cone.mk s.pt (s.π ≫ ιN)) k
        simp only [cW, Subfunctor.lift_ι, Category.assoc, Subfunctor.lift_ι_assoc]
        exact this
      uniq := fun s m hm => by
        rw [← cancel_mono W.ι, Subfunctor.lift_ι]
        refine hlimR.hom_ext fun k => ?_
        rw [hlimR.fac]
        change _ = s.π.app k ≫ (V k.unop).ι
        rw [← hm k]
        simp only [cW, Category.assoc, Subfunctor.lift_ι]
        rfl }
  -- `X ⟶ W` is an isomorphism.
  let fW : X ⟶ W.toFunctor := Subfunctor.lift j (by rw [hW])
  have : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hfW : IsIso fW := isIso_subfunctorLift_of_range_eq j hW.symm
  -- The data of Stacks 0828, part (3), for the system `(U_k)_{k ≥ i₀}` over `Y`.
  let t' : D' ⟶ (Functor.const _).obj Y :=
    { app := fun k => (V k.unop).ι ≫ P.structureMap.app (op k.unop.1)
      naturality := fun {k l} g => by
        have hn := P.structureMap.naturality
          (homOfLE (show l.unop.1 ≤ k.unop.1 from leOfHom g.unop)).op
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hn ⊢
        change Dm (leOfHom g.unop) ≫ (V l.unop).ι ≫ _ = _
        rw [← Category.assoc, hDm, Category.assoc]
        exact congrArg (fun z => (V k.unop).ι ≫ z) hn }
  have hcommutes : cW.π ≫ t' = (Functor.const _).map (W.ι ≫ π) := by
    ext1
    funext k
    simp only [cW, t', NatTrans.comp_app, Functor.const_map_app, Subfunctor.lift_ι_assoc,
      Category.assoc]
    rw [← P.compatible]
  have hVqc : ∀ k, IsQuasiCompactSpace B S hS (V k).toFunctor := by
    intro k
    refine isQuasiCompactSpace_of_isCompact_range B S hS (hDalg _) (hVopen k) ?_
    rw [range_pointsMap_ι_of_eq_openSubspaceOfPoints (hVpts k)]
    exact (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS (hDalg _)
      (hcl _ _ k.2)).isCompact_preimage hU₁c
  have hev := eventually_isIso_comp_limitπ B S hS Y hY D' (fun k => (hVopen k).1) t' cW hlim
    (W.ι ≫ π) hcommutes X hX fW hfW (fun k => hVqc k)
    (fun k => isLocallyOfFiniteType_comp B S hS (hVopen k).1 (hDalg _) hY _ _
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS (hVopen k).2))
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (P.stageFinitePresentation _).1))
    (fun k l h => (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_lift_of_eq_preimage _ (hVpre h)).flip (hcl _ _ h))
    (by rwa [Subfunctor.lift_ι_assoc, hfac])
  obtain ⟨k, hk⟩ := hev.exists
  -- `X ⟶ T_k` is the isomorphism `X ⟶ U_k` followed by the inclusion of `U_k`.
  have hj' : j ≫ lc.app (op k.1) = (fW ≫ cW.π.app (op k)) ≫ (V k).ι := by
    simp only [cW, fW, Category.assoc, Subfunctor.lift_ι, Subfunctor.lift_ι_assoc]
  refine ⟨D.obj (op k.1), j ≫ lc.app (op k.1), P.structureMap.app (op k.1), hDalg _, ?_,
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (hDalg _) (hDqs _) hXqc _,
    P.stageFinite _, P.stageFinitePresentation _, ?_⟩
  · rw [hj']
    exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) (hVopen k).2
  · rw [Category.assoc, ← P.compatible, hfac]

/-- **Stacks 0874, granted Stacks 07VR.**  Let `f : X ⟶ Y` be a quasi-finite separated
morphism of algebraic spaces over `S` which is locally of finite presentation, with `Y`
quasi-compact and quasi-separated.  Then `f = π ∘ j` with `j : X ⟶ T` a quasi-compact open
immersion and `π : T ⟶ Y` finite and of finite presentation.

The factorization of Stacks 082K is
`AlgebraicGeometry.Space.exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite`; it is
improved by
`AlgebraicGeometry.Space.exists_isOpenImmersion_isFinitePresentation_of_factorization`, which
carries `h07VR`. -/
theorem exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hfp : IsLocallyOfFinitePresentation B S hS f) :
    ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : X ⟶ T) (π : T ⟶ Y),
      IsAlgebraicSpace B S hS T ∧ IsOpenImmersion B S hS j ∧ IsQuasiCompact B S hS j ∧
        IsFinite B S hS π ∧ IsFinitePresentation B S hS π ∧ j ≫ π = f := by
  obtain ⟨T, j, π, hT, hj, hjqc, hπ, hfac⟩ :=
    exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite f hX hY hqf hsep
      hYqc hYqs
  exact exists_isOpenImmersion_isFinitePresentation_of_factorization h07VR f hX hY hT hYqc hYqs
    hfp j π hj hjqc hπ hfac

end AlgebraicGeometry.Space

end
