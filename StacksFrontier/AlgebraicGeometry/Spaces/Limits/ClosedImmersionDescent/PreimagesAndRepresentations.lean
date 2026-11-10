module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Immersion
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# Preimage systems, quasi-compact open subspaces and affine representations

This file collects the preliminaries for the eventual closed immersion and the eventual immersion
into the stages of a directed limit of algebraic spaces (Stacks 0828).

A subfunctor of the target of a natural transformation from an inverse system to a constant
diagram pulls back to a subfunctor of every stage, and those preimages form an inverse system
whose limit is the preimage in the limit of the system.  An immersion with quasi-compact source
is a closed immersion into a quasi-compact open subspace of its target.  Finally, a morphism from
an algebraic space to the restricted points of an affine scheme over `S` is represented by a
morphism of schemes from an object of the site, and limits of affine objects of the site are
computed in the slice of all schemes over `S`.

## Main results

* `CategoryTheory.Subfunctor.isLimitPreimageCone`: the preimages of a subfunctor of the target
  of a natural transformation from an inverse system to a constant diagram form an inverse
  system whose limit is the preimage in the limit of the system.
* `AlgebraicGeometry.Space.exists_isQuasiCompactSpace_isClosedImmersion_of_isImmersion`: an
  immersion with quasi-compact source is a closed immersion into a quasi-compact open subspace
  of its target.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_lift`: a morphism from a
  quasi-compact algebraic space factors through a quasi-compact open subspace of its target.

## Implementation notes

Objects of the site are only representably prescribed, so the limits of chosen representing
objects are formed in the slice over `S` and compared to the inverse system of presheaves
through the restricted Yoneda embedding of that slice.  Factoring a morphism into an affine
object of the slice through an affine object of the *site* uses the scheme-theoretic image,
whose size is bounded by the cardinality of the ring of global sections of the source.

## References

* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe u

/-! ### The inverse system of preimages of a subfunctor

A subfunctor of the target of a natural transformation from an inverse system to a constant
diagram pulls back to a subfunctor of every stage, and those preimages form an inverse system
whose limit is the preimage in the limit.  This is the shape in which an open subspace of a
limit of algebraic spaces is presented as a limit of open subspaces of the stages. -/

namespace CategoryTheory.Subfunctor

universe w₀ v₁ u₀ u₁

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₀} [Category.{w₀} C]
  {Dg : J ⥤ C ⥤ Type w₀} {Z : C ⥤ Type w₀} (τ : Dg ⟶ (Functor.const J).obj Z)
  (V : Subfunctor Z)

/-- A square exhibiting a subfunctor as the preimage of another is cartesian. -/
theorem isPullback_of_comp_ι_eq {F F' : C ⥤ Type w₀} (G : Subfunctor F) (p : F' ⟶ F)
    {W : Subfunctor F'} (hW : W = G.preimage p) (q : W.toFunctor ⟶ G.toFunctor)
    (hq : q ≫ G.ι = W.ι ≫ p) : IsPullback q W.ι G.ι p := by
  subst hW
  have hqe : q = G.fromPreimage p := (cancel_mono G.ι).1 (by rw [hq, fromPreimage_ι])
  rw [hqe]
  exact Subfunctor.isPullback_fromPreimage G p

/-- A transition morphism `Dg.map φ` carries the preimage of `V` at the stage `j` into the
preimage of `V` at the stage `k`: this is what defines the transition maps of
`preimageDiagram`. -/
theorem range_le_preimage_app {j k : J} (φ : j ⟶ k) :
    range ((V.preimage (τ.app j)).ι ≫ Dg.map φ) ≤ V.preimage (τ.app k) := by
  rw [range_comp, range_ι, image_le_iff, ← preimage_comp]
  simp

/-- The inverse system of preimages of a subfunctor of the target of a natural transformation
to a constant diagram. -/
@[simps]
def preimageDiagram : J ⥤ C ⥤ Type w₀ where
  obj j := (V.preimage (τ.app j)).toFunctor
  map {j k} φ := lift ((V.preimage (τ.app j)).ι ≫ Dg.map φ) (range_le_preimage_app τ V φ)
  map_id j := by
    apply (cancel_mono (V.preimage (τ.app j)).ι).1
    simp
  map_comp {j k l} φ ψ := by
    apply (cancel_mono (V.preimage (τ.app l)).ι).1
    simp

/-- Each transition morphism of the inverse system of preimages is a base change of the
corresponding transition morphism of the original system. -/
theorem isPullback_preimageDiagram_map {j k : J} (φ : j ⟶ k) :
    IsPullback ((preimageDiagram τ V).map φ) ((V.preimage (τ.app j)).ι)
      ((V.preimage (τ.app k)).ι) (Dg.map φ) :=
  isPullback_of_comp_ι_eq _ _ (by
    rw [← preimage_comp]
    simp) _ (by simp [preimageDiagram])

variable {cg : Cone Dg} {σ : cg.pt ⟶ Z}

/-- A leg of a cone over `Dg` whose composites with `τ` all equal `σ` carries the preimage of `V`
under `σ` into the preimage of `V` at its stage: this is what defines the legs of
`preimageCone`. -/
theorem range_le_preimage_cone (hσ : ∀ j, cg.π.app j ≫ τ.app j = σ) (j : J) :
    range ((V.preimage σ).ι ≫ cg.π.app j) ≤ V.preimage (τ.app j) := by
  rw [range_comp, range_ι, image_le_iff, ← preimage_comp, hσ j]

/-- The cone over the inverse system of preimages induced by a cone over the system itself. -/
@[simps]
def preimageCone (hσ : ∀ j, cg.π.app j ≫ τ.app j = σ) : Cone (preimageDiagram τ V) where
  pt := (V.preimage σ).toFunctor
  π :=
    { app j := lift ((V.preimage σ).ι ≫ cg.π.app j) (range_le_preimage_cone τ V hσ j)
      naturality {j k} φ := by
        apply (cancel_mono (V.preimage (τ.app k)).ι).1
        simp [preimageDiagram, cg.w φ] }

/-- The cone over the original system induced by a cone over the system of preimages. -/
@[simps]
def preimageConeDown (s : Cone (preimageDiagram τ V)) : Cone Dg where
  pt := s.pt
  π :=
    { app j := s.π.app j ≫ (V.preimage (τ.app j)).ι
      naturality {j k} φ := by
        have h : s.π.app j ≫ (preimageDiagram τ V).map φ = s.π.app k := by simpa using s.w φ
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        rw [← h]
        simp [preimageDiagram] }

/-- The cone of preimages under the projections of a limiting cone is limiting. -/
def isLimitPreimageCone [Nonempty J] (hσ : ∀ j, cg.π.app j ≫ τ.app j = σ)
    (hcg : IsLimit cg) :
    IsLimit (preimageCone τ V hσ) where
  lift s := lift (hcg.lift (preimageConeDown τ V s)) (by
    obtain ⟨j₀⟩ := ‹Nonempty J›
    have hα : hcg.lift (preimageConeDown τ V s) ≫ cg.π.app j₀
        = s.π.app j₀ ≫ (V.preimage (τ.app j₀)).ι := hcg.fac _ j₀
    rw [Subfunctor.le_def]
    intro A x hx
    obtain ⟨y, rfl⟩ := hx
    have h1 := ConcreteCategory.congr_hom (congr_app hα A) y
    have h2 := ((s.π.app j₀).app A y).2
    simp only [preimage_obj, Set.mem_preimage] at h2 ⊢
    simp only [NatTrans.comp_app, types_comp_apply] at h1
    rw [← hσ j₀]
    simp only [NatTrans.comp_app, types_comp_apply, h1]
    exact h2)
  fac s j := by
    apply (cancel_mono (V.preimage (τ.app j)).ι).1
    change hcg.lift (preimageConeDown τ V s) ≫ cg.π.app j
      = s.π.app j ≫ (V.preimage (τ.app j)).ι
    exact hcg.fac (preimageConeDown τ V s) j
  uniq s m hm := by
    apply (cancel_mono (V.preimage σ).ι).1
    change m ≫ (V.preimage σ).ι = hcg.lift (preimageConeDown τ V s)
    refine hcg.uniq (preimageConeDown τ V s) _ fun j => ?_
    change (m ≫ (preimageCone τ V hσ).π.app j) ≫ (V.preimage (τ.app j)).ι
      = s.π.app j ≫ (V.preimage (τ.app j)).ι
    rw [hm j]

end CategoryTheory.Subfunctor

/-! ### Shrinking the open subspace an immersion is closed in -/

/-- Products of presheaves of types, indexed by a type in `Type`, supplied directly (instance
search times out without this shortcut). -/
private instance (priority := high) hasLimitsOfShape_discrete_preimagesAndRepresentations
    {C : Type*} [Category* C] {J : Type} : HasLimitsOfShape (Discrete J) (C ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

namespace AlgebraicGeometry.Space

section Immersion

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism from a quasi-compact algebraic space whose points land in an open set of the
points of its target factors through a quasi-compact open subspace with points in that set. -/
private theorem exists_isQuasiCompactSpace_lift_of_range_subset
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (g : Y ⟶ X) {O : Set (points B S hS X)}
    (hO : IsOpen O) (hgO : Set.range (pointsMap B S hS Y g) ⊆ O) :
    ∃ (U : Subfunctor X) (h : Y ⟶ U.toFunctor), IsOpenSubspace B S hS U ∧
      IsQuasiCompactSpace B S hS U.toFunctor ∧
        Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆ O ∧ h ≫ U.ι = g := by
  classical
  have hYcpt : CompactSpace (points B S hS Y) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS Y hY).mp hYqc
  have hRcpt : IsCompact (Set.range (pointsMap B S hS Y g)) :=
    isCompact_range (continuous_pointsMap B S hS _)
  have hcov : ∀ x ∈ Set.range (pointsMap B S hS Y g), ∃ V : Subfunctor X,
      (IsOpenSubspace B S hS V ∧ IsQuasiCompactSpace B S hS V.toFunctor ∧
        x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
        Set.range (pointsMap B S hS V.toFunctor V.ι) ⊆ O := by
    intro x hx
    obtain ⟨V, hV, hVqc, hxV, hVsub⟩ :=
      exists_isQuasiCompactSpace_isOpenSubspace_range_subset B S hS hX _ hO x (hgO hx)
    exact ⟨V, ⟨hV, hVqc, hxV⟩, hVsub⟩
  choose! V hV hVsub using hcov
  obtain ⟨σ, hσR, hσcover⟩ := hRcpt.elim_nhds_subcover
    (fun x ↦ Set.range (pointsMap B S hS (V x).toFunctor (V x).ι))
    fun x hx ↦ (isOpen_range_pointsMap_of_isOpenImmersion B S hS (V x).ι
      (hV x hx).1.2).mem_nhds (hV x hx).2.2
  let P := ⋃ x : {z // z ∈ σ}, Set.range (pointsMap B S hS (V x.1).toFunctor (V x.1).ι)
  have hPopen : IsOpen P := isOpen_iUnion fun x ↦ isOpen_range_pointsMap_of_isOpenImmersion
    B S hS _ (hV x.1 (hσR x.1 x.2)).1.2
  have hPcpt : IsCompact P := by
    refine isCompact_iUnion fun x ↦ ?_
    have hc : CompactSpace (points B S hS (V x.1).toFunctor) :=
      (isQuasiCompactSpace_iff_compactSpace_points B S hS _
        (hV x.1 (hσR x.1 x.2)).1.1).mp (hV x.1 (hσR x.1 x.2)).2.1
    exact isCompact_range (continuous_pointsMap B S hS _)
  have hRP : Set.range (pointsMap B S hS Y g) ⊆ P := by
    refine le_trans hσcover (Set.iUnion₂_subset fun x hx ↦ ?_)
    exact Set.subset_iUnion
      (fun z : {w // w ∈ σ} ↦ Set.range (pointsMap B S hS (V z.1).toFunctor (V z.1).ι)) ⟨x, hx⟩
  have hU : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X P) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _ hPopen
  have hUrange := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := X) P
  have hUqc : IsQuasiCompactSpace B S hS (openSubspaceOfPoints B S hS X P).toFunctor :=
    isQuasiCompactSpace_of_isCompact_range B S hS hX hU (by rw [hUrange]; exact hPcpt)
  obtain ⟨h, hhι⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hY _ hU g).2
    (by rw [hUrange]; exact hRP)
  exact ⟨_, h, hU, hUqc, by rw [hUrange]; exact Set.iUnion_subset fun x ↦ hVsub x.1 (hσR x.1 x.2),
    hhι⟩

/-- A closed immersion into an open subspace is a closed immersion into a quasi-compact open
subspace, as soon as its source is quasi-compact. -/
theorem exists_isQuasiCompactSpace_isClosedImmersion_of_isOpenSubspace
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (W : Subfunctor X) (hW : IsOpenSubspace B S hS W)
    (g : Y ⟶ W.toFunctor) (hg : IsClosedImmersion B S hS g) :
    ∃ (U : Subfunctor X) (h : Y ⟶ U.toFunctor), IsOpenSubspace B S hS U ∧
      IsQuasiCompactSpace B S hS U.toFunctor ∧ IsClosedImmersion B S hS h ∧
        h ≫ U.ι = g ≫ W.ι := by
  obtain ⟨U, h, hU, hUqc, hUsub, hhι⟩ := exists_isQuasiCompactSpace_lift_of_range_subset B S hS hX
    hY hYqc (g ≫ W.ι) (isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hW.2)
    (by rw [pointsMap_comp]; exact Set.range_comp_subset_range _ _)
  have hUW : U ≤ W := le_of_range_pointsMap_ι_subset B S hS hW hUsub
  have hfac : h ≫ Subfunctor.homOfLe hUW = g := by
    apply (cancel_mono W.ι).1
    rw [Category.assoc, Subfunctor.homOfLe_ι, hhι]
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact ⟨U, h, hU, hUqc, MorphismProperty.of_isPullback
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 Y) (snd := h) (f := g)
      (g := Subfunctor.homOfLe hUW) ⟨by simpa using hfac.symm⟩) hg, hhι⟩

/-- An immersion with quasi-compact source is a closed immersion into a quasi-compact open
subspace of its target. -/
theorem exists_isQuasiCompactSpace_isClosedImmersion_of_isImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (f : Y ⟶ X) (hf : IsImmersion B S hS f) :
    ∃ (U : Subfunctor X) (h : Y ⟶ U.toFunctor), IsOpenSubspace B S hS U ∧
      IsQuasiCompactSpace B S hS U.toFunctor ∧ IsClosedImmersion B S hS h ∧ h ≫ U.ι = f := by
  obtain ⟨g, hgclosed, hgι⟩ :=
    exists_isClosedImmersion_comp_ι_boundaryComplement B S hS hX hY f hf
  obtain ⟨U, h, hU, hUqc, hhclosed, hhι⟩ :=
    exists_isQuasiCompactSpace_isClosedImmersion_of_isOpenSubspace B S hS hX hY hYqc _
      (isOpenSubspace_boundaryComplement B S hS hX
        (isLocallyClosed_range_pointsMap_of_isImmersion B S hS hX f hf)) g hgclosed
  exact ⟨U, h, hU, hUqc, hhclosed, by rw [hhι, hgι]⟩

/-- A morphism from a quasi-compact algebraic space factors through a quasi-compact open subspace
of its target. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_lift
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (g : Y ⟶ X) :
    ∃ (U : Subfunctor X) (h : Y ⟶ U.toFunctor), IsOpenSubspace B S hS U ∧
      IsQuasiCompactSpace B S hS U.toFunctor ∧ h ≫ U.ι = g := by
  obtain ⟨U, h, hU, hUqc, -, hhι⟩ :=
    exists_isQuasiCompactSpace_lift_of_range_subset B S hS hX hY hYqc g isOpen_univ
      (Set.subset_univ _)
  exact ⟨U, h, hU, hUqc, hhι⟩

end Immersion

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

noncomputable abbrev restrictedPoints
    {C : Type*} [Category.{u} C] {E : Type*} [Category.{u} E]
    (F : C ⥤ E) : E ⥤ Cᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

noncomputable abbrev restrictedPointsIso
    {C : Type*} [Category.{u} C] {E : Type*} [Category.{u} E]
    (F : C ⥤ E) [F.Full] [F.Faithful] (X : C) :
    (restrictedPoints F).obj (F.obj X) ≅ yoneda.obj X := by
  let hFF := Functor.FullyFaithful.ofFullyFaithful F
  refine NatIso.ofComponents (fun _ => hFF.homEquiv.symm.toIso) ?_
  intro X Y g
  ext x
  change F.preimage (F.map g.unop ≫ x) = g.unop ≫ F.preimage x
  apply F.map_injective
  rw [F.map_preimage, F.map_comp, F.map_preimage]

lemma restrictedPointsIso_naturality
    {C : Type*} [Category.{u} C] {E : Type*} [Category.{u} E]
    (F : C ⥤ E) [F.Full] [F.Faithful] {X Y : C} (f : X ⟶ Y) :
    (restrictedPoints F).map (F.map f) ≫ (restrictedPointsIso F Y).hom =
      (restrictedPointsIso F X).hom ≫ yoneda.map f := by
  ext Z x
  change F.preimage (x ≫ F.map f) = F.preimage x ≫ f
  apply F.map_injective
  rw [F.map_preimage, F.map_comp, F.map_preimage]

private lemma mk_globalSections_lt
    (B : BigFppfSite.{u}) {T : Scheme.{u}} (hT : B.Contains T) :
    Cardinal.mk Γ(T, ⊤) < B.cutoff := by
  let r : Γ(T, ⊤) → ∀ U : T.affineOpens, Γ(T, U.1) :=
    fun x U => T.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op x
  have hr : Function.Injective r := by
    intro x y h
    apply T.IsSheaf.section_ext
    intro p _
    obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show p ∈ (⊤ : T.Opens) from trivial)
    exact ⟨U, le_top, hpU, congrFun h ⟨U, hU⟩⟩
  have hcard : Cardinal.mk Γ(T, ⊤) ≤ T.size ^ T.size := by
    apply (Cardinal.mk_le_of_injective hr).trans
    calc
      Cardinal.mk (∀ U : T.affineOpens, Γ(T, U.1)) ≤
          T.size ^ Cardinal.mk T.affineOpens := by
        rw [Cardinal.mk_pi, ← Cardinal.prod_const' T.affineOpens]
        exact Cardinal.prod_le_prod _ _ (fun U => T.mk_sections_le_size U)
      _ ≤ T.size ^ T.size := Cardinal.power_le_power_left
        (ne_of_gt (Cardinal.aleph0_pos.trans_le T.aleph0_le_size)) T.mk_affineOpens_le_size
  apply hcard.trans_lt
  rw [Cardinal.power_self_eq (T.aleph0_le_size)]
  exact B.cutoff_isStrongPrelimit hT

private lemma exists_small_affine_closed_factorization
    (B : BigFppfSite.{u}) {T U : Scheme.{u}}
    (hT : B.Contains T) [IsAffine U] (f : T ⟶ U) :
    ∃ (V : Scheme.{u}) (_ : B.Contains V) (_ : IsAffine V)
      (a : T ⟶ V) (b : V ⟶ U), _root_.AlgebraicGeometry.IsClosedImmersion b ∧ a ≫ b = f := by
  let f' := f ≫ U.isoSpec.hom
  let V := Spec (specTargetImage f')
  let a := specTargetImageFactorization f'
  let b := Spec.map (specTargetImageRingHom f') ≫ U.isoSpec.inv
  have ha : Function.Injective a.appTop := specTargetImageFactorization_app_injective f'
  have hV : B.Contains V := by
    rw [BigFppfSite.Contains, Scheme.size_of_isAffine]
    exact max_lt B.aleph0_lt_cutoff
      ((Cardinal.mk_le_of_injective ha).trans_lt (mk_globalSections_lt B hT))
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (specTargetImageRingHom f')) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      (specTargetImageRingHom_surjective f')
  refine ⟨V, hV, inferInstance, a, b, inferInstance, ?_⟩
  simp [a, b, f']

private lemma factor_through_mono_of_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hK : Presheaf.IsSheaf (BigFppfOver.topology B S hS) K)
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ G)
    (haS : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haE : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (f : G ⟶ H) (m : K ⟶ H) [Mono m] (k : yoneda.obj T ⟶ K)
    (hk : k ≫ m = a ≫ f) : ∃ b : G ⟶ K, b ≫ m = f := by
  let s := haE.rep.fst' a
  let t := haE.rep.snd a
  have hR := haE.rep.isPullback' a
  obtain ⟨hRsh, hTsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale
    B S hS a s t hR hG haS haE
  have hw : yoneda.map s ≫ k = yoneda.map t ≫ k := by
    apply (cancel_mono m).1
    rw [Category.assoc, Category.assoc, hk]
    exact congrArg (· ≫ f) hR.w
  let k' : (⟨yoneda.obj T, hTsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨K, hK⟩ := ⟨k⟩
  let b := hc.desc (Cofork.ofπ k' (Sheaf.hom_ext hw))
  refine ⟨b.hom, ?_⟩
  have hb : a ≫ b.hom = k :=
    congrArg (fun z : (⟨yoneda.obj T, hTsh⟩ : Sheaf _ _) ⟶ ⟨K, hK⟩ => z.hom)
      (hc.fac (Cofork.ofπ k' (Sheaf.hom_ext hw)) WalkingParallelPair.one)
  have heq : b ≫ (⟨m⟩ : (⟨K, hK⟩ : Sheaf _ _) ⟶ ⟨H, hH⟩) = ⟨f⟩ := by
    apply hc.hom_ext
    intro j
    cases j
    · apply Sheaf.hom_ext
      change (yoneda.map s ≫ a) ≫ (b.hom ≫ m) = (yoneda.map s ≫ a) ≫ f
      have hb' : a ≫ b.hom ≫ m = a ≫ f := by rw [← Category.assoc, hb, hk]
      simpa only [Category.assoc] using congrArg (yoneda.map s ≫ ·) hb'
    · apply Sheaf.hom_ext
      change a ≫ (b.hom ≫ m) = a ≫ f
      rw [← Category.assoc, hb, hk]
  exact congrArg (fun z => z.hom) heq

/-- A morphism from an algebraic space to the restricted points of an affine scheme over `S`
which is representable with a property `P` after every represented base change is, up to
isomorphism, the restricted points of a morphism of schemes with `P` from an object of the site,
as soon as `P` is preserved by composing with a closed immersion. -/
lemma exists_representation_of_presheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X Y Z : Scheme.{u}} (q : X ⟶ Y) (m : Y ⟶ Z), P q →
      _root_.AlgebraicGeometry.IsClosedImmersion m → P (q ≫ m))
    (U : Over S) [IsAffine U.left]
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((restrictedPoints (Over.post B.inclusion)).obj U))
    (f : G ⟶ (restrictedPoints (Over.post B.inclusion)).obj U)
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ (V : BigFppfOver B S hS)
      (e : yoneda.obj V ≅ G) (v : (Over.post B.inclusion).obj V ⟶ U),
      P v.left ∧
      e.hom ≫ f = (restrictedPointsIso (Over.post B.inclusion) V).inv ≫
        (restrictedPoints (Over.post B.inclusion)).map v := by
  classical
  let F := Over.post (X := B.obj hS) B.inclusion
  let R := restrictedPoints F
  obtain ⟨T, a, haS, haE⟩ := hG.exists_atlas
  let g : F.obj T ⟶ U := yonedaEquiv (a ≫ f)
  obtain ⟨W, hW, hWA, k, m, hm, hkm⟩ :=
    exists_small_affine_closed_factorization B T.left.property g.left
  let : _root_.AlgebraicGeometry.IsClosedImmersion m := hm
  let W' : BigFppfOver B S hS :=
    Over.mk (Y := B.obj hW) (ObjectProperty.homMk (m ≫ U.hom))
  let m' : F.obj W' ⟶ U := Over.homMk m
  let k' : T ⟶ W' := Over.homMk (ObjectProperty.homMk k) (by
    apply B.inclusion.map_injective
    change k ≫ (m ≫ U.hom) = (F.obj T).hom
    rw [← Category.assoc, hkm]
    exact g.w)
  have hkm' : F.map k' ≫ m' = g := by
    apply Over.OverMorphism.ext
    exact hkm
  let mR := (restrictedPointsIso F W').inv ≫ R.map m'
  have : Mono m := inferInstance
  have : Mono m' := by
    have : Mono m'.left := inferInstanceAs (Mono m)
    exact Over.mono_of_mono_left m'
  have hRm : Mono (R.map m') := inferInstance
  have hinv : Mono (restrictedPointsIso F W').inv := ⟨fun g h w => by
    have := w =≫ (restrictedPointsIso F W').hom
    rwa [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.comp_id] at this⟩
  have : Mono mR := @mono_comp _ _ _ _ _ _ hinv _ hRm
  have hk : yoneda.map k' ≫ mR = a ≫ f := by
    apply yonedaEquiv.injective
    change F.map k' ≫ m' = yonedaEquiv (a ≫ f)
    exact hkm'
  obtain ⟨b, hb⟩ := factor_through_mono_of_atlas B S hS hG hU
    (isAlgebraicSpace_yoneda B S hS W').isSheaf a haS haE f mR
    (yoneda.map k') hk
  let V := hf.rep.pullback mR
  let p := hf.rep.fst mR
  let q := hf.rep.snd mR
  have hpq := hf.rep.isPullback mR
  have hpb : IsPullback (𝟙 G) b f mR :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hb.symm⟩
  let e : yoneda.obj V ≅ G := hpq.isoIsPullback _ _ hpb
  have he : e.hom = p := by
    simpa using hpq.isoIsPullback_hom_fst _ _ hpb
  have hq : P ((BigFppfOver.toScheme B S hS).map q) := hf.property_snd mR
  let v : F.obj V ⟶ U := F.map q ≫ m'
  have hv : P v.left := hP _ m hq hm
  refine ⟨V, e, v, hv, ?_⟩
  change e.hom ≫ f = (restrictedPointsIso F V).inv ≫ R.map v
  rw [he, hpq.w]
  dsimp only [mR, v]
  rw [R.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1

end AlgebraicGeometry.Space
