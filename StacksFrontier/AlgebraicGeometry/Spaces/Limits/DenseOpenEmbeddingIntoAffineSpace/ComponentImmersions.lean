module

public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Size.UniversallyClosedCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen

/-!
# Component-wise immersions into affine space

Auxiliary results for Stacks 088N.  For a quasi-compact morphism `f : Y ⟶ X` of
quasi-separated algebraic spaces with `Y` Noetherian on points, each irreducible component `C`
of the space of points of `Y` contains an affine open, lying in the locus `componentGenericOpen C`
missing every other component and with `C` in its closure, on which `f` factors through an
immersion of a scheme into `X`; such a factorization then yields an immersion of the affine
open into relative affine space over `X`.  Also: being an algebraic space is invariant under
isomorphism of presheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace TopCat

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance]
  AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme

private theorem pointsMap_id_point
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (x : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS F (𝟙 F) x = x := by
  induction x using Quot.inductionOn with | h p => rfl

/-- The inverse image of a base-change-stable property under `toScheme` is stable under base
change. -/
private theorem inverseImage_toScheme_isStableUnderBaseChange
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun h hf => MorphismProperty.of_isPullback (P := P) (h.map _) hf⟩

private theorem openImmersion_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : AlgebraicGeometry.Space.IsOpenImmersion B S hS f)
    (hg : AlgebraicGeometry.Space.IsOpenImmersion B S hS g) :
    AlgebraicGeometry.Space.IsOpenImmersion B S hS (f ≫ g) := by
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : Q.IsStableUnderComposition := inferInstance
  let : Q.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  exact MorphismProperty.comp_mem Q.presheaf f g hf hg

private theorem immersion_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : AlgebraicGeometry.Space.IsImmersion B S hS f)
    (hg : AlgebraicGeometry.Space.IsImmersion B S hS g) :
    AlgebraicGeometry.Space.IsImmersion B S hS (f ≫ g) := by
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.IsImmersion.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@AlgebraicGeometry.IsImmersion.{u})).toIsStableUnderComposition
  let : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let : Q.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  exact MorphismProperty.comp_mem Q.presheaf f g hf hg

private theorem genericPoint_of_irreducibleComponent
    {α : Type*} [TopologicalSpace α] [QuasiSober α]
    (C : Set α) (hC : C ∈ irreducibleComponents α) :
    ∃ η, IsGenericPoint η C :=
  ⟨hC.1.genericPoint, hC.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents C hC)⟩

private noncomputable def componentGenericOpen
    {α : Type*} [TopologicalSpace α] (C : Set α) : Set α :=
  (⋃₀ (irreducibleComponents α \ {C}))ᶜ

private theorem componentGenericOpen_isOpen
  {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α]
    (C : Set α) : IsOpen (componentGenericOpen C) := by
  rw [componentGenericOpen, Set.sUnion_eq_biUnion, isOpen_compl_iff]
  exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff).isClosed_biUnion
    fun D hD => isClosed_of_mem_irreducibleComponents D hD.1

private theorem componentGenericOpen_subset
    {α : Type*} [TopologicalSpace α]
    (C : Set α) :
    componentGenericOpen C ⊆ C := by
  intro x hx
  have hxComponents : x ∈ ⋃₀ irreducibleComponents α := by
    rw [sUnion_irreducibleComponents]
    simp
  obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp hxComponents
  by_contra hxC
  have hDC : D ≠ C := by
    rintro rfl
    exact hxC hxD
  have hxOther : x ∈ ⋃₀ (irreducibleComponents α \ {C}) :=
    Set.mem_sUnion.mpr ⟨D, ⟨hD, hDC⟩, hxD⟩
  exact hx (by simpa [componentGenericOpen] using hxOther)

private theorem genericPoint_mem_componentGenericOpen
    {α : Type*} [TopologicalSpace α]
    (C : Set α) (hC : C ∈ irreducibleComponents α) {η : α}
    (hη : IsGenericPoint η C) : η ∈ componentGenericOpen C := by
  rw [componentGenericOpen, Set.mem_compl_iff, Set.mem_sUnion]
  rintro ⟨D, hD, hηD⟩
  have hCD : C ⊆ D := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηD)
      (isClosed_of_mem_irreducibleComponents D hD.1)
  have hne : D ≠ C := by simpa using hD.2
  exact hne ((hC.2 hD.1.1 hCD).antisymm hCD)

private theorem componentGenericOpen_disjoint
    {α : Type*} [TopologicalSpace α]
    {C D : Set α} (hC : C ∈ irreducibleComponents α) (hCD : C ≠ D) :
    Disjoint (componentGenericOpen C) (componentGenericOpen D) := by
  refine Set.disjoint_left.mpr fun x hxC hxD => ?_
  have hxInC := componentGenericOpen_subset C hxC
  have hxOther : x ∈ ⋃₀ (irreducibleComponents α \ {D}) :=
    Set.mem_sUnion.mpr ⟨C, ⟨hC, by simp [hCD]⟩, hxInC⟩
  exact hxD (by simpa [componentGenericOpen] using hxOther)

private theorem pointsMap_comp_point
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H) (x : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS F (f ≫ g) x =
      AlgebraicGeometry.Space.pointsMap B S hS G g
        (AlgebraicGeometry.Space.pointsMap B S hS F f x) := by
  induction x using Quot.inductionOn with | h p => rfl

private theorem closure_image_eq_closure_genericPoint
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f) {C : Set α} {η : α}
    (hη : IsGenericPoint η C) :
    closure (f '' C) = closure ({f η} : Set β) := by
  calc
    closure (f '' C) = closure (f '' closure ({η} : Set α)) := by
      rw [hη.def]
    _ = closure (f '' ({η} : Set α)) := closure_image_closure hf
    _ = closure ({f η} : Set β) := by simp

/-- A map whose range contains a generic point of the whole space has dense range. -/
private theorem denseRange_of_isGenericPoint_mem_range
    {α β : Type*} [TopologicalSpace α] {f : β → α} {η : α}
    (hη : IsGenericPoint η (Set.univ : Set α)) (h : η ∈ Set.range f) : DenseRange f :=
  (dense_iff_closure_eq.2 hη.def).mono (Set.singleton_subset_iff.2 h)

/-- Composing with a continuous map `g` after a dense-range map `f` does not change the closure
of the range. -/
private theorem closure_range_comp_eq_of_denseRange
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : γ → α} {g : α → β}
    (hg : Continuous g) (hf : DenseRange f) :
    closure (Set.range (g ∘ f)) = closure (Set.range g) := by
  rw [Set.range_comp, ← closure_image_closure hg, hf.closure_eq, Set.image_univ]

/-- A quasi-separated algebraic space over `S` is Zariski locally quasi-separated over `S`. -/
private theorem isZariskiLocallyQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X) :
    AlgebraicGeometry.Space.IsZariskiLocallyQuasiSeparatedOver B S hS X :=
  AlgebraicGeometry.Space.isZariskiLocallyQuasiSeparatedOver_of_isQuasiSeparatedOver B S hS hX
    (AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated
      B S hS hZ hX hqs)

private theorem genericPoint_mem_schematicLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (x : AlgebraicGeometry.Space.points B S hS X)
    (hx : @IsGenericPoint (AlgebraicGeometry.Space.points B S hS X)
      (AlgebraicGeometry.Space.pointTopology B S hS X) x
      (Set.univ : Set (AlgebraicGeometry.Space.points B S hS X))) :
    x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS
      (AlgebraicGeometry.Space.schematicLocus B S hS X).toFunctor
      (AlgebraicGeometry.Space.schematicLocus B S hS X).ι) := by
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
    AlgebraicGeometry.Space.pointTopology B S hS X
  have : Nonempty (AlgebraicGeometry.Space.points B S hS X) := ⟨x⟩
  have hdense :=
    denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ X hX
      (isZariskiLocallyQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ hX hqs)
  have hopen := AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS
    (AlgebraicGeometry.Space.schematicLocus B S hS X).ι
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX).1.2
  obtain ⟨y, hy⟩ : (Set.range (AlgebraicGeometry.Space.pointsMap B S hS
      (AlgebraicGeometry.Space.schematicLocus B S hS X).toFunctor
      (AlgebraicGeometry.Space.schematicLocus B S hS X).ι)).Nonempty := Dense.nonempty hdense
  have hyc : y ∈ closure ({x} : Set (AlgebraicGeometry.Space.points B S hS X)) := by
    rw [hx.def]; trivial
  obtain ⟨z, hzU, hzx⟩ := mem_closure_iff.mp hyc _ hopen hy
  exact Set.mem_singleton_iff.mp hzx ▸ hzU

/-- Monotonicity of the relative property attached to `toScheme`. -/
private theorem presheaf_toScheme_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P P' : MorphismProperty Scheme.{u}} (h : P ≤ P')
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    (P'.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f :=
  MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage _ h) f hf

private theorem closedSubspace_immersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : AlgebraicGeometry.Space.IsClosedImmersion B S hS f) :
    AlgebraicGeometry.Space.IsImmersion B S hS f := by
  exact presheaf_toScheme_mono B S hS (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (P' := @_root_.AlgebraicGeometry.IsImmersion.{u}) (fun _ _ _ _ => inferInstance) hf

private theorem quasiCompact_of_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) (hF : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS F) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS G := by
  obtain ⟨U, f, hc, hs, he⟩ := hF
  refine ⟨U, f ≫ e.hom, hc,
    MorphismProperty.RespectsIso.postcomp _ e.hom f hs, ?_⟩
  intro V g hg
  exact MorphismProperty.RespectsIso.postcomp _ e.hom (g ≫ f) (he V g hg)

private theorem quasiSeparated_of_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [Mono f] : AlgebraicGeometry.Space.IsQuasiSeparated B S hS f := by
  show AlgebraicGeometry.Space.IsQuasiCompact B S hS (pullback.diagonal f)
  let : IsIso (pullback.diagonal f) := (pullback.isIso_diagonal_iff f).2 inferInstance
  intro Z hZ hZqc g
  have : IsIso (pullback.fst g (pullback.diagonal f)) := by infer_instance
  exact quasiCompact_of_iso B S hS
    (asIso (pullback.fst g (pullback.diagonal f))).symm hZqc

private theorem immersion_of_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : AlgebraicGeometry.Space.IsOpenImmersion B S hS f) :
    AlgebraicGeometry.Space.IsImmersion B S hS f := by
  exact presheaf_toScheme_mono B S hS (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    (P' := @_root_.AlgebraicGeometry.IsImmersion.{u}) (fun _ _ _ _ => inferInstance) hf

private theorem exists_dense_open_factor_through_scheme_of_genericPoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hXqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S hS f)
    (η : AlgebraicGeometry.Space.points B S hS Y)
    (hη : @IsGenericPoint _ (AlgebraicGeometry.Space.pointTopology B S hS Y) η Set.univ) :
    ∃ (P : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_hP : AlgebraicGeometry.IsAlgebraicSpace B S hS P) (j : P ⟶ Y),
      AlgebraicGeometry.Space.IsOpenImmersion B S hS j ∧ Mono j ∧
      η ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS P j) ∧
      (letI := AlgebraicGeometry.Space.pointTopology B S hS Y
       DenseRange (AlgebraicGeometry.Space.pointsMap B S hS P j)) ∧
      ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (a : P ⟶ yoneda.obj U)
        (b : yoneda.obj U ⟶ X),
        AlgebraicGeometry.Space.IsImmersion B S hS b ∧ a ≫ b = j ≫ f := by
  let := AlgebraicGeometry.Space.pointTopology B S hS Y
  let W := AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor B S hS f
  have hW := isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hX
  let := AlgebraicGeometry.Space.pointTopology B S hS W.toFunctor
  let g : Y ⟶ W.toFunctor := AlgebraicGeometry.Space.toSchemeTheoreticImage B S hS f
  have hfac : g ≫ W.ι = f := Subfunctor.lift_ι _ _
  have hWqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ W.toFunctor :=
    AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
      B S hS hZ hW.1 hXqs (quasiSeparated_of_mono B S hS W.ι)
  have hdense : DenseRange (AlgebraicGeometry.Space.pointsMap B S hS Y g) :=
    AlgebraicGeometry.Space.denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact
      B S hS f hY hX hf
  have hgeneric : IsGenericPoint (AlgebraicGeometry.Space.pointsMap B S hS Y g η)
      (Set.univ : Set (AlgebraicGeometry.Space.points B S hS W.toFunctor)) := by
    rw [isGenericPoint_def,
      ← closure_image_eq_closure_genericPoint _
        (AlgebraicGeometry.Space.continuous_pointsMap B S hS g) hη,
      Set.image_univ]
    exact hdense.closure_eq
  let L := AlgebraicGeometry.Space.schematicLocus B S hS W.toFunctor
  have hL :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hW.1).1
  obtain ⟨ξ, hξ⟩ := genericPoint_mem_schematicLocus B S hS hZ hW.1 hWqs
    (AlgebraicGeometry.Space.pointsMap B S hS Y g η) hgeneric
  let Y' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let W' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨W.toFunctor, hW.1⟩
  let L' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨L.toFunctor, hL.1⟩
  let g' : Y' ⟶ W' := ObjectProperty.homMk g
  let l' : L' ⟶ W' := ObjectProperty.homMk L.ι
  let P := AlgebraicGeometry.AlgebraicSpaces.fiberProduct B S hS g' l'
  have sq := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS g' l'
  let j : P.1 ⟶ Y := pullback.fst g L.ι
  let k : P.1 ⟶ L.toFunctor := pullback.snd g L.ι
  have hj : AlgebraicGeometry.Space.IsOpenImmersion B S hS j :=
    AlgebraicGeometry.Space.isOpenImmersion_of_isPullback B S hS sq.flip hL.2
  obtain ⟨p, hp, _⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS sq η ξ hξ.symm
  have hjdense : DenseRange (AlgebraicGeometry.Space.pointsMap B S hS P.1 j) :=
    denseRange_of_isGenericPoint_mem_range hη ⟨p, hp⟩
  let :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hW.1).2
  let U := L.toFunctor.reprX
  let e : yoneda.obj U ≅ L.toFunctor := L.toFunctor.reprW
  let a := k ≫ e.inv
  let b := e.hom ≫ L.ι ≫ W.ι
  have hLI : AlgebraicGeometry.Space.IsImmersion B S hS L.ι :=
    immersion_of_openImmersion B S hS L.ι hL.2
  have hb : AlgebraicGeometry.Space.IsImmersion B S hS b := by
    let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsImmersion.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    exact MorphismProperty.RespectsIso.precomp Q.presheaf e.hom (L.ι ≫ W.ι)
      (immersion_comp B S hS L.ι W.ι hLI
        (closedSubspace_immersion B S hS W.ι hW.2))
  refine ⟨P.1, P.2, j, hj, by change Mono (pullback.fst g L.ι); infer_instance,
    ⟨p, hp⟩, hjdense, U, a, b, hb, ?_⟩
  dsimp only [a, b]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  show (pullback.snd g L.ι ≫ L.ι) ≫ W.ι = j ≫ f
  rw [← pullback.condition, Category.assoc, hfac]
  rfl

private theorem point_lift_of_schemePoint_mem_range
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A T : AlgebraicGeometry.BigFppfOver B S hS} (k : A ⟶ T)
    (hk : _root_.AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map k))
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj T))
    (hp : AlgebraicGeometry.Space.schemePoint B S hS T p ∈
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map k)) :
    p.class B S hS (yoneda.obj T) ∈ Set.range
      (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (yoneda.map k)) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let := hk
  let δ := G.map p.value
  let : Field p.carrier := p.field
  have hδ : Set.range δ ⊆ Set.range (G.map k) := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint p.carrier :=
      (inferInstance : Subsingleton (Spec (.of p.carrier))).elim _ _
    rw [hz]
    exact hp
  let l₀ : B.obj p.contained ⟶ A.left :=
    ObjectProperty.homMk (_root_.AlgebraicGeometry.IsOpenImmersion.lift (G.map k) δ hδ)
  have hl₀ : l₀ ≫ k.left = p.value.left := by
    apply ObjectProperty.hom_ext
    exact _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac (G.map k) δ hδ
  let l : p.siteObject B S hS (yoneda.obj T) ⟶ A := Over.homMk l₀ (by
    rw [← k.w, ← Category.assoc, hl₀]
    exact p.value.w)
  have hl : l ≫ k = p.value := by
    apply Over.OverMorphism.ext
    exact hl₀
  let q : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj A) :=
    ⟨p.carrier, p.contained, p.toBase, l⟩
  refine ⟨q.class B S hS (yoneda.obj A), ?_⟩
  show Quot.mk _ (⟨p.carrier, p.contained, p.toBase, l ≫ k⟩ :
    AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj T)) = Quot.mk _ p
  rw [hl]

private theorem exists_affine_open_scheme_neighborhood
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (x : AlgebraicGeometry.Space.points B S hS (yoneda.obj T)) :
    ∃ (A : AlgebraicGeometry.BigFppfOver B S hS) (i : A ⟶ T),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A) ∧
      AlgebraicGeometry.IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) ∧
      x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (yoneda.map i)) := by
  induction x using Quot.inductionOn with
  | h p =>
    let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    let X := G.obj T
    let δ : Spec (.of p.carrier) ⟶ X := G.map p.value
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (x := δ (IsLocalRing.closedPoint p.carrier))
      (U := ⊤) (by trivial)
    let A₀ : B.Schemes := ⟨V.toScheme, (Scheme.size_coe_opens_le _ V).trans_lt T.left.2⟩
    let i₀ : A₀ ⟶ T.left := ObjectProperty.homMk V.ι
    let A : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (i₀ ≫ T.hom)
    let i : A ⟶ T := Over.homMk i₀
    have hi : _root_.AlgebraicGeometry.IsOpenImmersion (G.map i) := by
      show _root_.AlgebraicGeometry.IsOpenImmersion V.ι
      infer_instance
    exact ⟨A, i, hV, hi, point_lift_of_schemePoint_mem_range B S hS i hi p (by
      show δ (IsLocalRing.closedPoint p.carrier) ∈ Set.range V.ι
      exact ⟨⟨_, hxV⟩, rfl⟩)⟩

private theorem exists_affine_open_neighborhood_of_mem_schematicLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (x : AlgebraicGeometry.Space.points B S hS F)
    (hx : x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS
      (AlgebraicGeometry.Space.schematicLocus B S hS F).toFunctor
      (AlgebraicGeometry.Space.schematicLocus B S hS F).ι)) :
    ∃ (A : AlgebraicGeometry.BigFppfOver B S hS) (j : yoneda.obj A ⟶ F),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A) ∧
      AlgebraicGeometry.Space.IsOpenImmersion B S hS j ∧
      x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) j) := by
  let L := AlgebraicGeometry.Space.schematicLocus B S hS F
  have hL :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).1
  let :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2
  let T := L.toFunctor.reprX
  let e : yoneda.obj T ≅ L.toFunctor := L.toFunctor.reprW
  obtain ⟨p, hp⟩ := hx
  let q := AlgebraicGeometry.Space.pointsMap B S hS L.toFunctor e.inv p
  obtain ⟨A, i, hA, hi, r, hr⟩ := exists_affine_open_scheme_neighborhood B S hS T q
  let j := yoneda.map i ≫ e.hom ≫ L.ι
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : Q.IsStableUnderBaseChange := inverseImage_toScheme_isStableUnderBaseChange B S hS _
  have hi' : AlgebraicGeometry.Space.IsOpenImmersion B S hS (yoneda.map i) :=
    MorphismProperty.relative_map (P := Q) hi
  have hj : AlgebraicGeometry.Space.IsOpenImmersion B S hS j :=
    openImmersion_comp B S hS (yoneda.map i) (e.hom ≫ L.ι) hi'
      (MorphismProperty.RespectsIso.precomp _ e.hom L.ι hL.2)
  refine ⟨A, j, hA, hj, r, ?_⟩
  rw [pointsMap_comp_point, pointsMap_comp_point, hr]
  show AlgebraicGeometry.Space.pointsMap B S hS L.toFunctor L.ι
    (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj T) e.hom
      (AlgebraicGeometry.Space.pointsMap B S hS L.toFunctor e.inv p)) = x
  rw [← pointsMap_comp_point B S hS e.inv e.hom p, e.inv_hom_id, pointsMap_id_point]
  exact hp

private theorem exists_component_open_factor_through_scheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hXqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hYN : @TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Space.points B S hS Y)
      (AlgebraicGeometry.Space.pointTopology B S hS Y))
    (hYs : @QuasiSober (AlgebraicGeometry.Space.points B S hS Y)
      (AlgebraicGeometry.Space.pointTopology B S hS Y))
    (C : Set (AlgebraicGeometry.Space.points B S hS Y))
    (hC : C ∈ @irreducibleComponents _ (AlgebraicGeometry.Space.pointTopology B S hS Y)) :
    ∃ (P : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_hP : AlgebraicGeometry.IsAlgebraicSpace B S hS P) (j : P ⟶ Y),
      AlgebraicGeometry.Space.IsOpenImmersion B S hS j ∧ Mono j ∧
      (∃ p, @IsGenericPoint _ (AlgebraicGeometry.Space.pointTopology B S hS P) p Set.univ) ∧
      (letI := AlgebraicGeometry.Space.pointTopology B S hS Y
       Set.range (AlgebraicGeometry.Space.pointsMap B S hS P j) ⊆ componentGenericOpen C ∧
       C ⊆ closure (Set.range (AlgebraicGeometry.Space.pointsMap B S hS P j))) ∧
      ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (a : P ⟶ yoneda.obj U)
        (b : yoneda.obj U ⟶ X),
        AlgebraicGeometry.Space.IsImmersion B S hS b ∧ a ≫ b = j ≫ f := by
  let := AlgebraicGeometry.Space.pointTopology B S hS Y
  let := hYN
  let := hYs
  obtain ⟨η, hη⟩ := genericPoint_of_irreducibleComponent C hC
  let E := AlgebraicGeometry.Space.openSubspacesOrderIso B S hS Y hY
  let D := E.symm ⟨componentGenericOpen C, componentGenericOpen_isOpen C⟩
  have hD : AlgebraicGeometry.Space.IsOpenSubspace B S hS D.1 := D.2
  let := AlgebraicGeometry.Space.pointTopology B S hS D.1.toFunctor
  let e := AlgebraicGeometry.Space.pointsMap B S hS D.1.toFunctor D.1.ι
  have hE : Set.range e = componentGenericOpen C := by
    rw [← AlgebraicGeometry.Space.openSubspacesOrderIso_apply B S hS Y hY D]
    exact congrArg (fun U : Opens (AlgebraicGeometry.Space.points B S hS Y) => U.1)
      (E.apply_symm_apply _)
  have he : Topology.IsEmbedding e :=
    AlgebraicGeometry.Space.isEmbedding_pointsMap_of_isImmersion B S hS hY D.1.ι
      (immersion_of_openImmersion B S hS D.1.ι hD.2)
  obtain ⟨η', hη'⟩ : η ∈ Set.range e := hE ▸ genericPoint_mem_componentGenericOpen C hC hη
  have hηgeneric : IsGenericPoint η'
      (Set.univ : Set (AlgebraicGeometry.Space.points B S hS D.1.toFunctor)) := by
    rw [isGenericPoint_def, he.closure_eq_preimage_closure_image, Set.image_singleton,
      hη', hη.def]
    exact Set.eq_univ_of_forall fun x =>
      componentGenericOpen_subset C (hE ▸ Set.mem_range_self x)
  let : TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Space.points B S hS D.1.toFunctor) :=
    he.isInducing.noetherianSpace
  have hDqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS D.1.toFunctor :=
    (AlgebraicGeometry.Space.isQuasiCompactSpace_iff_compactSpace_points
      B S hS D.1.toFunctor hD.1).2
      inferInstance
  have hq := AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace
    B S hS hZ hX hXqs hDqc (D.1.ι ≫ f)
  obtain ⟨P, hP, j, hj, hjmono, hηP, hjdense, U, a, b, hb, hfac⟩ :=
    exists_dense_open_factor_through_scheme_of_genericPoint B S hS hZ
      (D.1.ι ≫ f) hD.1 hX hXqs hq η' hηgeneric
  let := AlgebraicGeometry.Space.pointTopology B S hS P
  let : Mono j := hjmono
  obtain ⟨p, hp⟩ := hηP
  have hjEmb := AlgebraicGeometry.Space.isEmbedding_pointsMap_of_isImmersion B S hS hD.1 j
    (immersion_of_openImmersion B S hS j hj)
  have hpgen : IsGenericPoint p (Set.univ : Set (AlgebraicGeometry.Space.points B S hS P)) := by
    rw [isGenericPoint_def, hjEmb.closure_eq_preimage_closure_image, Set.image_singleton,
      hp, hηgeneric.def, Set.preimage_univ]
  let q := AlgebraicGeometry.Space.pointsMap B S hS P j
  have hcomp : AlgebraicGeometry.Space.pointsMap B S hS P (j ≫ D.1.ι) = e ∘ q :=
    funext (pointsMap_comp_point B S hS j D.1.ι)
  refine ⟨P, hP, j ≫ D.1.ι, openImmersion_comp B S hS j D.1.ι hj hD.2, inferInstance,
    ⟨p, hpgen⟩, ⟨?_, ?_⟩, U, a, b, hb, ?_⟩
  · rw [hcomp, ← hE]
    exact Set.range_comp_subset_range q e
  · rw [hcomp, closure_range_comp_eq_of_denseRange he.continuous hjdense, ← hη.def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨η', hη'⟩)
  · simpa only [Category.assoc] using hfac

private theorem exists_component_affine_open_factor_through_scheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hYqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hXqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hYN : @TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Space.points B S hS Y)
      (AlgebraicGeometry.Space.pointTopology B S hS Y))
    (hYs : @QuasiSober (AlgebraicGeometry.Space.points B S hS Y)
      (AlgebraicGeometry.Space.pointTopology B S hS Y))
    (C : Set (AlgebraicGeometry.Space.points B S hS Y))
    (hC : C ∈ @irreducibleComponents _ (AlgebraicGeometry.Space.pointTopology B S hS Y)) :
    ∃ (A : AlgebraicGeometry.BigFppfOver B S hS) (j : yoneda.obj A ⟶ Y),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A) ∧
      AlgebraicGeometry.Space.IsOpenImmersion B S hS j ∧
      (letI := AlgebraicGeometry.Space.pointTopology B S hS Y
       Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) j) ⊆
         componentGenericOpen C ∧
       C ⊆ closure (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) j))) ∧
      ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj A ⟶ yoneda.obj U)
        (b : yoneda.obj U ⟶ X),
        AlgebraicGeometry.Space.IsImmersion B S hS b ∧ a ≫ b = j ≫ f := by
  let := AlgebraicGeometry.Space.pointTopology B S hS Y
  obtain ⟨P, hP, j, hj, hjmono, ⟨p, hp⟩, hjC, U, a, b, hb, hfac⟩ :=
    exists_component_open_factor_through_scheme B S hS hZ f hY hX hXqs hYN hYs C hC
  let := AlgebraicGeometry.Space.pointTopology B S hS P
  let : Mono j := hjmono
  have hPqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hP (f := j) hYqs (quasiSeparated_of_mono B S hS j)
  obtain ⟨A, k, hA, hk, q, hq⟩ := exists_affine_open_neighborhood_of_mem_schematicLocus
    B S hS hP p (genericPoint_mem_schematicLocus B S hS hZ hP hPqs p hp)
  let e := AlgebraicGeometry.Space.pointsMap B S hS P j
  let t := AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) k
  have ht : DenseRange t := denseRange_of_isGenericPoint_mem_range hp ⟨q, hq⟩
  have hcomp : AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (k ≫ j) = e ∘ t :=
    funext (pointsMap_comp_point B S hS k j)
  have he : Continuous e := AlgebraicGeometry.Space.continuous_pointsMap B S hS j
  refine ⟨A, k ≫ j, hA, openImmersion_comp B S hS k j hk hj, ⟨?_, ?_⟩,
    U, k ≫ a, b, hb, ?_⟩
  · rw [hcomp]
    rintro _ ⟨x, rfl⟩
    exact hjC.1 ⟨t x, rfl⟩
  · rw [hcomp, closure_range_comp_eq_of_denseRange he ht]
    exact hjC.2
  · simp only [Category.assoc, hfac]

private theorem exists_affineSpace_immersion_of_affine_open_factorization
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hf : AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS f)
    (A U : AlgebraicGeometry.BigFppfOver B S hS)
    (j : yoneda.obj A ⟶ Y)
    (hj : AlgebraicGeometry.Space.IsOpenImmersion B S hS j)
    (hA : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A))
    (a : yoneda.obj A ⟶ yoneda.obj U) (b : yoneda.obj U ⟶ X)
    (hfac : a ≫ b = j ≫ f) :
    ∃ (n : ℕ) (i : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A ⟶
      AffineSpace (ULift.{u} (Fin n)) ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)),
      _root_.AlgebraicGeometry.IsImmersion i ∧ i ≫ (AffineSpace.over (ULift.{u} (Fin n))
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)).hom =
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (yoneda.preimage a) := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@Etale.{u}) T
  let : MorphismProperty.IsMultiplicative (@Etale.{u}) :=
    AlgebraicGeometry.Etale.instIsMultiplicativeScheme
  let : Q.IsMultiplicative := {
    id_mem A := by
      show Etale (T.map (𝟙 A))
      rw [T.map_id]
      infer_instance
    comp_mem g h hg hh := by
      show Etale (T.map (g ≫ h))
      rw [T.map_comp]
      let : Etale (T.map g) := hg
      let : Etale (T.map h) := hh
      infer_instance }
  let : Q.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : Q.presheaf.IsMultiplicative := MorphismProperty.relative_isMultiplicative Q
  have hje : Q.presheaf j :=
    presheaf_toScheme_mono B S hS (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (P' := @Etale.{u}) (fun _ _ _ _ => inferInstance) hj
  have hjft : AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS j :=
    AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale B S hS hY (f := j) (by
      intro V g hg
      exact MorphismProperty.comp_mem Q.presheaf g j hg hje)
  have haft : AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS a :=
    AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hX a b (by
        rw [hfac]
        exact AlgebraicGeometry.Space.isLocallyOfFiniteType_comp B S hS
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) hY hX j f hjft hf)
  let : LocallyOfFiniteType (T.map (yoneda.preimage a)) :=
    haft A U (𝟙 _) (𝟙 _) (yoneda.preimage a)
      (MorphismProperty.id_mem Q.presheaf _) (MorphismProperty.id_mem Q.presheaf _)
      (by simp)
  let := hA
  exact AlgebraicGeometry.exists_immersion_affineSpace (T.map (yoneda.preimage a))

/-- Being an algebraic space is invariant under isomorphism of presheaves. -/
theorem isAlgebraicSpace_of_presheafIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS G := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).mp hF.isSheaf, ?_, ?_⟩
  · let Q : MorphismProperty ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
      yoneda.relativelyRepresentable
    have hdiag : Q (diag F) := hF.diagonal_representable
    have hprod : Q (diag F ≫ prod.map e.hom e.hom) := by
      let : Q.RespectsIso := inferInstance
      exact MorphismProperty.RespectsIso.postcomp Q (prod.map e.hom e.hom) (diag F) hdiag
    have hnaturality : diag F ≫ prod.map e.hom e.hom = e.hom ≫ diag G := by
      apply prod.hom_ext <;> simp
    have hcomp : Q (e.hom ≫ diag G) := hnaturality ▸ hprod
    let : Q.RespectsIso := inferInstance
    have hpre : Q (e.inv ≫ (e.hom ≫ diag G)) :=
      MorphismProperty.RespectsIso.precomp Q e.inv (e.hom ≫ diag G) hcomp
    simpa using hpre
  · obtain ⟨U, q, hqSurj, hqEtale⟩ := hF.exists_atlas
    refine ⟨U, q ≫ e.hom, ?_, ?_⟩
    · let Q := MorphismProperty.presheaf
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
      let : Q.RespectsIso := inferInstance
      exact MorphismProperty.RespectsIso.postcomp Q e.hom q hqSurj
    · let Q := MorphismProperty.presheaf
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
      let : Q.RespectsIso := inferInstance
      exact MorphismProperty.RespectsIso.postcomp Q e.hom q hqEtale

private theorem exists_immersion_affineSpaceOver_of_scheme_immersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A U : AlgebraicGeometry.BigFppfOver B S hS)
    (a : A ⟶ U) (b : yoneda.obj U ⟶ X)
    (hb : AlgebraicGeometry.Space.IsImmersion B S hS b) (n : ℕ)
    (i : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A ⟶
      AffineSpace (ULift.{u} (Fin n)) ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U))
    (hi : _root_.AlgebraicGeometry.IsImmersion i)
    (hifac : i ≫ (AffineSpace.over (ULift.{u} (Fin n))
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)).hom =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a) :
    ∃ j : yoneda.obj A ⟶ AlgebraicGeometry.Space.affineSpaceOver B S hS X n,
      AlgebraicGeometry.Space.IsImmersion B S hS j ∧ j ≫ prod.fst = yoneda.map a ≫ b := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let E : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (ObjectProperty.homMk
    (X := B.obj (B.contains_affineSpace hS n)) (Y := B.obj hS)
    (AffineSpace.over (ULift.{u} (Fin n)) S).hom)
  let : HasPullbacks B.Schemes := inferInstance
  let : HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let H := U ⨯ E
  have hprod : IsPullback (T.map (prod.fst : H ⟶ U)) (T.map (prod.snd : H ⟶ E))
      U.hom.hom (AffineSpace.over (ULift.{u} (Fin n)) S).hom :=
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd U E)).map B.inclusion
  have hAff : IsPullback (AffineSpace.over (ULift.{u} (Fin n)) (T.obj U)).hom
      (AffineSpace.map (ULift.{u} (Fin n)) U.hom.hom)
      U.hom.hom (AffineSpace.over (ULift.{u} (Fin n)) S).hom :=
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) U.hom.hom).flip
  let e : T.obj H ≅ AffineSpace (ULift.{u} (Fin n)) (T.obj U) :=
    hprod.isoPullback ≪≫ hAff.isoPullback.symm
  have he : e.inv ≫ T.map (prod.fst : H ⟶ U) =
      (AffineSpace.over (ULift.{u} (Fin n)) (T.obj U)).hom := by
    show (hAff.isoPullback.hom ≫ hprod.isoPullback.inv) ≫ _ = _
    rw [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]
  let m : A ⟶ H := Over.homMk (ObjectProperty.homMk (i ≫ e.inv)) (by
    apply ObjectProperty.hom_ext
    show (i ≫ e.inv) ≫ H.hom.hom = A.hom.hom
    have hh : H.hom.hom = T.map (prod.fst : H ⟶ U) ≫ U.hom.hom :=
      congrArg (fun g => g.hom) (Over.w (prod.fst : H ⟶ U)).symm
    rw [hh, ← Category.assoc, Category.assoc i, he, hifac]
    exact congrArg (fun g => g.hom) a.w)
  have hm : m ≫ prod.fst = a := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show (i ≫ e.inv) ≫ T.map (prod.fst : H ⟶ U) = T.map a
    rw [Category.assoc, he, hifac]
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsImmersion.{u}) T
  have : Q.IsStableUnderBaseChange := inverseImage_toScheme_isStableUnderBaseChange B S hS _
  have hmi : AlgebraicGeometry.Space.IsImmersion B S hS (yoneda.map m) := by
    apply MorphismProperty.relative_map (P := Q)
    show _root_.AlgebraicGeometry.IsImmersion (i ≫ e.inv)
    let := hi
    infer_instance
  let eR := (restrictedYonedaIso F).app E
  let c : yoneda.obj H ≅ yoneda.obj U ⨯ yoneda.obj E :=
    asIso (prodComparison yoneda U E)
  let d : yoneda.obj H ≅ AlgebraicGeometry.Space.affineSpaceOver B S hS (yoneda.obj U) n :=
    c ≪≫ prod.mapIso (Iso.refl _) eR.symm
  have hd : d.hom ≫ prod.fst = yoneda.map (prod.fst : H ⟶ U) := by
    show (prodComparison yoneda U E ≫ prod.map (𝟙 _) eR.inv) ≫ prod.fst = _
    simp
  let q : AlgebraicGeometry.Space.affineSpaceOver B S hS (yoneda.obj U) n ⟶
      AlgebraicGeometry.Space.affineSpaceOver B S hS X n := prod.map b (𝟙 _)
  let : Q.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  have hq : AlgebraicGeometry.Space.IsImmersion B S hS q :=
    MorphismProperty.of_isPullback (P := Q.presheaf)
      (IsPullback.of_prod_fst_with_id b _) hb
  refine ⟨(yoneda.map m ≫ d.hom) ≫ q,
    immersion_comp B S hS (yoneda.map m ≫ d.hom) q
      (MorphismProperty.RespectsIso.postcomp Q.presheaf d.hom (yoneda.map m) hmi) hq, ?_⟩
  simp only [Category.assoc, q, prod.map_fst, ← Category.assoc d.hom, hd]
  rw [← Category.assoc, ← yoneda.map_comp, hm]

end AlgebraicGeometry.Space

end
