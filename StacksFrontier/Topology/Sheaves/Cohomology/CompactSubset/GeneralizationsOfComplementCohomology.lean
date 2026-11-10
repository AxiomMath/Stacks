module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.GeneralizationsOfCohomology
public import StacksFrontier.Topology.Spectral.ConstructiblyClosed
public import StacksFrontier.Topology.Spectral.LimitGeneralizations

/-!
# Cohomology of the complement of a constructible set in its generalization locus

Let `X` be a spectral space, let `F` be a sheaf of abelian groups on `X`, let `E ⊆ X` be
quasi-compact and constructible and let `W` be the set of points of `X` which specialize to a
point of `E`. This file proves [Stacks, Tag 0A3D] (2): the canonical map

`colim_{E ⊆ U quasi-compact open} H^p(U \ E, F|_{U \ E}) ⟶ H^p(W \ E, F|_{W \ E})`

is an isomorphism in every degree.

Unlike part (1), proved in
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/GeneralizationsOfCohomology.lean`,
this needs `E` to be constructible and not merely quasi-compact: the ambient space of the whole
argument is the subspace `Eᶜ`, which is a spectral space exactly because `Eᶜ` is constructible
([Stacks, Tag 0902]).

## Main definitions

* `Stacks.Topology.openDiff`: the open `U \ E` of the subspace `Eᶜ`, for `U` an open of `X`.
* `Stacks.Topology.complementGeneralizations`: the subset `W \ E`, read inside `Eᶜ`.
* `Stacks.Topology.complementNeighborhoodCohomology`: the diagram `U ↦ H^p(U \ E, F|_{U \ E})`
  over the quasi-compact open neighbourhoods of `E`.
* `Stacks.Topology.cohomologyOfComplementGeneralizationsMap`: the comparison map of
  [Stacks, Tag 0A3D] (2).

## Main results

* `Stacks.Topology.complementGeneralizationsHomeomorph`: the subspace `W \ E` of `X` and the
  subspace `complementGeneralizations E` of `Eᶜ` are canonically homeomorphic.
* `Stacks.Topology.isStableCompact_complementGeneralizations`: `W \ E`, read inside `Eᶜ`, is
  quasi-compact and stable under generalization.
* `Stacks.Topology.exists_compactOpenNeighborhood_openDiff_le`: every open neighbourhood of
  `W \ E` in `Eᶜ` contains `U \ E` for some quasi-compact open neighbourhood `U` of `E` in `X`.
* `Stacks.Topology.initial_complementOpenNhdsFunctor`: consequently the quasi-compact open
  neighbourhoods of `E` are cofinal among the open neighbourhoods of `W \ E` in `Eᶜ`.
* `Stacks.Topology.isIso_cohomologyOfComplementGeneralizationsMap` is [Stacks, Tag 0A3D] (2).

## Implementation notes

The set `W \ E` is **not** stable under generalization in `X`: a point of `W \ E` can very well
have a generalization inside `E`. It *is* stable under generalization in the subspace `Eᶜ`, and
`Eᶜ` is again a spectral space because `E`, hence `Eᶜ`, is constructible. So the entire argument
takes place in the spectral space `Eᶜ` with the coefficients `F|_{Eᶜ}`, and the general
machinery of part (1) — which is stated for an arbitrary quasi-compact, generalization-stable
subset of an arbitrary spectral space — applies verbatim:
`Stacks.Topology.isIso_cohomologyOfClosedMap_of_isStableCompact` at the subset
`complementGeneralizations E` of `Eᶜ` is the comparison with the *open* neighbourhoods of
`W \ E` inside `Eᶜ`, and `initial_complementOpenNhdsFunctor` reindexes it by the quasi-compact
open neighbourhoods of `E` in `X`. The statement is therefore `IsIso` of a named map, exactly as
in part (1), rather than a bare isomorphism of groups.

Accordingly both sides of the comparison are read inside `Eᶜ`: the term `H^p(U \ E, F|_{U \ E})`
is the cohomology of `F|_{Eᶜ}` over the open `U \ E` of `Eᶜ`, and `H^p(W \ E, F|_{W \ E})` is the
cohomology of the restriction of `F|_{Eᶜ}` to the subset `complementGeneralizations E` of `Eᶜ`.
That subspace of `Eᶜ` is the subspace `W \ E` of `X`: `complementGeneralizationsHomeomorph`
exhibits the canonical homeomorphism between them.

Cofinality is where constructibility is spent a second time. An open neighbourhood `V` of
`W \ E` in `Eᶜ` is first shrunk to a quasi-compact one by conclusion (c) of [Stacks, Tag 0A31]
(`Stacks.Topology.StableCompact.exists_subset`), and a quasi-compact open of `Eᶜ` is the
restriction of a quasi-compact open `W'` of `X` (`exists_compactOpen_eq_preimage`). The set
`Eᶜ \ W'` is then constructible and misses `W`, so each of its points `y` admits a quasi-compact
open neighbourhood of `E` avoiding `closure {y}`; the set `Eᶜ \ W'` is quasi-compact for the
constructible topology, so finitely many of those neighbourhoods suffice, and their intersection
is a quasi-compact open neighbourhood `U` of `E` with `U \ E ⊆ V`.

## References

* [Stacks Project, Tag 0A3D](https://stacks.math.columbia.edu/tag/0A3D)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 0902](https://stacks.math.columbia.edu/tag/0902)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat Abelian

namespace Stacks.Topology

universe u

noncomputable section

/-! ### The complement of `E` in its generalization locus, read inside `Eᶜ` -/

section Subspace

variable {X : TopCat.{u}}

/-- The open `U \ E` of the subspace `Eᶜ` of `X`, for `U` an open subset of `X`. -/
def openDiff (E : Set X) (U : Opens X) : Opens (TopCat.of (Eᶜ : Set X)) :=
  ⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩

/-- A point of `Eᶜ` lies in `openDiff E U` if and only if it lies in `U`. -/
theorem mem_openDiff {E : Set X} {U : Opens X} {x : TopCat.of (Eᶜ : Set X)} :
    x ∈ openDiff E U ↔ (x : X) ∈ U :=
  Iff.rfl

/-- The map `U ↦ openDiff E U` is monotone. -/
theorem openDiff_le_openDiff {E : Set X} {U V : Opens X} (h : U ≤ V) :
    openDiff E U ≤ openDiff E V := fun _ hx ↦ h hx

/-- The points of `Eᶜ` which specialize to a point of `E`: the set `W \ E` of
[Stacks, Tag 0A3D] (2), read inside the subspace `Eᶜ`. -/
def complementGeneralizations (E : Set X) : Set (TopCat.of (Eᶜ : Set X)) :=
  Subtype.val ⁻¹' SpectralSubset.generalizationsOf E

/-- A point of `Eᶜ` lies in `complementGeneralizations E` if and only if it specializes to a
point of `E`. -/
theorem mem_complementGeneralizations {E : Set X} {x : TopCat.of (Eᶜ : Set X)} :
    x ∈ complementGeneralizations E ↔ (x : X) ∈ SpectralSubset.generalizationsOf E :=
  Iff.rfl

/-- **The subspace `W \ E` of `X` is the subspace `complementGeneralizations E` of `Eᶜ`.** -/
def complementGeneralizationsHomeomorph (E : Set X) :
    (SpectralSubset.generalizationsOf E \ E : Set X) ≃ₜ complementGeneralizations E where
  toEquiv :=
    { toFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      invFun := fun y ↦ ⟨y.1.1, y.2, y.1.2⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl) }
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- A quasi-compact open neighbourhood of `E` contains every point of `X` specializing to a
point of `E`, because an open set is stable under generalization. -/
theorem complementGeneralizations_subset_openDiff (E : Set X) {U : Opens X}
    (hEU : E ⊆ (U : Set X)) :
    complementGeneralizations E ⊆ (openDiff E U : Set (TopCat.of (Eᶜ : Set X))) := by
  rintro x ⟨y, hyE, hxy⟩
  exact hxy.mem_open U.isOpen (hEU hyE)

variable [SpectralSpace X]

/-- The subspace `Eᶜ` of a spectral space is a spectral space when `E` is constructible. This is
[Stacks, Tag 0902] for the constructible subset `Eᶜ`. -/
theorem spectralSpace_complement {E : Set X} (hE : Topology.IsConstructible E) :
    SpectralSpace (TopCat.of (Eᶜ : Set X)) :=
  spectralSpace_of_isConstructible hE.compl

/-- The set `W \ E` is quasi-compact: it is a spectral space by [Stacks, Tag 0AP0], hence
quasi-compact, and quasi-compactness passes along the embedding of `Eᶜ` into `X`. -/
theorem isCompact_complementGeneralizations {E : Set X} (hE : Topology.IsConstructible E) :
    IsCompact (complementGeneralizations E) := by
  have hdiff : IsCompact (SpectralSubset.generalizationsOf E \ E) := by
    have hsp : SpectralSpace ↥(SpectralSubset.generalizationsOf E \ E) :=
      isSpectral_specGen_diff_constructible hE
    exact isCompact_iff_compactSpace.mpr inferInstance
  rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal]
  change IsCompact (Subtype.val '' (Subtype.val ⁻¹' SpectralSubset.generalizationsOf E))
  rw [Subtype.image_preimage_coe]
  simpa only [Set.sdiff_eq, Set.inter_comm] using hdiff

omit [SpectralSpace X] in
/-- The set `W \ E`, read inside `Eᶜ`, is stable under generalization: a generalization in `Eᶜ`
of a point of `Eᶜ` is a generalization of it in `X`, and `W` is stable under generalization
in `X`. -/
theorem stableUnderGeneralization_complementGeneralizations (E : Set X) :
    StableUnderGeneralization (complementGeneralizations E) := fun _ _ hxy hy ↦
  stableUnderGeneralization_specGen E
    (Topology.IsInducing.subtypeVal.specializes_iff.mpr hxy) hy

/-- **The set `W \ E`, read inside `Eᶜ`, is quasi-compact and stable under generalization**, so
that the machinery of part (1) applies to it. -/
theorem isStableCompact_complementGeneralizations {E : Set X}
    (hE : Topology.IsConstructible E) :
    SpectralSubset.IsStableCompact (complementGeneralizations E) :=
  ⟨isCompact_complementGeneralizations hE,
    stableUnderGeneralization_complementGeneralizations E⟩

end Subspace

/-! ### Cofinality of the quasi-compact open neighbourhoods of `E` -/

section Cofinal

variable {X : TopCat.{u}} [SpectralSpace X]

/-- **A quasi-compact open neighbourhood of `W \ E` in `Eᶜ` is refined by one coming from `X`.**
If `V` is a quasi-compact open of `Eᶜ` containing `W \ E`, then there is a quasi-compact open
neighbourhood `U` of `E` in `X` with `U \ E ⊆ V`. -/
private theorem exists_compactOpen_openDiff_le_of_isCompact {E : Set X}
    (hE : Topology.IsConstructible E) (hEc : IsCompact E)
    (V : Opens (TopCat.of (Eᶜ : Set X)))
    (hVc : IsCompact (V : Set (TopCat.of (Eᶜ : Set X))))
    (hV : complementGeneralizations E ⊆ (V : Set (TopCat.of (Eᶜ : Set X)))) :
    ∃ U : Opens X, IsCompact (U : Set X) ∧ E ⊆ (U : Set X) ∧ openDiff E U ≤ V := by
  classical
  have : SpectralSpace (TopCat.of (Eᶜ : Set X)) := spectralSpace_complement hE
  obtain ⟨W, hWo, hWc, hVeq⟩ :=
    exists_compactOpen_eq_preimage (Eᶜ : Set X) (V : Set (TopCat.of (Eᶜ : Set X))) V.isOpen hVc
  -- The part of `Eᶜ` outside `W` is constructible and misses `W \ E`.
  set D : Set X := Eᶜ \ W with hDdef
  have hDcompact : @IsCompact X (constructibleTopology X) D :=
    (_root_.IsConstructible.isClosed_constructibleTopology
      (hE.compl.sdiff (hWc.isConstructible hWo))).isCompact_constructibleTopology
  have hnotGen : ∀ y ∈ D, y ∉ SpectralSubset.generalizationsOf E := fun y hy hgen ↦
    hy.2 ((Set.ext_iff.1 hVeq ⟨y, hy.1⟩).1 (hV hgen))
  -- Each point of `D` is avoided by a quasi-compact open neighbourhood of `E`.
  have hExists : ∀ y ∈ D,
      ∃ U : Set X, IsCompact U ∧ IsOpen U ∧ E ⊆ U ∧ U ⊆ (closure ({y} : Set X))ᶜ := by
    intro y hy
    refine PrespectralSpace.exists_isCompact_and_isOpen_between hEc
      isClosed_closure.isOpen_compl fun e he hecl ↦ ?_
    exact hnotGen y hy ⟨e, he, specializes_iff_mem_closure.2 hecl⟩
  choose! O hOc hOo hEO hOy using hExists
  -- Finitely many of them already cover the complement of `D`.
  have hcover : D ⊆ ⋃ y : {y : X // y ∈ D}, (O y.1)ᶜ := fun y hy ↦
    Set.mem_iUnion.2 ⟨⟨y, hy⟩, fun hyO ↦ hOy y hy hyO (subset_closure rfl)⟩
  have hcoverOpen : ∀ y : {y : X // y ∈ D},
      @IsOpen X (constructibleTopology X) ((O y.1)ᶜ) := fun y ↦
    (@isOpen_compl_iff X (O y.1) (constructibleTopology X)).2
      ((hOc y.1 y.2).isClopen_constructibleTopology (hOo y.1 y.2)).1
  obtain ⟨t, hscov⟩ :=
    @IsCompact.elim_finite_subcover X (constructibleTopology X) D {y : X // y ∈ D} hDcompact
      (fun y ↦ (O y.1)ᶜ) hcoverOpen hcover
  set S : Set (Set X) := (fun y : {y : X // y ∈ D} ↦ O y.1) '' (t : Set {y : X // y ∈ D})
    with hSdef
  have hSfin : S.Finite := t.finite_toSet.image _
  have hSopen : ∀ A ∈ S, IsOpen A := by
    rintro A ⟨y, -, rfl⟩; exact hOo y.1 y.2
  have hScompact : ∀ A ∈ S, IsCompact A := by
    rintro A ⟨y, -, rfl⟩; exact hOc y.1 y.2
  -- Their intersection is a quasi-compact open neighbourhood of `E` contained in `W`.
  refine ⟨⟨⋂₀ S, hSfin.isOpen_sInter hSopen⟩,
    QuasiSeparatedSpace.isCompact_sInter hSfin (fun A hA ↦ Or.inl (hSopen A hA)) hScompact,
    fun x hx ↦ Set.mem_sInter.2 ?_, fun x hx ↦ ?_⟩
  · rintro A ⟨y, -, rfl⟩
    exact hEO y.1 y.2 hx
  · have hxU : (x : X) ∈ ⋂₀ S := hx
    have hxW : (x : X) ∈ W := by
      by_contra hxW
      obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (hscov ⟨x.2, hxW⟩)
      obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.1 hy
      exact hxy (Set.mem_sInter.1 hxU (O y.1) ⟨y, hyt, rfl⟩)
    exact (Set.ext_iff.1 hVeq x).2 hxW

/-- **Every open neighbourhood of `W \ E` in `Eᶜ` is refined by one coming from `X`.** If `V` is
an open of `Eᶜ` containing `W \ E`, then there is a quasi-compact open neighbourhood `U` of `E`
in `X` with `U \ E ⊆ V`. -/
theorem exists_compactOpenNeighborhood_openDiff_le {E : Set X}
    (hE : Topology.IsConstructible E) (hEc : IsCompact E)
    {V : Opens (TopCat.of (Eᶜ : Set X))}
    (hV : complementGeneralizations E ⊆ (V : Set (TopCat.of (Eᶜ : Set X)))) :
    ∃ U : SpectralSubset.CompactOpenNeighborhood E,
      openDiff E ⟨(U : Set X), U.2.1⟩ ≤ V := by
  have : SpectralSpace (TopCat.of (Eᶜ : Set X)) := spectralSpace_complement hE
  obtain ⟨V₀, hV₀⟩ := StableCompact.exists_subset (complementGeneralizations E)
    (isStableCompact_complementGeneralizations hE) V.isOpen hV
  obtain ⟨U, hUc, hEU, hUV⟩ := exists_compactOpen_openDiff_le_of_isCompact hE hEc
    ⟨(V₀ : Set (TopCat.of (Eᶜ : Set X))), V₀.2.1⟩ V₀.2.2.1 V₀.2.2.2
  exact ⟨⟨(U : Set X), U.isOpen, hUc, hEU⟩, hUV.trans hV₀⟩

/-- A quasi-compact open neighbourhood `U` of `E` gives the open neighbourhood `U \ E` of
`W \ E` in `Eᶜ`, functorially in the inclusion. -/
def complementOpenNhdsFunctor (E : Set X) :
    SpectralSubset.CompactOpenNeighborhood E ⥤ OpenNhdsSet (complementGeneralizations E) where
  obj U := ⟨openDiff E ⟨(U : Set X), U.2.1⟩,
    complementGeneralizations_subset_openDiff E U.2.2.2⟩
  map f := ObjectProperty.homMk (homOfLE (openDiff_le_openDiff (leOfHom f)))
  map_id _ := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)
  map_comp _ _ := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)

/-- **The quasi-compact open neighbourhoods of a quasi-compact constructible `E` are cofinal
among the open neighbourhoods of `W \ E` in `Eᶜ`.** -/
theorem initial_complementOpenNhdsFunctor {E : Set X} (hE : Topology.IsConstructible E)
    (hEc : IsCompact E) : (complementOpenNhdsFunctor E).Initial := by
  classical
  refine ⟨fun V ↦ ?_⟩
  obtain ⟨U₀, hU₀⟩ := exists_compactOpenNeighborhood_openDiff_le hE hEc V.property
  have : Nonempty (CostructuredArrow (complementOpenNhdsFunctor E) V) :=
    ⟨CostructuredArrow.mk (Y := U₀) (ObjectProperty.homMk (homOfLE hU₀))⟩
  have : IsCofilteredOrEmpty (CostructuredArrow (complementOpenNhdsFunctor E) V) := by
    refine ⟨fun a b ↦ ?_, fun {a b} f g ↦ ⟨a, 𝟙 a, ?_⟩⟩
    · obtain ⟨c, hca, hcb⟩ := directed_of (· ≥ ·) a.left b.left
      exact ⟨CostructuredArrow.mk ((complementOpenNhdsFunctor E).map (homOfLE hca) ≫ a.hom),
        CostructuredArrow.homMk (homOfLE hca) rfl,
        CostructuredArrow.homMk (homOfLE hcb)
          (ObjectProperty.hom_ext _ (Subsingleton.elim _ _)), trivial⟩
    · rw [Category.id_comp, Category.id_comp]
      exact CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)
  have : IsCofiltered (CostructuredArrow (complementOpenNhdsFunctor E) V) := IsCofiltered.mk
  exact IsCofiltered.isConnected _

end Cofinal

/-! ### Stacks 0A3D (2) -/

section Main

variable {X : TopCat.{u}} [SpectralSpace X] (E : Set X)
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of (Eᶜ : Set X))) AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology
    (TopCat.of (complementGeneralizations E))) AddCommGrpCat.{u})]

/-- The diagram `U ↦ H^p(U \ E, F|_{U \ E})` over the quasi-compact open neighbourhoods of `E`,
formed inside the subspace `Eᶜ`. -/
abbrev complementNeighborhoodCohomology
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    (SpectralSubset.CompactOpenNeighborhood E)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (complementOpenNhdsFunctor E).op ⋙
    openNeighborhoodCohomology (complementGeneralizations E)
      ((restrictionFunctor X (Eᶜ : Set X)).obj F) p

/-- **The comparison map of [Stacks, Tag 0A3D] (2)**, from the colimit of the cohomology of
`F` over the sets `U \ E`, for `U` a quasi-compact open neighbourhood of `E`, to the cohomology
of the restriction of `F` to `W \ E`. It is the comparison map of [Stacks, Tag 09V3] for the
subset `W \ E` of the spectral space `Eᶜ`, precomposed with the passage from the colimit over
the quasi-compact open neighbourhoods of `E` to the colimit over all open neighbourhoods of
`W \ E` in `Eᶜ`. -/
def cohomologyOfComplementGeneralizationsMap
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    colimit (complementNeighborhoodCohomology E F p) ⟶
      (((restrictionFunctor (TopCat.of (Eᶜ : Set X)) (complementGeneralizations E)).obj
        ((restrictionFunctor X (Eᶜ : Set X)).obj F)).cohomologyPresheaf p).obj (op ⊤) :=
  colimit.pre (openNeighborhoodCohomology (complementGeneralizations E)
        ((restrictionFunctor X (Eᶜ : Set X)).obj F) p)
      (complementOpenNhdsFunctor E).op ≫
    cohomologyOfClosedMap (complementGeneralizations E)
      ((restrictionFunctor X (Eᶜ : Set X)).obj F) p

/-- **[Stacks, Tag 0A3D] (2).** Let `X` be a spectral space, let `F` be an abelian sheaf on `X`,
let `E ⊆ X` be quasi-compact and constructible and let `W` be the set of points of `X` which
specialize to a point of `E`. Then for every `p` the canonical map

`colim_{E ⊆ U quasi-compact open} H^p(U \ E, F|_{U \ E}) ⟶ H^p(W \ E, F|_{W \ E})`

is an isomorphism. -/
@[stacks 0A3D "cohomology_of_complements"]
theorem isIso_cohomologyOfComplementGeneralizationsMap (hE : Topology.IsConstructible E)
    (hEc : IsCompact E) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (cohomologyOfComplementGeneralizationsMap E F p) := by
  have : SpectralSpace (TopCat.of (Eᶜ : Set X)) := spectralSpace_complement hE
  have : (complementOpenNhdsFunctor E).Initial := initial_complementOpenNhdsFunctor hE hEc
  have := isIso_cohomologyOfClosedMap_of_isStableCompact (complementGeneralizations E)
    (isStableCompact_complementGeneralizations hE) ((restrictionFunctor X (Eᶜ : Set X)).obj F) p
  exact IsIso.comp_isIso

end Main

end

end Stacks.Topology

end
