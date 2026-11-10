module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap
public import StacksFrontier.Topology.Connected.ClopenIntersection
public import StacksFrontier.Topology.Connected.ComponentSpaceCompact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invariance of `π₀` and `π₁` under an equivalence of finite étale covers

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes for which the base
change functor `FÉt_Y ⥤ FÉt_X` is an equivalence of categories. Then `f` already determines the
space of connected components and the étale fundamental group of `Y`.

The mechanism is that clopen subsets are finite étale covers: a clopen subset of `X` is the same
thing as a finite étale cover of `X` which is a subobject of the terminal cover, and an
equivalence carries subobjects of the terminal cover to subobjects of the terminal cover. Hence
taking preimages along `f` identifies the lattice of clopen subsets of `Y` with that of `X`.
The underlying space of a quasi-compact quasi-separated scheme is spectral, so that lattice
determines the set of connected components (Stacks 005F), and the space of connected components
of such a space is profinite (Stacks 0900), so a continuous bijection between two of them is a
homeomorphism.

For fundamental groups, base change of a finite étale cover of `Y` to `X` does not change its
geometric fibre at a geometric point `x` of `X`: the canonical projection
`AlgebraicGeometry.finiteEtaleFiberProjection` is a bijection, naturally in the cover. So the
fibre functor of `X` at `x`, precomposed with base change, is the fibre functor of `Y` at the
image point, and the automorphism groups of the two functors agree. The resulting isomorphism is
the canonical induced map `AlgebraicGeometry.etaleFundamentalGroupMap`.

## Main results

* `AlgebraicGeometry.isHomeomorph_connectedComponentsMap_of_finiteEtaleBaseChange` — part (1) of
  Stacks 0BQA: the induced map `π₀(X) → π₀(Y)` is a homeomorphism.
* `AlgebraicGeometry.connectedSpace_iff_of_finiteEtaleBaseChange` — the "or equivalently" of
  part (2): `X` is connected if and only if `Y` is.
* `AlgebraicGeometry.fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange` — part (2) of
  Stacks 0BQA: for connected `X` and `Y` the induced continuous homomorphism identifies
  `π₁(X, x)` with `π₁(Y, f ∘ x)` as topological groups.

## Implementation notes

Part (1) is stated as `IsHomeomorph` for `Continuous.connectedComponentsMap` of the underlying
continuous map of `f`, rather than as the existence of some homeomorphism; this records that the
homeomorphism is the canonical map and keeps its compatibility with the quotient maps from the
schemes.

The source's equality `π₁(X, x) = π₁(Y, f ∘ x)` in part (2) is a canonical isomorphism, formalized
as a `ContinuousMulEquiv` bundled with the statement that its underlying map is the induced
homomorphism `AlgebraicGeometry.etaleFundamentalGroupMap`. Without that side condition the
statement would only assert that two groups are abstractly isomorphic. Through
`AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection` the side condition says
that the isomorphism intertwines the two actions on the geometric fibre of every finite étale
cover of `Y`.

Part (2) takes connectedness of both `X` and `Y` as hypotheses, because `π₁(Y, f ∘ x)` is only
defined for connected `Y`; `AlgebraicGeometry.connectedSpace_iff_of_finiteEtaleBaseChange` is the
content of the source's "or equivalently", and it is deduced from part (1).

## References

* [Stacks Project, Tag 0BQA](https://stacks.math.columbia.edu/tag/0BQA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Clopen subsets as subobjects of the terminal finite étale cover -/

/-- The terminal finite étale cover `X ⟶ X` of a scheme. -/
private abbrev finiteEtaleTerminal (Y : Scheme.{u}) : FiniteEtaleOver Y :=
  MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) (𝟙 Y) ⟨inferInstance, inferInstance⟩

/-- The structure morphism of a finite étale cover, read as a morphism to the terminal cover. -/
private abbrev finiteEtaleToTerminal {Y : Scheme.{u}} (V : FiniteEtaleOver Y) :
    V ⟶ finiteEtaleTerminal Y :=
  MorphismProperty.Over.homMk (P := finiteEtale) (Q := ⊤) V.hom
    (by change V.hom ≫ 𝟙 Y = V.hom; simp)

/-- A finite étale cover which is a subobject of the terminal cover has monomorphic structure
morphism: the two projections of its self-fibre product are again morphisms of finite étale
covers, and they are identified by the assumed monomorphism. -/
private theorem mono_hom_of_mono_finiteEtaleToTerminal {Y : Scheme.{u}} (V : FiniteEtaleOver Y)
    (hV : Mono (finiteEtaleToTerminal V)) : Mono V.hom := by
  let g := V.hom
  have hfst : finiteEtale (pullback.fst g g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g g).flip V.prop
  have _ : IsFinite (pullback.fst g g) := hfst.1
  have _ : Etale (pullback.fst g g) := hfst.2
  have _ : IsFinite g := V.prop.1
  have _ : Etale g := V.prop.2
  let D : FiniteEtaleOver Y := MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤)
    (pullback.fst g g ≫ g) ⟨inferInstance, inferInstance⟩
  let p₁ : D ⟶ V := MorphismProperty.Over.homMk (P := finiteEtale) (Q := ⊤) (pullback.fst g g) rfl
  let p₂ : D ⟶ V := MorphismProperty.Over.homMk (P := finiteEtale) (Q := ⊤) (pullback.snd g g)
    (pullback.condition (f := g) (g := g)).symm
  have hp : p₁ = p₂ := (cancel_mono (finiteEtaleToTerminal V)).1 <|
    MorphismProperty.Over.Hom.ext (pullback.condition (f := g) (g := g))
  exact (CategoryTheory.mono_iff_fst_eq_snd (pullbackIsPullback g g)).2 (congrArg (·.left) hp)

/-- The inclusion of a clopen open subscheme is finite étale: it is an open immersion, and it is
a closed immersion because its range is closed. -/
private theorem finiteEtale_ι_of_isClosed {Y : Scheme.{u}} (U : Y.Opens)
    (hU : IsClosed (U : Set Y)) : finiteEtale U.ι := by
  have _ : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι (by simpa [Scheme.Opens.range_ι] using hU)
  exact ⟨inferInstance, inferInstance⟩

/-- Conversely, a subobject of the terminal finite étale cover has clopen range: its structure
morphism is a monomorphism, hence an open immersion by flatness and a closed immersion by
finiteness. -/
private theorem isClopen_range_of_mono_finiteEtaleToTerminal {Y : Scheme.{u}}
    (V : FiniteEtaleOver Y) (hV : Mono (finiteEtaleToTerminal V)) :
    IsClopen (Set.range V.hom) := by
  have hmono : Mono V.hom := mono_hom_of_mono_finiteEtaleToTerminal V hV
  have hprops := (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified).mp V.prop.2
  have _ : Flat V.hom := hprops.1
  have _ : LocallyOfFinitePresentation V.hom := hprops.2.2
  have hopen : IsOpenImmersion V.hom := IsOpenImmersion.of_flat_of_mono V.hom
  have hclosed : IsClosedImmersion V.hom :=
    (IsClosedImmersion.iff_isFinite_and_mono V.hom).2 ⟨V.prop.1, hmono⟩
  exact ⟨hclosed.isClosedEmbedding.isClosed_range, hopen.isOpen_range⟩

/-- Every clopen subset of `X` is the preimage of a clopen subset of `Y`. The clopen is a finite
étale cover of `X` which is a subobject of the terminal cover; an essential preimage of it under
the equivalence is a subobject of the terminal cover of `Y`, hence a clopen subset of `Y`, and
base change computes its preimage. -/
private theorem exists_isClosed_preimage_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : (finiteEtaleBaseChange f).IsEquivalence) (U : X.Opens) (hU : IsClosed (U : Set X)) :
    ∃ V : Y.Opens, IsClosed (V : Set Y) ∧ f ⁻¹ᵁ V = U := by
  let F := finiteEtaleBaseChange f
  let W : FiniteEtaleOver X :=
    MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) U.ι (finiteEtale_ι_of_isClosed U hU)
  have _ : F.IsEquivalence := hf
  obtain ⟨V, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage F W
  let qPull : F.obj V ⟶ F.obj (finiteEtaleTerminal Y) := F.map (finiteEtaleToTerminal V)
  have _ : Mono W.hom := by change Mono U.ι; infer_instance
  have _ : Mono qPull.left :=
    mono_of_mono_fac ((MorphismProperty.Over.w qPull).trans (MorphismProperty.Over.w e.hom).symm)
  have hmonoPull : Mono qPull := ⟨fun a b hab =>
    MorphismProperty.Over.Hom.ext ((cancel_mono qPull.left).1 (congrArg (·.left) hab))⟩
  have hrangeClopen :=
    isClopen_range_of_mono_finiteEtaleToTerminal V (F.mono_of_mono_map hmonoPull)
  let V' : Y.Opens := ⟨Set.range V.hom, hrangeClopen.2⟩
  have hrangePull : Set.range (F.obj V).hom = f ⁻¹' Set.range V.hom := by
    change Set.range (pullback.snd V.hom f) = f ⁻¹' Set.range V.hom
    simpa using Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback V.hom f)
      (Set.univ : Set V.left)
  have hrangeU : Set.range (F.obj V).hom = (U : Set X) := by
    have he : e.hom.left ≫ W.hom = (F.obj V).hom := MorphismProperty.Over.w e.hom
    rw [← he]
    exact (e.hom.left.surjective.range_comp W.hom).trans (Scheme.Opens.range_ι U)
  have hset : f ⁻¹' (V' : Set Y) = (U : Set X) := by
    simpa [V'] using hrangePull.symm.trans hrangeU
  refine ⟨V', hrangeClopen.1, ?_⟩
  ext x
  change x ∈ (TopologicalSpace.Opens.map f.base).obj V' ↔ x ∈ U
  rw [Scheme.Hom.mem_preimage]
  simpa using (Set.ext_iff.mp hset x)

/-- The image of `f` meets every nonempty clopen subset of `Y`. Otherwise the complementary
clopen subset `W` is a finite étale cover of `Y` whose structure morphism is not an isomorphism,
while its base change to `X` is all of `X`, hence an isomorphism; an equivalence reflects
isomorphisms. -/
private theorem exists_mem_of_isClosed_of_nonempty {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : (finiteEtaleBaseChange f).IsEquivalence) (U : Y.Opens)
    (hUclosed : IsClosed (U : Set Y)) (hUne : (U : Set Y).Nonempty) : ∃ x : X, f x ∈ U := by
  by_contra hmiss
  let W : Y.Opens := ⟨(U : Set Y)ᶜ, hUclosed.isOpen_compl⟩
  have hpre : f ⁻¹ᵁ W = ⊤ := by
    ext x
    change f x ∉ (U : Set Y) ↔ True
    exact ⟨fun _ => trivial, fun _ hxu => hmiss ⟨x, hxu⟩⟩
  have hWclosed : IsClosed (W : Set Y) := isClosed_compl_iff.mpr U.2
  let A : FiniteEtaleOver Y :=
    MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) W.ι
      (finiteEtale_ι_of_isClosed W hWclosed)
  let q : A ⟶ finiteEtaleTerminal Y := finiteEtaleToTerminal A
  let F := finiteEtaleBaseChange f
  let qPull : F.obj A ⟶ F.obj (finiteEtaleTerminal Y) := F.map q
  have hsource : IsIso (F.obj A).hom := by
    change IsIso (pullback.snd W.ι f)
    have hpreι : IsIso (f ⁻¹ᵁ W).ι := by
      rw [hpre]
      have _ : IsIso ((⊤ : X.Opens).ι) := (Scheme.topIso X).isIso_hom
      infer_instance
    have hc : IsIso ((isPullback_morphismRestrict f W).isoPullback.inv ≫ (f ⁻¹ᵁ W).ι) :=
      inferInstance
    rwa [IsPullback.isoPullback_inv_snd (isPullback_morphismRestrict f W)] at hc
  have htarget : IsIso (F.obj (finiteEtaleTerminal Y)).hom := by
    change IsIso (pullback.snd (𝟙 Y) f)
    infer_instance
  have hcomp : qPull.left ≫ (F.obj (finiteEtaleTerminal Y)).hom = (F.obj A).hom :=
    MorphismProperty.Over.w qPull
  have hleft : IsIso qPull.left := IsIso.of_isIso_fac_right hcomp
  let qInv : F.obj (finiteEtaleTerminal Y) ⟶ F.obj A :=
    MorphismProperty.Over.homMk (inv qPull.left) (by rw [← hcomp, IsIso.inv_hom_id_assoc])
  have hqPull : IsIso qPull :=
    ⟨qInv, MorphismProperty.Over.Hom.ext (IsIso.hom_inv_id qPull.left),
      MorphismProperty.Over.Hom.ext (IsIso.inv_hom_id qPull.left)⟩
  have _ : F.IsEquivalence := hf
  have hq : IsIso q := Functor.ReflectsIsomorphisms.reflects F q
  have _ : IsIso W.ι := by change IsIso q.left; infer_instance
  obtain ⟨y, hy⟩ := hUne
  obtain ⟨w, hw⟩ := W.ι.surjective y
  exact (Scheme.Opens.range_ι W ▸ ⟨w, hw⟩ : y ∈ (W : Set Y)) hy

/-! ### The topology of the space of connected components -/

/-- In a quasi-compact quasi-separated prespectral space the connected component of a point is
the intersection of the clopen subsets containing it: Stacks 005F for spectral spaces. -/
private theorem connectedComponent_eq_iInter_isClopen_prespectral {X : Type u}
    [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] (x : X) :
    connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, (Z : Set X) :=
  connectedComponent_eq_iInter_isClopen_of_compactSpace
    PrespectralSpace.isTopologicalBasis (fun _ hZ => hZ.2)
    (fun A B => QuasiSeparatedSpace.inter_isCompact A B) x

/-- The same statement in the shape taken by Stacks 0900: every connected component is the
intersection of the clopen subsets containing it. -/
private theorem connectedComponent_eq_sInter_isClopen_scheme {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (x : X) :
    connectedComponent x = ⋂₀ { U : Set X | IsClopen U ∧ connectedComponent x ⊆ U } := by
  rw [connectedComponent_eq_iInter_isClopen_prespectral]
  ext y
  simp only [Set.mem_iInter, Set.mem_sInter, Set.mem_ofPred_eq]
  refine ⟨fun hy U hU => hU.2 (Set.mem_iInter.mpr hy), fun hy Z => ?_⟩
  have hsub : (⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, (Z : Set X)) ⊆ Z := by
    rw [← connectedComponent_eq_iInter_isClopen_prespectral]
    exact Z.2.1.connectedComponent_subset Z.2.2
  exact hy Z.1 ⟨Z.2.1, hsub⟩

/-- An open set containing the connected component of a point contains a clopen neighbourhood of
that point, in a quasi-compact quasi-separated prespectral space. -/
private theorem exists_isClopen_mem_subset {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [PrespectralSpace X] [QuasiSeparatedSpace X] (U : Set X) (hU : IsOpen U) (x : X)
    (hcomp : connectedComponent x ⊆ U) : ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  have hdisj : Disjoint (⋂ Z ∈ { s : Set X | IsClopen s ∧ x ∈ s }, Z) Uᶜ := by
    refine Set.disjoint_left.mpr fun y hy hny => hny (hcomp ?_)
    rw [connectedComponent_eq_iInter_isClopen_prespectral]
    exact Set.mem_iInter.mpr fun Z => Set.mem_iInter₂.mp hy Z.1 Z.2
  obtain ⟨T, hT, hTdisj⟩ :=
    exists_finite_clopen_inter_disjoint_isCompact x hU.isClosed_compl.isCompact hdisj
  exact ⟨⋂ Z ∈ T, (Z : Set X), isClopen_biInter_finset fun Z hZ => (hT Z hZ).1,
    Set.mem_iInter₂.mpr fun Z hZ => (hT Z hZ).2,
    fun y hy => not_not.1 fun hyU => Set.disjoint_left.mp hTdisj hy hyU⟩

/-! ### Part (1): the homeomorphism on connected components -/

/-- **Stacks Project, Tag 0BQA, part (1).** Let `f : X ⟶ Y` be a morphism of quasi-compact and
quasi-separated schemes such that the base change functor `FÉt_Y ⥤ FÉt_X` is an equivalence of
categories. Then the induced map `π₀(X) → π₀(Y)` on spaces of connected components is a
homeomorphism.

The equivalence identifies the clopen subsets of `Y` with those of `X` by taking preimages, and
in a spectral space that lattice determines the connected components; both spaces of connected
components are profinite, so a continuous bijection between them is a homeomorphism. -/
@[stacks 0BQA "part (1)"]
theorem isHomeomorph_connectedComponentsMap_of_finiteEtaleBaseChange {X Y : Scheme.{u}}
    (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (hf : (finiteEtaleBaseChange f).IsEquivalence) :
    IsHomeomorph f.continuous.connectedComponentsMap := by
  have hprofX := isProfiniteSpacePropForm_connectedComponents X
    (fun x => connectedComponent_eq_sInter_isClopen_scheme x)
  have hprofY := isProfiniteSpacePropForm_connectedComponents Y
    (fun y => connectedComponent_eq_sInter_isClopen_scheme y)
  have _ : CompactSpace (ConnectedComponents X) := hprofX.1
  have _ : T2Space (ConnectedComponents X) := hprofX.2.1
  have _ : CompactSpace (ConnectedComponents Y) := hprofY.1
  have _ : T2Space (ConnectedComponents Y) := hprofY.2.1
  have hcont : Continuous f.continuous.connectedComponentsMap :=
    f.continuous.connectedComponentsMap_continuous
  refine isHomeomorph_iff_continuous_bijective.mpr ⟨hcont, ?_, ?_⟩
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    have hcomp : connectedComponent (f x) = connectedComponent (f y) :=
      ConnectedComponents.coe_eq_coe.mp (by simpa using hab)
    refine ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq ?_)
    rw [connectedComponent_eq_iInter_isClopen_prespectral]
    refine Set.mem_iInter.mpr ?_
    rintro ⟨U, hUcl, hxU⟩
    obtain ⟨V, hVclosed, hpre⟩ :=
      exists_isClosed_preimage_eq f hf ⟨U, hUcl.isOpen⟩ hUcl.isClosed
    have hVcl : IsClopen (V : Set Y) := ⟨hVclosed, V.2⟩
    have hxV : f x ∈ (V : Set Y) := (Scheme.Hom.mem_preimage f).1 (hpre ▸ hxU)
    have hyV : f y ∈ (V : Set Y) :=
      hVcl.connectedComponent_subset hxV (hcomp ▸ mem_connectedComponent)
    have hy : y ∈ f ⁻¹ᵁ V := (Scheme.Hom.mem_preimage f).2 hyV
    rw [hpre] at hy
    exact hy
  · intro c
    by_contra hc
    have hOopen : IsOpen (Set.range f.continuous.connectedComponentsMap)ᶜ :=
      (isCompact_range hcont).isClosed.isOpen_compl
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    have hcompU : connectedComponent y ⊆
        ConnectedComponents.mk ⁻¹' (Set.range f.continuous.connectedComponentsMap)ᶜ := by
      intro z hz
      rw [Set.mem_preimage, ConnectedComponents.coe_eq_coe'.mpr hz]
      exact hc
    obtain ⟨V, hVcl, hyV, hVU⟩ := exists_isClopen_mem_subset
      (ConnectedComponents.mk ⁻¹' (Set.range f.continuous.connectedComponentsMap)ᶜ)
      (hOopen.preimage ConnectedComponents.continuous_coe) y hcompU
    obtain ⟨x, hx⟩ :=
      exists_mem_of_isClosed_of_nonempty f hf ⟨V, hVcl.isOpen⟩ hVcl.isClosed ⟨y, hyV⟩
    exact hVU hx ⟨ConnectedComponents.mk x, by simp⟩

/-- A space is connected exactly when its space of connected components is a single point. -/
private theorem connectedSpace_iff_connectedComponents {α : Type*} [TopologicalSpace α] :
    ConnectedSpace α ↔
      Nonempty (ConnectedComponents α) ∧ Subsingleton (ConnectedComponents α) := by
  rw [connectedSpace_iff_univ]
  refine ⟨fun h => ?_, fun hp => ?_⟩
  · have _ : ConnectedSpace α := connectedSpace_iff_univ.mpr h
    exact ⟨inferInstance, inferInstance⟩
  · obtain ⟨hne, hsub⟩ := hp
    rw [ConnectedComponents.nonempty_iff_nonempty] at hne
    obtain ⟨x₀⟩ := hne
    have huniv : connectedComponent x₀ = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      rw [← ConnectedComponents.coe_eq_coe.mp (Subsingleton.elim
        (ConnectedComponents.mk y) (ConnectedComponents.mk x₀))]
      exact mem_connectedComponent
    exact ⟨⟨x₀, Set.mem_univ _⟩, huniv ▸ isPreconnected_connectedComponent⟩

/-- **Stacks Project, Tag 0BQA, part (2), the "or equivalently".** Under the hypotheses of
Tag 0BQA the source is connected if and only if the target is: part (1) puts the two spaces of
connected components in bijection, and a space is connected exactly when its space of connected
components is a single point. -/
@[stacks 0BQA "part (2), the source is connected iff the target is",
  sga "4 XII 6.5" "(ii) b')⇒b'') π₀"]
theorem connectedSpace_iff_of_finiteEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hf : (finiteEtaleBaseChange f).IsEquivalence) : ConnectedSpace X ↔ ConnectedSpace Y := by
  have e := Equiv.ofBijective _
    (isHomeomorph_connectedComponentsMap_of_finiteEtaleBaseChange f hf).bijective
  rw [connectedSpace_iff_connectedComponents, connectedSpace_iff_connectedComponents,
    e.nonempty_congr, e.subsingleton_congr]

/-! ### Part (2): the isomorphism of fundamental groups -/

/-- The induced homomorphism of fundamental groups is a group isomorphism when base change on
finite étale covers is an equivalence: precomposition with an equivalence is an equivalence of
functor categories, hence identifies the automorphism group of the fibre functor of `X` with that
of its restriction along base change, which is the fibre functor of `Y`. -/
def etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [ConnectedSpace X] [ConnectedSpace Y] [(finiteEtaleBaseChange f).IsEquivalence]
    (x : GeometricPoint X) :
    EtaleFundamentalGroup X x ≃* EtaleFundamentalGroup Y (x.map f) :=
  (Functor.FullyFaithful.autMulEquivOfFullyFaithful
    ((Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) (Type u)).obj
      (finiteEtaleBaseChange f)).asEquivalence.fullyFaithfulFunctor
    (finiteEtaleFiberFunctor x)).trans (finiteEtaleFiberProjectionIso f x).conjAut

/-- The group isomorphism is the canonical induced map on fundamental groups. -/
theorem etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange_apply {X Y : Scheme.{u}}
    (f : X ⟶ Y) [ConnectedSpace X] [ConnectedSpace Y]
    [(finiteEtaleBaseChange f).IsEquivalence] (x : GeometricPoint X)
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange f x σ =
      etaleFundamentalGroupMap f x σ := rfl

/-- **Stacks Project, Tag 0BQA, part (2).** Let `f : X ⟶ Y` be a morphism of connected schemes
such that the base change functor `FÉt_Y ⥤ FÉt_X` is an equivalence of categories, and let `x` be
a geometric point of `X`. Then the induced continuous homomorphism
`AlgebraicGeometry.etaleFundamentalGroupMap` is an isomorphism of topological groups
`π₁(X, x) ≅ π₁(Y, f ∘ x)`.

The two connectedness hypotheses are equivalent to one another whenever `X` and `Y` are
quasi-compact and quasi-separated, by
`AlgebraicGeometry.connectedSpace_iff_of_finiteEtaleBaseChange`. Combined with
`AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection`, the recorded
identification of the underlying map says that the isomorphism intertwines the actions of the two
fundamental groups on the geometric fibre of every finite étale cover of `Y`. -/
@[stacks 0BQA "part (2)", sga "4 XII 6.5" "(ii) b')⇒b'') π₁", sga "1 V 6.10" "special case"]
def fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [ConnectedSpace X] [ConnectedSpace Y]
    (hf : (finiteEtaleBaseChange f).IsEquivalence) (x : GeometricPoint X) :
    { e : EtaleFundamentalGroup X x ≃ₜ* EtaleFundamentalGroup Y (x.map f) //
      ∀ σ : EtaleFundamentalGroup X x, e σ = etaleFundamentalGroupMap f x σ } :=
  have _ : (finiteEtaleBaseChange f).IsEquivalence := hf
  have _ : CompactSpace (EtaleFundamentalGroup X x) := compactSpace_etaleFundamentalGroup X x
  have _ : T2Space (EtaleFundamentalGroup Y (x.map f)) :=
    t2Space_etaleFundamentalGroup Y (x.map f)
  have hcont : Continuous (etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange f x :
      EtaleFundamentalGroup X x → EtaleFundamentalGroup Y (x.map f)) := by
    rw [funext (etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange_apply f x)]
    exact (etaleFundamentalGroupMap f x).continuous_toFun
  ⟨{ toMulEquiv := etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange f x
     continuous_toFun := hcont
     continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
       (f := (etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange f x).toEquiv) hcont },
    etaleFundamentalGroupMulEquivOfFiniteEtaleBaseChange_apply f x⟩

end AlgebraicGeometry

end
