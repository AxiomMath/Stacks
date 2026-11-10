module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FpqcSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableSmallEtaleBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SchemeToSpaceSites
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcEtaleRefinement
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison

/-!
# The inverse image from the small étale topos is an fpqc sheaf (Stacks 0DG7)

Let `T` be a big étale site of algebraic spaces over `S`, let `X` be an algebraic space of it
and let `F` be a sheaf on the spaces-étale site of `X`. The presheaf underlying `π_X⁻¹F` on the
slice of algebraic spaces over `X` satisfies étale descent for every étale covering family, and the
sheaf condition for the finite fpqc families of affine schemes over an affine scheme over `X`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.schemeInclusion` — the schemes of the fppf site of `T`,
  with their big étale topology, inside the algebraic spaces of `T` (Stacks 0DFV).
* `AlgebraicGeometry.BigEtaleSpaceSite.overSchemeInclusion` — its localization at a scheme `A`:
  schemes over `A` inside algebraic spaces over `h_A`.
* `AlgebraicGeometry.BigEtaleSpaceSite.schemeProjectionInverseImageIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.chartProjectionInverseImageIso` — `π_A⁻¹` for the scheme
  `A` and `π_{h_A}⁻¹` for the algebraic space it represents, compared through the chart functor.
* `AlgebraicGeometry.BigEtaleSpaceSite.restrictionToSchemesIso` — on schemes over `A`,
  `π_{h_A}⁻¹G` is `π_A⁻¹` of the restriction of `G` to the small étale site of the scheme `A`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.isEtaleSheafOver_inverseImage` — `π_X⁻¹F` satisfies
  étale descent for every étale covering family of the slice, not only for the chosen ones.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleMorphism_inverseImageIso` — restriction of
  `π_X⁻¹F` along composition with `f : Y ⟶ X` is `π_Y⁻¹ f_small⁻¹ F`: the inverse-image form of
  the commutative square of Stacks 0DF6, part (3).
* `AlgebraicGeometry.BigEtaleSpaceSite.isAffineFpqcSheafOver_inverseImage` — **Stacks 0DG7,
  Case I**: `π_X⁻¹F` satisfies the sheaf condition for the finite fpqc families of affine schemes
  over an affine scheme over `X`.
* `CategoryTheory.Presieve.isSheafFor_ofArrows_map_of_iso`,
  `CategoryTheory.Presieve.isSheafFor_ofArrows_iff_of_iso` and
  `CategoryTheory.Presieve.isInitialStructuredArrowMkOfIsIso` — the sheaf condition for a family
  transfers along any functor from a presheaf isomorphic to the restriction, and is invariant
  under isomorphisms of families; an isomorphism into the image of a fully faithful functor is an
  initial structured arrow.

## References

* [Stacks Project, Tag 0DF6](https://stacks.math.columbia.edu/tag/0DF6)
* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Presieve

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- **The sheaf condition for a family transfers along a functor.** If a presheaf `P'` on `D` is
isomorphic to the restriction of a presheaf `P` on `C` along `ι : D ⥤ C`, and `P'` satisfies the
sheaf condition for a family of `D`, then `P` satisfies it for the image family. -/
theorem isSheafFor_ofArrows_map_of_iso (ι : D ⥤ C) {P : Cᵒᵖ ⥤ Type w} {P' : Dᵒᵖ ⥤ Type w}
    (e : P' ≅ ι.op ⋙ P) {I : Type*} {Z : D} {V : I → D} (g : ∀ i, V i ⟶ Z)
    (h : IsSheafFor P' (ofArrows V g)) :
    IsSheafFor P (ofArrows (fun i ↦ ι.obj (V i)) (fun i ↦ ι.map (g i))) := by
  rw [isSheafFor_arrows_iff] at h ⊢
  intro x hx
  have hinv : ∀ {W W' : D} (k : W ⟶ W') (y : P.obj (op (ι.obj W'))),
      P'.map k.op (e.inv.app (op W') y) = e.inv.app (op W) (P.map (ι.map k).op y) :=
    fun k y ↦ (NatTrans.naturality_apply e.inv k.op y).symm
  have hhom : ∀ {W W' : D} (k : W ⟶ W') (y : P'.obj (op W')),
      P.map (ι.map k).op (e.hom.app (op W') y) = e.hom.app (op W) (P'.map k.op y) :=
    fun k y ↦ (NatTrans.naturality_apply e.hom k.op y).symm
  have hy : Arrows.Compatible P' g (fun i ↦ e.inv.app (op (V i)) (x i)) := by
    intro i j W gi gj hij
    rw [hinv, hinv]
    exact congrArg (e.inv.app (op W)) (hx i j (ι.obj W) (ι.map gi) (ι.map gj) (by
      rw [← ι.map_comp, ← ι.map_comp, hij]))
  obtain ⟨s, hs, hu⟩ := h _ hy
  refine ⟨e.hom.app (op Z) s, fun i ↦ ?_, fun t ht ↦ ?_⟩
  · rw [hhom, hs i]
    exact congrFun (congrArg (fun φ ↦ φ.app (op (V i))) e.inv_hom_id) (x i)
  · have : e.inv.app (op Z) t = s := hu _ fun i ↦ by
      rw [hinv]
      exact congrArg (e.inv.app (op (V i))) (ht i)
    rw [← this]
    exact (congrFun (congrArg (fun φ ↦ φ.app (op Z)) e.inv_hom_id) t).symm

/-- **An isomorphism into the image of a fully faithful functor is initial among the structured
arrows over it.** For `i : D ⥤ C` fully faithful and an isomorphism `φ : i d ⟶ c`, the structured
arrow `φ.op : op c ⟶ i.op (op d)` is initial. -/
def isInitialStructuredArrowMkOfIsIso (i : D ⥤ C) [i.Full] [i.Faithful] {d : D} {c : C}
    (φ : i.obj d ⟶ c) [IsIso φ] :
    IsInitial (StructuredArrow.mk (T := i.op) (Y := op d) φ.op) := by
  let lift (k : StructuredArrow (op c) i.op) : k.right.unop ⟶ d :=
    i.preimage (k.hom.unop ≫ inv φ)
  refine IsInitial.ofUniqueHom (fun k ↦ StructuredArrow.homMk (lift k).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    change i.map (lift k) ≫ φ = k.hom.unop
    simp [lift]
  · intro k m
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply i.map_injective
    have hm := congrArg Quiver.Hom.unop (StructuredArrow.w m)
    change i.map m.right.unop ≫ φ = k.hom.unop at hm
    change i.map m.right.unop = i.map (lift k)
    simp [lift, ← hm]

/-- The sheaf condition for a family is unchanged on replacing its members and its target by
isomorphic ones, compatibly with the maps. -/
theorem isSheafFor_ofArrows_iff_of_iso {P : Cᵒᵖ ⥤ Type w} {I : Type*} {Z Z' : C}
    {V V' : I → C} (g : ∀ i, V i ⟶ Z) (g' : ∀ i, V' i ⟶ Z') (e : ∀ i, V i ≅ V' i)
    (β : Z ≅ Z') (he : ∀ i, (e i).hom ≫ g' i = g i ≫ β.hom) :
    IsSheafFor P (ofArrows V g) ↔ IsSheafFor P (ofArrows V' g') := by
  have h : Sieve.generate (ofArrows V' g') = (Sieve.generate (ofArrows V g)).pullback β.inv := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff]
      rintro W k ⟨i⟩
      refine ⟨_, (e i).inv, g i, ⟨i⟩, ?_⟩
      rw [← cancel_epi (e i).hom, Iso.hom_inv_id_assoc, ← Category.assoc, he i, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · rintro W k ⟨W', m, _, ⟨i⟩, hm⟩
      refine ⟨_, m ≫ (e i).hom, g' i, ⟨i⟩, ?_⟩
      rw [Category.assoc, he i, ← Category.assoc, hm, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
  rw [isSheafFor_iff_generate, isSheafFor_iff_generate (ofArrows V' g'), h,
    isSheafFor_pullback_iff]

end CategoryTheory.Presieve

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-! ### Étale descent -/

/-- **`π_X⁻¹F` satisfies étale descent for every étale covering family of the slice.** -/
theorem isEtaleSheafOver_inverseImage (X : T.Spaces)
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :
    Space.IsEtaleSheafOnSlice T.fppfSite S T.fppf_mem X
      ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj := by
  intro U E hE
  obtain ⟨⟨V, G⟩, hG, hbase, hcomb⟩ :=
    T.covering_representative ⟨U.left, E.map (Over.forget X)⟩ hE
  change U.left = V at hbase
  subst hbase
  have hpres : (E.map (Over.forget X)).presieve₀ = G.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb
  have hmem : Sieve.generate E.presieve₀ ∈ T.bigEtaleTopology X U := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv U (Sieve.ofArrows E.X E.f) ∈ _
    rw [Sieve.overEquiv_ofArrows]
    change Sieve.generate (E.map (Over.forget X)).presieve₀ ∈ _
    rw [hpres]
    exact Precoverage.generate_mem_toGrothendieck ((T.mem_precoverage_iff).2 ⟨G, rfl, hG⟩)
  rw [Presieve.isSheafFor_iff_generate]
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((bigToSmallEtaleMorphism T X).inverseImage.obj F).property) _ hmem

/-! ### Schemes inside the big étale site of algebraic spaces -/

/-- The big étale site of algebraic spaces `T` with its chosen big étale site of schemes replaced
by the étale site carried by its own big fppf site of schemes. The algebraic spaces, their
covering families and hence the topology are those of `T`; only the scheme site changes, and its
cutoff is now that of the fppf site. -/
def withAssociatedSchemeSite : BigEtaleSpaceSite S where
  schemeSite := associatedBigEtaleSite T.fppfSite
  scheme_mem := T.fppf_mem
  fppfSite := T.fppfSite
  fppf_mem := T.fppf_mem
  initialCoverings := T.initialCoverings
  initialCoverings_small := T.initialCoverings_small
  initialCoverings_etale := T.initialCoverings_etale
  coveringBound := T.coveringBound
  coveringOrdinal := T.coveringOrdinal
  coveringOrdinal_isSuccLimit := T.coveringOrdinal_isSuccLimit
  initialCoverings_bounded := T.initialCoverings_bounded
  coverings_isSite := T.coverings_isSite
  covering_representative := T.covering_representative

/-- The inclusion of the big étale category of schemes over `S` carried by the big fppf site of
`T` into the algebraic spaces of `T`: a scheme goes to the algebraic space it represents. -/
abbrev schemeInclusion :
    BigEtaleOver (associatedBigEtaleSite T.fppfSite) S T.fppf_mem ⥤ T.Spaces :=
  etaleSchemeToSpace T.withAssociatedSchemeSite rfl

/-- The inclusion of the schemes of the fppf site of `T` into the algebraic spaces of `T` is
cocontinuous and a dense subsite for the big étale topologies (Stacks 0DFV, étale case). -/
theorem schemeInclusion_isSpecialCocontinuous :
    IsSpecialCocontinuous (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem)
      T.topology (schemeInclusion T) :=
  etaleSchemeToSpace_isSpecialCocontinuous T.withAssociatedSchemeSite rfl

/-- The inclusion of schemes into algebraic spaces is cocontinuous for the big étale
topologies. -/
instance schemeInclusion_isCocontinuous :
    (schemeInclusion T).IsCocontinuous
      (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem) T.topology :=
  (schemeInclusion_isSpecialCocontinuous T).1

/-- The inclusion of schemes into algebraic spaces is a dense subsite for the big étale
topologies. -/
instance schemeInclusion_isDenseSubsite :
    (schemeInclusion T).IsDenseSubsite
      (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem) T.topology :=
  (schemeInclusion_isSpecialCocontinuous T).2

/-- The inclusion of schemes into algebraic spaces is faithful. -/
instance schemeInclusion_faithful : (schemeInclusion T).Faithful where
  map_injective {X Y} f g h := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    have h' := congrArg (fun q ↦ q.hom) h
    exact congrArg (fun k ↦ k.left.hom) (yoneda.map_injective h')

/-- The inclusion of schemes into algebraic spaces is full. -/
instance schemeInclusion_full : (schemeInclusion T).Full where
  map_surjective {X Y} f := by
    let g := yoneda.preimage f.hom
    refine ⟨Over.homMk (ObjectProperty.homMk g.left.hom) ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      exact congrArg (fun k ↦ k.hom) (Over.w g)
    · apply ObjectProperty.hom_ext
      exact (congrArg yoneda.map (by ext; rfl : _ = g)).trans (yoneda.map_preimage f.hom)

/-! ### The schemes over a scheme of the site -/

section OverScheme

variable (A : BigEtaleOver (associatedBigEtaleSite T.fppfSite) S T.fppf_mem)

/-- The big étale category of schemes over a scheme `A` of the site, mapped into the algebraic
spaces over the algebraic space `A` represents. -/
abbrev overSchemeInclusion :
    BigEtaleOver (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property ⥤
      Over ((schemeInclusion T).obj A) :=
  (Over.iteratedSliceEquiv A).inverse ⋙ Over.post (schemeInclusion T)

/-- The inclusion of schemes over `A` into algebraic spaces over `h_A` is continuous for the big
étale topologies. -/
instance overSchemeInclusion_isContinuous :
    (overSchemeInclusion T A).IsContinuous
      (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (T.bigEtaleTopology ((schemeInclusion T).obj A)) := by
  have h₁ : (Over.iteratedSliceEquiv A).inverse.IsContinuous
      (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      ((BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem).over A) := by
    rw [bigEtaleOver_topology_eq, bigEtaleOver_topology_eq]
    exact inferInstanceAs ((Over.iteratedSliceEquiv A).inverse.IsContinuous
      ((associatedBigEtaleSite T.fppfSite).topology.over A.left)
      (((associatedBigEtaleSite T.fppfSite).topology.over _).over A))
  have h₂ := Functor.isContinuous_overPost
    (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem) T.topology
    (schemeInclusion T) A
  exact Functor.isContinuous_comp _ _ _
    ((BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem).over A) _

/-- The inclusion of schemes over `A` into algebraic spaces over `h_A` is cocontinuous for the
big étale topologies. -/
instance overSchemeInclusion_isCocontinuous :
    (overSchemeInclusion T A).IsCocontinuous
      (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (T.bigEtaleTopology ((schemeInclusion T).obj A)) := by
  have h₁ : (Over.iteratedSliceEquiv A).inverse.IsCocontinuous
      (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      ((BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem).over A) := by
    rw [bigEtaleOver_topology_eq, bigEtaleOver_topology_eq]
    exact inferInstanceAs ((Over.iteratedSliceEquiv A).inverse.IsCocontinuous
      ((associatedBigEtaleSite T.fppfSite).topology.over A.left)
      (((associatedBigEtaleSite T.fppfSite).topology.over _).over A))
  exact CategoryTheory.isCocontinuous_comp _ _
    (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
    ((BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) S T.fppf_mem).over A)
    (L := T.bigEtaleTopology ((schemeInclusion T).obj A))

/-- The chart functor of the represented algebraic space, followed by the inclusion of its
spaces-étale site into its big étale site. -/
abbrev chartToBig :
    Space.representedSchemeSmallEtale T.fppfSite S T.fppf_mem A ⥤
      Over ((schemeInclusion T).obj A) :=
  Space.representedChartFunctor T.fppfSite S T.fppf_mem A ⋙
    Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem
      (Space.yonedaSpace T.fppfSite S T.fppf_mem A)

/-- The chart functor of `h_A`, followed by the inclusion into the big étale site of `h_A`, is
continuous. -/
instance chartToBig_isContinuous :
    (chartToBig T A).IsContinuous
      (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (T.bigEtaleTopology ((schemeInclusion T).obj A)) :=
  haveI := spacesEtaleInclusion_isContinuous T (Space.yonedaSpace T.fppfSite S T.fppf_mem A)
  Functor.isContinuous_comp _ _ (Space.representedSchemeTopology T.fppfSite S T.fppf_mem A)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
      (Space.yonedaSpace T.fppfSite S T.fppf_mem A))
    (T.bigEtaleTopology (Space.yonedaSpace T.fppfSite S T.fppf_mem A))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the sheaf adjunction over the big étale site is slow
/-- The direct image along the chart functor `chartToBig T A` has a left adjoint, the sheaf
pullback built from the left Kan extension. -/
instance chartToBig_sheafPushforwardContinuous_isRightAdjoint :
    ((chartToBig T A).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (T.bigEtaleTopology ((schemeInclusion T).obj A))).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (chartToBig T A) (Type (u + 1))
    (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
    (T.bigEtaleTopology ((schemeInclusion T).obj A))).isRightAdjoint

/-- The chart functor of the represented algebraic space is the restriction of the inclusion of
schemes over `A` to the étale ones. -/
def chartToBigIso :
    SmallEtale.inclusion (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property ⋙
        overSchemeInclusion T A ≅ chartToBig T A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of large-universe presheaves on the big étale site is slow
/-- Right Kan extensions along the inclusion of schemes over `A` into spaces over `h_A` exist
pointwise. -/
instance overSchemeInclusion_hasLimit_bigToSmallEtaleFpqcSheaf
    (F : (BigEtaleOver (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)ᵒᵖ ⥤
      Type (u + 1))
    (Y : (Over ((schemeInclusion T).obj A))ᵒᵖ) :
    HasLimit (StructuredArrow.proj Y (overSchemeInclusion T A).op ⋙ F) :=
  inferInstance

/-- **The inverse image `π_A⁻¹` of the scheme `A`, through the spaces over `A`.** The inverse
image from the small étale topos of the scheme `A` to its big étale topos is the sheaf pullback
along the chart functor, into the big étale site of the algebraic space `A` represents, followed
by restriction to the schemes over `A`. -/
def schemeProjectionInverseImageIso :
    (bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite T.fppfSite) A.left.obj
        A.left.property).inverseImage ≅
      (chartToBig T A).sheafPullback (Type (u + 1))
          (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
          (T.bigEtaleTopology ((schemeInclusion T).obj A)) ⋙
        (overSchemeInclusion T A).sheafPushforwardContinuous (Type (u + 1))
          (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
          (T.bigEtaleTopology ((schemeInclusion T).obj A)) :=
  haveI := chartToBig_isContinuous T A
  Adjunction.leftAdjointUniq
      (bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite T.fppfSite) A.left.obj
        A.left.property).adj
      ((SmallEtale.inclusion (associatedBigEtaleSite T.fppfSite) A.left.obj
        A.left.property).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
        (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)) ≪≫
    CategoryTheory.sheafPullbackIsoOfInitial
      (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (T.bigEtaleTopology ((schemeInclusion T).obj A))
      (SmallEtale.inclusion (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (overSchemeInclusion T A) (chartToBig T A) (chartToBigIso T A).hom
      ((chartToBig T A).sheafPullback (Type (u + 1))
          (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
          (T.bigEtaleTopology ((schemeInclusion T).obj A)))
      ((chartToBig T A).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
          (T.bigEtaleTopology ((schemeInclusion T).obj A)))
      (fun U ↦ Presieve.isInitialStructuredArrowMkOfIsIso (overSchemeInclusion T A)
        ((chartToBigIso T A).hom.app U))

/-- **The inverse image `π_A⁻¹` of the algebraic space represented by `A`, through the charts.**
Restricting a sheaf on the spaces-étale site of `h_A` to the small étale site of the scheme `A`
and then pulling back along the chart functor into the big étale site of `h_A` is
`π_{h_A}⁻¹`. -/
def chartProjectionInverseImageIso :
    (Space.representedSpacesEtaleSheafEquiv T.fppfSite S T.fppf_mem A).functor ⋙
        (chartToBig T A).sheafPullback (Type (u + 1))
          (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
          (T.bigEtaleTopology ((schemeInclusion T).obj A)) ≅
      (bigToSmallEtaleMorphism T ((schemeInclusion T).obj A)).inverseImage :=
  haveI := chartToBig_isContinuous T A
  haveI : (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem
      (Space.yonedaSpace T.fppfSite S T.fppf_mem A)).IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
        (Space.yonedaSpace T.fppfSite S T.fppf_mem A))
      (T.bigEtaleTopology ((schemeInclusion T).obj A)) :=
    spacesEtaleInclusion_isContinuous T (Space.yonedaSpace T.fppfSite S T.fppf_mem A)
  let e := Space.representedSpacesEtaleSheafEquiv T.fppfSite S T.fppf_mem A
  let c := Space.representedChartFunctor T.fppfSite S T.fppf_mem A
  let w := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem
    (Space.yonedaSpace T.fppfSite S T.fppf_mem A)
  let Jc := Space.representedSchemeTopology T.fppfSite S T.fppf_mem A
  let Jw := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
    (Space.yonedaSpace T.fppfSite S T.fppf_mem A)
  let K := T.bigEtaleTopology ((schemeInclusion T).obj A)
  haveI : w.IsContinuous Jw K :=
    spacesEtaleInclusion_isContinuous T (Space.yonedaSpace T.fppfSite S T.fppf_mem A)
  let ρ : (chartToBig T A).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
        (T.bigEtaleTopology ((schemeInclusion T).obj A)) ⋙ e.inverse ≅
      w.sheafPushforwardContinuous (Type (u + 1)) Jw K :=
    Functor.isoWhiskerRight
        (Functor.sheafPushforwardContinuousComp c w (Type (u + 1)) Jc Jw K).symm e.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (w.sheafPushforwardContinuous (Type (u + 1)) Jw K)
        (Functor.isoWhiskerRight
          (Space.representedSpacesEtaleSheafEquiv_functor_iso T.fppfSite S T.fppf_mem A).symm
            e.inverse ≪≫ e.unitIso.symm) ≪≫
      Functor.rightUnitor _
  Adjunction.leftAdjointUniq
    ((e.toAdjunction.comp ((chartToBig T A).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
      (T.bigEtaleTopology ((schemeInclusion T).obj A)))).ofNatIsoRight ρ)
    (bigToSmallEtaleMorphism T ((schemeInclusion T).obj A)).adj

end OverScheme

/-! ### The fpqc sheaf condition over an affine scheme -/

section Affine

variable (A : BigEtaleOver (associatedBigEtaleSite T.fppfSite) S T.fppf_mem)
  (G : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
    (Space.yonedaSpace T.fppfSite S T.fppf_mem A)) (Type (u + 1)))

/-- **On schemes over `A`, `π_{h_A}⁻¹G` is `π_A⁻¹` of a sheaf on the small étale site of the
scheme `A`**, namely of the restriction of `G` to the étale schemes over `A`. -/
def restrictionToSchemesIso :
    (overSchemeInclusion T A).op ⋙
        ((bigToSmallEtaleMorphism T ((schemeInclusion T).obj A)).inverseImage.obj G).obj ≅
      ((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite T.fppfSite) A.left.obj
        A.left.property).inverseImage.obj
          ((Space.representedSpacesEtaleSheafEquiv T.fppfSite S T.fppf_mem A).functor.obj G)).obj :=
  (sheafToPresheaf _ _).mapIso
    (((overSchemeInclusion T A).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property)
        (T.bigEtaleTopology ((schemeInclusion T).obj A))).mapIso
      ((chartProjectionInverseImageIso T A).app G).symm ≪≫
    ((schemeProjectionInverseImageIso T A).app
      ((Space.representedSpacesEtaleSheafEquiv T.fppfSite S T.fppf_mem A).functor.obj G)).symm)

/-- The object of the big étale site of the scheme `A` given by a morphism `g : W ⟶ A`. -/
abbrev schemeOverObj {W : BigEtaleOver (associatedBigEtaleSite T.fppfSite) S T.fppf_mem}
    (g : W ⟶ A) : BigEtaleOver (associatedBigEtaleSite T.fppfSite) A.left.obj A.left.property :=
  (Over.iteratedSliceEquiv A).functor.obj (Over.mk g)

/-- The image of `AlgebraicGeometry.BigEtaleSpaceSite.schemeOverObj` among algebraic spaces over
`h_A` is the morphism of represented algebraic spaces. -/
def overSchemeInclusion_schemeOverIso {W : BigEtaleOver (associatedBigEtaleSite T.fppfSite) S
    T.fppf_mem} (g : W ⟶ A) :
    (overSchemeInclusion T A).obj (schemeOverObj T A g) ≅ Over.mk ((schemeInclusion T).map g) :=
  (Over.post (schemeInclusion T)).mapIso ((Over.iteratedSliceEquiv A).unitIso.app (Over.mk g)).symm

/-- `AlgebraicGeometry.BigEtaleSpaceSite.overSchemeInclusion_schemeOverIso` is natural. -/
theorem overSchemeInclusion_schemeOverIso_naturality
    {W W' : BigEtaleOver (associatedBigEtaleSite T.fppfSite) S T.fppf_mem}
    (g : W ⟶ A) (g' : W' ⟶ A) (k : Over.mk g ⟶ Over.mk g') :
    (overSchemeInclusion T A).map ((Over.iteratedSliceEquiv A).functor.map k) ≫
        (overSchemeInclusion_schemeOverIso T A g').hom =
      (overSchemeInclusion_schemeOverIso T A g).hom ≫ (Over.post (schemeInclusion T)).map k := by
  have h := (Over.iteratedSliceEquiv A).unitIso.inv.naturality k
  simp only [Functor.comp_map, Functor.id_map] at h
  have h' := congrArg (Over.post (schemeInclusion T)).map h
  simp only [Functor.map_comp] at h'
  exact h'

end Affine

/-! ### Restriction along composition with a morphism -/

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- **Restricting `π_X⁻¹` along composition with `f` is `π_Y⁻¹ ∘ f_small⁻¹`** (Stacks 0DF6,
part (3)). The inverse image of the big étale morphism along `f` is restriction along
`Over.map f`. -/
def bigEtaleMorphism_inverseImageIso :
    (bigToSmallEtaleMorphism T X).inverseImage ⋙ (bigEtaleMorphism T f).inverseImage ≅
      (smallEtaleMorphism T f).inverseImage ⋙ (bigToSmallEtaleMorphism T Y).inverseImage :=
  Adjunction.leftAdjointUniq ((bigToSmallEtaleMorphism T X).comp (bigEtaleMorphism T f)).adj
    (((smallEtaleMorphism T f).comp (bigToSmallEtaleMorphism T Y)).adj.ofNatIsoRight
      (bigSmallEtale_pushforwardCommIso T f))

/-! ### Stacks 0DG7, Case I: finite affine fpqc families -/

/-- **Stacks 0DG7, Case I.** `π_X⁻¹F` satisfies the sheaf condition for every finite fpqc family
of affine schemes over an affine scheme `A` over `X`. -/
theorem isAffineFpqcSheafOver_inverseImage (X : T.Spaces)
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :
    Space.IsAffineFpqcSheafOver T.fppfSite S T.fppf_mem X
      ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj := by
  intro Ta a R hfin hR
  let A : BigEtaleOver (associatedBigEtaleSite T.fppfSite) S T.fppf_mem :=
    (BigAffineFppf.inclusion T.fppfSite S T.fppf_mem).obj Ta
  let a' : (schemeInclusion T).obj A ⟶ X := a
  let G := (smallEtaleMorphism T a').inverseImage.obj F
  let H := (Space.representedSpacesEtaleSheafEquiv T.fppfSite S T.fppf_mem A).functor.obj G
  let g : ∀ j, (BigAffineFppf.inclusion T.fppfSite S T.fppf_mem).obj (R.X j) ⟶ A :=
    fun j ↦ (BigAffineFppf.inclusion T.fppfSite S T.fppf_mem).map (R.f j)
  have h09XN := (isSheaf_iff_isSheaf_of_type _ _).mp
    (bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc (associatedBigEtaleSite T.fppfSite)
      A.left.obj A.left.property H)
  have hmem : Presieve.ofArrows (fun j ↦ schemeOverObj T A (g j))
      (fun j ↦ (Over.iteratedSliceEquiv A).functor.map
        (Over.homMk (g j) : Over.mk (g j) ⟶ Over.mk (𝟙 A))) ∈
      (Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme (associatedBigEtaleSite T.fppfSite)
        A.left.obj A.left.property)) (schemeOverObj T A (𝟙 A)) := by
    rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hR
    rwa [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  have hsch := (Presieve.isSheafFor_iff_generate _).2
    (h09XN _ (Precoverage.generate_mem_toGrothendieck hmem))
  let ι := overSchemeInclusion T A ⋙ Over.map a'
  let e : ((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite T.fppfSite) A.left.obj
      A.left.property).inverseImage.obj H).obj ≅
      ι.op ⋙ ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj :=
    (restrictionToSchemesIso T A G).symm ≪≫
      Functor.isoWhiskerLeft (overSchemeInclusion T A).op
        ((sheafToPresheaf _ _).mapIso ((bigEtaleMorphism_inverseImageIso T a').app F).symm)
  have htr := Presieve.isSheafFor_ofArrows_map_of_iso ι e _ hsch
  let β₀ : Over.mk ((schemeInclusion T).map (𝟙 A) ≫ a') ≅ Over.mk a' :=
    Over.isoMk (Iso.refl _) (by simp)
  refine (Presieve.isSheafFor_ofArrows_iff_of_iso _ _
    (fun j ↦ (Over.map a').mapIso (overSchemeInclusion_schemeOverIso T A (g j)))
    ((Over.map a').mapIso (overSchemeInclusion_schemeOverIso T A (𝟙 A)) ≪≫ β₀)
    (fun j ↦ ?_)).mp htr
  have hn := congrArg (fun k ↦ k.left) (overSchemeInclusion_schemeOverIso_naturality T A (g j)
    (𝟙 A) (Over.homMk (g j)))
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.post_map, Over.homMk_left] at hn
  simp only [Over.comp_left, Functor.mapIso_hom, Iso.trans_hom, Over.map_map_left, β₀,
    Over.isoMk_hom_left, Iso.refl_hom, Functor.comp_map, ι]
  exact hn.symm

end AlgebraicGeometry.BigEtaleSpaceSite

end
