module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Pieces
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GlueingAux1
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GlueingAux2
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GlueingAux3
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GlueingAux4
public import StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing the affine pieces: essential surjectivity in Stacks Tag 01ZM part (1)

Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact, quasi-separated schemes with affine
transition morphisms.  This file proves that every scheme of finite presentation over `S` is the
base change of a scheme of finite presentation over one of the stages `Sᵢ`.  This is Stacks Tag
01ZM part (1), equivalently the essential-surjectivity half of Stacks Tag 0EY1, and it completes
the descent of the affine pieces carried out in
`StacksDraft.AlgebraicGeometry.F3b.LimitDescent.Pieces` by glueing them.

## Main definitions

* `AlgebraicGeometry.LimitDescent.HasModel`: a morphism to the limit is the base change along a
  cone leg of a morphism of finite presentation over a stage.

## Main results

* `AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation`: Tag 01ZM part (1) for
  an index category at the universe of the schemes.
* `AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall`,
  `AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation_of_initiallySmall`: the
  same with the index universes independent of the scheme universe, under
  `CategoryTheory.EssentiallySmall.{u}` resp.
  `CategoryTheory.LocallySmall.{u}` and `CategoryTheory.InitiallySmall.{u}` on the index.
* `AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall`: Tag
  01ZM part (1) in the `CategoryTheory.Over.pullback` idiom, which is where that tag sits.
* `AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation`: the
  essential-surjectivity half of Stacks Tag 0EY1 over quasi-compact, quasi-separated stages, for
  a directed inverse system and in the `CategoryTheory.Over.pullback` idiom; the form over
  arbitrary stages, which is the source's, is
  `AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation`.
* `AlgebraicGeometry.LimitDescent.hasFinitePresentationModels`: the predicate
  `AlgebraicGeometry.LimitDescent.HasFinitePresentationModels`, carried as a hypothesis by the
  Tag 0CNT results of `StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystem`, holds.
* `AlgebraicGeometry.exists_isPullback_transport`,
  `AlgebraicGeometry.exists_isPullback_transport_open`: a model, and a quasi-compact open of it
  cutting out a given open of the source, transport to any later stage.

## Implementation notes

The source glues the whole affine cover at once against a glueing datum indexed by pairs.  Here
the cover is glued **two pieces at a time**, which is cheaper: the glued scheme is a plain
`CategoryTheory.Limits.pushout` of two open immersions, so no `AlgebraicGeometry.Scheme.GlueData`,
no `t'` and no cocycle condition appear, and the base change of the glueing is identified with the
source by `AlgebraicGeometry.Scheme.isPullback_of_openCover`, which needs no statement that base
change preserves the glueing colimit.

The induction runs over `Finset`s of the index of the affine cover produced by
`AlgebraicGeometry.LimitDescent.exists_stage_isAffineModels`, over the statement that the union of
the selected members is quasi-compact and has a model over a stage.  In the step the union of the
members selected so far is glued to one further member; their intersection is a quasi-compact
open, so it descends by `AlgebraicGeometry.LimitDescent.exists_isOpen_model_of_initiallySmall`,
and the number of pieces to glue
does not grow.  An induction over *affine* covers would not close, intersections of affine opens
not being affine.

The two descents of that intersection are identified at a later stage by
`AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`, which is Tag 01ZM parts (2) and (3) --
in the form of Tag 081E -- applied to the comparison morphism.  Its conclusion includes the
compatibility of the isomorphism with the two presentations of the intersection, and that
compatibility, not merely the existence of an isomorphism over the stage, is what the glueing
consumes.

Quasi-separatedness of the glued model is `AlgebraicGeometry.quasiSeparatedSpace_of_sup`: the two
pieces are quasi-separated and their intersection, being the image of the open along which they
are glued, is quasi-compact.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

universe w v uI u

open CategoryTheory CategoryTheory.Limits CategoryTheory.InitiallySmall TopologicalSpace

namespace AlgebraicGeometry

/-! ### Finite presentation and base change -/

/-- Finite presentation is stable under base change.

`FinitePresentation` is this development's bundling of `LocallyOfFinitePresentation`,
`QuasiCompact` and `QuasiSeparated`, and Mathlib has no such bundled predicate. Its three
components are stable under base change in Mathlib, by
`AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange` and the
`MorphismProperty.IsStableUnderBaseChange` instances for `QuasiCompact` and `QuasiSeparated`,
and that is all the proof below uses; no Stacks attribute is attached for that reason. -/
@[ega "IV 1.4.3" "(iii), special case", ega "IV 1.6.2", sga "1 VIII 3.6"]
public lemma FinitePresentation.of_isPullback {X S Y T : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ T}
    {a : X ⟶ Y} {b : S ⟶ T} (h : IsPullback a f g b) (hg : FinitePresentation g) :
    FinitePresentation f :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback h hg.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h hg.2.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h hg.2.2⟩

/-- A morphism with quasi-compact quasi-separated source into a quasi-separated target which is
locally of finite presentation is of finite presentation. -/
public lemma finitePresentation_of_compactSpace {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] (hf : LocallyOfFinitePresentation f) :
    FinitePresentation f :=
  ⟨hf, inferInstance, inferInstance⟩

/-- A model of `f : X ⟶ S` over a stage transports to any later stage, as the base change of the
model along the transition morphism.

The index universes are independent of the scheme universe: the proof is a universal property of
pullbacks and uses nothing about the index beyond its being a category. -/
public lemma exists_isPullback_transport {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) {i m : I} (a : m ⟶ i) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    {X : Scheme.{u}} (f : X ⟶ c.pt) (g : X ⟶ Y) (hpb : IsPullback g f p (c.π.app i)) :
    ∃ g' : X ⟶ pullback (D.map a) p,
      IsPullback g' f (pullback.fst (D.map a) p) (c.π.app m) ∧
        g' ≫ pullback.snd (D.map a) p = g := by
  have ht : IsPullback (pullback.snd (D.map a) p) (pullback.fst (D.map a) p) p (D.map a) :=
    (IsPullback.of_hasPullback (D.map a) p).flip
  have hs : IsPullback g f p (c.π.app m ≫ D.map a) := by rwa [c.w a]
  exact ⟨_, hs.of_right' ht, ht.lift_fst _ _ _⟩

/-- A model together with a quasi-compact open of it cutting out a given open of the source
transports to any later stage.

The index universes are independent of the scheme universe, as for
`AlgebraicGeometry.exists_isPullback_transport`: beyond its being a category with affine
transition morphisms, nothing about the index is used. -/
public lemma exists_isPullback_transport_open {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] {i m : I} (a : m ⟶ i)
    {Y : Scheme.{u}} (p : Y ⟶ D.obj i) {X : Scheme.{u}} (f : X ⟶ c.pt) (g : X ⟶ Y)
    (hpb : IsPullback g f p (c.π.app i)) (V : Y.Opens) (hV : IsCompact V.1) (U : X.Opens)
    (hU : g ⁻¹ᵁ V = U) :
    ∃ (g' : X ⟶ pullback (D.map a) p) (V' : (pullback (D.map a) p).Opens)
      (ρ : V'.toScheme ⟶ V.toScheme),
      IsPullback g' f (pullback.fst (D.map a) p) (c.π.app m) ∧ IsCompact V'.1 ∧
        g' ⁻¹ᵁ V' = U ∧ g' ≫ pullback.snd (D.map a) p = g ∧
          V'.ι ≫ pullback.snd (D.map a) p = ρ ≫ V.ι ∧
          IsPullback ρ (V'.ι ≫ pullback.fst (D.map a) p) (V.ι ≫ p) (D.map a) := by
  obtain ⟨g', hg'pb, hg's⟩ := exists_isPullback_transport D c a p f g hpb
  have hqc : QuasiCompact (pullback.snd (D.map a) p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (D.map a) p) inferInstance
  refine ⟨g', pullback.snd (D.map a) p ⁻¹ᵁ V, pullback.snd (D.map a) p ∣_ V, hg'pb,
    hqc.isCompact_preimage _ V.isOpen hV, ?_, hg's, (isPullback_morphismRestrict _ V).w.symm, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, hg's, hU]
  · exact (isPullback_morphismRestrict (pullback.snd (D.map a) p) V).paste_vert
      (IsPullback.of_hasPullback (D.map a) p).flip

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-! ### Having a model over a stage -/

namespace LimitDescent

/-- `f : X ⟶ S` **has a model over a stage** if it is the base change along one of the cone legs
of a morphism of finite presentation over that stage. -/
public def HasModel {X : Scheme.{u}} (f : X ⟶ c.pt) : Prop :=
  ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (g : X ⟶ Y),
    FinitePresentation p ∧ IsPullback g f p (c.π.app i)

/-- Having a model over a stage only depends on the isomorphism class of `f` in the category of
schemes over the limit. -/
public lemma HasModel.of_iso {X X' : Scheme.{u}} {f : X ⟶ c.pt} {f' : X' ⟶ c.pt} (e : X' ≅ X)
    (he : e.hom ≫ f = f') (hm : HasModel D c f) : HasModel D c f' := by
  obtain ⟨i, Y, p, g, hp, hpb⟩ := hm
  exact ⟨i, Y, p, e.hom ≫ g, hp,
    hpb.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) (Category.comp_id _).symm
      (by rw [Iso.refl_hom, Category.comp_id]; exact he) (by simp) (by simp)⟩

end LimitDescent

/-! ### Opens of open subschemes -/

/-- An open `V` of an open subscheme `A` of `X` whose image in `X` is `W` presents `W`. -/
public noncomputable def isoOfImageEq {X : Scheme.{u}} {A : X.Opens} (V : A.toScheme.Opens)
    (W : X.Opens) (h : A.ι ''ᵁ V = W) : W.toScheme ≅ V.toScheme :=
  IsOpenImmersion.isoOfRangeEq W.ι (V.ι ≫ A.ι) (by subst h; simp [Set.range_comp])

/-- The isomorphism `isoOfImageEq V W h` commutes with the inclusions of `V` and `W` into `X`. -/
@[reassoc (attr := simp)]
public lemma isoOfImageEq_hom {X : Scheme.{u}} {A : X.Opens} (V : A.toScheme.Opens)
    (W : X.Opens) (h : A.ι ''ᵁ V = W) :
    (isoOfImageEq V W h).hom ≫ V.ι ≫ A.ι = W.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The copy inside `U` of an open `W` contained in `U` is quasi-compact when `W` is. -/
public lemma isCompact_preimage_ι {X : Scheme.{u}} {U W : X.Opens} (h : W ≤ U)
    (hW : IsCompact W.1) : IsCompact ((U.ι ⁻¹ᵁ W : U.toScheme.Opens) : Set U.toScheme) := by
  rw [U.ι.isOpenEmbedding.isEmbedding.isCompact_iff, Scheme.Hom.coe_preimage,
    Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_eq_left.2 h]
  exact hW

/-- The image in `X` of an open of `U` contained in the copy of `W ≤ U` is `W`. -/
public lemma image_preimage_ι {X : Scheme.{u}} {U W : X.Opens} (h : W ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.2 h]

/-- A morphism of finite presentation restricted to a quasi-compact open of its source is again of
finite presentation. -/
public lemma finitePresentation_ι_comp {Z T : Scheme.{u}} {q : Z ⟶ T}
    (hq : FinitePresentation q) [QuasiSeparatedSpace T] (V : Z.Opens) (hV : IsCompact V.1) :
    FinitePresentation (V.ι ≫ q) := by
  have : QuasiSeparated q := hq.2.2
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated q
  have : QuasiSeparatedSpace V.toScheme := QuasiSeparatedSpace.of_isOpenEmbedding
    V.ι.isOpenEmbedding
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.1 hV
  have : LocallyOfFinitePresentation q := hq.1
  exact finitePresentation_of_compactSpace _ (MorphismProperty.comp_mem _ _ _ inferInstance ‹_›)

/-! ### Glue data at a single stage -/

namespace LimitDescent

section Glue

variable [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- The preimages of `A ⊓ B` in `A` and in `B` are those of `B` and of `A`. -/
private lemma preimage_ι_inf {X : Scheme.{u}} (A B : X.Opens) :
    A.ι ⁻¹ᵁ (A ⊓ B : X.Opens) = A.ι ⁻¹ᵁ B ∧ B.ι ⁻¹ᵁ (A ⊓ B : X.Opens) = B.ι ⁻¹ᵁ A := by
  simp only [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq, inf_top_eq,
    and_self]

omit [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)] in
/-- Two quasi-compact opens with models over stages have models over a *common* stage, each
carrying a quasi-compact open which cuts out their intersection. -/
private lemma exists_common_models (hc : IsLimit c) {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (f : X ⟶ c.pt) {A B : X.Opens} (hA : IsCompact A.1) (hB : IsCompact B.1)
    (hAm : HasModel D c (A.ι ≫ f)) (hBm : HasModel D c (B.ι ≫ f)) :
    ∃ (m : I) (ZA ZB : Scheme.{u}) (qA : ZA ⟶ D.obj m) (qB : ZB ⟶ D.obj m)
      (hA' : A.toScheme ⟶ ZA) (hB' : B.toScheme ⟶ ZB) (VA : ZA.Opens) (VB : ZB.Opens),
      FinitePresentation qA ∧ FinitePresentation qB ∧
        IsPullback hA' (A.ι ≫ f) qA (c.π.app m) ∧ IsPullback hB' (B.ι ≫ f) qB (c.π.app m) ∧
        IsCompact VA.1 ∧ IsCompact VB.1 ∧
        hA' ⁻¹ᵁ VA = A.ι ⁻¹ᵁ B ∧ hB' ⁻¹ᵁ VB = B.ι ⁻¹ᵁ A := by
  have : InitiallySmall.{u} I := CategoryTheory.initiallySmall_of_essentiallySmall.{u} I
  obtain ⟨iA, YA, pA, gA, hpA, hmA⟩ := hAm
  obtain ⟨iB, YB, pB, gB, hpB, hmB⟩ := hBm
  have hABc : IsCompact ((A ⊓ B : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact hA.inter_of_isOpen hB A.isOpen B.isOpen
  obtain ⟨e1, e2⟩ := preimage_ι_inf A B
  have hpreA : IsCompact ((A.ι ⁻¹ᵁ B : A.toScheme.Opens) : Set A.toScheme) :=
    e1 ▸ isCompact_preimage_ι inf_le_left hABc
  have hpreB : IsCompact ((B.ι ⁻¹ᵁ A : B.toScheme.Opens) : Set B.toScheme) :=
    e2 ▸ isCompact_preimage_ι inf_le_right hABc
  obtain ⟨mA, aA, gA1, VA1, hmA1, -, hVA1c, hVA1e⟩ :=
    exists_isOpen_model_of_initiallySmall D c hc pA (A.ι ≫ f) gA hmA (A.ι ⁻¹ᵁ B) hpreA
  obtain ⟨mB, aB, gB1, VB1, hmB1, -, hVB1c, hVB1e⟩ :=
    exists_isOpen_model_of_initiallySmall D c hc pB (B.ι ≫ f) gB hmB (B.ι ⁻¹ᵁ A) hpreB
  have hqA1 : FinitePresentation (pullback.fst (D.map aA) pA) :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback (D.map aA) pA).flip hpA
  have hqB1 : FinitePresentation (pullback.fst (D.map aB) pB) :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback (D.map aB) pB).flip hpB
  obtain ⟨hA2, VA2, -, hmA2, hVA2c, hVA2e, -⟩ :=
    exists_isPullback_transport_open D c (IsCofiltered.minToLeft mA mB) _ (A.ι ≫ f) gA1 hmA1
      VA1 hVA1c (A.ι ⁻¹ᵁ B) hVA1e
  obtain ⟨hB2, VB2, -, hmB2, hVB2c, hVB2e, -⟩ :=
    exists_isPullback_transport_open D c (IsCofiltered.minToRight mA mB) _ (B.ι ≫ f) gB1 hmB1
      VB1 hVB1c (B.ι ⁻¹ᵁ A) hVB1e
  exact ⟨IsCofiltered.min mA mB, _, _, _, _, hA2, hB2, VA2, VB2,
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback _ _).flip hqA1,
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback _ _).flip hqB1,
    hmA2, hmB2, hVA2c, hVB2c, hVA2e, hVB2e⟩

/-- If the preimage of an open `V` under `h` is the copy of `W ≤ A`, then `W` maps to `V`
compatibly, and this square is a pullback. -/
private lemma exists_isPullback_homOfLE {X Z : Scheme.{u}} {A W : X.Opens} (hWA : W ≤ A)
    (h : A.toScheme ⟶ Z) (V : Z.Opens) (hV : h ⁻¹ᵁ V = A.ι ⁻¹ᵁ W) :
    ∃ w : W.toScheme ⟶ V.toScheme, IsPullback w (X.homOfLE hWA) V.ι h := by
  have hrng : Set.range (X.homOfLE hWA ≫ h).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    show _ ∈ (V : Set Z)
    have : (X.homOfLE hWA ≫ h) ⁻¹ᵁ V = ⊤ := by
      rw [Scheme.Hom.comp_preimage, hV, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι,
        Scheme.Opens.ι_preimage_self]
    exact this.ge (Set.mem_univ y)
  refine ⟨IsOpenImmersion.lift V.ι _ hrng, IsOpenImmersion.isPullback _ _ _ _
    (IsOpenImmersion.lift_fac _ _ hrng).symm ?_⟩
  rw [Scheme.Opens.opensRange_ι, hV, Scheme.opensRange_homOfLE]

/-- **The glue datum for two quasi-compact opens with models.**  At one stage, the two opens have
models carrying quasi-compact opens cutting out their intersection, together with an isomorphism
between those two opens over the stage which is compatible with the two presentations of the
intersection. -/
private lemma exists_glue_data (hc : IsLimit c) {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (f : X ⟶ c.pt) {A B : X.Opens} (hA : IsCompact A.1) (hB : IsCompact B.1)
    (hAm : HasModel D c (A.ι ≫ f)) (hBm : HasModel D c (B.ι ≫ f)) :
    ∃ (m : I) (ZA ZB : Scheme.{u}) (qA : ZA ⟶ D.obj m) (qB : ZB ⟶ D.obj m)
      (hA' : A.toScheme ⟶ ZA) (hB' : B.toScheme ⟶ ZB) (VA : ZA.Opens) (VB : ZB.Opens)
      (φ : VA.toScheme ≅ VB.toScheme) (wA : (A ⊓ B : X.Opens).toScheme ⟶ VA.toScheme),
      FinitePresentation qA ∧ FinitePresentation qB ∧
        IsPullback hA' (A.ι ≫ f) qA (c.π.app m) ∧ IsPullback hB' (B.ι ≫ f) qB (c.π.app m) ∧
        hA' ⁻¹ᵁ VA = A.ι ⁻¹ᵁ B ∧ hB' ⁻¹ᵁ VB = B.ι ⁻¹ᵁ A ∧ IsCompact VA.1 ∧
        φ.hom ≫ VB.ι ≫ qB = VA.ι ≫ qA ∧
        wA ≫ VA.ι = X.homOfLE inf_le_left ≫ hA' ∧
        wA ≫ φ.hom ≫ VB.ι = X.homOfLE inf_le_right ≫ hB' := by
  obtain ⟨m, ZA, ZB, qA, qB, hA', hB', VA, VB, hqA, hqB, hmA, hmB, hVAc, hVBc, hVAe, hVBe⟩ :=
    exists_common_models D c hc f hA hB hAm hBm
  obtain ⟨e1, e2⟩ := preimage_ι_inf A B
  -- the two presentations of `A ⊓ B` inside the two models
  obtain ⟨wA0, hwA0⟩ :=
    exists_isPullback_homOfLE (inf_le_left : A ⊓ B ≤ A) hA' VA (hVAe.trans e1.symm)
  obtain ⟨wB0, hwB0⟩ :=
    exists_isPullback_homOfLE (inf_le_right : A ⊓ B ≤ B) hB' VB (hVBe.trans e2.symm)
  have hmodA : IsPullback wA0 ((A ⊓ B : X.Opens).ι ≫ f) (VA.ι ≫ qA) (c.π.app m) := by
    have h := hwA0.paste_vert hmA
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have hmodB : IsPullback wB0 ((A ⊓ B : X.Opens).ι ≫ f) (VB.ι ≫ qB) (c.π.app m) := by
    have h := hwB0.paste_vert hmB
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  obtain ⟨m', e, YA'', YB'', pA'', pB'', rA, rB, gA'', gB'', φ', hrA, hrB, hgA'', hgB'',
    hφ'p, hφ'c, hgArA, hgBrB⟩ :=
    exists_iso_of_isPullback_of_isPullback D c hc m
      (finitePresentation_ι_comp hqA VA hVAc) (finitePresentation_ι_comp hqB VB hVBc)
      hmodA hmodB
  obtain ⟨hA3, VA3, ρA, hmA3, hVA3c, hVA3e, hA3s, hρAw, hρA⟩ :=
    exists_isPullback_transport_open D c e qA (A.ι ≫ f) hA' hmA VA hVAc (A.ι ⁻¹ᵁ B) hVAe
  obtain ⟨hB3, VB3, ρB, hmB3, hVB3c, hVB3e, hB3s, hρBw, hρB⟩ :=
    exists_isPullback_transport_open D c e qB (B.ι ≫ f) hB' hmB VB hVBc (B.ι ⁻¹ᵁ A) hVBe
  set θA := hrA.isoIsPullback _ _ hρA with hθA
  set θB := hrB.isoIsPullback _ _ hρB with hθB
  have hθAs : θA.hom ≫ VA3.ι ≫ pullback.fst (D.map e) qA = pA'' :=
    hrA.isoIsPullback_hom_snd _ _ hρA
  have hθBs : θB.hom ≫ VB3.ι ≫ pullback.fst (D.map e) qB = pB'' :=
    hrB.isoIsPullback_hom_snd _ _ hρB
  have hθAf : θA.hom ≫ ρA = rA := hrA.isoIsPullback_hom_fst _ _ hρA
  have hθBf : θB.hom ≫ ρB = rB := hrB.isoIsPullback_hom_fst _ _ hρB
  have keyA : (gA'' ≫ θA.hom) ≫ VA3.ι = X.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ hA3 := by
    apply pullback.hom_ext
    · have l : ((gA'' ≫ θA.hom) ≫ VA3.ι) ≫ pullback.fst (D.map e) qA = gA'' ≫ pA'' := by
        simp only [Category.assoc, hθAs]
      have r : (X.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ hA3) ≫ pullback.fst (D.map e) qA =
          X.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ (A.ι ≫ f) ≫ c.π.app m' := by
        rw [Category.assoc, hmA3.w]
      rw [l, r, hgA''.w]
      simp only [← Category.assoc, Scheme.homOfLE_ι]
    · have l : ((gA'' ≫ θA.hom) ≫ VA3.ι) ≫ pullback.snd (D.map e) qA = wA0 ≫ VA.ι := by
        simp only [Category.assoc, hρAw]
        rw [← Category.assoc θA.hom ρA VA.ι, hθAf, ← Category.assoc gA'' rA VA.ι, hgArA]
      have r : (X.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ hA3) ≫ pullback.snd (D.map e) qA =
          X.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ hA' := by
        rw [Category.assoc, hA3s]
      rw [l, r]
      exact hwA0.w
  have keyB : (gB'' ≫ θB.hom) ≫ VB3.ι = X.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ hB3 := by
    apply pullback.hom_ext
    · have l : ((gB'' ≫ θB.hom) ≫ VB3.ι) ≫ pullback.fst (D.map e) qB = gB'' ≫ pB'' := by
        simp only [Category.assoc, hθBs]
      have r : (X.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ hB3) ≫ pullback.fst (D.map e) qB =
          X.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ (B.ι ≫ f) ≫ c.π.app m' := by
        rw [Category.assoc, hmB3.w]
      rw [l, r, hgB''.w]
      simp only [← Category.assoc, Scheme.homOfLE_ι]
    · have l : ((gB'' ≫ θB.hom) ≫ VB3.ι) ≫ pullback.snd (D.map e) qB = wB0 ≫ VB.ι := by
        simp only [Category.assoc, hρBw]
        rw [← Category.assoc θB.hom ρB VB.ι, hθBf, ← Category.assoc gB'' rB VB.ι, hgBrB]
      have r : (X.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ hB3) ≫ pullback.snd (D.map e) qB =
          X.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ hB' := by
        rw [Category.assoc, hB3s]
      rw [l, r]
      exact hwB0.w
  refine ⟨m', _, _, pullback.fst (D.map e) qA, pullback.fst (D.map e) qB, hA3, hB3, VA3, VB3,
    θA.symm ≪≫ φ' ≪≫ θB, gA'' ≫ θA.hom,
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback _ _).flip hqA,
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback _ _).flip hqB,
    hmA3, hmB3, hVA3e, hVB3e, hVA3c, ?_, keyA, ?_⟩
  · rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [hθBs, hφ'p, ← hθAs, Iso.inv_hom_id_assoc]
  · rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc gA'' φ'.hom (θB.hom ≫ VB3.ι), hφ'c,
      ← Category.assoc gB'' θB.hom VB3.ι, keyB]

/-! ### The glueing step -/

omit [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i : I, CompactSpace (D.obj i)] in
/-- A morphism out of an empty scheme has a model over a stage: the empty scheme over that
stage. -/
private lemma hasModel_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (f : X ⟶ c.pt) :
    HasModel D c f := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have hXi : IsInitial X := isInitialOfIsEmpty
  have hEe : IsEmpty (⊥ : (D.obj i₀).Opens).toScheme :=
    inferInstanceAs (IsEmpty (∅ : Set (D.obj i₀)))
  have hfp : FinitePresentation ((⊥ : (D.obj i₀).Opens).ι) :=
    finitePresentation_of_compactSpace _ inferInstance
  refine ⟨i₀, (⊥ : (D.obj i₀).Opens).toScheme, (⊥ : (D.obj i₀).Opens).ι, hXi.to _, hfp, ?_⟩
  have hEi : IsInitial (⊥ : (D.obj i₀).Opens).toScheme := isInitialOfIsEmpty
  exact IsPullback.of_iso_pullback ⟨hXi.hom_ext _ _⟩
    (hXi.uniqueUpToIso (hEi.ofIso (asIso (pullback.fst _ _)).symm))
    (hXi.hom_ext _ _) (hXi.hom_ext _ _)

/-- **The glueing step of Stacks Tag 01ZM part (1).**  If `X` is covered by two quasi-compact
opens each of which has a model over a stage, then `X` itself has a model over a stage: glue the
two models along the isomorphism of Tag 081E between the two descents of the intersection. -/
private lemma hasModel_of_sup (hc : IsLimit c) {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (f : X ⟶ c.pt) {A B : X.Opens} (hAB : A ⊔ B = ⊤) (hA : IsCompact A.1) (hB : IsCompact B.1)
    (hAm : HasModel D c (A.ι ≫ f)) (hBm : HasModel D c (B.ι ≫ f)) : HasModel D c f := by
  obtain ⟨m, ZA, ZB, qA, qB, hA', hB', VA, VB, φ, wA, hqA, hqB, hmA, hmB, hVAe, hVBe, hVAc,
    hφq, hwA, hwB⟩ := exists_glue_data D c hc f hA hB hAm hBm
  have hd : VA.ι ≫ qA = (φ.hom ≫ VB.ι) ≫ qB := by rw [Category.assoc]; exact hφq.symm
  have hjAq : pushout.inl VA.ι (φ.hom ≫ VB.ι) ≫ pushout.desc qA qB hd = qA :=
    pushout.inl_desc _ _ _
  have hjBq : pushout.inr VA.ι (φ.hom ≫ VB.ι) ≫ pushout.desc qA qB hd = qB :=
    pushout.inr_desc _ _ _
  have hpo : VA.ι ≫ pushout.inl VA.ι (φ.hom ≫ VB.ι) =
      φ.hom ≫ VB.ι ≫ pushout.inr VA.ι (φ.hom ≫ VB.ι) := by
    rw [← Category.assoc]; exact pushout.condition
  have hcov := opensRange_pushout_inl_sup_inr VA.ι (φ.hom ≫ VB.ι)
  have hint := opensRange_pushout_inl_inf_inr VA.ι (φ.hom ≫ VB.ι)
  obtain ⟨g, hg, -, -⟩ := isPullback_of_glueData (c.π.app m) f hAB hmA hmB hVAe hVBe φ
    (pushout.desc qA qB hd) _ _ hjAq hjBq hpo hcov hint wA hwA hwB
  refine ⟨m, _, pushout.desc qA qB hd, g, ?_, hg⟩
  have iqsA : QuasiSeparated qA := hqA.2.2
  have iqcA : QuasiCompact qA := hqA.2.1
  have iqsB : QuasiSeparated qB := hqB.2.2
  have iqcB : QuasiCompact qB := hqB.2.1
  have : QuasiSeparatedSpace ZA := quasiSeparatedSpace_of_quasiSeparated qA
  have : CompactSpace ZA := QuasiCompact.compactSpace_of_compactSpace qA
  have : QuasiSeparatedSpace ZB := quasiSeparatedSpace_of_quasiSeparated qB
  have : CompactSpace ZB := QuasiCompact.compactSpace_of_compactSpace qB
  have : CompactSpace VA.toScheme := isCompact_iff_compactSpace.1 hVAc
  have hzls : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have hCS : CompactSpace ↥(pushout VA.ι (φ.hom ≫ VB.ι)) := by
    rw [← isCompact_univ_iff, ← TopologicalSpace.Opens.coe_top, ← hcov,
      TopologicalSpace.Opens.coe_sup]
    exact (isCompact_range (pushout.inl VA.ι (φ.hom ≫ VB.ι)).continuous).union
      (isCompact_range (pushout.inr VA.ι (φ.hom ≫ VB.ι)).continuous)
  have hQS : QuasiSeparatedSpace ↥(pushout VA.ι (φ.hom ≫ VB.ι)) := by
    refine quasiSeparatedSpace_of_sup hcov ?_ ?_ ?_
    · have h := ((pushout.inl VA.ι (φ.hom ≫ VB.ι)).isOpenEmbedding.isQuasiSeparated_iff
        (s := Set.univ)).mp isQuasiSeparated_univ
      rwa [Set.image_univ] at h
    · have h := ((pushout.inr VA.ι (φ.hom ≫ VB.ι)).isOpenEmbedding.isQuasiSeparated_iff
        (s := Set.univ)).mp isQuasiSeparated_univ
      rwa [Set.image_univ] at h
    · rw [hint]
      exact isCompact_range (VA.ι ≫ pushout.inl VA.ι (φ.hom ≫ VB.ι)).continuous
  refine ⟨?_, inferInstance, inferInstance⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun b : Bool => cond b (pushout.inl VA.ι (φ.hom ≫ VB.ι)).opensRange
      (pushout.inr VA.ι (φ.hom ≫ VB.ι)).opensRange) (by rw [iSup_bool_eq]; exact hcov) ?_
  rintro (_ | _)
  · dsimp only [Bool.cond_false]
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (pushout.inr VA.ι (φ.hom ≫ VB.ι))
      (Scheme.Opens.ι _) (congrArg TopologicalSpace.Opens.carrier
        (pushout.inr VA.ι (φ.hom ≫ VB.ι)).opensRange.opensRange_ι.symm), Category.assoc, hjBq]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hqB.1
  · dsimp only [Bool.cond_true]
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (pushout.inl VA.ι (φ.hom ≫ VB.ι))
      (Scheme.Opens.ι _) (congrArg TopologicalSpace.Opens.carrier
        (pushout.inl VA.ι (φ.hom ≫ VB.ι)).opensRange.opensRange_ι.symm), Category.assoc, hjAq]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hqA.1

/-! ### Induction over a finite cover -/

/-- If `X` is covered by finitely many quasi-compact opens each of which has a model over a stage,
then `X` has a model over a stage.  The induction glues two pieces at a time, which is why the
quasi-compactness of the intersections is available at every step. -/
private lemma hasModel_of_finite_cover (hc : IsLimit c) {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (f : X ⟶ c.pt) {J : Type u} [Finite J] (U : J → X.Opens) (hU : IsOpenCover U)
    (hUc : ∀ k, IsCompact (U k).1) (hUm : ∀ k, HasModel D c ((U k).ι ≫ f)) :
    HasModel D c f := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have key : ∀ T : Finset J, IsCompact ((⨆ k ∈ T, U k : X.Opens) : Set X) ∧
      HasModel D c ((⨆ k ∈ T, U k : X.Opens).ι ≫ f) := by
    intro T
    induction T using Finset.induction with
    | empty =>
      have hbot : (⨆ k ∈ (∅ : Finset J), U k : X.Opens) = ⊥ := by simp
      rw [hbot]
      refine ⟨by rw [TopologicalSpace.Opens.coe_bot]; exact isCompact_empty, ?_⟩
      have : IsEmpty (⊥ : X.Opens).toScheme := inferInstanceAs (IsEmpty (∅ : Set X))
      exact hasModel_of_isEmpty D c _
    | insert k T hk ih =>
      obtain ⟨hWc, hWm⟩ := ih
      have hins : (⨆ l ∈ insert k T, U l : X.Opens) = U k ⊔ ⨆ l ∈ T, U l := by
        apply TopologicalSpace.Opens.ext
        simp
      rw [hins]
      refine ⟨by rw [TopologicalSpace.Opens.coe_sup]; exact (hUc k).union hWc, ?_⟩
      set W' : X.Opens := U k ⊔ ⨆ l ∈ T, U l with hW'
      have : QuasiSeparatedSpace W'.toScheme :=
        QuasiSeparatedSpace.of_isOpenEmbedding W'.ι.isOpenEmbedding
      have hsup : (W'.ι ⁻¹ᵁ U k) ⊔ (W'.ι ⁻¹ᵁ (⨆ l ∈ T, U l : X.Opens)) = ⊤ := by
        rw [← Scheme.Hom.preimage_sup, ← hW', Scheme.Opens.ι_preimage_self]
      have hsub : ∀ {V : X.Opens}, V ≤ W' → HasModel D c (V.ι ≫ f) →
          HasModel D c ((W'.ι ⁻¹ᵁ V).ι ≫ W'.ι ≫ f) := fun h hV => by
        refine HasModel.of_iso D c (isoOfImageEq _ _ (image_preimage_ι h)).symm ?_ hV
        rw [Iso.symm_hom, Iso.inv_comp_eq, isoOfImageEq_hom_assoc]
      exact hasModel_of_sup D c hc (W'.ι ≫ f) hsup
        (isCompact_preimage_ι le_sup_left (hUc k))
        (isCompact_preimage_ι le_sup_right hWc) (hsub le_sup_left (hUm k))
        (hsub le_sup_right hWm)
  have htop : (⨆ k ∈ (Finset.univ : Finset J), U k : X.Opens) = ⊤ := by
    have : (⨆ k ∈ (Finset.univ : Finset J), U k : X.Opens) = ⨆ k, U k := by simp
    rw [this]
    exact hU
  have h := (key Finset.univ).2
  rw [htop] at h
  refine HasModel.of_iso D c (X.topIso).symm ?_ h
  rw [Iso.symm_hom, ← Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.id_comp]

/-! ### Essential surjectivity -/

/-- **Stacks Project, Tag 01ZM part (1)**, at an index category in the universe of the schemes:
a scheme of finite presentation over a cofiltered limit of quasi-compact, quasi-separated schemes
with affine transition morphisms is the base change of a scheme of finite presentation over one of
the stages. -/
@[ega "IV 8.1.1" "more general", sga "3 VIB 10.0" "more general"]
public theorem exists_isPullback_of_finitePresentation (hc : IsLimit c) {X : Scheme.{u}}
    (f : X ⟶ c.pt) (hf : FinitePresentation f) :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (g : X ⟶ Y),
      FinitePresentation p ∧ IsPullback g f p (c.π.app i) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app D c hc i₀
  have : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace (c.π.app i₀)
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  have h1 : LocallyOfFinitePresentation f := hf.1
  have h2 : QuasiCompact f := hf.2.1
  have h3 : QuasiSeparated f := hf.2.2
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨i, J, hJ, U, V, Vᵢ, Xᵢ, fᵢ, g, hcov, hall⟩ := exists_stage_isAffineModels D c hc f
  have : Finite J := hJ
  refine hasModel_of_finite_cover D c hc f U hcov (fun k => (hall k).1.isCompact) fun k => ?_
  have haff : IsAffine (Xᵢ k) := (hall k).2.2.2.1
  have : CompactSpace (Xᵢ k) := inferInstance
  have : QuasiSeparatedSpace (Xᵢ k) := inferInstance
  have hlfp : LocallyOfFinitePresentation (fᵢ k) := (hall k).2.2.2.2.2.1
  exact ⟨i, Xᵢ k, fᵢ k ≫ (Vᵢ k).ι, g k,
    finitePresentation_of_compactSpace _ (MorphismProperty.comp_mem _ _ _ hlfp inferInstance),
    (hall k).2.2.2.2.2.2⟩

end Glue

/-- **Stacks Project, Tag 01ZM part (1)**, with the index universes independent of the scheme
universe at the cost of `CategoryTheory.EssentiallySmall.{u}` on the index category: this is the
essential-surjectivity half of Stacks Tag 0EY1.  See
`AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall` for the
same statement in the `CategoryTheory.Over.pullback` idiom, which is where the tag sits. -/
@[ega "IV 8.8.3" "essential surjectivity"]
public theorem exists_isPullback_of_finitePresentation_of_essentiallySmall {I : Type v}
    [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) (hf : FinitePresentation f) :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (g : X ⟶ Y),
      FinitePresentation p ∧ IsPullback g f p (c.π.app i) := by
  let e := equivSmallModel.{u} I
  have : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  have h1 : ∀ {j k : SmallModel.{u} I} (a : j ⟶ k), IsAffineHom ((e.inverse ⋙ D).map a) := by
    intros; dsimp; infer_instance
  have h2 : ∀ j : SmallModel.{u} I, CompactSpace ((e.inverse ⋙ D).obj j) := by
    intro j; dsimp; infer_instance
  have h3 : ∀ j : SmallModel.{u} I, QuasiSeparatedSpace ((e.inverse ⋙ D).obj j) := by
    intro j; dsimp; infer_instance
  obtain ⟨j, Y, p, g, hp, hpb⟩ := exists_isPullback_of_finitePresentation (e.inverse ⋙ D)
    (c.whisker e.inverse) ((Functor.Initial.isLimitWhiskerEquiv e.inverse c).symm hc) f hf
  exact ⟨e.inverse.obj j, Y, p, g, hp, hpb⟩

/-- `AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation` with the index
universes independent of the scheme universe, at the cost of `CategoryTheory.LocallySmall.{u}` and
`CategoryTheory.InitiallySmall.{u}` on the index category.  These are the hypotheses under which
`StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit` frees Mathlib's limit
theory, and they are weaker than the `CategoryTheory.EssentiallySmall.{u}` of
`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall`. -/
@[ega "IV 8.8.3" "essential surjectivity"]
public theorem exists_isPullback_of_finitePresentation_of_initiallySmall {I : Type uI}
    [Category.{v} I] [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) (hf : FinitePresentation f) :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (g : X ⟶ Y),
      FinitePresentation p ∧ IsPullback g f p (c.π.app i) := by
  have h₁ : ∀ {a b : CofilteredInitialModel.{u} I} (g : a ⟶ b),
      IsAffineHom ((fromCofilteredInitialModel.{u} I ⋙ D).map g) := by
    intros; dsimp; infer_instance
  have h₂ : ∀ a, CompactSpace ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  have h₃ : ∀ a, QuasiSeparatedSpace ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  obtain ⟨a, Y, p, g, hp, hpb⟩ := exists_isPullback_of_finitePresentation
    (fromCofilteredInitialModel.{u} I ⋙ D) _
    ((Functor.Initial.isLimitWhiskerEquiv (fromCofilteredInitialModel.{u} I) c).symm hc) f hf
  exact ⟨_, Y, p, g, hp, hpb⟩

/-- Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact, quasi-separated schemes with affine
transition morphisms. Every scheme of finite presentation over `S` is isomorphic, over `S`, to the
base change of a scheme of finite presentation over one of the stages `Sᵢ`.

This is
`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall`
stated with `CategoryTheory.Over.pullback`. The index hypothesis
`CategoryTheory.EssentiallySmall.{u} I` is relative to the universe of the schemes. -/
@[stacks 01ZM "part (1)",
  sga "3 VIB 10.0" "(ii)",
  sga "4 VII 5.2" "(b)",
  sga "4 VII 5.3" "essential surjectivity",
  ega "IV 8.1.1" "more general",
  ega "IV 8.8.3" "essential surjectivity"]
public theorem exists_model_of_finitePresentation_of_essentiallySmall {I : Type v}
    [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (X : Over c.pt) (hX : FinitePresentation X.hom) :
    ∃ (i : I) (Xᵢ : Over (D.obj i)), FinitePresentation Xᵢ.hom ∧
      Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xᵢ) := by
  obtain ⟨i, Y, p, g, hp, hpb⟩ :=
    exists_isPullback_of_finitePresentation_of_essentiallySmall D c hc X.hom hX
  exact ⟨i, Over.mk p, hp, ⟨Over.isoMk hpb.isoPullback (by simp)⟩⟩

/-- **Essential surjectivity of base change, over quasi-compact, quasi-separated stages.**

Let `S = lim Sᵢ` be a directed inverse limit of quasi-compact, quasi-separated schemes with affine
transition morphisms, and let `X` be a quasi-compact, quasi-separated scheme locally of finite
presentation over `S`.  Then `X` is isomorphic, over `S`, to the base change of a quasi-compact,
quasi-separated scheme locally of finite presentation over one of the stages `Sᵢ`.

This is the special case, for stages that are quasi-compact and quasi-separated, of
`AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation`, which assumes
nothing about the stages and is the form the source states.

The index hypothesis `CategoryTheory.FinallySmall.{u} I` asks that `I` have a `u`-small cofinal
set of objects; it is automatic for the directed *set* of the source, and is needed because the
comparison of the sections of the limit with the sections at the stages is a statement about an
index category at the scheme universe. -/
@[sga "4 VII 5.3" "essential surjectivity",
  ega "IV 8.1.1" "more general",
  ega "IV 8.8.2",
  ega "IV 8.8.3" "essential surjectivity", sga "3 VIB 10.0" "more general", sga "4 VII 5.2"]
public theorem exists_model_of_finitePresentation {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] [FinallySmall.{u} I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (X : Over c.pt)
    (hXqc : CompactSpace X.left) (hXqs : QuasiSeparatedSpace X.left)
    (hX : LocallyOfFinitePresentation X.hom) :
    ∃ (i : I) (Xᵢ : Over (D.obj (.op i))),
      CompactSpace Xᵢ.left ∧ QuasiSeparatedSpace Xᵢ.left ∧
        LocallyOfFinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app (.op i))).obj Xᵢ) := by
  have := hXqc
  have := hXqs
  have : IsAffineHom (c.π.app (.op (Classical.arbitrary I))) :=
    isAffineHom_π_app_of_initiallySmall D c hc _
  have : CompactSpace c.pt :=
    QuasiCompact.compactSpace_of_compactSpace (c.π.app (.op (Classical.arbitrary I)))
  have : QuasiSeparatedSpace c.pt :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app (.op (Classical.arbitrary I)))
  obtain ⟨i, Y, p, g, hp, hpb⟩ := exists_isPullback_of_finitePresentation_of_initiallySmall D c hc
    X.hom ⟨hX, inferInstance, inferInstance⟩
  have h1 : QuasiCompact p := hp.2.1
  have h2 : QuasiSeparated p := hp.2.2
  exact ⟨i.unop, Over.mk p, QuasiCompact.compactSpace_of_compactSpace p,
    quasiSeparatedSpace_of_quasiSeparated p, hp.1, ⟨Over.isoMk hpb.isoPullback (by simp)⟩⟩

/-- **Stacks Tag 01ZM part (1) discharges
`AlgebraicGeometry.LimitDescent.HasFinitePresentationModels`**, the hypothesis under which the
flat-model results of `StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystem` are stated. -/
public theorem hasFinitePresentationModels : HasFinitePresentationModels.{u} := by
  intro J _ _ D _ _ _ c hc X hX
  obtain ⟨i, Y, p, g, hp, hpb⟩ := exists_isPullback_of_finitePresentation D c hc X.hom hX
  exact ⟨i, Over.mk p, hp, ⟨Over.isoMk hpb.isoPullback (by simp)⟩⟩

end LimitDescent

end AlgebraicGeometry
