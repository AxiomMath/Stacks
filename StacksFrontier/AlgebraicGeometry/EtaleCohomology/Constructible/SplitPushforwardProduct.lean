module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitSections
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections
public import StacksFrontier.CategoryTheory.Sites.SheafFanOfSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along a split étale morphism preserves constructible sheaves

Let `p : T ⟶ S` be an étale morphism of a big étale site which is *split*: it carries sheet data
`Stacks.Etale.IsSplitOver (B.inclusion.map p) (𝟙 S)`, that is finitely many sections `S ⟶ T` of
`p` through which every `S`-point of `T` factors locally on its source and which are pairwise
disjoint. Then the direct image along `p` of a sheaf on the small étale site of `T` is the
product, over the sheets, of its restrictions along them; and since restriction along a sheet is
inverse image (Stacks 03S3), which preserves constructibility (Stacks 095G), the direct image of
a constructible sheaf along a split `p` is constructible.

Indeed on sections over an object `V` of the small étale site of `S` the direct image is the
sections of the sheaf over `V ×_S T`, and the sheets base change to a family of pairwise disjoint
open immersions `V ⟶ V ×_S T` covering `V ×_S T`; over such a family the sections of a sheaf are
a product, with no compatibility condition to impose.

## Main results

* `AlgebraicGeometry.splitSheetGraph` — the section of the base change of `V` along `p` cut out by
  a sheet, natural in `V`.
* `AlgebraicGeometry.isLimitFanSplitPushforward` and
  `AlgebraicGeometry.splitPushforwardIsoProduct` — the direct image along `p`, with its
  restriction maps to the sheets, is a product of the restrictions along the sheets; the second
  states this as an isomorphism with a limit over the discrete category of sheets.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_splitSheetRestriction` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_splitSheetRestriction` — restriction along a sheet
  preserves constructibility.
* `AlgebraicGeometry.isConstructibleSetSheaf_splitPushforward`,
  `AlgebraicGeometry.isConstructibleAbelianSheaf_splitPushforward` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_splitPushforward` — the direct image along a split
  étale morphism preserves constructible sheaves of sets, of abelian groups, and of modules over a
  Noetherian ring.
* `CategoryTheory.ObjectProperty.isClosedUnderFiniteProducts_of_isWeakSerreClass` — a weak Serre
  class in an abelian category is closed under finite products, which is how the abelian and module
  cases use Stacks 03RZ (2) and (3).

## What remains for Stacks 095H, and why no tag appears here

**No `@[stacks 095H]` attribute appears in this file.** Tag 095H asserts that the direct image
along a *finite étale* morphism preserves constructible sheaves, and splitness is strictly
stronger than what a finite étale morphism satisfies: by Stacks 04HN, in the form
`Stacks.Etale.exists_isSplitOver`, a finite étale morphism carries sheet data only over an étale
neighbourhood of each point of the base, not over the base itself. Three further steps are needed
to get from what is proved here to 095H, and none of them is carried out in this file:

* the reduction of constructibility to an open cover of the base, Stacks 095F, available as
  `AlgebraicGeometry.isConstructibleFiniteSheaf_of_openCover` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_of_openCover`;
* the identification of the restriction of a direct image with the direct image of a restriction,
  `AlgebraicGeometry.smallEtaleRestrictionPushforwardBaseChangeIso`, which is what carries the
  hypothesis across the étale neighbourhood;
* the descent of constructibility along a surjective morphism, Stacks 095Q, which is what turns a
  statement holding on an étale cover of the base into one holding on the base. This is the step
  that genuinely needs more than Zariski-local information, because the trivialization of Stacks
  04HN is étale-local and not Zariski-local.

Finiteness of `p` is *not* assumed here: sheet data already provides a finite index set, so the
split case needs only étaleness. The hypotheses that are assumed are assumed in full — the
Noetherian hypothesis on the coefficient ring of the module case is the one carried by
`AlgebraicGeometry.IsConstructibleModuleSheaf` itself and is not dropped.

## Implementation notes

In this site flavour one object has several non-syntactic spellings: the underlying scheme of
`(smallEtaleBaseChange B p).obj V` is the fibre product `pullback V.obj.hom p` under a different
name, and the domain of `smallEtalePostcompose B T.1 T.property U` spells the base as
`U.obj.left`. The elaborator identifies these, but `rw` and `simp` match syntactically and so
cannot be relied on for the associativity steps; those are therefore chained in term mode, as in
`AlgebraicGeometry.map_smallEtaleLiftGraph_eq`. The one place where this matters in a naturality
square is reduced to a single projection by
`AlgebraicGeometry.smallEtaleBaseChange_hom_ext`: a morphism of the site into a base change is
determined by its first component, the second being its own structure morphism.

`Stacks.Etale.IsSplitOver.baseChangeOfId` repeats `Stacks.Etale.IsSplitOver.comp` for the identity
of the base, so that the base-changed sheets are literally `g ≫ sheet i` rather than carrying a
trailing identity; the composite spelling is what the fibre-product comparisons have to match.

## References

* [Stacks Project, Tag 095H](https://stacks.math.columbia.edu/tag/095H)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w r t

namespace Stacks.Etale

/-- Sheet data over the identity of the base is sheet data over an arbitrary morphism to the
base, by composing the sheets with it. This is `Stacks.Etale.IsSplitOver.comp` in the special
case of the identity, rebuilt so that the base morphism appears without a trailing identity. -/
public def IsSplitOver.baseChangeOfId {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
    (h : IsSplitOver f (𝟙 S)) {V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ S) :
    IsSplitOver f g where
  I := h.I
  finite_I := h.finite_I
  sheet i := g ≫ h.sheet i
  sheet_comp i := by rw [Category.assoc, h.sheet_comp, Category.comp_id]
  exists_openCover := by
    intro Z z b hb
    obtain ⟨κ, Y, pr, hpr, idx, hcov, hfac⟩ :=
      h.exists_openCover (z ≫ g) b (by rwa [Category.comp_id])
    exact ⟨κ, Y, pr, hpr, idx, hcov, fun k ↦ by simpa only [Category.assoc] using hfac k⟩
  isEmpty_of_sheet_eq := by
    intro Z z i j hij hz
    exact h.isEmpty_of_sheet_eq (z ≫ g) hij (by simpa only [Category.assoc] using hz)

end Stacks.Etale

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (p : T ⟶ S)

/-- **A morphism of the small étale site into a base change is determined by its first
component.** Its second component is its own structure morphism, because it is a morphism over
the base of the base change. -/
public theorem smallEtaleBaseChange_hom_ext {V : SmallEtale B S.1 S.property}
    {W : SmallEtale B T.1 T.property} {a b : W ⟶ (smallEtaleBaseChange B p).obj V}
    (h : a.hom.left ≫ pullback.fst V.obj.hom p = b.hom.left ≫ pullback.fst V.obj.hom p) :
    a = b :=
  (SmallEtale.inclusion B T.1 T.property).map_injective <|
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a.hom).trans (Over.w b.hom).symm))

/-- The fibre square of schemes exhibiting the base change of `V` along `p`. -/
public theorem isPullback_splitBaseChange (V : SmallEtale B S.1 S.property) :
    IsPullback (B.inclusion.map (pullback.snd V.obj.hom p))
      (B.inclusion.map (pullback.fst V.obj.hom p)) (B.inclusion.map p)
      (B.inclusion.map V.obj.hom) :=
  (IsPullback.of_hasPullback V.obj.hom p).flip.map B.inclusion

section Sheets

variable (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (𝟙 (B.inclusion.obj S)))

/-- A sheet of global sheet data for `p`, read as a morphism of the big étale site. -/
public def splitSheet (i : hsp.I) : S ⟶ T := ObjectProperty.homMk (hsp.sheet i)

/-- The underlying morphism of schemes of a sheet is the sheet. -/
public theorem inclusion_map_splitSheet (i : hsp.I) :
    B.inclusion.map (splitSheet B p hsp i) = hsp.sheet i := rfl

/-- A sheet is a section of `p`. -/
public theorem splitSheet_comp (i : hsp.I) : splitSheet B p hsp i ≫ p = 𝟙 S := by
  apply B.inclusion.map_injective
  rw [Functor.map_comp, CategoryTheory.Functor.map_id, inclusion_map_splitSheet]
  exact hsp.sheet_comp i

variable [Etale (B.inclusion.map p)]

/-- A sheet is étale, being a section of an étale morphism. -/
public theorem etale_splitSheet (i : hsp.I) :
    Etale (B.inclusion.map (splitSheet B p hsp i)) := by
  have : Etale (B.inclusion.map (splitSheet B p hsp i) ≫ B.inclusion.map p) := by
    rw [← Functor.map_comp, splitSheet_comp, CategoryTheory.Functor.map_id]
    infer_instance
  exact Etale.of_comp _ (B.inclusion.map p)

attribute [local instance] etale_splitSheet

/-- Restriction along a sheet, as a functor between the small étale sites: an étale scheme over
`S` becomes one over `T` by composing with the sheet. -/
public abbrev splitSheetFunctor (i : hsp.I) :
    SmallEtale B S.1 S.property ⥤ SmallEtale B T.1 T.property :=
  smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B (splitSheet B p hsp i))

/-- Restriction along a sheet is continuous, by Stacks 03S3. -/
public instance isContinuous_splitSheetFunctor (i : hsp.I) :
    (splitSheetFunctor B p hsp i).IsContinuous
      (SmallEtale.topology B S.1 S.property) (SmallEtale.topology B T.1 T.property) :=
  isContinuous_smallEtalePostcompose_ofEtaleHom B (splitSheet B p hsp i)

/-- **The graph of a sheet.** The sheet turns an étale scheme `V` over `S` into one over `T`,
and the identity of `V` together with that structure morphism is a section of the base change of
`V` along `p`. It is natural in `V`. -/
public def splitSheetGraph (i : hsp.I) :
    splitSheetFunctor B p hsp i ⟶ smallEtaleBaseChange B p where
  app V := smallEtaleBaseChangeLift B p V _ (𝟙 V.obj.left) (by
    change 𝟙 V.obj.left ≫ V.obj.hom = (V.obj.hom ≫ splitSheet B p hsp i) ≫ p
    rw [Category.id_comp, Category.assoc, splitSheet_comp, Category.comp_id])
  naturality V V' k := by
    refine smallEtaleBaseChange_hom_ext B p ?_
    have hL : ((splitSheetFunctor B p hsp i).map k ≫
        smallEtaleBaseChangeLift B p V' ((splitSheetFunctor B p hsp i).obj V')
          (𝟙 V'.obj.left) (by
            change 𝟙 V'.obj.left ≫ V'.obj.hom = (V'.obj.hom ≫ splitSheet B p hsp i) ≫ p
            rw [Category.id_comp, Category.assoc, splitSheet_comp,
              Category.comp_id])).hom.left ≫ pullback.fst V'.obj.hom p = k.hom.left :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun m => k.hom.left ≫ m) (pullback.lift_fst _ _ _)).trans
          (Category.comp_id _))
    refine hL.trans (Eq.symm ?_)
    have h₂ : ((smallEtaleBaseChange B p).map k).hom.left ≫ pullback.fst V'.obj.hom p =
        pullback.fst V.obj.hom p ≫ k.hom.left := pullback.lift_fst _ _ _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => _ ≫ m) h₂).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (fun m => m ≫ k.hom.left) (pullback.lift_fst _ _ _)).trans
      (Category.id_comp _)

/-- **The graph of a sheet is the section of the base change determined by that sheet.** Both
are the lift into the fibre product with first component the identity and second component the
structure morphism composed with the sheet. -/
public theorem toScheme_map_splitSheetGraph (i : hsp.I) (V : SmallEtale B S.1 S.property) :
    (SmallEtale.toScheme B T.1 T.property).map ((splitSheetGraph B p hsp i).app V) =
      (hsp.baseChangeOfId (B.inclusion.map V.obj.hom)).sectionOfIsPullback
        (isPullback_splitBaseChange B p V) i := by
  refine (isPullback_splitBaseChange B p V).hom_ext ?_ ?_
  · refine Eq.trans ?_
      ((hsp.baseChangeOfId (B.inclusion.map V.obj.hom)).sectionOfIsPullback_comp_fst
        (isPullback_splitBaseChange B p V) i).symm
    exact (B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map (pullback.lift_snd _ _ _)).trans (B.inclusion.map_comp _ _))
  · refine Eq.trans ?_
      ((hsp.baseChangeOfId (B.inclusion.map V.obj.hom)).sectionOfIsPullback_comp_snd
        (isPullback_splitBaseChange B p V) i).symm
    exact (B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map (pullback.lift_fst _ _ _)).trans
        (CategoryTheory.Functor.map_id _ _))

/-- The graph of a sheet is a monomorphism of the small étale site: it is split by the first
projection of the fibre product on underlying schemes, and the site is faithful over schemes. -/
public theorem mono_splitSheetGraph (i : hsp.I) (V : SmallEtale B S.1 S.property) :
    Mono ((splitSheetGraph B p hsp i).app V) := by
  have : IsSplitMono ((splitSheetGraph B p hsp i).app V).hom.left :=
    IsSplitMono.mk' ⟨pullback.fst V.obj.hom p, pullback.lift_fst _ _ _⟩
  refine ⟨fun {Z} a b hab => ?_⟩
  apply (SmallEtale.inclusion B T.1 T.property).map_injective
  apply Over.OverMorphism.ext
  refine (cancel_mono ((splitSheetGraph B p hsp i).app V).hom.left).1 ?_
  exact congrArg (fun m : Z ⟶ (smallEtaleBaseChange B p).obj V => m.hom.left) hab

/-- **The graphs of the sheets cover the base change.** Every point of `V ×_S T` lies on the
graph of some sheet, so the graphs form a covering family of the small étale site. -/
public theorem splitSheetGraph_mem_topology (V : SmallEtale B S.1 S.property) :
    Sieve.ofArrows (fun i => (splitSheetFunctor B p hsp i).obj V)
        (fun i => (splitSheetGraph B p hsp i).app V) ∈
      SmallEtale.topology B T.1 T.property ((smallEtaleBaseChange B p).obj V) := by
  refine ofArrows_mem_topology B T.property _ _ fun x => ?_
  obtain ⟨i, hi⟩ := Stacks.Etale.IsSplitOver.exists_mem_range_sectionOfIsPullback
    (hsp.baseChangeOfId (B.inclusion.map V.obj.hom)) (isPullback_splitBaseChange B p V) x
  refine ⟨(i : hsp.I), ?_⟩
  rwa [toScheme_map_splitSheetGraph B p hsp (i : hsp.I) V]

/-- **The graphs of two distinct sheets are disjoint.** An object of the small étale site mapping
to the base change through both graphs has empty underlying scheme, because the two sheets then
agree on it; so it is covered by the empty sieve. -/
public theorem splitSheetGraph_bot_mem_topology (V : SmallEtale B S.1 S.property)
    (i j : hsp.I) (hij : i ≠ j) {Z : SmallEtale B T.1 T.property}
    (gi : Z ⟶ (splitSheetFunctor B p hsp i).obj V)
    (gj : Z ⟶ (splitSheetFunctor B p hsp j).obj V)
    (hg : gi ≫ (splitSheetGraph B p hsp i).app V = gj ≫ (splitSheetGraph B p hsp j).app V) :
    (⊥ : Sieve Z) ∈ SmallEtale.topology B T.1 T.property Z := by
  refine bot_mem_topology B T.property ?_
  refine Stacks.Etale.IsSplitOver.isEmpty_of_mem_two_sections
    (hsp.baseChangeOfId (B.inclusion.map V.obj.hom)) (isPullback_splitBaseChange B p V) hij
    ((SmallEtale.toScheme B T.1 T.property).map gi ≫
      (hsp.baseChangeOfId (B.inclusion.map V.obj.hom)).sectionOfIsPullback
        (isPullback_splitBaseChange B p V) i)
    ((SmallEtale.toScheme B T.1 T.property).map gi) rfl
    ((SmallEtale.toScheme B T.1 T.property).map gj) ?_
  have hmid : (SmallEtale.toScheme B T.1 T.property).map gj ≫
        (SmallEtale.toScheme B T.1 T.property).map ((splitSheetGraph B p hsp j).app V) =
      (SmallEtale.toScheme B T.1 T.property).map gi ≫
        (SmallEtale.toScheme B T.1 T.property).map ((splitSheetGraph B p hsp i).app V) :=
    ((SmallEtale.toScheme B T.1 T.property).map_comp _ _).symm.trans
      ((congrArg (SmallEtale.toScheme B T.1 T.property).map hg.symm).trans
        ((SmallEtale.toScheme B T.1 T.property).map_comp _ _))
  refine (congrArg (fun m => (SmallEtale.toScheme B T.1 T.property).map gj ≫ m)
    (toScheme_map_splitSheetGraph B p hsp j V).symm).trans (hmid.trans ?_)
  exact congrArg (fun m => (SmallEtale.toScheme B T.1 T.property).map gi ≫ m)
    (toScheme_map_splitSheetGraph B p hsp i V)

variable (A : Type w) [Category.{v} A]

/-- **The sections of a sheaf over a base change along a split morphism are a product.** The
graphs of the sheets are a pairwise disjoint covering family, over which a family of sections
glues uniquely. -/
public def isLimitFanSplitSections
    (F : Sheaf (SmallEtale.topology B T.1 T.property) A)
    (V : SmallEtale B S.1 S.property) :
    IsLimit (Fan.mk (F.obj.obj (op ((smallEtaleBaseChange B p).obj V)))
      fun i => F.obj.map ((splitSheetGraph B p hsp i).app V).op) :=
  F.property.isLimitFanSectionsOfDisjointArrows _
    (splitSheetGraph_mem_topology B p hsp V)
    (fun i => mono_splitSheetGraph B p hsp i V)
    (fun i j hij _ gi gj hg => splitSheetGraph_bot_mem_topology B p hsp V i j hij gi gj hg)

/-- Restriction of a sheaf on `T` along a sheet: the direct image of composition with the
sheet, which is the inverse image along it by Stacks 03S3. -/
public abbrev splitSheetRestriction (i : hsp.I) :
    Sheaf (SmallEtale.topology B T.1 T.property) A ⥤
      Sheaf (SmallEtale.topology B S.1 S.property) A :=
  (splitSheetFunctor B p hsp i).sheafPushforwardContinuous A
    (SmallEtale.topology B S.1 S.property) (SmallEtale.topology B T.1 T.property)

/-- The restriction map from the direct image along `p` to the restriction along a sheet, given
by restricting a section along the graph of the sheet. -/
public def splitPushforwardLeg (F : Sheaf (SmallEtale.topology B T.1 T.property) A)
    (i : hsp.I) :
    (B.smallPushforward p A).obj F ⟶ (splitSheetRestriction B p hsp A i).obj F :=
  (Functor.sheafPushforwardContinuousNatTrans
    (J := SmallEtale.topology B S.1 S.property)
    (K := SmallEtale.topology B T.1 T.property)
    (splitSheetGraph B p hsp i) A).app F

/-- **The direct image along a split morphism is a product of the restrictions along its
sheets.** Being a product is checked on sections, where it is
`AlgebraicGeometry.isLimitFanSplitSections`. -/
public def isLimitFanSplitPushforward [HasLimitsOfShape (Discrete hsp.I) A]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) A) :
    IsLimit (Fan.mk ((B.smallPushforward p A).obj F) (splitPushforwardLeg B p hsp A F)) :=
  isLimitFanOfSections _ _ fun X => isLimitFanSplitSections B p hsp A F X.unop

/-- **The direct image along a split morphism is a product of the restrictions along its
sheets**, as an isomorphism with the limit over the discrete category of sheets. -/
public def splitPushforwardIsoProduct [HasLimitsOfShape (Discrete hsp.I) A]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) A) :
    (B.smallPushforward p A).obj F ≅
      limit (Discrete.functor fun i => (splitSheetRestriction B p hsp A i).obj F) :=
  (isLimitFanSplitPushforward B p hsp A F).conePointUniqueUpToIso (limit.isLimit _)

end Sheets

end AlgebraicGeometry

namespace CategoryTheory.ObjectProperty

/-- **A weak Serre class in an abelian category is closed under finite products.** A binary
product is a binary biproduct, hence an extension of one factor by the other, and the empty
product is a zero object. -/
public theorem isClosedUnderFiniteProducts_of_isWeakSerreClass {C : Type*} [Category C]
    [Abelian C] (P : ObjectProperty C) [P.IsWeakSerreClass] :
    P.IsClosedUnderFiniteProducts := by
  have : P.IsClosedUnderBinaryProducts := by
    refine IsClosedUnderLimitsOfShape.mk' ?_
    rintro _ ⟨K, hK⟩
    exact P.prop_of_iso ((Limits.biprod.isoProd _ _) ≪≫
      (Limits.HasLimit.isoOfNatIso (Limits.diagramIsoPair K)).symm)
      (P.prop_biprod (hK ⟨.left⟩) (hK ⟨.right⟩))
  exact IsClosedUnderFiniteProducts.mk'

/-- The limit of a finite family in a weak Serre class lies in the class. -/
private theorem prop_of_isLimit_fan_of_isWeakSerreClass {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {J : Type*} [Finite J] {f : J → C} {F : Fan f}
    (hF : IsLimit F) (h : ∀ j, P (f j)) : P F.pt := by
  have := isClosedUnderFiniteProducts_of_isWeakSerreClass P
  exact P.prop_of_isLimit_fan hF h

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (p : T ⟶ S) [Etale (B.inclusion.map p)]

section Finite

variable (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (𝟙 (B.inclusion.obj S)))
  {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

/-- Constructibility of a sheaf with values in a concrete category transports along an
isomorphism: the stratification that one of the two sheaves furnishes works for the other, since
inverse image to a stratum carries the isomorphism along. -/
public theorem isConstructibleFiniteSheaf_congr (X : B.Scheme)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) D} (e : F ≅ G)
    (hF : IsConstructibleFiniteSheaf B X F) : IsConstructibleFiniteSheaf B X G :=
  isStratifiedSheaf_congr B X
    (fun Z G' => Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
      (SmallEtale.topology B Z.obj Z.property) G')
    (fun Z _ _ e' h => Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
      (SmallEtale.topology B Z.obj Z.property) e' (hF := h)) e hF

/-- **Restriction along a sheet preserves constructibility.** By Stacks 03S3 restriction along an
étale morphism is the inverse image along it, and Stacks 095G says that inverse image preserves
constructibility. -/
public theorem isConstructibleFiniteSheaf_splitSheetRestriction (i : hsp.I)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) D)
    (hF : IsConstructibleFiniteSheaf B T F) :
    IsConstructibleFiniteSheaf B S ((splitSheetRestriction B p hsp D i).obj F) :=
  have := etale_splitSheet B p hsp i
  isConstructibleFiniteSheaf_congr B S
    ((smallInverseImageIsoPostcomposePushforward B (splitSheet B p hsp i) D).app F)
    (isConstructibleFiniteSheaf_pullback B (splitSheet B p hsp i) F hF)

end Finite

/-- **Stacks 095H for a split morphism, sheaves of sets.** The direct image of a constructible
sheaf of sets along a split étale morphism is constructible: it is the finite product of the
restrictions along the sheets, each constructible by Stacks 095G, and constructible sheaves of
sets are closed under finite limits by Stacks 03RZ (1). -/
@[sga "4 XIV 1.1" "special case"]
public theorem isConstructibleSetSheaf_splitPushforward
    (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (𝟙 (B.inclusion.obj S)))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  classical
  have := hsp.finite_I
  have : Fintype hsp.I := Fintype.ofFinite hsp.I
  refine isConstructibleSetSheaf_congr B S
    (splitPushforwardIsoProduct B p hsp (Type (u + 1)) F).symm ?_
  exact isConstructibleSetSheaf_limit B S
    (Discrete.functor fun i => (splitSheetRestriction B p hsp (Type (u + 1)) i).obj F)
    fun ⟨i⟩ => isConstructibleFiniteSheaf_splitSheetRestriction B p hsp i F hF

/-- **Stacks 095H for a split morphism, sheaves of abelian groups.** The direct image of a
constructible abelian sheaf along a split étale morphism is constructible: it is the finite
product of the restrictions along the sheets, each constructible by Stacks 095G, and the
constructible abelian sheaves are a weak Serre subcategory by Stacks 03RZ (2), hence closed under
finite products. -/
public theorem isConstructibleAbelianSheaf_splitPushforward
    (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (𝟙 (B.inclusion.obj S)))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B T F) :
    IsConstructibleAbelianSheaf B S
      ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F) := by
  have := hsp.finite_I
  exact CategoryTheory.ObjectProperty.prop_of_isLimit_fan_of_isWeakSerreClass
    (P := fun G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} =>
      IsConstructibleAbelianSheaf B S G)
    (isLimitFanSplitPushforward B p hsp AddCommGrpCat.{u + 1} F)
    fun i => isConstructibleFiniteSheaf_splitSheetRestriction B p hsp i F hF

section Modules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]

/-- **Restriction along a sheet preserves constructibility of sheaves of modules.** By
Stacks 03S3 restriction along an étale morphism is the inverse image along it, and Stacks 095G
for modules over a Noetherian ring says that inverse image preserves constructibility. -/
public theorem isConstructibleModuleSheaf_splitSheetRestriction
    (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (𝟙 (B.inclusion.obj S))) (i : hsp.I)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{max (u + 1) w} Λ))
    (hF : IsConstructibleModuleSheaf B T Λ F) :
    IsConstructibleModuleSheaf B S Λ
      ((splitSheetRestriction B p hsp (ModuleCat.{max (u + 1) w} Λ) i).obj F) :=
  have := etale_splitSheet B p hsp i
  isConstructibleModuleSheaf_congr B Λ S
    ((smallInverseImageIsoPostcomposePushforward B (splitSheet B p hsp i)
      (ModuleCat.{max (u + 1) w} Λ)).app F)
    (isConstructibleModuleSheaf_pullback B Λ (splitSheet B p hsp i) F hF)

/-- **Stacks 095H for a split morphism, sheaves of modules over a Noetherian ring.** The direct
image of a constructible sheaf of `Λ`-modules along a split étale morphism is constructible: it
is the finite product of the restrictions along the sheets, each constructible by Stacks 095G,
and the constructible sheaves of `Λ`-modules are a weak Serre subcategory by Stacks 03RZ (3),
hence closed under finite products. -/
public theorem isConstructibleModuleSheaf_splitPushforward
    (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (𝟙 (B.inclusion.obj S)))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{max (u + 1) w} Λ))
    (hF : IsConstructibleModuleSheaf B T Λ F) :
    IsConstructibleModuleSheaf B S Λ
      ((B.smallPushforward p (ModuleCat.{max (u + 1) w} Λ)).obj F) := by
  have := hsp.finite_I
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) w} Λ) :=
    hasLimitsOfSizeShrink.{u, u, max (u + 1) w, max (u + 1) w} _
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf B S Λ
  exact CategoryTheory.ObjectProperty.prop_of_isLimit_fan_of_isWeakSerreClass
    (P := fun G : Sheaf (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) w} Λ) => IsConstructibleModuleSheaf B S Λ G)
    (isLimitFanSplitPushforward B p hsp (ModuleCat.{max (u + 1) w} Λ) F)
    fun i => isConstructibleModuleSheaf_splitSheetRestriction B p Λ hsp i F hF

end Modules

end AlgebraicGeometry

end
