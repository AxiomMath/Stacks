module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalIso

/-!
# Comparing two reconstruction charts on their overlap

`AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover` produces,
for an affine open cover `U i` of `X` and an equivalence `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)`, opens
`V i` covering `Y` together with, for each `i`, an equivalence `F i : QCoh(𝒪_{U i}) ≌
QCoh(𝒪_{V i})` and two isomorphisms of functors,

* `e.functor ⋙ restriction to V i ≅ restriction to U i ⋙ F i`, and
* `F i ⋙ (inclusion of the quasi-coherent modules) ≅ (f i)^*(-) ⊗ L i`.

Gluing those charts into the single isomorphism `Y ≅ X` that [Stacks, Tag 0GPJ] asserts needs
them to agree on the overlaps, and the rigidity theorem
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` turns that into a question
about one isomorphism of functors on `V i ⊓ V j`.  This file produces that isomorphism from the
per-chart data.  No new mathematics is involved: the two per-chart isomorphisms are composed,
the result is restricted along `V i ⊓ V j ≤ V i`, and the two indices are compared.

Write `k_i : (V i ⊓ V j).toScheme ⟶ (V i).toScheme` for the inclusion of the overlap,
`b_i := k_i ≫ (f i).hom ≫ (U i).ι : (V i ⊓ V j).toScheme ⟶ X` for the chart map read on the
overlap, and `N_i := k_i^*(L i)` for the invertible sheaf restricted to the overlap.  The point
is that the composite of the two per-chart isomorphisms, followed by inverse image along `k_i`,
computes `b_i^*(-) ⊗ N_i` as a functor that **does not mention `i`**, namely
`e.functor` followed by the inverse image along the inclusion `(V i ⊓ V j).ι : V i ⊓ V j ⟶ Y`.
Comparing the two indices against that common value gives
`b_i^*(-) ⊗ N_i ≅ b_j^*(-) ⊗ N_j`.

## Main definitions

* `AlgebraicGeometry.pullbackTensorFunctorPullbackIso`: inverse image and tensor along
  `g : V ⟶ S` followed by inverse image along `q : W ⟶ V` is inverse image and tensor along
  `q ≫ g` with the sheaf pulled back.
* `AlgebraicGeometry.quasicoherentRestrictionCompIotaIsoPullback`: restriction of
  quasi-coherent modules to an open, read in all modules, is the inverse image along the
  inclusion.
* `AlgebraicGeometry.pullbackTensorFunctorIsoOfChartIso`: for the data of one chart,
  `e.functor` followed by the inverse image along a morphism `c : W ⟶ Y` factoring as
  `k ≫ V.ι` is `b^*(-) ⊗ k^*L` for `b = (k ≫ f.hom) ≫ U.ι`.
* `AlgebraicGeometry.pullbackTensorFunctorOverlapIso`: the isomorphism
  `b_i^*(-) ⊗ N_i ≅ b_j^*(-) ⊗ N_j` between the functors of two charts on their overlap.

## Main results

* `AlgebraicGeometry.range_subset_coe_of_comp_ι`: a morphism factoring through `U.ι` has image
  in `U`.
* `AlgebraicGeometry.range_eq_of_iso_pullbackTensorFunctor`: two open immersions out of a
  quasi-compact scheme with isomorphic inverse-image-and-tensor functors have the same image.
* `AlgebraicGeometry.range_subset_of_chartIso_overlap`: on the overlap, the second chart map
  lands in `U i`.
* `AlgebraicGeometry.range_eq_of_chartIso_overlap`: on the overlap, the two chart maps have the
  same image.
* `AlgebraicGeometry.exists_iso_pullbackTensorFunctor_of_isAffineOpenCover`: for the charts
  produced from an affine open cover of `X`, the two chart maps on each overlap have isomorphic
  inverse-image-and-tensor functors and the same image.

## What this does and does not give for [Stacks, Tag 0GPJ]

`AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible` glues the charts into
one isomorphism `Y ≅ X` from two hypotheses: `hVcompat`, that the `f i` agree on `V i ⊓ V j` as
morphisms into `X`, and the mirror `hUcompat` for the inverses on `U i ⊓ U j`.  This file
removes the second of the three obstructions listed in the implementation notes of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalIso.lean`: the hypothesis `θ`
of the rigidity theorem is now *produced* from the reconstruction's own output rather than
assumed.

`hVcompat` itself is not proved in this file, but it IS proved, in
`QuasiCoherent/ReconstructionOverlapCompatible.lean:256`, out of what this file supplies.  That an
invertible sheaf on an affine scheme is the sheaf of an invertible module is proved in
`QuasiCoherent/AffineInvertiblePresentation.lean:162`.  Nor is covering the overlap by affine opens
necessary: `Scheme.affineCover` together
with `Scheme.Cover.hom_ext` suffices, which is why
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_isInvertible`
(`ReconstructionOverlapCompatible.lean:169`) can drop both the affine-source and the
presentation restriction.

What this file obtains unconditionally, and what is used there, is the comparison `θ` together
with the topological statement `AlgebraicGeometry.range_eq_of_chartIso_overlap`: the two chart
maps have the same image on the overlap, which is `hVcompat` after forgetting everything but the
underlying sets.  The mirror hypothesis `hUcompat` is untouched here; it needs the inverse of a
reconstruction pair, which is `QuasiCoherent/ReconstructionPairInverse.lean:349`.

## Implementation notes

The structure sheaf of a scheme is named both as `AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf, and
instance search, which runs at reducible transparency, sees through neither chain; the
definitions involved are therefore made `implicit_reducible` locally.

The indexed statement is assembled with `choose`, so that the families `V`, `f` and `L` stay
opaque local variables; handing an explicit composite to `refine` instead makes the conclusion
unfold definitionally once per index and per conjunct.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 17.16.3 (Tag 01CD)](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  Without this
an invertibility hypothesis spelled with `ringCatSheaf.2` does not deliver
`Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### Restricting the source of `pullbackTensorFunctor` -/

/-- **Inverse image and tensor, followed by a further inverse image.**  For `g : V ⟶ S`, a
sheaf `L` of `𝒪_V`-modules and `q : W ⟶ V`, the functor `q^*(g^*(-) ⊗_{𝒪_V} L)` is
`(q ≫ g)^*(-) ⊗_{𝒪_W} q^*L`.

Two steps.  The inverse image moves past the tensor product by [Stacks, Tag 01CD] with the
left-hand factor held fixed, which is
`AlgebraicGeometry.tensorLeftFunctorCompPullback`; then the two inverse images compose, by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
def pullbackTensorFunctorPullbackIso {S V W : Scheme.{u}} (g : V ⟶ S) (q : W ⟶ V)
    (L : SheafOfModules.{u} V.ringCatSheaf) :
    pullbackTensorFunctor g L ⋙ Scheme.Modules.pullback q ≅
      pullbackTensorFunctor (q ≫ g) ((Scheme.Modules.pullback q).obj L) :=
  Functor.isoWhiskerLeft
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent S.ringCatSheaf) ⋙
        Scheme.Modules.pullback g)
      (tensorLeftFunctorCompPullback q.toLRSHom.toShHom W.ringCatSheaf.2 V.ringCatSheaf.2 L) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent S.ringCatSheaf))
      (Functor.isoWhiskerRight (Scheme.Modules.pullbackComp q g)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ W.presheaf
            (forget₂ CommRingCat RingCat) W.ringCatSheaf.2⟩).obj
          ((Scheme.Modules.pullback q).obj L)))

/-- **Restriction of quasi-coherent modules to an open, read in all modules, is the inverse
image along the inclusion.**  The restriction functor
`AlgebraicGeometry.quasicoherentRestriction` is by construction the lift of
`(inclusion) ⋙ AlgebraicGeometry.Scheme.Modules.restrictFunctor`, so
`CategoryTheory.ObjectProperty.liftCompιIso` cancels the lift against the inclusion, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` identifies restriction along an
open immersion with the inverse image. -/
def quasicoherentRestrictionCompIotaIsoPullback {Y : Scheme.{u}} (V : Y.Opens) :
    quasicoherentRestriction V.ι ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ⋙
        Scheme.Modules.pullback V.ι :=
  (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).liftCompιIso
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ⋙
        Scheme.Modules.restrictFunctor V.ι)
      (fun M ↦ Scheme.Modules.isQuasicoherent_restrictFunctor V.ι M.obj) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf))
      (Scheme.Modules.restrictFunctorIsoPullback V.ι)

/-! ### The per-chart calculation -/

/-- **What one reconstruction chart computes on a smaller scheme.**  Let `E : QCoh(𝒪_X) ⥤
QCoh(𝒪_Y)` be a functor, let `V ⊆ Y` and `U ⊆ X` be opens, and suppose given the data of one
chart of [Stacks, Tag 0GPJ]: a functor `F : QCoh(𝒪_U) ⥤ QCoh(𝒪_V)`, an isomorphism of schemes
`f : V ≅ U`, a sheaf `L` of `𝒪_V`-modules, an isomorphism `α` identifying `E` followed by
restriction to `V` with restriction to `U` followed by `F`, and an isomorphism `β` identifying
`F` with `f^*(-) ⊗ L`.  Let `k : W ⟶ V` be any morphism, let `c = k ≫ V.ι` and let
`b = (k ≫ f.hom) ≫ U.ι`.  Then `E` followed by the inverse image along `c` is
`b^*(-) ⊗_{𝒪_W} k^*L`.

The two morphisms `c` and `b` are taken as variables with their factorisations as hypotheses so
that the conclusion can be stated in whatever form the consumer wants; for the overlap of two
charts `c` is the inclusion of `V i ⊓ V j` into `Y`, which is independent of `i`.

The calculation is: the inverse image along `c = k ≫ V.ι` splits as the inverse image along
`V.ι` followed by the one along `k`
(`AlgebraicGeometry.Scheme.Modules.pullbackComp`); the first of those is restriction to `V`
(`AlgebraicGeometry.quasicoherentRestrictionCompIotaIsoPullback`), where `α` and then `β`
apply; the inverse image along `k` is moved inside by
`AlgebraicGeometry.pullbackTensorFunctorPullbackIso`; and the remaining restriction to `U` is
absorbed into the target by
`AlgebraicGeometry.pullbackTensorFunctorQuasicoherentRestrictIso`. -/
def pullbackTensorFunctorIsoOfChartIso {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {V : Y.Opens} {U : X.Opens}
    {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
    (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L)
    {W : Scheme.{u}} (k : W ⟶ V.toScheme) (c : W ⟶ Y) (b : W ⟶ X)
    (hc : k ≫ V.ι = c) (hb : (k ≫ f.hom) ≫ U.ι = b) :
    E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ⋙
        Scheme.Modules.pullback c ≅
      pullbackTensorFunctor b ((Scheme.Modules.pullback k).obj L) := by
  subst hc hb
  exact Functor.isoWhiskerLeft E (Functor.isoWhiskerLeft
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf))
        (Scheme.Modules.pullbackComp k V.ι).symm) ≪≫
    Functor.isoWhiskerLeft E (Functor.isoWhiskerRight
      (quasicoherentRestrictionCompIotaIsoPullback V).symm (Scheme.Modules.pullback k)) ≪≫
    Functor.isoWhiskerRight α
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ⋙
        Scheme.Modules.pullback k) ≪≫
    Functor.isoWhiskerLeft (quasicoherentRestriction U.ι)
      (Functor.isoWhiskerRight β (Scheme.Modules.pullback k)) ≪≫
    Functor.isoWhiskerLeft (quasicoherentRestriction U.ι)
      (pullbackTensorFunctorPullbackIso f.hom k L) ≪≫
    pullbackTensorFunctorQuasicoherentRestrictIso U (k ≫ f.hom)
      ((Scheme.Modules.pullback k).obj L)

/-! ### The comparison isomorphism on an overlap -/

/-- **The comparison isomorphism of two reconstruction charts over their overlap.**  Given the
chart data of [Stacks, Tag 0GPJ] for two opens `V₁, V₂ ⊆ Y` with the same functor `E` — an
isomorphism of schemes `fₐ : Vₐ ≅ Uₐ`, a sheaf `Lₐ` of `𝒪_{Vₐ}`-modules and the two
isomorphisms `αₐ`, `βₐ` — the two chart maps read on the overlap `V₁ ⊓ V₂`, namely
`bₐ = (inclusion) ≫ (fₐ).hom ≫ (Uₐ).ι`, satisfy

`b₁^*(-) ⊗ (inclusion)^*L₁ ≅ b₂^*(-) ⊗ (inclusion)^*L₂`.

Both sides are computed by `AlgebraicGeometry.pullbackTensorFunctorIsoOfChartIso` to be `E`
followed by the inverse image along the inclusion `V₁ ⊓ V₂ ⟶ Y`, which mentions neither chart;
the isomorphism is the composite of one computation with the inverse of the other.

This is the hypothesis `θ` of
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset`; its other hypothesis is
`AlgebraicGeometry.range_subset_coe_of_comp_ι`. -/
def pullbackTensorFunctorOverlapIso {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {V₁ V₂ : Y.Opens} {U₁ U₂ : X.Opens}
    {F₁ : (SheafOfModules.isQuasicoherent U₁.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf).FullSubcategory}
    {F₂ : (SheafOfModules.isQuasicoherent U₂.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf).FullSubcategory}
    (f₁ : V₁.toScheme ≅ U₁.toScheme) (f₂ : V₂.toScheme ≅ U₂.toScheme)
    (L₁ : SheafOfModules.{u} V₁.toScheme.ringCatSheaf)
    (L₂ : SheafOfModules.{u} V₂.toScheme.ringCatSheaf)
    (α₁ : E ⋙ quasicoherentRestriction V₁.ι ≅ quasicoherentRestriction U₁.ι ⋙ F₁)
    (β₁ : F₁ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₁.hom L₁)
    (α₂ : E ⋙ quasicoherentRestriction V₂.ι ≅ quasicoherentRestriction U₂.ι ⋙ F₂)
    (β₂ : F₂ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₂.hom L₂) :
    pullbackTensorFunctor
        (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ≫ f₁.hom ≫ U₁.ι)
        ((Scheme.Modules.pullback (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁))).obj L₁) ≅
      pullbackTensorFunctor
        (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ≫ f₂.hom ≫ U₂.ι)
        ((Scheme.Modules.pullback (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂))).obj L₂) :=
  (pullbackTensorFunctorIsoOfChartIso E f₁ L₁ α₁ β₁
      (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) (V₁ ⊓ V₂).ι _
      (Y.homOfLE_ι _) (Category.assoc _ _ _)).symm ≪≫
    pullbackTensorFunctorIsoOfChartIso E f₂ L₂ α₂ β₂
      (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) (V₁ ⊓ V₂).ι _
      (Y.homOfLE_ι _) (Category.assoc _ _ _)

/-! ### The images of the two chart maps -/

/-- **A morphism factoring through an open immersion lands in that open.**  If
`b = a ≫ U.ι` for an open `U` of `X`, then the image of `b` is contained in `U`.

This is the second hypothesis of
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` for the chart map
`b = (inclusion ≫ f.hom) ≫ U.ι`, which factors through `U.ι` by construction. -/
theorem range_subset_coe_of_comp_ι {X W : Scheme.{u}} {U : X.Opens} (a : W ⟶ U.toScheme)
    (b : W ⟶ X) (hb : a ≫ U.ι = b) : Set.range b ⊆ (U : Set X) := by
  subst hb
  rw [← Scheme.Opens.range_ι]
  rintro z ⟨x, rfl⟩
  exact ⟨a x, (Scheme.Hom.comp_apply _ _ _).symm⟩

/-- **Two open immersions with isomorphic inverse-image-and-tensor functors have the same
image.**  Let `W` be quasi-compact, let `S` be quasi-compact and quasi-separated, let
`g, g' : W ⟶ S` be open immersions and let `N`, `N'` be invertible sheaves of `𝒪_W`-modules with
`g^*(-) ⊗ N ≅ g'^*(-) ⊗ N'`.  Then `g` and `g'` have the same image.

`AlgebraicGeometry.range_subset_of_iso_pullbackTensorFunctor` transports containment of the
image in a quasi-compact open from one morphism to the other.  Because `g` is an open immersion
out of a quasi-compact scheme its own image *is* such an open, so applying that lemma to it
gives one containment, and applying it to `g'` gives the other. -/
theorem range_eq_of_iso_pullbackTensorFunctor {W S : Scheme.{u}} [CompactSpace W]
    [CompactSpace S] [QuasiSeparatedSpace S] (g g' : W ⟶ S) [IsOpenImmersion g]
    [IsOpenImmersion g'] (N N' : SheafOfModules.{u} W.ringCatSheaf)
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N]
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N']
    (θ : pullbackTensorFunctor g N ≅ pullbackTensorFunctor g' N') :
    Set.range g = Set.range g' := by
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · simpa using range_subset_of_iso_pullbackTensorFunctor g' g N' N θ.symm g'.opensRange
      (by simpa using isCompact_range g'.continuous) (by simp) hz
  · simpa using range_subset_of_iso_pullbackTensorFunctor g g' N N' θ g.opensRange
      (by simpa using isCompact_range g.continuous) (by simp) hz

/-- **On the overlap, the second chart map lands in the first chart's affine open.**  With the
chart data of two reconstruction charts and `X` quasi-compact and quasi-separated, the second
chart map read on `V₁ ⊓ V₂` has image inside `U₁`, provided `U₁` is quasi-compact.

The comparison isomorphism `AlgebraicGeometry.pullbackTensorFunctorOverlapIso` is fed to
`AlgebraicGeometry.range_subset_of_iso_pullbackTensorFunctor`; that the first chart map lands in
`U₁` is `AlgebraicGeometry.range_subset_coe_of_comp_ι`, and the restrictions of the `Lₐ` to the
overlap are invertible by [Stacks, Tag 0B8L]. -/
theorem range_subset_of_chartIso_overlap {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {V₁ V₂ : Y.Opens} {U₁ U₂ : X.Opens}
    {F₁ : (SheafOfModules.isQuasicoherent U₁.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf).FullSubcategory}
    {F₂ : (SheafOfModules.isQuasicoherent U₂.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf).FullSubcategory}
    (f₁ : V₁.toScheme ≅ U₁.toScheme) (f₂ : V₂.toScheme ≅ U₂.toScheme)
    (L₁ : SheafOfModules.{u} V₁.toScheme.ringCatSheaf)
    (L₂ : SheafOfModules.{u} V₂.toScheme.ringCatSheaf)
    [Stacks.SheafOfModules.IsInvertible V₁.toScheme.presheaf V₁.toScheme.ringCatSheaf.2 L₁]
    [Stacks.SheafOfModules.IsInvertible V₂.toScheme.presheaf V₂.toScheme.ringCatSheaf.2 L₂]
    (α₁ : E ⋙ quasicoherentRestriction V₁.ι ≅ quasicoherentRestriction U₁.ι ⋙ F₁)
    (β₁ : F₁ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₁.hom L₁)
    (α₂ : E ⋙ quasicoherentRestriction V₂.ι ≅ quasicoherentRestriction U₂.ι ⋙ F₂)
    (β₂ : F₂ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₂.hom L₂)
    (hU₁ : IsCompact (U₁ : Set X)) :
    Set.range (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ≫ f₂.hom ≫ U₂.ι) ⊆ (U₁ : Set X) := by
  have h₁ := @Stacks.RingedSpace.modulePullback_isInvertible _ _
    (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).toLRSHom.toShHom L₁ inferInstance
  have h₂ := @Stacks.RingedSpace.modulePullback_isInvertible _ _
    (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).toLRSHom.toShHom L₂ inferInstance
  exact range_subset_of_iso_pullbackTensorFunctor _ _ _ _
    (pullbackTensorFunctorOverlapIso E f₁ f₂ L₁ L₂ α₁ β₁ α₂ β₂) U₁ hU₁
    (range_subset_coe_of_comp_ι (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ≫ f₁.hom) _
      (Category.assoc _ _ _))

/-- **The two chart maps have the same image on the overlap.**  With the chart data of two
reconstruction charts, `X` quasi-compact and quasi-separated and the overlap `V₁ ⊓ V₂`
quasi-compact, the two chart maps read on `V₁ ⊓ V₂` have the same image in `X`.

This is the topological shadow of the overlap compatibility `hVcompat` of
`AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`, which asserts that
the two chart maps are *equal*; see the module documentation for what the equality still needs.
Both chart maps are open immersions, being a composite of an inclusion of opens, an isomorphism
and an inclusion of opens, so
`AlgebraicGeometry.range_eq_of_iso_pullbackTensorFunctor` applies to the comparison isomorphism
`AlgebraicGeometry.pullbackTensorFunctorOverlapIso`. -/
theorem range_eq_of_chartIso_overlap {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {V₁ V₂ : Y.Opens} {U₁ U₂ : X.Opens}
    {F₁ : (SheafOfModules.isQuasicoherent U₁.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf).FullSubcategory}
    {F₂ : (SheafOfModules.isQuasicoherent U₂.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf).FullSubcategory}
    (f₁ : V₁.toScheme ≅ U₁.toScheme) (f₂ : V₂.toScheme ≅ U₂.toScheme)
    (L₁ : SheafOfModules.{u} V₁.toScheme.ringCatSheaf)
    (L₂ : SheafOfModules.{u} V₂.toScheme.ringCatSheaf)
    [Stacks.SheafOfModules.IsInvertible V₁.toScheme.presheaf V₁.toScheme.ringCatSheaf.2 L₁]
    [Stacks.SheafOfModules.IsInvertible V₂.toScheme.presheaf V₂.toScheme.ringCatSheaf.2 L₂]
    (α₁ : E ⋙ quasicoherentRestriction V₁.ι ≅ quasicoherentRestriction U₁.ι ⋙ F₁)
    (β₁ : F₁ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₁.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₁.hom L₁)
    (α₂ : E ⋙ quasicoherentRestriction V₂.ι ≅ quasicoherentRestriction U₂.ι ⋙ F₂)
    (β₂ : F₂ ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V₂.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f₂.hom L₂)
    (hV : IsCompact ((V₁ ⊓ V₂ : Y.Opens) : Set Y)) :
    Set.range (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ≫ f₁.hom ≫ U₁.ι) =
      Set.range (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ≫ f₂.hom ≫ U₂.ι) := by
  have hW : CompactSpace (V₁ ⊓ V₂ : Y.Opens).toScheme := isCompact_iff_compactSpace.mp hV
  have h₁ := @Stacks.RingedSpace.modulePullback_isInvertible _ _
    (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).toLRSHom.toShHom L₁ inferInstance
  have h₂ := @Stacks.RingedSpace.modulePullback_isInvertible _ _
    (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).toLRSHom.toShHom L₂ inferInstance
  exact range_eq_of_iso_pullbackTensorFunctor _ _ _ _
    (pullbackTensorFunctorOverlapIso E f₁ f₂ L₁ L₂ α₁ β₁ α₂ β₂)

/-! ### The comparison for the reconstruction's own charts -/

/-- **The overlap comparison for the charts the reconstruction produces.**  Let `X` and `Y` be
quasi-compact and quasi-separated schemes, let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence and
let `U i` be an affine open cover of `X`.  Then there are opens `V i` covering `Y`, isomorphisms
`f i : V i ≅ U i` and invertible sheaves `L i` of `𝒪_{V i}`-modules such that for every pair
`i, j` the two chart maps read on `V i ⊓ V j` have isomorphic inverse-image-and-tensor functors
and the same image in `X`.

This is `AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover`
with the functors `F i` and the two per-chart isomorphisms consumed: what is left is exactly the
hypothesis of the rigidity theorem
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset`, stated over the overlap.
The isomorphism is `AlgebraicGeometry.pullbackTensorFunctorOverlapIso` and the equality of
images is `AlgebraicGeometry.range_eq_of_chartIso_overlap`; the overlap is quasi-compact because
the `V i` are and `Y` is quasi-separated. -/
theorem exists_iso_pullbackTensorFunctor_of_isAffineOpenCover {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {ι : Type u} (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    ∃ (V : ι → Y.Opens) (f : ∀ i, (V i).toScheme ≅ (U i).toScheme)
      (L : ∀ i, SheafOfModules.{u} (V i).toScheme.ringCatSheaf),
      IsOpenCover V ∧ (∀ i, IsAffineOpen (V i)) ∧
        (∀ i, Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
          (V i).toScheme.ringCatSheaf.2 (L i)) ∧
        (∀ i j, Nonempty (pullbackTensorFunctor
            (Y.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ (f i).hom ≫ (U i).ι)
            ((Scheme.Modules.pullback
              (Y.homOfLE (inf_le_left : V i ⊓ V j ≤ V i))).obj (L i)) ≅
          pullbackTensorFunctor
            (Y.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ (f j).hom ≫ (U j).ι)
            ((Scheme.Modules.pullback
              (Y.homOfLE (inf_le_right : V i ⊓ V j ≤ V j))).obj (L j)))) ∧
        ∀ i j, Set.range (Y.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ (f i).hom ≫ (U i).ι) =
          Set.range (Y.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ (f j).hom ≫ (U j).ι) := by
  obtain ⟨V, hVcover, hV⟩ :=
    exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover e U hUaff hUcover
  choose hVaff hVc F f L hFequiv hLinv hα hβ using hV
  refine ⟨V, f, L, hVcover, hVaff, hLinv, fun i j => ⟨?_⟩, fun i j => ?_⟩
  · exact pullbackTensorFunctorOverlapIso e.functor (f i) (f j) (L i) (L j)
      (hα i).some (hβ i).some (hα j).some (hβ j).some
  · have := hLinv i
    have := hLinv j
    exact range_eq_of_chartIso_overlap e.functor (f i) (f j) (L i) (L j)
      (hα i).some (hβ i).some (hα j).some (hβ j).some
      ((hVc i).inter_of_isOpen (hVc j) (V i).2 (V j).2)

end AlgebraicGeometry

end
