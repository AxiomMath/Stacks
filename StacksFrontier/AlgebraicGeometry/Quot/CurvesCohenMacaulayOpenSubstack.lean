module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodalUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackFromBaseLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The open substack of Cohen–Macaulay curves

The open substack `Curves^{CM} ⊂ Curves` of families of curves whose structure morphism is
Cohen–Macaulay, cut out by the Cohen–Macaulay locus in the base of a family of curves, together
with the characterisation of its objects: for a family of curves `X → S` the classifying morphism
`S → Curves` factors through `Curves^{CM}` exactly when `X → S` is Cohen–Macaulay, and for a
scheme `X` proper over a field `k` with `dim(X) ≤ 1` the classifying morphism `Spec(k) → Curves`
factors through `Curves^{CM}` exactly when `X` is Cohen–Macaulay.

The open substack of an algebraic stack is formed inside an arbitrary algebraic stack `𝒳`
identified, over the big fppf site of the integers, with the category of families of curves; the
remaining statements are made for the fibred category of families of curves itself.

## Main definitions

* `AlgebraicGeometry.CurveFamily.cohenMacaulayBaseOpenSubspace`: the Cohen–Macaulay locus in
  the base of a family of curves, as an open subspace of the base.
* `AlgebraicGeometry.cohenMacaulayCurvesOpenSubstack`: the open substack `Curves^{CM}` of an
  algebraic stack identified with families of curves, together with the characterisation of its
  objects.
* `AlgebraicGeometry.cohenMacaulayCurvesFibered` and
  `AlgebraicGeometry.cohenMacaulayCurvesInclusion`: the subcategory `Curves^{CM}` of the category
  of families of curves and the inclusion `Curves^{CM} ⊂ Curves`.

## Main results

* `AlgebraicGeometry.Space.isCohenMacaulay_iff_cohenMacaulayBaseLocus_eq_univ`: a morphism of
  algebraic spaces is Cohen–Macaulay exactly when its Cohen–Macaulay locus in the base is the
  whole base.
* `AlgebraicGeometry.CurveFamily.exists_cohenMacaulay_baseOpen`: a family of curves mapping to a
  fixed family is Cohen–Macaulay exactly when its morphism of base schemes factors through an
  open subspace of the base of that fixed family.
* `AlgebraicGeometry.classifying_factors_cohenMacaulayCurvesOpenSubstack_iff`: the classifying
  object of a family of curves lies in `Curves^{CM}` exactly when the family is Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulayFamily_curveFamilyOfSchemeMorphism_iff` and
  `AlgebraicGeometry.classifying_factors_cohenMacaulayCurvesOpenSubstack_iff_of_field`: the
  family of curves of a scheme proper over a field with dimension at most one is Cohen–Macaulay,
  equivalently its classifying object lies in `Curves^{CM}`, exactly when the scheme is
  Cohen–Macaulay.
* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_cohenMacaulayCurvesInclusion`,
  `AlgebraicGeometry.isOpenImmersion_cohenMacaulayCurvesInclusion` and
  `AlgebraicGeometry.isOpenSubstack_cohenMacaulayCurves`: `Curves^{CM}` is a strictly full
  subcategory of `Curves` inherited along morphisms of families, and its inclusion is
  representable by algebraic spaces and by open immersions.
* `AlgebraicGeometry.lifts_cohenMacaulayCurves_iff`,
  `AlgebraicGeometry.lifts_cohenMacaulayCurvesInclusion_iff` and
  `AlgebraicGeometry.lifts_cohenMacaulayCurves_iff_of_field`: the characterisation of the objects
  of `Curves^{CM}` over the category of families of curves.
* `AlgebraicGeometry.full_cohenMacaulayCurvesInclusion` and
  `AlgebraicGeometry.faithful_cohenMacaulayCurvesInclusion`: the inclusion
  `Curves^{CM} ⊂ Curves` is fully faithful.

## References

* [Stacks Project, Tag 0E0I](https://stacks.math.columbia.edu/tag/0E0I)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0D5B](https://stacks.math.columbia.edu/tag/0D5B)
* [Stacks Project, Tag 0E10](https://stacks.math.columbia.edu/tag/0E10)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The Cohen–Macaulay locus in the base as an open subspace -/

/-- A morphism of algebraic spaces over `S` is Cohen–Macaulay exactly when its Cohen–Macaulay
locus in the target is the whole target. -/
theorem Space.isCohenMacaulay_iff_cohenMacaulayBaseLocus_eq_univ (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Space.IsCohenMacaulay B S hS f ↔
      Space.cohenMacaulayBaseLocus B S hS f = Set.univ :=
  ⟨fun hf => Set.eq_univ_of_forall fun _ x _ => hf x,
    fun hf x => Set.eq_univ_iff_forall.mp hf (Space.pointsMap B S hS X f x) x rfl⟩

/-- The Cohen–Macaulay locus in the base of a family of curves, as the subspace of the algebraic
space of the base scheme with that point set. -/
def CurveFamily.cohenMacaulayBaseOpenSubspace (X : CurveFamily B hZ) :
    Subfunctor (schemeSpace X.base).obj :=
  Space.openSubspaceOfPoints B integerBase hZ (schemeSpace X.base).obj
    (Space.cohenMacaulayBaseLocus B integerBase hZ X.toBase.hom)

/-- `AlgebraicGeometry.CurveFamily.cohenMacaulayBaseOpenSubspace` is an open subspace of the
algebraic space of the base scheme. -/
theorem CurveFamily.isOpenSubspace_cohenMacaulayBaseOpenSubspace (X : CurveFamily B hZ) :
    Space.IsOpenSubspace B integerBase hZ (CurveFamily.cohenMacaulayBaseOpenSubspace B hZ X) :=
  Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ (schemeSpace X.base).property _
    (CurveFamily.isOpen_cohenMacaulayBaseLocus B hZ X)

/-- The point set of `AlgebraicGeometry.CurveFamily.cohenMacaulayBaseOpenSubspace` is the
Cohen–Macaulay locus in the base. -/
theorem CurveFamily.range_pointsMap_cohenMacaulayBaseOpenSubspace (X : CurveFamily B hZ) :
    Set.range (Space.pointsMap B integerBase hZ
        (CurveFamily.cohenMacaulayBaseOpenSubspace B hZ X).toFunctor
        (CurveFamily.cohenMacaulayBaseOpenSubspace B hZ X).ι) =
      Space.cohenMacaulayBaseLocus B integerBase hZ X.toBase.hom :=
  Space.range_pointsMap_ι_openSubspaceOfPoints B integerBase hZ _

/-- For a family of curves `G` there is an open subspace of the algebraic space of its base
through which the morphism of base schemes of a family of curves `F ⟶ G` factors exactly when
`F` is Cohen–Macaulay. -/
theorem CurveFamily.exists_cohenMacaulay_baseOpen (G : CurveFamily B hZ) :
    ∃ W : Subfunctor (schemeSpace G.base).obj,
      Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        IsCohenMacaulayFamily B hZ F ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom := by
  refine ⟨CurveFamily.cohenMacaulayBaseOpenSubspace B hZ G,
    CurveFamily.isOpenSubspace_cohenMacaulayBaseOpenSubspace B hZ G, fun F a => ?_⟩
  rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property _
      (CurveFamily.isOpenSubspace_cohenMacaulayBaseOpenSubspace B hZ G),
    CurveFamily.range_pointsMap_cohenMacaulayBaseOpenSubspace B hZ G,
    ← Set.preimage_eq_univ_iff, CurveFamily.preimage_cohenMacaulayBaseLocus B hZ a]
  exact Space.isCohenMacaulay_iff_cohenMacaulayBaseLocus_eq_univ B integerBase hZ F.toBase.hom

/-! ### The open substack of an algebraic stack of curves -/

/-- The open substack `Curves^{CM}` of `𝒳` of families of curves whose structure morphism is
Cohen–Macaulay, together with the characterisation of its objects: the object of `𝒳` attached to
a family of curves by `E` belongs to it exactly when the family is Cohen–Macaulay.

The algebraic stack of curves is a hypothesis: `𝒳` is any algebraic stack over the big fppf site
of the integers whose objects are identified with families of curves by an equivalence `E` over
that site. -/
@[no_expose]
def cohenMacaulayCurvesOpenSubstack
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) :
    {U : Stack.OpenSubstack 𝒳 //
      ∀ F : CurveFamily B hZ,
        U.property (E.functor.obj F) ↔ IsCohenMacaulayFamily B hZ F} :=
  curvesOpenSubstackOfBaseLocus B hZ (fun F => IsCohenMacaulayFamily B hZ F)
    (fun a hG => CurveFamily.isCohenMacaulayFamily_of_hom B hZ a hG)
    (CurveFamily.exists_cohenMacaulay_baseOpen B hZ) 𝒳 E hE

/-- The classifying object of a family of curves lifts through the inclusion of the open substack
`AlgebraicGeometry.cohenMacaulayCurvesOpenSubstack` exactly when the family is Cohen–Macaulay.
The algebraic stack `𝒳` of curves and its identification `E` with families of curves are
hypotheses. -/
theorem classifying_factors_cohenMacaulayCurvesOpenSubstack_iff
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (F : CurveFamily B hZ) :
    (∃ Y : (cohenMacaulayCurvesOpenSubstack B hZ 𝒳 E hE).1.property.FullSubcategory,
      Y.obj = E.functor.obj F) ↔ IsCohenMacaulayFamily B hZ F := by
  have hchar := (cohenMacaulayCurvesOpenSubstack B hZ 𝒳 E hE).2 F
  exact ⟨fun ⟨Y, hY⟩ => hchar.mp (hY ▸ Y.property), fun hN => ⟨⟨_, hchar.mpr hN⟩, rfl⟩⟩

/-! ### Schemes proper over a field -/

/-- The family of curves attached to a proper morphism of schemes onto the spectrum of a field,
whose source has dimension at most one, is Cohen–Macaulay exactly when that source scheme is
Cohen–Macaulay.

It takes the hypotheses of `AlgebraicGeometry.curveFamilyOfSchemeMorphism`: besides properness
and `dim ≤ 1`, flatness and local finite presentation of the morphism of schemes, and
quasi-compactness, separatedness and quasi-separatedness of the induced morphism of algebraic
spaces. -/
theorem isCohenMacaulayFamily_curveFamilyOfSchemeMorphism_iff
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k)) :
    IsCohenMacaulayFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
  have _ : Flat ((BigFppfOver.toScheme B integerBase hZ).map g) := hflat
  have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g) := hlfp
  exact isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec B hZ g k hU fun v =>
    inferInstanceAs (IsLocallyNoetherian
      (pullback ((BigFppfOver.toScheme B integerBase hZ).map g)
        (((BigFppfOver.toScheme B integerBase hZ).obj U).fromSpecResidueField v)))

/-- For a scheme proper over a field with dimension at most one, the classifying object of the
family of curves it defines lifts through the inclusion of the open substack
`AlgebraicGeometry.cohenMacaulayCurvesOpenSubstack` exactly when that scheme is Cohen–Macaulay.

The algebraic stack `𝒳` of curves and its identification `E` with families of curves are
hypotheses, and so are those of `AlgebraicGeometry.curveFamilyOfSchemeMorphism` beyond
properness and `dim ≤ 1`. -/
theorem classifying_factors_cohenMacaulayCurvesOpenSubstack_iff_of_field
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k)) :
    (∃ Y : (cohenMacaulayCurvesOpenSubstack B hZ 𝒳 E hE).1.property.FullSubcategory,
        Y.obj = E.functor.obj
          (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim)) ↔
      IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
  (classifying_factors_cohenMacaulayCurvesOpenSubstack_iff B hZ 𝒳 E hE _).trans
    (isCohenMacaulayFamily_curveFamilyOfSchemeMorphism_iff B hZ g hflat hproper hlfp hqc hsep
      hqsep hdim k hU)

/-! ### The open substack over the category of families of curves -/

/-- `Curves^{CM}`, the subcategory of families of curves whose structure morphism is
Cohen–Macaulay, as a category fibred in groupoids over the big fppf site of `Spec(ℤ)`. -/
@[no_expose]
def cohenMacaulayCurvesFibered :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesFullSubcategoryFibered B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    fun a hG => CurveFamily.isCohenMacaulayFamily_of_hom B hZ a hG

/-- The inclusion `Curves^{CM} ⊂ Curves`, as a 1-morphism of categories fibred in groupoids over
the big fppf site of `Spec(ℤ)`. -/
@[no_expose]
def cohenMacaulayCurvesInclusion :
    cohenMacaulayCurvesFibered B hZ ⟶ curvesFiberedCategory B hZ :=
  curvesFullSubcategoryInclusion B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    fun a hG => CurveFamily.isCohenMacaulayFamily_of_hom B hZ a hG

/-- The inclusion `Curves^{CM} ⊂ Curves` is full. -/
theorem full_cohenMacaulayCurvesInclusion :
    (cohenMacaulayCurvesInclusion B hZ).hom.toFunctor.Full :=
  full_curvesFullSubcategoryInclusion B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    (CurveFamily.isCohenMacaulayFamily_of_hom B hZ)

/-- The inclusion `Curves^{CM} ⊂ Curves` is faithful. -/
theorem faithful_cohenMacaulayCurvesInclusion :
    (cohenMacaulayCurvesInclusion B hZ).hom.toFunctor.Faithful :=
  faithful_curvesFullSubcategoryInclusion B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    (CurveFamily.isCohenMacaulayFamily_of_hom B hZ)

/-- The inclusion `Curves^{CM} ⊂ Curves` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_cohenMacaulayCurvesInclusion :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (cohenMacaulayCurvesInclusion B hZ).hom :=
  isRepresentableByAlgebraicSpaces_curvesFullSubcategoryInclusion B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    (CurveFamily.isCohenMacaulayFamily_of_hom B hZ)
    (CurveFamily.exists_cohenMacaulay_baseOpen B hZ)

/-- The inclusion `Curves^{CM} ⊂ Curves` is an open immersion: every algebraic space representing
one of its base changes along a scheme-valued point of `Curves` has open immersion structural
morphism. -/
theorem isOpenImmersion_cohenMacaulayCurvesInclusion :
    Stack.IsOpenImmersion B integerBase hZ (cohenMacaulayCurvesInclusion B hZ) :=
  isOpenImmersion_curvesFullSubcategoryInclusion B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    (CurveFamily.isCohenMacaulayFamily_of_hom B hZ)
    (CurveFamily.exists_cohenMacaulay_baseOpen B hZ)

/-- The Cohen–Macaulay condition cuts a strictly full subcategory out of the category of families
of curves which is inherited along every morphism of families of curves, and the inclusion of
that subcategory is representable by algebraic spaces and by open immersions. -/
theorem isOpenSubstack_cohenMacaulayCurves :
    (show ObjectProperty (CurveFamily B hZ) from
        IsCohenMacaulayFamily B hZ).IsClosedUnderIsomorphisms ∧
      (∀ F G : CurveFamily B hZ, (F ⟶ G) →
        IsCohenMacaulayFamily B hZ G → IsCohenMacaulayFamily B hZ F) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (cohenMacaulayCurvesInclusion B hZ).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (cohenMacaulayCurvesInclusion B hZ) :=
  ⟨curvesCM_isStrictlyFull B hZ,
    fun _ _ => CurveFamily.isCohenMacaulayFamily_of_hom B hZ,
    isRepresentableByAlgebraicSpaces_cohenMacaulayCurvesInclusion B hZ,
    isOpenImmersion_cohenMacaulayCurvesInclusion B hZ⟩

/-- A family of curves lifts to `AlgebraicGeometry.CurvesCM` exactly when it is Cohen–Macaulay. -/
theorem lifts_cohenMacaulayCurves_iff (F : CurveFamily B hZ) :
    (∃ Y : CurvesCM B hZ, Y.obj = F) ↔ IsCohenMacaulayFamily B hZ F :=
  lifts_curvesFullSubcategory_iff B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ) F

/-- A family of curves lies in the image on objects of the 1-morphism
`AlgebraicGeometry.cohenMacaulayCurvesInclusion` exactly when it is Cohen–Macaulay. -/
theorem lifts_cohenMacaulayCurvesInclusion_iff (F : CurveFamily B hZ) :
    (∃ Y : (cohenMacaulayCurvesFibered B hZ).based.obj,
        (CatFiberedInGroupoids.homFunctor (cohenMacaulayCurvesInclusion B hZ)).obj Y = F) ↔
      IsCohenMacaulayFamily B hZ F :=
  lifts_curvesFullSubcategoryInclusion_iff B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    (CurveFamily.isCohenMacaulayFamily_of_hom B hZ) F

/-- For a scheme proper over a field with dimension at most one, the family of curves it defines
lifts to `AlgebraicGeometry.CurvesCM` exactly when that scheme is Cohen–Macaulay.

It takes the hypotheses of `AlgebraicGeometry.curveFamilyOfSchemeMorphism` beyond properness
and `dim ≤ 1`: flatness and local finite presentation of the morphism of schemes, and
quasi-compactness, separatedness and quasi-separatedness of the induced morphism of algebraic
spaces. -/
theorem lifts_cohenMacaulayCurves_iff_of_field
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k)) :
    (∃ Y : CurvesCM B hZ,
        Y.obj = curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
  (lifts_cohenMacaulayCurves_iff B hZ _).trans
    (isCohenMacaulayFamily_curveFamilyOfSchemeMorphism_iff B hZ g hflat hproper hlfp hqc hsep
      hqsep hdim k hU)

end AlgebraicGeometry

end
