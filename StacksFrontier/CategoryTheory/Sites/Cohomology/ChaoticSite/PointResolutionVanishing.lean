module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.KProjectiveLeftDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionCofinality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionProjectivity

/-!
# The derived colimit of a diagram projective along a point resolution has no higher terms

Let `C` be a small category carrying the chaotic topology and let `D` be an abelian category with
coproducts indexed by the morphism universe of `C` and enough projectives, so that `π_!` is the
colimit over `Cᵒᵖ` and `Lπ_!` is its total left derived functor
(`Stacks.CategoryHomology.totalDerivedColimit`). Let `U_•` be a cosimplicial object of `C` which
is a point resolution in the sense of `Stacks.ChaoticSite.IsPointResolution`, and let `Z` be a
diagram `Cᵒᵖ ⥤ D` whose restriction `U.op ⋙ Z` along the point resolution is a **projective**
simplicial object of `D`. This file proves `L_nπ_!(Z) = 0` for `n > 0`, in the form the rest of
[Stacks, Tag 08QA] needs it: the comparison `Lπ_!(Z) ⟶ π_!(Z)` of the left derived functor is
invertible at `Z` placed in degree zero.

The mechanism is the one of `Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective`: the
comparison of a total left derived functor is invertible at a K-projective complex, so it suffices
to compare `Z` in degree zero with a projective resolution `R` of `Z`, which is K-projective. The
comparison transformation is natural, and `R.π' : R.cochainComplex ⟶ Z[0]` becomes invertible in
the derived category because it is a quasi-isomorphism; so all that is left is that `π_!` itself —
the colimit over `Cᵒᵖ` applied degreewise — carries `R.π'` to a quasi-isomorphism. That is the one
place where the hypothesis on `Z` is used, and it is *not* automatic: the colimit over `Cᵒᵖ` is
only right exact, so a projective resolution need not stay a resolution after applying it.

What makes it true is that the colimit over `Cᵒᵖ` is computed by the colimit over
`SimplexCategoryᵒᵖ` of the restriction along `U.op`
(`Stacks.ChaoticSite.isIso_colimitPre_of_isPointResolution`, a point resolution being an initial
functor), that restriction along `U.op` preserves projective objects
(`Stacks.ChaoticSite.preservesProjectiveObjects_restrictAlongPointResolution`) and is exact, and
that `U.op ⋙ Z` is assumed projective. So after restricting, both `R.cochainComplex` and `Z[0]`
become K-projective complexes, and a quasi-isomorphism between K-projective complexes is a
*homotopy equivalence* (`CochainComplex.IsKProjective.quasiIso_iff`); homotopy equivalences are
preserved by any additive functor applied degreewise, hence by the colimit over
`SimplexCategoryᵒᵖ`, and a homotopy equivalence is a quasi-isomorphism.

## Main definitions

* `Stacks.ChaoticSite.colimitPointResolutionPre`: the comparison
  `(U.op ⋙ -) ⋙ colim_{Δᵒᵖ} ⟶ colim_{Cᵒᵖ}`, with component `Limits.colimit.pre G U.op`.
* `Stacks.ChaoticSite.colimitPointResolutionPreNatIso`: that comparison is an isomorphism of
  functors, for a point resolution.

## Main results

* `Stacks.Homology.isIso_leftDerivedCounit_app_of_isIso_map`: the comparison of a total left
  derived functor is invertible at any object of the homotopy category which is related to a
  K-projective complex by a morphism that both the localization and the underived functor invert.
* `Stacks.ChaoticSite.isKProjective_restrict_single_of_projective`: `Z[0]` restricted along a
  point resolution is K-projective when `U.op ⋙ Z` is projective.
* `Stacks.ChaoticSite.quasiIso_colimMap_of_isKProjective_restrict`: the colimit over `Cᵒᵖ`,
  applied degreewise, carries a quasi-isomorphism whose two ends restrict to K-projective
  complexes to a quasi-isomorphism.
* `Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_projective_restrict`:
  `Lπ_!(Z) = π_!(Z)`, with no higher terms, at such a `Z`.

## Implementation notes

`Stacks.CategoryHomology.diagramColimitRestrictionPre` is the same comparison as
`Stacks.ChaoticSite.colimitPointResolutionPre` but stated at `f.op` for a functor `f : C' ⥤ C` of
index categories, which does not cover `U.op : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ`; so the transformation is
declared again here rather than specialised, its naturality being
`CategoryTheory.Limits.colimit.pre_map` in both cases.

The transport of a quasi-isomorphism from `colim_{Δᵒᵖ} ∘ (U.op ⋙ -)` to `colim_{Cᵒᵖ}` is done on
the morphism property `HomologicalComplex.quasiIso`, which respects isomorphisms of arrows: the
isomorphism of arrows is the naturality square of the degreewise comparison
`CategoryTheory.Functor.mapHomologicalComplexCompIso`. Going through the property rather than
through the `QuasiIso` class spares rewriting under `Functor.map`, which is where
`not type-correct` appears.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

universe uD u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Homology

/-! ### Two general facts about left derived functors on the homotopy category -/

section General

variable {A : Type*} [Category* A] [Abelian A]

omit [Abelian A] in
/-- **A functor preserving zero morphisms carries a strictly bounded above complex to a strictly
bounded above complex**, the degreewise image of a zero object being a zero object. -/
theorem isStrictlyLE_mapHomologicalComplex {B : Type*} [Category* B] [Preadditive A]
    [HasZeroObject A] [Preadditive B] [HasZeroObject B] (F : A ⥤ B)
    [F.PreservesZeroMorphisms] (K : CochainComplex A ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
  (CochainComplex.isStrictlyLE_iff
    (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n).2 fun i hi =>
      F.map_isZero (K.isZero_of_isStrictlyLE n i hi)

variable [HasDerivedCategory A]

/-- **A quasi-isomorphism of cochain complexes becomes invertible in the derived category, read
through the homotopy category.** This is the invertibility of `DerivedCategory.Q.map` on
quasi-isomorphisms conjugated by `DerivedCategory.quotientCompQhIso`. -/
theorem isIso_Qh_map_quotient_map_of_quasiIso {K L : CochainComplex A ℤ} (f : K ⟶ L)
    [QuasiIso f] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)) := by
  have h : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app L =
      (DerivedCategory.quotientCompQhIso A).hom.app K ≫ DerivedCategory.Q.map f :=
    DerivedCategory.quotientCompQhIso_hom_naturality f
  exact IsIso.of_isIso_fac_right h

/-- **The comparison of a total left derived functor is invertible wherever a K-projective complex
can be moved to.** Let `u : P ⟶ X` be a morphism of the homotopy category out of (the image of) a
K-projective complex `P` which the localization `DerivedCategory.Qh` inverts and which the
underived functor `G` inverts. Then the comparison `α : Qh ⋙ LG ⟶ G` is invertible at `X`.

By naturality `α.app X` is the composite of `(Qh ⋙ LG).map u` inverted, the comparison at `P` —
invertible by `Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective` — and `G.map u`. This
is how a derived functor is computed at an object that is not itself a complex of projectives: at
a projective resolution of it. -/
theorem isIso_leftDerivedCounit_app_of_isIso_map {E : Type*} [Category* E]
    {G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ E}
    (LG : DerivedCategory A ⥤ E) (α : DerivedCategory.Qh ⋙ LG ⟶ G)
    [LG.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [G.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {P : CochainComplex A ℤ} [P.IsKProjective]
    {X : HomotopyCategory A (ComplexShape.up ℤ)}
    (u : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶ X)
    (hu : IsIso (DerivedCategory.Qh.map u)) (hG : IsIso (G.map u)) :
    IsIso (α.app X) := by
  have := hu
  have := hG
  have := isIso_leftDerivedCounit_app_of_isKProjective LG α P
  have : IsIso ((DerivedCategory.Qh ⋙ LG).map u) :=
    show IsIso (LG.map (DerivedCategory.Qh.map u)) from inferInstance
  exact IsIso.of_isIso_fac_left (α.naturality u)

end General

end Stacks.Homology

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] (D : Type uD) [Category.{u} D] [Abelian D]
  [HasCoproducts.{u} D] [EnoughProjectives D] [EnoughProjectives (Cᵒᵖ ⥤ D)]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape SimplexCategoryᵒᵖ D]

/-! ### The colimit over a point resolution computes the colimit over the site -/

/-- The canonical comparison from the colimit over `SimplexCategoryᵒᵖ` of the restriction of a
diagram along a cosimplicial object `U_•` to the colimit of the diagram over `Cᵒᵖ`, as a natural
transformation `(U.op ⋙ -) ⋙ colim_{Δᵒᵖ} ⟶ colim_{Cᵒᵖ}`. Degreewise it is
`CategoryTheory.Limits.colimit.pre`, whose naturality is
`CategoryTheory.Limits.colimit.pre_map`.

`Stacks.CategoryHomology.diagramColimitRestrictionPre` is the same transformation stated at `f.op`
for a functor `f : C' ⥤ C` between index categories, which does not cover `U.op`. -/
def colimitPointResolutionPre (U : CosimplicialObject C) :
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op ⋙
        (colim : (SimplexCategoryᵒᵖ ⥤ D) ⥤ D) ⟶
      (colim : (Cᵒᵖ ⥤ D) ⥤ D) where
  app G := colimit.pre G U.op
  naturality _ _ α := (colimit.pre_map α U.op).symm

/-- **The colimit over `Cᵒᵖ` is the colimit over `Δᵒᵖ` of the restriction along a point
resolution**, as an isomorphism of functors. This is
`Stacks.ChaoticSite.isIso_colimitPre_of_isPointResolution`, which says that a point resolution is
a final functor to `Cᵒᵖ`, read on `Stacks.ChaoticSite.colimitPointResolutionPre`. -/
def colimitPointResolutionPreNatIso {U : CosimplicialObject C} (hU : IsPointResolution U) :
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op ⋙
        (colim : (SimplexCategoryᵒᵖ ⥤ D) ⥤ D) ≅
      (colim : (Cᵒᵖ ⥤ D) ⥤ D) :=
  haveI : IsIso (colimitPointResolutionPre D U) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun G =>
      isIso_colimitPre_of_isPointResolution hU D G
  asIso (colimitPointResolutionPre D U)

/-! ### K-projectivity after restricting along a point resolution -/

section Restriction

variable {U : CosimplicialObject C} (hU : IsPointResolution U)

omit [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape SimplexCategoryᵒᵖ D] in
include hU in
/-- **A complex of projective diagrams bounded above restricts to a K-projective complex along a
point resolution.** Restriction along `U.op` preserves projective objects
(`Stacks.ChaoticSite.preservesProjectiveObjects_restrictAlongPointResolution`) and is additive, so
the restricted complex is a strictly bounded above complex of projective objects, and
`CochainComplex.isKProjective_of_projective` applies. -/
theorem isKProjective_restrict_of_projective (K : CochainComplex (Cᵒᵖ ⥤ D) ℤ) (n : ℤ)
    [K.IsStrictlyLE n] [∀ i : ℤ, Projective (K.X i)] :
    CochainComplex.IsKProjective
      ((((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) := by
  have := preservesProjectiveObjects_restrictAlongPointResolution (D := D) hU
  have := Stacks.Homology.isStrictlyLE_mapHomologicalComplex
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op) K n
  have : ∀ i : ℤ, Projective (((((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj
      U.op).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X i) := fun i =>
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).projective_obj_of_projective
      (inferInstanceAs (Projective (K.X i)))
  exact CochainComplex.isKProjective_of_projective _ n

omit [HasCoproducts D] [EnoughProjectives D] [EnoughProjectives (Cᵒᵖ ⥤ D)]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape SimplexCategoryᵒᵖ D] in
include hU in
/-- **A diagram whose restriction along a point resolution is projective has a K-projective
restriction in degree zero.** The restriction of `Z[0]` is `(U.op ⋙ Z)[0]` by
`HomologicalComplex.singleMapHomologicalComplex`, which is K-projective by
`Stacks.Homology.isKProjective_single`. -/
theorem isKProjective_restrict_single_of_projective (Z : Cᵒᵖ ⥤ D)
    (hZ : Projective (U.op ⋙ Z)) :
    CochainComplex.IsKProjective
      ((((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj Z)) := by
  have := hZ
  have : CochainComplex.IsKProjective
      (((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op ⋙
        HomologicalComplex.single (SimplexCategoryᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj Z) :=
    Stacks.Homology.isKProjective_single (U.op ⋙ Z)
  exact CochainComplex.isKProjective_of_iso
    ((HomologicalComplex.singleMapHomologicalComplex
      ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op)
        (ComplexShape.up ℤ) 0).app Z).symm

omit [HasCoproducts D] [EnoughProjectives D] [EnoughProjectives (Cᵒᵖ ⥤ D)]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D] in
include hU in
/-- **The colimit over `Cᵒᵖ` applied degreewise preserves a quasi-isomorphism whose two ends are
K-projective after restricting along a point resolution.** This is the one step of the vanishing
that is not formal.

Restriction along `U.op` is exact, being precomposition, so it carries the quasi-isomorphism `f`
to a quasi-isomorphism; between K-projective complexes a quasi-isomorphism is a homotopy
equivalence (`CochainComplex.IsKProjective.quasiIso_iff`); an additive functor applied degreewise
preserves homotopy equivalences (`CategoryTheory.Functor.mapHomotopyEquiv`), so the colimit over
`SimplexCategoryᵒᵖ` does, and a homotopy equivalence is a quasi-isomorphism. Finally
`Stacks.ChaoticSite.colimitPointResolutionPreNatIso` identifies that composite with the colimit
over `Cᵒᵖ`, and `HomologicalComplex.quasiIso` respects isomorphisms of arrows. -/
theorem quasiIso_colimMap_of_isKProjective_restrict
    {K L : CochainComplex (Cᵒᵖ ⥤ D) ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : CochainComplex.IsKProjective
      ((((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))
    (hL : CochainComplex.IsKProjective
      ((((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)) :
    QuasiIso (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have := hK
  have := hL
  -- the restriction of `f` is a homotopy equivalence
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff
    ((((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)).1 inferInstance
  -- hence so is its image under the colimit over `Δᵒᵖ`
  have hq : HomologicalComplex.quasiIso D (ComplexShape.up ℤ)
      (((((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙
        ((colim : (SimplexCategoryᵒᵖ ⥤ D) ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) :=
    _root_.homotopyEquivalences_le_quasiIso _ _ _
      ⟨(colim : (SimplexCategoryᵒᵖ ⥤ D) ⥤ D).mapHomotopyEquiv e, by simp [he]⟩
  -- and the comparison with the colimit over `Cᵒᵖ` is an isomorphism of arrows
  let η := Functor.mapHomologicalComplexCompIso
    (colimitPointResolutionPreNatIso D hU) (ComplexShape.up ℤ)
  exact (MorphismProperty.arrow_mk_iso_iff (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (Arrow.isoMk (η.app K) (η.app L) (η.hom.naturality f).symm)).1 hq

end Restriction

/-! ### The vanishing -/

/-- **`L_nπ_!(Z) = 0` for `n > 0` at a diagram projective along a point resolution**, in the form
[Stacks, Tag 08QA] needs it: the comparison of the total left derived functor
`Stacks.CategoryHomology.totalDerivedColimit` with the colimit itself is invertible at `Z` placed
in degree zero, that is `Lπ_!(Z) = π_!(Z)` with no higher terms.

Take a projective resolution `R` of `Z`. Its associated cochain complex is K-projective, so the
comparison is invertible there (`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective`),
and `Stacks.Homology.isIso_leftDerivedCounit_app_of_isIso_map` moves that along `R.π'`: the
localization inverts `R.π'` because it is a quasi-isomorphism, and the colimit over `Cᵒᵖ` applied
degreewise inverts it by `Stacks.ChaoticSite.quasiIso_colimMap_of_isKProjective_restrict`, whose
two K-projectivity hypotheses are the two previous lemmas. -/
theorem isIso_totalDerivedColimitCounit_single_of_projective_restrict
    {U : CosimplicialObject C} (hU : IsPointResolution U) (Z : Cᵒᵖ ⥤ D)
    (hZ : Projective (U.op ⋙ Z)) :
    IsIso ((Stacks.CategoryHomology.totalDerivedColimitCounit C D).app
      ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj Z))) := by
  have := Stacks.CategoryHomology.colim_hasPointwiseLeftDerivedFunctor C D
  have := Stacks.CategoryHomology.totalDerivedColimit_isLeftDerivedFunctor C D
  have : CochainComplex.IsKProjective (ProjectiveResolution.of Z).cochainComplex :=
    CochainComplex.isKProjective_of_projective _ 0
  have : QuasiIso (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (ProjectiveResolution.of Z).π') :=
    quasiIso_colimMap_of_isKProjective_restrict D hU _
      (isKProjective_restrict_of_projective D hU (ProjectiveResolution.of Z).cochainComplex 0)
      (isKProjective_restrict_single_of_projective D hU Z hZ)
  refine Stacks.Homology.isIso_leftDerivedCounit_app_of_isIso_map
    (P := (ProjectiveResolution.of Z).cochainComplex)
    (Stacks.CategoryHomology.totalDerivedColimit C D)
    (Stacks.CategoryHomology.totalDerivedColimitCounit C D)
    ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
      (ProjectiveResolution.of Z).π') ?_ ?_
  · exact Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso _
  · exact Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso
      (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ProjectiveResolution.of Z).π')

end Stacks.ChaoticSite

end
