module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeDirectImageAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# The direct image of the structure sheaf of the relative spectrum is the algebra

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site and let `ν : X' = \underline{Spec}_X(A) ⟶ X` be the
relative spectrum `AlgebraicGeometry.Space.chartRelativeSpecQuotient`, the quotient of the
relation of a pair `pr₁, pr₂ : V' ⟶ V₂` of étale charts with `V₂ ⟶ X` surjective.

This file constructs an isomorphism `A ≅ ν_* 𝒪_{X'}` of sheaves of commutative rings, and then of
sheaves of commutative `𝒪_X`-algebras, on the small étale site of `X`.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecSectionsFunctorIso`: the sections of `A` over the
  charts over `V₂` are, naturally, the global sections of the relative spectra of `A` over those
  charts.
* `AlgebraicGeometry.Space.chartRelativeSpecQuotientRestrictionRingIso`: the isomorphism
  `A ≅ ν_* 𝒪_{X'}` of the restrictions of the two sheaves of commutative rings to the charts
  over `V₂`.
* `AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecSectionsMap`: pullback of regular
  functions along the comparison of charts of `X'` at a chart over `V₂`.
* `AlgebraicGeometry.Space.chartRelativeSpecQuotientPushforwardRingIso`: `A ≅ ν_* 𝒪_{X'}` as
  sheaves of commutative rings on the small étale site of `X`.
* `AlgebraicGeometry.Space.chartRelativeSpecQuotientPushforwardIso`: `A ≅ ν_* 𝒪_{X'}` as sheaves
  of commutative `𝒪_X`-algebras, which is clause (2) of Definition 0822.

## Main results

* `AlgebraicGeometry.Space.hom_app_comp_chartRelativeSpecSectionsIso`: at a chart, the
  structure-algebra map of `A` followed by the identification of its sections with the global
  sections of the relative spectrum is pullback of regular functions along the structure
  morphism of that relative spectrum.
* `AlgebraicGeometry.Space.Γ_map_comp_smallBaseChangeChartRelativeSpecSectionsMap`: at a chart
  `W` over `V₂`, that pullback followed by the comparison of charts of `X'` is pullback along the
  cartesian projection `X' ×_X W ⟶ W`.
* `AlgebraicGeometry.Space.hom_comp_chartRelativeSpecQuotientRestrictionRingIso`: the comparison
  on the charts over `V₂` carries the structure-algebra map of `A` to that of `ν_* 𝒪_{X'}`.
* `AlgebraicGeometry.Space.chartRelativeSpecQuotientPushforwardRingIso_restrict`: the comparison
  on the small étale site of `X` restricts on the charts over `V₂` to
  `AlgebraicGeometry.Space.chartRelativeSpecQuotientRestrictionRingIso`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))
    (hcon : ∀ V : SmallEtale B S hS X.1, B.Contains (chartRelativeSpec B S hS X A hA V))

/-! ### The structure-algebra maps -/

/-- Restricting a regular function on a chart's scheme to the étale chart that the top open cuts
out is the comparison `Γ(chartScheme V, ⊤) ≅ Γ(openChart V ⊤, ⊤)`. -/
theorem structureSheaf_map_openChartInclusion_top (V : SmallEtale B S hS X.1) :
    (structureSheaf B S hS X.1 X.2).obj.map (openChartInclusion B S hS X.1 V ⊤).op =
      (Scheme.Opens.topIso (⊤ : (chartScheme V).Opens)).inv := by
  change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS X.1).map (openChartInclusion B S hS X.1 V ⊤))).op = _
  rw [toScheme_map_toOver_map_openChartInclusion]
  exact appTop_ι_top

/-- The structure-algebra map of `A` followed by the identification of `A(V)` with the global
sections of the relative spectrum over `V` is pullback of regular functions along the structure
morphism of that relative spectrum. -/
theorem hom_app_comp_chartRelativeSpecSectionsIso (V : SmallEtale B S hS X.1) :
    A.hom.hom.app (op V) ≫ (chartRelativeSpecSectionsIso B S hS X A hA V).hom =
      Scheme.Γ.map (chartRelativeSpecToChart B S hS X A hA V).op := by
  have hchart : (chartSchemeAlgebra B S hS X A V).hom.hom.app
        (op (⊤ : (chartScheme V).Opens)) =
      (structureSheaf B S hS X.1 X.2).obj.map (openChartTopIso B S hS X.1 V).hom.op ≫
        A.hom.hom.app (op (openChart B S hS X.1 V ⊤)) := by
    rw [openChartTopIso_hom, structureSheaf_map_openChartInclusion_top]
    exact chartSchemeAlgebra_hom_app B S hS X A V ⊤
  have hw := congrArg
    (fun m : (chartScheme V).sheaf ⟶ (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (chartRelativeSpecToChart B S hS X A hA V)).right =>
      m.hom.app (op (⊤ : (chartScheme V).Opens)))
    (Under.w (chartRelativeSpecPushforwardIso B S hS X A hA V).inv)
  change A.hom.hom.app (op V) ≫ A.right.obj.map (openChartTopIso B S hS X.1 V).hom.op ≫
      (chartRelativeSpecTopSectionsIso B S hS X A hA V).inv =
    Scheme.Γ.map (chartRelativeSpecToChart B S hS X A hA V).op
  rw [← Category.assoc, ← A.hom.hom.naturality (openChartTopIso B S hS X.1 V).hom.op, ← hchart]
  exact hw

include hsq hsurj hV''

/-! ### The first factor, as an isomorphism of functors -/

/-- The sections of `A` over the charts over `V₂` are the global sections of the relative
spectra of `A` over those charts, as an isomorphism of functors whose components are
`AlgebraicGeometry.Space.chartRelativeSpecSectionsIso`. -/
def chartRelativeSpecSectionsFunctorIso :
    (chartOverInclusion B S hS X.1 V₂).op ⋙ A.right.obj ≅
      (chartRelativeSpecAtlasOverFunctor B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          hcon).op ⋙
        structurePresheaf B S hS
          (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1 :=
  NatIso.ofComponents
    (fun W ↦ chartRelativeSpecSectionsIso B S hS X A hA W.unop.obj)
    (fun {_W _W₂} k ↦ chartRelativeSpecSectionsIso_naturality B S hS X A hA k.unop.hom)

/-! ### The comparison on the charts over the atlas chart -/

/-- The comparison `A ≅ ν_*𝒪_{X'}` on the charts over `V₂`, as an isomorphism of the
restrictions of the two sheaves of commutative rings to that full subcategory.

It is the composite of `AlgebraicGeometry.Space.chartRelativeSpecSectionsFunctorIso`, the
comparison of charts of `X'` read through the structure presheaf of `X'`, and the inverse of
`AlgebraicGeometry.Space.pushforwardAlgebraChartRingIso` restricted to the charts over `V₂`. -/
def chartRelativeSpecQuotientRestrictionRingIso :
    (chartOverInclusion B S hS X.1 V₂).op ⋙ A.right.obj ≅
      (chartOverInclusion B S hS X.1 V₂).op ⋙
        (pushforwardAlgebra B S hS (Over.mk
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂
            hV''))).right.obj :=
  chartRelativeSpecSectionsFunctorIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' hcon ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (smallBaseChangeChartRelativeSpecFunctorIso B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'' hcon))
      (structurePresheaf B S hS
        (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1) ≪≫
    Functor.isoWhiskerLeft (chartOverInclusion B S hS X.1 V₂).op
      ((sheafToPresheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}).mapIso
        (pushforwardAlgebraChartRingIso B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'')).symm)

/-! ### The structure-algebra map at a chart over the atlas chart -/

section StructureMap

variable (W : ChartOver B S hS X.1 V₂)
    (hW : B.Contains (chartRelativeSpec B S hS X A hA W.obj))

/-- Pullback of regular functions along the comparison
`AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecIso` of charts of `X'` at a chart `W`
over `V₂`, from the global sections of the relative spectrum over `W` to the sections over `W`
of the direct image of the structure sheaf of `X'` along
`AlgebraicGeometry.Space.smallBaseChange`. -/
def smallBaseChangeChartRelativeSpecSectionsMap :
    Scheme.Γ.obj (op (chartRelativeSpec B S hS X A hA W.obj)) ⟶
      (((smallBaseChange B S hS
              (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
              (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq
                hsurj hV' hV₂ hV'')).sheafPushforwardContinuous CommRingCat.{u}
            (SmallEtale.topology B S hS X.1)
            (SmallEtale.topology B S hS
              (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1)).obj
          (structureSheaf B S hS
            (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1
            (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').2)).obj.obj
        (op W.obj) :=
  (structurePresheaf B S hS
      (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1).map
    (smallBaseChangeChartRelativeSpecIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
      W hW).hom.op

/-- Pullback of regular functions along the structure morphism of the relative spectrum over
`W`, followed by the comparison of charts of `X'`, is pullback along the cartesian projection
`X' ×_X W ⟶ W`, which is the structure-algebra map of the restriction along
`AlgebraicGeometry.Space.smallBaseChange`. -/
theorem Γ_map_comp_smallBaseChangeChartRelativeSpecSectionsMap :
    Scheme.Γ.map (chartRelativeSpecToChart B S hS X A hA W.obj).op ≫
        smallBaseChangeChartRelativeSpecSectionsMap B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'' W hW =
      (smallBaseChangeSharpCommRingCat B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq
            hsurj hV' hV₂ hV'')).hom.app (op W.obj) := by
  refine Eq.trans ?_ (congrArg (fun m => Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)
    (smallBaseChangeChartRelativeSpecLeftIso_hom_comp_toChart B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' W hW))
  rw [Functor.map_comp, op_comp, Functor.map_comp]
  rfl

end StructureMap

/-- The comparison on the charts over `V₂` carries the structure-algebra map of `A` to that of
`ν_*𝒪_{X'}`. -/
theorem hom_comp_chartRelativeSpecQuotientRestrictionRingIso :
    Functor.whiskerLeft (chartOverInclusion B S hS X.1 V₂).op A.hom.hom ≫
        (chartRelativeSpecQuotientRestrictionRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'' hcon).hom =
      Functor.whiskerLeft (chartOverInclusion B S hS X.1 V₂).op
        (pushforwardAlgebra B S hS (Over.mk
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV''))).hom.hom := by
  have hb : smallBaseChangeSharpCommRingCat B S hS
        (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
        (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'') ≫
      (pushforwardAlgebraChartRingIso B S hS
        (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
        (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'')).inv =
      (pushforwardAlgebra B S hS (Over.mk
        (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV''))).hom := by
    rw [← hom_comp_pushforwardAlgebraChartRingIso B S hS
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
      (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV''), Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine NatTrans.ext (funext fun W => ?_)
  have key : A.hom.hom.app (op W.unop.obj) ≫
        (chartRelativeSpecSectionsIso B S hS X A hA W.unop.obj).hom ≫
          smallBaseChangeChartRelativeSpecSectionsMap B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'' W.unop (hcon W.unop.obj) =
      (smallBaseChangeSharpCommRingCat B S hS
        (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
        (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'')).hom.app (op W.unop.obj) := by
    rw [← Category.assoc, hom_app_comp_chartRelativeSpecSectionsIso]
    exact Γ_map_comp_smallBaseChangeChartRelativeSpecSectionsMap B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' W.unop (hcon W.unop.obj)
  change A.hom.hom.app (op W.unop.obj) ≫
      ((chartRelativeSpecSectionsIso B S hS X A hA W.unop.obj).hom ≫
        smallBaseChangeChartRelativeSpecSectionsMap B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'' W.unop (hcon W.unop.obj)) ≫
        (pushforwardAlgebraChartRingIso B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'')).inv.hom.app (op W.unop.obj) =
    (pushforwardAlgebra B S hS (Over.mk
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV''))).hom.hom.app
      (op W.unop.obj)
  rw [← Category.assoc, key]
  exact congrArg (fun m : structureSheaf B S hS X.1 X.2 ⟶
      (pushforwardAlgebra B S hS (Over.mk
        (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV''))).right =>
    m.hom.app (op W.unop.obj)) hb

/-! ### The comparison on the small étale site of `X` -/

/-- `A ≅ ν_* 𝒪_{X'}` as sheaves of commutative rings on the small étale site of `X`: the
descent along the surjective étale chart `V₂` of
`AlgebraicGeometry.Space.chartRelativeSpecQuotientRestrictionRingIso`. -/
def chartRelativeSpecQuotientPushforwardRingIso :
    A.right ≅ (pushforwardAlgebra B S hS (Over.mk
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV''))).right :=
  haveI : IsIso (chartRelativeSpecQuotientRestrictionRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' hcon).hom := Iso.isIso_hom _
  haveI := isIso_descChartRingHom B S hS X.1 X.2 V₂
    (isSurjective_of_presheafSurjective B S hS V₂.obj.hom hsurj)
    (chartRelativeSpecQuotientRestrictionRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' hcon).hom
  asIso (descChartRingHom B S hS X.1 X.2 V₂
    (isSurjective_of_presheafSurjective B S hS V₂.obj.hom hsurj)
    (chartRelativeSpecQuotientRestrictionRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' hcon).hom)

/-- The comparison restricts on the charts over `V₂` to the isomorphism it was built from. -/
theorem chartRelativeSpecQuotientPushforwardRingIso_restrict :
    Functor.whiskerLeft (chartOverInclusion B S hS X.1 V₂).op
        (chartRelativeSpecQuotientPushforwardRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'' hcon).hom.hom =
      (chartRelativeSpecQuotientRestrictionRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'' hcon).hom :=
  descChartRingHom_restrict B S hS X.1 X.2 V₂
    (isSurjective_of_presheafSurjective B S hS V₂.obj.hom hsurj) _

/-! ### Clause (2) of Definition 0822 -/

/-- `A ≅ ν_* 𝒪_{X'}` as sheaves of commutative `𝒪_X`-algebras on the small étale site of `X`,
for the relative spectrum `X' = \underline{Spec}_X(A)` built as the quotient of the relation of
a pair of étale charts: the direct image of the structure sheaf of `X'` is the algebra `A`. -/
def chartRelativeSpecQuotientPushforwardIso :
    A ≅ pushforwardAlgebra B S hS (Over.mk
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')) :=
  descChartAlgebraIso B S hS X.1 X.2 V₂
    (isSurjective_of_presheafSurjective B S hS V₂.obj.hom hsurj)
    (chartRelativeSpecQuotientRestrictionRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' hcon)
    (hom_comp_chartRelativeSpecQuotientRestrictionRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' hcon)

/-- The algebra comparison of
`AlgebraicGeometry.Space.chartRelativeSpecQuotientPushforwardIso` has the sheaf-of-rings
comparison as its underlying morphism of sheaves of commutative rings. -/
theorem chartRelativeSpecQuotientPushforwardIso_hom_right :
    (chartRelativeSpecQuotientPushforwardIso B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'' hcon).hom.right =
      (chartRelativeSpecQuotientPushforwardRingIso B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'' hcon).hom :=
  rfl

end AlgebraicGeometry.Space

end
