module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverMapCorners
public import StacksFrontier.Deformation.Applications.TwoFibreProductDeformation
public import StacksFrontier.Deformation.CofiberedPresentation.SmoothPresentation
public import StacksFrontier.Deformation.Examples.Geometric.SchemesCofibered
public import StacksFrontier.Deformation.Examples.Geometric.SchemesDeformationCategory
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverEquivalence
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverSmooth

/-!
# The deformation category of a two-chart scheme as a 2-fibre product of ring deformations

[Stacks Project, Tag 0DYZ]: in Situation 0DYY there is an equivalence of deformation categories
`Def_X = Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`, where `Def_P` is the deformation category of the
`k`-algebra `P` of Example 0DY1 and the two legs are the restriction functors of the source.

The proof of the source glues: a deformation of `X` is the same as deformations of the two
opens `U₁`, `U₂` with an identification over `U₁₂`. That is
`Deformation.Examples.GluingSituation.isEquivalence_comparisonFunctor`, an equivalence
`Def_X ≌ Def_{U₁} ×_{Def_{U₁₂}} Def_{U₂}` with the *scheme* deformation categories of the
three opens. The remaining step, which the source leaves implicit, is to pass from the opens to
their coordinate rings: the deformations of an affine scheme `U = Spec P` are the deformations
of `P`, via spectra and global sections (Tag 0DYX, here
`Deformation.Examples.chartEquivalenceOver` for an open presented as a spectrum), and this
identification is natural in the restriction `U₁₂ → U_i`.

## The restriction functors `Def_{P_i} ⟶ Def_{P₁₂}`

They are `Deformation.Examples.GluingSituation.chartRestrictLeft` and `chartRestrictRight`:
take spectra, restrict the deformation of `U_i` to `U₁₂`, take global sections. In ring terms
(`Deformation.Examples.chartRestriction_fiber_topIso`,
`Deformation.Examples.structureMap_comp_chartRestrictionSectionsHom`,
`Deformation.Examples.chartRestrictionSectionsHom_comp_hom_map`): a deformation `A → P'` of
`P = P_i` goes to the ring of sections of `Spec P'` over the open cut out by `U₁₂`, an
`A`-algebra receiving `P'` by restriction of sections, and that restriction lifts the ring map
`P_i → P₁₂` of the charts (`Deformation.Examples.chartRestrictionRingHom`, the ring map whose
spectrum is `Spec P₁₂ ≅ U₁₂ ⊆ U_i ≅ Spec P_i`). In general `U₁₂` is not a principal open of
`U_i`, so the restriction is not a localization of `P'`; it is the ring of sections over an
open.

## Main definitions

* `Deformation.Examples.chartRestrictionRingHom`: the ring map of the charts.
* `Deformation.Examples.chartRestrictionSectionsHom`: restriction of sections from a
  deformation of `P` to its restriction.
* `Deformation.Examples.GluingSituation.chartRestrictLeftIso`,
  `Deformation.Examples.GluingSituation.chartRestrictRightIso`: the naturality of Tag 0DYX in
  the restrictions, as 2-isomorphisms over `𝒞_Λ`.
* `Deformation.Examples.GluingSituation.RingChartDeformations`: the 2-fibre product
  `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` over `𝒞_Λ`.
* `Deformation.Examples.GluingSituation.ringComparisonFunctor`: the comparison functor
  `Def_X ⥤ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`.
* `Deformation.Examples.GluingSituation.ringDeformationEquivalenceOver`: it, as an equivalence
  over `𝒞_Λ`.

## Main results

* `Deformation.Examples.GluingSituation.isEquivalence_ringComparisonFunctor`: the comparison
  functor is an equivalence of categories.
* `Deformation.Examples.GluingSituation.deformationCategories_equivalence`: **Stacks 0DYZ.**

## References

* [Stacks Project, Tag 0DYZ](https://stacks.math.columbia.edu/tag/0DYZ)
* [Stacks Project, Tag 0DYY](https://stacks.math.columbia.edu/tag/0DYY)
* [Stacks Project, Tag 0DYX](https://stacks.math.columbia.edu/tag/0DYX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StacksRepresentableCFG

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The restriction of a chart, in ring terms -/

section ChartRestriction

variable {X : Over (Spec (.of k))} {U V : X.left.Opens} (h : V ≤ U)
  {P Q : Type u} [CommRing P] [Algebra k P] [CommRing Q] [Algebra k Q]
  (eU : Over.mk (U.ι ≫ X.hom) ≅ specOver k P) (eV : Over.mk (V.ι ≫ X.hom) ≅ specOver k Q)

/-- The ring map `P → Q` of two charts `U ≅ Spec P` and `V ≅ Spec Q` of opens `V ≤ U`: the ring
map whose spectrum is `Spec Q ≅ V ⊆ U ≅ Spec P`. -/
def chartRestrictionRingHom : CommRingCat.of P ⟶ CommRingCat.of Q :=
  Spec.preimage (eV.inv.left ≫ (openIsoPreimage h).hom ≫ (U.ι ⁻¹ᵁ V).ι ≫ eU.hom.left)

/-- The spectrum of the ring map of two charts is the inclusion of the charts. -/
theorem spec_map_chartRestrictionRingHom :
    Spec.map (chartRestrictionRingHom h eU eV) =
      eV.inv.left ≫ (openIsoPreimage h).hom ≫ (U.ι ⁻¹ᵁ V).ι ≫ eU.hom.left :=
  Spec.map_preimage _

variable (D : ringDeformationCategory (Λ := Λ) (k := k) P)

/-- The deformation of `U` corresponding to a deformation `D` of `P`: the spectrum of `D`, with
its special fibre identified with `U` through the chart. -/
abbrev chartSpectrum : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom)) :=
  (chartEquivalenceOver (Λ := Λ) P eU).inv.functor.obj D

/-- The open of the spectrum of a deformation `D` of `P` cut out by `V`: the image of `V` under
`Spec P ≅ U` followed by the special-fibre immersion `Spec P ⟶ Spec D`. -/
abbrev chartRestrictionOpen : (Spec (CommRingCat.of D.left.fiber)).Opens :=
  restrictedOpen (chartSpectrum eU D) (U.ι ⁻¹ᵁ V)

/-- The restriction of a deformation `D` of `P` along two charts of opens `V ≤ U`: take the
spectrum, restrict to `V`, take global sections. For the two charts of Situation 0DYY this is
`Deformation.Examples.GluingSituation.chartRestrictLeft` and `chartRestrictRight` on objects. -/
abbrev chartRestriction : ringDeformationCategory (Λ := Λ) (k := k) Q :=
  (chartEquivalenceOver (Λ := Λ) Q eV).hom.functor.obj
    ((openRestrictionLEFunctor (Λ := Λ) (k := k) h).obj (chartSpectrum eU D))

/-- The restriction of a deformation lives over the same object of `𝒞_Λ`. -/
theorem chartRestriction_base : (chartRestriction h eU eV D).left.base = D.left.base := rfl

/-- **The ring of a restricted deformation is a ring of sections.** The ring of the restriction
of `D` is the ring of sections of `Spec D` over the open `chartRestrictionOpen eU D` cut out by
`V`, by the canonical identification of the global sections of an open subscheme. -/
def chartRestrictionFiberIso :
    CommRingCat.of (chartRestriction h eU eV D).left.fiber ≅
      (Spec (CommRingCat.of D.left.fiber)).presheaf.obj
        (Opposite.op (chartRestrictionOpen (V := V) eU D)) :=
  (chartRestrictionOpen (V := V) eU D).topIso

/-- Restriction of sections from a deformation `D` of `P` to its restriction: the ring map
`D → Γ(Spec D, chartRestrictionOpen eU D)`. -/
def chartRestrictionSectionsHom :
    CommRingCat.of D.left.fiber ⟶ CommRingCat.of (chartRestriction h eU eV D).left.fiber :=
  (Scheme.ΓSpecIso (CommRingCat.of D.left.fiber)).inv ≫
    (chartRestrictionOpen (V := V) eU D).ι.appTop

/-- **The restriction map is restriction of sections of `Spec D`.** Read through
`chartRestrictionFiberIso`, the map `chartRestrictionSectionsHom` is the restriction of the
structure sheaf of `Spec D` from the whole space to the open cut out by `V`. -/
theorem chartRestriction_fiber_topIso :
    chartRestrictionSectionsHom h eU eV D ≫ (chartRestrictionFiberIso h eU eV D).hom =
      (Scheme.ΓSpecIso (CommRingCat.of D.left.fiber)).inv ≫
        (Spec (CommRingCat.of D.left.fiber)).presheaf.map
          (homOfLE le_top : chartRestrictionOpen (V := V) eU D ⟶ ⊤).op := by
  simp only [chartRestrictionSectionsHom, chartRestrictionFiberIso, Scheme.Opens.ι_appTop,
    Scheme.Opens.topIso_hom]
  rfl

/-- **The restriction map is a map of algebras over the Artinian base.** -/
theorem structureMap_comp_chartRestrictionSectionsHom :
    FlatAlgebraCategory.structureMap D.left ≫ chartRestrictionSectionsHom h eU eV D =
      FlatAlgebraCategory.structureMap (chartRestriction h eU eV D).left := by
  rw [show FlatAlgebraCategory.structureMap (chartRestriction h eU eV D).left =
      (Scheme.ΓSpecIso (CommRingCat.of D.left.base)).inv ≫
        ((chartRestrictionOpen (V := V) eU D).ι ≫
          Spec.map (FlatAlgebraCategory.structureMap D.left)).appTop from
    SchemeRingDeformation.structureMap_sectionsFlatAlgebra Q _, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- **The restriction map lifts the ring map of the charts.** The square formed by the
restriction of sections `D → chartRestriction D`, the two reductions `D → P` and
`chartRestriction D → Q`, and the ring map `P → Q` of the charts commutes. -/
theorem chartRestrictionSectionsHom_comp_hom_map :
    chartRestrictionSectionsHom h eU eV D ≫ (chartRestriction h eU eV D).hom.map =
      D.hom.map ≫ chartRestrictionRingHom (P := P) (Q := Q) h eU eV := by
  let ι := restrictDeformationι (X := Over.mk (U.ι ≫ X.hom)) (U.ι ⁻¹ᵁ V) (chartSpectrum eU D)
  let sp := (restrictDeformation (X := Over.mk (U.ι ≫ X.hom)) (U.ι ⁻¹ᵁ V)
    (chartSpectrum eU D)).specialMap
  let ρ := chartRestrictionRingHom (P := P) (Q := Q) h eU eV
  have hsp : (eV.inv.left ≫ (openIsoPreimage h).hom ≫ sp) ≫ ι = Spec.map (D.hom.map ≫ ρ) := by
    have s₁ : (eV.inv.left ≫ (openIsoPreimage h).hom ≫ sp) ≫ ι =
        eV.inv.left ≫ (openIsoPreimage h).hom ≫
          ((U.ι ⁻¹ᵁ V).ι ≫ (chartSpectrum eU D).specialMap) := by
      simp only [Category.assoc]
      rw [restrictDeformation_specialMap_comp_ι (X := Over.mk (U.ι ≫ X.hom)) (U.ι ⁻¹ᵁ V)
        (chartSpectrum eU D)]
    have s₂ : Spec.map (D.hom.map ≫ ρ) =
        (eV.inv.left ≫ (openIsoPreimage h).hom ≫ (U.ι ⁻¹ᵁ V).ι ≫ eU.hom.left) ≫
          Spec.map D.hom.map :=
      (Spec.map_comp _ _).trans
        (congrArg (fun t => t ≫ Spec.map D.hom.map) (spec_map_chartRestrictionRingHom h eU eV))
    refine s₁.trans (Eq.trans ?_ s₂.symm)
    simp only [Category.assoc]
    rfl
  let Γi := (Scheme.ΓSpecIso (CommRingCat.of D.left.fiber)).inv
  let Γq := (Scheme.ΓSpecIso (CommRingCat.of Q)).hom
  let j := eV.inv.left ≫ (openIsoPreimage h).hom ≫ sp
  have t₁ : chartRestrictionSectionsHom h eU eV D ≫ (chartRestriction h eU eV D).hom.map =
      Γi ≫ (ι.appTop ≫ j.appTop) ≫ Γq := rfl
  have t₂ : Γi ≫ (ι.appTop ≫ j.appTop) ≫ Γq = Γi ≫ (j ≫ ι).appTop ≫ Γq :=
    congrArg (fun t => Γi ≫ t ≫ Γq) (Scheme.Hom.comp_appTop j ι).symm
  have t₃ : Γi ≫ (j ≫ ι).appTop ≫ Γq = Γi ≫ (Spec.map (D.hom.map ≫ ρ)).appTop ≫ Γq := by
    rw [hsp]
    rfl
  have t₄ : Γi ≫ (Spec.map (D.hom.map ≫ ρ)).appTop ≫ Γq = D.hom.map ≫ ρ :=
    (congrArg (fun t => Γi ≫ t) (Scheme.ΓSpecIso_naturality (D.hom.map ≫ ρ))).trans
      (Iso.inv_hom_id_assoc _ _)
  exact t₁.trans (t₂.trans (t₃.trans t₄))

end ChartRestriction

namespace GluingSituation

variable (S : GluingSituation Λ k)

/-! ### The restriction functors of the source, on objects -/

/-- The restriction functor `Def_{P₁} ⟶ Def_{P₁₂}` on objects is `chartRestriction`. -/
theorem chartRestrictLeft_obj (D : ringDeformationCategory (Λ := Λ) (k := k) S.P₁) :
    (chartRestrictLeft S).obj D =
      chartRestriction (inf_le_left : S.U₁ ⊓ S.U₂ ≤ S.U₁) S.affine₁ S.affine₁₂ D :=
  rfl

/-- The restriction functor `Def_{P₂} ⟶ Def_{P₁₂}` on objects is `chartRestriction`. -/
theorem chartRestrictRight_obj (D : ringDeformationCategory (Λ := Λ) (k := k) S.P₂) :
    (chartRestrictRight S).obj D =
      chartRestriction (inf_le_right : S.U₁ ⊓ S.U₂ ≤ S.U₂) S.affine₂ S.affine₁₂ D :=
  rfl

/-! ### Naturality of Tag 0DYX in the restrictions -/

/-- **Tag 0DYX is natural in the restriction `U₁₂ ⊆ U₁`**: restricting a deformation of `U₁` to
`U₁₂` and passing to `Def_{P₁₂}` is isomorphic, by vertical isomorphisms, to passing to
`Def_{P₁}` and restricting there. -/
def chartRestrictLeftIso :
    (restrictLeft S).toFunctor ⋙ (chartOverlap S).toFunctor ≅
      (chartLeft S).toFunctor ⋙ (chartRestrictLeft S).toFunctor :=
  NatIso.ofComponents
    (fun D => ((restrictLeft S).toFunctor ⋙ (chartOverlap S).toFunctor).mapIso
      ((chartEquivalenceOver (Λ := Λ) S.P₁ S.affine₁).unitIso.app D))
    (fun f => ((Functor.map_comp _ _ _).symm.trans
      (congrArg ((restrictLeft S).toFunctor ⋙ (chartOverlap S).toFunctor).map
        ((chartEquivalenceOver (Λ := Λ) S.P₁ S.affine₁).unitIso.hom.naturality f))).trans
      (Functor.map_comp _ _ _))

/-- **Tag 0DYX is natural in the restriction `U₁₂ ⊆ U₂`.** -/
def chartRestrictRightIso :
    (restrictRight S).toFunctor ⋙ (chartOverlap S).toFunctor ≅
      (chartRight S).toFunctor ⋙ (chartRestrictRight S).toFunctor :=
  NatIso.ofComponents
    (fun D => ((restrictRight S).toFunctor ⋙ (chartOverlap S).toFunctor).mapIso
      ((chartEquivalenceOver (Λ := Λ) S.P₂ S.affine₂).unitIso.app D))
    (fun f => ((Functor.map_comp _ _ _).symm.trans
      (congrArg ((restrictRight S).toFunctor ⋙ (chartOverlap S).toFunctor).map
        ((chartEquivalenceOver (Λ := Λ) S.P₂ S.affine₂).unitIso.hom.naturality f))).trans
      (Functor.map_comp _ _ _))

/-- The components of `chartRestrictLeftIso` are vertical over `𝒞_Λ`. -/
theorem isHomLift_chartRestrictLeftIso
    (D : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (S.U₁.ι ≫ S.X.hom))) :
    (ringDeformationCategoryOver Λ k S.P₁₂).p.IsHomLift
      (𝟙 ((ringDeformationCategoryOver Λ k S.P₁₂).p.obj
        ((chartOverlap S).toFunctor.obj ((restrictLeft S).toFunctor.obj D))))
      ((chartRestrictLeftIso S).hom.app D) := by
  have := (chartEquivalenceOver (Λ := Λ) S.P₁ S.affine₁).isHomLift_unitIso_hom_app D
  exact Functor.isHomLift_map_of_comp_eq
    (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) _)
    (q := (ringDeformationCategoryOver Λ k S.P₁₂).p)
    (BasedFunctor.comp (restrictLeft S) (chartOverlap S)).w
    (𝟙 ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) _).obj D))
    ((chartEquivalenceOver (Λ := Λ) S.P₁ S.affine₁).unitIso.hom.app D)

/-- The components of `chartRestrictRightIso` are vertical over `𝒞_Λ`. -/
theorem isHomLift_chartRestrictRightIso
    (D : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (S.U₂.ι ≫ S.X.hom))) :
    (ringDeformationCategoryOver Λ k S.P₁₂).p.IsHomLift
      (𝟙 ((ringDeformationCategoryOver Λ k S.P₁₂).p.obj
        ((chartOverlap S).toFunctor.obj ((restrictRight S).toFunctor.obj D))))
      ((chartRestrictRightIso S).hom.app D) := by
  have := (chartEquivalenceOver (Λ := Λ) S.P₂ S.affine₂).isHomLift_unitIso_hom_app D
  exact Functor.isHomLift_map_of_comp_eq
    (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) _)
    (q := (ringDeformationCategoryOver Λ k S.P₁₂).p)
    (BasedFunctor.comp (restrictRight S) (chartOverlap S)).w
    (𝟙 ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) _).obj D))
    ((chartEquivalenceOver (Λ := Λ) S.P₂ S.affine₂).unitIso.hom.app D)

/-! ### The 2-fibre product of the ring deformation categories -/

/-- The 2-fibre product `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` over `𝒞_Λ` of the deformation
categories of the three coordinate rings, along the two restriction functors. -/
abbrev RingChartDeformations :=
  TwoFibreProductOver (ringDeformationCategoryOver Λ k S.P₁).p
    (ringDeformationCategoryOver Λ k S.P₂).p (ringDeformationCategoryOver Λ k S.P₁₂).p
    (chartRestrictLeft S).toFunctor (chartRestrictRight S).toFunctor

/-- The structure functor of `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` to `𝒞_Λ`. -/
abbrev ringChartDeformationsProjection :
    RingChartDeformations S ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k :=
  TwoFibreProductOver.structureFunctor (ringDeformationCategoryOver Λ k S.P₁).p
    (ringDeformationCategoryOver Λ k S.P₂).p (ringDeformationCategoryOver Λ k S.P₁₂).p
    (chartRestrictLeft S).toFunctor (chartRestrictRight S).toFunctor

/-- Passing from the three opens to their coordinate rings:
`Def_{U₁} ×_{Def_{U₁₂}} Def_{U₂} ⥤ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`, induced by Tag 0DYX on
the three corners. -/
def chartMapCorners : TwoOpenDeformations (Λ := Λ) (k := k) S.X S.U₁ S.U₂ ⥤
    RingChartDeformations S :=
  TwoFibreProductOver.mapCorners (chartLeft S).w (chartRight S).w (chartOverlap S).w
    (chartRestrictLeftIso S) (chartRestrictRightIso S) (isHomLift_chartRestrictLeftIso S)
    (isHomLift_chartRestrictRightIso S)

/-- Passing from the opens to their coordinate rings is an equivalence. -/
theorem isEquivalence_chartMapCorners : (chartMapCorners S).IsEquivalence :=
  TwoFibreProductOver.isEquivalence_mapCorners (chartEquivalenceOver (Λ := Λ) S.P₁ S.affine₁)
    (chartEquivalenceOver (Λ := Λ) S.P₂ S.affine₂)
    (chartEquivalenceOver (Λ := Λ) S.P₁₂ S.affine₁₂) (chartRestrictLeft S).w
    (chartRestrictRight S).w (chartRestrictLeftIso S) (chartRestrictRightIso S)
    (isHomLift_chartRestrictLeftIso S) (isHomLift_chartRestrictRightIso S)

/-! ### The equivalence -/

/-- The comparison functor `Def_X ⥤ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`: restrict a deformation
of `X` to the two opens and pass to their coordinate rings. -/
def ringComparisonFunctor :
    SchemeDeformationCategory (Λ := Λ) (k := k) S.X ⥤ RingChartDeformations S :=
  comparisonFunctor S ⋙ chartMapCorners S

/-- The comparison functor is over `𝒞_Λ`. -/
theorem ringComparisonFunctor_comp_projection :
    ringComparisonFunctor S ⋙ ringChartDeformationsProjection S =
      schemeDeformationCategoryProjection (Λ := Λ) (k := k) S.X :=
  rfl

/-- The comparison functor `Def_X ⥤ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` is an equivalence of
categories. -/
theorem isEquivalence_ringComparisonFunctor : (ringComparisonFunctor S).IsEquivalence := by
  have := isEquivalence_comparisonFunctor S
  have := isEquivalence_chartMapCorners S
  exact inferInstanceAs (comparisonFunctor S ⋙ chartMapCorners S).IsEquivalence

/-- The comparison functor, as an equivalence over `𝒞_Λ` between `Def_X` and
`Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`. -/
def ringDeformationEquivalenceOver :
    EquivalenceOver (schemeDeformationCategoryProjection (Λ := Λ) (k := k) S.X)
      (ringChartDeformationsProjection S) :=
  haveI := isEquivalence_ringComparisonFunctor S
  Deformation.equivalenceOverOfCofibered
    (schemeDeformationCategoryProjection_cofiberedInGroupoids S.X) (ringComparisonFunctor S)
    (ringComparisonFunctor_comp_projection S)

/-- The forward functor of `ringDeformationEquivalenceOver` is the comparison functor. -/
theorem ringDeformationEquivalenceOver_hom_functor :
    (ringDeformationEquivalenceOver S).hom.functor = ringComparisonFunctor S :=
  rfl

/-- **Stacks 0DYZ.** In Situation 0DYY, `Def_X` and `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` are
deformation categories, and the comparison functor between them is an equivalence of
categories over `𝒞_Λ`. Here `Def_{P_i}` is the deformation category of the `k`-algebra `P_i`
of Example 0DY1, `Def_X` that of the scheme `X` of Example 0DY7, and the two legs of the
2-fibre product are the restriction functors `Def_{P_i} ⟶ Def_{P₁₂}` along `U₁₂ ⊆ U_i`. -/
@[stacks 0DYZ "Def_X = Def_{P_1} ×_{Def_{P_12}} Def_{P_2} as an equivalence over 𝒞_Λ of \
deformation categories, with the ring deformation categories of Example 0DY1 and the \
restriction functors along U_12 ⊆ U_i"]
theorem deformationCategories_equivalence :
    IsDeformationCategory.{u, u, u} (schemeDeformationCategoryProjection (Λ := Λ) (k := k) S.X) ∧
      IsDeformationCategory.{u, u, u} (ringChartDeformationsProjection S) ∧
      ∃ e : EquivalenceOver (schemeDeformationCategoryProjection (Λ := Λ) (k := k) S.X)
        (ringChartDeformationsProjection S), e.hom.functor = ringComparisonFunctor S :=
  ⟨isDeformationCategory_schemeDeformationCategoryProjection S.X,
    isDeformationCategory_twoFibreProductOver _ _ _ _ _ (chartRestrictLeft S).w
      (chartRestrictRight S).w (ringDeformationCategory_isDeformationCategory S.P₁)
      (ringDeformationCategory_isDeformationCategory S.P₂)
      (ringDeformationCategory_isDeformationCategory S.P₁₂),
    ringDeformationEquivalenceOver S, ringDeformationEquivalenceOver_hom_functor S⟩

end GluingSituation

end Deformation.Examples

end
