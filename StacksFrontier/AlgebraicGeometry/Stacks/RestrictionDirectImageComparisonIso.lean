module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageGlueSection
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageTwoFibreProductArrow

/-!
# Equation 075M: the comparison map is an isomorphism

This file proves that the canonical comparison map of equation 075M,
`AlgebraicGeometry.Space.restrictedDirectImageComparison`, is an **isomorphism**, and hence that
the square of ringed topoi of Stacks 073N commutes at the morphism of algebraic spaces a
1-morphism induces.

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f)
  (fSpace : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
  (ha : schemeChartFunctor B S hS F p eF ⋙ f ≅
    CostructuredArrow.map fSpace.hom ⋙ schemeChartFunctor B S hS G q eG)
  [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]
  (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))

/-! ### The canonical map of sections over the chart diagrams, and its injectivity -/

section ChartCorrespondence

variable {X Y : AlgebraicSpaces B S hS}

/-- **The canonical map of sections of a small étale direct image over the diagrams of étale
scheme charts.** The chart correspondence of Stacks 03G8 is a bijection between the `fSp`-maps
into a sheaf and the homomorphisms out of it into the direct image; this is the `fSp`-map of the
identity homomorphism of the direct image, i.e. the canonical restriction of a section of the
direct image to a diagram of étale scheme charts. -/
noncomputable def idFMap (fSp : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    FMap B S hS X.1 Y.1 fSp.hom P.obj
      ((smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.obj P).obj :=
  (fMapEquivPushforwardHom_ringUniverse B S hS fSp P
    ((smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.obj P)).symm (𝟙 _)

/-- **A sheaf on the spaces-étale site is separated for a one-element covering**: restriction of
sections along a morphism whose one-element family covers its target is injective. -/
theorem injective_map_of_singleton_covering (Z : AlgebraicSpaces B S hS)
    (H : Sheaf (SpacesEtale.topology B S hS Z) (Type u))
    {U : SpacesEtale B S hS Z} {W : SmallEtale B S hS Z.1}
    (g : (comparisonFunctor B S hS Z).obj W ⟶ U)
    (hg : SpacesEtale.IsCovering B S hS Z
      ⟨U, PreZeroHypercover.singleton.{u + 1} g⟩) :
    Function.Injective (H.obj.map g.op) := by
  intro x y h
  refine (((isSheaf_iff_isSheaf_of_type _ H.obj).1 H.2).isSeparated _
    (singleton_generate_mem_topology B S hS Z g hg)).ext ?_
  rintro T m ⟨T', a, b, hb, rfl⟩
  cases hb
  have e : ∀ z : H.obj.obj (op U), H.obj.map (a ≫ g).op z = H.obj.map a.op (H.obj.map g.op z) := by
    intro z
    rw [op_comp, H.obj.map_comp]
    rfl
  rw [e, e, h]

/-- **A section of a small étale direct image over a chart of the target is determined by its
restriction to a chart of the source covering the cartesian base change.**

Through the chart correspondence of Stacks 03G8 in the form
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_chart`, that restriction is the
restriction along the given arrow of a section of the presenting spaces-étale sheaf over the
base change, transported by a bijection; and restriction along a one-element covering is
injective. -/
theorem injective_idFMap_app (fSp : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (W : SmallEtale B S hS X.1)
    (g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS fSp V)
    (hg : SpacesEtale.IsCovering B S hS X
      ⟨chartBaseChange B S hS fSp V, PreZeroHypercover.singleton.{u + 1} g⟩) :
    Function.Injective ((idFMap B S hS fSp P).app
      (chartDiagramOfBaseChangeArrow B S hS fSp W V g)) := by
  set H := (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P with hH
  set i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H :=
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app P).symm with hi
  set A := (smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.map i.hom ≫
    (smallEtaleRingedToposHom_pushforward B S hS fSp).hom.app H with hA
  have hc := fMapEquivPushforwardHom_ringUniverse_chart B S hS fSp P
    ((smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.obj P) H i
    (idFMap B S hS fSp P) (chartDiagramOfBaseChangeArrow B S hS fSp W V g) g
    (heq_of_eq (yoneda_map_chartDiagramOfBaseChangeArrow_g B S hS fSp W V g).symm)
  have hψ : fMapEquivPushforwardHom_ringUniverse B S hS fSp P
        ((smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.obj P)
        (idFMap B S hS fSp P) ≫ A = A := by
    rw [hA, hi]
    refine congrArg (fun z ↦ z ≫ (smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.map
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app P).symm.hom ≫
      (smallEtaleRingedToposHom_pushforward B S hS fSp).hom.app H) ?_ |>.trans
      (Category.id_comp _)
    exact (fMapEquivPushforwardHom_ringUniverse B S hS fSp P
      ((smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.obj P)).apply_symm_apply _
  have : IsIso A := by
    rw [hA]
    infer_instance
  have hc' : ∀ z : ((smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.obj P).obj.obj
        (op V),
      ((sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).map i.hom).app (op W)
          ((idFMap B S hS fSp P).app
            (chartDiagramOfBaseChangeArrow B S hS fSp W V g) z) =
        H.obj.map g.op (A.hom.app (op V) z) := fun z ↦ hψ ▸ hc z
  intro t t' htt'
  have h1 : H.obj.map g.op (A.hom.app (op V) t) = H.obj.map g.op (A.hom.app (op V) t') :=
    (hc' t).symm.trans (Eq.trans (congrArg (fun z ↦
      ((sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).map i.hom).app (op W) z)
        htt') (hc' t'))
  have h2 := injective_map_of_singleton_covering B S hS X H g hg h1
  exact (Sheaf.sheafIsoSectionsEquiv (asIso A) (op V)).injective h2

end ChartCorrespondence

/-! ### The canonical map of sections of the right-hand side over the chart diagrams -/

include hp in
/-- **The canonical map of sections of the right-hand side of equation 075M over the diagrams of
étale scheme charts.** The chart correspondence of Stacks 03G8 is a bijection between the
`fSpace`-maps into a sheaf and the homomorphisms out of it into the direct image; this is the
`fSpace`-map of the identity homomorphism of `f_{small,*}(ℱ|_{F_étale})`, i.e. the canonical
restriction of a section of the direct image to a diagram of étale scheme charts. -/
noncomputable abbrev chartRestrictionFMap :
    FMap B S hS F G fSpace.hom ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ).obj
      ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
        ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj :=
  idFMap B S hS fSpace ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)

include hp hq hf in
/-- **The comparison map of equation 075M followed by restriction to a diagram of étale scheme
charts is the map of sections out of which it was built.**

This is naturality of the chart correspondence of Stacks 03G8 in the sheaf on the target,
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_symm_target_map`, at the identity
homomorphism. -/
theorem chartRestrictionFMap_comparison (d : ChartDiagram B S hS F G fSpace.hom)
    (s : ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj.obj (op d.V)) :
    (chartRestrictionFMap B S hS F G p hp hF hG eF fSpace ℱ).app d
        ((restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace
          ha ℱ).hom.app (op d.V) s) =
      restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha ℱ d s := by
  have h := fMapEquivPushforwardHom_ringUniverse_symm_target_map B S hS fSpace
    ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)
    ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ))
    ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ))
    (restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ)
    (𝟙 _) d s
  refine Eq.trans h.symm ?_
  refine Eq.trans (congrArg (fun z ↦ ((fMapEquivPushforwardHom_ringUniverse B S hS fSpace
    ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)
    ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ))).symm z).app d s)
      (Category.comp_id _)) ?_
  exact congrArg (fun ξ ↦ FMap.app ξ d s)
    ((fMapEquivPushforwardHom_ringUniverse B S hS fSpace
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)
      ((restrictionSheafFunctor B S hS G q hq eG).obj
        ((etaleDirectImage B S hS p q hp f hf).obj ℱ))).symm_apply_apply
      (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ))

/-! ### The section of the left-hand side a section of the right-hand side glues to -/

variable (c : q.ChoiceOfPullbacks) (V : SmallEtale B S hS G)

/-- The family of sections of `ℱ` attached to a section `t` of the right-hand side of
equation 075M over a chart `V` of `G`: over the object of `𝒳` of each diagram of étale scheme
charts over `V`, the canonical restriction of `t` to that diagram. -/
noncomputable abbrev comparisonChartFamily
    (t : ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj.obj (op V))
    (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) :
    ℱ.obj.obj (op ((restrictionFunctor B S hS F p eF).obj W)) :=
  (chartRestrictionFMap B S hS F G p hp hF hG eF fSpace ℱ).app
    (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ) t

include hp hF hG eF eG in
omit [∀ (H : 𝒳ᵒᵖ ⥤ Type u), f.op.HasPointwiseRightKanExtension H] in
/-- The family is compatible in the sense the gluing `AlgebraicGeometry.Space.glueSection` asks
for: this is `AlgebraicGeometry.Space.fMap_app_congr_of_comparisonChartHom_eq`, the refinement of
two chart diagrams. -/
theorem comparisonChartFamily_compatible
    (t : ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj.obj (op V))
    (W₁ W₂ : SmallEtale B S hS F)
    (ζ₁ : (CostructuredArrow.map fSpace.hom).obj W₁.1 ⟶ V.1)
    (ζ₂ : (CostructuredArrow.map fSpace.hom).obj W₂.1 ⟶ V.1)
    (Y : 𝒳) (n₁ : Y ⟶ (restrictionFunctor B S hS F p eF).obj W₁)
    (n₂ : Y ⟶ (restrictionFunctor B S hS F p eF).obj W₂)
    (hn : f.map n₁ ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
          (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₁ ζ₁) =
        f.map n₂ ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
          (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₂ ζ₂)) :
    ℱ.obj.map n₁.op (comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t W₁ ζ₁) =
      ℱ.obj.map n₂.op (comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t W₂ ζ₂) :=
  fMap_app_congr_of_comparisonChartHom_eq B S hS F G p q hF hG eF eG f fSpace ha V ℱ.obj
    ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj
    (chartRestrictionFMap B S hS F G p hp hF hG eF fSpace ℱ) t W₁ W₂ ζ₁ ζ₂ Y n₁ n₂ hn

include hp hF hG eF eG in
/-- **The compatible family of glued values, as a section of the pullback of `ℱ` to the 2-fibre
product of equation 075M.** Its component at an object of the 2-fibre product is the glued value
of the family at the pair the object is, and the compatibility is
`AlgebraicGeometry.Space.glueSection_map` together with
`AlgebraicGeometry.Space.twoFibreProductArrow_comp`. -/
noncomputable def comparisonGlueSections
    (t : ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj.obj (op V)) :
    ((twoFibreProductSnd B S hS G p q eG f c V).op ⋙ ℱ.obj).sections where
  val P := glueSection B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ
    (comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t)
    (comparisonChartFamily_compatible B S hS F G p q hp hF hG eF eG f fSpace ha ℱ V t)
    P.unop.y (twoFibreProductArrow B S hS G p q eG f c V P.unop)
  property {P P'} φ := by
    refine Eq.trans (glueSection_map B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ
      (comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t)
      (comparisonChartFamily_compatible B S hS F G p q hp hF hG eF eG f fSpace ha ℱ V t)
      P.unop.y P'.unop.y φ.unop.b
      (twoFibreProductArrow B S hS G p q eG f c V P.unop)) ?_
    exact congrArg (fun κ ↦ glueSection B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ
      (comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t)
      (comparisonChartFamily_compatible B S hS F G p q hp hF hG eF eG f fSpace ha ℱ V t)
      P'.unop.y κ) (twoFibreProductArrow_comp B S hS G p q eG f c V φ.unop)

include hp hq hF hG eF eG hf in
/-- **The section of the left-hand side of equation 075M a section of the right-hand side glues
to.** The glued values at the pairs are the components of a global section over the 2-fibre
product of equation 075M, and the sections of `(f_*ℱ)|_{G_étale}` over `V` are those global
sections by Stacks 06W6. -/
noncomputable def comparisonPreimage
    (t : ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj.obj (op V)) :
    ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj.obj (op V) :=
  (restrictedDirectImageChartEquiv B S hS G p q hp hq eG f hf c ℱ V).symm
    ((Presheaf.globalSectionsEquivSections
      ((twoFibreProductSnd B S hS G p q eG f c V).op ⋙ ℱ.obj)).symm
      (comparisonGlueSections B S hS F G p q hp hF hG eF eG f fSpace ha ℱ c V t))

include hp hq hF hG eF eG hf in
/-- **The values of the glued section are the glued values.** -/
theorem ranSection_comparisonPreimage
    (t : ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj.obj (op V))
    (P : TwoFibreProductOver (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
      (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f) :
    ranSection B S hS p f ℱ (twoFibreProductArrow B S hS G p q eG f c V P)
        (comparisonPreimage B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ c V t) =
      glueSection B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ
        (comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t)
        (comparisonChartFamily_compatible B S hS F G p q hp hF hG eF eG f fSpace ha ℱ V t)
        P.y (twoFibreProductArrow B S hS G p q eG f c V P) := by
  have h := Presheaf.pushforwardSectionsEquiv_apply p q f hq hf.comp_eq c
    (chartFiberObj B S hS G q eG V) ℱ.obj
    (comparisonPreimage B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ c V t) P
  have h1 : Presheaf.pushforwardSectionsEquiv p q f hq hf.comp_eq c
        (chartFiberObj B S hS G q eG V) ℱ.obj
        (comparisonPreimage B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ c V t) =
      (Presheaf.globalSectionsEquivSections
        ((twoFibreProductSnd B S hS G p q eG f c V).op ⋙ ℱ.obj)).symm
        (comparisonGlueSections B S hS F G p q hp hF hG eF eG f fSpace ha ℱ c V t) :=
    (restrictedDirectImageChartEquiv B S hS G p q hp hq eG f hf c ℱ V).apply_symm_apply _
  rw [h1, Equiv.apply_symm_apply] at h
  exact h.symm

include hp hq hF hG eF eG hf in
/-- **The glued section restricts over every diagram of étale scheme charts to the canonical
restriction of the given section.** -/
theorem comparisonSections_comparisonPreimage
    (t : ((smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.obj
      ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)).obj.obj (op V))
    (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) :
    restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha ℱ
        (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ)
        (comparisonPreimage B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ c V t) =
      comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t W ζ := by
  have harr := twoFibreProductArrow_twoFibreProductMk B S hS G p q hq eG f hf c V
    ((restrictionFunctor B S hS F p eF).obj W)
    (comparisonChartHom B S hS p q eF eG f fSpace ha
      (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ))
  have h := ranSection_comparisonPreimage B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ c V t
    (twoFibreProductMk B S hS G p q hq eG f hf c V ((restrictionFunctor B S hS F p eF).obj W)
      (comparisonChartHom B S hS p q eF eG f fSpace ha
        (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ)))
  rw [harr] at h
  refine Eq.trans h ?_
  exact glueSection_chart B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ
    (comparisonChartFamily B S hS F G p hp hF hG eF fSpace ℱ V t)
    (comparisonChartFamily_compatible B S hS F G p q hp hF hG eF eG f fSpace ha ℱ V t) W ζ

/-! ### Equation 075M: the comparison map is an isomorphism -/

include hp hq hF hG eF eG hf c in
/-- **The comparison map of equation 075M is surjective on sections over an étale scheme chart of
`G`.** The section of the left-hand side it hits is the one glued from the given section of the
right-hand side.

The two are equal because both restrict, over every diagram of étale scheme charts over `V`, to
the canonical restriction of the given section — the comparison map by
`AlgebraicGeometry.Space.chartRestrictionFMap_comparison` and the glued section by
`AlgebraicGeometry.Space.comparisonSections_comparisonPreimage` — and because a section of the
right-hand side over `V` is determined by its restriction to one diagram whose chart covers the
cartesian base change `F ×_G V` (`AlgebraicGeometry.Space.injective_idFMap_app`, Stacks 03H7). -/
theorem surjective_restrictedDirectImageComparisonHom_app :
    Function.Surjective
      ((restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace
        ha ℱ).hom.app (op V)) := by
  intro t
  refine ⟨comparisonPreimage B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ c V t, ?_⟩
  obtain ⟨W₀, g₀, -, -, hg₀⟩ := exists_etaleChart_singleton_covering B S hS
    (⟨F, hF⟩ : AlgebraicSpaces B S hS) (chartBaseChange B S hS fSpace V)
  refine injective_idFMap_app B S hS fSpace
    ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ) V W₀ g₀ hg₀ ?_
  refine Eq.trans (chartRestrictionFMap_comparison B S hS F G p q hp hq hF hG eF eG f hf fSpace
    ha ℱ (chartDiagramOfBaseChangeArrow B S hS fSpace W₀ V g₀) _) ?_
  exact comparisonSections_comparisonPreimage B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ
    c V t W₀ (CostructuredArrow.homMk
      (chartDiagramOfBaseChangeArrow B S hS fSpace W₀ V g₀).g
      (chartDiagramOfBaseChangeArrow B S hS fSpace W₀ V g₀).comm.symm)

include hp hq hF hG eF eG hf in
/-- **The comparison map of equation 075M is a bijection on sections over every étale scheme
chart of `G`**, with no hypothesis beyond those of equation 075M itself: the choice of pullbacks
that the pushforward formula of Stacks 06W6 needs is not one, because a category fibred in
groupoids admits one. -/
theorem bijective_restrictedDirectImageComparisonHom_app :
    Function.Bijective
      ((restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace
        ha ℱ).hom.app (op V)) := by
  obtain ⟨c⟩ : Nonempty q.ChoiceOfPullbacks :=
    (Functor.nonempty_choiceOfPullbacks_iff_isFibered q).mpr hq.isFibered
  exact ⟨injective_restrictedDirectImageComparisonHom_app B S hS F G p q hp hq hF hG eF eG f hf
      fSpace ha c ℱ V,
    surjective_restrictedDirectImageComparisonHom_app B S hS F G p q hp hq hF hG eF eG f hf
      fSpace ha ℱ c V⟩

include hp hq hF hG eF eG hf in
/-- **Equation 075M.** The canonical comparison map of equation 075M,
`AlgebraicGeometry.Space.restrictedDirectImageComparison`, is an **isomorphism**: the two sides
of the equation,
```
(f_*ℱ)|_{G_étale} = f_{small,*}(ℱ|_{F_étale}),
```
agree, naturally in the sheaf, through that canonical map.

Invertibility is reduced to a bijection on sections over each étale scheme chart `V` of `G` by
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison_of_bijective`, and there:

* **injectivity** is
  `AlgebraicGeometry.Space.injective_restrictedDirectImageComparisonHom_app`. A section of
  `f_*ℱ` over `u_G V` is determined by its values at the pairs `(Z, κ : f(Z) ⟶ u_G V)` (Stacks
  06W6), the chart correspondence of Stacks 03G8 determines those values at the morphisms out of
  the image of an étale chart of `F`, and the factorization lemma together with the sheaf
  condition on `ℱ` carries that to all of them.
* **surjectivity** is
  `AlgebraicGeometry.Space.surjective_restrictedDirectImageComparisonHom_app`. The canonical
  restrictions of a section of the right-hand side to the diagrams of étale scheme charts over
  `V` form a family which the refinement of two chart diagrams shows compatible, the sheaf
  condition on `ℱ` glues that family to a value at every pair `(Z, κ)`, and those values are the
  components of a global section over the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` — a section of
  the left-hand side. It is carried to the given section because a section of the right-hand side
  is determined by its restriction to one diagram whose chart covers the cartesian base change
  `F ×_G V`, which is Properties of Spaces 03H7.

The choice of pullbacks that the pushforward formula of Stacks 06W6 needs is not a hypothesis: a
category fibred in groupoids admits one. -/
@[stacks 075M "the displayed equality itself: the canonical comparison map between the two sides \
is an isomorphism"]
theorem isIso_restrictedDirectImageComparison :
    IsIso (restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf fSpace ha) :=
  isIso_restrictedDirectImageComparison_of_bijective B S hS F G p q hp hq hF hG eF eG f hf
    fSpace ha fun ℱ V ↦ bijective_restrictedDirectImageComparisonHom_app B S hS F G p q hp hq
      hF hG eF eG f hf fSpace ha ℱ V

include hp hq hF hG eF eG hf in
/-- **Stacks 073N at the morphism of algebraic spaces a 1-morphism induces, unconditionally.**
The square of ringed topoi of Stacks 073N commutes: its two legs are 2-isomorphic.

This is `AlgebraicGeometry.Space.restrictionRingedSquareInduced` with its hypothesis `hiso`
discharged by `AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`, the invertibility
of the comparison map of equation 075M; the structure-sheaf compatibility of the square is
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`, whose
verticality input is `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`. -/
noncomputable def restrictionRingedSquareOfInduced :=
  restrictionRingedSquareInduced B S hS F G p q hp hq hF hG eF eG f hf
    (isIso_restrictedDirectImageComparison B S hS F G p q hp hq hF hG eF eG f hf
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)
      (schemeChartPostcompIso B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq))

end AlgebraicGeometry.Space

end
