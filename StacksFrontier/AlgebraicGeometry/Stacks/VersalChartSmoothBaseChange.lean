module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenary
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituation
public import StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ArtinianAtlas

/-!
# Versality gives smoothness on a neighbourhood (Stacks 0DQZ, (1) ⟹ (4))

In the versal situation of **Stacks 0DQU** let `x` be an object of `𝒳` over a scheme `U` locally of
finite type over `S`, and let `u₀ ∈ U` be a finite type point at which `x` is versal. This file
proves that `x|_{U'} : U' → 𝒳` is smooth for some open neighbourhood `U' ⊆ U` of `u₀`, which is
the implication (1) ⟹ (4) of **Stacks 0DQZ**, and registers the equivalence of (1) and (4).

The source's proof is followed. A smooth surjection `a : (Sch/P) ⟶ 𝒳` from a scheme
(`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`) is locally of finite type over
`S` because `𝒳` is. The 2-fibre product `(Sch/P) ×_𝒳 (Sch/U)` is represented by an algebraic
space `F` over `P`; its lower-shriek extension `Λ_P F` to the site of `S` maps smoothly and
surjectively to `U` (`AlgebraicGeometry.Stack.versalChartProjMap`), so it has a finite type point
over
`u₀` (**Stacks 06EJ**), which read over `P` is a finite type point `z₀` of `F` lying over `u₀`.
Artin's Axioms, **Stacks 0CXM**, makes `F ⟶ P` smooth at `z₀`, on an open subspace `W`; its
(RS) hypothesis is **Stacks 07WQ** and its diagonal hypotheses are those of an algebraic stack
(**Stacks 04XR** for the local finite type of the isomorphism sheaves). The open image of `W` in
`|(Sch/U)|` is an open set of points on which `x` is smooth
(`AlgebraicGeometry.Stack.isSmooth_openImage_inclusion_comp`, which is the descent of smoothness
along a smooth surjection of the source's last sentence), and it cuts out an open subscheme
`U' ∋ u₀` of `U` on which `x` is smooth.

## Main results

* `AlgebraicGeometry.Stack.exists_isRelativelySmooth_restrict_of_isVersalAt`: **Stacks 0DQZ**,
  (1) ⟹ (4).
* `AlgebraicGeometry.Stack.isVersalAt_iff_exists_isRelativelySmooth_restrict`: **Stacks 0DQZ**,
  the equivalence of (1) and (4).
* `AlgebraicGeometry.Stack.exists_isOpen_isSmooth_versalChartSub`: an open of the base change
  smooth over the chart has an open image in `|(Sch/U)|` on which `x` is smooth.
* `AlgebraicGeometry.Stack.exists_isRelativelySmooth_restrict_of_openSubstackOfPoints`: smoothness
  on an open set of points of `(Sch/U)` is smoothness on an open subscheme of `U`.
* `AlgebraicGeometry.Stack.locallyOfFiniteType_of_isSmooth_schemeStack`: a smooth scheme chart of
  an algebraic stack locally of finite type over `S` is locally of finite type over `S`.

## Implementation notes

Stacks 0CXM is stated over the big fppf site of the chart `P`, with `F` a presheaf there; the
geometry over `S` is done with its lower-shriek extension `Λ_P F`, through
`AlgebraicGeometry.Stack.relocalizeFibreEquivalence` and
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`. Field-valued points pass between the
two sites by `AlgebraicGeometry.Stack.liftFieldValuedPoint` and
`AlgebraicGeometry.Stack.descendFieldValuedPoint`, and smoothness over the two sites is compared
by `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff` and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`.

Smoothness of `x|_{U'}` is that of Stacks 04XB, `AlgebraicGeometry.Stack.IsRelativelySmooth`: the
1-morphism is representable by algebraic spaces, its source being a scheme and its target an
algebraic stack, and it is obtained from smoothness in the sense of Stacks 075U by Stacks 06FM.

## References

* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 06EJ](https://stacks.math.columbia.edu/tag/06EJ)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth scheme chart of an algebraic stack locally of finite type over `S` is locally of
finite type over `S`.** A smooth 1-morphism is locally of finite type, so the composite with the
structure morphism is, and that composite is the structure morphism of the represented
algebraic stack of the chart, whose local finite type is that of the scheme. -/
theorem locallyOfFiniteType_of_isSmooth_schemeStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒳))
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (ha : AlgebraicStacks.IsSmooth B S hS a) :
    LocallyOfFiniteType (B.inclusion.map U.hom) := by
  have haType : AlgebraicStacks.IsLocallyOfFiniteType B S hS a :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a ha)
  have hchain : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (a ≫ structureMorphism B S hS 𝒳) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS a (structureMorphism B S hS 𝒳) haType h𝒳
  rw [comp_structureMorphism] at hchain
  obtain ⟨g, hg⟩ := exists_schemeMap_locallyOfFiniteType_of_schemeStackHom B S hS
    (structureMorphism B S hS (schemeStack.{u, w} B S hS U)) hchain
  have hgU : g.left = U.hom := by simpa using Over.w g
  have : (BigFppfOver.toScheme B S hS).map g = B.inclusion.map U.hom := by
    change B.inclusion.map g.left = _
    rw [hgU]
  rw [this] at hg
  exact hg

/-- **The isomorphism sheaves of an algebraic stack are locally of finite type, in the form Stacks
0CXM asks for.** Every algebraic space whose universe lift is isomorphic to that of an
isomorphism presheaf of `𝒳` is locally of finite type over its base; this is **Stacks 04XR**
transported along the isomorphism. -/
theorem isLocallyOfFiniteType_of_iso_isomPresheaf
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ (T : BigFppfOver B S hS) (a b : 𝒳.val.p.Fiber T)
      (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B T.left.1 T.left.2 G →
      Nonempty (G ⋙ uliftFunctor.{u, u} ≅
        ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
          uliftFunctor.{u, u}) →
      Space.IsLocallyOfFiniteType B T.left.1 T.left.2
        (terminal.from G : G ⟶
          ⊤_ ((BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  intro T a b G _ ⟨e⟩
  have hiso : G ≅ (Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b :=
    ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e
  exact (Space.isLocallyOfFiniteType_terminal_iff_of_iso B T.left.1 T.left.2 hiso).mpr
    (isLocallyOfFiniteType_isomPresheaf.{u, w} B S hS 𝒳 h𝒳 T a b)

/-- The inverse functor of an equivalence over the site transported along an equality of
projections is the original one. -/
theorem _root_.StacksRepresentableCFG.EquivalenceOver.ofEq_inv_functor {C : Type*} [Category C]
    {D₁ D₂ : Type*} [Category D₁] [Category D₂] {p p' : D₁ ⥤ C} {q : D₂ ⥤ C} (h : p = p')
    (e : StacksRepresentableCFG.EquivalenceOver p q) : (e.ofEq h).inv.functor = e.inv.functor := by
  subst h
  rfl

/-- The section of the presheaf represented by `T` named by an object of the slice over `T` is its
structure morphism, read over the prescribed base. -/
theorem sectionOfObj_sliceElementsEquivalenceOver {C : Type*} [Category C] {T : C}
    (o : Over T) {W : C} (h : o.left = W) :
    PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver T) o h =
      eqToHom h.symm ≫ o.hom := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- Two objects over `T` which are equal carry a point of a one-point source to the same point,
whichever of the two equal sources the point is read in. -/
theorem toScheme_map_apply_eq_of_eq {T W A : BigFppfOver B S hS} {O₁ O₂ : Over T}
    (hO : O₁ = O₂) (h₁ : O₁.left = W) (h₂ : A = O₂.left)
    (hsub : ∀ a b : (BigFppfOver.toScheme B S hS).obj W, a = b)
    (c : (BigFppfOver.toScheme B S hS).obj W) (c' : (BigFppfOver.toScheme B S hS).obj A)
    {u : (BigFppfOver.toScheme B S hS).obj T}
    (hu : (BigFppfOver.toScheme B S hS).map (eqToHom h₁.symm ≫ O₁.hom) c = u) :
    (BigFppfOver.toScheme B S hS).map (eqToHom h₂ ≫ O₂.hom) c' = u := by
  subst hO
  subst h₁
  subst h₂
  simp only [eqToHom_refl, Category.id_comp] at hu ⊢
  rw [hsub c' c]
  exact hu

/-! ### Field-valued points of a space over `P` and of its lower-shriek extension -/

section LiftPoint

variable {P : BigFppfOver B S hS} {G : (BigFppfOver B P.left.1 P.left.2)ᵒᵖ ⥤ Type u}

/-- A field-valued point of a presheaf on the big fppf site of `P`, read as a field-valued point of
its lower-shriek extension to the big fppf site of `S`. -/
def liftFieldValuedPoint (p : Space.FieldValuedPoint B P.left.1 P.left.2 G) :
    Space.FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor P.hom).obj G) where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase ≫ P.hom.hom
  value := OverShriek.relocalizeMk P.hom G
    (W := Opposite.op (Over.mk (⟨p.toBase ≫ P.hom.hom⟩ : B.obj p.contained ⟶ B.obj hS)))
    (⟨p.toBase⟩ : B.obj p.contained ⟶ P.left) p.value rfl

/-- Lifting field-valued points preserves domination. -/
theorem dominates_liftFieldValuedPoint {p q : Space.FieldValuedPoint B P.left.1 P.left.2 G}
    (h : Space.FieldValuedPoint.Dominates B P.left.1 P.left.2 G p q) :
    Space.FieldValuedPoint.Dominates B S hS _ (liftFieldValuedPoint B S hS p)
      (liftFieldValuedPoint B S hS q) := by
  obtain ⟨f, hf⟩ := h
  have hw : f.left ≫ (⟨q.toBase⟩ : B.obj q.contained ⟶ P.left) = ⟨p.toBase⟩ := Over.w f
  refine ⟨Over.homMk f.left
    (ObjectProperty.hom_ext _ (congrArg (fun k => k.hom ≫ P.hom.hom) hw)), ?_⟩
  apply Subtype.ext
  change (⟨f.left ≫ ⟨q.toBase⟩, G.map (Over.homMk f.left rfl :
      Over.mk (f.left ≫ (⟨q.toBase⟩ : B.obj q.contained ⟶ P.left)) ⟶ Over.mk ⟨q.toBase⟩).op
        q.value⟩ : Σ χ : B.obj p.contained ⟶ P.left, G.obj (Opposite.op (Over.mk χ))) =
    ⟨⟨p.toBase⟩, p.value⟩
  rw [← hf]
  exact OverShriek.sigmaMk_eq G q.value _ f rfl

/-- The lift of field-valued points, on points. -/
noncomputable def liftPoints :
    Space.points B P.left.1 P.left.2 G →
      Space.points B S hS ((OverShriek.relocalizePresheafFunctor P.hom).obj G) :=
  Quot.map (liftFieldValuedPoint B S hS) (fun _ _ ⟨r, h₁, h₂⟩ =>
    ⟨liftFieldValuedPoint B S hS r, dominates_liftFieldValuedPoint B S hS h₁,
      dominates_liftFieldValuedPoint B S hS h₂⟩)

/-- The lift of the class of a field-valued point is the class of its lift. -/
theorem liftPoints_class (p : Space.FieldValuedPoint B P.left.1 P.left.2 G) :
    liftPoints B S hS (p.class B P.left.1 P.left.2 G) =
      (liftFieldValuedPoint B S hS p).class B S hS _ := rfl

/-- The lift of points is natural in the presheaf. -/
theorem pointsMap_liftPoints {F : (BigFppfOver B P.left.1 P.left.2)ᵒᵖ ⥤ Type u} (ι : G ⟶ F)
    (g : Space.points B P.left.1 P.left.2 G) :
    Space.pointsMap B S hS _ ((OverShriek.relocalizePresheafFunctor P.hom).map ι)
        (liftPoints B S hS g) =
      liftPoints B S hS (Space.pointsMap B P.left.1 P.left.2 G ι g) := by
  induction g using Quot.inductionOn with
  | h p => rfl

/-- A field-valued point of the lower-shriek extension, read over `P`. -/
def descendFieldValuedPoint
    (q : Space.FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor P.hom).obj G)) :
    Space.FieldValuedPoint B P.left.1 P.left.2 G where
  carrier := q.carrier
  contained := q.contained
  toBase := q.value.1.1.hom
  value := q.value.1.2

/-- Descending a field-valued point of the lower-shriek extension and lifting it back gives the
same point. -/
theorem liftPoints_descend
    (q : Space.FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor P.hom).obj G)) :
    liftPoints B S hS ((descendFieldValuedPoint B S hS q).class B P.left.1 P.left.2 G) =
      q.class B S hS _ := by
  rw [liftPoints_class]
  have hq : q.value.1.1 ≫ P.hom = ⟨q.toBase⟩ := q.value.2
  refine Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _ ⟨q, ?_,
    Space.FieldValuedPoint.dominates_refl B S hS _ q⟩
  refine ⟨Over.homMk (𝟙 _)
    (ObjectProperty.hom_ext _ ((Category.id_comp _).trans (congrArg (fun k => k.hom) hq))), ?_⟩
  apply Subtype.ext
  change (⟨𝟙 _ ≫ (⟨q.value.1.1.hom⟩ : B.obj q.contained ⟶ P.left),
      G.map (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 _ ≫ (⟨q.value.1.1.hom⟩ : B.obj q.contained ⟶ P.left))
        ⟶ Over.mk (⟨q.value.1.1.hom⟩ : B.obj q.contained ⟶ P.left)).op q.value.1.2⟩ :
      Σ χ : B.obj q.contained ⟶ P.left, G.obj (Opposite.op (Over.mk χ))) = q.value.1
  exact OverShriek.sigmaMk_eq_self G q.value.1.2 _ rfl

end LiftPoint

/-! ### The base change of `x` along a smooth chart -/

section Chart

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {P : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS P ⟶ 𝒳)

/-- A 1-morphism `a : (Sch/P) ⟶ 𝒳`, read as a scheme-valued point of `𝒳` with values in `P`: a
functor out of the big fppf site of `P`. -/
abbrev versalChartPoint : BigFppfOver B P.left.1 P.left.2 ⥤ 𝒳.val.val.obj :=
  Over.iteratedSliceBackward P ⋙ a.hom.hom.toFunctor

/-- `versalChartPoint` lies over the structure functor of the big fppf site of `P`. -/
theorem versalChartPoint_comp : versalChartPoint B S hS 𝒳 a ⋙ 𝒳.val.val.p = Over.map P.hom :=
  (Functor.assoc _ _ _).trans ((congrArg (Over.iteratedSliceBackward P ⋙ ·) a.hom.hom.w).trans
    (Over.iteratedSliceBackward_forget P))

/-- The equivalence between the big fppf site of `P` and the slice `(Sch/S)/P`, as a 1-morphism
of algebraic stacks. -/
abbrev sliceToSchemeStack (P : BigFppfOver B S hS) :
    schemeSliceStack.{u, w} B S hS P ⟶ schemeStack.{u, w} B S hS P :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨Over.iteratedSliceBackward P, Over.iteratedSliceBackward_forget P⟩)

/-- `sliceToSchemeStack` is an equivalence. -/
theorem isEquivalence_sliceToSchemeStack (P : BigFppfOver B S hS) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (sliceToSchemeStack.{u, w} B S hS P).hom) :=
  (Over.iteratedSliceEquiv P).isEquivalence_inverse

/-- The point `versalChartPoint` of `a`, as a 1-morphism of algebraic stacks out of the big fppf
site of
`P`; it is `a` precomposed with the equivalence `sliceToSchemeStack`. -/
abbrev versalChartSliceMap : schemeSliceStack.{u, w} B S hS P ⟶ 𝒳 :=
  schemeSliceStackMap.{u, w} B S hS P (versalChartPoint B S hS 𝒳 a) (versalChartPoint_comp B S hS 𝒳
      a)

/-- `versalChartSliceMap` is the chart precomposed with `sliceToSchemeStack`. -/
theorem versalChartSliceMap_eq : versalChartSliceMap B S hS 𝒳 a = sliceToSchemeStack B S hS P ≫ a
    := rfl

/-- `versalChartSliceMap` is smooth when the chart is. -/
theorem isSmooth_versalChartSliceMap (ha : AlgebraicStacks.IsSmooth B S hS a) :
    AlgebraicStacks.IsSmooth B S hS (versalChartSliceMap B S hS 𝒳 a) := by
  rw [versalChartSliceMap_eq]
  exact AlgebraicStacks.isSmooth_comp B S hS _ a
    (AlgebraicStacks.isSmooth_of_isEquivalence B S hS _
      (isEquivalence_sliceToSchemeStack.{u, w} B S hS P))
    ha

/-- `versalChartSliceMap` is surjective when the chart is. -/
theorem isSurjective_versalChartSliceMap (ha : IsSurjective B S hS a) :
    IsSurjective B S hS (versalChartSliceMap B S hS 𝒳 a) := by
  rw [versalChartSliceMap_eq]
  exact isSurjective_comp B S hS _ a
    (surjective_pointsMap_of_isEquivalence B S hS _
      (isEquivalence_sliceToSchemeStack.{u, w} B S hS P)) ha

variable (x : 𝒳.val.val.obj)

/-- The 1-morphism `x : (Sch/U) ⟶ 𝒳` of an object `x` over `U`, as a 1-morphism of algebraic
stacks. -/
abbrev objectStackMap : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))

/-- The canonical 2-fibre product square of the chart and of `x`. -/
abbrev versalChartSquare : Bicategory.TwoCommSq (versalChartSliceMap B S hS 𝒳 a) (objectStackMap B
    S hS 𝒳 x) :=
  twoFibreProductSquareAlgebraicStacks B S hS (versalChartSliceMap B S hS 𝒳 a) (objectStackMap B S
      hS 𝒳 x)

variable (F : (BigFppfOver B P.left.1 P.left.2)ᵒᵖ ⥤ Type u)
  (e : Deformation.Artin.BaseChange.BaseChangeEquivalence B S hS 𝒳.val (𝒳.val.val.p.obj x) P x rfl
    (versalChartPoint B S hS 𝒳 a) F)

/-- The base change of `x` along the chart, read over `S`. -/
abbrev versalChartBaseChange : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (OverShriek.relocalizePresheafFunctor P.hom).obj F

/-- The equivalence of the 2-fibre product with the category of elements of the base change. -/
abbrev versalChartBaseChangeEquivalence :=
  relocalizeFibreEquivalence B S hS P (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))
    (versalChartPoint B S hS 𝒳 a) F e

variable (hF : IsAlgebraicSpace B P.left.1 P.left.2 F)

/-- The base change of `x` along the chart, as an algebraic stack over `S`. -/
abbrev versalChartSpaceStack : AlgebraicStacks.{u, w} B S hS :=
  algebraicSpaceStack.{u, w} B S hS (versalChartBaseChange B S hS F)
    (Space.isAlgebraicSpace_relocalizePresheaf B S hS P F hF)

/-- The comparison of the algebraic stack of the base change with the 2-fibre product. -/
abbrev versalChartEquivMap : versalChartSpaceStack.{u, w} B S hS F hF ⟶ (versalChartSquare B S hS 𝒳
    a x).pt :=
  Bicategory.InducedBicategory.mkHom
    (equivalenceOverInvMap B S hS (versalChartBaseChange B S hS F)
      (versalChartBaseChangeEquivalence B S hS 𝒳 a x F e))

/-- `versalChartEquivMap` is an equivalence. -/
theorem isEquivalence_versalChartEquivMap :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (versalChartEquivMap B S hS 𝒳 a x F e hF).hom) :=
  (versalChartBaseChangeEquivalence B S hS 𝒳 a x F e).isEquivalence_inv_functor

/-- The projection of the base change of `x` along the chart to `(Sch/U)`. -/
abbrev versalChartProj : versalChartSpaceStack.{u, w} B S hS F hF ⟶ schemeStack.{u, w} B S hS
    (𝒳.val.val.p.obj x) :=
  versalChartEquivMap B S hS 𝒳 a x F e hF ≫ (versalChartSquare B S hS 𝒳 a x).snd

/-- The projection of the base change to `(Sch/U)` is smooth: it is the base change of the
smooth chart, after an equivalence. -/
theorem isSmooth_versalChartProj (ha : AlgebraicStacks.IsSmooth B S hS a) :
    AlgebraicStacks.IsSmooth B S hS (versalChartProj B S hS 𝒳 a x F e hF) :=
  AlgebraicStacks.isSmooth_comp B S hS _ _
    (AlgebraicStacks.isSmooth_of_isEquivalence B S hS _
      (isEquivalence_versalChartEquivMap B S hS 𝒳 a x F e hF))
    (AlgebraicStacks.isSmooth_baseChange B S hS _ _ (versalChartSquare B S hS 𝒳 a x).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _))
      (isSmooth_versalChartSliceMap B S hS 𝒳 a ha))

/-- The projection of the base change to `(Sch/U)` is surjective. -/
theorem isSurjective_versalChartProj (ha : IsSurjective B S hS a) :
    IsSurjective B S hS (versalChartProj B S hS 𝒳 a x F e hF) :=
  isSurjective_comp B S hS _ _
    (surjective_pointsMap_of_isEquivalence B S hS _
      (isEquivalence_versalChartEquivMap B S hS 𝒳 a x F e hF))
    (isSurjective_of_isTwoFibreProduct B S hS (versalChartSquare B S hS 𝒳 a x)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _)
      (isSurjective_versalChartSliceMap B S hS 𝒳 a ha))

/-- The projection of the base change to `U`, as a morphism of algebraic spaces over `S`. -/
abbrev versalChartProjMap : versalChartBaseChange B S hS F ⟶ yoneda.obj (𝒳.val.val.p.obj x) :=
  representingMap B S hS (versalChartSpaceStack.{u, w} B S hS F hF).val
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)).val (versalChartBaseChange B S hS F)
    (yoneda.obj (𝒳.val.val.p.obj x)) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver (𝒳.val.val.p.obj x))
    (versalChartProj B S hS 𝒳 a x F e hF).hom

/-- The projection of the base change to `U` is a smooth morphism of algebraic spaces. -/
theorem isSmooth_versalChartProjMap (ha : AlgebraicStacks.IsSmooth B S hS a) :
    Space.IsSmooth B S hS (versalChartProjMap B S hS 𝒳 a x F e hF) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (versalChartSpaceStack.{u, w} B S hS F hF).property
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)).property _ _
    (Space.isAlgebraicSpace_relocalizePresheaf B S hS P F hF)
    (isAlgebraicSpace_yoneda B S hS _) _ _ _).1 (isSmooth_versalChartProj B S hS 𝒳 a x F e hF ha)

/-- The projection of the base change to `U` is a surjective morphism of algebraic spaces. -/
theorem isSurjective_versalChartProjMap (ha : IsSurjective B S hS a) :
    Space.IsSurjective B S hS (versalChartProjMap B S hS 𝒳 a x F e hF) :=
  isSurjective_representingMap_of_isSurjective B S hS _ _ _ _ _
    (isSurjective_versalChartProj B S hS 𝒳 a x F e hF ha)

/-- The map of representing presheaves of the first projection of the chart square is the
structural morphism `Λ_P F ⟶ h_P` of the base change. -/
theorem representingMap_versalChartEquivMap_fst :
    representingMap B S hS (fibredCategory B S hS (versalChartBaseChange B S hS F))
        (schemeSlice B S hS P) (versalChartBaseChange B S hS F) (yoneda.obj P)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (schemeSliceEquivalenceOver B S hS P)
        (equivalenceOverInvMap B S hS (versalChartBaseChange B S hS F)
            (versalChartBaseChangeEquivalence B S hS 𝒳 a x F e) ≫
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (schemeSliceMap B S hS P (versalChartPoint B S hS 𝒳 a) (versalChartPoint_comp B S hS 𝒳
                a))
            (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))).fst) =
      OverShriek.relocalizeToYoneda P.hom F := by
  refine (representingMap_comp B S hS (𝒜 := fibredCategory B S hS (versalChartBaseChange B S hS F))
    (ℬ := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (schemeSliceMap B S hS P (versalChartPoint B S hS 𝒳 a) (versalChartPoint_comp B S hS 𝒳
                a))
            (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))).pt)
    (𝒞 := schemeSlice B S hS P) _ (versalChartBaseChange B S hS F) (yoneda.obj P)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (versalChartBaseChangeEquivalence B S hS 𝒳 a x F e) (schemeSliceEquivalenceOver B S hS P) _
        _).trans ?_
  have h0 := representingMap_equivalenceOverInvMap B S hS
    (𝒳 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (schemeSliceMap B S hS P (versalChartPoint B S hS 𝒳 a) (versalChartPoint_comp B S hS 𝒳
                a))
            (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))).pt)
    (versalChartBaseChange B S hS F) (versalChartBaseChangeEquivalence B S hS 𝒳 a x F e)
  rw [h0, Category.id_comp]
  exact representingMap_relocalizeFibre B S hS P
    (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) (versalChartPoint B S hS 𝒳 a) F e
    (versalChartPoint_comp B S hS 𝒳 a)

variable {G : (BigFppfOver B P.left.1 P.left.2)ᵒᵖ ⥤ Type u}
  (hG : IsAlgebraicSpace B P.left.1 P.left.2 G) (ι : G ⟶ F)

/-- The 1-morphism to `(Sch/U)` from the algebraic stack of a space `G` over the chart mapping to
the base change `F`. -/
abbrev versalChartSubMap :
    algebraicSpaceStack.{u, w} B S hS ((OverShriek.relocalizePresheafFunctor P.hom).obj G)
        (Space.isAlgebraicSpace_relocalizePresheaf B S hS P G hG) ⟶
      schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) :=
  algebraicSpaceStackMap.{u, w} B S hS (Space.isAlgebraicSpace_relocalizePresheaf B S hS P G hG)
      (Space.isAlgebraicSpace_relocalizePresheaf B S hS P F hF)
      ((OverShriek.relocalizePresheafFunctor P.hom).map ι) ≫
    versalChartProj B S hS 𝒳 a x F e hF

/-- The lower-shriek extension of a smooth morphism of presheaves over `P` is smooth over `S`. -/
theorem isSmooth_relocalizeMap_of_isSmooth {X Y : (BigFppfOver B P.left.1 P.left.2)ᵒᵖ ⥤ Type u}
    (k : X ⟶ Y) (hk : Space.IsSmooth B P.left.1 P.left.2 k) :
    Space.IsSmooth B S hS ((OverShriek.relocalizePresheafFunctor P.hom).map k) :=
  (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B P.left.1 S P.left.2 hS P.hom _ k).2 hk

/-- `versalChartSubMap` is smooth when `ι` is. -/
theorem isSmooth_versalChartSubMap (ha : AlgebraicStacks.IsSmooth B S hS a)
    (hι : Space.IsSmooth B P.left.1 P.left.2 ι) :
    AlgebraicStacks.IsSmooth B S hS (versalChartSubMap B S hS 𝒳 a x F e hF hG ι) :=
  AlgebraicStacks.isSmooth_comp B S hS _ _
    ((isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS _ _ _).2
      (isSmooth_relocalizeMap_of_isSmooth B S hS ι hι))
    (isSmooth_versalChartProj B S hS 𝒳 a x F e hF ha)

/-- The first projection of the chart square, restricted along `ι`, is smooth when `G` is smooth
over the chart. -/
theorem isSmooth_versalChartSubMap_fst
    (hιF : Space.IsSmooth B P.left.1 P.left.2 (ι ≫ terminal.from F)) :
    AlgebraicStacks.IsSmooth B S hS
      (algebraicSpaceStackMap.{u, w} B S hS (Space.isAlgebraicSpace_relocalizePresheaf B S hS P G
          hG)
          (Space.isAlgebraicSpace_relocalizePresheaf B S hS P F hF)
          ((OverShriek.relocalizePresheafFunctor P.hom).map ι) ≫
        versalChartEquivMap B S hS 𝒳 a x F e hF ≫ (versalChartSquare B S hS 𝒳 a x).fst) := by
  have hGs := Space.isAlgebraicSpace_relocalizePresheaf B S hS P G hG
  have hh₀ : Space.IsSmooth B S hS (OverShriek.relocalizeToYoneda P.hom G) := by
    refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B P.left.1 S P.left.2 hS P.hom
      _ G).2 ?_
    exact Space.holdsOnEveryEtaleChart_of_isTerminal B P.left.1 P.left.2 terminalIsTerminal
      (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj P.left.2)))) _ _ hιF
  refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (algebraicSpaceStack.{u, w} B S hS _ hGs).property
    (schemeSliceStack.{u, w} B S hS P).property _ (yoneda.obj P) hGs
    (isAlgebraicSpace_yoneda B S hS P) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (schemeSliceEquivalenceOver B S hS P) _).2 ?_
  have h1 := representingMap_comp B S hS
    (𝒜 := fibredCategory B S hS ((OverShriek.relocalizePresheafFunctor P.hom).obj G))
    (ℬ := fibredCategory B S hS (versalChartBaseChange B S hS F)) (𝒞 := schemeSlice B S hS P)
    _ (versalChartBaseChange B S hS F) (yoneda.obj P)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (schemeSliceEquivalenceOver B S hS P)
    (associatedMap B S hS ((OverShriek.relocalizePresheafFunctor P.hom).map ι)).1
    (equivalenceOverInvMap B S hS (versalChartBaseChange B S hS F)
          (versalChartBaseChangeEquivalence B S hS 𝒳 a x F e) ≫
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS P (versalChartPoint B S hS 𝒳 a) (versalChartPoint_comp B S hS 𝒳 a))
          (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))).fst)
  rw [representingMap_versalChartEquivMap_fst, representingMap_associatedMap,
    relocalizeToYoneda_comp_map] at h1
  exact h1 ▸ hh₀

/-- `versalChartSubMap` followed by `x` is smooth when `G` is smooth over the chart: up to the
2-cell of
the chart square it is the smooth first projection followed by the smooth chart. -/
theorem isSmooth_versalChartSubMap_comp (ha : AlgebraicStacks.IsSmooth B S hS a)
    (hιF : Space.IsSmooth B P.left.1 P.left.2 (ι ≫ terminal.from F)) :
    AlgebraicStacks.IsSmooth B S hS
      (versalChartSubMap B S hS 𝒳 a x F e hF hG ι ≫ objectStackMap B S hS 𝒳 x) := by
  refine AlgebraicStacks.isSmooth_of_twoIso B S hS ?_
    (AlgebraicStacks.isSmooth_comp B S hS _ _
      (isSmooth_versalChartSubMap_fst B S hS 𝒳 a x F e hF hG ι hιF)
      (isSmooth_versalChartSliceMap B S hS 𝒳 a ha))
  exact Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso _
      (Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso _ (versalChartSquare B S hS 𝒳 a
          x).iso ≪≫
        (Bicategory.associator _ _ _).symm) ≪≫ (Bicategory.associator _ _ _).symm

/-- **A finite type point of the base change over a finite type point of `U`** (Stacks 06EJ).
The projection of the base change of `x` along a smooth surjective chart to `U` is smooth and
surjective, so it carries finite type points onto finite type points. -/
theorem exists_finiteTypePoint_versalChartBaseChange (ha : AlgebraicStacks.IsSmooth B S hS a)
    (hasurj : IsSurjective B S hS a)
    (u₀ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    ∃ z : Space.FieldValuedPoint B S hS (versalChartBaseChange B S hS F),
      Space.IsLocallyOfFiniteType B S hS (yonedaEquiv.symm z.value) ∧
      Space.pointsToScheme B S hS _ (Space.pointsMap B S hS _
        (versalChartProjMap B S hS 𝒳 a x F e hF) (z.class B S hS _)) = u₀ := by
  have hΛ := Space.isAlgebraicSpace_relocalizePresheaf B S hS P F hF
  set t := Space.schemePointRepresentative B S hS (𝒳.val.val.p.obj x) u₀
  have hlft : Space.IsLocallyOfFiniteType B S hS (yonedaEquiv.symm t.value) := by
    rw [show yonedaEquiv.symm t.value = yoneda.map t.value from
      yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]),
      Space.isLocallyOfFiniteType_yoneda_map_iff,
          Space.toScheme_map_schemePointRepresentative_value]
    exact hu₀.1
  have ht : t.class B S hS _ ∈ Space.finiteTypePoints B S hS (yoneda.obj (𝒳.val.val.p.obj x)) :=
    ⟨t, rfl, hlft⟩
  rw [← Space.image_finiteTypePoints_eq B S hS (versalChartProjMap B S hS 𝒳 a x F e hF) hΛ
    (isAlgebraicSpace_yoneda B S hS _)
    (Space.isLocallyOfFiniteType_of_isSmooth B S hS (isSmooth_versalChartProjMap B S hS 𝒳 a x F e
        hF ha))
    (isSurjective_versalChartProjMap B S hS 𝒳 a x F e hF hasurj)] at ht
  obtain ⟨_, ⟨z, rfl, hzlft⟩, hz⟩ := ht
  refine ⟨z, hzlft, ?_⟩
  rw [hz, Space.pointsToScheme_class]
  exact Space.schemePointRepresentative_point B S hS _ u₀

include hG in
/-- **The open image of a smooth open of the base change carries `x` smoothly.** If `ι : G ⟶ F` is
smooth and `G` is smooth over the chart, the image in `|(Sch/U)|` of the points of `G` is an open
set on which `x` is smooth, and it contains the image of every point of `G`. -/
theorem exists_isOpen_isSmooth_versalChartSub (ha : AlgebraicStacks.IsSmooth B S hS a)
    (hι : Space.IsSmooth B P.left.1 P.left.2 ι)
    (hιF : Space.IsSmooth B P.left.1 P.left.2 (ι ≫ terminal.from F))
    (g : Space.points B S hS ((OverShriek.relocalizePresheafFunctor P.hom).obj G)) :
    ∃ (Ω : Set (points B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x)).val
        (schemeFibredCategory B S hS (𝒳.val.val.p.obj x)).property))
      (hΩ : @IsOpen _ (pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x))) Ω),
      AlgebraicStacks.IsSmooth B S hS
        ((openSubstackOfPoints (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)) Ω hΩ).inclusion ≫
          objectStackMap B S hS 𝒳 x) ∧
      letI := pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x))
      (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x)).symm
        (Space.pointsToScheme B S hS _ (Space.pointsMap B S hS _
          (versalChartProjMap B S hS 𝒳 a x F e hF)
          (Space.pointsMap B S hS _ ((OverShriek.relocalizePresheafFunctor P.hom).map ι) g))) ∈ Ω
              := by
  have hc := isSmooth_versalChartSubMap B S hS 𝒳 a x F e hF hG ι ha hι
  refine ⟨_, isOpen_range_pointsMap_of_isSmooth B S hS _ hc,
    isSmooth_openImage_inclusion_comp B S hS _ _ hc
      (isSmooth_versalChartSubMap_comp B S hS 𝒳 a x F e hF hG ι ha hιF), ?_⟩
  let := pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x))
  let Gs := (OverShriek.relocalizePresheafFunctor P.hom).obj G
  let Fs := versalChartBaseChange B S hS F
  refine ⟨spacePointMap B S hS Gs (fibredCategory B S hS Gs)
    (representingEquivalence B S hS Gs (fibredCategory B S hS Gs)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).functor g, ?_⟩
  refine ((pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x)).eq_symm_apply).2 ?_
  have h1 := spacePointMap_representing_naturality B S hS Gs Fs (fibredCategory B S hS Gs)
    (fibredCategory B S hS Fs) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (associatedMap B S hS ((OverShriek.relocalizePresheafFunctor P.hom).map ι)).1 g
  rw [representingMap_associatedMap] at h1
  have h2 := spacePointMap_representing_naturality B S hS Fs
    (yoneda.obj (𝒳.val.val.p.obj x)) (fibredCategory B S hS Fs)
    (schemeFibredCategory B S hS (𝒳.val.val.p.obj x))
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representedChart B S hS (𝒳.val.val.p.obj x)) (versalChartProj B S hS 𝒳 a x F e hF).hom
    (Space.pointsMap B S hS Gs ((OverShriek.relocalizePresheafFunctor P.hom).map ι) g)
  have h3 := pointsHomeomorphScheme_representedChartPointMap B S hS (𝒳.val.val.p.obj x)
    (Space.pointsMap B S hS Fs (versalChartProjMap B S hS 𝒳 a x F e hF)
      (Space.pointsMap B S hS Gs ((OverShriek.relocalizePresheafFunctor P.hom).map ι) g))
  refine Eq.trans ?_ h3
  congr 1
  refine Eq.trans ?_ h2.symm
  refine (pointsMap_comp B S hS _ _ (h𝒴 := (fibredCategory B S hS Fs).property) _ _ _ _).symm.trans
      ?_
  exact congrArg _ h1.symm

include hF e in
/-- **The finite type point of the base change, read over the chart, is a finite type point.** A
field-valued point of `Λ_P F` which is locally of finite type over `S` — that is, over `U` — gives
a field-valued point of `F` over `P` which is locally of finite type: its morphism to `P` is
locally of finite type because its morphism to `S` is, and local finite type of `Spec K ⟶ F`
follows by cancellation. -/
theorem isFiniteTypePoint_descendFieldValuedPoint
    [LocallyOfFiniteType (B.inclusion.map (𝒳.val.val.p.obj x).hom)]
    (ha : AlgebraicStacks.IsSmooth B S hS a)
    (q : Space.FieldValuedPoint B S hS (versalChartBaseChange B S hS F))
    (hq : Space.IsLocallyOfFiniteType B S hS (yonedaEquiv.symm q.value)) :
    Space.IsFiniteTypePoint B P.left.1 P.left.2 F
      ((descendFieldValuedPoint B S hS q).class B P.left.1 P.left.2 F) := by
  refine ⟨descendFieldValuedPoint B S hS q, rfl, ?_⟩
  have hΛ := Space.isAlgebraicSpace_relocalizePresheaf B S hS P F hF
  let φ := yonedaEquiv.symm q.value ≫ versalChartProjMap B S hS 𝒳 a x F e hF
  have hφ : Space.IsLocallyOfFiniteType B S hS φ :=
    Space.isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS _) hΛ
      (isAlgebraicSpace_yoneda B S hS _) _ _ hq
      (Space.isLocallyOfFiniteType_of_isSmooth B S hS
        (isSmooth_versalChartProjMap B S hS 𝒳 a x F e hF ha))
  let g := yoneda.preimage φ
  have hg : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
    (Space.isLocallyOfFiniteType_yoneda_map_iff B S hS g).1 (by rw [yoneda.map_preimage]; exact hφ)
  have hscheme : (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map (𝒳.val.val.p.obj x).hom =
      q.toBase :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w g))
  have hψ : q.toBase = q.value.1.1.hom ≫ P.hom.hom := (congrArg (fun k => k.hom) q.value.2).symm
  have : LocallyOfFiniteType (q.value.1.1.hom ≫ P.hom.hom) := by
    rw [← hψ, ← hscheme]
    infer_instance
  have hψlft : LocallyOfFiniteType q.value.1.1.hom := locallyOfFiniteType_of_comp _ P.hom.hom
  let k : (descendFieldValuedPoint B S hS q).siteObject B P.left.1 P.left.2 F ⟶
      Over.mk (𝟙 (B.obj P.left.2)) := Over.homMk ⟨q.value.1.1.hom⟩ (Category.comp_id _)
  have hk : Space.IsLocallyOfFiniteType B P.left.1 P.left.2 (yoneda.map k) :=
    (Space.isLocallyOfFiniteType_yoneda_map_iff B P.left.1 P.left.2 k).2 hψlft
  have hcomp : Space.IsLocallyOfFiniteType B P.left.1 P.left.2
      (yonedaEquiv.symm (descendFieldValuedPoint B S hS q).value ≫ terminal.from F) :=
    Space.holdsOnEveryEtaleChart_of_isTerminal B P.left.1 P.left.2
      (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj P.left.2)))) terminalIsTerminal
      (yoneda.map k) _ hk
  exact Space.isLocallyOfFiniteType_of_comp B P.left.1 P.left.2 (isAlgebraicSpace_yoneda B _ _ _)
    hF (Space.isAlgebraicSpace_terminal B P.left.1 P.left.2) _ _ hcomp

include hF in
/-- **The point of `U` under the descended point is `u₀`**, in the form Stacks 0CXM asks for: the
`U`-component of the object of the 2-fibre product named by the descended point carries the
closed point of its field to `u₀`. -/
theorem descendFieldValuedPoint_lies_over
    (q : Space.FieldValuedPoint B S hS (versalChartBaseChange B S hS F))
    (u₀ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))
    (hq : Space.pointsToScheme B S hS _ (Space.pointsMap B S hS _
        (versalChartProjMap B S hS 𝒳 a x F e hF) (q.class B S hS _)) = u₀) :
    letI : Category (TwoFibreProductOver (Over.map P.hom)
      (Over.forget (𝒳.val.val.p.obj x)) 𝒳.val.val.p (versalChartPoint B S hS 𝒳 a)
      (Functor.TwoYoneda.liftBased 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (𝒳.val.val.p.obj x) ⟨x, rfl⟩).toFunctor) :=
          TwoFibreProductOver.instCategory
    let Pz := e.inv.functor.obj ⟨(descendFieldValuedPoint B S hS q).siteObject,
      Discrete.mk (descendFieldValuedPoint B S hS q).value⟩
    ∃ hP : Pz.x = (descendFieldValuedPoint B S hS q).siteObject,
      (B.inclusion.map ((eqToHom (Pz.hx.trans Pz.hy.symm) ≫ Pz.y.hom).left))
        ((B.inclusion.map (eqToHom (congrArg Over.left hP).symm))
          (IsLocalRing.closedPoint (descendFieldValuedPoint B S hS q).carrier)) = u₀ := by
  intro Pz
  let : Category (TwoFibreProductOver (Over.map P.hom)
      (Over.forget (𝒳.val.val.p.obj x)) 𝒳.val.val.p (versalChartPoint B S hS 𝒳 a)
      (Functor.TwoYoneda.liftBased 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (𝒳.val.val.p.obj x) ⟨x, rfl⟩).toFunctor) :=
    TwoFibreProductOver.instCategory
  have hP : Pz.x = (descendFieldValuedPoint B S hS q).siteObject :=
    congrArg (fun G => G.obj ⟨(descendFieldValuedPoint B S hS q).siteObject,
      Discrete.mk (descendFieldValuedPoint B S hS q).value⟩) e.inv.w
  refine ⟨hP, ?_⟩
  have hobj : (versalChartBaseChangeEquivalence B S hS 𝒳 a x F e).inv.functor.obj
      ⟨q.siteObject, Discrete.mk q.value⟩ = Pz := by
    simp only [versalChartBaseChangeEquivalence, relocalizeFibreEquivalence,
      StacksRepresentableCFG.EquivalenceOver.ofEq_inv_functor]
    rfl
  have hm := morphismSpaceEquiv_app_sectionOfObj B S hS
    (fibredCategory B S hS (versalChartBaseChange B S hS F))
    (schemeFibredCategory B S hS (𝒳.val.val.p.obj x)) (versalChartBaseChange B S hS F)
    (yoneda.obj (𝒳.val.val.p.obj x)) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver (𝒳.val.val.p.obj x))
    ⟨CatFiberedInGroupoids.homFunctor (versalChartProj B S hS 𝒳 a x F e hF).hom,
      CatFiberedInGroupoids.homFunctor_comp_p (versalChartProj B S hS 𝒳 a x F e hF).hom⟩
    (⟨q.siteObject, Discrete.mk q.value⟩ : (presheafOfCategories
      (versalChartBaseChange B S hS F ⋙ typeToCat)).obj) rfl
  have hm2 := hm.trans (sectionOfObj_sliceElementsEquivalenceOver _ _)
  have hq2 := (congrArg (fun (m : q.siteObject B S hS _ ⟶ 𝒳.val.val.p.obj x) =>
    (BigFppfOver.toScheme B S hS).map m (IsLocalRing.closedPoint q.carrier)) hm2).symm.trans hq
  have hOy : ((versalChartBaseChangeEquivalence B S hS 𝒳 a x F e).inv.functor.obj
      ⟨q.siteObject, Discrete.mk q.value⟩).y = Pz.y := congrArg (fun P => P.y) hobj
  have hsub : ∀ a b : (BigFppfOver.toScheme B S hS).obj (q.siteObject B S hS _), a = b :=
    fun a b => Deformation.Artin.subsingleton_spec_of_isArtinianRing q.carrier a b
  exact toScheme_map_apply_eq_of_eq B S hS (T := 𝒳.val.val.p.obj x) (W := q.siteObject B S hS _)
    (A := (Over.map P.hom).obj Pz.x) hOy
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (versalChartProj B S hS 𝒳 a x F e
        hF).hom)
      (⟨q.siteObject, Discrete.mk q.value⟩ : (presheafOfCategories
        (versalChartBaseChange B S hS F ⋙ typeToCat)).obj))
    (Pz.hx.trans Pz.hy.symm) hsub _ _ hq2

end Chart


/-! ### From an open substack of a scheme to an open subscheme -/

section OpenSubscheme

/-- **Smoothness on an open set of points of `(Sch/U)` through a point gives smoothness on an
open subscheme of `U` through it.** If `x : (Sch/U) ⟶ 𝒳` is smooth on the open substack cut out by
an open set `Ω` of points containing the point of `u₀`, then the points of `U` whose point lies in
`Ω` form an open subscheme `U' ∋ u₀`, and `U' → U → 𝒳` is smooth: it factors through that open
substack by a 1-morphism which is smooth, being an open immersion after the inclusion. -/
theorem exists_isRelativelySmooth_restrict_of_openSubstackOfPoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : 𝒳.val.val.obj)
    (Ω : Set (points B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x)).val
      (schemeFibredCategory B S hS (𝒳.val.val.p.obj x)).property))
    (hΩ : @IsOpen _ (pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x))) Ω)
    (hZ : AlgebraicStacks.IsSmooth B S hS
      ((openSubstackOfPoints (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)) Ω hΩ).inclusion ≫
        objectStackMap B S hS 𝒳 x))
    (u₀ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))
    (hu₀ : letI := pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x))
      (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x)).symm u₀ ∈ Ω) :
    ∃ V : (𝒳.val.val.p.obj x).left.obj.Opens, u₀ ∈ V ∧
      IsRelativelySmooth B S hS
        (schemeFibredCategoryMap B S hS (BigFppfOver.openSubHom B S hS (𝒳.val.val.p.obj x) V) ≫
          objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) := by
  let := pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x))
  let V : (𝒳.val.val.p.obj x).left.obj.Opens :=
    ⟨(pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x)).symm ⁻¹' Ω,
      hΩ.preimage (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x)).symm.continuous⟩
  refine ⟨V, hu₀, ?_⟩
  let g := BigFppfOver.openSubHom B S hS (𝒳.val.val.p.obj x) V
  let gs : schemeStack.{u, w} B S hS (BigFppfOver.openSubObj B S hS (𝒳.val.val.p.obj x) V) ⟶
      schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) := schemeStackMap.{u, w} B S hS g
  have hgsm : AlgebraicStacks.IsSmooth B S hS gs := by
    refine hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)).property
      (schemeFibredCategoryMap B S hS g)
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g) ?_
    refine hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS _ g ?_
    refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Smooth.isEtaleLocalOnSourceAndTarget g).2 ?_
    change Smooth V.ι
    infer_instance
  have hfac : ∀ o, (openSubstackOfPoints (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)) Ω
      hΩ).property (gs.hom.hom.toFunctor.obj o) := by
    intro o
    rw [openSubstackOfPoints_property, pointsWithin_obj_iff]
    intro r _
    have hnat := pointsHomeomorphScheme_naturality B S hS g
      (pointClass B S hS _ (schemeFibredCategory B S hS _).property r)
    have hmem : (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x))
        (pointsMap B S hS _ (schemeFibredCategory B S hS _).property
          (schemeFibredCategory B S hS _).property (schemeFibredCategoryMap B S hS g).hom
          (pointClass B S hS _ (schemeFibredCategory B S hS _).property r)) ∈ V := by
      rw [hnat]
      change V.ι _ ∈ V
      exact (V.ι_apply _).symm ▸ Subtype.property _
    have h2 := Homeomorph.symm_apply_apply (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x))
      (pointsMap B S hS _ (schemeFibredCategory B S hS _).property
          (schemeFibredCategory B S hS _).property (schemeFibredCategoryMap B S hS g).hom
          (pointClass B S hS _ (schemeFibredCategory B S hS _).property r))
    exact h2 ▸ hmem
  have hw : AlgebraicStacks.IsSmooth B S hS
      ((openSubstackOfPoints (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)) Ω hΩ).factor
        B S hS gs hfac) :=
    OpenSubstack.isSmooth_of_isSmooth_comp_inclusion B S hS _ _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _) hgsm
  have hcomp : AlgebraicStacks.IsSmooth B S hS (gs ≫ objectStackMap B S hS 𝒳 x) := by
    rw [← OpenSubstack.factor_comp_inclusion B S hS _ gs hfac, Category.assoc]
    exact AlgebraicStacks.isSmooth_comp B S hS _ _ hw hZ
  have hrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)
    (gs ≫ objectStackMap B S hS 𝒳 x).hom
  exact ⟨hrep, (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
    (fun _ _ k => Space.IsSmooth B S hS k) (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (schemeStack.{u, w} B S hS _).property 𝒳.property _ hrep).1 hcomp⟩

end OpenSubscheme

/-! ### Stacks 0DQZ, (1) ⟹ (4) -/

/-- **Stacks 0DQZ, (1) ⟹ (4).** In the versal situation, let `x` be an object of `𝒳` over a
scheme `U` locally of finite type over `S` and let `u₀ ∈ U` be a finite type point at which `x`
is versal. Then there is an open neighbourhood `U' ⊆ U` of `u₀` such that `x|_{U'} : U' → U → 𝒳`
is smooth.

The proof is the source's. Choose a smooth surjection `y : V → 𝒳` from a scheme (which is then
locally of finite type over `S`), let `Z = V ×_𝒳 U` be represented by the algebraic space `F` over
`V`, and pick a finite type point `z₀` of `Z` over `u₀` (**Stacks 06EJ**). By Artin's Axioms,
**Stacks 0CXM** — whose (RS) hypothesis is **Stacks 07WQ** and whose diagonal hypotheses are those
of an algebraic stack — `Z ⟶ V` is smooth at `z₀`, that is on an open `W ∋ z₀`. The image `U'` of
`W` in `U` is open, `W ⟶ U'` is smooth and surjective, and `W ⟶ U' → 𝒳` is `W ⟶ V → 𝒳`, which is
smooth; so `U' → 𝒳` is smooth (smoothness descends along a smooth surjection, **Stacks 0AHD**). -/
theorem exists_isRelativelySmooth_restrict_of_isVersalAt (D : VersalSituation.{u, w})
    (x : D.𝒳.val.val.obj)
    [LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom]
    (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : Deformation.Artin.IsVersalAt ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x)
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x rfl) :
    ∃ V : (D.𝒳.val.val.p.obj x).left.obj.Opens, u₀ ∈ V ∧
      IsRelativelySmooth D.B D.S D.hS
        (schemeFibredCategoryMap D.B D.S D.hS
            (BigFppfOver.openSubHom D.B D.S D.hS (D.𝒳.val.val.p.obj x) V) ≫
          objectMorphism D.B D.S D.hS D.𝒳.val (Functor.Fiber.mk (a := x) rfl)) := by
  obtain ⟨P, a, ha, hasurj⟩ := exists_smooth_surjective_schemeStack D.B D.S D.hS D.𝒳
  have : LocallyOfFiniteType (D.B.inclusion.map P.hom) :=
    locallyOfFiniteType_of_isSmooth_schemeStack D.B D.S D.hS D.𝒳 D.locallyFiniteType P a ha
  have : LocallyOfFiniteType (D.B.inclusion.map (D.𝒳.val.val.p.obj x).hom) :=
    ‹LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom›
  obtain ⟨F, hF, ⟨e⟩⟩ := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} D.B D.S D.hS
    D.𝒳.property (isRepresentableByAlgebraicSpace_schemeFibredCategory D.B D.S D.hS _)
    (objectMorphism D.B D.S D.hS D.𝒳.val (Functor.Fiber.mk (a := x) rfl)) P
    (versalChartPoint D.B D.S D.hS D.𝒳 a) (versalChartPoint_comp D.B D.S D.hS D.𝒳 a)
  obtain ⟨q, hqlft, hqT⟩ :=
    exists_finiteTypePoint_versalChartBaseChange D.B D.S D.hS D.𝒳 a x F e hF ha hasurj u₀ hu₀
  have hz₀ := isFiniteTypePoint_descendFieldValuedPoint D.B D.S D.hS D.𝒳 a x F e hF ha q hqlft
  have hzu := descendFieldValuedPoint_lies_over D.B D.S D.hS D.𝒳 a x F e hF q u₀ hqT
  have hΔ := SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack D.B D.S D.hS D.𝒳.val
    D.𝒳.property
  obtain ⟨W, hW, w₀, hw₀, hWsm⟩ :=
    Deformation.Artin.BaseChange.isSmoothAt_baseChange_of_isVersalAt D.B D.S D.hS D.𝒳.val hΔ
      (isLocallyOfFiniteType_of_iso_isomPresheaf.{u, w} D.B D.S D.hS D.𝒳.val D.𝒳.property)
      (Deformation.Artin.satisfiesRS_of_isAlgebraicStack D.B D.S D.hS D.𝒳)
      (D.𝒳.val.val.p.obj x) P x rfl u₀ hu₀ (versalChartPoint D.B D.S D.hS D.𝒳 a)
      (versalChartPoint_comp D.B D.S D.hS D.𝒳 a) F hF e (descendFieldValuedPoint D.B D.S D.hS q)
          hz₀ hzu
      hversal
  have hι : Space.IsSmooth D.B P.left.1 P.left.2 W.ι :=
    Space.isSmooth_of_isEtale D.B P.left.1 P.left.2 hF
      (Space.isEtale_of_isOpenImmersion D.B P.left.1 P.left.2 hW.2)
  obtain ⟨Ω, hΩ, hZsm, hmem⟩ := exists_isOpen_isSmooth_versalChartSub D.B D.S D.hS D.𝒳 a x F e hF
    hW.1 W.ι ha hι hWsm (liftPoints D.B D.S D.hS w₀)
  rw [pointsMap_liftPoints, hw₀, liftPoints_descend, hqT] at hmem
  exact exists_isRelativelySmooth_restrict_of_openSubstackOfPoints D.B D.S D.hS D.𝒳 x Ω hΩ hZsm u₀
    hmem

/-! ### Condition (4): smoothness on a neighbourhood -/

/-- **Stacks 0DQZ, the equivalence of (1) and (4).** In the versal situation, let `x` be an object
of `𝒳` over a scheme `U` locally of finite type over `S`, and let `u₀ ∈ U` be a finite type point.
Then `x` is versal at `u₀` exactly when there is an open neighbourhood `U' ⊆ U` of `u₀` such that
`x|_{U'} : U' → 𝒳` is smooth.

The open subscheme `U'` is read as an object of the site by
`AlgebraicGeometry.BigFppfOver.openSubObj`, and `x|_{U'}` is the composite of its inclusion
`U' → U` with the 1-morphism `x : U → 𝒳` of the 2-Yoneda lemma; it is representable by algebraic
spaces, and smooth is meant in the sense of Stacks 04XB.

The implication (4) ⟹ (1) is
`AlgebraicGeometry.Stack.isVersalAt_of_exists_isRelativelySmooth_restrict`
(Stacks 07WK, case (3), at the residue point of `u₀` in `U'`, and versality is unchanged by
restriction to an open subscheme); (1) ⟹ (4) is
`AlgebraicGeometry.Stack.exists_isRelativelySmooth_restrict_of_isVersalAt` (Stacks 0CXM along a
smooth surjective presentation of `𝒳`, Stacks 06EJ, and descent of smoothness along a smooth
surjection). -/
@[stacks 0DQZ "the equivalence of (1) and (4): x is versal at u₀ exactly when there is an open \
neighbourhood U' ⊆ U of u₀ such that x|_{U'} : U' → 𝒳 is smooth"]
theorem isVersalAt_iff_exists_isRelativelySmooth_restrict (D : VersalSituation.{u, w})
    (x : D.𝒳.val.val.obj)
    [LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom]
    (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    Deformation.Artin.IsVersalAt ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x)
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x rfl ↔
      ∃ V : (D.𝒳.val.val.p.obj x).left.obj.Opens, u₀ ∈ V ∧
        IsRelativelySmooth D.B D.S D.hS
          (schemeFibredCategoryMap D.B D.S D.hS
              (BigFppfOver.openSubHom D.B D.S D.hS (D.𝒳.val.val.p.obj x) V) ≫
            objectMorphism D.B D.S D.hS D.𝒳.val (Functor.Fiber.mk (a := x) rfl)) := by
  refine ⟨exists_isRelativelySmooth_restrict_of_isVersalAt D x u₀ hu₀, fun h => ?_⟩
  have : LocallyOfFiniteType
      (((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecResidueField u₀) := hu₀.1
  exact isVersalAt_of_exists_isRelativelySmooth_restrict D.B D.S D.hS D.𝒳.val x u₀
    inferInstance h

end AlgebraicGeometry.Stack

end
