module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.FieldPointImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteTypeSupplement
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentableSupplement
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismSupplement
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafVertHom
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf
public import StacksFrontier.CategoryTheory.TwoYoneda.RepresentedPoint
public import StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange

/-!
# Smoothness from smoothness at the finite type points

An open condition on the points of an algebraic space that holds at every finite type point
holds everywhere, because the complement of the locus where it holds is closed, hence locally
closed, and a nonempty locally closed set of points contains a finite type point.

The second half of the file de-abstracts the relative-property form of local finite type of the
diagonal into the isomorphism-sheaf form: the shape in which the smoothness criterion for a base
change of a versal object asks for it.

## Main results

* `AlgebraicGeometry.Space.isSmooth_of_isSmoothAt_finiteTypePoints`.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_terminal_of_isLocallyOfFiniteType_diagonal`.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 0CXI](https://stacks.math.columbia.edu/tag/0CXI)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

section SmoothFromFiniteTypePoints

attribute [local instance] pointTopology

/-- **A morphism of algebraic spaces smooth at every finite type point of its source is
smooth.** The smooth locus is open by Stacks 03BZ, so its complement is closed and therefore
locally closed; were it nonempty it would contain a finite type point by Stacks 06EK, which the
hypothesis forbids.  Hence every point of the source is a smooth point, and that is one of the
equivalent formulations of smoothness in Stacks 03ZF. -/
theorem isSmooth_of_isSmoothAt_finiteTypePoints
    {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B W hW X) (hY : IsAlgebraicSpace B W hW Y) (g : X ⟶ Y)
    (hpt : ∀ z : points B W hW X, IsFiniteTypePoint B W hW X z → IsSmoothAt B W hW g z) :
    IsSmooth B W hW g := by
  refine ((isSmooth_tfae B W hW hX hY g).out 2 1).mp fun z => ?_
  by_contra hz
  obtain ⟨w, hwmem, hwft⟩ := inter_finiteTypePoints_nonempty B W hW X hX
    (T := {z : points B W hW X | IsSmoothAt B W hW g z}ᶜ)
    (isOpen_setOf_isSmoothAt B W hW hX g).isClosed_compl.isLocallyClosed ⟨z, hz⟩
  exact hwmem (hpt w hwft)

end SmoothFromFiniteTypePoints

/-- **The structure map of a field-valued point of an algebraic space locally of finite type
over `W` is locally of finite type.** The field-valued point is a morphism of algebraic spaces
from a representable one, so composing it with the structural morphism of the space gives the
structural morphism of the representable, which is the morphism of schemes in question. -/
theorem locallyOfFiniteType_fieldValuedPoint_toBase
    {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B W hW F)
    (hFlft : IsLocallyOfFiniteType B W hW
      (terminal.from F : F ⟶ ⊤_ ((BigFppfOver B W hW)ᵒᵖ ⥤ Type u)))
    (p : FieldValuedPoint B W hW F)
    (hp : IsLocallyOfFiniteType B W hW (yonedaEquiv.symm p.value)) :
    LocallyOfFiniteType p.toBase := by
  have hcomp := isLocallyOfFiniteType_comp B W hW
    (isAlgebraicSpace_yoneda B W hW (p.siteObject B W hW F)) hF (isAlgebraicSpace_terminal B W hW)
    (yonedaEquiv.symm p.value) (terminal.from F) hp hFlft
  rw [show yonedaEquiv.symm p.value ≫ (terminal.from F : F ⟶ ⊤_ _) =
      terminal.from (yoneda.obj (p.siteObject B W hW F)) from terminal.hom_ext _ _] at hcomp
  refine (isLocallyOfFiniteType_yoneda_map_iff B W hW
    (Over.homMk (p.siteObject B W hW F).hom :
      p.siteObject B W hW F ⟶ Over.mk (𝟙 (B.obj hW)))).mp ?_
  exact holdsOnEveryEtaleChart_of_isTerminal B W hW terminalIsTerminal
    (Over.mkIdTerminal.isTerminalObj yoneda _) _ _ hcomp

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))

/-- **The every-étale-chart condition for the structural morphism of a representing algebraic
space, read over `S` or over `V`.** The relative property of Stacks 03YK asks for a property of
the morphism `AlgebraicGeometry.algebraicSpaceMap` of algebraic spaces over `S`; for an
every-étale-chart condition that is the same as the condition on the structural morphism of the
presheaf over `V` itself, by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`. -/
theorem holdsOnEveryEtaleChart_algebraicSpaceMap_iff (P : MorphismProperty Scheme.{u})
    (V : BigFppfOver B S hS) (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B V.left.1 V.left.2 F) :
    Space.HoldsOnEveryEtaleChart B S hS P
        (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom ↔
      Space.HoldsOnEveryEtaleChart B V.left.1 V.left.2 P
        (terminal.from F : F ⟶ ⊤_ ((BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ g => Space.HoldsOnEveryEtaleChart B S hS P g.hom
  have _ : Q.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso B S hS P
  have hQ := prop_algebraicSpaceMap_iff B S hS Q V F hF
  have hR := Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B V.left.1 S V.left.2 hS V.hom P F
  exact ⟨fun h => Space.holdsOnEveryEtaleChart_of_isTerminal B V.left.1 V.left.2
      (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _ (hR.mp (hQ.mp h)),
    fun h => hQ.mpr (hR.mpr (Space.holdsOnEveryEtaleChart_of_isTerminal B V.left.1 V.left.2
      terminalIsTerminal (Over.mkIdTerminal.isTerminalObj yoneda _) _ _ h))⟩

/-- **The isomorphism-sheaf form of local finite type of the diagonal.** The relative property
of Stacks 03YK for `Δ : 𝒳 ⟶ 𝒳 × 𝒳` says that every algebraic space representing a base change
of `Δ` is locally of finite type over `S`; this reads it off, for a base change taken along the
point of `𝒳 × 𝒳` over `T` with components `a` and `b`, as local finite type over `T` itself of
the structural morphism of any algebraic space isomorphic to `Isom(a, b)`.

The point of `𝒳 × 𝒳` is assembled from `a` and `b` by
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.pairFunctor`, and the base change of `Δ`
along it is the presheaf of vertical morphisms between the two components, which is `Isom(a, b)`
by Stacks 045G.  Passing from the property over `S` to the property over `T` is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`: the every-étale-chart
condition for the structural morphism of an algebraic space does not depend on the base it is
read over. -/
theorem isLocallyOfFiniteType_terminal_of_isLocallyOfFiniteType_diagonal
    (hΔ : HasRepresentableDiagonal B S hS 𝒳)
    (hlft : HasRelativeProperty.{u, max u v, max (u + 1) v w, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS)
      (diagonal.{u, v, w} B S hS 𝒳) hΔ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ (T : BigFppfOver B S hS) (a b : 𝒳.val.p.Fiber T)
      (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B T.left.1 T.left.2 G →
      Nonempty (G ⋙ uliftFunctor.{max u v, u} ≅
        ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
          uliftFunctor.{u, max u v}) →
      Space.IsLocallyOfFiniteType B T.left.1 T.left.2
        (terminal.from G : G ⟶ ⊤_ ((BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)) := by
  have hp := 𝒳.isFiberedInGroupoids
  have hpf : 𝒳.val.p.IsFibered := hp.isFibered
  have hri : (Space.locallyOfFiniteTypeProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := Space.locallyOfFiniteTypeProperty B S hS)
  intro T a b G hG ⟨i⟩
  -- the point of `𝒳 × 𝒳` over `T` whose two components are `a` and `b`
  have h₁ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p T a
  have h₂ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p T b
  have hY : pairFunctor h₁ h₂ ⋙ ProdP 𝒳.val.p = Over.map T.hom := pairFunctor_comp h₁ h₂
  -- the base change of the diagonal along it is `Isom(a, b)` (Stacks 045G)
  have c : vertHomPresheaf hp hY ≅
      (Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b :=
    Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.p T a b hp
  have hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom) 𝒳.val.p (ProdP 𝒳.val.p)
        (pairFunctor h₁ h₂) (Diag 𝒳.val.p))
      (presheafOfCategories (G ⋙ typeToCat)).p) :=
    (nonempty_equivalenceOver_fst_iff hp hY G).2
      ⟨(Functor.isoWhiskerRight c uliftFunctor.{u, max u v}).trans i.symm⟩
  exact (holdsOnEveryEtaleChart_algebraicSpaceMap_iff B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) T G hG).mp (hlft T (pairFunctor h₁ h₂) hY G hG hE)

section Versal

-- The slice functor `Over.post`, fibres of a functor and their formation, the 2-Yoneda lift and
-- the projection of the category attached to a presheaf of categories are plain `def`s, so goals
-- mentioning an object of a fibre, an object of the site read in `Over S`, or the base of a
-- section of the representing presheaf are not type-correct at `implicit` transparency.  Naming
-- them here is what lets instance search and `exact` see through exactly these and nothing else.
attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.TwoYoneda.liftBased
  CategoryTheory.Functor.TwoYoneda.liftFunctor
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc
  CategoryTheory.Pseudofunctor.CoGrothendieck.forget

/-- **Stacks 07XY, the geometric half.** Let `𝒳` be a category fibred in groupoids over the big
fppf site of a locally Noetherian scheme `S`, with representable diagonal, satisfying (RS) and
limit preserving, and let `x` be an object of `𝒳` over a scheme `U` locally of finite type over
`S`.  If `x` is versal at every finite type point of `U`, then the 1-morphism
`(Sch/U)_{fppf} ⟶ 𝒳` attached to `x` by the 2-Yoneda lemma is smooth.

The Stacks Project deduces this from Lemma 07XT and Lemma 07XX; this proof instead routes it
through Stacks 0CXM.  By Stacks 07WI it is enough to test the relative property on affine bases
`V` locally of finite presentation over `S`, and there the base change is represented by an
algebraic space `F` over `V`.  Stacks 0CXM gives smoothness of `F ⟶ V` at every finite type
point of `F`, because such a point lies over a point of `U` which is again of finite type — the
projection `F ⟶ U` being locally of finite type by local finite type of the diagonal, Stacks
0CXI — and smoothness at every finite type point is smoothness, by Stacks 06EK. -/
theorem isRelativelySmooth_of_isVersalAt_finiteTypePoints
    [IsLocallyNoetherian S]
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u,
      max (u + 1) v w, max u v} B S hS 𝒳)
    (x : 𝒳.val.obj)
    (hfinite : LocallyOfFiniteType ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom)
    (hversal : ∀ u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left,
      AlgebraicGeometry.IsFiniteTypePoint u₀ →
      Deformation.Artin.IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
        (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl) :
    ∃ f : (schemeFibredCategory B S hS (𝒳.val.p.obj x)).val ⥤ᵇ 𝒳.val,
      Nonempty ((Functor.twoYonedaEvaluation 𝒳.val.p (𝒳.val.p.obj x)).obj f ≅
          (⟨x, rfl⟩ : 𝒳.val.p.Fiber (𝒳.val.p.obj x))) ∧
      ∃ hf : IsRepresentableByAlgebraicSpaces B S hS f,
        HasRelativePropertyBased.{u, u, u + 1, max u v, max (u + 1) v w, u} B S hS
          (Space.smoothMorphismProperty B S hS) f hf := by
  classical
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  set U : BigFppfOver B S hS := 𝒳.val.p.obj x
  let hUlft : LocallyOfFiniteType (B.inclusion.map U.hom) := hfinite
  let a : 𝒳.val.p.Fiber U := ⟨x, rfl⟩
  -- the 1-morphism of the 2-Yoneda lemma attached to `x`
  let f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val :=
    Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U a
  -- it is representable by algebraic spaces, by Stacks 045G
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp hdiag) U f
  -- the diagonal is locally of finite type, in the isomorphism-sheaf form Stacks 0CXM asks for
  have hΔlft := isLocallyOfFiniteType_terminal_of_isLocallyOfFiniteType_diagonal B S hS 𝒳 hdiag
    (isLocallyOfFiniteType_diagonal_univ.{u, v, w} B S hS 𝒳 hdiag hlimit)
  refine ⟨f, ⟨Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.p 𝒳.isFiberedInGroupoids U a⟩,
    hrep, ?_⟩
  refine hasRelativeProperty_of_affine_locallyOfFinitePresentation_univ B S hS
    (Space.smoothMorphismProperty B S hS) f hrep
    (isLimitPreservingOverTerminal_of_isLimitPreserving B S hS 𝒳 hlimit) ?_
  intro V _hVaff hVlfp y hy F hF ⟨eF⟩
  let : LocallyOfFinitePresentation (B.inclusion.map V.hom) := hVlfp
  let : LocallyOfFiniteType (B.inclusion.map V.hom) := inferInstance
  refine (holdsOnEveryEtaleChart_algebraicSpaceMap_iff B S hS
    (@AlgebraicGeometry.Smooth.{u}) V F hF).mpr ?_
  -- the base change is represented by `F` over `V`
  let e : Deformation.Artin.BaseChange.BaseChangeEquivalence B S hS 𝒳 U V x rfl y F := eF
  have hZV := Deformation.Artin.BaseChange.isLocallyOfFiniteType_twoFibreProduct_of_baseChangeEquiv
    B S hS 𝒳 hdiag hΔlft U V x rfl y hy F e
  -- smoothness at every finite type point suffices (Stacks 06EK)
  refine Space.isSmooth_of_isSmoothAt_finiteTypePoints B V.left.1 V.left.2 hF
    (Space.isAlgebraicSpace_terminal B V.left.1 V.left.2) _ ?_
  rintro z ⟨z₀, rfl, hz₀lft⟩
  -- the image of `z₀` under the projection to `U`
  let η := Deformation.Artin.BaseChange.baseChangeProjection B S hS 𝒳 U V x rfl y F e
  let s : (presheafOfCategories (F ⋙ typeToCat)).obj :=
    ⟨z₀.siteObject B V.left.1 V.left.2 F, Discrete.mk z₀.value⟩
  have hP : (e.inv.functor.obj s).x = z₀.siteObject B V.left.1 V.left.2 F :=
    congrArg (fun G => G.obj s) e.inv.w
  let g : Spec (.of z₀.carrier) ⟶ U.left.1 := B.inclusion.map (η.app s).left
  -- it is a finite type point of `U`, because `g` is locally of finite type
  have hw : g ≫ B.inclusion.map U.hom = z₀.toBase ≫ B.inclusion.map V.hom := by
    calc g ≫ B.inclusion.map U.hom
        = B.inclusion.map ((η.app s).left ≫ U.hom) := (B.inclusion.map_comp _ _).symm
      _ = B.inclusion.map ((z₀.siteObject B V.left.1 V.left.2 F).hom ≫ V.hom) :=
            congrArg B.inclusion.map (Over.w (η.app s))
      _ = z₀.toBase ≫ B.inclusion.map V.hom := B.inclusion.map_comp _ _
  have : LocallyOfFiniteType z₀.toBase :=
    Space.locallyOfFiniteType_fieldValuedPoint_toBase B V.left.1 V.left.2 hF hZV z₀ hz₀lft
  have : LocallyOfFiniteType (g ≫ B.inclusion.map U.hom) := hw ▸ inferInstance
  have hu₀ : AlgebraicGeometry.IsFiniteTypePoint (g (IsLocalRing.closedPoint z₀.carrier)) :=
    isFiniteTypePoint_of_locallyOfFiniteType g
      (locallyOfFiniteType_of_comp g (B.inclusion.map U.hom))
  -- Stacks 0CXM at that point
  exact Deformation.Artin.BaseChange.isSmoothAt_baseChange_of_isVersalAt B S hS 𝒳 hdiag hΔlft
    hRS U V x rfl _ hu₀ y hy F hF e z₀ ⟨z₀, rfl, hz₀lft⟩
    ⟨hP, (Deformation.Artin.BaseChange.baseChangeProjection_point B S hS 𝒳 U V x rfl y F e
      z₀ hP).symm⟩
    (hversal _ hu₀)

end Versal

end AlgebraicGeometry.Stack

end
