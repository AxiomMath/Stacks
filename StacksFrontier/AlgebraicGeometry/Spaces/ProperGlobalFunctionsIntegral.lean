module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAffineLine
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Integrality of the global functions of a proper algebraic space over a field

Let `k` be a field and let `X` be an algebraic space over `k` which is proper and étale-locally
reduced.  Every global regular function on `X` is then integral over `k`:
`AlgebraicGeometry.Space.isIntegralElem_globalFunctions_of_isProper`.

The argument is the one of Stacks 0A0Q read at the terminal chart.  A global function is a
morphism `q` from `X` to the relative affine line `𝔸¹` over the base, taken over the base.  The
projection of `𝔸¹` to the base is separated, so the image of `|X|` in `|𝔸¹|` is closed and the
reduced closed subspace `Z` it carries is proper over the base (Stacks 0CZG).  The inclusion of
`Z` is a closed immersion, hence affine (Stacks 07U2), and the projection of `𝔸¹` is affine, so
`Z` is affine and universally closed over the base and therefore integral over it
(Stacks 0415).  Integrality produces an affine object `W` of the site representing `Z` over the
base whose structure morphism is an integral morphism of schemes, and reducedness of `X` makes
`q` factor through `Z` (Stacks 03JJ).  So the given function is pulled back from a global
function on `W`, where integrality over `k` is Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`.

## Main results

* `AlgebraicGeometry.Space.isIntegralElem_globalFunctions_of_isProper`: **Stacks 0A0Q at the
  terminal chart.**

## Implementation notes

The ring of global functions of the algebraic space represented by an object `W` of the site is
not identified here with `Γ(W, ⊤)`;  only restriction to the identity étale chart of `W` is
used, which is a ring homomorphism into `Γ(W, ⊤)` and is injective because that chart is
surjective on points
(`AlgebraicGeometry.Space.injective_globalFunctionsChartRestriction_of_isSurjective`).  A monic
relation over `k` satisfied by the image of a function descends through an injective
homomorphism of `k`-algebras, which is
`AlgebraicGeometry.Space.AlgebraSheaf.isIntegralElem_of_injective`.

## References

* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The scalars of an affine base as a function on every chart -/

section Constants

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (F : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)

/-- The pullback of a scalar of the affine base to every scheme chart of a presheaf over that
base, as a compatible family of regular functions on all charts.  The family is compatible
because every morphism of charts is a morphism over the base;  this is
`AlgebraicGeometry.Space.baseToGlobalFunctions` with the étale charts replaced by all of
them. -/
def baseToChartFunctions (c : A) : chartFunctions B (Spec (.of A)) hA F :=
  ⟨fun j => (((Scheme.ΓSpecIso (.of A)).inv ≫
      Scheme.Γ.map (B.inclusion.map j.unop.left.hom).op).hom c),
    by
      intro U V g
      let T := CostructuredArrow.proj (yoneda : BigFppfOver B (Spec (.of A)) hA ⥤ _) F
      have hw :
          B.inclusion.map (T.map g.unop).left ≫
              B.inclusion.map (T.obj U.unop).hom =
            B.inclusion.map (T.obj V.unop).hom := by
        simpa only [← Functor.map_comp] using
          congrArg B.inclusion.map (Over.w (T.map g.unop))
      change (((Scheme.ΓSpecIso (.of A)).inv ≫
        (B.inclusion.map (T.obj U.unop).hom).appTop ≫
        (B.inclusion.map (T.map g.unop).left).appTop).hom c) =
        (((Scheme.ΓSpecIso (.of A)).inv ≫
          (B.inclusion.map (T.obj V.unop).hom).appTop).hom c)
      rw [← Scheme.Hom.comp_appTop, hw]⟩

/-- Restricting the constants of the base from all charts to the étale charts gives the
canonical homomorphism from the base ring to the global regular functions. -/
theorem chartFunctionsToSmall_baseToChartFunctions (c : A) :
    chartFunctionsToSmall B (Spec (.of A)) hA F (baseToChartFunctions A B hA F c) =
      baseToGlobalFunctions A B hA F c :=
  rfl

/-- The constants of the base pull back to the constants of the base along any morphism of
presheaves:  precomposition with a morphism does not change the underlying object of a chart,
hence does not change its structure morphism to the base. -/
theorem chartFunctionsMap_baseToChartFunctions
    {F G : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (f : G ⟶ F) (c : A) :
    chartFunctionsMap B (Spec (.of A)) hA f (baseToChartFunctions A B hA F c) =
      baseToChartFunctions A B hA G c :=
  rfl

/-- Pullback of global regular functions along a morphism of algebraic spaces over an affine
base fixes the constants of the base ring.  Restriction of an all-chart family to the étale
charts is injective, and the two sides restrict to the same all-chart family by
`AlgebraicGeometry.Space.chartFunctionsMap_baseToChartFunctions`. -/
theorem globalFunctionsMap_baseToGlobalFunctions
    {U V : AlgebraicSpaces B (Spec (.of A)) hA} (f : V ⟶ U) (c : A) :
    globalFunctionsMap B (Spec (.of A)) hA f (baseToGlobalFunctions A B hA U.obj c) =
      baseToGlobalFunctions A B hA V.obj c := by
  have key : ∀ (T : AlgebraicSpaces B (Spec (.of A)) hA),
      (globalFunctionsChartEquiv B (Spec (.of A)) hA T).val
          (baseToGlobalFunctions A B hA T.obj c) =
        baseToChartFunctions A B hA T.obj c := by
    intro T
    refine chartFunctionsToSmall_injective B (Spec (.of A)) hA T.obj T.property ?_
    rw [(globalFunctionsChartEquiv B (Spec (.of A)) hA T).2,
      chartFunctionsToSmall_baseToChartFunctions]
  refine (globalFunctionsChartEquiv B (Spec (.of A)) hA V).val.injective ?_
  rw [globalFunctionsMap_chart, key U, key V, chartFunctionsMap_baseToChartFunctions]

/-- Pullback of global regular functions along a morphism of algebraic spaces over an affine
base is a homomorphism of algebras over the base ring. -/
theorem globalFunctionsMap_algebraMap
    {U V : AlgebraicSpaces B (Spec (.of A)) hA} (f : V ⟶ U) (c : A) :
    globalFunctionsMap B (Spec (.of A)) hA f
        (algebraMap A (globalFunctions B (Spec (.of A)) hA U.obj) c) =
      algebraMap A (globalFunctions B (Spec (.of A)) hA V.obj) c := by
  rw [algebraMap_globalFunctions, algebraMap_globalFunctions]
  exact globalFunctionsMap_baseToGlobalFunctions A B hA f c

/-- Restriction of global regular functions to the identity étale chart of the algebraic space
represented by an object of the site carries the constants of the base ring to their pullbacks
along the structure morphism of that object. -/
theorem globalFunctionsChartRestriction_idEtaleChart_comp_algebraMap
    (W : BigFppfOver B (Spec (.of A)) hA) :
    (globalFunctionsChartRestriction B (Spec (.of A)) hA (schemeSpace W)
          (idEtaleChart B (Spec (.of A)) hA W)).comp
        (algebraMap A (globalFunctions B (Spec (.of A)) hA (yoneda.obj W))) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map W.hom).appTop).hom :=
  rfl

end Constants

/-! ### Stacks 0A0Q at the terminal chart -/

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- **Stacks 0A0Q at the terminal chart.**  Every global regular function on a proper,
étale-locally reduced algebraic space over a field is integral over that field. -/
theorem isIntegralElem_globalFunctions_of_isProper
    (hf : IsProper B (Spec (.of k)) hS f)
    (hred : HasEtaleLocalProperty B (Spec (.of k)) hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (a : globalFunctions B (Spec (.of k)) hS X) :
    (algebraMap k (globalFunctions B (Spec (.of k)) hS X)).IsIntegralElem a := by
  -- Step 0: notation.  The base object is not abstracted, since `f` is stated over it.
  set L : BigFppfOver B (Spec (.of k)) hS :=
    relativeAffineLine B (Spec (.of k)) hS (baseObject k B hS)
  set pr : L ⟶ baseObject k B hS :=
    relativeAffineLineProjection B (Spec (.of k)) hS (baseObject k B hS)
  set tl : L ⟶ affineLineBigFppfOver B (Spec (.of k)) hS :=
    relativeAffineLineToAffineLine B (Spec (.of k)) hS (baseObject k B hS)
  have hValg : IsAlgebraicSpace B (Spec (.of k)) hS (yoneda.obj (baseObject k B hS)) :=
    isAlgebraicSpace_yoneda B (Spec (.of k)) hS (baseObject k B hS)
  have hLalg : IsAlgebraicSpace B (Spec (.of k)) hS (yoneda.obj L) :=
    isAlgebraicSpace_yoneda B (Spec (.of k)) hS L
  have hVaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj (baseObject k B hS)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  have hLaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj L) :=
    isAffine_relativeAffineLine B (Spec (.of k)) hS (baseObject k B hS) hVaff
  have hft : IsLocallyOfFiniteType B (Spec (.of k)) hS f := hf.2.1.1
  -- Step 1: read `a` as a morphism to the relative affine line over the base.
  obtain ⟨⟨q, hqcomm⟩, hq2⟩ :
      ∃ p : { q : X ⟶ yoneda.obj L // q ≫ yoneda.map pr = f },
        p.1 ≫ yoneda.map tl =
          (globalFunctionsHomEquiv B (Spec (.of k)) hS ⟨X, hX⟩ a).hom :=
    ⟨(relativeAffineLineHomEquiv B (Spec (.of k)) hS (baseObject k B hS) X f).symm _,
      (relativeAffineLineHomEquiv B (Spec (.of k)) hS
        (baseObject k B hS) X f).apply_symm_apply _⟩
  -- Step 2: the projection of the relative affine line is separated and of finite type.
  have hsep : IsSeparated B (Spec (.of k)) hS (yoneda.map pr) :=
    isSeparated_relativeAffineLineProjection B (Spec (.of k)) hS (baseObject k B hS)
  have hprft : IsLocallyOfFiniteType B (Spec (.of k)) hS (yoneda.map pr) :=
    (isLocallyOfFiniteType_yoneda_map_iff B (Spec (.of k)) hS pr).2 (by
      rw [toScheme_map_relativeAffineLineProjection]
      -- synthesised at an abstract scheme: synthesis at the site object itself does not succeed
      exact (fun Y : Scheme.{u} => (inferInstance : LocallyOfFiniteType (𝔸(PUnit.{u + 1}; Y) ↘ Y)))
        _)
  -- Step 3: the whole of `X` is proper over the base.
  have hproperUniv :
      IsProperOver B (Spec (.of k)) hS hX hValg f hft Set.univ isClosed_univ :=
    isProper_comp B (Spec (.of k)) hS
      (isAlgebraicSpace_reducedClosedSubspace B (Spec (.of k)) hS X hX Set.univ isClosed_univ)
      hX hValg _ f
      (isProper_ι_reducedClosedSubspace B (Spec (.of k)) hS X hX Set.univ isClosed_univ) hf
  -- Step 4: Stacks 0CZG — the image of `X` in the relative affine line is closed and proper.
  have hImgClosed : IsClosed (pointsMap B (Spec (.of k)) hS X q '' Set.univ) :=
    isClosed_image_of_isProperOver B (Spec (.of k)) hS hX hLalg hValg q f (yoneda.map pr)
      hqcomm hft hprft hsep Set.univ isClosed_univ hproperUniv
  have hZproper :
      IsProperOver B (Spec (.of k)) hS hLalg hValg (yoneda.map pr) hprft
        (pointsMap B (Spec (.of k)) hS X q '' Set.univ) hImgClosed :=
    isProperOver_image_of_isSeparated B (Spec (.of k)) hS hX hLalg hValg q f (yoneda.map pr)
      hqcomm hft hprft hsep Set.univ isClosed_univ hproperUniv hImgClosed
  set Z := reducedClosedSubspace B (Spec (.of k)) hS (yoneda.obj L) hLalg
    (pointsMap B (Spec (.of k)) hS X q '' Set.univ) hImgClosed
  have hZalg : IsAlgebraicSpace B (Spec (.of k)) hS Z.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B (Spec (.of k)) hS (yoneda.obj L) hLalg _ hImgClosed
  -- Step 5: `Z` is affine over the base: a closed immersion is affine (07U2) and the
  -- projection of the relative affine line is affine, both schemes being affine (03WH).
  have hZiaff : IsAffineHom B (Spec (.of k)) hS Z.ι :=
    isAffineHom_of_isClosedImmersion B (Spec (.of k)) hS _
      (isClosedImmersion_ι_reducedClosedSubspace B (Spec (.of k)) hS hLalg _ hImgClosed)
  have hpraff : IsAffineHom B (Spec (.of k)) hS (yoneda.map pr) := by
    have := hLaff
    have := hVaff
    exact isAffineHom_yoneda_map B (Spec (.of k)) hS pr
  -- Step 6: Stacks 0415 — affine and universally closed, hence integral.
  have hint : IsIntegralHom B (Spec (.of k)) hS (Z.ι ≫ yoneda.map pr) :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B (Spec (.of k)) hS hZalg hValg _).2
      ⟨isAffineHom_comp B (Spec (.of k)) hS _ _ hZiaff hpraff, hZproper.2.2⟩
  -- Step 7: integrality gives an affine object `W` of the site representing `Z`, whose
  -- projection to the base is an integral morphism of schemes.
  obtain ⟨W, pW, iW, hpb, _, hpWint⟩ := hint (baseObject k B hS) hVaff (𝟙 _)
  have : IsIso iW := hpb.isIso_fst_of_isIso
  obtain ⟨jW, hjW⟩ : ∃ j : Z.toFunctor ⟶ yoneda.obj W, j ≫ iW = 𝟙 Z.toFunctor :=
    ⟨inv iW, IsIso.inv_hom_id iW⟩
  -- Step 8: Stacks 03JJ — `X` being reduced, it factors through `Z`.
  have hrange :
      Set.range (pointsMap B (Spec (.of k)) hS X q) ⊆
        Set.range (pointsMap B (Spec (.of k)) hS Z.toFunctor Z.ι) := by
    rw [range_pointsMap_ι_reducedClosedSubspace, Set.image_univ]
  obtain ⟨g, hg⟩ :=
    (exists_lift_closedSubspace_iff_pointsMap_range_subset B (Spec (.of k)) hS hLalg hX Z
      (isClosedSubspace_reducedClosedSubspace' B (Spec (.of k)) hS hLalg _ hImgClosed)
      hred q).2 hrange
  -- Step 9: the resulting morphism of `X` to the affine scheme `W`.
  set φ : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of k)) hS) ⟶ schemeSpace W :=
    ObjectProperty.homMk (g ≫ jW)
  -- Step 10: `a` is the pullback along `φ` of a global function on `W`.
  set m : schemeSpace W ⟶ affineLineSpace B (Spec (.of k)) hS :=
    ObjectProperty.homMk (iW ≫ Z.ι ≫ yoneda.map tl)
  set b := (globalFunctionsHomEquiv B (Spec (.of k)) hS (schemeSpace W)).symm m with hbdef
  have hab : a = globalFunctionsMap B (Spec (.of k)) hS φ b := by
    refine (globalFunctionsHomEquiv B (Spec (.of k)) hS ⟨X, hX⟩).injective ?_
    rw [globalFunctionsHomEquiv_natural, hbdef, Equiv.apply_symm_apply]
    apply ObjectProperty.hom_ext
    change (globalFunctionsHomEquiv B (Spec (.of k)) hS ⟨X, hX⟩ a).hom = (φ ≫ m).hom
    rw [← hq2]
    change q ≫ yoneda.map tl = (g ≫ jW) ≫ iW ≫ Z.ι ≫ yoneda.map tl
    rw [← Category.assoc (g ≫ jW) iW, Category.assoc g jW iW, hjW, Category.comp_id,
      ← Category.assoc g Z.ι, hg]
  -- Step 11: `Γ(W, ⊤)` is integral over `k`, hence so are `b` and `a`.
  have hpWleft : pW.left = W.hom := (Category.comp_id pW.left).symm.trans (Over.w pW)
  have : _root_.AlgebraicGeometry.IsIntegralHom (B.inclusion.map W.hom) := hpWleft ▸ hpWint
  have : IsAffine (B.inclusion.obj (B.obj hS)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  have hΓint : (((Scheme.ΓSpecIso (.of k)).inv ≫
      (B.inclusion.map W.hom).appTop).hom).IsIntegral :=
    RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv) _
      (isIntegral_appTop_of_universallyClosed _)
  have hb : (algebraMap k (globalFunctions B (Spec (.of k)) hS (yoneda.obj W))).IsIntegralElem b :=
    AlgebraSheaf.isIntegralElem_of_injective
      (globalFunctionsChartRestriction B (Spec (.of k)) hS (schemeSpace W)
        (idEtaleChart B (Spec (.of k)) hS W))
      (injective_globalFunctionsChartRestriction_of_isSurjective B (Spec (.of k)) hS
        (schemeSpace W) (idEtaleChart B (Spec (.of k)) hS W)
        (isSurjective_idEtaleChart B (Spec (.of k)) hS W))
      (globalFunctionsChartRestriction_idEtaleChart_comp_algebraMap k B hS W) (hΓint _)
  have hcomp : (globalFunctionsMap B (Spec (.of k)) hS φ).comp
        (algebraMap k (globalFunctions B (Spec (.of k)) hS (yoneda.obj W))) =
      algebraMap k (globalFunctions B (Spec (.of k)) hS X) :=
    RingHom.ext fun c => globalFunctionsMap_algebraMap k B hS φ c
  rw [hab]
  exact hcomp ▸ hb.map (globalFunctionsMap B (Spec (.of k)) hS φ)

end AlgebraicGeometry.Space

end
