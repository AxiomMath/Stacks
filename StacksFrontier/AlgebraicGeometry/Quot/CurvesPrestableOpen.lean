module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionUpperSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.Topology.Dimension.Equidimensional
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal

/-!
# The open substack of prestable curves

Stacks 0E6U produces the open substack `Curves^{prestable} ⊂ Curves` of prestable families of
curves (Stacks 0E6T): families `f : X → S` which are at-worst-nodal of relative dimension one
with `f_*𝒪_X = 𝒪_S` universally. Its proof is the identity
`Curves^{prestable} = Curves^{nodal} ∩ Curves^{h0,1}`, with the openness of the two substacks on
the right given by Stacks 0DSY and Stacks 0E6I, and the method of Section 0E0E.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_point_over_of_hasUniversallyBijectiveGlobalFunctions`:
  a family of curves with `f_*𝒪_X = 𝒪_S` universally is surjective on points.
* `AlgebraicGeometry.CurveFamily.fiberDimension_toBase_eq_one_of_isPrestableCurveFamily`: every
  fibre of a prestable family of curves has dimension one.
* `AlgebraicGeometry.isH01CurveFamily_of_isPrestableCurveFamily`:
  `Curves^{prestable} ⊂ Curves^{h0,1}`, and
  `AlgebraicGeometry.isPrestableCurveFamily_iff_isAtWorstNodal_and_isH01CurveFamily`:
  `Curves^{prestable} = Curves^{nodal} ∩ Curves^{h0,1}`.
* `AlgebraicGeometry.isOpenCurvesLocus_isPrestableCurveFamily_of`: condition (o) for
  `Curves^{prestable}`, from condition (o) for `Curves^{h0,1}` (Stacks 0E6I).
* `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of`: the open substack and
  part (1) of Stacks 0E6U, from condition (o) for `Curves^{h0,1}`.
* `AlgebraicGeometry.topologicalKrullDim_eq_one_of_mem_irreducibleComponents`: in a connected
  Noetherian `T₀` space of dimension one every irreducible component has dimension one.
* `AlgebraicGeometry.isPrestableCurveFamily_curveFamilyOfSchemeMorphism_iff_of`: part (2) of
  Stacks 0E6U read on the family of a proper scheme over a field.
* `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of_inputs`: the whole of
  Stacks 0E6U from its three inputs (parts (1) and (2) of Stacks 0E6I and the criterion for
  at-worst-nodal morphisms over a field behind part (2) of Stacks 0DSY), and
  `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of_h01Inputs` with Stacks 0E6I
  reduced to its own inputs (Stacks 0E0R at `i = 0` and Stacks 0E6B, part (a)).

## Implementation notes

`AlgebraicGeometry.curveFamilyOverFieldOfProper` is the family of curves of a proper scheme of
dimension at most one over a field: `AlgebraicGeometry.curveFamilyOfSchemeMorphism` with every
hypothesis beyond properness and the dimension bound discharged.

## References

* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A value in `WithBot ℕ∞` that is at most one and not equal to one is at most zero. -/
private theorem le_zero_of_le_one_of_ne_one {d : WithBot ℕ∞} (hle : d ≤ 1) (hne : d ≠ 1) :
    d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h : (⊤ : ℕ∞) ≤ 1 := by exact_mod_cast hle
      exact absurd (top_le_iff.mp h) ENat.one_ne_top
    | coe n =>
      have h1 : n ≤ 1 := by exact_mod_cast hle
      have hn : n ≠ 1 := fun h => hne (by subst h; rfl)
      obtain rfl : n = 0 := by lia
      exact le_rfl

namespace CurveFamily

/-- **A family of curves with `f_*𝒪_X = 𝒪_S` universally is surjective:** every point of the
base is the image of a point of the total space. -/
theorem exists_point_over_of_hasUniversallyBijectiveGlobalFunctions {X : CurveFamily B hZ}
    (hX : HasUniversallyBijectiveGlobalFunctions B hZ X)
    (s : Space.points B integerBase hZ (schemeSpace X.base).obj) :
    s ∈ Set.range (Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom) := by
  classical
  obtain ⟨p, rfl⟩ := Quot.exists_rep s
  let g : schemeSpace p.siteObject ⟶ schemeSpace X.base := schemeSpaceMap p.value
  let P := AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g
  by_contra hne
  let fst : P ⟶ X.total := ObjectProperty.homMk (pullback.fst X.toBase.hom g.hom)
  let snd : P ⟶ schemeSpace p.siteObject := ObjectProperty.homMk (pullback.snd X.toBase.hom g.hom)
  have hw : fst.hom ≫ X.toBase.hom = snd.hom ≫ g.hom := pullback.condition
  have hP : IsEmpty (Space.points B integerBase hZ P.obj) := by
    refine ⟨fun z => hne ⟨Space.pointsMap B integerBase hZ P.obj fst.hom z, ?_⟩⟩
    rw [Space.pointsMap_apply_comm B integerBase hZ hw z]
    have hsing : Space.pointsMap B integerBase hZ P.obj snd.hom z =
        (Space.FieldValuedPoint.tautological B integerBase hZ p).class B integerBase hZ _ :=
      (Space.subsingleton_points_yoneda_siteObject B integerBase hZ p).elim _ _
    rw [hsing]
    exact congrArg (Quot.mk _) (Space.FieldValuedPoint.map_tautological B integerBase hZ p)
  have hsub : Subsingleton (Space.globalFunctions' B integerBase hZ P.obj) := by
    have : Subsingleton (Space.chartFunctions B integerBase hZ P.obj) := by
      refine ⟨fun a b => Subtype.ext (funext fun j => ?_)⟩
      have : IsEmpty ((BigFppfOver.toScheme B integerBase hZ).obj j.unop.left) :=
        ⟨fun t => hP.false (Space.pointsMap B integerBase hZ _ j.unop.hom
          ((Space.pointsEquivScheme B integerBase hZ j.unop.left).symm t))⟩
      exact Subsingleton.elim
        (α := Γ((BigFppfOver.toScheme B integerBase hZ).obj j.unop.left, ⊤)) _ _
    exact (Space.globalFunctionsChartEquiv B integerBase hZ P).val.injective.subsingleton
  have hnt : Nontrivial
      (Space.globalFunctions' B integerBase hZ (schemeSpace p.siteObject).obj) := by
    let j : (CostructuredArrow yoneda (yoneda.obj p.siteObject))ᵒᵖ :=
      op (CostructuredArrow.mk (𝟙 (yoneda.obj p.siteObject)))
    let T := (BigFppfOver.toScheme B integerBase hZ).obj p.siteObject
    let t : T := Space.pointsEquivScheme B integerBase hZ p.siteObject
      ((Space.FieldValuedPoint.tautological B integerBase hZ p).class B integerBase hZ _)
    have : Nontrivial Γ(T, ⊤) := (T.presheaf.germ ⊤ t trivial).hom.domain_nontrivial
    have : Nontrivial (Space.chartFunctions B integerBase hZ (schemeSpace p.siteObject).obj) :=
      ⟨⟨1, 0, fun h => one_ne_zero (α := Γ(T, ⊤))
        (congrArg (fun a : Space.chartFunctions B integerBase hZ
          (schemeSpace p.siteObject).obj => a.val j) h)⟩⟩
    exact Equiv.nontrivial
      (Space.globalFunctionsChartEquiv B integerBase hZ (schemeSpace p.siteObject)).val.toEquiv
  have := (hX (schemeSpace p.siteObject) g).1.subsingleton
  exact false_of_nontrivial_of_subsingleton
    (Space.globalFunctions' B integerBase hZ (schemeSpace p.siteObject).obj)

/-- **An at-worst-nodal family of relative dimension one has relative dimension one** at every
point of its total space: on every pair of étale charts at the point the morphism of charts is
syntomic of relative dimension one. -/
theorem hasRelativeDimensionAt_one_of_isAtWorstNodal {X : CurveFamily B hZ}
    (hX : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ X.toBase.hom)
    (x : Space.points B integerBase hZ X.total.obj) :
    Space.HasRelativeDimensionAt (1 : ℕ∞) B integerBase hZ X.toBase.hom x := by
  intro c
  have hc := (hX c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm).1.2
    (c.sourcePoint B integerBase hZ)
  exact (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).2 (by exact_mod_cast hc)

/-- **The fibres of a prestable family of curves have dimension one.** -/
theorem fiberDimension_toBase_eq_one_of_isPrestableCurveFamily {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (s : Space.points B integerBase hZ (schemeSpace X.base).obj) :
    Space.fiberDimension B integerBase hZ X.toBase.hom s = ((1 : ℕ) : WithBot ℕ∞) := by
  have hrel := hasRelativeDimensionAt_one_of_isAtWorstNodal hX.1
  obtain ⟨x, hx⟩ := exists_point_over_of_hasUniversallyBijectiveGlobalFunctions hX.2 s
  have hle : Space.fiberDimension B integerBase hZ X.toBase.hom s ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    (Space.fiberDimension_le_iff B integerBase hZ X.toBase.hom s 1).2
      fun x' _ => ⟨1, hrel x', by simp⟩
  have hnle : ¬ Space.fiberDimension B integerBase hZ X.toBase.hom s ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    intro h
    obtain ⟨e, he, he0⟩ := (Space.fiberDimension_le_iff B integerBase hZ X.toBase.hom s 0).1 h x hx
    obtain ⟨c⟩ := Space.exists_etaleChartAtPoint B integerBase hZ X.total.property
      (schemeSpace X.base).property X.toBase.hom x
    have h1 := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).1 (hrel x c)
    have h0 := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).1 (he c)
    rw [h1] at h0
    have h10 : ((1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := h0 ▸ he0
    exact absurd (WithBot.coe_le_coe.mp h10) (by simp)
  generalize Space.fiberDimension B integerBase hZ X.toBase.hom s = d at hle hnle
  by_contra hne
  exact hnle (le_zero_of_le_one_of_ne_one hle (by simpa using hne))

/-- **The fibres of a prestable family of curves have dimension one**, in the form of
condition (1)(b) of Stacks 0E6I. -/
theorem hasFibresOfDimensionOne_of_isPrestableCurveFamily {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) : HasFibresOfDimensionOne B hZ X :=
  fiberDimension_toBase_eq_one_of_isPrestableCurveFamily hX

end CurveFamily

/-- **`Curves^{prestable} ⊂ Curves^{h0,1}`.** A prestable family of curves satisfies condition
(1)(b) of Stacks 0E6I: `f_*𝒪_X = 𝒪_S` universally, and its fibres have dimension one. -/
theorem isH01CurveFamily_of_isPrestableCurveFamily {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) : IsH01CurveFamily B hZ X :=
  ⟨hX.2, CurveFamily.hasFibresOfDimensionOne_of_isPrestableCurveFamily hX⟩

/-- **`Curves^{prestable} = Curves^{nodal} ∩ Curves^{h0,1}`.** -/
theorem isPrestableCurveFamily_iff_isAtWorstNodal_and_isH01CurveFamily (X : CurveFamily B hZ) :
    IsPrestableCurveFamily B hZ X ↔
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ X.toBase.hom ∧
        IsH01CurveFamily B hZ X :=
  ⟨fun h => ⟨h.1, isH01CurveFamily_of_isPrestableCurveFamily h⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-- **Condition (o) of Section 0E0E for `Curves^{prestable}`**, from condition (o) for
`Curves^{h0,1}` (Stacks 0E6I). -/
theorem isOpenCurvesLocus_isPrestableCurveFamily_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ)) :
    IsOpenCurvesLocus B hZ (IsPrestableCurveFamily B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := ((isOpenCurvesLocus_isAtWorstNodal B hZ).and hH01) G
  exact ⟨W, hW, fun F a =>
    (isPrestableCurveFamily_iff_isAtWorstNodal_and_isH01CurveFamily F).trans (hchar F a)⟩

/-- **Stacks 0E6U, the open substack and part (1), from condition (o) for `Curves^{h0,1}`.**
The strictly full subcategory `Curves^{prestable}` of prestable families of curves (Stacks 0E6T)
is an open substack of `Curves` — its inclusion is representable by algebraic spaces and an open
immersion — and the classifying morphism of a family of curves factors through it exactly when
the family is prestable. The input is condition (o) for `Curves^{h0,1}`, Stacks 0E6I. -/
theorem curvesPrestable_isOpenSubstack_and_factors_iff_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ)) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of hH01).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of hH01).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left)))) :=
  isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (isOpenCurvesLocus_isPrestableCurveFamily_of hH01)

/-! ### Part (2): a proper scheme of dimension at most one over a field -/

/-- **Irreducible components of a connected one-dimensional Noetherian space.** In a connected
Noetherian `T₀` space of dimension one every irreducible component has dimension one. -/
theorem topologicalKrullDim_eq_one_of_mem_irreducibleComponents {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [T0Space X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    topologicalKrullDim Z = 1 := by
  have hle : topologicalKrullDim Z ≤ 1 := hdim ▸ topologicalKrullDim_subspace_le X Z
  by_contra hne
  have h0 := le_zero_of_le_one_of_ne_one hle hne
  have : IrreducibleSpace Z := Subtype.irreducibleSpace hZ.1
  have : Subsingleton Z := Stacks.Chow.subsingleton_of_topologicalKrullDim_le_zero h0
  obtain ⟨η, hη⟩ := hZ.1.nonempty
  have hZη : ∀ x ∈ Z, x = η := fun x hx =>
    congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Z) ⟨η, hη⟩)
  let Y : Set X := ⋃ W ∈ irreducibleComponents X \ {Z}, W
  have hY : IsClosed Y :=
    ((TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).subset
      Set.sdiff_subset).isClosed_biUnion
        fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have hZY : Zᶜ = Y := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion₂.2 ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, fun h => hx ?_⟩,
        mem_irreducibleComponent⟩
      exact (Set.mem_singleton_iff.mp h) ▸ mem_irreducibleComponent
    · intro hx hxZ
      obtain ⟨W, ⟨hW, hWZ⟩, hxW⟩ := Set.mem_iUnion₂.1 hx
      have hsub : Z ⊆ W := fun z hz => (hZη z hz).trans (hZη x hxZ).symm ▸ hxW
      exact hWZ (Set.mem_singleton_iff.mpr (hZ.2 hW.1 hsub |>.antisymm hsub))
  have hclopen : IsClopen Z := ⟨isClosed_of_mem_irreducibleComponents Z hZ,
    by rw [← compl_compl Z, hZY]; exact hY.isOpen_compl⟩
  rcases isClopen_iff.1 hclopen with h | h
  · exact hZ.1.nonempty.ne_empty h
  · have hX : Subsingleton X := ⟨fun a b =>
      (hZη a (h ▸ Set.mem_univ a)).trans (hZη b (h ▸ Set.mem_univ b)).symm⟩
    exact Stacks.Chow.not_subsingleton_of_one_le_topologicalKrullDim (hdim ▸ le_rfl) hX

/-- Being at-worst-nodal of relative dimension one is unchanged by composing with the
identification of the target with the spectrum of a field. -/
private theorem isAtWorstNodalOfRelativeDimensionOne_comp_eqToHom_iff {X Y Y' : Scheme.{u}}
    (q : X ⟶ Y) (hY : Y = Y') :
    IsAtWorstNodalOfRelativeDimensionOne (q ≫ eqToHom hY) ↔
      IsAtWorstNodalOfRelativeDimensionOne q := by
  subst hY
  simp

variable (B hZ) in
/-- **Stacks 0E6U, part (2), from its two inputs, for the family of a scheme morphism.** Let
`g : T ⟶ W` be a morphism of the site with `W = Spec k` for a field `k`, inducing a family of
curves. The family is prestable exactly when the singularities of `X = T` are at-worst-nodal,
`dim(X) = 1` and `k = H⁰(X, 𝒪_X)`.

The inputs are the criterion for at-worst-nodal morphisms of relative dimension one over a field
(`hsch`, the scheme-level content of part (2) of Stacks 0DSY) and part (2) of Stacks 0E6I for
this family (`h0E6I`). The condition `k = H⁰(X, 𝒪_X)` is the bijectivity of the pullback
`Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)` of global functions along the structure morphism. -/
theorem isPrestableCurveFamily_curveFamilyOfSchemeMorphism_iff_of
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (h0E6I : IsH01CurveFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1) :
    letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
      ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
    IsPrestableCurveFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (Stacks.Curves.HasAtWorstNodalSingularities k
          ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
        Function.Bijective
          ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop) := by
  set X := (BigFppfOver.toScheme B integerBase hZ).obj T with hXdef
  set q : X ⟶ Spec (.of k) := (BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW
    with hq
  let : X.Over (Spec (.of k)) := ⟨q⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := by
    change LocallyOfFiniteType q
    infer_instance
  let F := curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim
  have hnodal : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom ↔
      (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
        ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)) :=
    ((Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget g).trans
      (isAtWorstNodalOfRelativeDimensionOne_comp_eqToHom_iff _ hW).symm).trans (hsch k X)
  constructor
  · rintro ⟨hN, hH⟩
    obtain ⟨hiso, hd⟩ := h0E6I.1 (isH01CurveFamily_of_isPrestableCurveFamily (X := F) ⟨hN, hH⟩)
    exact ⟨(hnodal.1 hN).1, hd, hiso⟩
  · rintro ⟨hsing, hd, hiso⟩
    have : IsIso q.appTop := (ConcreteCategory.isIso_iff_bijective q.appTop).2 hiso
    have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k q
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    have : IsNoetherian X := {}
    have hcomp : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞) :=
      fun Z hZ => topologicalKrullDim_eq_one_of_mem_irreducibleComponents hd hZ
    have hN := hnodal.2 ⟨hsing, fun Z hZ Z' hZ' => (hcomp Z hZ).trans (hcomp Z' hZ').symm, hcomp⟩
    exact ⟨hN, (h0E6I.2 ⟨hiso, hd⟩).1⟩

/-- A proper morphism of the site onto the spectrum of a field is flat and locally of finite
presentation. -/
theorem flat_and_locallyOfFinitePresentation_of_obj_eq_specField
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g)) :
    Flat ((BigFppfOver.toScheme B integerBase hZ).map g) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g) := by
  have aux : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Y = Spec (.of k) → LocallyOfFiniteType f →
      Flat f ∧ LocallyOfFinitePresentation f := by
    intro X Y f hY hf
    subst hY
    exact ⟨inferInstance, inferInstance⟩
  exact aux _ hW inferInstance

variable (B hZ) in
/-- **The family of curves of a proper scheme of dimension at most one over a field**, read off
a proper morphism `g : T ⟶ W` of the site with `W = Spec k`:
`AlgebraicGeometry.curveFamilyOfSchemeMorphism` at `g`, with flatness, local finite presentation,
quasi-compactness, separatedness and quasi-separatedness discharged from properness over the
field. -/
abbrev curveFamilyOverFieldOfProper {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (k : Type u) [Field k] (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    CurveFamily B hZ :=
  curveFamilyOfSchemeMorphism B hZ g
    (flat_and_locallyOfFinitePresentation_of_obj_eq_specField g k hW hproper).1 hproper
    (flat_and_locallyOfFinitePresentation_of_obj_eq_specField g k hW hproper).2
    (Space.isQuasiCompact_yoneda_map B integerBase hZ g (by have := hproper; infer_instance))
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).mpr
      (by have := hproper; infer_instance))
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).mpr
      (by have := hproper; infer_instance))
    hdim

/-- **Stacks 0E6U, from its inputs.** There is an open substack
`Curves^{prestable} ⊂ Curves` — the strictly full subcategory of prestable families of curves
(Stacks 0E6T), whose inclusion is representable by algebraic spaces and an open immersion — such
that

1. the classifying morphism of a family of curves factors through it exactly when the family is
   prestable, and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1` (a proper morphism `g : T ⟶ W` of
   the site with `W = Spec k`), the classifying morphism `Spec k → Curves` of `X` factors through
   it exactly when the singularities of `X` are at-worst-nodal, `dim(X) = 1` and
   `k = H⁰(X, 𝒪_X)`.

The inputs are condition (o) for `Curves^{h0,1}` (`hH01`, part (1) of Stacks 0E6I), part (2) of
Stacks 0E6I (`h0E6I`) and the criterion for at-worst-nodal morphisms of relative dimension one
over a field (`hsch`, the scheme-level content of part (2) of Stacks 0DSY). -/
theorem curvesPrestable_isOpenSubstack_and_factors_iff_of_inputs
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (h0E6I : ∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1),
      IsH01CurveFamily B hZ
          (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
        Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞))) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of hH01).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of hH01).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ g k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop))) := by
  refine ⟨(curvesPrestable_isOpenSubstack_and_factors_iff_of hH01).1,
    (curvesPrestable_isOpenSubstack_and_factors_iff_of hH01).2, ?_⟩
  intro k _ T W g hW hproper hdim U y hy e
  rw [factors_curvesSubstack_iff_of_iso (isOpenCurvesLocus_isPrestableCurveFamily_of hH01)
    U y hy _ e]
  exact isPrestableCurveFamily_curveFamilyOfSchemeMorphism_iff_of B hZ g k hW _ hproper _ _ _ _
    hdim hsch (h0E6I g k hW _ hproper _ _ _ _ hdim)

/-- **Stacks 0E6U, from the inputs of Stacks 0E6I and of part (2) of Stacks 0DSY.** The whole
statement of `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of_inputs` with
both parts of Stacks 0E6I supplied by `AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of`
and `AlgebraicGeometry.CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of`. The
remaining inputs are the openness and base change of the fibrewise condition
`k = H⁰(X_k, 𝒪_{X_k})` (`hopen`, Stacks 0E0R at `i = 0`), Stacks 0E6B part (a) (`hpush`), and the
criterion for at-worst-nodal morphisms over a field (`hsch`). -/
theorem curvesPrestable_isOpenSubstack_and_factors_iff_of_h01Inputs
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞))) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of
            (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of
            (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ g k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop))) :=
  curvesPrestable_isOpenSubstack_and_factors_iff_of_inputs
    (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)
    (fun {_ _} g k _ hW hflat hproper hlfp hqc hsep hqsep hdim =>
      CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hflat hproper
        hlfp hqc hsep hqsep hdim)
    hsch

end AlgebraicGeometry

end
