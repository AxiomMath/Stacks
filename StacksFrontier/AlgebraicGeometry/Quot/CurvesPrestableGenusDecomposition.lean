module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusDecomposition
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.LocalDimensionComponents

/-!
# The decomposition `Curves^{prestable} = ∐_g Curves^{prestable}_g` (Stacks 0E6V)

Stacks 0E6V decomposes the open substack `Curves^{prestable}` of the stack of curves (Stacks
0E6U) into open and closed substacks `Curves^{prestable}_g`, `g ≥ 0`, characterized
1. on a family of curves `f : X → S`: the classifying morphism factors through
   `Curves^{prestable}_g` exactly when `f` is a prestable family of curves (Stacks 0E6T) and
   `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`;
2. on a scheme `X` proper over a field `k` with `dim(X) ≤ 1`: the classifying morphism
   `Spec(k) → Curves` factors through `Curves^{prestable}_g` exactly when the singularities of `X`
   are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and the genus of `X` is `g`.

The source proves this from Stacks 0E6U and 0E6K, since `Curves^{prestable} ⊂ Curves^{h0,1}`,
and so does this file: `Curves^{prestable}_g = Curves^{prestable} ∩ Curves_g`, with
`Curves^{prestable} = Curves^{nodal} ∩ Curves^{h0,1}` open by Stacks 0DSY and 0E6I
(`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily`), and `Curves_g` open with its
decomposition over `Curves^{h0,1}` by Stacks 0E6K
(`StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusDecomposition`).

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_isPrestableGenusCurveFamily`: condition (o) of Section
  0E0E for the families of `Curves^{prestable}_g`, so that `Curves^{prestable}_g` is an open
  substack of `Curves`.
* `curvesPrestableGenus_isOpenSubstack_and_factors_iff_and_decomposition_and_over_field_iff`
  (**Stacks 0E6V**, in namespace `AlgebraicGeometry`): the decomposition and parts (1) and (2).

## Implementation notes

`Curves^{prestable}_g` is the full subcategory of families satisfying
`AlgebraicGeometry.IsPrestableGenusCurveFamily`, `Curves^{prestable} ∩ Curves_g`; condition (1)(b)
does not mention `Curves_g` because a prestable family lies in `Curves^{h0,1}`. The decomposition
into open and closed substacks is stated on the scheme-valued points of `Curves^{prestable}`: over
a prestable family `G` with base `S`, the base change of `Curves^{prestable}_g` along
`S → Curves^{prestable}` is the open subscheme `Ω_g` of `S`, and the `Ω_g` are open and closed,
pairwise disjoint, and cover `S`. Each `Curves^{prestable}_g` is moreover an open substack of
`Curves` contained in `Curves^{prestable}`.

Part (2) is stated, as in Stacks 0E0E (1) and Stacks 0DSY, for the family of curves
`AlgebraicGeometry.curveFamilyOverFieldOfProper` of a proper morphism `p : T ⟶ W` of the site with
`W = Spec k` and `dim(T) ≤ 1`: "the classifying morphism factors" is read for every
`Spec k`-point `y` of `Curves` isomorphic to that family; `k = H⁰(X, 𝒪_X)` is the bijectivity of
pullback of global sections along `X → Spec k`, and the genus is
`AlgebraicGeometry.genus` (Stacks 0BY7).

For part (2) this file proves the at-worst-nodal criterion over a field behind part (2) of
Stacks 0DSY (from Stacks 0C59) and uses Stacks 0E6B part (a) for algebraic spaces; the private
helpers of this file are not registered.

## References

* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

/-! ### The at-worst-nodal criterion over a field -/

/-- The dimension of a space is at most `d` when that of each irreducible component is. -/
private theorem topologicalKrullDim_le_of_forall_mem_irreducibleComponents_le {X : Type*}
    [TopologicalSpace X] {d : WithBot ℕ∞}
    (h : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (p.toFun (Fin.last p.length)).isIrreducible
  exact (length_le_topologicalKrullDim_of_forall_subset p fun j =>
    (SetLike.coe_subset_coe.2 (LTSeries.monotone p (Fin.le_last j))).trans hsub).trans (h Z hZ)

/-- On a nonempty equidimensional space, every irreducible component has dimension one exactly
when the space has dimension one. -/
private theorem forall_mem_irreducibleComponents_topologicalKrullDim_eq_one_iff {X : Type*}
    [TopologicalSpace X] [Nonempty X] (hequi : TopologicalSpace.Equidimensional X) :
    (∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)) ↔
      topologicalKrullDim X = (1 : WithBot ℕ∞) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hZ₀ := irreducibleComponent_mem_irreducibleComponents x
  have hle : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z ≤ topologicalKrullDim X :=
    fun Z _ => topologicalKrullDim_subspace_le X Z
  refine ⟨fun h => le_antisymm (topologicalKrullDim_le_of_forall_mem_irreducibleComponents_le
    fun Z hZ => (h Z hZ).le) ((h _ hZ₀).ge.trans (hle _ hZ₀)), fun h Z hZ => ?_⟩
  exact le_antisymm ((hle Z hZ).trans h.le) (h.ge.trans
    (topologicalKrullDim_le_of_forall_mem_irreducibleComponents_le fun W hW =>
      (hequi W hW Z hZ).le))

/-- **At-worst-nodal of relative dimension one over a field (the scheme content of part (2) of
Stacks 0DSY).** A scheme `X` locally of finite type over a field `k` is at-worst-nodal of relative
dimension one over `k` exactly when its singularities are at-worst-nodal and it is
equidimensional with every irreducible component of dimension one. By Stacks 0C59 the left side
is the condition on the only fibre, which is `X` over the residue field `κ = k` of the only point
of `Spec k`; over an empty `X` both sides hold vacuously. -/
private theorem isAtWorstNodalOfRelativeDimensionOne_overField_iff (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
      (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
        ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)) := by
  set f := X ↘ Spec (.of k)
  have : LocallyOfFinitePresentation f := inferInstance
  rw [← Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff]
  rcases isEmpty_or_nonempty X with hXe | _
  · exact ⟨fun _ => ⟨fun x => hXe.elim x, fun Z hZ => hXe.elim hZ.1.nonempty.some,
      fun Z hZ => hXe.elim hZ.1.nonempty.some⟩,
      fun _ => ⟨inferInstance, inferInstance, fun s ⟨y⟩ => hXe.elim (f.fiberι s y)⟩⟩
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := ⟨f (Classical.arbitrary X)⟩
  have : IsIso ((Spec (.of k)).fromSpecResidueField s) := isIso_fromSpecResidueField_of_field k s
  have : IsIso (f.fiberι s) := isIso_fiberι_of_isIso_fromSpecResidueField f s inferInstance
  let e : f.fiber s ≃ₜ X := Scheme.homeoOfIso (asIso (f.fiberι s))
  have hdimeq : topologicalKrullDim (f.fiber s) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph
  set ψ := (Spec (.of k)).fromSpecResidueField s with hψ
  let φ : CommRingCat.of k ⟶ CommRingCat.of ((Spec (.of k)).residueField s) := Spec.preimage ψ
  have hφ : Spec.map φ = ψ := Spec.map_preimage ψ
  have : IsIso φ := by
    have : IsIso (Spec.map φ) := by
      rw [hφ]
      infer_instance
    exact (ConcreteCategory.isIso_iff_bijective φ).2 (isIso_SpecMap_iff.1 this)
  have he₁ : inv (f.fiberι s) ≫ f.fiberToSpecResidueField s ≫ Spec.map φ = f := by
    rw [hφ, hψ, ← Scheme.Hom.fiber_fac, IsIso.inv_hom_id_assoc]
  have he₂ : f.fiberι s ≫ f ≫ Spec.map (inv φ) = f.fiberToSpecResidueField s := by
    rw [Scheme.Hom.fiber_fac_assoc, ← hψ, ← hφ, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id]
    exact Category.comp_id _
  constructor
  · rintro ⟨-, -, hfib⟩
    obtain ⟨hequi, hdim, hnod⟩ := hfib s ⟨e.symm (Classical.arbitrary X)⟩
    have hequiX : TopologicalSpace.Equidimensional X := hequi.of_homeomorph e.symm
    exact ⟨@Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _
      (f.fiberToSpecResidueField s) f (Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s)
      hdim (inv (f.fiberι s)) inferInstance φ ‹IsIso φ› he₁ hnod, hequiX,
      (forall_mem_irreducibleComponents_topologicalKrullDim_eq_one_iff hequiX).2 (hdimeq ▸ hdim)⟩
  · rintro ⟨hnod, hequi, hcomp⟩
    have hdim : topologicalKrullDim X = (1 : WithBot ℕ∞) :=
      (forall_mem_irreducibleComponents_topologicalKrullDim_eq_one_iff hequi).1 hcomp
    refine ⟨inferInstance, inferInstance, fun s' _ => ?_⟩
    obtain rfl : s = s' := Subsingleton.elim _ _
    exact ⟨hequi.of_homeomorph e, hdimeq.trans hdim,
      @Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _ f
        (f.fiberToSpecResidueField s) inferInstance hdim (f.fiberι s) inferInstance
        (@inv _ _ _ _ φ ‹_›) (@IsIso.inv_isIso _ _ _ _ φ ‹_›) he₂ hnod⟩

/-! ### Assembly -/

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

section Assembly

open CurveFamily

/-- **Condition (o) of Stacks 0E0E for `Curves^{prestable}_g`**: the families of
`Curves^{prestable}_g` form an open substack of `Curves`. It is the intersection of condition (o)
for `Curves^{prestable}` (Stacks 0E6U) with condition (o) for `Curves_g` (Stacks 0E6K). -/
theorem isOpenCurvesLocus_isPrestableGenusCurveFamily (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsPrestableGenusCurveFamily B hZ g) :=
  (isOpenCurvesLocus_isPrestableCurveFamily_of isOpenCurvesLocus_isH01CurveFamily).and
    (isOpenCurvesLocus_isGenusCurveFamily_of
      isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres
      hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
      (fun _ => hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions)
      (fun _ => firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions) g)

/-- **The decomposition `Curves^{prestable} = ∐_g Curves^{prestable}_g` into open and closed
substacks, read on a scheme-valued point of `Curves^{prestable}`.** Over a prestable family `G`
with base `S` the loci `Ω_g` of `Curves_g` over `G ∈ Curves^{h0,1}` (Stacks 0E6K) are open and
closed, pairwise disjoint and cover `S`, and a family mapping to `G` is in
`Curves^{prestable}_g` exactly when its base maps into `Ω_g`, since it is prestable. -/
private theorem curvesPrestableGenus_decomposition_of_isPrestable (G : CurveFamily B hZ)
    (hG : IsPrestableCurveFamily B hZ G) :
    ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
      (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
        (⋃ g, Ω g) = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          IsPrestableGenusCurveFamily B hZ g F ↔
            Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
              (schemeSpaceMap a.baseMap).hom) ⊆ Ω g := by
  obtain ⟨Ω, hclopen, hdisj, hcov, hchar⟩ :=
    curvesGenus_decomposition_of isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres
      hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
      (fun _ => hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions)
      (fun _ => firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions) G
      (isH01CurveFamily_of_isPrestableCurveFamily hG)
  exact ⟨Ω, hclopen, hdisj, hcov, fun g F a => (and_iff_right
    ((isOpenCurvesLocus_isPrestableCurveFamily_of isOpenCurvesLocus_isH01CurveFamily).prop_of_hom
      a hG)).trans (hchar g F a)⟩

/-- **Stacks 0E6V.** There is a decomposition
`Curves^{prestable} = ∐_{g ≥ 0} Curves^{prestable}_g` into open and closed substacks, where
1. the classifying morphism of a family of curves `f : X → S` factors through
   `Curves^{prestable}_g` exactly when `f` is a prestable family of curves and `R¹f_*𝒪_X` is a
   locally free `𝒪_S`-module of rank `g`;
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1` (a proper morphism `p : T ⟶ W` of
   the site with `W = Spec k`), the classifying morphism `Spec k → Curves` of `X` factors through
   `Curves^{prestable}_g` exactly when the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
   `k = H⁰(X, 𝒪_X)` and the genus of `X` is `g`.

Each `Curves^{prestable}_g` is an open substack of `Curves` contained in `Curves^{prestable}`
(the first conjunct, with the second), and over every scheme-valued point of
`Curves^{prestable}` — a prestable family `G` over a scheme `S` — the loci `Ω_g ⊂ S` of the
`Curves^{prestable}_g` are open and closed, pairwise disjoint and cover `S`, a family mapping to
`G` lying in `Curves^{prestable}_g` exactly when its base maps into `Ω_g` (the third conjunct):
this is the decomposition into open and closed substacks. -/
@[stacks 0E6V]
theorem curvesPrestableGenus_isOpenSubstack_and_factors_iff_and_decomposition_and_over_field_iff :
    (∀ g : ℕ,
      (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ, IsPrestableGenusCurveFamily B hZ g X →
        IsPrestableCurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
          IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
            RingedSite.IsFiniteLocallyFreeOfRank
              (Space.smallEtaleRingedSite B integerBase hZ
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).1
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).2)
              ((y.obj (Over.mk (𝟙 U.left))).firstDirectImage B hZ) g)) ∧
    (∀ G : CurveFamily B hZ, IsPrestableCurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsPrestableGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g) ∧
    (∀ (g : ℕ) (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ p k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW⟩
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
          z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW).appTop ∧
          genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW) = g))) := by
  refine ⟨fun g => ⟨isOpenImmersion_curvesSubstackInclusion
      (isOpenCurvesLocus_isPrestableGenusCurveFamily g), fun _ h => h.1,
    fun U y hy => (factors_curvesSubstack_iff
      (isOpenCurvesLocus_isPrestableGenusCurveFamily g) U y hy).trans
        (isPrestableGenusCurveFamily_iff g _)⟩,
    curvesPrestableGenus_decomposition_of_isPrestable, ?_⟩
  intro g k _ T W p hW hproper hdim U y hy e
  rw [factors_curvesSubstack_iff_of_iso
    (isOpenCurvesLocus_isPrestableGenusCurveFamily g) U y hy _ e]
  exact isPrestableGenusCurveFamily_curveFamilyOverFieldOfProper_iff_of
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
    (fun k _ X _ _ => isAtWorstNodalOfRelativeDimensionOne_overField_iff k X)
    (fun k _ _ _ p hW hproper hdim _ =>
      isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus k p hW
        hproper hdim) g k p hW hproper hdim

end Assembly

end AlgebraicGeometry
