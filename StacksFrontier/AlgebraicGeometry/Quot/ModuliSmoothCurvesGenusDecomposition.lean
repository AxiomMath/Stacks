module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusUnion
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfSchemeFibreGenus
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOfGenus
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.SmoothProperCurveOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace

/-!
# The decomposition of `𝓜` by the genus (Stacks 0E83)

Stacks 0E83 decomposes the moduli stack `𝓜 = Curves^{smooth, h0}` of smooth proper curves
(`AlgebraicGeometry.moduliSmoothCurves`) into open and closed substacks
`𝓜 = ∐_{g ≥ 0} 𝓜_g`, the summands being the stacks `𝓜_g` of Stacks 0E82
(`AlgebraicGeometry.moduliSmoothCurvesOfGenus`), and characterizes `𝓜_g`:

1. the classifying morphism of a family of curves `f : X → S` factors through `𝓜_g` exactly when
   `X → S` is smooth (of relative dimension one, see below), `f_*𝒪_X = 𝒪_S` universally, and
   `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`;
2. for a proper scheme `X` of dimension at most one over a field `k`, the classifying morphism
   `Spec(k) → Curves` factors through `𝓜_g` exactly when `X` is smooth, `dim(X) = 1`,
   `k = H⁰(X, 𝒪_X)` and `X` has genus `g`, and this is equivalent to the variants with
   "geometrically connected", "geometrically integral", and "`X_{k̄}` is a smooth curve of genus
   `g`".

## Main results

* `AlgebraicGeometry.CurveFamily.openClosedDecomposition_fibreGenusLocus`: over the base of a
  family with `f_*𝒪_X = 𝒪_S` universally, the loci of points whose fibre has genus `g` are open and
  closed, pairwise disjoint, cover the base, and a family mapping to it has all its fibres of genus
  `g` exactly when its base lands in the `g`-th locus.
* `AlgebraicGeometry.moduliSmoothCurves_openClosedDecomposition`: **Stacks 0E83**, the
  decomposition `𝓜 = ∐_{g ≥ 0} 𝓜_g` into open and closed substacks.
* `AlgebraicGeometry.factors_moduliSmoothCurvesOfGenus_iff`: **Stacks 0E83, part (1)**.
* `AlgebraicGeometry.isSmoothH0FamilyOfFibreGenus_curveFamilyOfScheme_iff`: the family of a proper
  scheme `X` over a field lies in `𝓜_g` exactly when `X` is smooth, of dimension one, with
  `k = H⁰(X, 𝒪_X)`, of genus `g`.
* `AlgebraicGeometry.factors_moduliSmoothCurvesOfGenus_over_field_iff`: **Stacks 0E83,
  part (2)**.
* `AlgebraicGeometry.not_factors_moduliSmoothCurvesOfGenus_zero_of_identity`: the statement of
  part (1) with "smooth" read without a relative dimension fails for `g = 0`.

## Implementation notes

*The decomposition.* An open substack `𝒰 ⊂ 𝓜` is determined by its pullbacks to the
scheme-valued points of `𝓜`: for a family `G ∈ 𝓜` over `S` the base change `𝒰 ×_𝓜 S` is an
open subscheme `W ⊂ S`, and a family `F → G` lies in `𝒰` exactly when its base `T → S` factors
through `W`. We record this for `𝒰 = 𝓜_g` with `W` the open subspace cut out by the points of `S`
whose fibre has genus `g` (`AlgebraicGeometry.CurveFamily.fibreGenusLocus`): these loci are
open and closed, pairwise disjoint, and cover `S`, which is the decomposition
`𝓜 = ∐_g 𝓜_g` into open and closed substacks. As in the source (which combines Stacks 0E81 with
Stacks 0E6K, that is with Stacks 0E1J), the input is that `R¹f_*𝒪_X` is finite locally free and
commutes with base change for a family with `f_*𝒪_X = 𝒪_S` universally, so that the fibre genus
is the rank of `R¹f_*𝒪_X`, a locally constant function
(`AlgebraicGeometry.CurveFamily.isClopen_fibreGenusLocus_and_pairwise_disjoint_and_iUnion_eq_univ`,
`AlgebraicGeometry.CurveFamily.preimage_fibreGenusLocus`). The openness of `𝓜` itself in
`Curves` is Stacks 0E81 and is not part of this statement.

*The classifying morphism.* As in `AlgebraicGeometry.factors_curvesSubstack_iff` (Stacks 0E0E),
the classifying morphism `S → Curves` of a family is a scheme-valued point
`y : (Sch/S)_{fppf} ⥤ Curves` of the stack of curves over `S` whose value at `S` is the family,
and it factors through `𝓜_g` when `y` lifts to the full subcategory of `𝓜_g`. Since membership in
`𝓜_g` passes to base changes, a lift exists exactly when the family `y(S)` lies in `𝓜_g`.

*A correction to part (1).* Condition (1)(b) of the source reads "`X → S` is smooth", without
the relative dimension. Read literally, (1)(b) ⟹ (1)(a) fails for `g = 0`: the identity
`Spec(k) → Spec(k)` of a field is a family of curves (its fibre has dimension `0 ≤ 1`), it is
smooth, `f_*𝒪 = 𝒪` holds universally, and `R¹f_*𝒪 = 0` is locally free of rank `0`, but it does
not lie in `𝓜 = Curves^{smooth, h0}`, whose families are smooth *of relative dimension one*
(condition (1)(b) of Stacks 0E81, `AlgebraicGeometry.IsSmoothH0Family`). This is
`AlgebraicGeometry.not_factors_moduliSmoothCurvesOfGenus_zero_of_identity`. Part (1) is therefore
stated with "smooth of relative dimension one", which is what membership in `𝓜` means.

## References

* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E82](https://stacks.math.columbia.edu/tag/0E82)
* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-! ### The fibre genus loci of a family with `f_*𝒪_X = 𝒪_S` universally -/

namespace CurveFamily

/-- **The decomposition by the fibre genus.** Let `P` be a property of families of curves which
passes to base changes and implies `f_*𝒪_X = 𝒪_S` universally (as for `𝓜`, `𝓜̄` or prestable
families). Over the base of a family `G` with `P`, the loci of points whose fibre has genus `g`
are open and closed, pairwise disjoint and cover the base, and a family `F` mapping to `G` has
`P` with every fibre of genus `g` exactly when its base lands in the `g`-th locus. -/
theorem openClosedDecomposition_fibreGenusLocus {P : ObjectProperty (CurveFamily B hZ)}
    (hP : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → P G → P F)
    (hPh : ∀ F : CurveFamily B hZ, P F → HasUniversallyBijectiveGlobalFunctions B hZ F)
    (G : CurveFamily B hZ) (hG : P G) :
    (∀ g : ℕ, IsClopen (fibreGenusLocus B hZ G g)) ∧
      Pairwise (fun g g' : ℕ => Disjoint (fibreGenusLocus B hZ G g) (fibreGenusLocus B hZ G g')) ∧
      (⋃ g : ℕ, fibreGenusLocus B hZ G g) = Set.univ ∧
      ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
        (P F ∧ HasFieldPointFibreGenus B hZ F g ↔
          Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
            (schemeSpaceMap a.baseMap).hom) ⊆ fibreGenusLocus B hZ G g) := by
  have hk := bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions (hPh G hG)
  obtain ⟨hclopen, hdisj, hcov⟩ :=
    G.isClopen_fibreGenusLocus_and_pairwise_disjoint_and_iUnion_eq_univ hk
  refine ⟨hclopen, hdisj, hcov, fun g F a => ?_⟩
  have hF : P F := hP a hG
  have hkF := bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions (hPh F hF)
  rw [and_iff_right hF, F.hasFieldPointFibreGenus_iff_fibreGenusLocus_eq_univ hkF g,
    ← G.preimage_fibreGenusLocus hk a hkF g, Set.preimage_eq_univ_iff]

/-- For a family of curves with `f_*𝒪_X = 𝒪_S` universally, every fibre has genus `g` exactly
when `R¹f_*𝒪_X` is locally free of rank `g`. -/
theorem hasFieldPointFibreGenus_iff_hasGenus_of_hasUniversallyBijectiveGlobalFunctions
    {X : CurveFamily B hZ} (hX : HasUniversallyBijectiveGlobalFunctions B hZ X) (g : ℕ) :
    HasFieldPointFibreGenus B hZ X g ↔ HasGenus B hZ X g :=
  X.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
    (bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hX) g

end CurveFamily

/-! ### The decomposition `𝓜 = ∐_g 𝓜_g` -/

/-- A family of curves lies in `𝓜_g` exactly when it is smooth of relative dimension one,
`f_*𝒪_X = 𝒪_S` universally, and `R¹f_*𝒪_X` is locally free of rank `g`. -/
theorem isSmoothH0FamilyOfFibreGenus_iff (g : ℕ) (X : CurveFamily B hZ) :
    IsSmoothH0FamilyOfFibreGenus B hZ g X ↔
      IsSmoothDimOneFamily B hZ X ∧ HasUniversallyBijectiveGlobalFunctions B hZ X ∧
        CurveFamily.HasGenus B hZ X g := by
  constructor
  · rintro ⟨⟨hs, hh⟩, hg⟩
    exact ⟨hs, hh,
      (CurveFamily.hasFieldPointFibreGenus_iff_hasGenus_of_hasUniversallyBijectiveGlobalFunctions
        hh g).1 hg⟩
  · rintro ⟨hs, hh, hg⟩
    exact ⟨⟨hs, hh⟩,
      (CurveFamily.hasFieldPointFibreGenus_iff_hasGenus_of_hasUniversallyBijectiveGlobalFunctions
        hh g).2 hg⟩

variable (B hZ) in
/-- **The decomposition `𝓜 = ∐_{g ≥ 0} 𝓜_g` into open and closed substacks.**
Let `G` be a family of curves in `𝓜` (`AlgebraicGeometry.moduliSmoothCurves`) over a scheme `S`,
that is, a scheme-valued point `S → 𝓜`. Then:

* the loci `S_g ⊂ S` of points whose fibre has genus `g` are open and closed in `S`, pairwise
  disjoint, and cover `S`;
* for every `g`, `𝓜_g ×_𝓜 S` is the open subscheme `S_g`: there is an open subspace `W` of `S`
  with points `S_g` such that a family `F` mapping to `G` (a base change of `G` along `T → S`)
  lies in `𝓜_g` (`AlgebraicGeometry.moduliSmoothCurvesOfGenus`) exactly when `T → S` factors
  through `W`, exactly when `T → S` maps every point into `S_g`.

So each `𝓜_g ⊂ 𝓜` is an open and closed substack, these substacks are pairwise disjoint, and
together they cover `𝓜`. -/
@[stacks 0E83 "the decomposition 𝓜 = ∐_{g ≥ 0} 𝓜_g into open and closed substacks, read on the \
scheme-valued points of 𝓜"]
theorem moduliSmoothCurves_openClosedDecomposition (G : CurveFamily B hZ)
    (hG : IsSmoothH0Family B hZ G) :
    (∀ g : ℕ, IsClopen (CurveFamily.fibreGenusLocus B hZ G g)) ∧
      Pairwise (fun g g' : ℕ => Disjoint (CurveFamily.fibreGenusLocus B hZ G g)
        (CurveFamily.fibreGenusLocus B hZ G g')) ∧
      (⋃ g : ℕ, CurveFamily.fibreGenusLocus B hZ G g) = Set.univ ∧
      ∀ g : ℕ, ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) =
          CurveFamily.fibreGenusLocus B hZ G g ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          (IsSmoothH0FamilyOfFibreGenus B hZ g F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom) ∧
          (IsSmoothH0FamilyOfFibreGenus B hZ g F ↔
            Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
              (schemeSpaceMap a.baseMap).hom) ⊆ CurveFamily.fibreGenusLocus B hZ G g) := by
  obtain ⟨hclopen, hdisj, hcov, hchar⟩ :=
    CurveFamily.openClosedDecomposition_fibreGenusLocus (P := IsSmoothH0Family B hZ)
      (fun a h => CurveFamily.isSmoothH0Family_of_hom B hZ a h) (fun _ h => h.2) G hG
  refine ⟨hclopen, hdisj, hcov, fun g => ?_⟩
  have hW := Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ
    (schemeSpace G.base).property _ (hclopen g).isOpen
  refine ⟨Space.openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).obj
      (CurveFamily.fibreGenusLocus B hZ G g), hW,
    Space.range_pointsMap_ι_openSubspaceOfPoints B integerBase hZ _, fun F a => ?_⟩
  have h := hchar g F a
  refine ⟨?_, h⟩
  rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property _ hW,
    Space.range_pointsMap_ι_openSubspaceOfPoints]
  exact h

/-! ### Part (1): the families of `𝓜_g` -/

/-- The classifying morphism `y` lifts to the families of `𝓜_g` exactly when the family `X`
isomorphic to `y(S)` lies in `𝓜_g`. -/
private theorem exists_lift_iff_isSmoothH0FamilyOfFibreGenus (g : ℕ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ) (X : CurveFamily B hZ)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ X) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSmoothH0FamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsSmoothH0FamilyOfFibreGenus B hZ g) = y) ↔
      IsSmoothH0FamilyOfFibreGenus B hZ g X := by
  constructor
  · rintro ⟨z, rfl⟩
    exact CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom e.inv (z.obj _).property
  · intro h
    have hall : ∀ T, IsSmoothH0FamilyOfFibreGenus B hZ g (y.obj T) := fun T =>
      CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom
        (y.map (Over.homMk T.hom (by simp)) ≫ e.hom) h
    exact ⟨ObjectProperty.lift (IsSmoothH0FamilyOfFibreGenus B hZ g) y hall, rfl⟩

variable (B hZ) in
/-- Let `f : X → S` be a family of curves, classified by a
scheme-valued point `y` of the stack of curves over `S` with `y(S) ≅ X`. The following are
equivalent:

* (a) the classifying morphism `S → Curves` factors through `𝓜_g`
  (`AlgebraicGeometry.moduliSmoothCurvesOfGenus`): `y` lifts to the full subcategory of the
  families of `𝓜_g`;
* (b) `X → S` is smooth of relative dimension one, `f_*𝒪_X = 𝒪_S` and this holds after any base
  change, and `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`.

The source writes "smooth" in (b); with no relative dimension (b) ⟹ (a) fails for `g = 0`
(`AlgebraicGeometry.not_factors_moduliSmoothCurvesOfGenus_zero_of_identity`), and (b) is stated
with the relative dimension one that membership in `𝓜` (Stacks 0E81) requires. -/
@[stacks 0E83 "part (1), with smooth of relative dimension one in (b): read with smooth of \
arbitrary relative dimension, (b) ⟹ (a) fails for g = 0, see \
not_factors_moduliSmoothCurvesOfGenus_zero_of_identity"]
theorem factors_moduliSmoothCurvesOfGenus_iff (g : ℕ) (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (_hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) (X : CurveFamily B hZ)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ X) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSmoothH0FamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsSmoothH0FamilyOfFibreGenus B hZ g) = y) ↔
      IsSmoothDimOneFamily B hZ X ∧ HasUniversallyBijectiveGlobalFunctions B hZ X ∧
        CurveFamily.HasGenus B hZ X g := by
  exact (exists_lift_iff_isSmoothH0FamilyOfFibreGenus g U y _ e).trans
    (isSmoothH0FamilyOfFibreGenus_iff g X)

/-! ### Part (2): over a field -/

/-- **Smoothness of relative dimension one of the family of a proper scheme over a field**: for
`X` nonempty, proper of dimension at most one over `k`, the family `X → Spec k` is smooth of
relative dimension one exactly when `X` is smooth over `k`, equidimensional, of dimension one
(Stacks 0DZZ, part (2)). -/
theorem isSmoothDimOneFamily_curveFamilyOfScheme_iff {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (hne : Nonempty X.left) :
    IsSmoothDimOneFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      Smooth X.hom ∧ TopologicalSpace.Equidimensional X.left ∧
        topologicalKrullDim X.left = 1 :=
  isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk X.hom)
    (inferInstance : Flat X.hom) ‹_› (inferInstance : LocallyOfFinitePresentation X.hom)
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ _
      (inferInstanceAs (QuasiCompact X.hom)))
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ _).2
      (inferInstanceAs (IsSeparated X.hom)))
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ _).2
      (inferInstanceAs (QuasiSeparated X.hom))) hdim k rfl hne

/-- **The family of a proper scheme over a field lies in `𝓜_g`** exactly when the scheme is
smooth, of dimension one, with `k = H⁰(X, 𝒪_X)`, and of genus `g` (Stacks 0DZZ, part (2), and
Stacks 0BY5). -/
theorem isSmoothH0FamilyOfFibreGenus_curveFamilyOfScheme_iff (g : ℕ) {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    IsSmoothH0FamilyOfFibreGenus B hZ g (curveFamilyOfScheme X B hZ hk hdim) ↔
      Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g := by
  have hsm := fun hne : Nonempty X.left =>
    isSmoothDimOneFamily_curveFamilyOfScheme_iff (hZ := hZ) hk X hdim hne
  have hne_of_H0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) → Nonempty X.left := by
    intro hH0
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have : Subsingleton Γ(X.left, ⊤) := inferInstance
    have hinj := (ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)).1
    exact zero_ne_one (hinj (Subsingleton.elim _ _) : (0 : k) = 1)
  have hH := hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff (hZ := hZ) hk X hdim
  have hG := hasFieldPointFibreGenus_curveFamilyOfScheme_iff (hZ := hZ) hk X hdim g
  constructor
  · rintro ⟨⟨hsd, hH0⟩, hgen⟩
    have hH0' := hH.1 hH0
    obtain ⟨hs, -, hd⟩ := (hsm (hne_of_H0 hH0')).1 hsd
    exact ⟨hs, hd, hH0', hG.1 hgen⟩
  · rintro ⟨hs, hdim1, hH0, hgen⟩
    have := hH0
    have hequi : TopologicalSpace.Equidimensional X.left :=
      equidimensional_of_isIso_globalSections_of_dimension_one k X.hom hdim1
    exact ⟨⟨(hsm (hne_of_H0 hH0)).2 ⟨hs, hequi, hdim1⟩, hH.2 hH0⟩, hG.2 hgen⟩

variable (B hZ) in
/-- Let `X` be a scheme proper over a field `k` with `dim(X) ≤ 1`, let `k̄` be an algebraic
closure of `k` and `g ≥ 0`. The following are equivalent:

* (a) the classifying morphism `Spec(k) → Curves` of `X` factors through `𝓜_g`
  (`AlgebraicGeometry.moduliSmoothCurvesOfGenus`): a scheme-valued point `y` of `Curves` over `U`
  with `y(U) ≅ X` lifts to the full subcategory of the families of `𝓜_g`;
* (b) `X` is smooth, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, and `X` has genus `g`;
* (c) `X` is smooth, `dim(X) = 1`, `X` is geometrically connected, and `X` has genus `g`;
* (d) `X` is smooth, `dim(X) = 1`, `X` is geometrically integral, and `X` has genus `g`;
* (e) `X_{k̄}` is a smooth curve of genus `g` over `k̄`. -/
@[stacks 0E83 "part (2): over a field, (a) the classifying morphism factors through 𝓜_g, \
(b)-(e) the conditions on X"]
theorem factors_moduliSmoothCurvesOfGenus_over_field_iff (g : ℕ) {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (K : Type u) [Field K] [Algebra k K]
    [IsAlgClosure k K] :
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0FamilyOfFibreGenus B hZ g),
          z ⋙ ObjectProperty.ι (IsSmoothH0FamilyOfFibreGenus B hZ g) = y) ↔
        Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g)) ∧
    List.TFAE [
      Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g,
      Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧ GeometricallyConnected X.hom ∧
        genus X.hom = g,
      Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧ GeometricallyIntegral X.hom ∧
        genus X.hom = g,
      Smooth (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        IsCurve K (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        genus (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) = g] := by
  refine ⟨fun U y hy e => ?_, smoothProperCurveOfGenus_tfae k X.hom K g⟩
  exact (exists_lift_iff_isSmoothH0FamilyOfFibreGenus g U y _ e).trans
    (isSmoothH0FamilyOfFibreGenus_curveFamilyOfScheme_iff (hZ := hZ) g hk X hdim)

/-! ### The literal reading of part (1)(b) for `g = 0` -/

variable (B hZ) in
/-- **Part (1) of Stacks 0E83 needs "smooth of relative dimension one".** The identity
`Spec(k) → Spec(k)` of a field `k` is a family of curves (its fibre has dimension `0 ≤ 1`) which
is smooth, has `f_*𝒪 = 𝒪` universally, and has `R¹f_*𝒪` locally free of rank `0`; yet its
classifying morphism does not factor through `𝓜_0`, because the family is not of relative
dimension one. So condition (1)(b) of Stacks 0E83, with "smooth" read without a relative
dimension, does not imply (1)(a) for `g = 0`. -/
theorem not_factors_moduliSmoothCurvesOfGenus_zero_of_identity {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) :
    haveI : IsProper (Over.mk (𝟙 (Spec (.of k)))).hom := inferInstanceAs (IsProper (𝟙 _))
    ∃ hdim : topologicalKrullDim (Over.mk (𝟙 (Spec (.of k)))).left ≤ 1,
      IsSmoothFamily B hZ (curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) ∧
      HasUniversallyBijectiveGlobalFunctions B hZ
        (curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) ∧
      CurveFamily.HasGenus B hZ
        (curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) 0 ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        (y.obj (Over.mk (𝟙 U.left)) ≅
          curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) →
        ¬ ∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsSmoothH0FamilyOfFibreGenus B hZ 0),
            z ⋙ ObjectProperty.ι (IsSmoothH0FamilyOfFibreGenus B hZ 0) = y := by
  have : IsProper (Over.mk (𝟙 (Spec (.of k)))).hom := inferInstanceAs (IsProper (𝟙 _))
  have hdim0 : topologicalKrullDim (Over.mk (𝟙 (Spec (.of k)))).left = 0 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := k)).trans
      (ringKrullDim_eq_zero_of_field k)
  have hdim : topologicalKrullDim (Over.mk (𝟙 (Spec (.of k)))).left ≤ 1 :=
    hdim0.le.trans zero_le_one
  have hH : HasUniversallyBijectiveGlobalFunctions B hZ
      (curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) :=
    (hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff hk _ hdim).2 (by
      show IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Hom.appTop (𝟙 (Spec (.of k))))
      rw [Scheme.Hom.id_appTop, Category.comp_id]
      infer_instance)
  have hgen : genus (Over.mk (𝟙 (Spec (.of k)))).hom = 0 := by
    rw [genus_eq_finrank_structureSheafCohomology]
    have : IsAffine (Over.mk (𝟙 (Spec (.of k)))).left := inferInstanceAs (IsAffine (Spec (.of k)))
    have := ModuleCat.isZero_iff_subsingleton.1
      (isZero_structureSheafCohomology_of_isAffine k (Over.mk (𝟙 (Spec (.of k)))).hom 1 one_pos)
    exact Module.finrank_zero_of_subsingleton
  have hnot : ¬ IsSmoothDimOneFamily B hZ
      (curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) := by
    intro h
    obtain ⟨-, -, h1⟩ :=
      (isSmoothDimOneFamily_curveFamilyOfScheme_iff hk _ hdim
        (inferInstanceAs (Nonempty (Spec (.of k))))).1 h
    exact zero_ne_one (hdim0.symm.trans h1)
  have hG : CurveFamily.HasGenus B hZ
      (curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) 0 :=
    (CurveFamily.hasFieldPointFibreGenus_iff_hasGenus_of_hasUniversallyBijectiveGlobalFunctions
      hH 0).1
      ((hasFieldPointFibreGenus_curveFamilyOfScheme_iff hk _ hdim 0).2 hgen)
  have hS : IsSmoothFamily B hZ
      (curveFamilyOfScheme (Over.mk (𝟙 (Spec (.of k)))) B hZ hk hdim) :=
    (Space.isSmooth_yoneda_map_iff B integerBase hZ
      (integerSiteMap B hZ hk hk (𝟙 (Spec (.of k))))).2
      (inferInstanceAs (Smooth (𝟙 (Spec (.of k)))))
  exact ⟨hdim, hS, hH, hG, fun U y hy e hz =>
    hnot ((factors_moduliSmoothCurvesOfGenus_iff B hZ 0 U y hy _ e).1 hz).1⟩

end AlgebraicGeometry

end
