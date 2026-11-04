module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField

/-!
# `Curves^{semistable} = ∐_{g ≥ 1} Curves^{semistable}_g` (towards Stacks 0E71)

Stacks 0E71 decomposes the open substack `Curves^{semistable}` of the stack of curves (Stacks
0E70) into open and closed substacks `Curves^{semistable}_g`, `g ≥ 1`. A family of curves
`f : X → S` lies in the genus-`g` piece when it is semistable and `R¹f_*𝒪_X` is a locally free
`𝒪_S`-module of rank `g`. The source's proof combines Stacks 0E70 with Stacks 0E6V.

The genus-`g` piece is base's `AlgebraicGeometry.IsSemistableCurveFamilyOfFibreGenus`: semistable
with all fibres of genus `g`. This file proves that, given

* `hss`, condition (o) for the semistable families (the open substack of Stacks 0E70), and
* the two inputs about `R¹f_*𝒪_X` of
  `StacksFrontier/AlgebraicGeometry/Quot/C1590Private/CurvesPrestableGenus.lean`
  (`AlgebraicGeometry.C1590Private.PrestableGenusLociOpen` and
  `AlgebraicGeometry.C1590Private.PrestableHasGenusIff`),

each `Curves^{semistable}_g` is an open substack of `Curves` contained in `Curves^{semistable}`.
Its families are the semistable families with `R¹f_*𝒪_X` locally free of rank `g`, which is part
(1) of Stacks 0E71. Over every semistable family the genus loci of positive genus are open and
closed, pairwise disjoint and cover the base, and the genus-zero locus is empty.

## Main results

* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus`:
  condition (o) for `Curves^{semistable}_g`.
* `AlgebraicGeometry.C1590Private.isSemistableCurveFamilyOfFibreGenus_iff_hasGenus`: the
  families of `Curves^{semistable}_g` are the semistable families with `R¹f_*𝒪_X` locally free of
  rank `g`.
* `AlgebraicGeometry.C1590Private.semistable_genus_decomposition`: the decomposition over a
  semistable family.
* `AlgebraicGeometry.C1590Private.curvesSemistableOfGenus_isOpenSubstack_and_factors_iff_of`:
  the open substacks `Curves^{semistable}_g`, part (1) of Stacks 0E71, and the decomposition.
* `AlgebraicGeometry.C1590Private.factors_curvesSemistableOfGenus_over_field_iff`: part (2)(a)
  over a field, reduced to semistability of the family of the scheme and its genus.
* `AlgebraicGeometry.C1590Private.factors_curvesSemistableOfGenus_over_field_iff_noRationalTail`
  and `C1590Private.factors_curvesSemistableOfGenus_over_field_iff_globallyGenerated`: part (2),
  (a) ⇔ (b) and (a) ⇔ (c), from part (2) of Stacks 0E70.

## Implementation notes

No declaration here carries a `stacks` attribute: `hss`, `hopen` and `hR` are arguments.

## References

* [Stacks Project, Tag 0E71](https://stacks.math.columbia.edu/tag/0E71)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public section

open CategoryTheory
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) of Stacks 0E0E for `Curves^{semistable}_g`**, from the open substack
`Curves^{semistable}` (Stacks 0E70, the hypothesis `hss`) and the openness of the genus loci of
prestable families (the input `hopen`). -/
theorem isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus
    (hss : IsOpenCurvesLocus B hZ (IsSemistableCurveFamily B hZ))
    (hopen : PrestableGenusLociOpen B hZ) (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g) :=
  isOpenCurvesLocus_and_hasFibresOfGenus hss (fun _ h => h.1) hopen g

/-- **The families of `Curves^{semistable}_g`**, given the input `hR`: a family of curves is
semistable of genus `g` exactly when it is semistable and `R¹f_*𝒪_X` is a locally free
`𝒪_S`-module of rank `g`, condition (1)(b) of Stacks 0E71. -/
theorem isSemistableCurveFamilyOfFibreGenus_iff_hasGenus (hR : PrestableHasGenusIff B hZ)
    (g : ℕ) (X : CurveFamily B hZ) :
    IsSemistableCurveFamilyOfFibreGenus B hZ g X ↔
      IsSemistableCurveFamily B hZ X ∧ CurveFamily.HasGenus B hZ X g :=
  ⟨fun h => ⟨h.1, (hR X h.1.1 g).2 h.2⟩, fun h => ⟨h.1, (hR X h.1.1 g).1 h.2⟩⟩

/-- **The decomposition of `Curves^{semistable}` by genus over a semistable family**, given the
input `hopen`. For a semistable family of curves `G` over `S`, the genus loci `Ω_g` of `G` are
open and closed in `S`, pairwise disjoint, the genus-zero locus is empty and those of positive
genus cover `S`. A family of curves mapping to `G` is semistable of genus `g` exactly when its
morphism of bases lands in `Ω_g`. That is, the base change of `Curves^{semistable}_g ⊂
Curves^{semistable}` along `S → Curves^{semistable}` is the open and closed subscheme `Ω_g`, and
these, for `g ≥ 1`, partition `S`. -/
theorem semistable_genus_decomposition (hopen : PrestableGenusLociOpen B hZ)
    (G : CurveFamily B hZ) (hG : IsSemistableCurveFamily B hZ G) :
    ∃ Ω : ℕ → Set ((BigFppfOver.toScheme B integerBase hZ).obj G.base),
      (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
        Ω 0 = ∅ ∧ ⋃ (g : ℕ) (_ : 1 ≤ g), Ω g = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          IsSemistableCurveFamilyOfFibreGenus B hZ g F ↔
            Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ Ω g :=
  ⟨G.genusLocus, fun g => ⟨hopen G hG.1 g,
      isClosed_genusLocus_of_forall_isOpen G (hopen G hG.1) g⟩,
    (disjoint_genusLocus_and_iUnion_genusLocus G).1, IsSemistableCurveFamily.genusLocus_zero hG,
    IsSemistableCurveFamily.iUnion_genusLocus hG,
    fun _ _ a => isSemistableCurveFamilyOfFibreGenus_iff_range_subset a hG⟩

/-- **Stacks 0E71, the decomposition and part (1), from Stacks 0E70 and the inputs about
`R¹f_*𝒪_X`.** Let `hss` be condition (o) for the semistable families (Stacks 0E70), and let `hopen`
and `hR` be the two inputs about `R¹f_*𝒪_X`. Then for every `g`:

* `Curves^{semistable}_g` is an open substack of `Curves` contained in `Curves^{semistable}`;
* part (1): the classifying morphism of a family of curves `f : X → S` factors through
  `Curves^{semistable}_g` exactly when `f` is semistable and `R¹f_*𝒪_X` is locally free of rank
  `g`.

Moreover, over every semistable family with base `S`, the loci of the `Curves^{semistable}_g` are
open and closed subsets of `S`, pairwise disjoint, empty for `g = 0`, and covering `S` for
`g ≥ 1`. So `Curves^{semistable} = ∐_{g ≥ 1} Curves^{semistable}_g` as open and closed
substacks. -/
theorem curvesSemistableOfGenus_isOpenSubstack_and_factors_iff_of
    (hss : IsOpenCurvesLocus B hZ (IsSemistableCurveFamily B hZ))
    (hopen : PrestableGenusLociOpen B hZ) (hR : PrestableHasGenusIff B hZ) :
    (∀ g : ℕ,
      ((show ObjectProperty (CurveFamily B hZ) from
          IsSemistableCurveFamilyOfFibreGenus B hZ g).IsClosedUnderIsomorphisms ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g)
            (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus hss hopen g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g)
            (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus hss hopen g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ,
        IsSemistableCurveFamilyOfFibreGenus B hZ g X → IsSemistableCurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsSemistableCurveFamilyOfFibreGenus B hZ g),
            z ⋙ ObjectProperty.ι (IsSemistableCurveFamilyOfFibreGenus B hZ g) = y) ↔
          IsSemistableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
            CurveFamily.HasGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g)) ∧
    ∀ G : CurveFamily B hZ, IsSemistableCurveFamily B hZ G →
      ∃ Ω : ℕ → Set ((BigFppfOver.toScheme B integerBase hZ).obj G.base),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          Ω 0 = ∅ ∧ ⋃ (g : ℕ) (_ : 1 ≤ g), Ω g = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsSemistableCurveFamilyOfFibreGenus B hZ g F ↔
              Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ Ω g :=
  ⟨fun g => ⟨isOpenImmersion_curvesSubstackInclusion
      (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus hss hopen g), fun _ h => h.1,
      fun U y hy => (factors_curvesSubstack_iff
        (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus hss hopen g) U y hy).trans
          (isSemistableCurveFamilyOfFibreGenus_iff_hasGenus hR g _)⟩,
    fun G hG => semistable_genus_decomposition hopen G hG⟩

/-! ### Part (2): a proper scheme of dimension at most one over a field -/

/-- **The genus of the family of curves of a proper scheme over a field.** For a proper scheme
`X` of dimension at most one over a field `k`, all fibres of its family of curves have genus `n`
exactly when `X` has genus `n` over `k`. -/
theorem hasFibresOfGenus_curveFamilyOfScheme_iff {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [IsProper X.hom] (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (n : ℕ) :
    (curveFamilyOfScheme X B hZ hk hdim).HasFibresOfGenus n ↔ genus X.hom = n :=
  CurveFamily.hasFibresOfGenus_curveFamilyOfSchemeMorphism_iff
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk X.hom)
    k rfl ‹_› hdim n

/-- **Clause (2) of Stacks 0E71, the genus.** For a proper scheme `X` of dimension at most one
over a field `k`, its family of curves is semistable of genus `n` exactly when it is semistable
and `X` has genus `n` over `k`. -/
theorem isSemistableCurveFamilyOfFibreGenus_curveFamilyOfScheme_iff {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
    (hdim : topologicalKrullDim X.left ≤ 1) (n : ℕ) :
    IsSemistableCurveFamilyOfFibreGenus B hZ n (curveFamilyOfScheme X B hZ hk hdim) ↔
      IsSemistableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ∧ genus X.hom = n :=
  and_congr_right' (hasFibresOfGenus_curveFamilyOfScheme_iff X hk hdim n)

/-- **Clause (2)(a) of Stacks 0E71 read on a scheme-valued point.** Given condition (o) for
`Curves^{semistable}_g`, the classifying morphism `Spec k → Curves` of a proper scheme `X` of
dimension at most one over a field factors through `Curves^{semistable}_g` exactly when the family
of curves of `X` is semistable and `X` has genus `g`. Here the classifying morphism is any
scheme-valued point `y` whose family is identified with that of `X`, which is part (2) of Stacks
0E0E. -/
theorem factors_curvesSemistableOfGenus_over_field_iff {g : ℕ}
    (hssg : IsOpenCurvesLocus B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g))
    {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamilyOfFibreGenus B hZ g) = y) ↔
      IsSemistableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ∧ genus X.hom = g :=
  (factors_curvesSubstack_iff_of_iso hssg U y hy _ e).trans
    (isSemistableCurveFamilyOfFibreGenus_curveFamilyOfScheme_iff X hk hdim g)

/-- **Stacks 0E71, part (2), (a) ⇔ (b).** Let `g ≥ 1`. Given condition (o) for
`Curves^{semistable}_g`, the classifying morphism `Spec k → Curves` of a proper scheme `X` of
dimension at most one over a field `k` factors through `Curves^{semistable}_g` exactly when the
singularities of `X` are at-worst-nodal, `dim X = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is `g`
and `X` has no rational tail. This is part (2) of Stacks 0E70, with the genus added. -/
theorem factors_curvesSemistableOfGenus_over_field_iff_noRationalTail {g : ℕ} (hg : 1 ≤ g)
    (hssg : IsOpenCurvesLocus B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g))
    {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamilyOfFibreGenus B hZ g) = y) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g ∧
          ∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C := by
  rw [factors_curvesSemistableOfGenus_over_field_iff hssg X hk hdim U y hy e,
    isSemistableCurveFamily_curveFamilyOfScheme_iff X hk hdim]
  constructor
  · rintro ⟨⟨hn, hd, hΓ, -, hr⟩, hgen⟩
    exact ⟨hn, hd, hΓ, hgen, hr⟩
  · rintro ⟨hn, hd, hΓ, hgen, hr⟩
    exact ⟨⟨hn, hd, hΓ, hgen ▸ hg, hr⟩, hgen⟩

/-- **Stacks 0E71, part (2), (a) ⇔ (c).** Given condition (o) for `Curves^{semistable}_g`, the
classifying morphism `Spec k → Curves` of a proper scheme `X` of dimension at most one over a
field `k` factors through `Curves^{semistable}_g` exactly when the singularities of `X` are
at-worst-nodal, `dim X = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is `g` and `ω_X^{⊗m}` is
globally generated for every `m ≥ 2`. This is part (2)(c) of Stacks 0E70, with the genus added;
the dualizing sheaf `ω_X` is invertible because `X` is nodal. -/
theorem factors_curvesSemistableOfGenus_over_field_iff_globallyGenerated {g : ℕ}
    (hssg : IsOpenCurvesLocus B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g))
    {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamilyOfFibreGenus B hZ g) = y) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
        (hdim1 : topologicalKrullDim X.left = 1)
        (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)),
        haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hΓ
        haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
        letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
          hdim1 hnodal
        genus X.hom = g ∧ ∀ m : ℕ, 2 ≤ m → SheafOfModules.IsGeneratedByGlobalSections
          (tensorPower X.left.presheaf X.left.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k))) m) := by
  rw [factors_curvesSemistableOfGenus_over_field_iff hssg X hk hdim U y hy e,
    isSemistableCurveFamily_curveFamilyOfScheme_iff_globallyGenerated X hk hdim]
  constructor
  · rintro ⟨⟨hn, hd, hΓ, hgg⟩, hgen⟩
    exact ⟨hn, hd, hΓ, hgen, hgg⟩
  · rintro ⟨hn, hd, hΓ, hgen, hgg⟩
    exact ⟨⟨hn, hd, hΓ, hgg⟩, hgen⟩

end AlgebraicGeometry.C1590Private

end
