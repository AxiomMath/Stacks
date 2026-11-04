module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# The open substack `Curves^{lci+}` (Stacks 0DZX, parts (2) and (3))

`Curves^{lci+} = Curves^{lci} ∩ Curves^{+}` is the open substack of the stack of curves cut out
by the families whose structure morphism is a local complete intersection morphism and whose
singular locus, the set of points at which the structure morphism is not smooth, is finite over
the base with any (equivalently, some) closed subspace structure. It is an open substack by
Tag 0E0E, its two defining conditions satisfying condition (o)
(`AlgebraicGeometry.isOpenCurvesLocus_lciPlus`).

## Main results

* `AlgebraicGeometry.isFiniteNonSmoothLocus_iff_forall_isFinite` and
  `AlgebraicGeometry.isFiniteNonSmoothLocus_iff_exists_isFinite`: finiteness of the singular
  locus over the base does not depend on the closed subspace structure put on it.
* `AlgebraicGeometry.curvesLciPlus_isOpenSubstack`: **Stacks 0DZX**, `Curves^{lci+}` is an open
  substack of `Curves`.
* `AlgebraicGeometry.factors_curvesLciPlus_iff`: **Stacks 0DZX**, part (2).
* `AlgebraicGeometry.factors_curvesLciPlus_over_field_iff`: **Stacks 0DZX**, part (3), from
  `AlgebraicGeometry.isLciPlusFamily_curveFamilyOfScheme_iff`.

Part (1), smoothness of `Curves^{lci+}` over `Spec(ℤ)`, is a statement about an algebraic stack
and is not proved here.

## References

* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves^{lci+} = Curves^{lci} ∩ Curves^{+}`: the structure morphism
of the family is a local complete intersection morphism and its reduced singular locus is finite
over the base. -/
abbrev IsLciPlusFamily : ObjectProperty (CurveFamily B hZ) :=
  fun F => IsLciFamily B hZ F ∧ IsFiniteNonSmoothLocus B hZ F

/-- The singular locus of a family of curves with *any* closed subspace structure is finite over
the base exactly when it is so with the reduced one. -/
theorem isFiniteNonSmoothLocus_iff_forall_isFinite (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔
      ∀ Z : Subfunctor X.total.obj, Space.IsClosedSubspace B integerBase hZ Z →
        Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
          {x : Space.points B integerBase hZ X.total.obj |
            ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} →
        Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom) := by
  have hY := (schemeSpace X.base).property
  constructor
  · intro h Z hZcl hrange
    have hall := (CurveFamily.isFiniteNonSmoothLocus_iff_finiteNonSmoothBaseLocus_eq_univ B hZ
      X).mp h
    have hp : Space.IsProper B integerBase hZ (Z.ι ≫ X.toBase.hom) :=
      Space.isProper_comp B integerBase hZ hZcl.1 X.total.property hY Z.ι X.toBase.hom
        (Space.isProper_of_isClosedImmersion B integerBase hZ hZcl.1 X.total.property Z.ι
          hZcl.2) X.proper
    refine Space.isFinite_of_isProper_of_isLocallyQuasiFinite B integerBase hZ hZcl.1 hY _ hp
      ((Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B integerBase hZ hZcl.1 hY
        _).mpr fun z => ?_)
    have hmem : _ ∈ CurveFamily.finiteNonSmoothBaseLocus B hZ X := hall ▸ Set.mem_univ
      (Space.pointsMap B integerBase hZ Z.toFunctor (Z.ι ≫ X.toBase.hom) z)
    exact (CurveFamily.finite_nonSmoothFibre_iff_forall_isQuasiFiniteAt B hZ X Z hZcl hrange hp
      _).mp hmem z rfl
  · intro h
    obtain ⟨Z, hZcl, hrange, hred, -⟩ := CurveFamily.exists_isClosedSubspace_nonSmooth B hZ X
    exact ⟨Z, hZcl, hrange, hred, h Z hZcl hrange⟩

/-- The singular locus of a family of curves with *some* closed subspace structure is finite over
the base exactly when it is so with the reduced one. -/
theorem isFiniteNonSmoothLocus_iff_exists_isFinite (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔
      ∃ Z : Subfunctor X.total.obj, Space.IsClosedSubspace B integerBase hZ Z ∧
        Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
          {x : Space.points B integerBase hZ X.total.obj |
            ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} ∧
        Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom) := by
  refine ⟨fun ⟨Z, hZcl, hrange, _, hfin⟩ => ⟨Z, hZcl, hrange, hfin⟩, ?_⟩
  rintro ⟨Z, hZcl, hrange, hfin⟩
  have hY := (schemeSpace X.base).property
  obtain ⟨hp, hlqf⟩ := Space.isProper_and_isLocallyQuasiFinite_of_isFinite B integerBase hZ
    hZcl.1 hY _ hfin
  rw [Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B integerBase hZ hZcl.1 hY] at hlqf
  exact (CurveFamily.isFiniteNonSmoothLocus_iff_finiteNonSmoothBaseLocus_eq_univ B hZ X).mpr
    (Set.eq_univ_of_forall fun t =>
      (CurveFamily.finite_nonSmoothFibre_iff_forall_isQuasiFiniteAt B hZ X Z hZcl hrange hp
        t).mpr fun z _ => hlqf z)

/-- **Stacks 0DZX.** `Curves^{lci+} = Curves^{lci} ∩ Curves^{+}`, the strictly full subcategory of
families of curves with local complete intersection structure morphism and singular locus finite
over the base, is an open substack of `Curves`: its inclusion is representable by algebraic
spaces and an open immersion. -/
@[stacks 0DZX "the open substack Curves^{lci+} = Curves^{lci} ∩ Curves^{+} of Curves"]
theorem curvesLciPlus_isOpenSubstack :
    ObjectProperty.IsClosedUnderIsomorphisms
        (fun F : CurveFamily B hZ => IsLciFamily B hZ F ∧ IsFiniteNonSmoothLocus B hZ F) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ _ (isOpenCurvesLocus_lciPlus B hZ).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ _ (isOpenCurvesLocus_lciPlus B hZ).prop_of_hom) :=
  isOpenImmersion_curvesSubstackInclusion (isOpenCurvesLocus_lciPlus B hZ)

/-- **Stacks 0DZX, part (2).** The classifying morphism of a family of curves `X ⟶ S` factors
through `Curves^{lci+}` exactly when `X ⟶ S` is a local complete intersection morphism and its
singular locus, with any (equivalently, some) closed subspace structure, is finite over `S`. -/
@[stacks 0DZX "part (2): the classifying morphism of a family of curves factors through \
Curves^{lci+} iff the family is a local complete intersection morphism whose singular locus, with \
any (equivalently, some) closed subspace structure, is finite over the base"]
theorem factors_curvesLciPlus_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    let X := y.obj (Over.mk (𝟙 U.left))
    ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        (IsLciPlusFamily B hZ).FullSubcategory,
        z ⋙ (IsLciPlusFamily B hZ).ι = y) ↔
      IsLciFamily B hZ X ∧
        ∀ Z : Subfunctor X.total.obj, Space.IsClosedSubspace B integerBase hZ Z →
          Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
            {x : Space.points B integerBase hZ X.total.obj |
              ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} →
          Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)) ∧
    ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        (IsLciPlusFamily B hZ).FullSubcategory,
        z ⋙ (IsLciPlusFamily B hZ).ι = y) ↔
      IsLciFamily B hZ X ∧
        ∃ Z : Subfunctor X.total.obj, Space.IsClosedSubspace B integerBase hZ Z ∧
          Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
            {x : Space.points B integerBase hZ X.total.obj |
              ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} ∧
          Space.IsFinite B integerBase hZ (Z.ι ≫ X.toBase.hom)) := by
  intro X
  have h := factors_curvesSubstack_iff (isOpenCurvesLocus_lciPlus B hZ) U y hy
  exact ⟨h.trans (and_congr_right fun _ => isFiniteNonSmoothLocus_iff_forall_isFinite B hZ X),
    h.trans (and_congr_right fun _ => isFiniteNonSmoothLocus_iff_exists_isFinite B hZ X)⟩

/-- The family of curves of a proper scheme `X` of dimension at most one over a field `k` lies in
`Curves^{lci+}` exactly when `X` is a local complete intersection over `k` and `X ⟶ Spec(k)` is
smooth except at finitely many points. -/
theorem isLciPlusFamily_curveFamilyOfScheme_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    IsLciPlusFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      IsLocalCompleteIntersectionMorphism X.hom ∧ (X.hom.smoothLocus : Set X.left)ᶜ.Finite := by
  let g := integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
    X.hom
  have hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom :=
    Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g
      (inferInstanceAs (QuasiCompact X.hom))
  have hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 (inferInstanceAs (IsSeparated X.hom))
  have hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2
      (inferInstanceAs (QuasiSeparated X.hom))
  exact and_congr (isLciFamily_curveFamilyOfSchemeMorphism_iff B hZ g
      (inferInstanceAs (Flat X.hom)) (inferInstanceAs (IsProper X.hom))
      (inferInstanceAs (LocallyOfFinitePresentation X.hom)) hqc hsep hqsep hdim)
    (isFiniteNonSmoothLocus_curveFamilyOfSchemeMorphism_iff B hZ g
      (inferInstanceAs (Flat X.hom)) (inferInstanceAs (IsProper X.hom))
      (inferInstanceAs (LocallyOfFinitePresentation X.hom)) hqc hsep hqsep hdim k rfl)

/-- **Stacks 0DZX, part (3).** Let `X` be a proper scheme of dimension at most one over a field
`k` (with `Spec k` in the site, so that the classifying morphism `Spec k ⟶ Curves` of `X` exists).
The classifying morphism of `X` factors through `Curves^{lci+}` exactly when `X` is a local
complete intersection over `k` and `X ⟶ Spec(k)` is smooth except at finitely many points. -/
@[stacks 0DZX "part (3): for a proper scheme of dimension at most one over a field, the \
classifying morphism factors through Curves^{lci+} iff the scheme is a local complete intersection \
over the field and is smooth over it except at finitely many points"]
theorem factors_curvesLciPlus_over_field_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        (IsLciPlusFamily B hZ).FullSubcategory,
        z ⋙ (IsLciPlusFamily B hZ).ι = y) ↔
      IsLocalCompleteIntersectionMorphism X.hom ∧ (X.hom.smoothLocus : Set X.left)ᶜ.Finite := by
  rw [factors_curvesSubstack_iff_of_iso (isOpenCurvesLocus_lciPlus B hZ) U y hy _ e]
  exact isLciPlusFamily_curveFamilyOfScheme_iff B hZ k hk X hdim

end AlgebraicGeometry

end
