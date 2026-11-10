module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallDerivedHomLocalModel

/-!
# Local models of `RSheafHom(E, 𝒢)` on an algebraic space, for `E` perfect

Let `X` be an algebraic space, `E` a perfect object of `D(𝒪_X)` and `𝒢` a complex of
`𝒪_X`-modules.  The derived internal Hom `RSheafHom(E, 𝒢)` (with sections in the module universe,
`AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor`) is, on the members of a family
covering the final object of the small étale site, the internal Hom complex `SheafHom^•(P, 𝒢|_W)`
out of a strictly perfect complex `P`, uniformly bounded near a compact set `Z` and with the
members away from `Z` lying entirely outside `Z`.

## Main results

* `AlgebraicGeometry.Space.notMem_supportOfSheaf_of_isZero_over`: a module vanishing on an étale
  chart has no point of that chart in its support.
* `AlgebraicGeometry.Space.exists_coversTop_uniform_hom_models`: the local models.

## References

* [Stacks Project, Tag 0DKK](https://stacks.math.columbia.edu/tag/0DKK)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective pointTopology

open Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall (exists_model_of_map)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The derived category of the modules on a slice of the small étale site, built from the abelian
structure named in `AlgebraicGeometry.Space.smallEtaleRingedSite_over_abelian`. -/
local instance (priority := 20000) sliceHasDerivedCategoryHom
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) :=
  @HasDerivedCategory.standard _ _ (smallEtaleRingedSite_over_abelian B S hS X.1 X.2 U)

/-- A slice of the small étale site is essentially small. -/
local instance essentiallySmall_smallEtale_over (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    EssentiallySmall.{u} ((smallEtaleRingedSite B S hS X.1 X.2).over U).C :=
  Stacks.essentiallySmall_over.{u} U

/-- **A module vanishing on an étale chart has no point of the chart in its support.**  The
restriction to the slice at the chart is, through Stacks 04M0, the étale restriction to the
algebraic space the chart represents, whose support is the inverse image of the support of the
module (Stacks 04KB). -/
theorem notMem_supportOfSheaf_of_isZero_over (M : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1)
    (h : IsZero ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) W).obj M))
    (z : chartScheme W) :
    chartSchemeToPoints B S hS X.1 W z ∉
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) := by
  let Mp := (etaleModulePullback B S hS (chartToSpace B S hS X W)
    (isEtale_chartToSpace B S hS X W)).obj M
  have hz : IsZero ((chartModuleSliceEquiv B S hS X W).inverse.obj Mp) :=
    h.of_iso ((chartSliceOverIso B S hS X W).app M).symm
  have hMp : IsZero Mp :=
    (Functor.map_isZero (chartModuleSliceEquiv B S hS X W).functor hz).of_iso
      ((chartModuleSliceEquiv B S hS X W).counitIso.app Mp).symm
  have hsupp := (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X W) Mp).2 hMp
  rw [supportOfSheaf_chartToSpace] at hsupp
  intro hx
  let p := (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W)).symm z
  have hp : chartSchemeToPoints B S hS X.1 W z = pointsMap B S hS _ W.obj.hom p := by
    rw [← chartSchemeToPoints_eq B S hS X W p]
    exact congrArg _ ((pointsEquivScheme B S hS _).apply_symm_apply z).symm
  have : p ∈ pointsMap B S hS (chartSpace B S hS X W).1 (chartToSpace B S hS X W).hom ⁻¹'
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) := by
    change pointsMap B S hS _ W.obj.hom p ∈
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)
    rw [← hp]
    exact hx
  exact hsupp.subset this

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **Local models of `RSheafHom(E, 𝒢)` in a uniform range of degrees near a compact set.**  For
`E` perfect and `Z ⊆ |X|` compact and closed there are an integer `N` and a family of objects
covering the final object of the small étale site, each member `W` of which carries a strictly
perfect complex `P` with `RSheafHom(E, 𝒢)|_W ≅ Q(SheafHom^•(P, 𝒢|_W))`, where either `P` is zero
outside `[-N, N]` or all the points of `W` lie outside `Z`; and every point outside `Z` is a point
of a member of the second kind. -/
theorem exists_coversTop_uniform_hom_models
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (Z : Set (points B S hS X.1))
    (hZc : IsCompact Z) (hZcl : IsClosed Z) :
    ∃ (N : ℕ) (I : Type (u + 1)) (W : I → (smallEtaleRingedSite B S hS X.1 X.2).C),
      (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop W ∧
      (∀ i, ∃ P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).over (W i))) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).over (W i)) P ∧
          Nonempty ((RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
              (smallEtaleRingedSite B S hS X.1 X.2) (W i)).obj
                (((RingedSite.derivedSheafHomSmallBifunctor
                  (smallEtaleRingedSite B S hS X.1 X.2)).obj (op E)).obj
                    (DerivedCategory.Q.obj G)) ≅
            DerivedCategory.Q.obj (RingedSite.sheafHomComplexSmall
              ((smallEtaleRingedSite B S hS X.1 X.2).over (W i)) P
              ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex G (W i)))) ∧
          ((∀ n : ℤ, n < -N ∨ (N : ℤ) < n → IsZero (P.X n)) ∨
            ∀ z : chartScheme (W i), chartSchemeToPoints B S hS X.1 (W i) z ∉ Z)) ∧
      ∀ x : points B S hS X.1, x ∉ Z → ∃ (i : I) (z : chartScheme (W i)),
        (∀ z' : chartScheme (W i), chartSchemeToPoints B S hS X.1 (W i) z' ∉ Z) ∧
          chartSchemeToPoints B S hS X.1 (W i) z = x := by
  classical
  let Xs := smallEtaleRingedSite B S hS X.1 X.2
  obtain ⟨E', hE', ⟨eE⟩⟩ := hE
  obtain ⟨K, V, hV, hmod⟩ := Xs.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex E' hE'
  choose P hP q hq using hmod
  choose Nk hNk using fun k => exists_bound_of_isStrictlyPerfect B S hS X (V k) (P k) (hP k)
  obtain ⟨F, I, W, κ, hW, hmap, hkind, hcov⟩ :=
    exists_coversTop_finite_near_over B S hS X hV Z hZc hZcl
  refine ⟨F.sup Nk, I, W, hW, fun i => ?_, hcov⟩
  obtain ⟨P', hP', hz, q', hq'⟩ := exists_model_of_map Xs E' (hmap i).some (P (κ i)) (hP (κ i))
    (q (κ i)) (hq (κ i))
  refine ⟨P', hP', ⟨RingedSite.restrictDerivedSheafHomSmallIsoOfModel Xs E E' eE (W i) P' hP' q'
    hq' G⟩, ?_⟩
  rcases hkind i with hk | hout
  · have hle : Nk (κ i) ≤ F.sup Nk := Finset.le_sup hk
    exact Or.inl fun n hn => hz n (hNk (κ i) n (by omega))
  · exact Or.inr hout

end AlgebraicGeometry.Space

end
