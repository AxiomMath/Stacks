module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionInduction

/-!
# `RΓ_c(X_k̄, K)` is perfect when `j_! K` is in `D_ctf` of a projective curve

Let `j : X ⟶ X̄` be a compactification of a scheme `X` over a field `k` by a projective curve
`X̄`, `k̄` an algebraic closure of `k`, `Λ` a finite ring and `K` a bounded below complex of
sheaves of `Λ`-modules on `X` with `j_! K ∈ D_ctf(X̄, Λ)`.  The compactly supported cohomology
`RΓ_c(X_k̄, K) = RΓ(Spec k̄, R(p_k̄)_*((j_! K)|_{X̄_k̄}))`
(`Stacks.EtaleCohomology.compactSupportFrobeniusCohomology`) is a perfect complex of
`Λ`-modules: it is `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`, which is perfect by [Stacks, Tag 03TV].

## Main results

* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_of_isCtf`: `RΓ_c(X_k̄, K)`
  is perfect when `j_! K ∈ D_ctf(X̄, Λ)`.
* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_of_isCtf_of_isProjective`:
  the same for `X` quasi-compact over `k` and `K ∈ D_ctf(X, Λ)`.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **`RΓ_c(X_k̄, K)` is perfect** for a compactification `j : X ⟶ X̄` by a projective curve and
`K` with `j_! K ∈ D_ctf(X̄, Λ)`. -/
theorem isPerfect_compactSupportFrobeniusCohomology_of_isCtf (B : BigEtaleSite.{u})
    (Λ : Type r) [Ring Λ] [Finite Λ] {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (hB : B.Contains j.space)
    (hcurve : IsCurve k j.toBase) (hproj : IsProjective j.toBase)
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hK : IsCtf.{u, r} B ⟨j.space, hB⟩ Λ (DerivedCategory.Q.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K).obj)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)) := by
  let L := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K
  have h := isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf B ⟨j.space, hB⟩ Λ
    j.toBase kbar hcurve hproj (DerivedCategory.Plus.Q.obj L) hK
  refine StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso ?_) h
  exact ((etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app _).symm ≪≫
    (etaleModuleDerivedGlobalSections.{u, r} Λ _).mapIso
      ((Functor.mapDerivedCategoryPlusQIso (etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar))).app L).symm

/-- **`RΓ_c(X_k̄, K)` is perfect for `K ∈ D_ctf(X, Λ)`**, `X` quasi-compact over `k`, and a
compactification `j : X ⟶ X̄` by a projective curve. -/
theorem isPerfect_compactSupportFrobeniusCohomology_of_isCtf_of_isProjective
    (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] [Finite Λ] {k : Type u} [Field k]
    {X : B.Scheme} {f : X.obj ⟶ Spec (.of k)} [QuasiCompact f] (j : CompactificationOf (Over.mk f))
    (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
    (hB : B.Contains j.space) (hcurve : IsCurve k j.toBase) (hproj : IsProjective j.toBase)
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Q.obj K.obj)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)) := by
  let Xb : B.Scheme := ⟨j.space, hB⟩
  let jj : X ⟶ Xb := ObjectProperty.homMk j.immersion
  have : IsOpenImmersion (B.inclusion.map jj) := inferInstanceAs (IsOpenImmersion j.immersion)
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace Xb.obj := QuasiCompact.compactSpace_of_compactSpace j.toBase
  have : QuasiSeparatedSpace Xb.obj := quasiSeparatedSpace_of_quasiSeparated j.toBase
  let C : TopologicalSpace.Closeds j.space :=
    ⟨(Set.range j.immersion.base)ᶜ, j.immersion.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let i : (Scheme.IdealSheafData.vanishingIdeal C).subscheme ⟶ j.space :=
    (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hZB : B.Contains (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    Scheme.size_lt_of_isClosedImmersion i hB
  let ii : (⟨_, hZB⟩ : B.Scheme) ⟶ Xb := ObjectProperty.homMk i
  have : IsClosedImmersion (B.inclusion.map ii) := inferInstanceAs (IsClosedImmersion i)
  have hrange : Set.range i.base = (Set.range j.immersion.base)ᶜ :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  have hij : Set.range (B.inclusion.map jj).base = (Set.range (B.inclusion.map ii).base)ᶜ := by
    change Set.range j.immersion.base = (Set.range i.base)ᶜ
    rw [hrange, compl_compl]
  exact isPerfect_compactSupportFrobeniusCohomology_of_isCtf B Λ j kbar hB hcurve hproj K
    (IsCtf.extensionByZero B Λ jj ii hij hK)

end Stacks.EtaleCohomology

end
