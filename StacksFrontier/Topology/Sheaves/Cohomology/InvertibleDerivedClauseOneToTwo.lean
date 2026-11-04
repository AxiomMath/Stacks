module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalPairing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualIsPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RestrictDerivedMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.StrictlyPerfectIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedFlatRestrictScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseThreeToTwo
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct

/-!
# Clause (1) of Stacks 0FPG implies clause (2)

Let `M` be an invertible object of `D(𝒪_X)` with inverse `N`. Both are perfect (Stacks 0FPD), so
near every point they are represented by strictly perfect complexes `P`, `P'`, and
`Tot(P ⊗ P') ≅ 𝒪_X[0]` there in the derived category. By Stacks 08C9 this isomorphism is, after
shrinking, a homotopy equivalence of complexes, and over the global sections of a small open it
becomes a homotopy equivalence `Tot(Γ(P) ⊗ Γ(P')) ≃ Γ(𝒪)[0]` of bounded complexes of finite
projective modules (Stacks 0FPF). The ring-level structure of invertible objects (Stacks 0FNT)
then splits the cohomology of `M` near the point by idempotents, and these local splittings glue
to clause (2).

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite TopologicalSpace StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.MonoidalDerived

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable (X : RingedSpace.{u, u})

attribute [local instance] HasDerivedCategory.standard in
/-- **A tensor inverse in `D(𝒪_X)` restricts to a derived tensor pairing of local strictly perfect
representatives.** -/
public def localDerivedPairing [HasDerivedCategory.{d} (Mod X.sheaf)] (W : Opens X.carrier)
    (M N : DerivedModules X.sheaf)
    (e : letI := derivedCategoryMonoidalCategory X; M ⊗ N ≅ 𝟙_ (DerivedModules X.sheaf))
    (P P' : CochainComplex (Mod (X.restrict W.isOpenEmbedding).sheaf) ℤ)
    (hP : IsStrictlyPerfect P) (hP' : IsStrictlyPerfect P')
    (φ : DerivedCategory.Q.obj P ≅
      (LeftDualPerfect.restrictMod X W).mapDerivedCategory.obj M)
    (φ' : DerivedCategory.Q.obj P' ≅
      (LeftDualPerfect.restrictMod X W).mapDerivedCategory.obj N) :
    DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex (X.restrict W.isOpenEmbedding).sheaf).obj
          P).obj P') ≅
      DerivedCategory.Q.obj (LeftDualPerfect.unitComplex (X.restrict W.isOpenEmbedding)) :=
  letI := derivedCategoryMonoidalCategory X
  letI := derivedCategoryMonoidalCategory (X.restrict W.isOpenEmbedding)
  letI := LeftDualPerfect.restrictDerivedMonoidal X W
  ((symmetricMonoidalDerivedCategory (X.restrict W.isOpenEmbedding)).comparison P P'
      (RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect P hP)
      (RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect P' hP')).symm ≪≫
    tensorIso φ φ' ≪≫ Functor.Monoidal.μIso _ M N ≪≫
    (LeftDualPerfect.restrictMod X W).mapDerivedCategory.mapIso e ≪≫
    (Functor.Monoidal.εIso _).symm ≪≫
    (symmetricMonoidalDerivedCategory (X.restrict W.isOpenEmbedding)).unitIso

/-- A complex of `𝒪_Y`-modules, in the spelling of the module category over the ring sheaf. -/
public abbrev modComplex {Y : RingedSpace.{u, u}} (K : CochainComplex (OXMod.{u} Y) ℤ) :
    CochainComplex (Mod.{u} Y.sheaf) ℤ :=
  K

variable {X} in
/-- A strictly perfect model over `U` of a complex on `X`, restricted to an open `W ≤ U`, is
isomorphic in the derived category to the restriction of the complex to `W`. -/
public def localFactorIso {U W : Opens X.carrier} (h : W ≤ U)
    (E : CochainComplex (OXMod.{u} X) ℤ)
    (P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ)
    (f : P ⟶ ((RingedSpace.restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
    (hf : QuasiIso f) :
    DerivedCategory.Q.obj
        (modComplex.{u} (((X.restrictModulesOfLE h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj
        (((LeftDualPerfect.restrictMod X W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) :=
  (_root_.CochainComplex.derivedIsoOfQuasiIso
      (((X.restrictModulesOfLE h).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      (@HomologicalComplex.quasiIso_map_of_preservesHomology _ _ _ _ _ _ _ _ _ _ f
        (X.restrictModulesOfLE h) _ _ _ _ _ _ hf) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (X.restrictModulesOfLECompIso h)
        (ComplexShape.up ℤ)).app E) :)

variable {X} in
/-- The cohomology sheaves of a complex restricted to an open, read through a derived
isomorphism. -/
public def homologyIsoOfDerivedIso {W : Opens X.carrier}
    (E : CochainComplex (OXMod.{u} X) ℤ)
    (P : CochainComplex (OXMod.{u} (X.restrict W.isOpenEmbedding)) ℤ)
    (ψ : DerivedCategory.Q.obj (modComplex.{u} P) ≅
      DerivedCategory.Q.obj (((LeftDualPerfect.restrictMod X W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E)) (k : ℤ) :
    (restrictModules X W).obj (E.homology k) ≅ (modComplex.{u} P).homology k :=
  (restrictModulesHomologyIso E W k).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors (Mod (X.restrict W.isOpenEmbedding).sheaf) k).app
      _).symm ≪≫
    (DerivedCategory.homologyFunctor (Mod (X.restrict W.isOpenEmbedding).sheaf) k).mapIso ψ.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (Mod (X.restrict W.isOpenEmbedding).sheaf) k).app
      (modComplex.{u} P)

/-- **The implication `(1) ⟹ (2)` of Stacks 0FPG.** If `M` is an invertible object of `D(𝒪_X)`,
there is a locally finite direct product decomposition `𝒪_X = ∏ 𝒪_n` and invertible
`𝒪_n`-modules `ℋ^n` with `M = ⨁ ℋ^n[-n]`. -/
@[stacks 0FPG "clause (1) implies clause (2): an invertible object of D(𝒪_X) has a locally finite \
invertible module decomposition"]
public theorem hasInvertibleModuleDecomposition_of_isInvertibleObject
    [inst : HasDerivedCategory.{d} (Mod X.sheaf)] (M : DerivedModules X.sheaf)
    (hM : IsInvertibleObject M) : HasInvertibleModuleDecomposition X M := by
  classical
  let := derivedCategoryMonoidalCategory X
  obtain ⟨H⟩ := hM
  have hN : IsInvertibleObject H.inv := ⟨⟨M, H.isoRight, H.isoLeft⟩⟩
  obtain ⟨N₁, ⟨p₁⟩⟩ := exists_exactPairing_of_isInvertibleObject M ⟨H⟩
  obtain ⟨N₂, ⟨p₂⟩⟩ := exists_exactPairing_of_isInvertibleObject H.inv hN
  let instO : HasDerivedCategory.{d} (OXMod.{u} X) := inst
  have hMp : @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X instO M :=
    LeftDualPerfect.isPerfect_of_exactPairing X M N₁ p₁
  have hNp : @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X instO H.inv :=
    LeftDualPerfect.isPerfect_of_exactPairing X H.inv N₂ p₂
  obtain ⟨E, ⟨I, U, hU, hE⟩, ⟨eM⟩⟩ := hMp
  obtain ⟨E', ⟨I', U', hU', hE'⟩, ⟨eN⟩⟩ := hNp
  choose P hP f hf using hE
  choose P' hP' f' hf' using hE'
  have key : ∀ x : X.carrier, ∃ V : Opens X.carrier, x ∈ V ∧ Nonempty (LocalSplitting E E' V) := by
    intro x
    obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top U hU x
    obtain ⟨j, hj⟩ := exists_mem_of_iSup_eq_top U' hU' x
    let W := U i ⊓ U' j
    let ψ := localFactorIso (inf_le_left : W ≤ U i) E (P i) (f i) (hf i)
    let ψ' := localFactorIso (inf_le_right : W ≤ U' j) E' (P' j) (f' j) (hf' j)
    have hPw := RingedSpace.isStrictlyPerfect_restrictModulesOfLE (inf_le_left : W ≤ U i) (hP i)
    have hPw' :=
      RingedSpace.isStrictlyPerfect_restrictModulesOfLE (inf_le_right : W ≤ U' j) (hP' j)
    let ρ := (LeftDualPerfect.restrictMod X W).mapDerivedCategory
    let φ := fun {E₀ : CochainComplex (OXMod.{u} X) ℤ} {M₀ : DerivedModules X.sheaf}
        (e₀ : (DerivedCategory.Q.obj E₀ : DerivedCategory.{d} (OXMod.{u} X)) ≅ M₀)
        {Q₀ : CochainComplex (OXMod.{u} (X.restrict W.isOpenEmbedding)) ℤ}
        (ψ₀ : DerivedCategory.Q.obj (modComplex.{u} Q₀) ≅ _) =>
      ψ₀ ≪≫ ((LeftDualPerfect.restrictMod X W).mapDerivedCategoryFactors.app E₀).symm ≪≫
        ρ.mapIso e₀
    let γ := localDerivedPairing X W M H.inv H.isoLeft _ _ hPw hPw' (φ eM ψ) (φ eN ψ')
    obtain ⟨V, hxV, ⟨A⟩⟩ := exists_localSplitting_of_derivedPairing (X.restrict W.isOpenEmbedding)
      _ _ hPw hPw' γ ⟨x, hi, hj⟩
    exact ⟨W.isOpenEmbedding.functor.obj V, ⟨⟨x, hi, hj⟩, hxV, rfl⟩,
      ⟨LocalSplitting.transport W (homologyIsoOfDerivedIso E _ ψ)
        (homologyIsoOfDerivedIso E' _ ψ') A⟩⟩
  choose V hxV A using key
  obtain ⟨D, H', hH', ⟨e⟩⟩ :=
    hasInvertibleModuleDecomposition_of_localSplitting V hxV (fun x => (A x).some)
  exact ⟨D, H', hH', ⟨eM.symm ≪≫ e⟩⟩

/-- **Stacks 0FPG.** Let `(X, 𝒪_X)` be a ringed space and `M` an object of `D(𝒪_X)`. The following
are equivalent:
1. `M` is invertible in `D(𝒪_X)` for the derived tensor product;
2. there is a locally finite direct product decomposition `𝒪_X = ∏ 𝒪_n` and for each `n` an
   invertible `𝒪_n`-module `ℋ^n` with `M = ⨁ ℋ^n[-n]` in `D(𝒪_X)`.

If they hold, `M` is perfect. If every stalk `𝒪_{X,x}` is a local ring, they are also equivalent
to
3. there is an open covering `X = ⋃ U_i` and for each `i` an integer `n_i` such that `M|_{U_i}` is
   represented by an invertible `𝒪_{U_i}`-module placed in degree `n_i`. -/
@[stacks 0FPG]
public theorem isInvertibleObject_tfae [inst : HasDerivedCategory.{d} (Mod X.sheaf)]
    (M : DerivedModules X.sheaf) :
    [IsInvertibleObject M, HasInvertibleModuleDecomposition X M].TFAE ∧
      (IsInvertibleObject M → @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X inst M) ∧
      ((∀ x : X.carrier, IsLocalRing (X.presheaf.stalk x)) →
        [IsInvertibleObject M, HasInvertibleModuleDecomposition X M,
          HasLocalInvertibleDegree M].TFAE) := by
  have h12 : IsInvertibleObject M ↔ HasInvertibleModuleDecomposition X M :=
    ⟨hasInvertibleModuleDecomposition_of_isInvertibleObject X M,
      isInvertibleObject_of_hasInvertibleModuleDecomposition_unconditional M⟩
  refine ⟨?_, fun hM => isPerfect_of_hasInvertibleModuleDecomposition M (h12.mp hM),
    fun hloc => ?_⟩
  · tfae_have 1 ↔ 2 := h12
    tfae_finish
  · tfae_have 1 ↔ 2 := h12
    tfae_have 2 ↔ 3 := hasInvertibleModuleDecomposition_iff_hasLocalInvertibleDegree M hloc
    tfae_finish

end Stacks.Cohomology.InvertibleDerived

end
