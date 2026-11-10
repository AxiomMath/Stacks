module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalObjectCoveringComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# Čech cohomology of quasi-coherent modules on an algebraic space separated over an affine base

Let `X` be an algebraic space over `Spec A` with affine intersections — for instance separated
over `Spec A` — and let `U ⟶ X` be a surjective étale chart with affine scheme, which exists when
`X` is quasi-compact. For a quasi-coherent `𝒪_X`-module `𝓜` the Čech complex
`Γ(U, 𝓜) → Γ(U ×_X U, 𝓜) → Γ(U ×_X U ×_X U, 𝓜) → ⋯`, a complex of `A`-modules, computes
`RΓ(X, 𝓜)` in `D(A)`. The powers `U^{×(m+1)}` are affine charts by the affine intersections, so
`𝓜` has no higher cohomology on them (Stacks 03DW, discharged in this tree), and the Čech complex
of a chart covering the final object then computes cohomology
(`Stacks.CechTop.exists_quasiIso_cechFunctorZ`).

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsOverSpec`: `Γ(X, -)` read as `A`-modules.
* `AlgebraicGeometry.Space.derivedGlobalSectionsOverBase`: `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, its total
  right derived functor.
* `AlgebraicGeometry.Space.cechComplexOverBase`: the `ℤ`-graded Čech complex of an `𝒪_X`-module
  for an étale chart, as `A`-modules. Its terms are the ones of the `ℕ`-graded
  `Stacks.CechTop.cechComplexOverBase`, whose degree-`n` term is `Γ(U^{×(n+1)}, 𝓜)` as an
  `A`-module, lifted to the universe of `RΓ`.

## Main results

* `AlgebraicGeometry.Space.isAffineChart_cechNerve`: the powers of an affine chart are affine.
* `AlgebraicGeometry.Space.exists_quasiIso_cechComplexOverBase`: the Čech complex and the
  global sections of an injective resolution are related by quasi-isomorphisms.
* `AlgebraicGeometry.Space.nonempty_cechComplexOverBase_iso`: the Čech complex is isomorphic to
  `RΓ(X, 𝓜)` in `D(A)`.
* `AlgebraicGeometry.Space.hasAffineIntersections_of_isSeparated` and
  `AlgebraicGeometry.Space.exists_isAffineChart_isSurjective`: the hypotheses, for `X` separated
  and quasi-compact over `Spec A`.

## Implementation notes

`D(A)` is taken at the universe `u + 1` of global sections, as are `cohomologyOverBase` and the
classical right derived functors of `Stacks.Cohomology.SiteModules.globalSectionsFunctor`: a global
section of an `𝒪_X`-module is a compatible family over the étale charts, which form a category in
`Type (u + 1)`. The Čech terms are `u`-small and are lifted by `ModuleCat.uliftFunctor`.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial ComplexShape

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace CategoryTheory.Limits

/-- In a category with binary products every finite nonempty power of an object exists. -/
theorem hasProduct_fin_succ_of_hasBinaryProducts {D : Type*} [Category D] [HasBinaryProducts D]
    (V : D) (n : ℕ) : HasProduct (fun _ : Fin (n + 1) => V) := by
  induction n with
  | zero => exact HasLimit.mk (limitConeOfUnique (fun _ : Fin 1 => V))
  | succ n ih =>
    exact HasLimit.mk ⟨_, extendFanIsLimit (fun _ : Fin (n + 2) => V) (limit.isLimit _)
      (limit.isLimit _)⟩

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

attribute [local instance] CategoryTheory.Limits.hasProduct_fin_succ_of_hasBinaryProducts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Being an affine chart is invariant under isomorphism of charts. -/
theorem isAffineChart_of_iso {P Q : SmallEtale B S hS X} (e : P ≅ Q)
    (hQ : IsAffineChart B S hS X Q) : IsAffineChart B S hS X P := by
  have : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj Q) := hQ
  exact IsAffine.of_isIso ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).map e.hom)

/-- On an algebraic space with affine intersections, the product of two affine charts in the small
étale site is an affine chart. -/
theorem isAffineChart_prodObj (hX : HasAffineIntersections B S hS X) {V W : SmallEtale B S hS X}
    (hV : IsAffineChart B S hS X V) (hW : IsAffineChart B S hS X W) :
    IsAffineChart B S hS X (SmallEtale.prodObj B S hS X V W) :=
  (hX V.obj.left W.obj.left _ V.obj.hom W.obj.hom _ _ hV hW
    (V.property.rep.isPullback' W.obj.hom)).1

/-- On an algebraic space with affine intersections, every power `V^{m+1}` of an affine chart in
the small étale site is an affine chart. -/
theorem isAffineChart_cechNerve (hX : HasAffineIntersections B S hS X) {V : SmallEtale B S hS X}
    (hV : IsAffineChart B S hS X V) (m : ℕ) :
    IsAffineChart B S hS X ((Stacks.CechTop.cechNerve V).obj (op ⦋m⦌)) := by
  induction m with
  | zero =>
    exact isAffineChart_of_iso B S hS X (IsLimit.conePointUniqueUpToIso
      (limit.isLimit (Discrete.functor fun _ : Fin 1 => V))
      (limitConeOfUnique (fun _ : Fin 1 => V)).isLimit) hV
  | succ m ih =>
    refine isAffineChart_of_iso B S hS X (IsLimit.conePointUniqueUpToIso
      (limit.isLimit (Discrete.functor fun _ : Fin (m + 2) => V))
      (extendFanIsLimit (fun _ : Fin (m + 2) => V)
        (limit.isLimit (Discrete.functor fun _ : Fin (m + 1) => V))
        (limit.isLimit (pair V (∏ᶜ fun _ : Fin (m + 1) => V))))) ?_
    change IsAffineChart B S hS X (V ⨯ ∏ᶜ fun _ : Fin (m + 1) => V)
    refine isAffineChart_of_iso B S hS X (IsLimit.conePointUniqueUpToIso
      (limit.isLimit (pair V (∏ᶜ fun _ : Fin (m + 1) => V)))
      (SmallEtale.prodIsLimit B S hS X V _)) ?_
    exact isAffineChart_prodObj B S hS X hX hV ih

/-! ### The Čech complex of a quasi-coherent module -/

section Cech

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
  (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- The category of `𝒪_X`-modules on an algebraic space over an affine scheme has enough
injectives. -/
local instance : EnoughInjectives (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
  enoughInjectives_modules B (Spec (.of A)) hA X hX

/-- Sheafification of abelian sheaves on the small étale site of an algebraic space over an affine
scheme. -/
local instance hasSheafify_smallEtaleRingedSite_spec :
    HasSheafify (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (SmallEtale.topology B (Spec (.of A)) hA X) AddCommGrpCat.{u})

/-- On the small étale site of an algebraic space over an affine scheme, a morphism of abelian
presheaves becomes an isomorphism after sheafification exactly when it is locally bijective. -/
local instance :
    (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B (Spec (.of A)) hA X).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- The Čech complex over `A` of an `𝒪_X`-module for an étale chart `U` of `X`, graded by `ℤ`:
`Γ(U, 𝓜) → Γ(U ×_X U, 𝓜) → ⋯`, as `A`-modules. -/
abbrev cechComplexOverBase (U : SmallEtale B (Spec (.of A)) hA X) :
    Modules.{u, u} B (Spec (.of A)) hA X hX ⥤ CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  Stacks.CechTop.cechFunctorZ (C := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (show (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C from U)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
    (baseRingHom A B hA X hX)

/-- Global sections of an `𝒪_X`-module, as `A`-modules along the structure morphism. -/
abbrev globalSectionsOverSpec :
    Modules.{u, u} B (Spec (.of A)) hA X hX ⥤ ModuleCat.{u + 1} A :=
  Stacks.CechTop.globalSectionsOverBase
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
    (baseRingHom A B hA X hX)

/-- A surjective étale chart covers the final object of the small étale site. -/
theorem coversTop_of_isSurjective (U : SmallEtale B (Spec (.of A)) hA X)
    (hU : IsSurjective B (Spec (.of A)) hA U.obj.hom) :
    (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J.CoversTop fun _ : Unit =>
      (show (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C from U) := fun W =>
  (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J.superset_covering
    (by
      rintro Y g ⟨i, ⟨b⟩⟩
      exact ⟨(), ⟨b⟩⟩)
    (SmallEtale.coversTop_of_isSurjective B (Spec (.of A)) hA X hX U hU W)

/-- **The Čech complex of a quasi-coherent module computes its cohomology.** Let `X` be an
algebraic space over `Spec A` with affine intersections (for instance separated over `Spec A`),
let `U` be a surjective étale chart of `X` with affine scheme, let `𝓜` be a quasi-coherent
`𝒪_X`-module and `𝓜 → I^•` an injective resolution. Then the Čech complex
`Γ(U, 𝓜) → Γ(U ×_X U, 𝓜) → ⋯` and the global sections `Γ(X, I^•)`, as complexes of `A`-modules,
both map quasi-isomorphically to a common complex. -/
theorem exists_quasiIso_cechComplexOverBase (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U)
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (hM : M.IsQuasicoherentOnSite)
    (R : InjectiveResolution M) :
    ∃ (T : CochainComplex (ModuleCat.{u + 1} A) ℤ)
      (φ : ((globalSectionsOverSpec A B hA X hX).mapHomologicalComplex (up ℤ)).obj
        R.cochainComplex ⟶ T)
      (ψ : (cechComplexOverBase A B hA X hX U).obj M ⟶ T), QuasiIso φ ∧ QuasiIso ψ :=
  Stacks.CechTop.exists_quasiIso_cechFunctorZ _ _ R
    (coversTop_of_isSurjective A B hA X hX U hUs)
    fun m q hq =>
      CategoryTheory.InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex _ R
        (fun n hn => isZero_rightDerived_evaluation_of_isAffineChart B (Spec (.of A)) hA X hX M hM _
          (isAffineChart_cechNerve B (Spec (.of A)) hA X hsep hUa m) n hn) q hq

/-- **`RΓ(X, -)` over the base ring**: the unbounded total right derived functor of the global
sections of `𝒪_X`-modules, read as `A`-modules along the structure morphism, on the derived
category of `𝒪_X`-modules at the universe of the schemes. -/
abbrev derivedGlobalSectionsOverBase [HasDerivedCategory (ModuleCat.{u + 1} A)] :
    letI := modulesHasDerivedCategorySmallEtale B (Spec (.of A)) hA X hX
    DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  letI := modulesHasDerivedCategorySmallEtale B (Spec (.of A)) hA X hX
  letI := isGrothendieckAbelian_modules B (Spec (.of A)) hA X hX
  Stacks.DerivedFunctor.totalRightDerived (globalSectionsOverSpec A B hA X hX)

/-- **`RΓ(X, 𝓜)` is computed by the Čech complex of a surjective affine étale chart**, for a
quasi-coherent `𝒪_X`-module `𝓜` on an algebraic space `X` over `Spec A` with affine
intersections (for instance separated over `Spec A`). -/
theorem nonempty_cechComplexOverBase_iso [HasDerivedCategory (ModuleCat.{u + 1} A)]
    (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U)
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (hM : M.IsQuasicoherentOnSite) :
    letI := modulesHasDerivedCategorySmallEtale B (Spec (.of A)) hA X hX
    Nonempty (DerivedCategory.Q.obj ((cechComplexOverBase A B hA X hX U).obj M) ≅
      (derivedGlobalSectionsOverBase A B hA X hX).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  let := modulesHasDerivedCategorySmallEtale B (Spec (.of A)) hA X hX
  let := isGrothendieckAbelian_modules B (Spec (.of A)) hA X hX
  let R := InjectiveResolution.of M
  obtain ⟨T, φ, ψ, hφ, hψ⟩ :=
    exists_quasiIso_cechComplexOverBase A B hA X hX hsep U hUs hUa M hM R
  let G := globalSectionsOverSpec A B hA X hX
  let RG := derivedGlobalSectionsOverBase A B hA X hX
  have hunit := Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective G
    R.cochainComplex
  have := hφ
  have := hψ
  let e₃ : RG.obj (DerivedCategory.Q.obj R.cochainComplex) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (up ℤ)).obj R.cochainComplex) :=
    RG.mapIso ((DerivedCategory.quotientCompQhIso _).app R.cochainComplex).symm ≪≫
      (@asIso _ _ _ _ _ hunit).symm ≪≫
      DerivedCategory.Qh.mapIso ((G.mapHomotopyCategoryFactors (up ℤ)).app R.cochainComplex) ≪≫
        (DerivedCategory.quotientCompQhIso _).app _
  let e₄ : (DerivedCategory.singleFunctor _ 0).obj M ≅ DerivedCategory.Q.obj R.cochainComplex :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app M ≪≫ asIso (DerivedCategory.Q.map R.ι')
  exact ⟨asIso (DerivedCategory.Q.map ψ) ≪≫ (asIso (DerivedCategory.Q.map φ)).symm ≪≫ e₃.symm ≪≫
    RG.mapIso e₄.symm⟩

include hX in
/-- An algebraic space separated over `Spec A` has affine intersections. -/
theorem hasAffineIntersections_of_isSeparated
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hf : IsSeparated B (Spec (.of A)) hA f) :
    HasAffineIntersections B (Spec (.of A)) hA X :=
  (isAbsolutelySeparated_iff_hasAffineIntersections B (Spec (.of A)) hA
    (BigFppfSite.contains_terminal B) X hX).mp
      (isAbsolutelySeparated_of_isSeparated_to_affine B (Spec (.of A)) hA
        (BigFppfSite.contains_terminal B) (Over.mk (𝟙 (B.obj hA)))
        (inferInstanceAs (IsAffine (Spec (.of A)))) f hf)

include hX in
/-- A quasi-compact algebraic space over `Spec A` has a surjective étale chart with affine
scheme. -/
theorem exists_isAffineChart_isSurjective
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hf : IsQuasiCompact B (Spec (.of A)) hA f) :
    ∃ U : SmallEtale B (Spec (.of A)) hA X,
      IsSurjective B (Spec (.of A)) hA U.obj.hom ∧ IsAffineChart B (Spec (.of A)) hA X U := by
  obtain ⟨W, c, hW, hcs, hce⟩ :=
    exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact B (Spec (.of A)) hA hX f hf
  exact ⟨⟨CostructuredArrow.mk c, presheaf_etale_of_isEtale B (Spec (.of A)) hA hce⟩,
    isSurjective_of_presheafSurjective B (Spec (.of A)) hA c hcs, hW⟩

end Cech

end AlgebraicGeometry.Space

end
