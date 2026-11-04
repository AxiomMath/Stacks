module
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

public import StacksFrontier.AlgebraicGeometry.Cohomology.SchemeOpenRestriction.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ScalarAction
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Top-degree cohomology surjects onto the cohomology of a quasi-compact open

Let `X` be a quasi-compact quasi-separated scheme over a field `k` whose underlying space has
Krull dimension at most `d ≥ 1`, and let `j : Y ⟶ X` be a quasi-compact open immersion. Clause (2)
of [Stacks, Tag 0A3G] says that the restriction `H^d(X, ℱ) → H^d(U, ℱ)` of abelian sheaf
cohomology is surjective for every quasi-compact open `U ⊆ X`. This file reads that statement
for the cohomology `AlgebraicGeometry.cohomologyOverField` of a module on a scheme over `k`:
there is a surjective `k`-linear map `H^d(X, ℱ) → H^d(Y, j^* ℱ)`, so `H^d(Y, j^* ℱ)` is
finite-dimensional whenever `H^d(X, ℱ)` is.

## Main definitions

* `AlgebraicGeometry.hfunctorNatIsoCohomologyPresheaf`: the comparison
  `AlgebraicGeometry.hgroupIsoSheafCohomology` of derived-functor cohomology of modules with
  `Ext`-theoretic cohomology of the underlying abelian sheaf, as a natural isomorphism.
* `AlgebraicGeometry.cohomologyRestrictOpensNatTrans`: a natural map
  `H^{n+1}(X, ℱ) → H^{n+1}(U, ℱ|_U)` of abelian groups, through `Ext`-theoretic cohomology.
* `AlgebraicGeometry.cohomologyOverFieldRestrictOpens`: the same map, as a `k`-linear map
  between the `cohomologyOverField` spaces.

## Main results

* `AlgebraicGeometry.surjective_cohomologyOverFieldRestrictOpens`: it is surjective in the top
  degree, for a quasi-compact open of a spectral space; this is [Stacks, Tag 0A3G] (2).
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_pullback_of_isOpenImmersion`: the
  finite-dimensionality consequence, for a quasi-compact open immersion `j : Y ⟶ X`.

## Implementation notes

The map is the composite of the comparison of `cohomologyOverField` with the cohomology functor
`Hfunctor` (`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`), the comparison
of `Hfunctor` with `Ext`-theoretic cohomology (`AlgebraicGeometry.hgroupIsoSheafCohomology`, which
needs the degree to be positive), the restriction of the cohomology presheaf from `⊤` to `U`,
and the same comparisons backwards on the open subscheme `U`
(`Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso`). Every factor is natural in
the module, so the composite is a natural transformation; it is `k`-linear because the action of
`a ∈ k` on `cohomologyOverField` is the cohomology of the endomorphism `a • 𝟙`
(`AlgebraicGeometry.cohomologyOverField_smul_eq`), and inverse image along a morphism of
`k`-schemes is `k`-linear (`AlgebraicGeometry.over_pullback_linear`). Whether the composite is
*the* restriction map of the derived-functor theory is never needed, only that it is natural and
surjective.

## References

* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

section Comparison

variable {X : Scheme.{u}} [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **`AlgebraicGeometry.hgroupIsoSheafCohomology` as a natural isomorphism.** In positive
degree the cohomology functor `H^{n+1}(U, -)` on modules over a scheme is, naturally in the
module, the `Ext`-theoretic cohomology over `U` of the underlying abelian sheaf. -/
def hfunctorNatIsoCohomologyPresheaf (U : X.Opens) (n : ℕ) :
    Hfunctor X.ringCatSheaf U (n + 1) ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1) ⋙
          (evaluation _ _).obj (op U) :=
  NatIso.ofComponents (fun F => hgroupIsoSheafCohomology F U n)
    (fun φ => hgroupIsoSheafCohomology_hom_naturality φ U n)

/-- **A natural map from the cohomology of a module on `X` to that of its restriction to an
open `U`, in positive degree.** It is assembled from the comparisons of the cohomology of
modules with `Ext`-theoretic cohomology of the underlying abelian sheaf, on `X` and on the open
subscheme `U`, and the restriction of the `Ext`-theoretic cohomology presheaf from `X` to `U`.
-/
def cohomologyRestrictOpensNatTrans (U : X.Opens) (n : ℕ) :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived (n + 1) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u} ⟶
      Scheme.Modules.pullback U.ι ⋙
        (SheafOfModules.evaluation (U : Scheme).ringCatSheaf (op ⊤)).rightDerived (n + 1) ⋙
          forget₂ (ModuleCat.{u} ((U : Scheme).ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
      (n + 1)).hom ≫
    (hfunctorNatIsoCohomologyPresheaf ⊤ n).hom ≫
    Functor.whiskerLeft
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙
        Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1))
      ((evaluation _ _).map (homOfLE (le_top : U ≤ ⊤)).op) ≫
    (hfunctorNatIsoCohomologyPresheaf U n).inv ≫
    (Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso X U (n + 1)).hom ≫
    (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι)
      (Hfunctor (U : Scheme).ringCatSheaf ⊤ (n + 1))).hom ≫
    Functor.whiskerLeft (Scheme.Modules.pullback U.ι)
      (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        (U : Scheme).ringCatSheaf ⊤ (n + 1)).inv

/-- A composite of surjective morphisms of abelian groups is surjective. -/
private theorem surjective_comp {A B C : AddCommGrpCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (f ≫ g) := by
  intro z
  obtain ⟨y, rfl⟩ := hg z
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, by simp⟩

/-- The forward map of an isomorphism of abelian groups is surjective. -/
private theorem surjective_iso_hom {A B : AddCommGrpCat.{u}} (e : A ≅ B) :
    Function.Surjective e.hom :=
  fun y => ⟨e.inv y, by simp⟩

/-- **[Stacks, Tag 0A3G] (2) for modules on a scheme.** If the underlying space of `X` is
spectral of Krull dimension at most `n + 1` and `U` is a quasi-compact open, the natural map
`cohomologyRestrictOpensNatTrans` from `H^{n+1}(X, ℱ)` to `H^{n+1}(U, ℱ|_U)` is surjective. -/
theorem surjective_cohomologyRestrictOpensNatTrans_app [SpectralSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (n : ℕ)
    (hdim : topologicalKrullDim X ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) (F : X.Modules) :
    Function.Surjective ((cohomologyRestrictOpensNatTrans U n).app F) := by
  have h0A3G :=
    Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le
      F.toAbelianSheaf (n + 1) hdim U hU
  refine surjective_comp _ _ (surjective_iso_hom
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
      (n + 1)).app F)) ?_
  refine surjective_comp _ _ (surjective_iso_hom ((hfunctorNatIsoCohomologyPresheaf ⊤ n).app F)) ?_
  refine surjective_comp _ _ h0A3G ?_
  refine surjective_comp _ _
    (surjective_iso_hom ((hfunctorNatIsoCohomologyPresheaf U n).symm.app F)) ?_
  refine surjective_comp _ _ (surjective_iso_hom
    ((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso X U (n + 1)).app F)) ?_
  refine surjective_comp _ _ (surjective_iso_hom
    ((Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι)
      (Hfunctor (U : Scheme).ringCatSheaf ⊤ (n + 1))).app F)) ?_
  exact surjective_iso_hom
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso (U : Scheme).ringCatSheaf
      ⊤ (n + 1)).symm.app ((Scheme.Modules.pullback U.ι).obj F))

/-- The naturality of `cohomologyRestrictOpensNatTrans` on elements, in the spelling of the
composite functors. -/
private theorem cohomologyRestrictOpensNatTrans_naturality_apply_aux (U : X.Opens) (n : ℕ)
    {F F' : X.Modules} (g : F ⟶ F')
    (x : ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived (n + 1) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).obj F) :
    ((cohomologyRestrictOpensNatTrans U n).app F').hom
        ((((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived (n + 1) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map g).hom x) =
      ((Scheme.Modules.pullback U.ι ⋙
        (SheafOfModules.evaluation (U : Scheme).ringCatSheaf (op ⊤)).rightDerived (n + 1) ⋙
          forget₂ (ModuleCat.{u} ((U : Scheme).ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          g).hom (((cohomologyRestrictOpensNatTrans U n).app F).hom x) :=
  ConcreteCategory.congr_hom ((cohomologyRestrictOpensNatTrans U n).naturality g) x

/-- The naturality of `cohomologyRestrictOpensNatTrans`, read on elements. -/
theorem cohomologyRestrictOpensNatTrans_naturality_apply (U : X.Opens) (n : ℕ) {F F' : X.Modules}
    (g : F ⟶ F')
    (x : ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived (n + 1)).obj F) :
    ((cohomologyRestrictOpensNatTrans U n).app F').hom
        ((((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived (n + 1)).map g).hom x) =
      (((SheafOfModules.evaluation (U : Scheme).ringCatSheaf (op ⊤)).rightDerived (n + 1)).map
        ((Scheme.Modules.pullback U.ι).map g)).hom
          (((cohomologyRestrictOpensNatTrans U n).app F).hom x) :=
  cohomologyRestrictOpensNatTrans_naturality_apply_aux U n g x

end Comparison

section OverField

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **`cohomologyRestrictOpensNatTrans` intertwines the two scalar actions of `k`**, written as
the cohomology of the endomorphisms `a • 𝟙` of `ℱ` and of `ℱ|_U`: inverse image along the open
immersion is `k`-linear for the structures of `X.Modules` and `U.Modules` over `k`. -/
theorem cohomologyRestrictOpensNatTrans_app_smul (U : X.Opens) (F : X.Modules) (n : ℕ) (a : k)
    (x : ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived (n + 1)).obj F) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    letI : Linear k (U : Scheme).Modules := modulesLinear k (Over.mk (U.ι ≫ f))
    ((cohomologyRestrictOpensNatTrans U n).app F).hom
        ((((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived (n + 1)).map
          (a • 𝟙 F)).hom x) =
      (((SheafOfModules.evaluation (U : Scheme).ringCatSheaf (op ⊤)).rightDerived (n + 1)).map
        (a • 𝟙 ((Scheme.Modules.pullback U.ι).obj F))).hom
          (((cohomologyRestrictOpensNatTrans U n).app F).hom x) := by
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  let : Linear k (U : Scheme).Modules := modulesLinear k (Over.mk (U.ι ≫ f))
  let : (Scheme.Modules.pullback U.ι).Linear k :=
    over_pullback_linear k (Over.homMk U.ι : Over.mk (U.ι ≫ f) ⟶ Over.mk f)
  have hmap : (Scheme.Modules.pullback U.ι).map (a • 𝟙 F) =
      a • 𝟙 ((Scheme.Modules.pullback U.ι).obj F) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [cohomologyRestrictOpensNatTrans_naturality_apply U n (a • 𝟙 F) x, hmap]

/-- **The map `H^{n+1}(X, ℱ) → H^{n+1}(U, ℱ|_U)` of `k`-vector spaces.** This is
`AlgebraicGeometry.cohomologyRestrictOpensNatTrans`, which is `k`-linear: the action of a scalar
on either side is the cohomology of multiplication by the scalar, inverse image along the open
immersion is `k`-linear, and the map is natural in the module. -/
def cohomologyOverFieldRestrictOpens (U : X.Opens) (F : X.Modules) (n : ℕ) :
    cohomologyOverField k f F (n + 1) →ₗ[k]
      cohomologyOverField k (U.ι ≫ f) ((Scheme.Modules.pullback U.ι).obj F) (n + 1) where
  toFun x := (cohomologyRestrictOpensNatTrans U n).app F x
  map_add' x y := map_add ((cohomologyRestrictOpensNatTrans U n).app F).hom x y
  map_smul' a x :=
    (congrArg (fun y => (cohomologyRestrictOpensNatTrans U n).app F y)
      (cohomologyOverField_smul_eq k f F (n + 1) a x)).trans
      ((cohomologyRestrictOpensNatTrans_app_smul k f U F n a x).trans
        (cohomologyOverField_smul_eq k (U.ι ≫ f) ((Scheme.Modules.pullback U.ι).obj F)
          (n + 1) a ((cohomologyRestrictOpensNatTrans U n).app F x)).symm)

/-- **[Stacks, Tag 0A3G] (2) for `cohomologyOverField`.** On a scheme whose underlying space is
spectral of Krull dimension at most `n + 1`, the map
`AlgebraicGeometry.cohomologyOverFieldRestrictOpens` to a quasi-compact open is surjective. -/
theorem surjective_cohomologyOverFieldRestrictOpens [SpectralSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (F : X.Modules) (n : ℕ)
    (hdim : topologicalKrullDim X ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    Function.Surjective (cohomologyOverFieldRestrictOpens k f U F n) :=
  surjective_cohomologyRestrictOpensNatTrans_app U hU n hdim F

end OverField

/-- **Top-degree cohomology of a quasi-compact open is finite-dimensional when that of the whole
space is.** Let `X` be a quasi-compact quasi-separated scheme over a field `k` whose underlying
space has Krull dimension at most `n + 1`, let `j : Y ⟶ X` be a quasi-compact open immersion and
`ℱ` a module on `X`. If `H^{n+1}(X, ℱ)` is finite-dimensional, so is `H^{n+1}(Y, j^* ℱ)`: it is a
quotient of `H^{n+1}(X, ℱ)` by [Stacks, Tag 0A3G] (2). -/
theorem finiteDimensional_cohomologyOverField_pullback_of_isOpenImmersion (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (F : X.Modules) (n : ℕ)
    (hdim : topologicalKrullDim X ≤ ((n + 1 : ℕ) : WithBot ℕ∞))
    (hfin : FiniteDimensional k (cohomologyOverField k f F (n + 1))) :
    FiniteDimensional k (cohomologyOverField k (j ≫ f) ((Scheme.Modules.pullback j).obj F)
      (n + 1)) := by
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  have : SpectralSpace X := {}
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
  have hU : IsCompact (j.opensRange : Set X) := by
    simpa using isCompact_range j.base.hom.continuous
  -- the open subscheme `U = j(Y)`, and the module `ℱ|_U` on it
  have hfinU : FiniteDimensional k (cohomologyOverField k (j.opensRange.ι ≫ f)
      ((Scheme.Modules.pullback j.opensRange.ι).obj F) (n + 1)) :=
    Module.Finite.of_surjective _
      (surjective_cohomologyOverFieldRestrictOpens k f j.opensRange hU F n hdim)
  -- transport from `U` to `Y` along `e : Y ≅ U`
  set e := j.isoOpensRange
  have hg : e.inv ≫ j ≫ f = j.opensRange.ι ≫ f := by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  rw [← hg] at hfinU
  have hY : FiniteDimensional k (cohomologyOverField k (j ≫ f)
      ((Scheme.Modules.pushforward e.inv).obj
        ((Scheme.Modules.pullback j.opensRange.ι).obj F)) (n + 1)) :=
    Module.Finite.equiv (cohomologyOverFieldPushforwardIso k e.inv (j ≫ f) _ (n + 1)).toLinearEquiv
  have hM : (Scheme.Modules.pushforward e.inv).obj
        ((Scheme.Modules.pullback j.opensRange.ι).obj F) ≅
      (Scheme.Modules.pullback j).obj F :=
    (Scheme.Modules.pullbackIsoPushforward e.symm).symm.app _ ≪≫
      (Scheme.Modules.pullbackComp e.hom j.opensRange.ι).app F ≪≫
      eqToIso (by rw [Scheme.Hom.isoOpensRange_hom_ι])
  exact Module.Finite.equiv (cohomologyOverFieldIso k (j ≫ f) hM (n + 1)).toLinearEquiv

end AlgebraicGeometry

end
