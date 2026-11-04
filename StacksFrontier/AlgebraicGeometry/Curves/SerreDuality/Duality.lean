module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.AlgebraicGeometry.Curves.SerreDuality.DualizingComplexAmplitude
public import StacksFrontier.AlgebraicGeometry.Curves.SerreDuality.Linearity
public import StacksFrontier.AlgebraicGeometry.Curves.SerreDuality.SectionsComparison
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
import StacksCore.Tactic.StacksAttribute

/-!
# Serre duality on a proper curve over a field: the genus is `dim_k H^0(X, ω_X)`

Let `k` be a field and let `f : X ⟶ Spec(k)` be proper with `X` of topological Krull dimension
one. The relative dualizing complex `ω_X^• = f^×(𝒪_{Spec(k)})` of [Stacks, Tag 0AWI] and its
relative dualizing module `ω_X = H^{-1}(ω_X^•)` are the dualizing sheaf of the curve, and the
duality isomorphism of [Stacks, Tag 0AWP] identifies the global sections of `ω_X` with the
`k`-linear dual of `H^1(X, 𝒪_X)`. Since the genus of [Stacks, Tag 0BY7] is `dim_k H^1(X, 𝒪_X)`
and a finite-dimensional space has the same dimension as its dual, this is the second equality of
[Stacks, Tag 0BY8]:

`g = dim_k H^1(X, 𝒪_X) = dim_k H^0(X, ω_X)`.

## The chain

Every step is an isomorphism of `k`-vector spaces, not merely of abelian groups: the assertion is
an equality of dimensions, which an additive bijection does not determine over an infinite field.
The `k`-linear structures are those of
`StacksFrontier/AlgebraicGeometry/Curves/SerreDuality/Linearity.lean`.

1. `H^0(X, ω_X) = Hom_{𝒪_X}(𝒪_X, ω_X)`, by
   `AlgebraicGeometry.CurveDuality.unitHomCohomologyZeroLinearEquiv`.
2. `Hom_{𝒪_X}(𝒪_X, H^{-1}(ω_X^•)) = Hom_{D(𝒪_X)}(𝒪_X[-1], ω_X^•)`: the structure sheaf placed in
   degree `-1` corepresents `H^{-1}` on `ω_X^•` because `ω_X^•` lies in degrees `≥ -1`, which is
   `Stacks.Duality.isGE_neg_one_relativeDualizingComplex_derivedStructureSheaf`. No projectivity
   is involved: `DerivedCategory.bijective_homologyFromSingle_of_isGE` is the full faithfulness of
   `𝒜 ⥤ D(𝒜)`.
3. `Hom_{D_QCoh(𝒪_X)}(𝒪_X[-1], ω_X^•) = Hom_{D_QCoh(𝒪_{Spec(k)})}(Rf_*(𝒪_X[-1]), 𝒪_{Spec(k)})`:
   the duality isomorphism, `k`-linearly, by
   `AlgebraicGeometry.CurveDuality.dualityLinearEquiv`.
4. `Hom_{D(𝒪_{Spec(k)})}(Rf_*(𝒪_X[-1]), 𝒪_{Spec(k)}) = Hom_{𝒪_{Spec(k)}}(R^1f_*𝒪_X, 𝒪_{Spec(k)})`
   by [Stacks, Tag 06XS]: the source lies in degrees `≤ 0` and the target in degrees `≥ 0`, so
   taking `H^0` is bijective on this Hom-group. The bound on the source is
   `Stacks.Duality.isLE_derivedPushforward_singleFunctor_obj`, and it is what makes the step
   legitimate with no injectivity hypothesis on the target.
5. `Hom_{𝒪_{Spec(k)}}(R^1f_*𝒪_X, 𝒪_{Spec(k)}) = Hom_k(Γ(Spec(k), R^1f_*𝒪_X), k)`: on an affine
   base a morphism of quasi-coherent modules is a linear map on global sections
   (`AlgebraicGeometry.CurveDuality.moduleSpecΓHomLinearEquiv`), and the global sections of the
   structure sheaf are `k`.
6. `Γ(Spec(k), R^1f_*𝒪_X) = H^1(X, 𝒪_X)` by [Stacks, Tag 01XK] over the affine base, in the form
   `AlgebraicGeometry.CurveDuality.gammaRightDerivedLinearEquiv`.

## Main results

* `dualizingModuleHomLinearEquiv` — for `ℱ` quasi-coherent,
  `Hom_{𝒪_X}(ℱ, ω_X) ≃ₗ[k] Hom_k(H^1(X, ℱ), k)`. This is the isomorphism of clause (5) of
  [Stacks, Tag 0BS2], at the relative dualizing module that [Stacks, Tag 0AWI] constructs.
* `serreDualityLinearEquiv` — `H^0(X, ω_X) ≃ₗ[k] Hom_k(H^1(X, 𝒪_X), k)`, the case `ℱ = 𝒪_X`.
* `finrank_structureSheafCohomology_eq_finrank_cohomologyOverField_relativeDualizingModule`
  — the second equality of [Stacks, Tag 0BY8]: `dim_k H^1(X, 𝒪_X) = dim_k H^0(X, ω_X)`.
* `genus_eq_finrank_structureSheafCohomology_and_eq_finrank_relativeDualizingModule`
  — **equation 53.8.1.1 of [Stacks, Tag 0BY8]**, both equalities:
  `g = dim_k H^1(X, 𝒪_X) = dim_k H^0(X, ω_X)`.

## Implementation notes

The dualizing module is `Stacks.Duality.relativeDualizingModule`, which is the `ω_X` of
[Stacks, Tag 0BS2]: the proof of that lemma pins its dualizing complex down as
`ω_X^• = a(𝒪_{Spec(k)})`, the value of the right adjoint of [Stacks, Tag 0A9E] on the structure
sheaf of the base, and sets `ω_X = H^{-1}(ω_X^•)`. It is the cohomology sheaf of
`ω_X^•` in degree minus the dimension of `X`; the hypothesis `topologicalKrullDim X = 1` is what
makes that degree `-1`, so that clause (1) of [Stacks, Tag 0BS2] places it at the bottom of the
complex and step 2 of the chain applies.

The two geometric inputs that the construction of `ω_X^•` needs are theorems, not hypotheses:
quasi-coherence of the cohomology sheaves of `Rf_*` is [Stacks, Tag 08D5] part (1), proved as
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`, and the existence of the
right adjoint `f^×` is [Stacks, Tag 0A9E], proved as
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs` with
its instance form. Both are available at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is why
`Stacks.Duality.isLE_derivedPushforward_singleFunctor_obj` is stated there at a free
`[HasDerivedCategory.{w}]` binder.

`CompactSpace X` and `QuasiSeparatedSpace X` follow from properness but cannot be found by
instance search, which does not see `f`; they are installed by `letI` inside the statement rather
than taken as hypotheses, so that the registered equality assumes only properness and the
dimension.

Finite-dimensionality of `H^1(X, 𝒪_X)`, needed to pass from the dual to the space itself, is
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper` applied to the structure
sheaf, which is coherent because properness makes `X` locally Noetherian.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0BY8](https://stacks.math.columbia.edu/tag/0BY8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.CurveDuality

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (specBase)
open Stacks.Duality

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [CompactSpace X] [QuasiSeparatedSpace X]
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

include f hpush in
/-- **Duality for a quasi-coherent module on a proper curve over a field**, which is the
isomorphism of clause (5) of [Stacks, Tag 0BS2] at the relative dualizing module constructed by
[Stacks, Tag 0AWI]. For `f : X ⟶ Spec(k)` proper with `X` of topological Krull dimension one and
`ℱ` quasi-coherent, the maps `ℱ ⟶ ω_X` are the `k`-linear functionals on `H^1(X, ℱ)`. The chain
of `k`-linear isomorphisms is described in the module documentation. -/
def dualizingModuleHomLinearEquiv (F : X.Modules) [F.IsQuasicoherent]
    (hdim : topologicalKrullDim X = 1) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    (F ⟶ relativeDualizingModule f hpush
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) ≃ₗ[k]
      Module.Dual k (cohomologyOverField k f F 1) := by
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  let : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
  let OS : (Spec (CommRingCat.of k)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf
  let ωY : quasiCoherentDerivedCategory (Spec (CommRingCat.of k)) :=
    DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))
  let ωc : quasiCoherentDerivedCategory X := relativeDualizingComplex f hpush ωY
  let K : quasiCoherentDerivedCategory X := singleQuasiCoherent F inferInstance (-1)
  let N : (Spec (CommRingCat.of k)).Modules :=
    ((Scheme.Modules.pushforward f).rightDerived 1).obj F
  have hge : ωc.obj.IsGE (-1) :=
    isGE_neg_one_relativeDualizingComplex_derivedStructureSheaf f hpush (le_of_eq hdim)
  have hgeY : ωY.obj.IsGE 0 := isGE_zero_derivedStructureSheaf (Spec (CommRingCat.of k))
  have hleK : ((quasiCoherentDerivedPushforward f hpush).obj K).obj.IsLE 0 := by
    have h1 : ((quasiCoherentDerivedPushforward f hpush).obj K).obj.IsLE (-1 + 1) :=
      isLE_derivedPushforward_singleFunctor_obj k f F (le_of_eq hdim) (-1)
    exact DerivedCategory.TStructure.t.isLE_of_le _ (-1 + 1) 0 (by omega)
  have := DerivedCategory.homologyFunctor_linear (C := (Spec (CommRingCat.of k)).Modules) k 0
  have hdeg : (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) = -1 := by rw [hdim]; rfl
  have hωX : relativeDualizingModule f hpush ωY =
      (DerivedCategory.homologyFunctor X.Modules (-1)).obj ωc.obj :=
    congrArg (fun c => (DerivedCategory.homologyFunctor X.Modules c).obj ωc.obj) hdeg
  rw [hωX]
  -- the module in degree `-1` corepresents `H^{-1}` on `ω•`
  let e1 : ((DerivedCategory.singleFunctor X.Modules (-1)).obj F ⟶ ωc.obj) ≃ₗ[k]
      (F ⟶ (DerivedCategory.homologyFunctor X.Modules (-1)).obj ωc.obj) :=
    LinearEquiv.ofBijective
      (DerivedCategory.homologyFromSingleLinearMap F ωc.obj (-1) k)
      (DerivedCategory.bijective_homologyFromSingle_of_isGE _ _ (-1))
  -- read in `D_QCoh(𝒪_X)`
  let e2 : (K ⟶ ωc) ≃ₗ[k] ((DerivedCategory.singleFunctor X.Modules (-1)).obj F ⟶ ωc.obj) :=
    InducedCategory.homLinearEquiv
  -- the duality isomorphism
  let e3 := dualityLinearEquiv k f hpush ωY K
  -- read in `D(𝒪_{Spec k})`
  let e4 : ((quasiCoherentDerivedPushforward f hpush).obj K ⟶ ωY) ≃ₗ[k]
      (((quasiCoherentDerivedPushforward f hpush).obj K).obj ⟶ ωY.obj) :=
    InducedCategory.homLinearEquiv
  -- degree-zero cohomology is a bijection on these Hom-groups
  let e5 : (((quasiCoherentDerivedPushforward f hpush).obj K).obj ⟶ ωY.obj) ≃ₗ[k]
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules 0).obj
          ((quasiCoherentDerivedPushforward f hpush).obj K).obj ⟶
        (DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules 0).obj ωY.obj) :=
    LinearEquiv.ofBijective
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules 0).mapLinearMap k)
      (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE _ _ 0)
  -- the two cohomology sheaves are `R¹f_*ℱ` and `𝒪_{Spec k}`
  let e6 : ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules 0).obj
          ((quasiCoherentDerivedPushforward f hpush).obj K).obj ⟶
        (DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules 0).obj ωY.obj) ≃ₗ[k]
      (N ⟶ OS) :=
    Linear.homCongr k
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso
        (Scheme.Modules.pushforward f) (derivedPushforward f) (derivedPushforwardUnit f)
        (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X) F (-1) 0 1 (by omega))
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Spec (CommRingCat.of k)).Modules 0).app OS)
  -- morphisms of quasi-coherent modules on `Spec k` are linear maps on global sections
  let e7 := moduleSpecΓHomLinearEquiv k N OS
  -- the global sections of the structure sheaf of `Spec k` are the ground field
  have hinv : ∀ a : k, (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) = a := fun a =>
    congrArg (fun t : CommRingCat.Hom _ _ => t.hom a)
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id
  let gu : moduleSpecΓFunctor.obj OS ≃ₗ[k] k :=
    { toFun := fun x => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by
        let b : ↥Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a
        let y : ↥Γ(Spec (CommRingCat.of k), ⊤) := x
        change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (b • y) =
          (RingHom.id k) a • (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y
        rw [smul_eq_mul, map_mul, RingHom.id_apply, smul_eq_mul]
        exact congrArg (fun t : k => t * (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y) (hinv a)
      invFun := fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a
      left_inv := fun x => congrArg (fun t : CommRingCat.Hom _ _ => t.hom x)
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
      right_inv := fun a => hinv a }
  let e8 : (moduleSpecΓFunctor.obj N ⟶ moduleSpecΓFunctor.obj OS) ≃ₗ[k]
      (moduleSpecΓFunctor.obj N ⟶ ModuleCat.of k k) :=
    Linear.homCongr k (Iso.refl _) gu.toModuleIso
  let e9 : (moduleSpecΓFunctor.obj N ⟶ ModuleCat.of k k) ≃ₗ[k]
      Module.Dual k (moduleSpecΓFunctor.obj N) := ModuleCat.homLinearEquiv
  exact e1.symm.trans (e2.symm.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans
    (e8.trans (e9.trans
      (gammaRightDerivedCohomologyOverFieldIso k f F 1).toLinearEquiv.symm.dualMap))))))))

include f hpush in
/-- **Serre duality on a proper curve over a field.** For `f : X ⟶ Spec(k)` proper with `X` of
topological Krull dimension one, the global sections of the relative dualizing module
`ω_X = H^{-1}(f^×𝒪_{Spec(k)})` are the `k`-linear dual of the first cohomology of the structure
sheaf. This is `AlgebraicGeometry.CurveDuality.dualizingModuleHomLinearEquiv` at the structure
sheaf, with the two sides read as `H^0(X, ω_X)` and as the dual of the cohomology module that
defines the genus. -/
def serreDualityLinearEquiv (hdim : topologicalKrullDim X = 1) :
    cohomologyOverField k f
        (relativeDualizingModule f hpush
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) 0 ≃ₗ[k]
      Module.Dual k (structureSheafCohomology f 1) := by
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  exact ((unitHomCohomologyZeroLinearEquiv k f _).symm.trans
      (dualizingModuleHomLinearEquiv k f hpush (SheafOfModules.unit X.ringCatSheaf) hdim)).trans
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.dualMap

/-- **The second equality of [Stacks, Tag 0BY8].** Let `k` be a field and let `f : X ⟶ Spec(k)`
be proper with `X` of topological Krull dimension one. Then the dimension over `k` of the first
cohomology of the structure sheaf is the dimension over `k` of the global sections of the
relative dualizing module `ω_X = H^{-1}(f^×𝒪_{Spec(k)})` of [Stacks, Tag 0AWI].

`AlgebraicGeometry.CurveDuality.serreDualityLinearEquiv` identifies `H^0(X, ω_X)` with the
`k`-linear dual of `H^1(X, 𝒪_X)`, and a finite-dimensional space has the dimension of its
dual. -/
theorem finrank_structureSheafCohomology_eq_finrank_cohomologyOverField_relativeDualizingModule
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    Module.finrank k (structureSheafCohomology f 1) =
      Module.finrank k (cohomologyOverField k f
        (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) 0) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have : FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f _ 1
  have : FiniteDimensional k (structureSheafCohomology f 1) :=
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.symm.finiteDimensional
  rw [(serreDualityLinearEquiv k f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f) hdim).finrank_eq,
    Subspace.dual_finrank_eq]

/-- **Equation 53.8.1.1 of [Stacks, Tag 0BY8].** Let `k` be a field and let `f : X ⟶ Spec(k)` be
proper with `X` of topological Krull dimension one. Then

`g = dim_k H^1(X, 𝒪_X) = dim_k H^0(X, ω_X)`,

where `g` is the genus of [Stacks, Tag 0BY7] and `ω_X = H^{-1}(f^×𝒪_{Spec(k)})` is the relative
dualizing module of [Stacks, Tag 0AWI] — the object that [Stacks, Tag 0BS2] produces as
`H^{-1}` of the relative dualizing complex `a(𝒪_{Spec(k)})`.

The first equality is the definition of the genus,
`AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology`; the second is
`finrank_structureSheafCohomology_eq_finrank_cohomologyOverField_relativeDualizingModule`.

Definition 53.8.1 of the source also assumes `H^0(X, 𝒪_X) = k`, which fixes the ground field and
makes `X` Cohen--Macaulay and equidimensional; neither equality needs it, so it is not assumed
here and the statement holds in the generality of the definition and beyond. -/
@[stacks 0BY8 "equation 53.8.1.1: the genus is the dimension over the ground field of the first \
cohomology of the structure sheaf, and the dimension over the ground field of the global \
sections of the relative dualizing module"]
theorem genus_eq_finrank_structureSheafCohomology_and_eq_finrank_relativeDualizingModule
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    genus f = Module.finrank k (structureSheafCohomology f 1) ∧
      Module.finrank k (structureSheafCohomology f 1) =
        Module.finrank k (cohomologyOverField k f
          (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) 0) :=
  ⟨genus_eq_finrank_structureSheafCohomology f,
    finrank_structureSheafCohomology_eq_finrank_cohomologyOverField_relativeDualizingModule
      k f hdim⟩

end AlgebraicGeometry.CurveDuality

end
