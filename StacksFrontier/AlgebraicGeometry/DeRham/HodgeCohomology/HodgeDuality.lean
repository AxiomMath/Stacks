module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.PerfectSheafPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WedgeHomCurrying
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.FormsWedgeDuality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductUnitLaw
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualContractionCupProduct
public import StacksFrontier.LinearAlgebra.PerfectPairing.TraceRescaling
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothEquidimensionalOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SmoothDualizingModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.RowHomologyOfACartanEilenbergResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Duality for Hodge cohomology

Let `X` be a proper scheme over a field `k`, smooth of relative dimension `d`, with dualizing
module `ω_X` and trace `Hᵈ(X, ω_X) ⟶ k` ([Stacks, Tag 0FVV], [Stacks, Tag 0FVW]). This file
proves the duality of Hodge cohomology of [Stacks, Tag 0FW4] for the linear form
`t : Hᵈ(X, Ω^d_{X/k}) ⟶ k` obtained from the trace through any isomorphism `ω_X ≅ Ω^d_{X/k}`:
for all `p, q` the pairing

`H^q(X, Ω^p_{X/k}) × H^{d-q}(X, Ω^{d-p}_{X/k}) ⟶ k, (ξ, ξ') ↦ t(ξ ∪ ξ')`

is perfect. Here `∪` is the cup product of Hodge cohomology of Section 0FM4: the
`H⁰(X, 𝒪_X)`-bilinear cup product of Cohomology, Section 0FKU on the ringed space `(X, 𝒪_X)`
along the wedge product `Ω^a ⊗ Ω^b ⟶ Ω^{a+b}`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formsMul`: the wedge product `Ω^a ⊗ Ω^b ⟶ Ω^n`, `a + b = n`.
* `AlgebraicGeometry.Scheme.Hom.hodgeCupModule`: the cup product of Hodge cohomology, on the
  `Γ(X, 𝒪_X)`-modules `H^i(X, Ω^a)`.
* `AlgebraicGeometry.Scheme.Hom.hodgeCup`: the same as a `k`-bilinear map.
* `AlgebraicGeometry.Scheme.Hom.hodgePairing`: the pairings `(ξ, ξ') ↦ t(ξ ∪ ξ')` of Tag 0FW4.
* `AlgebraicGeometry.Scheme.Hom.hodgeTraceOfIso`: the trace read on `Hᵈ(X, Ω^d)` through an
  isomorphism `ω_X ≅ Ω^d`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfPair_hodgePairing_hodgeTraceOfIso`: the pairings are
  perfect for every `p` and `q`.
* `AlgebraicGeometry.Scheme.Hom.hodgeDuality`: [Stacks, Tag 0FW4].

## The proof

For `0 ≤ p ≤ d` the sheaf `Ω^{d-p}` is finite locally free (Tag 02G1) and the wedge product
`Ω^p ⊗ Ω^{d-p} ⟶ Ω^d` is perfect at the level of sheaves
(`Stacks.SheafOfModules.WedgeDuality.bijective_map_app_comp_mulSheaf` with
`AlgebraicGeometry.Scheme.Hom.isIso_formsWedgeHom`), so
`Ω^p ≅ Ω^d ⊗ (Ω^{d-p})^∨ ≅ ω_X ⊗ (Ω^{d-p})^∨` and the pairing is the one of [Stacks, Tag 0FW0]
(`Stacks.Duality.isPerfPair_tracePairing`). For `p < 0` or `p > d` both sheaves of forms vanish.

## Implementation notes

The cup product is built from the global cup product
`Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace` of the canonical one-point
comparison, the one for which the unit law of the cup product is available; the duality of
`Stacks.Duality.isPerfPair_tracePairing` holds for it since its tensor comparison is invertible.

standard model: uses `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing`, which exists only
there.

## References

* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
* [Stacks Project, Section 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FW0](https://stacks.math.columbia.edu/tag/0FW0)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Duality (sheafCohomology singleModule tensorModule dualizingModule topTrace
  cupContraction contractionMapOf tracePairing)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 100000] HasDerivedCategory.standard

section Cup

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The wedge product `Ω^a_{X/S} ⊗ Ω^b_{X/S} ⟶ Ω^n_{X/S}`** for `a + b = n`: multiplication in
the algebra of differential forms, read in degree `n`. -/
def formsMul (a b n : ℤ) (h : a + b = n) :
    tensorModule (relativeDifferentialForms f a) (relativeDifferentialForms f b) ⟶
      relativeDifferentialForms f n :=
  (relativeDifferentialFormsAlgebra f).mulSheaf a b ≫
    eqToHom (congrArg (relativeDifferentialForms f) h)

/-- **The cup product of Hodge cohomology** of Section 0FM4,
`H^i(X, Ω^a) ⊗ H^j(X, Ω^b) ⟶ H^m(X, Ω^n)` for `a + b = n` and `i + j = m`, on the
`Γ(X, 𝒪_X)`-modules of cohomology: the cup product of Cohomology, Section 0FKU on `(X, 𝒪_X)`
followed by the wedge product. -/
def hodgeCupModule (a b n : ℤ) (h : a + b = n) (i j m : ℤ) (hm : i + j = m) :
    cohomologyModule (singleModule (relativeDifferentialForms f a)) i ⊗
        cohomologyModule (singleModule (relativeDifferentialForms f b)) j ⟶
      cohomologyModule (singleModule (relativeDifferentialForms f n)) m :=
  cupContraction (cupProductOnSpace X.toRingedSpace) (formsMul f a b n h) i j m hm

end Cup

/-- `cupContraction` is functorial in the target of the pairing. -/
theorem _root_.Stacks.Duality.cupContraction_comp {X : Scheme.{u}}
    (κ : Stacks.Cohomology.GlobalKunneth.GlobalCupProduct X.toRingedSpace) {F E W W' : X.Modules}
    (μ : tensorModule F E ⟶ W) (g : W ⟶ W') (i j n : ℤ) (h : i + j = n) :
    cupContraction κ (μ ≫ g) i j n h = cupContraction κ μ i j n h ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n).map
        ((baseSections X.toRingedSpace).map
          (DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map g))) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace))
  have hc : contractionMapOf (μ ≫ g) = contractionMapOf μ ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map g) :=
    (congrArg (Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor (R := X.sheaf) F E ≫ ·)
      ((congrArg DerivedCategory.Q.map
        ((CochainComplex.singleFunctor X.Modules 0).map_comp μ g)).trans
        (DerivedCategory.Q.map_comp _ _))).trans (Category.assoc _ _ _).symm
  have hH : (H (i + j)).map ((baseSections X.toRingedSpace).map (contractionMapOf (μ ≫ g))) =
      (H (i + j)).map ((baseSections X.toRingedSpace).map (contractionMapOf μ)) ≫
        (H (i + j)).map ((baseSections X.toRingedSpace).map
          (DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map g))) :=
    (congrArg (fun t => (H (i + j)).map ((baseSections X.toRingedSpace).map t)) hc).trans
      ((congrArg (H (i + j)).map ((baseSections X.toRingedSpace).map_comp _ _)).trans
        ((H (i + j)).map_comp _ _))
  have hE := Stacks.Duality.eqToHom_comp_homologyFunctor_map (X := X)
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map g)) h
  exact (congrArg (cupPairing κ _ _ i j ≫ ·) ((congrArg (· ≫ eqToHom _) hH).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hE)))).trans
      ((Category.assoc _ _ _).trans (congrArg (cupPairing κ _ _ i j ≫ ·)
        (Category.assoc _ _ _))).symm

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The cup product of Hodge cohomology** of Section 0FM4,
`H^i(X, Ω^a_{X/k}) × H^j(X, Ω^b_{X/k}) ⟶ H^m(X, Ω^n_{X/k})` for `a + b = n` and `i + j = m`,
as a `k`-bilinear map. -/
def hodgeCup (a b n : ℤ) (h : a + b = n) (i j m : ℤ) (hm : i + j = m) :
    sheafCohomology f (relativeDifferentialForms f a) i →ₗ[k]
      sheafCohomology f (relativeDifferentialForms f b) j →ₗ[k]
        sheafCohomology f (relativeDifferentialForms f n) m :=
  let B := (TensorProduct.mk ↑(baseRing X.toRingedSpace)
      ↑(cohomologyModule (singleModule (relativeDifferentialForms f a)) i)
      ↑(cohomologyModule (singleModule (relativeDifferentialForms f b)) j)).compr₂
    (hodgeCupModule f a b n h i j m hm).hom
  LinearMap.mk₂ k (fun ξ η => B ξ η) (fun ξ₁ ξ₂ η => B.map_add₂ ξ₁ ξ₂ η)
    (fun c ξ η => B.map_smul₂ (Stacks.Duality.globalRingHom f c) ξ η)
    (fun ξ η₁ η₂ => (B ξ).map_add η₁ η₂)
    (fun c ξ η => (B ξ).map_smul (Stacks.Duality.globalRingHom f c) η)

/-- `hodgeCup` sends `(ξ, η)` to the image of `ξ ⊗ η` under the cup product of modules. -/
theorem hodgeCup_apply (a b n : ℤ) (h : a + b = n) (i j m : ℤ) (hm : i + j = m)
    (ξ : sheafCohomology f (relativeDifferentialForms f a) i)
    (η : sheafCohomology f (relativeDifferentialForms f b) j) :
    hodgeCup f a b n h i j m hm ξ η = (hodgeCupModule f a b n h i j m hm).hom (ξ ⊗ₜ η) :=
  rfl

/-- **The pairings of [Stacks, Tag 0FW4]**: for a linear form `t` on `Hᵈ(X, Ω^d_{X/k})`,
`H^q(X, Ω^p_{X/k}) × H^{d-q}(X, Ω^{d-p}_{X/k}) ⟶ k, (ξ, ξ') ↦ t(ξ ∪ ξ')`. -/
def hodgePairing (d : ℕ)
    (t : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k) (p q : ℤ) :
    sheafCohomology f (relativeDifferentialForms f p) q →ₗ[k]
      sheafCohomology f (relativeDifferentialForms f (d - p)) (d - q) →ₗ[k] k :=
  (hodgeCup f p (d - p) d (by ring) q (d - q) d (by ring)).compr₂ t

variable [IsProper f]

/-- **The trace `Hᵈ(X, Ω^d_{X/k}) ⟶ k` attached to an isomorphism `ω_X ≅ Ω^d_{X/k}`**: the trace
`Hᵈ(X, ω_X) ⟶ k` of [Stacks, Tag 0FVW] (`Stacks.Duality.topTrace`) read through the
isomorphism. -/
def hodgeTraceOfIso (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (e : dualizingModule f ≅ relativeDifferentialForms f d) :
    sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k :=
  (topTrace f hCM hequi d hd).hom ∘ₗ ((ModuleCat.restrictScalars.{u}
    (Stacks.Duality.globalRingHom f)).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) d).map
        ((baseSections X.toRingedSpace).map
          (DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map e.inv))))).hom

/-- The pairing of Tag 0FW4 at the trace attached to `ω_X ≅ Ω^d` is the pairing of Tag 0FW0 for
the wedge product followed by the inverse of the isomorphism. -/
theorem hodgeCup_compr₂_hodgeTraceOfIso (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (e : dualizingModule f ≅ relativeDifferentialForms f d) (a b : ℤ) (hab : a + b = d)
    (i j : ℤ) (hij : i + j = d) :
    (hodgeCup f a b d hab i j d hij).compr₂ (hodgeTraceOfIso f hCM hequi d hd e) =
      tracePairing f hCM hequi d hd (cupProductOnSpace X.toRingedSpace)
        (formsMul f a b d hab ≫ e.inv) i j hij := by
  refine LinearMap.ext fun ξ => LinearMap.ext fun η => ?_
  rw [Stacks.Duality.tracePairing_apply, Stacks.Duality.cupContraction_comp]
  rfl

end Field

/-! ### Perfectness of the pairings -/

section Perfect

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`Ω^n_{X/k}` is finite locally free** for `X` smooth of relative dimension `d` over `k`: it is
the `n`-th exterior power of `Ω_{X/k}`, which is finite locally free of rank `d`
([Stacks, Tag 02G1]). -/
theorem isFiniteLocallyFree_relativeDifferentialForms (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (relativeDifferentialForms f n) := by
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f d
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (hM := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (relativeDifferentials f) d n)
    (relativeDifferentialForms f n) (d.choose n)

/-- **`Ω^n_{X/k} = 0` for `n > d`**, for `X` smooth of relative dimension `d` over `k`: the
exterior powers of a finite locally free module of rank `d` vanish above `d`. -/
@[sga "1 III 5.2" "special case", sga "6 VII 4.1" "special case"]
theorem isZero_relativeDifferentialForms_of_lt (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℤ)
    (hn : (d : ℤ) < n) : IsZero (relativeDifferentialForms f n) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf) (relativeDifferentials f) d :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f d
  refine (IsZero.iff_id_eq_zero _).2 (_root_.SheafOfModules.hom_ext ?_)
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  exact Stacks.SheafOfModules.TopWedge.exteriorPower_eq_zero_of_lt
    (_root_.SheafOfModules.algebras _ (relativeDifferentials f)) d m (by omega) U z

/-- **`Ω^n_{X/k} = 0` for `n < 0`.** -/
theorem isZero_relativeDifferentialForms_of_neg (n : ℤ) (hn : n < 0) :
    IsZero (relativeDifferentialForms f n) :=
  Stacks.DeRhamSmooth.isZero_relativeDifferentialForms_of_neg f n hn

/-- The cohomology of a zero sheaf vanishes. -/
theorem subsingleton_sheafCohomology_of_isZero {F : X.Modules} (hF : IsZero F) (n : ℤ) :
    Subsingleton (sheafCohomology f F n) :=
  have := CochainComplex.CartanEilenbergResolution.additive_rightDerivedPlus
    (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤) n
  have h : IsZero (cohomologyModule (singleModule F) n) := IsZero.of_iso
    (Functor.map_isZero ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace
      ⊤).rightDerivedPlus n) hF) ((Stacks.Duality.homologyBaseSectionsSingleIso (X := X) n).app F)
  have h' : Subsingleton (cohomologyModule (singleModule F) n) := ModuleCat.subsingleton_of_isZero h
  h'

/-- A bilinear form between two zero modules is a perfect pairing. -/
theorem _root_.LinearMap.isPerfPair_of_subsingleton_of_subsingleton {R M N : Type*} [Field R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Subsingleton M] [Subsingleton N]
    (B : M →ₗ[R] N →ₗ[R] R) : B.IsPerfPair :=
  ⟨⟨fun _ _ _ => Subsingleton.elim _ _, fun φ => ⟨0, LinearMap.ext fun n => by
      rw [Subsingleton.elim n 0, map_zero, map_zero]⟩⟩,
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun φ => ⟨0, LinearMap.ext fun m => by
      rw [Subsingleton.elim m 0, map_zero, map_zero]⟩⟩⟩

variable [IsProper f]

/-- **The pairing `H^i(X, Ω^a) × H^j(X, Ω^b) ⟶ k, (ξ, η) ↦ t(ξ ∪ η)` is perfect** for
`a, b ≥ 0`, `a + b = d` and `i + j = d`, `t` the trace attached to an isomorphism
`ω_X ≅ Ω^d_{X/k}`. -/
theorem isPerfPair_hodgeCup_compr₂_hodgeTraceOfIso (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    [SmoothOfRelativeDimension d f] (e : dualizingModule f ≅ relativeDifferentialForms f d)
    (a b : ℕ) (hab : (a : ℤ) + b = d) (i j : ℤ) (hij : i + j = d) :
    ((hodgeCup f a b d hab i j d hij).compr₂ (hodgeTraceOfIso f hCM hequi d hd e)).IsPerfPair := by
  rw [hodgeCup_compr₂_hodgeTraceOfIso]
  have hab' : a + b = d := by omega
  have : SmoothOfRelativeDimension (a + b) f := hab' ▸ ‹SmoothOfRelativeDimension d f›
  have : IsIso (Stacks.SheafOfModules.WedgeDuality.wedgeHom
      (relativeDifferentialFormsAlgebra f) (a : ℤ) (b : ℤ)) := isIso_formsWedgeHom f a b
  refine Stacks.Duality.isPerfPair_tracePairing f (canonicalOnePointComparison X.toRingedSpace)
    hCM hequi d hd (isFiniteLocallyFree_relativeDifferentialForms f d b) _ (fun T => ?_) i j hij
  have h := Stacks.SheafOfModules.WedgeDuality.bijective_map_app_comp_mulSheaf
    (relativeDifferentialFormsAlgebra f) (a : ℤ) (b : ℤ) T
  let w : relativeDifferentialForms f ((a : ℤ) + (b : ℤ)) ≅ dualizingModule f :=
    eqToIso (congrArg (relativeDifferentialForms f) hab) ≪≫ e.symm
  have hfun : (fun g : T ⟶ relativeDifferentialForms f a =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map g).app
        (relativeDifferentialForms f b) ≫ (formsMul f a b d hab ≫ e.inv)) =
      (fun φ => φ ≫ w.hom) ∘ (fun g : T ⟶ relativeDifferentialForms f a =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map g).app
          (relativeDifferentialForms f b) ≫ (relativeDifferentialFormsAlgebra f).mulSheaf a b) := by
    funext g
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm
  exact (congrArg Function.Bijective hfun).mpr <| (show Function.Bijective
      (fun φ : tensorModule T (relativeDifferentialForms f b) ⟶
        relativeDifferentialForms f ((a : ℤ) + (b : ℤ)) => φ ≫ w.hom) from
    ⟨fun φ φ' e' => (Iso.cancel_iso_hom_right φ φ' w).1 e',
      fun φ => ⟨φ ≫ w.inv, (Category.assoc _ _ _).trans
        ((congrArg (φ ≫ ·) w.inv_hom_id).trans (Category.comp_id φ))⟩⟩).comp h

/-- **The pairings of [Stacks, Tag 0FW4] are perfect for every `p` and `q`**, for the trace
attached to an isomorphism `ω_X ≅ Ω^d_{X/k}`. For `0 ≤ p ≤ d` this is
`isPerfPair_hodgeCup_compr₂_hodgeTraceOfIso`; otherwise both `Ω^p` and `Ω^{d-p}` vanish. -/
theorem isPerfPair_hodgePairing_hodgeTraceOfIso (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    [SmoothOfRelativeDimension d f] (e : dualizingModule f ≅ relativeDifferentialForms f d)
    (p q : ℤ) : (hodgePairing f d (hodgeTraceOfIso f hCM hequi d hd e) p q).IsPerfPair := by
  by_cases hp : 0 ≤ p ∧ p ≤ d
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hp.1
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (d : ℤ) - a by omega)
    have key : ∀ (b' : ℤ) (hb' : b' = b),
        ((hodgeCup f a b' d (by omega) q (d - q) d (by ring)).compr₂
          (hodgeTraceOfIso f hCM hequi d hd e)).IsPerfPair := by
      rintro b' rfl
      exact isPerfPair_hodgeCup_compr₂_hodgeTraceOfIso f hCM hequi d hd e a b (by omega) q (d - q)
        (by ring)
    exact key _ hb
  · obtain ⟨h₁, h₂⟩ : IsZero (relativeDifferentialForms f p) ∧
        IsZero (relativeDifferentialForms f ((d : ℤ) - p)) := by
      rcases not_and_or.mp hp with h | h
      · exact ⟨isZero_relativeDifferentialForms_of_neg f p (by omega),
          isZero_relativeDifferentialForms_of_lt f d _ (by omega)⟩
      · exact ⟨isZero_relativeDifferentialForms_of_lt f d p (by omega),
          isZero_relativeDifferentialForms_of_neg f _ (by omega)⟩
    have := subsingleton_sheafCohomology_of_isZero f h₁ q
    have := subsingleton_sheafCohomology_of_isZero f h₂ ((d : ℤ) - q)
    exact LinearMap.isPerfPair_of_subsingleton_of_subsingleton _

end Perfect

/-! ### Two pasting identities -/

section Pasting

variable {C : Type*} [Category* C]

/-- If `XI⁻¹ = F(g⁻¹) ≫ ι` then `ι ≫ XI = F(g)`. -/
theorem comp_hom_eq_map_of_inv_eq {A B Q : C} (F : C ⥤ C) (ι : F.obj A ⟶ Q) (XI : Q ≅ F.obj B)
    (g : A ≅ B) (h : XI.inv = F.map g.inv ≫ ι) :
    ι ≫ XI.hom = F.map g.hom := by
  have hι : ι = F.map g.hom ≫ XI.inv := by
    rw [h, ← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]
  rw [hι, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The degree-zero computation behind `derivedTensorSingleToTensor_sheafTensorUnitLeft`. -/
theorem unitorSummand_paste (T : C ⥤ C ⥤ C) {K₀ O G₀ G P Q R : C} (eO : K₀ ≅ O) (eG : G₀ ≅ G)
    (lam : T.obj O ⟶ 𝟭 C) (ι : P ⟶ Q) (I : Q ⟶ (T.obj K₀).obj G) (M : (T.obj K₀).obj G ⟶ R)
    (L : R ⟶ G₀) (e₁ : R ≅ (T.obj O).obj G) (hP : P = (T.obj K₀).obj G₀)
    (hι : ι ≫ I = eqToHom hP ≫ (T.obj K₀).map eG.hom) (hM : M = (T.map eO.hom).app G ≫ e₁.inv)
    (hL : L = e₁.hom ≫ lam.app G ≫ eG.inv) :
    ι ≫ ((I ≫ M) ≫ L) = eqToHom hP ≫ (T.map eO.hom).app G₀ ≫ lam.app G₀ := by
  subst hP
  rw [← Category.assoc, ← Category.assoc, hι, hM, hL]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [NatTrans.naturality_assoc, lam.naturality_assoc]
  simp

/-- The algebra of the unit law: naturality of the cup product, the unit law of
`totalCupPairing_unitClass`, and a factorisation of the multiplication, pasted together. -/
theorem unitLaw_paste [MonoidalCategory C] {A A' B T T' Y Z Y' : C} (a : 𝟙_ C ⟶ A)
    (U : A ⟶ A') (η : 𝟙_ C ⟶ B) (V : B ⟶ B) (cup : A ⊗ B ⟶ T) (cup' : A' ⊗ B ⟶ T') (W : T ⟶ T')
    (Mu : T' ⟶ Y) (Tt : T ⟶ Z) (Ul : Z ⟶ Y') (Fq : Y' ⟶ Y) (E : B ⟶ Y')
    (hn : (λ_ (𝟙_ C)).inv ≫ ((a ≫ U) ⊗ₘ (η ≫ V)) ≫ cup' = (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ η) ≫ cup ≫ W)
    (hV : η ≫ V = η) (hW : W ≫ Mu = Tt ≫ Ul ≫ Fq)
    (hu : (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ η) ≫ (cup ≫ Tt) ≫ Ul = η ≫ E) :
    (λ_ (𝟙_ C)).inv ≫ ((a ≫ U) ⊗ₘ η) ≫ cup' ≫ Mu = η ≫ E ≫ Fq := by
  rw [hV] at hn
  calc (λ_ (𝟙_ C)).inv ≫ ((a ≫ U) ⊗ₘ η) ≫ cup' ≫ Mu
      = ((λ_ (𝟙_ C)).inv ≫ ((a ≫ U) ⊗ₘ η) ≫ cup') ≫ Mu := by simp only [Category.assoc]
    _ = ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ η) ≫ cup ≫ W) ≫ Mu := by rw [hn]
    _ = ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ η) ≫ (cup ≫ Tt) ≫ Ul) ≫ Fq := by
        simp only [Category.assoc, hW]
    _ = η ≫ E ≫ Fq := by rw [hu, Category.assoc]

end Pasting

/-! ### The two identifications of `Tot(𝒪[0] ⊗ 𝒢[0])` -/

section SingleUnitor

open Stacks.SheafOfModules.DerivedMonoidal (Mod)

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The two identifications of `Tot(𝒪[0] ⊗ 𝒢[0])` with `(𝒪 ⊗ 𝒢)[0]` agree after an action
`𝒪 ⊗ - ⟶ 𝟭`**: collapsing the second factor and then applying `lam` in degree zero is collapsing
the first factor and applying `lam` degreewise. -/
theorem mapBifunctorSingleRightIso_hom_comp_lam (G : Mod R)
    (lam : (Stacks.SheafOfModules.Tensor.sheafTensor R).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ⟶ 𝟭 (Mod R)) :
    (HomologicalComplex.mapBifunctorSingleRightIso (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (Stacks.DerivedTensor.RingedSite.singleComplex
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) G).hom ≫
      ((MonoidalCategory.tensorRight (C := Mod R) G).mapCochainComplexSingleFunctor 0).hom.app
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≫
        (CochainComplex.singleFunctor (Mod R) 0).map (lam.app G) =
    (HomologicalComplex.mapBifunctorSingleLeftIso (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))
        (Stacks.DerivedTensor.RingedSite.singleComplex G)).hom ≫
      (NatTrans.mapHomologicalComplex lam (ComplexShape.up ℤ)).app
          (Stacks.DerivedTensor.RingedSite.singleComplex G) ≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app
          (Stacks.DerivedTensor.RingedSite.singleComplex G) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun a c hac => ?_
  by_cases hc : c = 0
  swap
  · exact (HomologicalComplex.isZero_obj_obj_single_obj_X_right _ _ G a c hc).eq_of_src _ _
  subst hc
  by_cases ha : a = 0
  swap
  · exact (HomologicalComplex.isZero_obj_obj_single_obj_X_left _ _ _ a 0 ha).eq_of_src _ _
  subst ha
  obtain rfl : n = 0 := by simpa using hac.symm
  let O := _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)
  have h1 := comp_hom_eq_map_of_inv_eq _
    (HomologicalComplex.singleRightι (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (Stacks.DerivedTensor.RingedSite.singleComplex O) G 0)
    (HomologicalComplex.mapBifunctorSingleRightXIso (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (Stacks.DerivedTensor.RingedSite.singleComplex O) G 0)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G)
    (HomologicalComplex.mapBifunctorSingleRightXIso_inv _ _ _ 0)
  have hM := HomologicalComplex.singleMapHomologicalComplex_hom_app_self
    (MonoidalCategory.tensorRight (C := Mod R) G) (ComplexShape.up ℤ) 0 O
  have hL := HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 (lam.app G)
  have hR := HomologicalComplex.singleLeftι_singleLeftXIso_hom
    (Stacks.SheafOfModules.Tensor.sheafTensor R) O
    (Stacks.DerivedTensor.RingedSite.singleComplex G) 0
  have key := unitorSummand_paste (Stacks.SheafOfModules.Tensor.sheafTensor R)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 O)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G) lam _ _ _ _
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _) rfl
    (h1.trans (Category.id_comp _).symm) hM hL
  simp only [HomologicalComplex.comp_f]
  refine ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans key).trans ?_
  rw [eqToHom_refl, Category.id_comp]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) hR).symm
  exact (congrArg (_ ≫ ·) (Category.comp_id _)).symm

end SingleUnitor

/-! ### The unit law -/

section UnitLaw

open Stacks.Cohomology.DerivedGlobalCupProduct (unitSingleComplex unitLeftAction sheafTensorUnitLeft
  unitSingleComplexXIso)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The unit `𝒪_X ⟶ Ω^0_{X/S}`** of the algebra of differential forms: `1 ↦ 1`. -/
def formsUnit :
    _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) ⟶
      relativeDifferentialForms f 0 :=
  (relativeDifferentialForms f 0).unitHomEquiv.symm (relativeDifferentialFormsAlgebra f).one

/-- On sections over `U`, `formsUnit` sends `r` to `r • 1`. -/
theorem formsUnit_val_app (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (r : (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)).val.obj U) :
    (formsUnit f).val.app U r =
      (show (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U from r) •
        (relativeDifferentialFormsAlgebra f).one.eval U :=
  rfl

/-- Reading a section of `Ω^b` in a propositionally equal degree. -/
theorem eqToHom_relativeDifferentialForms_val_app {b n : ℤ} (hn : b = n)
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (z : (relativeDifferentialForms f b).val.obj U)
    (w : (relativeDifferentialForms f n).val.obj U) (hw : HEq w z) :
    (eqToHom (congrArg (relativeDifferentialForms f) hn)).val.app U z = w := by
  subst hn
  exact (eq_of_heq hw).symm

/-- **`1 ∧ ω = ω`**: the unit `𝒪_X ⟶ Ω^0` followed by the wedge product `Ω^0 ⊗ Ω^b ⟶ Ω^b` is the
left unitor `𝒪_X ⊗ Ω^b ≅ Ω^b`. -/
theorem formsUnit_whisker_mulSheaf (b : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (formsUnit f)).app
        (relativeDifferentialForms f b) ≫ (relativeDifferentialFormsAlgebra f).mulSheaf 0 b =
      (sheafTensorUnitLeft X.toRingedSpace).app (relativeDifferentialForms f b) ≫
        eqToHom (congrArg (relativeDifferentialForms f) (zero_add b).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (J := Opens.grothendieckTopology X)
    (Osharp := X.sheaf)
    (F := _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (G := relativeDifferentialForms f b) (Q := relativeDifferentialForms f (0 + b))
    fun U r y => ?_
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    (Osharp := X.sheaf)
    (F := _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (G := relativeDifferentialForms f b) (formsUnit f) (𝟙 (relativeDifferentialForms f b)) U r y
  have e : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (formsUnit f)).app
        (relativeDifferentialForms f b) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (formsUnit f)).app
          (relativeDifferentialForms f b) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          (relativeDifferentialForms f 0)).map (𝟙 (relativeDifferentialForms f b)) :=
    (Category.comp_id _).symm.trans (congrArg (fun k => _ ≫ k)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
        (relativeDifferentialForms f 0)).map_id (relativeDifferentialForms f b)).symm)
  refine (congrArg (fun z => ((relativeDifferentialFormsAlgebra f).mulSheaf 0 b).val.app U z)
      ((congrArg (fun k => k.val.app U ((PresheafOfModules.tensorSheafUnit
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
        (relativeDifferentialForms f b)).app U (r ⊗ₜ y))) e).trans h)).trans ?_
  refine (SheafOfModules.GradedAlgebra.mulSheaf_unit _ 0 b U _ _).trans ?_
  have hl := Stacks.RingedSpace.tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X.toRingedSpace
    (relativeDifferentialForms f b) U r y
  refine Eq.trans ?_ (congrArg (fun t => (eqToHom (congrArg (relativeDifferentialForms f)
    (zero_add b).symm)).val.app U t) hl).symm
  let r' : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U := r
  let y₀ : ((relativeDifferentialFormsAlgebra f).piece b).val.obj U := y
  have h1 := formsUnit_val_app f U r
  have h2 := ((relativeDifferentialFormsAlgebra f).mul 0 b).map_smul_left U r'
    ((relativeDifferentialFormsAlgebra f).one.eval U) y
  have hsmul : ∀ {n : ℤ} (_ : b = n) (w : ((relativeDifferentialFormsAlgebra f).piece n).val.obj U),
      HEq w y₀ → HEq (r' • w) (r' • y₀) := by
    rintro n rfl w hw
    rw [eq_of_heq hw]
  have hA : HEq (((relativeDifferentialFormsAlgebra f).mul 0 b).app U ((formsUnit f).val.app U r) y)
      (r' • y₀) :=
    (heq_of_eq ((congrArg (fun z => ((relativeDifferentialFormsAlgebra f).mul 0 b).app U z y)
      h1).trans h2)).trans
      (hsmul (zero_add b).symm _ ((relativeDifferentialFormsAlgebra f).one_mul b U y))
  have heqToHom : ∀ {n : ℤ} (hn : b = n) (z : (relativeDifferentialForms f b).val.obj U),
      HEq ((eqToHom (congrArg (relativeDifferentialForms f) hn)).val.app U z) z := by
    rintro n rfl z
    rfl
  exact eq_of_heq (hA.trans (heqToHom (zero_add b).symm _).symm)

/-- **The canonical map `𝒪_X[0] ⊗^𝐋 𝒢[0] ⟶ (𝒪_X ⊗ 𝒢)[0]` followed by the left unitor is the
action of `𝒪_X[0]`**: both are the canonical map to the total tensor complex followed by the left
unitor on the only nonzero summand. -/
theorem derivedTensorSingleToTensor_sheafTensorUnitLeft (G : X.Modules) :
    Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor (R := X.sheaf)
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) G ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map
        ((sheafTensorUnitLeft X.toRingedSpace).app G)) =
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        (unitSingleComplex X.toRingedSpace) ((CochainComplex.singleFunctor X.Modules 0).obj G) ≫
      DerivedCategory.Q.map (unitLeftAction X.toRingedSpace
        ((CochainComplex.singleFunctor X.Modules 0).obj G)) := by
  unfold Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map ?_)
  exact (Category.assoc _ _ _).trans
    (mapBifunctorSingleRightIso_hom_comp_lam (R := X.sheaf) G (sheafTensorUnitLeft X.toRingedSpace))

/-- **The wedge product with the unit, in `D(𝒪_X)`**: `𝒪_X[0] ⊗^𝐋 Ω^b[0] ⟶ Ω^0[0] ⊗^𝐋 Ω^b[0]`
followed by the wedge product is the canonical map to the total tensor complex, the action of
`𝒪_X[0]`, and `Ω^b = Ω^{0+b}`. -/
theorem uncurry_map_formsUnit_comp_contractionMapOf (b : ℤ) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map (formsUnit f)) ×ₘ
          𝟙 (singleModule (relativeDifferentialForms f b))) ≫
      contractionMapOf (formsMul f 0 b (0 + b) rfl) =
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        (unitSingleComplex X.toRingedSpace)
        ((CochainComplex.singleFunctor X.Modules 0).obj (relativeDifferentialForms f b)) ≫
      DerivedCategory.Q.map (unitLeftAction X.toRingedSpace
        ((CochainComplex.singleFunctor X.Modules 0).obj (relativeDifferentialForms f b))) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map
        (eqToHom (congrArg (relativeDifferentialForms f) (zero_add b).symm))) := by
  let T := Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf
  let s := CochainComplex.singleFunctor X.Modules 0
  have a1 : (Functor.uncurry.obj T).map
      (DerivedCategory.Q.map (s.map (formsUnit f)) ×ₘ
        𝟙 (singleModule (relativeDifferentialForms f b))) =
      (T.map (DerivedCategory.Q.map (s.map (formsUnit f)))).app
        (singleModule (relativeDifferentialForms f b)) :=
    (congrArg (_ ≫ ·) ((T.obj _).map_id _)).trans (Category.comp_id _)
  have a2 : contractionMapOf (formsMul f 0 b (0 + b) rfl) =
      Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor (R := X.sheaf)
          (relativeDifferentialForms f 0) (relativeDifferentialForms f b) ≫
        DerivedCategory.Q.map (s.map ((relativeDifferentialFormsAlgebra f).mulSheaf 0 b)) :=
    congrArg (fun t => Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor (R := X.sheaf)
        (relativeDifferentialForms f 0) (relativeDifferentialForms f b) ≫
      DerivedCategory.Q.map (s.map t)) (Category.comp_id _)
  have a3 : (T.map (DerivedCategory.Q.map (s.map (formsUnit f)))).app
        (singleModule (relativeDifferentialForms f b)) ≫
      Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor (R := X.sheaf)
        (relativeDifferentialForms f 0) (relativeDifferentialForms f b) =
      Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor (R := X.sheaf)
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
          (relativeDifferentialForms f b) ≫
        DerivedCategory.Q.map (s.map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (formsUnit f)).app
            (relativeDifferentialForms f b))) :=
    Stacks.Duality.derivedTensorSingleToTensor_naturality_left (formsUnit f) _
  have a4 : DerivedCategory.Q.map (s.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (formsUnit f)).app
          (relativeDifferentialForms f b))) ≫
      DerivedCategory.Q.map (s.map ((relativeDifferentialFormsAlgebra f).mulSheaf 0 b)) =
      DerivedCategory.Q.map (s.map ((sheafTensorUnitLeft X.toRingedSpace).app
          (relativeDifferentialForms f b))) ≫
        DerivedCategory.Q.map (s.map
          (eqToHom (congrArg (relativeDifferentialForms f) (zero_add b).symm))) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      ((s.map_comp _ _).symm.trans ((congrArg s.map (formsUnit_whisker_mulSheaf f b)).trans
        (s.map_comp _ _)))).trans (DerivedCategory.Q.map_comp _ _))
  have a5 := derivedTensorSingleToTensor_sheafTensorUnitLeft (X := X)
    (relativeDifferentialForms f b)
  exact (congrArg (· ≫ contractionMapOf (formsMul f 0 b (0 + b) rfl)) a1).trans
    ((congrArg (_ ≫ ·) a2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) a3).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a4).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) a5).trans (Category.assoc _ _ _))))))))

open Stacks.Cohomology.DerivedGlobalCupProduct (unitClass totalCupPairing) in
/-- **The unit class `1 ∈ H⁰(X, Ω^0)`**: the image of the class `1 ∈ H⁰(X, 𝒪_X)` of the unit
section under the unit `𝒪_X ⟶ Ω^0` of the algebra of differential forms. -/
def hodgeUnitModule : cohomologyModule (singleModule (relativeDifferentialForms f 0)) 0 :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) 0).map
    ((baseSections X.toRingedSpace).map (DerivedCategory.Q.map
      ((CochainComplex.singleFunctor X.Modules 0).map (formsUnit f))))).hom
    ((unitClass (S := X.toRingedSpace)).hom 1)

open Stacks.Cohomology.DerivedGlobalCupProduct (unitClass totalCupPairing) in
/-- **The unit law of the cup product of Hodge cohomology**, as an identity of morphisms out of
`Γ(X, 𝒪_X)`. -/
theorem hodgeCupModule_unit_comp (b j : ℤ)
    (η : ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace) ⟶
      cohomologyModule (singleModule (relativeDifferentialForms f b)) j) :
    (λ_ (ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace))).inv ≫
        ((unitClass (S := X.toRingedSpace) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) 0).map
            ((baseSections X.toRingedSpace).map (DerivedCategory.Q.map
              ((CochainComplex.singleFunctor X.Modules 0).map (formsUnit f))))) ⊗ₘ η) ≫
        hodgeCupModule f 0 b (0 + b) rfl 0 j (0 + j) rfl =
      η ≫ eqToHom (congrArg (fun n => cohomologyModule
          (singleModule (relativeDifferentialForms f b)) n) (zero_add j).symm) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) (0 + j)).map
          ((baseSections X.toRingedSpace).map (DerivedCategory.Q.map
            ((CochainComplex.singleFunctor X.Modules 0).map
              (eqToHom (congrArg (relativeDifferentialForms f) (zero_add b).symm))))) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace))
  let Γs := baseSections X.toRingedSpace
  let s := CochainComplex.singleFunctor X.Modules 0
  have hn := cupPairing_naturality (cupProductOnSpace X.toRingedSpace)
    (DerivedCategory.Q.map (s.map (formsUnit f))) (𝟙 (singleModule (relativeDifferentialForms f b)))
    0 j unitClass η
  have hV : η ≫ (H j).map (Γs.map (𝟙 (singleModule (relativeDifferentialForms f b)))) = η :=
    (congrArg (η ≫ ·) ((congrArg (H j).map (Γs.map_id _)).trans ((H j).map_id _))).trans
      (Category.comp_id η)
  have hD := uncurry_map_formsUnit_comp_contractionMapOf f b
  have hW : (H (0 + j)).map (Γs.map ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
          (DerivedCategory.Q.map (s.map (formsUnit f)) ×ₘ
            𝟙 (singleModule (relativeDifferentialForms f b))))) ≫
      ((H (0 + j)).map (Γs.map (contractionMapOf (formsMul f 0 b (0 + b) rfl))) ≫ eqToHom rfl) =
      (H (0 + j)).map (Γs.map ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          X.sheaf).toTensor
            (Stacks.Cohomology.DerivedGlobalCupProduct.unitSingleComplex X.toRingedSpace)
            (s.obj (relativeDifferentialForms f b)))) ≫
        (H (0 + j)).map (Γs.map (DerivedCategory.Q.map
          (Stacks.Cohomology.DerivedGlobalCupProduct.unitLeftAction X.toRingedSpace
            (s.obj (relativeDifferentialForms f b))))) ≫
        (H (0 + j)).map (Γs.map (DerivedCategory.Q.map (s.map
          (eqToHom (congrArg (relativeDifferentialForms f) (zero_add b).symm))))) :=
    (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (eqToHom_refl _ _)).trans (Category.comp_id _))).trans
      (((H _).map_comp _ _).symm.trans ((congrArg (H _).map (Γs.map_comp _ _).symm).trans
        ((congrArg (fun t => (H (0 + j)).map (Γs.map t)) hD).trans
          ((congrArg (H _).map (Γs.map_comp _ _)).trans (((H _).map_comp _ _).trans
            (congrArg (_ ≫ ·) ((congrArg (H _).map (Γs.map_comp _ _)).trans
              ((H _).map_comp _ _))))))))
  have hu := Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_unitClass
    (S := X.toRingedSpace) ((CochainComplex.singleFunctor X.Modules 0).obj
      (relativeDifferentialForms f b))
    ⟨0, (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩ j η
  exact unitLaw_paste _ _ _ _ _ _ _ _ _ _ _ _ hn hV hW hu

/-- **The unit law of the cup product of Hodge cohomology**: `1 ∪ ξ = ξ` for `ξ ∈ H^j(X, Ω^b)`,
read in `H^m(X, Ω^n)` for `0 + b = n` and `0 + j = m`. -/
theorem hodgeCupModule_hodgeUnitModule (b n : ℤ) (h : 0 + b = n) (j m : ℤ) (hm : 0 + j = m)
    (ξ : cohomologyModule (singleModule (relativeDifferentialForms f b)) j) :
    (hodgeCupModule f 0 b n h 0 j m hm).hom (hodgeUnitModule f ⊗ₜ ξ) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) m).map
        ((baseSections X.toRingedSpace).map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor X.Modules 0).map
            (eqToHom (congrArg (relativeDifferentialForms f) (show b = n by omega))))))).hom
        ((eqToHom (congrArg (fun i => cohomologyModule
          (singleModule (relativeDifferentialForms f b)) i) (show j = m by omega))).hom ξ) := by
  subst h hm
  have key := ConcreteCategory.congr_hom (hodgeCupModule_unit_comp f b j
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X.toRingedSpace) _ ξ)))
      (1 : baseRing X.toRingedSpace)
  have key' := (Stacks.Cohomology.DerivedGlobalCupProduct.leftUnitor_inv_tensorHom_comp_hom_one
    _ _ _).symm.trans key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ConcreteCategory.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at key'
  exact key'

/-- The cup product of Hodge cohomology is `Γ(X, 𝒪_X)`-linear in its first variable. -/
theorem hodgeCupModule_smul_left (a b n : ℤ) (h : a + b = n) (i j m : ℤ) (hm : i + j = m)
    (g : baseRing X.toRingedSpace)
    (x : cohomologyModule (singleModule (relativeDifferentialForms f a)) i)
    (y : cohomologyModule (singleModule (relativeDifferentialForms f b)) j) :
    (hodgeCupModule f a b n h i j m hm).hom ((g • x) ⊗ₜ y) =
      g • (hodgeCupModule f a b n h i j m hm).hom (x ⊗ₜ y) := by
  rw [← TensorProduct.smul_tmul', map_smul]

/-- Mapping the identity of a single complex through the sections and homology fixes classes. -/
private theorem homologyFunctor_map_baseSections_map_Q_map_id_hom {X : Scheme.{u}} (G : X.Modules)
    (j : ℤ) (v : cohomologyModule (singleModule G) j) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) j).map
      ((baseSections X.toRingedSpace).map (DerivedCategory.Q.map
        (𝟙 ((CochainComplex.singleFunctor X.Modules 0).obj G))))).hom v = v :=
  (congrArg (fun φ => φ.hom v) ((congrArg (fun t =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) j).map
      ((baseSections X.toRingedSpace).map t)) (DerivedCategory.Q.map_id _)).trans
    ((congrArg (DerivedCategory.homologyFunctor _ j).map
        ((baseSections X.toRingedSpace).map_id _)).trans
      ((DerivedCategory.homologyFunctor _ j).map_id _)))).trans rfl

/-! ### `H⁰(X, Ω^0)` is free of rank one on the unit -/

/-- **`H⁰(X, Ω^0) ≅ Γ(X, 𝒪_X)`** as `Γ(X, 𝒪_X)`-modules: `H⁰(X, ℱ[0]) = R⁰Γ(X, ℱ) = Γ(X, ℱ)`, and
`Ω^0 = 𝒪_X`. -/
def hodgeZeroIso : cohomologyModule (singleModule (relativeDifferentialForms f 0)) 0 ≅
    ModuleCat.of (baseRing X.toRingedSpace) (baseRing X.toRingedSpace) :=
  (Stacks.Duality.homologyBaseSectionsSingleIso (X := X) 0).app (relativeDifferentialForms f 0) ≪≫
    (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
      (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤)).app
        (relativeDifferentialForms f 0) ≪≫
    (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤).mapIso
      (_root_.SheafOfModules.algebras _ (relativeDifferentials f)).exteriorPieceZeroIsoUnit

/-- `H⁰(X, Ω^0)` is free of rank one over `Γ(X, 𝒪_X)`, on the class `x₀` corresponding to `1`. -/
theorem bijective_smul_hodgeZeroGenerator :
    Function.Bijective (fun g : baseRing X.toRingedSpace =>
      g • (hodgeZeroIso f).inv.hom (1 : baseRing X.toRingedSpace)) := by
  have e : (fun g : baseRing X.toRingedSpace =>
      g • (hodgeZeroIso f).inv.hom (1 : baseRing X.toRingedSpace)) = (hodgeZeroIso f).inv.hom := by
    funext g
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [e]
  exact ConcreteCategory.bijective_of_isIso _

/-- **`H⁰(X, Ω^0)` is free of rank one over `Γ(X, 𝒪_X)` on the unit**: `g ↦ g • 1` is a
bijection `Γ(X, 𝒪_X) ⟶ H⁰(X, Ω^0)`. The unit is `s • x₀` for the generator `x₀` of
`bijective_smul_hodgeZeroGenerator` and some `s`; the unit law `1 ∪ x₀ = x₀` and linearity force
`s` to be a unit. -/
theorem bijective_smul_hodgeUnitModule :
    Function.Bijective (fun g : baseRing X.toRingedSpace => g • hodgeUnitModule f) := by
  have hφ := bijective_smul_hodgeZeroGenerator f
  set x₀ := (hodgeZeroIso f).inv.hom (1 : baseRing X.toRingedSpace)
  have hunit : ∀ ξ : cohomologyModule (singleModule (relativeDifferentialForms f 0)) 0,
      (hodgeCupModule f 0 0 0 rfl 0 0 0 rfl).hom (hodgeUnitModule f ⊗ₜ ξ) = ξ := by
    intro ξ
    rw [hodgeCupModule_hodgeUnitModule f 0 0 rfl 0 0 rfl ξ]
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
    exact homologyFunctor_map_baseSections_map_Q_map_id_hom _ 0 ξ
  obtain ⟨s, hs⟩ := hφ.2 (hodgeUnitModule f)
  obtain ⟨t, ht⟩ := hφ.2 ((hodgeCupModule f 0 0 0 rfl 0 0 0 rfl).hom (x₀ ⊗ₜ x₀))
  have hst : s * t = 1 := by
    refine hφ.1 ?_
    change (s * t) • x₀ = (1 : baseRing X.toRingedSpace) • x₀
    rw [one_smul, mul_smul]
    change s • (fun g : baseRing X.toRingedSpace => g • x₀) t = x₀
    rw [ht, ← hodgeCupModule_smul_left]
    change (hodgeCupModule f 0 0 0 rfl 0 0 0 rfl).hom
      ((fun g : baseRing X.toRingedSpace => g • x₀) s ⊗ₜ x₀) = x₀
    rw [hs, hunit]
  have key : (fun g : baseRing X.toRingedSpace => g • hodgeUnitModule f) =
      (fun g : baseRing X.toRingedSpace => g • x₀) ∘ (fun g => g * s) := by
    funext g
    simp only [Function.comp_apply, mul_smul]
    rw [← hs]
  rw [key]
  refine hφ.comp ⟨fun a b hab => ?_, fun a => ⟨a * t, by
    change a * t * s = a
    rw [mul_assoc, mul_comm t s, hst, mul_one]⟩⟩
  simpa [mul_assoc, hst] using congrArg (· * t) hab

end UnitLaw

/-! ### Uniqueness of the trace up to a unit -/

section Uniqueness

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Multiplication by `g ∈ Γ(X, 𝒪_X)` on `Hⁿ(X, ℱ)`**, as a `k`-linear map: the action of
`Γ(X, 𝒪_X)` on the cohomology module. -/
def cohomologySMul (F : X.Modules) (n : ℤ) (g : Γ(X, ⊤)) :
    sheafCohomology f F n →ₗ[k] sheafCohomology f F n where
  toFun v := (show baseRing X.toRingedSpace from g) •
    (show cohomologyModule (singleModule F) n from v)
  map_add' _ _ := smul_add _ _ _
  map_smul' c v := smul_comm (show baseRing X.toRingedSpace from g)
    (Stacks.Duality.globalRingHom f c) (show cohomologyModule (singleModule F) n from v)

/-- Moving the degrees of `Hⁿ(X, Ω^b)` along equalities and back is the identity. -/
theorem homologyFunctor_map_eqToHom_eqToHom_cancel {b n : ℤ} (hb : b = n) {j m : ℤ} (hj : j = m)
    (v : sheafCohomology f (relativeDifferentialForms f n) m) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) m).map
        ((baseSections X.toRingedSpace).map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor X.Modules 0).map
            (eqToHom (congrArg (relativeDifferentialForms f) hb)))))).hom
      ((eqToHom (congrArg (fun i => cohomologyModule
          (singleModule (relativeDifferentialForms f b)) i) hj)).hom
        ((eqToHom (by subst hb hj; rfl : sheafCohomology f (relativeDifferentialForms f n) m =
          sheafCohomology f (relativeDifferentialForms f b) j)).hom v)) = v := by
  subst hb hj
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact homologyFunctor_map_baseSections_map_Q_map_id_hom _ j v

/-- The `k`-algebra structure on `Γ(X, 𝒪_X)` given by the structure morphism `X ⟶ Spec k`. -/
abbrev algebraOfStructureMap : Algebra k (baseRing X.toRingedSpace) :=
  (Stacks.Duality.globalRingHom f).toAlgebra

/-- `Hⁿ(X, ℱ)` as a module over `Γ(X, 𝒪_X)`: the module structure of the cohomology module. -/
abbrev moduleSheafCohomology (F : X.Modules) (n : ℤ) :
    Module (baseRing X.toRingedSpace) (sheafCohomology f F n) :=
  inferInstanceAs (Module (baseRing X.toRingedSpace) (cohomologyModule (singleModule F) n))

/-- The scalar actions of `k` and `Γ(X, 𝒪_X)` on `Hⁿ(X, ℱ)` form a scalar tower. -/
theorem isScalarTower_sheafCohomology (F : X.Modules) (n : ℤ) :
    letI := algebraOfStructureMap f
    letI := moduleSheafCohomology f F n
    IsScalarTower k (baseRing X.toRingedSpace) (sheafCohomology f F n) :=
  let := algebraOfStructureMap f
  let := moduleSheafCohomology f F n
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

variable [IsProper f]

/-- **[Stacks, Tag 0FW4], for the trace attached to an isomorphism `ω_X ≅ Ω^d_{X/k}`.** Let `X`
be proper over a field `k` and smooth of relative dimension `d`, Cohen--Macaulay, equidimensional
of dimension `d`. For every isomorphism `e : ω_X ≅ Ω^d_{X/k}` the linear form
`t = hodgeTraceOfIso e : Hᵈ(X, Ω^d_{X/k}) ⟶ k` makes every pairing
`H^q(X, Ω^p) × H^{d-q}(X, Ω^{d-p}) ⟶ k, (ξ, ξ') ↦ t(ξ ∪ ξ')` perfect, and a linear form `t'` makes
all of them perfect if and only if `t' = t ∘ (u · -)` for a unit `u` of `H⁰(X, 𝒪_X)`, which is then
unique. -/
theorem hodgeDuality_of_iso (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    [SmoothOfRelativeDimension d f] (e : dualizingModule f ≅ relativeDifferentialForms f d) :
    ∃ t : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k,
      (∀ p q : ℤ, (hodgePairing f d t p q).IsPerfPair) ∧
      ∀ t' : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k,
        (∀ p q : ℤ, (hodgePairing f d t' p q).IsPerfPair) ↔
          ∃! u : (Γ(X, ⊤))ˣ, t' = t ∘ₗ cohomologySMul f (relativeDifferentialForms f d) d u := by
  let t := hodgeTraceOfIso f hCM hequi d hd e
  refine ⟨t, isPerfPair_hodgePairing_hodgeTraceOfIso f hCM hequi d hd e, fun t' => ?_⟩
  let := algebraOfStructureMap f
  let := fun (F : X.Modules) (n : ℤ) => moduleSheafCohomology f F n
  have := fun (F : X.Modules) (n : ℤ) => isScalarTower_sheafCohomology f F n
  let c : ∀ i : ℤ × ℤ, sheafCohomology f (relativeDifferentialForms f i.1) i.2 →ₗ[k]
      sheafCohomology f (relativeDifferentialForms f (d - i.1)) (d - i.2) →ₗ[k]
        sheafCohomology f (relativeDifferentialForms f d) d := fun i =>
    hodgeCup f i.1 (d - i.1) d (by ring) i.2 (d - i.2) d (by ring)
  have hc : ∀ (i : ℤ × ℤ) (g : baseRing X.toRingedSpace)
      (a : sheafCohomology f (relativeDifferentialForms f i.1) i.2)
      (b : sheafCohomology f (relativeDifferentialForms f (d - i.1)) (d - i.2)),
      c i (g • a) b = g • c i a b := fun i g a b =>
    hodgeCupModule_smul_left f i.1 (d - i.1) d (by ring) i.2 (d - i.2) d (by ring) g a b
  let lin : baseRing X.toRingedSpace →ₗ[k]
      sheafCohomology f (relativeDifferentialForms f ((0, 0) : ℤ × ℤ).1) ((0, 0) : ℤ × ℤ).2 :=
    { toFun := fun g => g • (show sheafCohomology f (relativeDifferentialForms f 0) 0 from
        hodgeUnitModule f)
      map_add' := fun g h => add_smul g h _
      map_smul' := fun c g => smul_assoc c g _ }
  let eA := LinearEquiv.ofBijective lin (bijective_smul_hodgeUnitModule f)
  have hV : sheafCohomology f (relativeDifferentialForms f d) d =
      sheafCohomology f (relativeDifferentialForms f ((d : ℤ) - ((0, 0) : ℤ × ℤ).1))
        ((d : ℤ) - ((0, 0) : ℤ × ℤ).2) := by
    simp
  let eB := (eqToIso hV).toLinearEquiv
  have h₀ : ∀ (g : baseRing X.toRingedSpace)
      (v : sheafCohomology f (relativeDifferentialForms f d) d),
      c (0, 0) (eA g) (eB v) = g • v := by
    intro g v
    refine (hc (0, 0) g _ (eB v)).trans (congrArg (g • ·) ?_)
    exact (hodgeCupModule_hodgeUnitModule f ((d : ℤ) - 0) d (by simp) ((d : ℤ) - 0) d (by simp)
      (eB v)).trans (homologyFunctor_map_eqToHom_eqToHom_cancel f
        (sub_zero _) (sub_zero _) v)
  have key := LinearMap.isPerfPair_compr₂_iff_existsUnique_unit c hc (i₀ := ((0, 0) : ℤ × ℤ)) eA eB
    h₀ t t' (fun i => isPerfPair_hodgePairing_hodgeTraceOfIso f hCM hequi d hd e i.1 i.2)
  exact ⟨fun h => key.1 fun i => h i.1 i.2, fun h p q => key.2 h (p, q)⟩

/-- **[Stacks, Tag 0FW4], at the hypotheses of the source, for the trace attached to an
isomorphism `ω_X ≅ Ω^d_{X/k}`.** Let `X` be a nonempty smooth proper scheme over a field `k`,
equidimensional of dimension `d`. For every isomorphism `e : ω_X ≅ Ω^d_{X/k}` the conclusion of
Tag 0FW4 holds for `t = hodgeTraceOfIso e`: `X` is Cohen--Macaulay (a smooth scheme over a field
is syntomic over it) and smooth of relative dimension `d` over `k`, and
`hodgeDuality_of_iso` applies. -/
theorem hodgeDuality_of_smooth_of_iso [Smooth f] [Nonempty X] (d : ℕ)
    (hequi : TopologicalSpace.Equidimensional X) (hd : topologicalKrullDim X = d)
    (e : dualizingModule f ≅ relativeDifferentialForms f d) :
    ∃ t : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k,
      (∀ p q : ℤ, (hodgePairing f d t p q).IsPerfPair) ∧
      ∀ t' : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k,
        (∀ p q : ℤ, (hodgePairing f d t' p q).IsPerfPair) ↔
          ∃! u : (Γ(X, ⊤))ˣ, t' = t ∘ₗ cohomologySMul f (relativeDifferentialForms f d) d u :=
  have := smoothOfRelativeDimension_of_equidimensional k f hequi d hd
  hodgeDuality_of_iso f (isCohenMacaulay_of_syntomic_over_field f (syntomic_of_smooth f))
    hequi d hd e

/-- **[Stacks, Tag 0FW4].** Let `k` be a field and `X` a nonempty smooth proper scheme over `k`,
equidimensional of dimension `d`. There is a `k`-linear map `t : Hᵈ(X, Ω^d_{X/k}) ⟶ k` such
that for all `p, q` the pairing `H^q(X, Ω^p_{X/k}) × H^{d-q}(X, Ω^{d-p}_{X/k}) ⟶ k`,
`(ξ, ξ') ↦ t(ξ ∪ ξ')` is perfect, and `t` is unique up to precomposing with multiplication by a
unit of `H⁰(X, 𝒪_X)`: a linear map `t'` has the same property if and only if
`t' = t ∘ (u · -)` for a unit `u` of `H⁰(X, 𝒪_X)`, and that unit is unique. The map `t` is the
trace read through `ω_X ≅ Ω^d_{X/k}` ([Stacks, Tag 0FVV], part (7)). -/
@[stacks 0FW4 "for X nonempty smooth proper over a field k, equidimensional of dimension d: \
there is t : H^d(X, Omega^d) -> k, unique up to precomposition with multiplication by a unit of \
H^0(X, O_X), such that every pairing H^q(X, Omega^p) x H^{d-q}(X, Omega^{d-p}) -> k, \
(xi, xi') |-> t(xi cup xi') is perfect"]
theorem hodgeDuality [Smooth f] [Nonempty X] (d : ℕ)
    (hequi : TopologicalSpace.Equidimensional X) (hd : topologicalKrullDim X = d) :
    ∃ t : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k,
      (∀ p q : ℤ, (hodgePairing f d t p q).IsPerfPair) ∧
      ∀ t' : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k,
        (∀ p q : ℤ, (hodgePairing f d t' p q).IsPerfPair) ↔
          ∃! u : (Γ(X, ⊤))ˣ, t' = t ∘ₗ cohomologySMul f (relativeDifferentialForms f d) d u :=
  have := smoothOfRelativeDimension_of_equidimensional k f hequi d hd
  hodgeDuality_of_smooth_of_iso f d hequi hd
    (Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      f d).2.some

end Uniqueness

end AlgebraicGeometry.Scheme.Hom
