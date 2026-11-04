module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.DeRhamDualityGradedPieces
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.DeRhamDualityTopDegree
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialSpreadOut
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupBottomTop
public import StacksFrontier.LinearAlgebra.PerfectPairing.TraceRescaling
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexCech
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Poincaré duality for de Rham cohomology

Let `k` be a field and `X` a nonempty smooth proper scheme over `k`, equidimensional of
dimension `d`. This file proves [Stacks, Tag 0FW7]: there is a `k`-linear map
`t : H^{2d}_{dR}(X/k) ⟶ k`, unique up to precomposing with multiplication by a unit of
`H⁰(X, 𝒪_X)`, such that for every `i` the pairing

`H^i_{dR}(X/k) × H^{2d-i}_{dR}(X/k) ⟶ k,  (ξ, ξ') ↦ t(ξ ∪ ξ')`

is perfect.

The proof is that of the Stacks project. By the vanishing of the top differential on `Hᵈ`
([Stacks, Tag 0FW6]), Grothendieck vanishing ([Stacks, Tag 02UZ]) and the vanishing of `Ω^p`
for `p > d`, the inclusion `Ωᵈ[-d] ⟶ Ω^•` identifies `H^{2d}_{dR}(X/k) = Hᵈ(X, Ωᵈ)`; the trace
`t` is the trace of Hodge duality ([Stacks, Tag 0FW4]) read through this identification. The
pairings of the graded pieces `Ωᵖ[-p]` of the brutal filtration are those of Hodge duality, so
they are perfect, and the five lemma along the brutal filtrations gives the perfectness for the
whole complex (`Stacks.Cech.Hypercohomology.isPerfPair_cupK_of_gradedPerfect`).

For the uniqueness, the projection `Ω^• ⟶ Ω⁰[0] = 𝒪_X[0]` gives `H⁰_{dR}(X/k) ⟶ H⁰(X, 𝒪_X)`;
through it and the identification of `H^{2d}_{dR}`, the cup product
`H⁰_{dR} × H^{2d}_{dR} ⟶ H^{2d}_{dR}` is the module structure of `Hᵈ(X, Ωᵈ)` over `H⁰(X, 𝒪_X)`
(`Stacks.Cech.Hypercohomology.cup_ιTruncPlus_eq_cup_gradedPairing` and the unit law of the cup
product of Hodge cohomology). The perfectness for `i = 0` then shows that
`H⁰_{dR}(X/k) ⟶ H⁰(X, 𝒪_X)` is bijective, and that a second linear form `t'` has the same
property exactly when `t' = t(u ∪ -)` for a unit `u` of `H⁰(X, 𝒪_X)`
(`LinearMap.isPerfPair_compr₂_iff_existsUnique_unit`).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyZeroToSections`: `H⁰_{dR}(X/k) ⟶ H⁰(X, 𝒪_X)`.
* `AlgebraicGeometry.Scheme.Hom.deRhamCupBilinear`: the cup product of de Rham cohomology over
  `k`, as a `k`-bilinear map.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamTopEquiv_cup`: the cup product with `H⁰_{dR}` is the module
  structure of `Hᵈ(X, Ωᵈ)`.
* `AlgebraicGeometry.Scheme.Hom.bijective_deRhamCohomologyZeroToSections`:
  `H⁰_{dR}(X/k) = H⁰(X, 𝒪_X)`.
* `AlgebraicGeometry.Scheme.Hom.deRhamPoincareDuality`: **[Stacks, Tag 0FW7].**

## References

* [Stacks Project, Tag 0FW7](https://stacks.math.columbia.edu/tag/0FW7)
* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
* [Stacks Project, Tag 0FW5](https://stacks.math.columbia.edu/tag/0FW5)
* [Stacks Project, Tag 0FW6](https://stacks.math.columbia.edu/tag/0FW6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (SectionRing)
open Stacks.Cech.Hypercohomology
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open Stacks.Duality (sheafCohomology singleModule)
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.TopDegreeDifferential
  (rightDerived_map_deRham_d_eq_zero_of_isProper_of_smooth)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafOfModules.deRhamComplexPlus

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### `H⁰(X, Ω⁰) = H⁰(X, 𝒪_X)` and the unit law in the top degree -/

/-- **`H⁰(X, 𝒪_X) ≅ H⁰(X, Ω⁰_{X/k})`, `g ↦ g · 1`**: `H⁰(X, Ω⁰)` is free of rank one over
`Γ(X, 𝒪_X)` on the unit class. -/
def hodgeZeroAddEquiv :
    baseRing X.toRingedSpace ≃+ sheafCohomology f (relativeDifferentialForms f 0) 0 :=
  AddEquiv.ofBijective
    ({ toFun := fun g : baseRing X.toRingedSpace => g • hodgeUnitModule f
       map_zero' := zero_smul _ _
       map_add' := fun _ _ => add_smul _ _ _ } :
      baseRing X.toRingedSpace →+ sheafCohomology f (relativeDifferentialForms f 0) 0)
    (bijective_smul_hodgeUnitModule f)

/-- `hodgeZeroAddEquiv` sends `g` to `g` times the unit class of `H⁰(X, Ω⁰)`. -/
theorem hodgeZeroAddEquiv_apply (g : baseRing X.toRingedSpace) :
    hodgeZeroAddEquiv f g = g • hodgeUnitModule f :=
  rfl

/-- **The cup product with the class of `g ∈ H⁰(X, 𝒪_X)` in `H⁰(X, Ω⁰)` is multiplication by
`g`** on `Hᵈ(X, Ωᵈ)`: the cup product is `Γ(X, 𝒪_X)`-linear in its first variable and the unit
class is a unit. -/
theorem hodgeCup_hodgeZeroAddEquiv (d : ℕ) (g : Γ(X, ⊤))
    (w : sheafCohomology f (relativeDifferentialForms f d) d) :
    hodgeCup f 0 d d (zero_add _) 0 d d (zero_add _) (hodgeZeroAddEquiv f g) w =
      cohomologySMul f (relativeDifferentialForms f d) d g w := by
  refine (hodgeCupModule_smul_left f 0 d d (zero_add _) 0 d d (zero_add _) g (hodgeUnitModule f)
    w).trans (congrArg ((g : baseRing X.toRingedSpace) • ·) ?_)
  rw [hodgeCupModule_hodgeUnitModule f d d (zero_add _) d d (zero_add _) w]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact (congrArg (fun φ => φ.hom w) ((congrArg (fun t =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) d).map
      ((baseSections X.toRingedSpace).map t)) (DerivedCategory.Q.map_id _)).trans
    ((congrArg (DerivedCategory.homologyFunctor _ d).map
      ((baseSections X.toRingedSpace).map_id _)).trans
      ((DerivedCategory.homologyFunctor _ d).map_id _)))).trans rfl

/-! ### The bottom degree: `Ω^• ⟶ Ω⁰[0]` -/

/-- **`Ω⁰[0] ≅ σ^{≤0}Ω^•`**: the de Rham complex lives in degrees `≥ 0`, so its quotient
truncation in degrees `≤ 0` is its degree-zero term. -/
def deRhamBottomIso :
    singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X 0) 0 ≅
      truncLEPlus (inverseImageRingSheaf f) (deRhamPlus f) 0 :=
  have : (deRhamPlus f).obj.IsStrictlyGE 0 := SheafOfModules.isStrictlyGE_deRhamComplexPlus _ _
  ObjectProperty.isoMk _ (@asIso _ _ _ _
    (StacksDraft.StupidTruncation.stupidTruncLEι (deRhamPlus f).obj 0)
    (StacksDraft.StupidTruncation.isIso_stupidTruncLEι (deRhamPlus f).obj 0))

/-- The forward map of `deRhamBottomIso` is `truncLEι`, the inclusion `Ω⁰[0] ⟶ σ^{≤0}Ω^•`. -/
theorem deRhamBottomIso_hom :
    (deRhamBottomIso f).hom = truncLEι (inverseImageRingSheaf f) (deRhamPlus f) 0 :=
  rfl

section AffineDiagonal

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **`H⁰(X, Ω^•_{X/k}) ⟶ H⁰(X, 𝒪_X)`**, induced by `Ω^• ⟶ Ω⁰[0] = 𝒪_X[0]`: the projection onto
`σ^{≤0}Ω^• = Ω⁰[0]`, the identification of `H⁰(X, Ω⁰[0])` with the Hodge cohomology group
`H⁰(X, Ω⁰)`, and `H⁰(X, Ω⁰) = H⁰(X, 𝒪_X)`. -/
def deRhamZeroHyper :
    hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) 0 →+ Γ(X, ⊤) :=
  (hodgeZeroAddEquiv f).symm.toAddMonoidHom.comp
    ((formsTransfer f 0 0).toLinearMap.toAddMonoidHom.comp
      ((hypercohomologyMap (inverseImageRingSheaf f) (deRhamBottomIso f).inv
        0).hom.toAddMonoidHom.comp
        (hypercohomologyMap (inverseImageRingSheaf f)
          (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) 0) 0).hom.toAddMonoidHom))

/-- The class in `H⁰(X, Ω⁰[0])` of the image of a class of `H⁰(X, Ω^•)`. -/
abbrev deRhamZeroClass (ξ : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) 0) :
    hypercohomology (inverseImageRingSheaf f) (singlePlus (inverseImageRingSheaf f)
      ((deRhamPlus f).obj.X 0) 0) 0 :=
  hypercohomologyMap (inverseImageRingSheaf f) (deRhamBottomIso f).inv 0
    (hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) 0) 0 ξ)

/-- The image under `hodgeZeroAddEquiv` of `deRhamZeroHyper f ξ` is the Hodge class
`formsTransfer f 0 0 (deRhamZeroClass f ξ)` in `H⁰(X, Ω⁰)`. -/
theorem hodgeZeroAddEquiv_deRhamZeroHyper
    (ξ : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) 0) :
    hodgeZeroAddEquiv f (deRhamZeroHyper f ξ) = formsTransfer f 0 0 (deRhamZeroClass f ξ) :=
  (hodgeZeroAddEquiv f).apply_symm_apply _

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- Mapping `deRhamZeroClass f ξ` along `Ω⁰[0] ⟶ σ^{≤0}Ω^•` recovers the image of `ξ` under the
projection `Ω^• ⟶ σ^{≤0}Ω^•`. -/
theorem hypercohomologyMap_truncLEι_deRhamZeroClass
    (ξ : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) 0) :
    hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) 0) 0
        (deRhamZeroClass f ξ) =
      hypercohomologyMap (inverseImageRingSheaf f)
        (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) 0) 0
        ξ := by
  rw [← deRhamBottomIso_hom]
  show (hypercohomologyMap (inverseImageRingSheaf f) (deRhamBottomIso f).inv 0 ≫
    hypercohomologyMap (inverseImageRingSheaf f) (deRhamBottomIso f).hom 0) _ = _
  rw [← hypercohomologyMap_comp, Iso.inv_hom_id, hypercohomologyMap_id]
  rfl

/-! ### The top degree: `H^{2d}_{dR} = Hᵈ(X, Ωᵈ)` -/

section Top

variable (d : ℕ) (hd : ∀ n, (d : ℤ) < n → IsZero ((deRhamPlus f).obj.X n))
  (hι : Function.Bijective (hypercohomologyMap (inverseImageRingSheaf f)
    (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)))

/-- **`H^{2d}(X, Ω^•) ≅ Hᵈ(X, Ωᵈ)`**, `k`-linearly, when the de Rham complex vanishes above
degree `d` and `Ωᵈ[-d] ⟶ σ^{≤d}Ω^• = Ω^•` is bijective on `H^{2d}`. -/
def deRhamTopEquiv :
    hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f) ((d : ℤ) + d) ≃ₗ[k]
      sheafCohomology f (relativeDifferentialForms f d) d :=
  (LinearEquiv.ofBijective (hypercohomologyMapK (inverseImageRingSheaf f) (deRhamCoeff f)
      (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d))
      (bijective_hypercohomologyMap_truncLEπ (deRhamPlus f) d _ hd)).trans
    ((LinearEquiv.ofBijective (hypercohomologyMapK (inverseImageRingSheaf f) (deRhamCoeff f)
      (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)) hι).symm.trans
      (formsTransfer f d d))

/-- On a class coming from the truncation `truncPlus` in degree `2d`, `deRhamTopEquiv` is the
Hodge class of its image under `truncPlusπ`. -/
theorem deRhamTopEquiv_hypercohomologyMap_ιTruncPlus
    (w : hypercohomology (inverseImageRingSheaf f)
      (truncPlus (inverseImageRingSheaf f) (deRhamPlus f).obj d) ((d : ℤ) + d)) :
    deRhamTopEquiv f d hd hι (hypercohomologyMap (inverseImageRingSheaf f)
        (ιTruncPlus (inverseImageRingSheaf f) (deRhamPlus f) d) _ w) =
      formsTransfer f d d (hypercohomologyMap (inverseImageRingSheaf f)
        (truncPlusπ (deRhamPlus f).obj d) _ w) := by
  have hc : hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)
        (hypercohomologyMap (inverseImageRingSheaf f)
          (ιTruncPlus (inverseImageRingSheaf f) (deRhamPlus f) d) _ w) =
      hypercohomologyMap (inverseImageRingSheaf f)
        (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)
          (hypercohomologyMap (inverseImageRingSheaf f) (truncPlusπ (deRhamPlus f).obj d) _ w) := by
    show (hypercohomologyMap _ _ _ ≫ hypercohomologyMap _ _ _) w =
      (hypercohomologyMap _ _ _ ≫ hypercohomologyMap _ _ _) w
    rw [← hypercohomologyMap_comp, ← hypercohomologyMap_comp, ιTruncPlus_truncLEπ]
  show formsTransfer f d d ((LinearEquiv.ofBijective _ hι).symm
    (hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) d)
      ((d : ℤ) + d) (hypercohomologyMap (inverseImageRingSheaf f)
        (ιTruncPlus (inverseImageRingSheaf f) (deRhamPlus f) d) _ w))) = _
  rw [hc, LinearEquiv.ofBijective_symm_apply_apply]

/-- **The cup product `H⁰_{dR} × H^{2d}_{dR} ⟶ H^{2d}_{dR}` is the module structure of
`Hᵈ(X, Ωᵈ)` over `H⁰(X, 𝒪_X)`**, through `H⁰_{dR} ⟶ H⁰(X, 𝒪_X)` and `H^{2d}_{dR} = Hᵈ(X, Ωᵈ)`:
only the bidegree `(0, d)` component of the wedge product contributes, and it is the cup product
`H⁰(X, Ω⁰) × Hᵈ(X, Ωᵈ) ⟶ Hᵈ(X, Ωᵈ)` of Hodge cohomology. -/
theorem deRhamTopEquiv_cup (ξ : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) 0)
    (η : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) ((d : ℤ) + d)) :
    deRhamTopEquiv f d hd hι (cup (inverseImageRingSheaf f)
        (cechComputes_of_terms _ _ (cechComputesSheaf_deRhamComplexInt_X f))
        (cechComputes_of_terms _ _ (cechComputesSheaf_deRhamComplexInt_X f))
        (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras f)))
        0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ η) =
      cohomologySMul f (relativeDifferentialForms f d) d (deRhamZeroHyper f ξ)
        (deRhamTopEquiv f d hd hι η) := by
  obtain ⟨w, rfl⟩ := (bijective_hypercohomologyMap_ιTruncPlus_of_truncLEι (deRhamPlus f) d
    ((d : ℤ) + d) hd hι).2 η
  rw [cup_ιTruncPlus_eq_cup_gradedPairing (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f)
      _ d hd 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ w (deRhamZeroClass f ξ)
      (hypercohomologyMap_truncLEι_deRhamZeroClass f ξ),
    deRhamTopEquiv_hypercohomologyMap_ιTruncPlus, ← hodgeCup_hodgeZeroAddEquiv,
    hodgeZeroAddEquiv_deRhamZeroHyper]
  set z := hypercohomologyMap (inverseImageRingSheaf f) (truncPlusπ (deRhamPlus f).obj d) _ w
  have hπ := hypercohomologyMap_truncLEπ_cup_gradedPairing (deRhamPlus f)
    (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras f))) d hd 0 d (zero_add _) _
    (deRhamCechPairing_μ f 0 d d (zero_add _))
    (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) 0)
    (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) d)
    0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) (deRhamZeroClass f ξ) z
  show formsTransfer f d d ((LinearEquiv.ofBijective _ hι).symm
    (hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) d)
      ((d : ℤ) + d) _)) = _
  rw [hπ, LinearEquiv.ofBijective_symm_apply_apply]
  refine (formsTransfer_cup f 0 d d 0 d (by simp) (by simp) (by simp)
    (deRhamZeroClass f ξ) z).trans ?_
  simp only [CharP.cast_eq_zero, zero_mul, Int.negOnePow_zero, Units.val_one, one_smul]
  rfl

end Top


/-! ### Perfectness and uniqueness, in hypercohomology -/

section Duality

variable (d : ℕ) [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
  (hd : ∀ n, (d : ℤ) < n → IsZero ((deRhamPlus f).obj.X n))
  (hι : Function.Bijective (hypercohomologyMap (inverseImageRingSheaf f)
    (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)))

/-- The cup product of de Rham cohomology over `k`, computed in hypercohomology. -/
abbrev deRhamCupK (i j n : ℤ) (h : i + j = n) :
    hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f) i →ₗ[k]
      hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f) j →ₗ[k]
        hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f) n :=
  cupK (inverseImageRingSheaf f) (deRhamCoeff f)
    (cechComputes_of_terms _ _ (cechComputesSheaf_deRhamComplexInt_X f))
    (cechComputes_of_terms _ _ (cechComputesSheaf_deRhamComplexInt_X f))
    (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras f))) i j n h

include hdim in
/-- **Poincaré duality from Hodge duality**: for a linear form `tH` on `Hᵈ(X, Ωᵈ)` making the
pairings of Hodge duality perfect ([Stacks, Tag 0FW4]), the linear form `tH` read on
`H^{2d}_{dR} = Hᵈ(X, Ωᵈ)` makes every pairing `Hⁱ_{dR} × Hʲ_{dR} ⟶ k`, `i + j = 2d`, perfect. -/
theorem isPerfPair_deRhamCupK (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (hH : ∀ p q : ℤ, (hodgePairing f d tH p q).IsPerfPair) (i j : ℤ) (hij : i + j = (d : ℤ) + d) :
    ((deRhamCupK f i j ((d : ℤ) + d) hij).compr₂
      (tH ∘ₗ (deRhamTopEquiv f d hd hι).toLinearMap)).IsPerfPair := by
  let t' : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
      (truncLEPlus (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d) →ₗ[k] k :=
    tH ∘ₗ (formsTransfer f d d).toLinearMap ∘ₗ
      (LinearEquiv.ofBijective (hypercohomologyMapK (inverseImageRingSheaf f) (deRhamCoeff f)
        (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)) hι).symm.toLinearMap
  exact isPerfPair_cupK_of_gradedPerfect (deRhamCoeff f) (deRhamPlus f)
    (cechComputesSheaf_deRhamComplexInt_X f)
    (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras f))) d hd ((d : ℤ) + d)
    (tH ∘ₗ (deRhamTopEquiv f d hd hι).toLinearMap) (isZero_deRhamPlus_X_of_neg f)
    (fun a b hab ha hb => gradedPerfect_deRham f d hdim hd tH hH _ t' (fun z => rfl)
      (fun z => congrArg (fun x => tH (formsTransfer f d d x))
        (LinearEquiv.ofBijective_symm_apply_apply _ z)) a b hab ha hb)
    (by positivity) i j hij

omit [NoetherianSpace X] in
/-- The pairing `(ξ, η) ↦ t(ξ ∪ η)` on `H⁰_{dR} × H^{2d}_{dR}`, for `t = tH` read on
`H^{2d}_{dR} = Hᵈ(X, Ωᵈ)`, is the pairing `(g, w) ↦ tH(g · w)` on `H⁰(X, 𝒪_X) × Hᵈ(X, Ωᵈ)`. -/
theorem deRhamCupK_zero_apply (t₀ : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (ξ : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) 0)
    (η : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) ((d : ℤ) + d)) :
    ((deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _)).compr₂
      (t₀ ∘ₗ (deRhamTopEquiv f d hd hι).toLinearMap)) ξ η =
      t₀ (cohomologySMul f (relativeDifferentialForms f d) d (deRhamZeroHyper f ξ)
        (deRhamTopEquiv f d hd hι η)) :=
  congrArg t₀ (deRhamTopEquiv_cup f d hd hι ξ η)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [NoetherianSpace X] in
/-- The pairing `(g, w) ↦ tH(g · w)` is perfect when `tH` makes the pairings of Hodge duality
perfect: it is the pairing `H⁰(X, Ω⁰) × Hᵈ(X, Ωᵈ) ⟶ k` through `H⁰(X, Ω⁰) = H⁰(X, 𝒪_X)`. -/
theorem isPerfPair_smul_of_hodgePairing
    (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (hH : ∀ p q : ℤ, (hodgePairing f d tH p q).IsPerfPair) :
    letI := algebraOfStructureMap f
    letI := moduleSheafCohomology f (relativeDifferentialForms f d) d
    haveI := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
    ((Algebra.lsmul (A := baseRing X.toRingedSpace) k k
      (sheafCohomology f (relativeDifferentialForms f d) d)).toLinearMap.compr₂
      tH).IsPerfPair := by
  let := algebraOfStructureMap f
  let := moduleSheafCohomology f (relativeDifferentialForms f d) d
  have := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
  refine LinearMap.isPerfPair_of_addEquiv _
    ((hodgeCup f 0 d d (zero_add _) 0 d d (zero_add _)).compr₂ tH) (hodgeZeroAddEquiv f)
    (AddEquiv.refl _) 1 (fun g w => ?_)
    (isPerfPair_hodgeCup_of_hodgePairing f d tH hH 0 d 0 d (zero_add _) (zero_add _))
  rw [Units.val_one, one_mul]
  exact congrArg tH (hodgeCup_hodgeZeroAddEquiv f d g w)

include hdim hd hι in
/-- **`H⁰_{dR}(X/k) = H⁰(X, 𝒪_X)`** in the setting of Poincaré duality: the map induced by
`Ω^• ⟶ 𝒪_X[0]` is bijective, because both are dual to `H^{2d}_{dR} = Hᵈ(X, Ωᵈ)`. -/
theorem bijective_deRhamZeroHyper
    (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (hH : ∀ p q : ℤ, (hodgePairing f d tH p q).IsPerfPair) :
    Function.Bijective (deRhamZeroHyper f) := by
  let := algebraOfStructureMap f
  let := moduleSheafCohomology f (relativeDifferentialForms f d) d
  have := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
  set β := deRhamTopEquiv f d hd hι
  set P := (deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _)).compr₂ (tH ∘ₗ β.toLinearMap)
  set Q := (Algebra.lsmul (A := baseRing X.toRingedSpace) k k
      (sheafCohomology f (relativeDifferentialForms f d) d)).toLinearMap.compr₂
    tH
  have := isPerfPair_deRhamCupK f d hdim hd hι tH hH 0 ((d : ℤ) + d) (zero_add _)
  have := isPerfPair_smul_of_hodgePairing f d tH hH
  have hP := LinearMap.IsPerfPair.bijective_left P
  have hQ := LinearMap.IsPerfPair.bijective_left Q
  have key : ∀ ξ η, P ξ η = Q (deRhamZeroHyper f ξ) (β η) := fun ξ η =>
    deRhamCupK_zero_apply f d hd hι tH ξ η
  refine ⟨fun ξ₁ ξ₂ h => hP.1 (LinearMap.ext fun η =>
    (key ξ₁ η).trans ((congrArg (fun g => Q g (β η)) h).trans (key ξ₂ η).symm)), fun g => ?_⟩
  obtain ⟨ξ, hξ⟩ := hP.2 (Q g ∘ₗ β.toLinearMap)
  refine ⟨ξ, hQ.1 (LinearMap.ext fun w => ?_)⟩
  have h := LinearMap.congr_fun hξ (β.symm w)
  rw [key, LinearEquiv.apply_symm_apply] at h
  exact h.trans (congrArg (Q g) (β.apply_symm_apply w))

omit [NoetherianSpace X] in
/-- A linear form `t₀` on `H^{2d}_{dR}` is `t(ξ ∪ -)`, for `t = tH` read on
`H^{2d}_{dR} = Hᵈ(X, Ωᵈ)`, if and only if `t₀` read on `Hᵈ(X, Ωᵈ)` is `tH(α(ξ) · -)`. -/
private theorem eq_comp_deRhamCupK_zero_iff
    (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (ξ : hypercohomology (inverseImageRingSheaf f) (deRhamPlus f) 0)
    (t₀ : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f)
      ((d : ℤ) + d) →ₗ[k] k) :
    letI := algebraOfStructureMap f
    letI := moduleSheafCohomology f (relativeDifferentialForms f d) d
    haveI := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
    t₀ = (tH ∘ₗ (deRhamTopEquiv f d hd hι).toLinearMap) ∘ₗ
        deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ ↔
      t₀ ∘ₗ (deRhamTopEquiv f d hd hι).symm.toLinearMap =
        tH ∘ₗ Algebra.lsmul (A := baseRing X.toRingedSpace) k k
          (sheafCohomology f (relativeDifferentialForms f d) d) (deRhamZeroHyper f ξ) := by
  let := algebraOfStructureMap f
  let := moduleSheafCohomology f (relativeDifferentialForms f d) d
  have := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
  set β := deRhamTopEquiv f d hd hι
  have hc : ∀ η, ((tH ∘ₗ β.toLinearMap) ∘ₗ
      deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ) η =
      tH (cohomologySMul f (relativeDifferentialForms f d) d (deRhamZeroHyper f ξ) (β η)) :=
    fun η => deRhamCupK_zero_apply f d hd hι tH ξ η
  constructor
  · rintro rfl
    exact LinearMap.ext fun w => by
      rw [LinearMap.comp_apply, hc, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rfl
  · intro h
    refine LinearMap.ext fun η => ?_
    rw [(β.comp_toLinearMap_symm_eq _ _).1 h]
    exact (hc η).symm

include hdim in
/-- If `t'` makes the pairing `H⁰_{dR} × H^{2d}_{dR} ⟶ k` perfect, then `t'` read on
`Hᵈ(X, Ωᵈ)` makes the pairing `(g, w) ↦ t'(g · w)` on `H⁰(X, 𝒪_X) × Hᵈ(X, Ωᵈ)` perfect. -/
private theorem isPerfPair_lsmul_compr₂_deRhamTopEquiv_symm
    (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (hH : ∀ p q : ℤ, (hodgePairing f d tH p q).IsPerfPair)
    (t' : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f)
      ((d : ℤ) + d) →ₗ[k] k)
    (ht' : ((deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _)).compr₂ t').IsPerfPair) :
    letI := algebraOfStructureMap f
    letI := moduleSheafCohomology f (relativeDifferentialForms f d) d
    haveI := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
    ((Algebra.lsmul (A := baseRing X.toRingedSpace) k k
      (sheafCohomology f (relativeDifferentialForms f d) d)).toLinearMap.compr₂
        (t' ∘ₗ (deRhamTopEquiv f d hd hι).symm.toLinearMap)).IsPerfPair := by
  let := algebraOfStructureMap f
  let := moduleSheafCohomology f (relativeDifferentialForms f d) d
  have := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
  set β := deRhamTopEquiv f d hd hι
  let αE := AddEquiv.ofBijective (deRhamZeroHyper f)
    (bijective_deRhamZeroHyper f d hdim hd hι tH hH)
  refine LinearMap.isPerfPair_of_addEquiv _
    ((deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _)).compr₂ t') αE.symm
    β.symm.toAddEquiv 1 (fun g w => ?_) ht'
  rw [Units.val_one, one_mul]
  show t' (deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) (αE.symm g)
    (β.symm w)) = t' (β.symm (g • w))
  refine congrArg t' (β.injective ?_)
  rw [LinearEquiv.apply_symm_apply]
  refine (deRhamTopEquiv_cup f d hd hι (αE.symm g) (β.symm w)).trans ?_
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun g' => cohomologySMul f (relativeDifferentialForms f d) d g' w)
    (αE.apply_symm_apply g)

include hdim in
/-- **The uniqueness in Poincaré duality, in hypercohomology.** For `t = tH` read on
`H^{2d}_{dR} = Hᵈ(X, Ωᵈ)`, where `tH` is a trace of Hodge duality, a linear form `t'` on
`H^{2d}_{dR}` makes every pairing `Hⁱ_{dR} × Hʲ_{dR} ⟶ k`, `i + j = 2d`, perfect if and only if
`t' = t(ξ ∪ -)` for a class `ξ ∈ H⁰_{dR}` whose image in `H⁰(X, 𝒪_X)` is a unit, and that unit is
unique. -/
theorem isPerfPair_deRhamCupK_iff
    (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (hH : ∀ p q : ℤ, (hodgePairing f d tH p q).IsPerfPair)
    (hHu : ∀ t' : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k,
      (∀ p q : ℤ, (hodgePairing f d t' p q).IsPerfPair) ↔
        ∃! u : (Γ(X, ⊤))ˣ, t' = tH ∘ₗ cohomologySMul f (relativeDifferentialForms f d) d u)
    (t' : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f)
      ((d : ℤ) + d) →ₗ[k] k) :
    (∀ (i j : ℤ) (hij : i + j = (d : ℤ) + d),
      ((deRhamCupK f i j ((d : ℤ) + d) hij).compr₂ t').IsPerfPair) ↔
      ∃! u : (Γ(X, ⊤))ˣ, ∃ ξ : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
        (deRhamPlus f) 0,
        deRhamZeroHyper f ξ = u ∧ t' = (tH ∘ₗ (deRhamTopEquiv f d hd hι).toLinearMap) ∘ₗ
          deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ := by
  let := algebraOfStructureMap f
  let := moduleSheafCohomology f (relativeDifferentialForms f d) d
  have := isScalarTower_sheafCohomology f (relativeDifferentialForms f d) d
  have hrel := eq_comp_deRhamCupK_zero_iff f d hd hι tH
  set β := deRhamTopEquiv f d hd hι
  let αE := AddEquiv.ofBijective (deRhamZeroHyper f)
    (bijective_deRhamZeroHyper f d hdim hd hι tH hH)
  have hT := isPerfPair_smul_of_hodgePairing f d tH hH
  have key := LinearMap.isPerfPair_compr₂_iff_existsUnique_unit (ι := PUnit.{1})
    (A := fun _ => baseRing X.toRingedSpace)
    (B := fun _ => (sheafCohomology f (relativeDifferentialForms f d) d))
    (fun _ => (Algebra.lsmul (A := baseRing X.toRingedSpace) k k
      (sheafCohomology f (relativeDifferentialForms f d) d)).toLinearMap)
    (fun _ g a b => mul_smul g a b)
    (i₀ := PUnit.unit) (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) (fun _ _ => rfl) tH
    (t' ∘ₗ β.symm.toLinearMap) (fun _ => hT)
  constructor
  · intro ht'
    obtain ⟨u, hu, huniq⟩ := key.1 fun _ =>
      isPerfPair_lsmul_compr₂_deRhamTopEquiv_symm f d hdim hd hι tH hH t' (ht' 0 _ (zero_add _))
    refine ⟨u, ⟨αE.symm (u : baseRing X.toRingedSpace), αE.apply_symm_apply _, ?_⟩,
      fun u' ⟨ξ', hξ', ht''⟩ => huniq u' ?_⟩
    · refine (hrel _ t').2 ?_
      rwa [show deRhamZeroHyper f (αE.symm (u : baseRing X.toRingedSpace)) = u from
        αE.apply_symm_apply _]
    · have := (hrel ξ' t').1 ht''
      rwa [hξ'] at this
  · rintro ⟨u, ⟨ξ, hξ, ht''⟩, -⟩
    have hs := (hrel ξ t').1 ht''
    rw [hξ] at hs
    set tH' := tH ∘ₗ cohomologySMul f (relativeDifferentialForms f d) d u
    have htH' : t' = tH' ∘ₗ β.toLinearMap := (β.comp_toLinearMap_symm_eq _ _).1 hs
    have hH' : ∀ p q : ℤ, (hodgePairing f d tH' p q).IsPerfPair := by
      refine (hHu tH').2 ⟨u, rfl, fun u' hu' => Units.ext ?_⟩
      have := hT
      exact (LinearMap.IsPerfPair.bijective_left
        ((Algebra.lsmul (A := baseRing X.toRingedSpace) k k
          (sheafCohomology f (relativeDifferentialForms f d) d)).toLinearMap.compr₂
          tH)).1 (LinearMap.ext fun w => (LinearMap.congr_fun hu' w).symm)
    intro i j hij
    rw [htH']
    exact isPerfPair_deRhamCupK f d hdim hd hι tH' hH' i j hij

end Duality


/-! ### De Rham cohomology over `k` -/

/-- **De Rham cohomology `Hⁿ_{dR}(X/k)` as a `k`-vector space**: the `H⁰(Spec k, 𝒪)`-module of
[Stacks, Tag 0FL6], read over `k` along `k ≅ H⁰(Spec k, 𝒪)`. -/
abbrev deRhamCohomologyOverField (n : ℤ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (.of k)).inv.hom).obj
    (f.deRhamCohomologyBaseModule n)

/-- De Rham cohomology is the hypercohomology of the de Rham complex, `k`-linearly. -/
def deRhamHyperEquiv (n : ℤ) :
    hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f) n ≃ₗ[k]
      deRhamCohomologyOverField f n where
  toFun := (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras f)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) n).hom.hom
  invFun := (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras f)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) n).inv.hom
  map_add' := map_add _
  map_smul' c x := (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras f)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) n).hom.hom.map_smul (deRhamCoeff f c) x
  left_inv x := ConcreteCategory.congr_hom (SheafOfModules.hypercohomologyIsoDeRhamCohomology
    (deRhamAlgebras f) (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) n).hom_inv_id x
  right_inv x := ConcreteCategory.congr_hom (SheafOfModules.hypercohomologyIsoDeRhamCohomology
    (deRhamAlgebras f) (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) n).inv_hom_id x

/-- **The cup product of de Rham cohomology** `Hⁱ_{dR}(X/k) × Hʲ_{dR}(X/k) ⟶ Hⁿ_{dR}(X/k)`,
`i + j = n`, of Section 0FM3 (`AlgebraicGeometry.Scheme.Hom.deRhamCup`), as a `k`-bilinear map. -/
def deRhamCupBilinear (i j n : ℤ) (h : i + j = n) :
    deRhamCohomologyOverField f i →ₗ[k] deRhamCohomologyOverField f j →ₗ[k]
      deRhamCohomologyOverField f n :=
  ((deRhamCupK f i j n h).compl₁₂ (deRhamHyperEquiv f i).symm.toLinearMap
    (deRhamHyperEquiv f j).symm.toLinearMap).compr₂ (deRhamHyperEquiv f n).toLinearMap

/-- `deRhamCupBilinear` evaluates to the cup product `deRhamCup` of de Rham cohomology. -/
theorem deRhamCupBilinear_apply (i j n : ℤ) (h : i + j = n) (x : deRhamCohomologyOverField f i)
    (y : deRhamCohomologyOverField f j) :
    deRhamCupBilinear f i j n h x y = f.deRhamCup i j n h x y := by
  unfold deRhamCupBilinear deRhamCup SheafOfModules.deRhamCechCup
  rfl

/-- **`H⁰_{dR}(X/k) ⟶ H⁰(X, 𝒪_X)`**, induced by the map of complexes `Ω^•_{X/k} ⟶ 𝒪_X[0]`. -/
def deRhamCohomologyZeroToSections : deRhamCohomologyOverField f 0 →+ Γ(X, ⊤) :=
  (deRhamZeroHyper f).comp (deRhamHyperEquiv f 0).symm.toLinearMap.toAddMonoidHom

/-! ### Poincaré duality -/

section Main

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- The terms of the de Rham complex of a morphism smooth of relative dimension `d` vanish above
degree `d`. -/
theorem isZero_deRhamPlus_X_of_lt (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℤ)
    (hn : (d : ℤ) < n) : IsZero ((deRhamPlus f).obj.X n) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
  rw [deRhamPlus_X]
  exact Functor.map_isZero _ (isZero_relativeDifferentialForms_of_lt f d m hn)

/-- For `X` smooth and proper over `k` and equidimensional of dimension `d`, the inclusion
`Ωᵈ[-d] ⟶ σ^{≤d}Ω^•` is bijective on `H^{2d}`. -/
private theorem bijective_truncLEι_of_equidimensional [IsProper f] [Smooth f] (d : ℕ)
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = d) :
    Function.Bijective (hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)) := by
  have := smoothOfRelativeDimension_of_equidimensional k f hequi d hdim
  have : IsNoetherian X :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k f
  exact bijective_hypercohomologyMap_truncLEι_deRham f d hdim.le fun e he => by
    subst he
    exact rightDerived_map_deRham_d_eq_zero_of_isProper_of_smooth f hequi (e + 1) hdim

variable [IsProper f] [Smooth f] [Nonempty X] (d : ℕ) (hequi : TopologicalSpace.Equidimensional X)
  (hdim : topologicalKrullDim X = d)

include hequi hdim in
/-- **Poincaré duality, in hypercohomology**: the hypotheses of the inputs are discharged — the
vanishing of the forms above degree `d`, Grothendieck vanishing ([Stacks, Tag 02UZ]), the
vanishing of the top differential on `Hᵈ` ([Stacks, Tag 0FW6]) and Hodge duality
([Stacks, Tag 0FW4]). -/
theorem deRhamPoincareDualityHyper :
    ∃ t : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f)
        ((d : ℤ) + d) →ₗ[k] k,
      (∀ (i j : ℤ) (hij : i + j = (d : ℤ) + d),
        ((deRhamCupK f i j ((d : ℤ) + d) hij).compr₂ t).IsPerfPair) ∧
      ∀ t' : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f)
          ((d : ℤ) + d) →ₗ[k] k,
        (∀ (i j : ℤ) (hij : i + j = (d : ℤ) + d),
          ((deRhamCupK f i j ((d : ℤ) + d) hij).compr₂ t').IsPerfPair) ↔
          ∃! u : (Γ(X, ⊤))ˣ, ∃ ξ : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
        (deRhamPlus f) 0,
            deRhamZeroHyper f ξ = u ∧
              t' = t ∘ₗ deRhamCupK f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ := by
  have := smoothOfRelativeDimension_of_equidimensional k f hequi d hdim
  have : IsNoetherian X :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k f
  have hd := isZero_deRhamPlus_X_of_lt f d
  have hι := bijective_truncLEι_of_equidimensional f d hequi hdim
  obtain ⟨tH, hH, hHu⟩ := hodgeDuality f d hequi hdim
  exact ⟨tH ∘ₗ (deRhamTopEquiv f d hd hι).toLinearMap,
    isPerfPair_deRhamCupK f d hdim.le hd hι tH hH,
    isPerfPair_deRhamCupK_iff f d hdim.le hd hι tH hH hHu⟩

include hequi hdim in
/-- **`H⁰_{dR}(X/k) = H⁰(X, 𝒪_X)`** for `X` nonempty, smooth and proper over `k` and
equidimensional: the map induced by `Ω^•_{X/k} ⟶ 𝒪_X[0]` is bijective. -/
theorem bijective_deRhamCohomologyZeroToSections :
    Function.Bijective (deRhamCohomologyZeroToSections f) := by
  have := smoothOfRelativeDimension_of_equidimensional k f hequi d hdim
  have : IsNoetherian X :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k f
  have hι := bijective_truncLEι_of_equidimensional f d hequi hdim
  obtain ⟨tH, hH, -⟩ := hodgeDuality f d hequi hdim
  exact (bijective_deRhamZeroHyper f d hdim.le (isZero_deRhamPlus_X_of_lt f d) hι tH hH).comp
    (deRhamHyperEquiv f 0).symm.bijective

include hequi hdim in
/-- **[Stacks, Tag 0FW7], for `X` with affine diagonal.** See `deRhamPoincareDuality`. -/
theorem deRhamPoincareDuality_of_isAffineHom :
    ∃ t : deRhamCohomologyOverField f ((d : ℤ) + d) →ₗ[k] k,
      (∀ i : ℤ, ((deRhamCupBilinear f i ((d : ℤ) + d - i) ((d : ℤ) + d) (by ring)).compr₂
        t).IsPerfPair) ∧
      ∀ t' : deRhamCohomologyOverField f ((d : ℤ) + d) →ₗ[k] k,
        (∀ i : ℤ, ((deRhamCupBilinear f i ((d : ℤ) + d - i) ((d : ℤ) + d) (by ring)).compr₂
          t').IsPerfPair) ↔
          ∃! u : (Γ(X, ⊤))ˣ, ∃ ξ : deRhamCohomologyOverField f 0,
            deRhamCohomologyZeroToSections f ξ = u ∧
              t' = t ∘ₗ deRhamCupBilinear f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ := by
  obtain ⟨tK, hP, hU⟩ := deRhamPoincareDualityHyper f d hequi hdim
  set E := deRhamHyperEquiv f ((d : ℤ) + d)
  have htr : ∀ (t₀ : deRhamCohomologyOverField f ((d : ℤ) + d) →ₗ[k] k) (i j : ℤ)
      (hij : i + j = (d : ℤ) + d),
      ((deRhamCupBilinear f i j ((d : ℤ) + d) hij).compr₂ t₀).IsPerfPair ↔
        ((deRhamCupK f i j ((d : ℤ) + d) hij).compr₂ (t₀ ∘ₗ E.toLinearMap)).IsPerfPair :=
    fun t₀ i j hij =>
      ⟨LinearMap.isPerfPair_of_linearEquiv _ _ (deRhamHyperEquiv f i) (deRhamHyperEquiv f j)
        (fun a b => by simp [deRhamCupBilinear, E]),
      LinearMap.isPerfPair_of_linearEquiv _ _ (deRhamHyperEquiv f i).symm
        (deRhamHyperEquiv f j).symm (fun a b => rfl)⟩
  have hall : ∀ t₀ : deRhamCohomologyOverField f ((d : ℤ) + d) →ₗ[k] k,
      (∀ i : ℤ, ((deRhamCupBilinear f i ((d : ℤ) + d - i) ((d : ℤ) + d) (by ring)).compr₂
        t₀).IsPerfPair) ↔
      ∀ (i j : ℤ) (hij : i + j = (d : ℤ) + d),
        ((deRhamCupK f i j ((d : ℤ) + d) hij).compr₂ (t₀ ∘ₗ E.toLinearMap)).IsPerfPair :=
    fun t₀ => ⟨fun h i j hij => by
      obtain rfl : j = (d : ℤ) + d - i := by omega
      exact (htr t₀ i _ hij).1 (h i), fun h i => (htr t₀ i _ _).2 (h i _ _)⟩
  have hEE : (tK ∘ₗ E.symm.toLinearMap) ∘ₗ E.toLinearMap = tK :=
    LinearMap.ext fun η => by simp
  refine ⟨tK ∘ₗ E.symm.toLinearMap, (hall _).2 (by rwa [hEE]), fun t' =>
    (hall t').trans ((hU (t' ∘ₗ E.toLinearMap)).trans (existsUnique_congr fun u => ?_))⟩
  constructor
  · rintro ⟨ξ, hξ, h⟩
    refine ⟨deRhamHyperEquiv f 0 ξ, ?_, LinearMap.ext fun η => ?_⟩
    · exact (congrArg (deRhamZeroHyper f) ((deRhamHyperEquiv f 0).symm_apply_apply ξ)).trans hξ
    · have h' := LinearMap.congr_fun h (E.symm η)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h'
      rw [h']
      simp [deRhamCupBilinear, E]
  · rintro ⟨ξ, hξ, h⟩
    refine ⟨(deRhamHyperEquiv f 0).symm ξ, hξ, LinearMap.ext fun η => ?_⟩
    have h' := LinearMap.congr_fun h (E η)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h'
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h']
    simp [deRhamCupBilinear, E]

end Main

end AffineDiagonal

/-- **Poincaré duality for de Rham cohomology ([Stacks, Tag 0FW7]).** Let `k` be a field and
`X` a nonempty smooth proper scheme over `k`, equidimensional of dimension `d`. There is a
`k`-linear map `t : H^{2d}_{dR}(X/k) ⟶ k` such that for every `i` the pairing
`Hⁱ_{dR}(X/k) × H^{2d-i}_{dR}(X/k) ⟶ k`, `(ξ, ξ') ↦ t(ξ ∪ ξ')` is perfect, and `t` is unique up
to precomposing with multiplication by a unit of `H⁰(X, 𝒪_X)`: a linear map `t'` has the same
property if and only if `t' = t(ξ ∪ -)` for the class `ξ ∈ H⁰_{dR}(X/k)` of a unit `u` of
`H⁰(X, 𝒪_X)` — `H⁰_{dR}(X/k) = H⁰(X, 𝒪_X)` through `Ω^•_{X/k} ⟶ 𝒪_X[0]`
(`bijective_deRhamCohomologyZeroToSections`) — and that unit is unique.

The cup product is that of Section 0FM3 (`AlgebraicGeometry.Scheme.Hom.deRhamCup`, see
`deRhamCupBilinear_apply`), defined for `X` with affine diagonal; a scheme proper over a field
is separated, so it has affine diagonal. -/
@[stacks 0FW7 "for X nonempty smooth proper over a field k, equidimensional of dimension d: \
there is t : H^{2d}_dR(X/k) -> k, unique up to precomposition with multiplication by a unit of \
H^0(X, O_X), such that for all i the pairing H^i_dR(X/k) x H^{2d-i}_dR(X/k) -> k, \
(xi, xi') |-> t(xi cup xi') is perfect"]
theorem deRhamPoincareDuality [IsProper f] [Smooth f] [Nonempty X] (d : ℕ)
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = d) :
    letI := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper f
    ∃ t : deRhamCohomologyOverField f ((d : ℤ) + d) →ₗ[k] k,
      (∀ i : ℤ, ((deRhamCupBilinear f i ((d : ℤ) + d - i) ((d : ℤ) + d) (by ring)).compr₂
        t).IsPerfPair) ∧
      ∀ t' : deRhamCohomologyOverField f ((d : ℤ) + d) →ₗ[k] k,
        (∀ i : ℤ, ((deRhamCupBilinear f i ((d : ℤ) + d - i) ((d : ℤ) + d) (by ring)).compr₂
          t').IsPerfPair) ↔
          ∃! u : (Γ(X, ⊤))ˣ, ∃ ξ : deRhamCohomologyOverField f 0,
            deRhamCohomologyZeroToSections f ξ = u ∧
              t' = t ∘ₗ deRhamCupBilinear f 0 ((d : ℤ) + d) ((d : ℤ) + d) (zero_add _) ξ :=
  let := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper f
  deRhamPoincareDuality_of_isAffineHom f d hequi hdim

end AlgebraicGeometry.Scheme.Hom

end
