module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.RestrictScalarsCechComputes
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.HypercohomologyBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyDifferentialGradedPairing

/-!
# The cup product on de Rham cohomology, computed by Čech cocycles

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`. The wedge
product makes the relative de Rham complex `Ω^•` a sheaf of differential graded `A`-algebras
(`AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra`, Tag 0FU6), so its
multiplication is a pairing `Ω^• ⊗ Ω^• ⟶ Ω^•` of complexes of sheaves of `A`-modules. Whenever
Čech cohomology computes the hypercohomology of `Ω^•`, the cup product of Cohomology,
Section 01FP — the Čech cup product of representing cocycles, which by
[Stacks, Tag 0FKV] (`Stacks.Cech.CupProductSquare.cupProductSquareCommutes`) is the global cup
product of Section 0FKU — composed with that pairing is the cup product

`∪ : H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}`

of Stacks Section 0FM3, described there as "the cup product of Cohomology, Section 0FKU combined
with the wedge product". The unit is the class of the global section `1` of `Ω⁰ = 𝒪_X`.

For a morphism of schemes `p : X ⟶ S` with `X` of affine diagonal (for instance separated) Čech
cohomology does compute the hypercohomology of `Ω^•_{X/S}`: its terms are quasi-coherent
`𝒪_X`-modules read over `p⁻¹𝒪_S`. This gives the cup product on `H^*_{dR}(X/S)` as an
`H⁰(S, 𝒪_S)`-module, without parameters.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamCechPairing`: the wedge product as a pairing of the de
  Rham complex with itself.
* `AlgebraicGeometry.SheafOfModules.deRhamCechCup`: **the cup product on `H^*_{dR}`**, when Čech
  cohomology computes the hypercohomology of `Ω^•`.
* `AlgebraicGeometry.SheafOfModules.deRhamUnitClass`: the unit `1 ∈ H⁰_{dR}`.
* `AlgebraicGeometry.Scheme.Hom.deRhamCup` and `AlgebraicGeometry.Scheme.Hom.deRhamUnit`: the
  cup product and its unit on `H^*_{dR}(X/S)` for a morphism of schemes with `X` of affine
  diagonal.

## Main results

* `AlgebraicGeometry.Scheme.Hom.cechComputes_deRhamComplexPlus`: Čech cohomology computes the
  hypercohomology of the relative de Rham complex of a scheme of affine diagonal.

## Implementation notes

The library's `AlgebraicGeometry.SheafOfModules.deRhamCupProduct` is stated against a parameter
`AlgebraicGeometry.SheafOfModules.HypercohomologyCupProduct` carrying Section 0FKU together with
Lemmas 0FP4 and 0FP5 for an *arbitrary* multiplication `Tot(Ω^• ⊗ Ω^•) ⟶ Ω^•`. The Čech cup
product constructed here is a genuine cup product, but filling that parameter would require the
graded commutativity of the Čech cup product on cohomology for every such multiplication, which
holds only up to a homotopy not available here; so the product is stated directly.

## References

* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.Hypercohomology

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The relative de Rham differential graded algebra is concentrated in nonnegative degrees. -/
instance isStrictlyGE_deRhamDifferentialGradedAlgebra :
    (_root_.SheafOfModules.DifferentialGradedAlgebra.complex (R := ringSheaf A)
      (deRhamDifferentialGradedAlgebra B D)).IsStrictlyGE 0 :=
  isStrictlyGE_deRhamComplexInt B D

/-- **The wedge product as a pairing of the relative de Rham complex with itself**, the
multiplication of the de Rham differential graded algebra of Tag 0FU6. -/
def deRhamCechPairing :
    Pairing A (deRhamComplexPlus B D) (deRhamComplexPlus B D) (deRhamComplexPlus B D) :=
  differentialGradedPairing (deRhamDifferentialGradedAlgebra B D) 0

/-- **The cup product on relative de Rham cohomology**

`∪ : H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}`,

when Čech cohomology computes the hypercohomology of the de Rham complex: the cup product of
Cohomology, Section 01FP (equivalently Section 0FKU, by Tag 0FKV) composed with the wedge product
of the de Rham differential graded algebra, read on `H^*_{dR}` through the agreement of the two
models of derived global sections. -/
def deRhamCechCup (hK : CechComputes A (deRhamComplexPlus B D)) (i j k : ℤ) (h : i + j = k)
    (x : deRhamCohomology B D i) (y : deRhamCohomology B D j) : deRhamCohomology B D k :=
  (hypercohomologyIsoDeRhamCohomology B D k).hom
    (cup A hK hK (deRhamCechPairing B D) i j k h
      ((hypercohomologyIsoDeRhamCohomology B D i).inv x)
      ((hypercohomologyIsoDeRhamCohomology B D j).inv y))

/-- **The unit `1 ∈ H⁰_{dR}`**: the class of the global section `1` of `Ω⁰ = 𝒪_X`, which is a
closed form. -/
def deRhamUnitClass : deRhamCohomology B D 0 :=
  (hypercohomologyIsoDeRhamCohomology B D 0).hom
    (differentialGradedUnitClass (deRhamDifferentialGradedAlgebra B D) 0)

/-- The cup product is computed in hypercohomology. -/
theorem hypercohomologyIsoDeRhamCohomology_inv_deRhamCechCup
    (hK : CechComputes A (deRhamComplexPlus B D)) (i j k : ℤ) (h : i + j = k)
    (x : deRhamCohomology B D i) (y : deRhamCohomology B D j) :
    (hypercohomologyIsoDeRhamCohomology B D k).inv (deRhamCechCup B D hK i j k h x y) =
      cup A hK hK (deRhamCechPairing B D) i j k h
        ((hypercohomologyIsoDeRhamCohomology B D i).inv x)
        ((hypercohomologyIsoDeRhamCohomology B D j).inv y) := by
  rw [deRhamCechCup, ← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **Čech cohomology computes the cohomology of each term of the relative de Rham complex** of a
morphism of schemes whose source has affine diagonal, read over `p⁻¹𝒪_S`: the term `Ωⁿ_{X/S}` is a
quasi-coherent `𝒪_X`-module read over `p⁻¹𝒪_S`, and the terms in negative degrees vanish. -/
theorem cechComputesSheaf_deRhamComplexInt_X [IsAffineHom (pullback.diagonal (terminal.from X))]
    (q : ℤ) :
    CechComputesSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
      ((SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).X q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have := isQuasicoherent_relativeDifferentialForms p n
    rw [SheafOfModules.deRhamComplexInt_X_of_nonneg _ _ _ (Int.natCast_nonneg n)]
    exact cechComputesSheaf_restrictScalars_of_isQuasicoherent X
      (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
      (relativeDifferentialForms p (n : ℤ))
  · have hz : IsZero ((SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).X q) :=
      (SheafOfModules.deRhamComplex (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).isZero_extend_X embeddingUpNat q
          fun n hn => by
            have : ((n : ℕ) : ℤ) = q := hn
            omega
    refine cechComputes_of_isZero_X _ _ fun k => ?_
    change IsZero (((HomologicalComplex.single _ (up ℤ) 0).obj
      ((SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).X q)).X k)
    by_cases hk : k = 0
    · subst hk
      exact hz.of_iso (HomologicalComplex.singleObjXSelf (up ℤ) 0 _)
    · exact HomologicalComplex.isZero_single_obj_X (up ℤ) 0 _ k hk

/-- **Čech cohomology computes the hypercohomology of the relative de Rham complex** of a morphism
of schemes whose source has affine diagonal. -/
theorem cechComputes_deRhamComplexPlus [IsAffineHom (pullback.diagonal (terminal.from X))] :
    CechComputes ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
      (SheafOfModules.deRhamComplexPlus (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) :=
  cechComputes_of_terms _ _ (cechComputesSheaf_deRhamComplexInt_X p)

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **The cup product on relative de Rham cohomology** `H^*_{dR}(X/S)` of a morphism of schemes
whose source has affine diagonal (Stacks Section 0FM3): the cup product of Cohomology,
Section 0FKU — computed, by Tag 0FKV, by Čech cocycles — composed with the wedge product, an
`H⁰(S, 𝒪_S)`-bilinear map `H^i_{dR}(X/S) × H^j_{dR}(X/S) ⟶ H^k_{dR}(X/S)` for `i + j = k`. -/
def deRhamCup (i j k : ℤ) (h : i + j = k) (x : deRhamCohomologyBaseModule p i)
    (y : deRhamCohomologyBaseModule p j) : deRhamCohomologyBaseModule p k :=
  SheafOfModules.deRhamCechCup (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) (cechComputes_deRhamComplexPlus p) i j
      k h x y

/-- **The unit `1 ∈ H⁰_{dR}(X/S)`**, the class of the global function `1`. -/
def deRhamUnit : deRhamCohomologyBaseModule p 0 :=
  SheafOfModules.deRhamUnitClass (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p))

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **The coefficients of relative de Rham cohomology act on `𝒪_X` through `p`**: the ring map
`H⁰(S, 𝒪_S) ⟶ Γ(X, p⁻¹𝒪_S)` along which `H^*_{dR}(X/S)` is an `H⁰(S, 𝒪_S)`-module, followed by
the structure map `p⁻¹𝒪_S ⟶ 𝒪_X` on global sections, is `p^♯` on global sections. -/
theorem inverseImageGlobalSections_comp_inverseImageStructureMap_app :
    inverseImageGlobalSections p ≫ (inverseImageStructureMap p).hom.app (op ⊤) = p.appTop := by
  have h := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.base).homEquiv_unit
    S.sheaf X.sheaf (inverseImageStructureMap p)).symm.trans
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.base).homEquiv
        S.sheaf X.sheaf).apply_symm_apply _)
  exact congrArg (fun g => g.hom.app (op ⊤)) h

end AlgebraicGeometry.Scheme.Hom

end
