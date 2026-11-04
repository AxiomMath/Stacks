module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.FormsWedgeDuality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingCupProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomBijectionNatural
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegrees
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotentSplitting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProductLinear

/-!
# The relative cup product pairing on Hodge cohomology

Let `f : X ⟶ S` be a morphism of schemes. The wedge product `Ω^a_{X/S} ⊗ Ω^b_{X/S} ⟶ Ω^{a+b}_{X/S}`
of differential forms, placed in degree zero, gives a morphism

`Ω^a_{X/S} ⊗^L_{𝒪_X} Ω^b_{X/S}[n] ⟶ Ω^{a+b}_{X/S}[n]`

in `D(𝒪_X)`, through the canonical map from the derived to the ordinary tensor product. Composed
with the relative cup product of [Stacks, Tag 0B68] it gives, for every morphism
`t : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S`, the pairing

`Rf_*Ω^p_{X/S} ⊗^L_{𝒪_S} Rf_*Ω^{n-p}_{X/S}[n] ⟶ Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S`

of [Stacks, Tag 0G8I]. A pairing `K ⊗^L L ⟶ 𝒪_S` of perfect complexes is *perfect* when the
map `K ⟶ R𝓗om(L, 𝒪_S)` it determines is an isomorphism; this is the sense in which the proof of
[Stacks, Tag 0G8I] uses the word, the conclusion of [Stacks, Tag 0G81].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formsInDegreeZero`: `Ω^a_{X/S}` placed in degree zero.
* `AlgebraicGeometry.Scheme.Hom.formsDerivedWedge`: the wedge product
  `Ω^a ⊗^L Ω^b ⟶ Ω^{a+b}` in `D(𝒪_X)`.
* `AlgebraicGeometry.Scheme.Hom.formsDerivedWedgeShift`: its shift
  `Ω^a ⊗^L Ω^b[n] ⟶ Ω^c[n]`, for `a + b = c`.
* `AlgebraicGeometry.Scheme.Hom.relativeHodgePairing`: the pairing
  `Rf_*Ω^p ⊗^L Rf_*Ω^q[n] ⟶ 𝒪_S`, for `p + q = n`, determined by `t`.
* `AlgebraicGeometry.IsPerfectDerivedPairing`: a perfect pairing of perfect complexes on `S`.
* `AlgebraicGeometry.Scheme.Hom.formsShiftSMul`: multiplication by `g ∈ Γ(X, 𝒪_X)` on
  `Rf_*Ω^n_{X/S}[n]`.

## Implementation notes

The derived categories are taken at the standard model, the scope
`Stacks.StandardDerivedModel`: the relative cup product
`Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct` is defined only there (it is
stated under `HasDerivedCategory.standard`). The derived tensor product is the canonical one of
[Stacks, Tag 06YU] over which the relative cup product is stated, and `R𝓗om` and the
tensor–internal-Hom bijection are those of
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction`.

## References

* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0G81](https://stacks.math.columbia.edu/tag/0G81)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The sheaf `Ω^a_{X/S}` of relative differential `a`-forms placed in degree zero, as an object of
the derived category of `𝒪_X`-modules. -/
abbrev formsInDegreeZero (a : ℤ) : DerivedCategory X.Modules :=
  DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
    (relativeDifferentialForms f a))

/-- **The wedge product `Ω^a_{X/S} ⊗^L Ω^b_{X/S} ⟶ Ω^{a+b}_{X/S}`** in `D(𝒪_X)`: the canonical map
from the derived tensor product to the total tensor complex of the two single complexes, which is
`Ω^a ⊗ Ω^b` in degree zero, followed by multiplication in the algebra of differential forms. -/
def formsDerivedWedge (a b : ℤ) :
    ((derivedTensorProductFunctor X.sheaf).obj (formsInDegreeZero f a)).obj
        (formsInDegreeZero f b) ⟶ formsInDegreeZero f (a + b) :=
  (canonicalDerivedTensorProduct X.sheaf).toTensor _ _ ≫
    DerivedCategory.Q.map ((HomologicalComplex.mapBifunctorSingleSingleIso _ _ _ 0 0).hom ≫
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) (0 + 0)).map
        ((relativeDifferentialFormsAlgebra f).mulSheaf a b))

/-- **The shifted wedge product `Ω^a_{X/S} ⊗^L Ω^b_{X/S}[n] ⟶ Ω^c_{X/S}[n]`** for `a + b = c`:
the commutation of the derived tensor product with the shift in its second variable
([Stacks, Tag 06YU]) followed by the shift of `formsDerivedWedge`. -/
def formsDerivedWedgeShift (n a b c : ℤ) (h : a + b = c) :
    ((derivedTensorProductFunctor X.sheaf).obj (formsInDegreeZero f a)).obj
        ((formsInDegreeZero f b)⟦n⟧) ⟶ (formsInDegreeZero f c)⟦n⟧ :=
  letI := (canonicalDerivedTensorProduct X.sheaf).commShift_right (formsInDegreeZero f a)
  (((derivedTensorProductFunctor X.sheaf).obj (formsInDegreeZero f a)).commShiftIso n).hom.app
      (formsInDegreeZero f b) ≫
    (formsDerivedWedge f a b ≫ eqToHom (by rw [h]))⟦n⟧'

/-- **The relative cup product pairing on Hodge cohomology determined by `t`**: for `p + q = n`
and `t : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S`, the composite

`Rf_*Ω^p_{X/S} ⊗^L_{𝒪_S} Rf_*Ω^q_{X/S}[n] ⟶ Rf_*(Ω^p_{X/S} ⊗^L Ω^q_{X/S}[n])`
`  ⟶ Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S`

of the relative cup product of [Stacks, Tag 0B68], `Rf_*` of the wedge product and `t`. -/
def relativeHodgePairing (n p q : ℤ) (h : p + q = n)
    (t : (Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) :
    ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).obj
        ((Stacks.Duality.derivedPushforward f).obj (formsInDegreeZero f p))).obj
        ((Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f q)⟦n⟧)) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj :=
  Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom
      (formsInDegreeZero f p) ((formsInDegreeZero f q)⟦n⟧) ≫
    (Stacks.Duality.derivedPushforward f).map (formsDerivedWedgeShift f n p q n h) ≫ t

/-- **Multiplication by a global function `g ∈ Γ(X, 𝒪_X)` on `Rf_*Ω^n_{X/S}[n]`**: `Rf_*` of the
shift of `g` acting on `Ω^n_{X/S}`. -/
def formsShiftSMul (n : ℤ) (g : Γ(X, ⊤)) :
    (Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f n)⟦n⟧) ⟶
      (Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f n)⟦n⟧) :=
  (Stacks.Duality.derivedPushforward f).map
    ((DerivedCategory.Q.map ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map
      (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
        (relativeDifferentialForms f n))))⟦n⟧')

end Scheme.Hom

/-- **The tensor–internal-Hom bijection is natural in the source**, in the direction of the
inverse bijection: precomposing a pairing with `v ⊗ 1` precomposes the map it determines with
`v`. -/
theorem _root_.Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction.homEquiv_symm_map_app_comp
    {C : Type*} [Category* C] {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}
    (DY : Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction T H)
    {A' A B M : C} (v : A' ⟶ A) (φ : (T.obj A).obj B ⟶ M) :
    (DY.homEquiv A' B M).symm ((T.map v).app B ≫ φ) = v ≫ (DY.homEquiv A B M).symm φ :=
  (Equiv.symm_apply_eq _).2 ((DY.homEquiv_naturality_source v _).trans
    (congrArg _ (Equiv.apply_symm_apply _ _))).symm

/-- The type of tensor–internal-Hom adjunctions `− ⊗^L_{𝒪_S} L ⊣ R𝓗om_{𝒪_S}(L, −)` on `D(𝒪_S)`
for the derived tensor product of [Stacks, Tag 06YU]. -/
abbrev DerivedTensorHomAdjunction (S : Scheme.{u}) :=
  Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction
    (derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O)
    (Stacks.SheafOfModules.ringedSite S.sheaf).derivedSheafHomBifunctor

/-- **A perfect pairing of perfect complexes on `S`** with respect to a tensor–internal-Hom
adjunction `DY`: a morphism `φ : K ⊗^L_{𝒪_S} L ⟶ 𝒪_S` with `K` and `L` perfect such that the map
`K ⟶ R𝓗om_{𝒪_S}(L, 𝒪_S)` it determines under `DY` is an isomorphism. -/
def IsPerfectDerivedPairing {S : Scheme.{u}} (DY : DerivedTensorHomAdjunction S)
    {K L : DerivedCategory S.Modules}
    (φ : ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).obj K).obj L ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) : Prop :=
  Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace) K ∧
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace) L ∧
    IsIso ((DY.homEquiv K L (Stacks.Duality.derivedStructureSheafInDegree S 0).obj).symm φ)

namespace RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- **The property of `t : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` in [Stacks, Tag 0G8I]**: for every `p` the
pairing `Rf_*Ω^p_{X/S} ⊗^L Rf_*Ω^{n-p}_{X/S}[n] ⟶ 𝒪_S` given by the relative cup product composed
with `t` is a perfect pairing of perfect complexes on `S`. -/
def IsRelativePoincareTrace
    (t : (Stacks.Duality.derivedPushforward D.f).obj ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) : Prop :=
  ∀ p : ℤ, IsPerfectDerivedPairing
    (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
      (Stacks.SheafOfModules.ringedSite D.S.sheaf))
    (D.f.relativeHodgePairing D.n p (D.n - p) (by ring) t)

end RelativeDualitySituation

end AlgebraicGeometry
