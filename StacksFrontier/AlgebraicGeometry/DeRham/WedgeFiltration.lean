module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.ImageFiltration
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.WedgeImageSystem
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The wedge filtration of a de Rham complex

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. Stacks Section 50.12 filters the relative de Rham complex
`Ω^•_{X/S}` by the forms pulled back from `Y`: the `k`-th step is

`F^kΩ^•_{X/S} = Im (Tot(f^{-1}σ^{≥k}Ω^•_{Y/S} ⊗_{(f∘g)^{-1}𝒪_S} Ω^•_{X/S}) ⟶ Ω^•_{X/S})`,

the image of the wedge map. Because the pulled-back forms are closed under the de Rham
differential, the source is a complex and the wedge map is a morphism of complexes, so the image
is a subcomplex. The filtration is decreasing, and exhaustive in the strong sense that
`F^kΩ^•_{X/S} = Ω^•_{X/S}` for `k ≤ 0`. It is a filtered complex in the sense of
[Stacks, Tag 012L].

## Main definitions

* `AlgebraicGeometry.SheafOfModules.wedgeImageSystem`: the system of wedge maps out of the
  brutal truncations of `P`, as a `CochainComplex.ImageSystem` over `Ω^•`.
* `AlgebraicGeometry.SheafOfModules.wedgeFiltrationStep` and
  `AlgebraicGeometry.SheafOfModules.wedgeFiltered`: **the filtration** whose `k`-th step is the
  image of the wedge map on the `k`-th brutal truncation of `P`, and the resulting filtered
  complex.

## Main results

* `AlgebraicGeometry.SheafOfModules.wedgeFiltrationStep_antitone`: the steps decrease.
* `AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos`: the filtration is
  exhaustive: its steps in degrees `≤ 0` are the whole complex.

## Implementation notes

`wedgeFiltered` takes any complex `P` of `A`-modules with a morphism `ι : P ⟶ Ω^•` and filters
`Ω^•` by the images of the wedge maps on the brutal truncations of `P`. Section 50.12 is the
instance `P = f^{-1}Ω^•_{Y/S}`, `ι = ρ`, where the morphism of complexes
`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}` of `(f∘g)^{-1}𝒪_S`-modules is a hypothesis. Truncating the
inverse image and taking the inverse image of the truncation agree here: the brutal truncation is
cut out by `⊤` and `⊥`, and an additive functor applied degreewise carries `⊥` to `⊥`, so the two
subcomplexes have the same image in `Ω^•_{X/S}`.

The step at `k ≤ 0` is `⊤` by definition. Section 50.12 posits `F^0Ω^•_{X/S} = Ω^•_{X/S}` as part
of the definition of the filtration, and the image description agrees there, since the
degree-zero summand of the wedge map is `a ⊗ η ↦ ρ(a)·η` and `ρ` is unital.

The ambient complex is the `ℤ`-indexed extension by zero of the `ℕ`-indexed de Rham complex,
`AlgebraicGeometry.SheafOfModules.deRhamComplexInt`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKP](https://stacks.math.columbia.edu/tag/0FKP)
* [Stacks Project, Tag 012L](https://stacks.math.columbia.edu/tag/012L)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe v u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)
/-- Sheaves of modules over the base ring sheaf form an abelian category. -/
local instance abelianModules :
    Abelian (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) :=
  _root_.SheafOfModules.instAbelian _

/-- Sheafification of presheaves of abelian groups exists on the open-cover site of a space:
`Opens space` is small, so `CategoryTheory.hasSheafifyEssentiallySmallSite` applies. -/
local instance hasSheafifyOpens (space : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology space) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- Weak equivalences of presheaves of abelian groups on the open-cover site of a space are the
locally bijective maps. -/
local instance wEqualsLocallyBijectiveOpens (space : TopCat.{u}) :
    (Opens.grothendieckTopology space).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The total complex of the tensor product over `A` of two `ℕ`-indexed cochain complexes of
sheaves of `A`-modules exists: in each total degree only the finitely many pairs `(p, q)` with
`p + q = n` contribute, and the category has finite biproducts. -/
instance hasMapBifunctorNat {space : TopCat.{u}}
    (coefficients : TopCat.Sheaf CommRingCat.{u} space)
    (left right : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf coefficients)) ℕ) :
    HomologicalComplex.HasMapBifunctor
      left right (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} coefficients)
        (ComplexShape.up ℕ) := by
  let : Abelian
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf coefficients)) :=
    _root_.SheafOfModules.instAbelian _
  exact HomologicalComplex₂.hasTotal_of_finite _ _
    (fun degree => Set.Finite.subset
      (Set.Finite.ofFinset (Finset.antidiagonal degree)
        (fun _ => Finset.mem_antidiagonal))
      (fun _ member => member.1))

/-- **The system of wedge maps out of the brutal truncations of `P`**, as a
`CochainComplex.ImageSystem` over `Ω^•`: the `k`-th member is `Tot(σ^{≥k}P ⊗_A Ω^•)` extended by
zero, its morphism into `Ω^•` is the wedge map, and the factorisations are the inclusions
`σ^{≥k'}P ⟶ σ^{≥k}P` tensored with `Ω^•`. It is `CochainComplex.wedgeImageSystem` at the tensor
product over `A` and the wedge product of [Stacks, Tag 0FM2]. -/
def wedgeImageSystem (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) :
    CochainComplex.ImageSystem (deRhamComplexInt B D) := by
  letI : Abelian
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A)) :=
    _root_.SheafOfModules.instAbelian _
  exact CochainComplex.wedgeImageSystem
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A) (wedgeProduct B D) P ι

/-- **The `k`-th step of the wedge filtration of `Ω^•`** determined by `ι : P ⟶ Ω^•`: the image
of the wedge map on the `k`-th brutal truncation of `P` for `k ≥ 1`, and the whole complex for
`k ≤ 0`. -/
def wedgeFiltrationStep
    (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k : ℤ) : Subobject (deRhamComplexInt B D) :=
  (wedgeImageSystem B D P ι).filtrationStep k

/-- **The wedge filtration is decreasing.** -/
theorem wedgeFiltrationStep_antitone
    (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) : Antitone (wedgeFiltrationStep B D P ι) :=
  (wedgeImageSystem B D P ι).filtrationStep_antitone

/-- **The wedge filtration of `Ω^•` determined by `ι : P ⟶ Ω^•`**, as a filtered complex in the
sense of [Stacks, Tag 012L]. -/
def wedgeFiltered (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) :
    CochainComplex.Filtered (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) :=
  (wedgeImageSystem B D P ι).filtered

/-- The underlying complex of the wedge filtration is `Ω^•`. -/
@[simp]
theorem wedgeFiltered_X
    (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) : (wedgeFiltered B D P ι).X = deRhamComplexInt B D :=
  rfl

/-- The `k`-th subobject of the wedge filtration is `wedgeFiltrationStep B D P ι k`. -/
@[simp]
theorem wedgeFiltered_subobject
    (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k : ℤ) :
    (wedgeFiltered B D P ι).filtration.subobject (op k) = wedgeFiltrationStep B D P ι k :=
  (wedgeImageSystem B D P ι).filtered_subobject k

/-- **The wedge filtration is exhaustive**: in degrees `≤ 0` its steps are the whole complex. -/
theorem isIso_wedgeFiltered_ι_of_nonpos
    (P : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k : ℤ) (hk : k ≤ 0) :
    IsIso ((wedgeFiltered B D P ι).filtration.ι.app (op k)) :=
  (wedgeImageSystem B D P ι).isIso_filtered_ι_of_nonpos hk

end AlgebraicGeometry.SheafOfModules

end
