module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.ComparisonToDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProduct

/-!
# The Čech cup product at module coefficients, linear over the ring of sections

Let `X` be a space carrying a sheaf `𝒪_X` of commutative rings, let `V` be an open subset and
put `A = 𝒪_X(V)`.  The Čech complex of a cover `U` of `V`, taken in the slice over `V`, is a
complex of `A`-modules, and this file instantiates the cup product of
`Stacks.Cech.LinearCupProduct` at those coefficients: for complexes `K` and `L` of sheaves of
`𝒪_X`-modules and a pairing `D` of their coefficients into a complex `M`, a morphism of
complexes of `A`-modules

`Tot(Tot(Č(U,K)) ⊗_A Tot(Č(U,L))) ⟶ Tot(Č(U,M))`

given on homogeneous pure tensors by the front/back restriction formula with the
Alexander--Whitney sign. The source tensors over the ring `A`, while the pairing `D` need not be
a tensor product over `A`.

## Main definitions

* `Stacks.Cech.ModuleCupProduct.sectionCommRing`: the commutative ring structure on `A`.
* `Stacks.Cech.ModuleCupProduct.sectionsFunctor`: a sheaf of `𝒪_X`-modules as a presheaf of
  `A`-modules on the opens over `V`.
* `Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA`: the total Čech complex of a complex of
  sheaves of `𝒪_X`-modules, as a complex of `A`-modules.
* `Stacks.Cech.ModuleCupProduct.cechCupProductA`: the signed Alexander--Whitney map at these
  coefficients.

## Main results

* `Stacks.Cech.ModuleCupProduct.cechCochains_eq`,
  `Stacks.Cech.ModuleCupProduct.cechComplexFunctorInt_eq`: the Čech complex used here is, on the
  nose, the module-valued Čech complex `Stacks.Cohomology.CechDerived.cechComplexIntFunctor` of
  [Stacks, Tag 01EQ].
* `Stacks.Cech.ModuleCupProduct.sectionCommRing_toRing`: the commutative ring structure on `A`
  refines the `Ring` structure carried by `RingCat` definitionally.
* `Stacks.Cech.ModuleCupProduct.cechCupProductA_eq`: the cup product is the generic one of
  `Stacks.Cech.LinearCupProduct`.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.LinearCupProduct

universe u

namespace Stacks.Cech.ModuleCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (V : Opens X)

/-- **The ring of sections on `V` is commutative**, with the commutative ring structure of
`O(V)`. -/
@[instance_reducible]
instance (priority := low) sectionCommRing : CommRing (SectionRing (ringSheaf O) V) :=
  show CommRing (O.obj.obj (op V)) from inferInstance

/-- The commutative ring structure on sections refines the `Ring` structure carried by
`RingCat` definitionally. -/
theorem sectionCommRing_toRing :
    (sectionCommRing O V).toRing = (inferInstance : Ring (SectionRing (ringSheaf O) V)) :=
  rfl

/-- Sheaves of `𝒪_X`-modules. -/
abbrev Modules := SheafOfModules.{u} (ringSheaf O)

/-- The ring of coefficients `A = 𝒪_X(V)`. -/
abbrev CoeffRing : Type u := SectionRing (ringSheaf O) V

/-- **Restriction to the opens over `V`**, read as presheaves of `A`-modules. -/
noncomputable abbrev sectionsFunctor :
    Modules O ⥤ PresheafModules.{u} (Over V) (CoeffRing O V) :=
  sectionsPresheafFunctor.{u, u, u} (R := ringSheaf O) V

/-- Restriction to the opens over `V`, on complexes. -/
noncomputable abbrev sectionsComplexFunctor :
    CochainComplex (Modules O) ℤ ⥤
      CochainComplex (PresheafModules.{u} (Over V) (CoeffRing O V)) ℤ :=
  haveI : (sectionsFunctor O V).PreservesZeroMorphisms :=
    Stacks.Cohomology.CechDerived.preservesZeroMorphisms_sectionsPresheafFunctor.{u}
      (ringSheaf O) V
  (sectionsFunctor O V).mapHomologicalComplex (up ℤ)

variable {ι : Type u} (U : ι → Opens X) (hU : V = ⨆ i, U i)

/-! ### Agreement with the module-valued Čech complex -/

/-- The generic Čech cochains of the sections presheaf are the module-valued Čech cochains of
[Stacks, Tag 01EP], on the nose. -/
theorem cechCochains_eq (F : Modules O) (p : ℕ) :
    cechCochains (coverObject U hU) (CoeffRing O V) ((sectionsFunctor O V).obj F) p =
      ((Stacks.Cohomology.CechDerived.cechComplexNatFunctor
        (ringSheaf O) V U hU).obj F).X p :=
  rfl

/-- The generic integer-indexed Čech complex of the sections presheaf is the module-valued one
of [Stacks, Tag 01EQ], on the nose. -/
theorem cechComplexFunctorInt_eq :
    sectionsFunctor O V ⋙ cechComplexFunctorInt (coverObject U hU) (CoeffRing O V) =
      Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) V U hU :=
  rfl

/-! ### The total Čech complex over the ring of sections -/

/-- **The total Čech complex of a complex of sheaves of `𝒪_X`-modules**, retaining its module
structure over `A = 𝒪_X(V)`: the totalization of the module-valued Čech bicomplex, with the
Čech degree first. -/
noncomputable abbrev totalCechComplexFunctorA :
    CochainComplex (Modules O) ℤ ⥤ CochainComplex (ModuleCat.{u} (CoeffRing O V)) ℤ :=
  sectionsComplexFunctor O V ⋙ totalCechComplexFunctor (coverObject U hU) (CoeffRing O V)

/-! ### The cup product -/

variable {K L M : CochainComplex (Modules O) ℤ}

/-- **The Čech cup product at `𝒪_X`-module coefficients.** The signed Alexander--Whitney
cup-product map

`Tot(Tot(Č(U,K)) ⊗_A Tot(Č(U,L))) ⟶ Tot(Č(U,M))`

for `A = 𝒪_X(V)`, attached to a pairing `D` of the coefficient sections presheaves into those
of `M`. On a homogeneous summand it is the front/back restriction formula with the
Alexander--Whitney sign `cupProductSign n p r = (-1)^((p+r)n+rp+r)`. -/
@[stacks 07MB "at 𝒪_X-module coefficients over the ring of sections"]
noncomputable abbrev cechCupProductA
    (D : ComplexPairing (CoeffRing O V) ((sectionsComplexFunctor O V).obj K)
      ((sectionsComplexFunctor O V).obj L) ((sectionsComplexFunctor O V).obj M)) :=
  cechCupProduct (coverObject U hU) (CoeffRing O V) D

/-- The cup product at `𝒪_X`-module coefficients is the generic cup product of
`Stacks.Cech.LinearCupProduct` read at the cover in the slice over `V` and at the base ring
`A = 𝒪_X(V)`. -/
theorem cechCupProductA_eq
    (D : ComplexPairing (CoeffRing O V) ((sectionsComplexFunctor O V).obj K)
      ((sectionsComplexFunctor O V).obj L) ((sectionsComplexFunctor O V).obj M)) :
    cechCupProductA O V U hU D = cechCupProduct (coverObject U hU) (CoeffRing O V) D :=
  rfl

end Stacks.Cech.ModuleCupProduct

end
