module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtExteriorPower
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafFromStructureSheaf

/-!
# Degree zero of the exterior-power description of self-Ext

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals `𝓘`, let `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. The
exterior-power description of the self-Ext sheaves of `O_X` asserts that composition induces
isomorphisms

`⋀ⁱ_{O_X}(Ext¹_{O♯}(O_X, O_X)) ⟶ Extⁱ_{O♯}(O_X, O_X)`

for every `i`. This file proves the case `i = 0`, where both sides are `O_X`.

They are `O_X` for different reasons. On the left, the zeroth exterior power of a sheaf of
modules is the free rank-one sheaf of modules over the ring it is taken over, and here that ring
is `O_X`, not `O♯`: exterior powers over a ring and over a quotient of it agree in positive
degrees but not in degree zero, where one is `O♯` and the other `O_X`. On the right, the Hom
complex out of the Koszul complex into `O_X` has vanishing differential, so the zeroth Ext sheaf
is the internal Hom sheaf out of the zeroth Koszul term `⋀⁰((O♯)ʳ) = O♯`, and the internal Hom
sheaf out of the structure sheaf is its target. Both sides are therefore `O_X`, and the
comparison identifies them.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.extZeroIsoQuotient`: **the zeroth self-Ext sheaf of
  `O_X` is `O_X`**, `Ext⁰_{O♯}(O_X, O_X) ≅ O_X`.
* `Stacks.RegularSequence.KoszulChainData.extExteriorPowerZeroIsoUnit`: the zeroth exterior power
  of the first Ext sheaf is the free rank-one sheaf of modules over `O_X`, and
  `Stacks.RegularSequence.KoszulChainData.restrictUnitIsoExteriorPowerZero` is that
  identification carried along restriction of scalars.
* `Stacks.RegularSequence.KoszulChainData.extZeroIsoRestrictUnit`: the zeroth Ext sheaf is the
  restriction of scalars of the free rank-one sheaf of modules over `O_X`, the step which crosses
  the two rings.
* `Stacks.RegularSequence.KoszulChainData.extZeroIsoExteriorPowerZero` and its inverse
  `Stacks.RegularSequence.KoszulChainData.extExteriorPowerZeroIsoExtZero`: **degree zero of the
  exterior-power description** — the zeroth exterior power of the first Ext sheaf over `O_X` and
  the zeroth self-Ext sheaf of `O_X` are the same sheaf of `O♯`-modules.
* `Stacks.RegularSequence.KoszulChainData.extExteriorPowerZeroIsoExtDescendedZero`: the same
  comparison with the Ext sheaf in the descended form, as the restriction of scalars of a sheaf
  of `O_X`-modules.

## Implementation notes

**Where the two `O_X`'s come from, and why they have to be compared and not identified.** The
left-hand side is the zeroth exterior power over `O_X` of a sheaf of `O_X`-modules; the
right-hand side is a sheaf of `O♯`-modules. So the comparison is stated after restriction of
scalars along the quotient map, and the step that crosses the two rings is
`Stacks.Sites.cokernelIsoQuotientRingOfHom`: it identifies the cokernel of `φ`, which is the
quotient as a sheaf of `O♯`-modules, with the restriction of scalars of the free rank-one sheaf
of modules over the quotient *ring* sheaf, which is what a zeroth exterior power over `O_X`
produces.

**The zeroth Ext sheaf is not computed through a degree-zero comparison of derived Ext with the
internal Hom.** No such comparison is available: it would say that the zeroth cohomology sheaf
of a derived internal Hom of two sheaves placed in degree zero is their internal Hom sheaf.
It is also not needed here, because the Koszul Hom complex has vanishing differential, so
`Stacks.RegularSequence.KoszulChainData.extIsoInternalHomExteriorPower` already computes *every*
Ext sheaf as an internal Hom sheaf, degree zero included; what degree zero then needs is only
that the internal Hom sheaf out of the structure sheaf is its target.

**The types are left to be inferred,** as elsewhere in this development: writing them out would
make the elaborator compare a hand-written copy of the quotient ring sheaf with the inferred
one, and that unfolds to a sheafification. One consequence is that the structure sheaf has to be
named in `Stacks.Sites.idealOfHom` and `Stacks.Sites.cokernelIsoQuotientRingOfHom`, whose
statements spell it `Stacks.SheafOfModules.Tensor.ringSheaf` while the Koszul
development spells it `CategoryTheory.Sheaf.toRingCat`: with no expected type to propagate, the
two spellings leave the sheaf of commutative rings undetermined, and the comparison below is
assembled from pieces whose types are inferred rather than demanded. The two spellings do agree
once the sheaf is named, so the composites go through unchanged.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}

/-- **The zeroth self-Ext sheaf of `O♯/𝓘` is `O♯/𝓘` itself:**

`Ext⁰_{O♯}(O♯/𝓘, O♯/𝓘) ≅ O♯/𝓘`.

The Hom complex out of the Koszul complex into the quotient has vanishing differential, so the
zeroth Ext sheaf is the internal Hom sheaf out of the zeroth exterior power of `(O♯)ʳ`; that
exterior power is the structure sheaf, and the internal Hom sheaf out of the structure sheaf is
its target. -/
def extZeroIsoQuotient (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] :=
  extIsoInternalHomExteriorPower Rc K 0 ≪≫
    internalHomSheafIsoOfIsoUnit Rc (quotient Rc (φ := φ)) A.exteriorPieceZeroIsoUnit

/-- **The zeroth exterior power of the first Ext sheaf is the free rank-one sheaf of modules over
`O_X`.** Degree zero of the exterior algebra is the ring the algebra is taken over, and here that
ring is `O_X`. -/
def extExteriorPowerZeroIsoUnit (K : KoszulChainData.{u, u, u} A φ)
    [QuasiIso K.augmentation] :=
  (extExteriorAlgebra Rc K).exteriorPieceZeroIsoUnit

/-- **The zeroth self-Ext sheaf of `O_X` is the zeroth exterior power of the first one.** The
zeroth Ext sheaf is `O_X`, which is the cokernel of `φ`; the cokernel of `φ` is the restriction
of scalars of the free rank-one sheaf of modules over the quotient ring sheaf, by the comparison
of the two quotients a sheaf of ideals carries; and that free rank-one sheaf of modules is the
zeroth exterior power over `O_X`. -/
def extZeroIsoRestrictUnit (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] :=
  extZeroIsoQuotient Rc K ≪≫ cokernelIsoQuotientRingOfHom (O := Rc) φ

/-- **The free rank-one sheaf of modules over `O_X`, read over `O♯`, is the zeroth exterior power
of the first Ext sheaf.** This is the previous identification of degree zero of an exterior
algebra, carried along restriction of scalars. -/
def restrictUnitIsoExteriorPowerZero (K : KoszulChainData.{u, u, u} A φ)
    [QuasiIso K.augmentation] :=
  ((SheafOfModules.restrictScalars (quotientRingHom (idealOfHom (O := Rc) φ))).mapIso
    (extExteriorPowerZeroIsoUnit Rc K)).symm

/-- **The zeroth self-Ext sheaf of `O_X` is the zeroth exterior power of the first one**, read as
sheaves of `O♯`-modules. -/
def extZeroIsoExteriorPowerZero (K : KoszulChainData.{u, u, u} A φ)
    [QuasiIso K.augmentation] :=
  extZeroIsoRestrictUnit Rc K ≪≫ restrictUnitIsoExteriorPowerZero Rc K

/-- **Degree zero of the exterior-power description of self-Ext.** The zeroth exterior power of
the first Ext sheaf, formed over `O_X = O♯/𝓘`, and the zeroth self-Ext sheaf of `O_X` are the
same sheaf of `O♯`-modules:

`⋀⁰_{O_X}(Ext¹_{O♯}(O_X, O_X)) ≅ Ext⁰_{O♯}(O_X, O_X)`,

the left side read as a sheaf of `O♯`-modules by restriction of scalars along the quotient map.

The zeroth exterior power over `O_X` is the free rank-one sheaf of modules over `O_X`; its
restriction of scalars is the cokernel of `φ`, by the comparison of the two quotients a sheaf of
ideals carries; and the cokernel of `φ` is the zeroth Ext sheaf. -/
def extExteriorPowerZeroIsoExtZero (K : KoszulChainData.{u, u, u} A φ)
    [QuasiIso K.augmentation] :=
  (extZeroIsoExteriorPowerZero Rc K).symm

/-- **Degree zero of the exterior-power description, with the Ext sheaf in its descended form.**
The zeroth Ext sheaf is the restriction of scalars of a sheaf of `O_X`-modules, and this is the
degree-zero comparison read against that form — the shape in which the comparison is stated in
every degree. -/
def extExteriorPowerZeroIsoExtDescendedZero (K : KoszulChainData.{u, u, u} A φ)
    [QuasiIso K.augmentation] :=
  extExteriorPowerZeroIsoExtZero Rc K ≪≫ (extDescendedIso Rc K 0).symm

end Stacks.RegularSequence.KoszulChainData

end
