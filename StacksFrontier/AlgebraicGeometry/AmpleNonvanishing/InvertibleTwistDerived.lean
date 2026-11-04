module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# Twisting a complex by an invertible module: the derived twist is the termwise twist

Let `X` be a scheme and `L` an invertible `𝒪_X`-module. This file proves that the derived
tensor product of an arbitrary object of `D(𝒪_X)` with `L` placed in degree zero is computed by
the *termwise* twist `p ↦ K^p ⊗_{𝒪_X} L`.

This is one input to the derived-category statement of [Stacks, Tag 0BQR], whose argument runs
over a complex of quasi-coherent modules twisted by a power of an ample invertible module; see
the "What is not done" section of
`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/TwistedSectionChart.lean` for what is still
missing there, and
`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/QuasicoherentComplexRepresentative.lean` for
the presentation of an object of `D_QCoh(𝒪_X)` by a complex of quasi-coherent modules.

## Main results

* `Stacks.AmpleNonvanishing.isFlat_of_isInvertibleModule`: **an invertible `𝒪_X`-module on a
  scheme is flat.** This is `Stacks.SheafOfModules.isFlat_of_isInvertible`, which is stated for
  a ringed space, read at the scheme spelling of the sheaf condition on the structure presheaf
  of rings.
* `Stacks.AmpleNonvanishing.isFlat_tensorPowModule`: every integer tensor power of an invertible
  `𝒪_X`-module is flat.
* `Stacks.AmpleNonvanishing.kFlat_single_of_isInvertibleModule`: an invertible `𝒪_X`-module
  placed in degree zero is a K-flat complex, by the base case of [Stacks, Tag 06YQ].
* `Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleIso`:
  `K ⊗^𝐋_{𝒪_X} L[0] ≅ Q(Tot(K ⊗_{𝒪_X} L[0]))` for every complex `K`, with **no flatness
  hypothesis on `K`** — the right-hand factor alone is K-flat, which is what the one-sided
  comparison field of the derived tensor product of [Stacks, Tag 06YU] needs.
* `Stacks.AmpleNonvanishing.totalTensorSingleIso`: the total tensor complex against a module in
  degree zero is the termwise twist.

Composing the last two gives `K ⊗^𝐋_{𝒪_X} L[0] ≅ Q(p ↦ K^p ⊗_{𝒪_X} L)`; the composition is
left to the consumer, who must choose which of the two spellings of the category of
`𝒪_X`-modules the derived category on the right is taken at (see the implementation notes).

## Implementation notes

**Why the flatness statement is a one-liner and was nevertheless missing.** The sheaf condition
on the structure presheaf of rings enters the *type* of the invertibility predicate, through
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, and the ringed-space development
supplies it as `(structureSheafRing X).property` while the ample cluster supplies it as
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X`. Both are proofs of the same `Prop`,
so proof irrelevance makes the two types definitionally equal and the transfer costs nothing;
what was missing was the statement, not an argument. The repository records the absence twice —
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackOpenInCoherentStack.lean` carries "an invertible
module is flat over the base" as a declared hypothesis rather than proving it, and the
derived-twist step of
`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/TwistedSectionChart.lean` was blocked on it.
(That algebraic-space hypothesis is *not* discharged here: it asks for flatness of a module
*over a base along a morphism*, a different predicate.)

**Instance spellings.** `(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive` and the
existence of the total tensor complex are seated at `C := Opens X.carrier` in
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback`, for `X` a *ringed space*; they are not
found at `X.sheaf` for `X` a scheme, because matching the tensor bifunctor against `X.sheaf`
leaves the universe constraint `max u v = u` with both sides unknown. Every statement below
that mentions the bifunctor therefore spells it `X.toRingedSpace.sheaf`, and
`StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace` is imported for those instances.
This is also why the presentation of an object of `D_QCoh(𝒪_X)` by a complex of quasi-coherent
modules lives in a separate module: importing
`StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDiagonalEquivalence` alongside this file puts
enough further instances in scope that the search for the additivity of the tensor bifunctor at
`X.toRingedSpace.sheaf` no longer terminates.

**Why `comparisonRight` and not `comparison`.** `Stacks.Duality.derivedTensorIsoQTensorComplex`
needs K-flat representatives of *both* arguments, and the complex of quasi-coherent modules
produced by [Stacks, Tag 08DB] is not K-flat. The `comparisonRight` field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` asks only for the right factor, which an
invertible module in degree zero supplies.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample

universe u

namespace Stacks.AmpleNonvanishing

/-! ### The tensor bifunctor of a scheme, at the spelling its instances are seated at -/

/-- `⊗_{𝒪_X}` is additive in its first variable, at the scheme spelling of the structure sheaf.
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive` is the same instance
for a ringed space; it is re-seated here because a goal whose subject is written with
`Scheme.toRingedSpace` does not reach it.

The five universes of the bifunctor are written out. Neither of the two module universes is
determined by `X.toRingedSpace.sheaf` or by `Functor.Additive`, and the abelianness of
`SheafOfModules.{max ?left ?right}` that `Functor.Additive` asks for sends instance search after
`HasSheafify` and `GrothendieckTopology.WEqualsLocallyBijective` on the site of opens, where the
unsolved `max ?left ?right =?= u` stops elaboration outright rather than merely failing. The
ringed-space instance this delegates to pins the same five universes for the same reason. -/
instance sheafTensor_additive (X : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.toRingedSpace.sheaf).Additive :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive X.toRingedSpace

/-- `M ⊗_{𝒪_X} -` is additive, at the scheme spelling. -/
instance sheafTensor_obj_additive (X : Scheme.{u})
    (N : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj N).Additive :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive
    X.toRingedSpace N

/-- The total complex of the tensor double complex of two complexes of `𝒪_X`-modules exists, at
the scheme spelling. -/
instance hasMapBifunctor_sheafTensor (X : Scheme.{u})
    (K N : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) ℤ) :
    HomologicalComplex.HasMapBifunctor K N
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) (ComplexShape.up ℤ) :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasMapBifunctor_sheafTensor
    X.toRingedSpace K N

/-! ### Flatness and K-flatness of an invertible module on a scheme -/

/-- **An invertible `𝒪_X`-module on a scheme is flat.** This is
`Stacks.SheafOfModules.isFlat_of_isInvertible` — flatness is stalkwise by [Stacks, Tag 05NE] and
the stalk of an invertible module is an invertible, hence flat, module over the local ring — read
at the spelling of the sheaf condition used by the ample cluster. The two spellings give
definitionally equal types by proof irrelevance. -/
theorem isFlat_of_isInvertibleModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) L :=
  Stacks.SheafOfModules.isFlat_of_isInvertible (X := X.toRingedSpace) L inferInstance

/-- **Every integer tensor power of an invertible `𝒪_X`-module is flat.** The powers of
[Stacks, Tag 01CU] are themselves invertible. -/
theorem isFlat_tensorPowModule (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (tensorPowModule X L n) :=
  isFlat_of_isInvertibleModule X (tensorPowModule X L n)

/-- **An invertible `𝒪_X`-module placed in degree zero is a K-flat complex**, by the base case
`Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat` of [Stacks, Tag 06YQ]. -/
theorem kFlat_single_of_isInvertibleModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] :
    Stacks.Duality.KFlatComplex
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ _
    (isFlat_of_isInvertibleModule X L) 0

/-! ### The derived twist by an invertible module is the termwise twist -/

/-- **The derived tensor product with an invertible module in degree zero is the ordinary total
tensor complex.** No flatness is asked of `K`: the one-sided comparison field of the derived
tensor product of [Stacks, Tag 06YU] needs only the right factor to be K-flat, and an invertible
module in degree zero is. -/
def derivedTensorSingleInvertibleIso (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (K : Stacks.Duality.TensorComplex X) :
    ((Stacks.Duality.derivedTensor X).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L)) ≅
      DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L)) :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonRight K _
    (kFlat_single_of_isInvertibleModule X L)

/-- **The total tensor complex against a module in degree zero is the termwise twist.** The
tensor double complex is concentrated in the row `0`, so its total complex is that row; this is
`CochainComplex.KFlatBifunctor.totalSingleIso` at the tensor product of sheaves of modules. No
invertibility is needed. -/
def totalTensorSingleIso (X : Scheme.{u}) (L : X.Modules)
    (K : Stacks.Duality.TensorComplex X) :
    Stacks.Duality.totalTensorComplex K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L) ≅
      CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) K L :=
  CochainComplex.KFlatBifunctor.totalSingleIso
    (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) K L

end Stacks.AmpleNonvanishing

end
