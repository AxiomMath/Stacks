module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBockstein
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

import StacksCore.Tactic.StacksAttribute

/-!
# A K-flat resolution of `I^i/I^{i+1}`

Let `(X, O_X)` be a ringed space and `ι : I ⟶ O_X` an invertible ideal subsheaf.  Tag 0GT9's
right-hand side is the Bockstein complex of Tag 0GT8, whose `i`-th term is the cohomology sheaf
`H^i(M ⊗^L I^i/I^{i+1})` of a **derived** tensor product.  The development's chain-level form,
`Reduction.bocksteinChainComplex`, instead uses the ordinary tensor product `F ⊗ I^i/I^{i+1}`.
Comparing the two needs the derived tensor product to be computed by an ordinary one, and the
lever for that is `DerivedTensorProduct.comparisonRight`: a **K-flat right factor** computes the
derived tensor product against an arbitrary left factor.

The single complex on `I^i/I^{i+1}` is not K-flat — it is a quotient, not an invertible sheaf.
This file supplies the resolution that is: the two-term complex

`[I^{i+1} ⟶ I^i]`

in degrees `-1, 0`, whose terms are integer tensor powers of an invertible sheaf, hence
invertible, hence flat.  A bounded-above complex of flat modules is K-flat (Tag 06YQ), and the
augmentation to the single complex on the cokernel is a quasi-isomorphism because the
differential is a monomorphism.

## Main definitions

* `powerInclSequence`: the short exact sequence `0 → I^{i+1} → I^i → I^i/I^{i+1} → 0`.
* `powerQuotientResolution`: the two-term complex `[I^{i+1} ⟶ I^i]`, realised as the mapping
  cone of `(single 0).map (idealPowerIncl …)` so that Mathlib's short-exact mapping-cone API
  applies to it directly.
* `powerQuotientResolutionAug`: the augmentation
  `powerQuotientResolution ⟶ (single 0).obj (I^i/I^{i+1})`.

## Main results

* `powerInclSequence_shortExact`: the sequence is short exact.  The monomorphy is
  `Bockstein.idealPowerIncl_mono`, which needs invertibility of `I` alone.
* `kFlat_powerQuotientResolution`: **the resolution is K-flat.**  Each term is an integer tensor
  power of `I`, invertible by `Invertible.tensorPower_isInvertible`, flat by
  `isFlat_of_isInvertible`, and the single complex on a flat module is K-flat
  (`KFlatResolution.kFlat_single_of_isFlat`); the mapping cone of a morphism of K-flat complexes
  is K-flat (`kFlat_mappingCone`).
* `quasiIso_powerQuotientResolutionAug`: **the augmentation is a quasi-isomorphism**, so the
  resolution really does resolve `I^i/I^{i+1}`.

## Implementation notes

### Why the mapping cone and not `HomologicalComplex.double`

`[I^{i+1} ⟶ I^i]` is `HomologicalComplex.double (idealPowerIncl …)
ComplexShape.upIntRelNegOneZero`, and `CochainComplex.doubleIsoMappingCone` identifies that with
the mapping cone used here.  The cone is taken as the definition because both results this file
exists to prove are stated about it upstream and need no transport: `kFlat_mappingCone` is about
a cone, and Mathlib's `CochainComplex.mappingCone.quasiIso_descShortComplex` — the augmentation's
quasi-isomorphy — is about the cone of the `f` of a short exact sequence of complexes.  Going
through `double` would mean transporting both along an isomorphism of complexes for no gain.

### The monomorphism at the structure sheaf

`Eta.idealPowerIncl_mono` asks for `I`-torsion-freeness of the module.  At the structure sheaf
that binder has an inhabitant only under a hypothesis on the structure-sheaf stalks
(`Reduction.isIdealTorsionFree_unit` assumes they are local rings), which Situation 0GT4 does not
provide.  `Bockstein.idealPowerIncl_mono` is the form that needs invertibility alone, because at
`𝒪` the transition is the image of the monomorphism `ι` under an equivalence.  It was `private`
until this file needed it.

## References

* [Stacks Project, Tag 0GT8](https://stacks.math.columbia.edu/tag/0GT8)
* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.IdealTorsion.Bockstein

open Stacks.IdealTorsion.Eta
open Stacks.SheafOfModules.Invertible (tensorPower_isInvertible)

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The short exact sequence of a consecutive ideal-power pair -/

/-- The sequence `0 → I^{i+1} → I^i → I^i/I^{i+1} → 0`, as a short complex.  Its third object
is `powerQuotient X I ι i` by definition, that being the cokernel of the transition. -/
public noncomputable abbrev powerInclSequence
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) : ShortComplex (SheafOfModules.{u} Oₓ) :=
  ShortComplex.cokernelSequence (Stacks.IdealTorsion.Eta.idealPowerIncl X I ι i 𝒪)

/-- **The consecutive ideal-power sequence is short exact.**  Epimorphy of the projection is the
cokernel projection; monomorphy of the transition is `idealPowerIncl_mono`, which at the
structure sheaf needs invertibility of `I` and nothing further. -/
public theorem powerInclSequence_shortExact
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) : (powerInclSequence X I ι i).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (idealPowerIncl_mono X I ι i) (inferInstanceAs (Epi (cokernel.π (idealPowerIncl X I ι i 𝒪))))

/-- The same sequence read in complexes, through the degree-`0` single-complex functor.  This is
the short exact sequence whose mapping cone is the resolution. -/
public noncomputable abbrev powerInclSequenceSingle
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) : ShortComplex (CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :=
  (powerInclSequence X I ι i).map
    (HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0)

/-- **The sequence of single complexes is short exact**, the single-complex functor being
exact. -/
public theorem powerInclSequenceSingle_shortExact
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) : (powerInclSequenceSingle X I ι i).ShortExact :=
  (powerInclSequence_shortExact X I ι i).map_of_exact _

/-! ### The resolution -/

/-- **The two-term complex `[I^{i+1} ⟶ I^i]`**, in degrees `-1` and `0`, as the mapping cone of
the transition read in single complexes. -/
public noncomputable abbrev powerQuotientResolution
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) : CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
  CochainComplex.mappingCone (powerInclSequenceSingle X I ι i).f

/-- **An integer ideal power is flat.**  It is invertible by Tag 01CU, and an invertible sheaf of
modules on a ringed space is flat. -/
public theorem isFlat_idealPowerTerm_unit
    (I : SheafOfModules.{u} Oₓ) (_ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (Stacks.IdealTorsion.Eta.idealPowerTerm X I i 𝒪) :=
  Stacks.SheafOfModules.isFlat_of_isInvertible _
    (tensorPower_isInvertible X.sheaf.obj (Oₓ).property I i)

/-- **The resolution is K-flat.**  Both of the cone's two single complexes are K-flat, each term
being an integer ideal power and so flat, and the mapping cone of a morphism of K-flat complexes
is K-flat. -/
public theorem kFlat_powerQuotientResolution
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X
      (powerQuotientResolution X I ι i) :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_mappingCone X _
    (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ _
      (isFlat_idealPowerTerm_unit X I ι (i + 1)) 0)
    (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ _
      (isFlat_idealPowerTerm_unit X I ι i) 0)

/-! ### The augmentation -/

/-- **The augmentation `[I^{i+1} ⟶ I^i] ⟶ (I^i/I^{i+1})[0]`.** -/
public noncomputable abbrev powerQuotientResolutionAug
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) :
    powerQuotientResolution X I ι i ⟶
      (HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0).obj
        (powerQuotient X I ι i) :=
  CochainComplex.mappingCone.descShortComplex (powerInclSequenceSingle X I ι i)

/-- **The augmentation is a quasi-isomorphism**, so `[I^{i+1} ⟶ I^i]` is a K-flat resolution of
`I^i/I^{i+1}`.  This is Mathlib's mapping-cone criterion at the short exact sequence of single
complexes. -/
public theorem quasiIso_powerQuotientResolutionAug
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) : QuasiIso (powerQuotientResolutionAug X I ι i) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (powerInclSequenceSingle_shortExact X I ι i)

/-- **The K-flat resolution of `I^i/I^{i+1}`, packaged.**  This is the input
`DerivedTensorProduct.comparisonRight` and `toTensor_eq_of_resolutions` ask for in order to
compute `M ⊗^L I^i/I^{i+1}` by an ordinary tensor product. -/
public theorem exists_kFlat_resolution_powerQuotient
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (i : ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
      (p : P ⟶ (HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0).obj
        (powerQuotient X I ι i)),
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P ∧ QuasiIso p :=
  ⟨powerQuotientResolution X I ι i, powerQuotientResolutionAug X I ι i,
    kFlat_powerQuotientResolution X I ι i, quasiIso_powerQuotientResolutionAug X I ι i⟩

/-! ### The derived tensor product with `I^i/I^{i+1}`, computed by an ordinary one -/

section DerivedTensor

open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor product with `I^i/I^{i+1}` is the ordinary total complex against the
resolution.**  For an *arbitrary* cochain complex `F` of `O_X`-modules — no flatness and no
torsion-freeness — the object

`F ⊗^L I^i/I^{i+1}`

of `D(O_X)` is the class of `Tot(F ⊗ [I^{i+1} ⟶ I^i])`.

Two steps, each supplied above.  The augmentation of the resolution is a quasi-isomorphism, so
its image under `DerivedCategory.Q` is invertible and tensoring with `F` keeps it invertible;
and the resolution is K-flat, so `DerivedTensorProduct.comparisonRight` identifies the derived
tensor product against it with the ordinary total complex, the left factor being unconstrained.

This is the sense in which `[I^{i+1} ⟶ I^i]` resolves the right-hand factor of Tag 0GT9's
right-hand side: it moves the Bockstein complex of Tag 0GT8 off the derived tensor product. -/
public noncomputable def derivedTensorPowerQuotientIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (i : ℤ) :
    ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj F)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0).obj
            (powerQuotient X I ι i))) ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj F).obj
          (powerQuotientResolution X I ι i)) :=
  (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj F)).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map (powerQuotientResolutionAug X I ι i))
        ((DerivedCategory.isIso_Q_map_iff_quasiIso (SheafOfModules.{u} Oₓ)
          (powerQuotientResolutionAug X I ι i)).2
            (quasiIso_powerQuotientResolutionAug X I ι i)))).symm ≪≫
    (canonicalDerivedTensorProduct X.sheaf).comparisonRight F
      (powerQuotientResolution X I ι i) (kFlat_powerQuotientResolution X I ι i)

/-- **Tag 0GT8's Bockstein term is the homology of an ordinary complex.**  On an object of
`D(O_X)` represented by a cochain complex `F`,

`H^i(F ⊗^L I^i/I^{i+1}) ≅ H^i(Tot(F ⊗ [I^{i+1} ⟶ I^i]))`.

`derivedTensorPowerQuotientIso` carried through `DerivedCategory.homologyFunctor`, then
`DerivedCategory.homologyFunctorFactors` to read the derived-category homology of a class as the
homology of the complex.  The left-hand side is `bocksteinTerm`, the degree-`i` term of
`bocksteinComplex`; the right-hand side mentions no derived tensor product. -/
public noncomputable def bocksteinTermIsoHomology
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (i : ℤ) :
    bocksteinTerm X I ι (DerivedCategory.Q.obj F) i ≅
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj F).obj
        (powerQuotientResolution X I ι i)).homology i :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} Oₓ) i).mapIso
      (derivedTensorPowerQuotientIso X I ι F i) ≪≫
    (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} Oₓ) i).app _

end DerivedTensor

end Stacks.IdealTorsion.Bockstein

end
