module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product `- ⊗^L_{A'} A` on module-valued crystalline cohomology

`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULiftDerivedGlobalSections` is
`RΓ(Cris(X/S), F)` as an object of `D⁺(Mod_A)`, where `A = Γ(S, 𝒪_S)`.  Three of the chapter's
assertions are about that object *after a derived base change of the coefficient ring*:

* the base change map labelled (07MT) of [Stacks, Tag 07MS] is
  `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)` in `D(A)`;
* [Stacks, Tag 07MU] asserts that that map is an isomorphism under seven conditions;
* [Stacks, Tag 07N5] asserts that
  `F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)` becomes an
  isomorphism after inverting `p`.

This file supplies the functor `- ⊗^L_{A'} A` those statements need, at the universes this
chapter's module-valued cohomology lives at, and writes down the **source** of (07MT) and of the
map of [Stacks, Tag 07N5] as objects of `D(Mod_A)`.

## The derived tensor product is not new; it is instantiated here

The note at
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleCohomology.lean:139-141` says that no
derived tensor product `- ⊗^L_A -` is constructed anywhere.  That is out of date: the library has
one, as `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`
(`StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean:1463`), the total left derived functor of
extension of scalars along a ring map, constructed by K-flat resolutions
([Stacks, Tag 06Y5], [Stacks, Tag 06Y4]).  It is usable here without modification, for three
reasons:

1. its ring and module universes are independent, so the chapter's arrangement — rings
   `A, A' : Type u`, modules at `ModuleCat.{u + 1}` — is an instance of it, taking its module
   universe parameter to be `u + 1` while both ring universes stay at `u`;
2. the two derived categories are *instance arguments*, not fixed at
   `CategoryTheory.HasDerivedCategory.standard`, so the models this chapter chooses in
   `Crystalline.GlobalCrystallineSituation.SmallSite.hasDerivedCategoryModuleCat` can be
   supplied;
3. no flatness of `A' ⟶ A` is needed: K-flat resolutions exist for every complex of modules over
   every commutative ring, which is the content of
   `StacksFrontier/Homology/KFlat/Resolution.lean` ([Stacks, Tag 06Y4]).

So the construction below is an instantiation, `derivedBaseChangeTensorBundle`, and everything
else in this file is read off it.  The *differential graded* derived tensor products of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChange.lean` and of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedDerivedTensor.lean` do **not**
serve: the first is a functor between the localizations `DifferentialGraded.derivedCategory'` of
categories of differential graded modules over differential graded algebras, and the library has
no comparison of those with `DerivedCategory (ModuleCat R)` for an ordinary ring `R`; the second
carries its derived category, its resolving class of good modules and the derived extension
itself as abstract parameters rather than constructing any of them.

## The target is `D(A)`, not `D⁺(A)`

`- ⊗^L_{A'} A` is a *left* derived functor, so it is right t-exact: it preserves upper
cohomological cutoffs (`isLE_derivedBaseChangeTensor_obj`) and in general destroys lower ones.
Accordingly it is a functor on the unbounded derived category, and the bounded below
`RΓ(Cris(X'/S'), F')` is carried into `D(Mod_{A'})` along `CategoryTheory.DerivedCategory.Plus.ι`
before it is applied.  This is faithful to the source: (07MT) is asserted to be a map *in
`D(A)`*, and so is the map of [Stacks, Tag 07N5].

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `derivedBaseChangeTensorBundle` — the instantiation of
  `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` along
  `Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeRingHom`, carrying the functor
  together with its comparison with degreewise extension of scalars, the universal property
  exhibiting it as a total left derived functor, and the statements that bounded above complexes
  of projectives and that K-flat complexes compute it.
* `derivedBaseChangeTensor` — **the derived tensor product `- ⊗^L_{A'} A`**, a functor
  `D(Mod_{A'}) ⥤ D(Mod_A)`.
* `derivedBaseChangeTensorGlobalSections` — **`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` as an object of
  `D(Mod_A)`**: the source of the base change map (07MT).
* `BaseChangeMap07MT` — **the type of the map (07MT)**, with the module `F` on `Cris(X/S)`
  carried as a parameter, and `BaseChangeMap07MTOfPullback` the same with `F` pinned to the
  pullback of `F'`, in the generality (`g` an open immersion) in which that pullback exists.
* `frobeniusDerivedBaseChangeTensor` and `frobeniusDerivedBaseChangeTensorGlobalSections` —
  **`- ⊗^L_{A, σ} A` and `RΓ(Cris(X/S), E) ⊗^L_{A, σ} A`** in a Frobenius crystal situation
  [Stacks, Tag 07N2], the source of the map of [Stacks, Tag 07N5].
* `FrobeniusMap07N5` — the type of that map.

## Main results

* `derivedBaseChangeTensor_additive`, `derivedBaseChangeTensor_commShift` and
  `derivedBaseChangeTensor_isTriangulated` — the derived tensor product is additive, commutes
  with the shift and is an exact functor of triangulated categories.
* `isLE_derivedBaseChangeTensor_obj` — it preserves every upper cohomological cutoff, the right
  t-exactness referred to above.
* `isIso_comparison_derivedBaseChangeTensor_of_kFlat` and
  `isIso_comparison_derivedBaseChangeTensor_of_projective` — a K-flat complex of `A'`-modules,
  and a bounded above complex of projective `A'`-modules, compute it.  These pin the functor
  down, so the construction is not an empty choice.
* `baseChangeRingHom_specSigma` — in a Frobenius crystal situation the ring map that
  `frobeniusDerivedBaseChangeTensor` extends scalars along **is** `σ`, so the twist in
  `- ⊗^L_{A, σ} A` is the one [Stacks, Tag 07N5] asks for and not the identity.

## What is and is not proved

What is proved is that the derived tensor product `- ⊗^L_{A'} A` exists as a functor
`D(Mod_{A'}) ⥤ D(Mod_A)` at the universes of this chapter's module-valued crystalline cohomology,
with the exactness, shift-compatibility and computation properties listed above; that
`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` and `RΓ(Cris(X/S), E) ⊗^L_{A, σ} A` are therefore objects of
`D(Mod_A)`; and that the twist used for [Stacks, Tag 07N5] is `σ`.

What is **not** proved, and what this file does not do:

* **The base change map (07MT) is not constructed here**, and for a general `g` it is not
  constructed anywhere.  Of that map only the *type* is written down in this file, as
  `BaseChangeMap07MT`.  For `g : X ⟶ X'` an **open immersion** a term of that type now exists,
  `Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeMap07MT` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapConstruction.lean`, built
  from the underived comparison on global sections
  `Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeGlobalSectionsTrans` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMap.lean` by the five derived
  steps that file lists, the last of them the adjunction
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`
  ([Stacks, Tag 0GMT]) against the derived tensor product of this file.  That generality is
  [Stacks, Tag 07KL] and **not** [Stacks, Tag 07MJ]: condition (4) of [Stacks, Tag 07MU] makes
  its `g` a base change `X = X' ×_{S'₀} S₀`, which is not an open immersion, so the tag's own
  map is still missing and nothing in the library carries `@[stacks 07MU]`.
  [Stacks, Tag 07MU] *is* stated, as
  `Crystalline.GlobalCrystallineSituation.SmallSite.IsBaseChangeIso07MU` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeIsomorphism.lean`, with all
  seven of its conditions, as a predicate on a carried `BaseChangeMap07MT`; carrying the map is
  what keeps the statement available in the generality the tag needs.
* **All seven conditions of [Stacks, Tag 07MU] are expressible in this library**, and are the
  hypotheses of `...SmallSite.IsBaseChangeIso07MU`.  With
  `A' = Γ(S', 𝒪_{S'})` and `A = Γ(S, 𝒪_S)`, they are rendered as follows.
  1. `p` nilpotent in `A'`: `IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤))`, the rendering used
     elsewhere in the chapter for this hypothesis on the base ring.
  2. `F'` a crystal in quasi-coherent modules: `SheafOfModules.IsQuasicoherentOnSite` together
     with `Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, the rendering used elsewhere
     in the chapter for this hypothesis on the coefficients.
  3. `X' ⟶ S'₀` quasi-compact and quasi-separated: `AlgebraicGeometry.QuasiCompact` and
     `AlgebraicGeometry.QuasiSeparated` of `S'.toClosedFiber`.
  4. `X = X' ×_{S'₀} S₀`: `CategoryTheory.IsPullback g S.toClosedFiber S'.toClosedFiber`
     applied to `Crystalline.DividedPowerScheme.closedFiberMap f`.
  5. `F'` a flat `𝒪_{X'/S'}`-module: `...SmallSite.IsFlatModule` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeIsomorphism.lean`.

     The library has a monoidal structure on the sheaves of modules of a general
     site — two, in fact: `Stacks.sheafTensorRight`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactness.lean:600`) and
     `Stacks.SheafOfModules.monoidalCategory`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean`), the latter by monoidal
     localization for an arbitrary site.  Mathlib has neither.
     The source's notion is already defined and tagged here, as
     `Stacks.SheafOfModules.IsFlat`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactness.lean`) and
     `AlgebraicGeometry.SheafOfModules.IsFlat` (`StacksFrontier/CategoryTheory/Sites/Modules/Flat
     .lean:297`), both `@[stacks 03ER "part (3)"]`, both exactness of `G ↦ G ⊗_𝒪 F`.

     The `RingCat`-versus-`CommRingCat` distinction does not matter, the definition not being
     objectwise: `commStructureSheaf` supplies the commutativity, and
     `...SmallSite.commRingSheafToRingSheaf_commStructureSheaf` proves it lands back on
     `structureSheaf S` by `rfl`, so the predicate is about this chapter's own modules with no
     transport.  *Objectwise* flatness would be strictly
     stronger, hence would state something weaker than [Stacks, Tag 07MU]; it is not used.
  6. `X' ⟶ S'₀` a local complete intersection morphism:
     `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism` of `S'.toClosedFiber`
     ([Stacks, Tag 069F], in
     `StacksFrontier/AlgebraicGeometry/MoreMorphisms/LocalCompleteIntersection/Defs.lean`).
  7. `X'` and `S₀` Tor independent over `S'₀`: `AlgebraicGeometry.TorIndependent` of
     `S'.toClosedFiber` and `Crystalline.DividedPowerScheme.closedFiberMap f`
     ([Stacks, Tag 08IA], in `StacksFrontier/AlgebraicGeometry/Perfect/TorIndependence.lean`).

  Condition (4) is in tension with the small-site pullback of modules the small sites had:
  `Crystalline.GlobalCrystallineSituation.SmallSite.smallChangeBaseModulePullback` needs
  `g : X ⟶ X'` to be an open immersion, which a projection from a fibre product is not.  That
  tension is resolved: `...SmallSite.crisModulePullback` is the pullback for an arbitrary `g`,
  and `...SmallSite.IsBaseChangeIso07MUOfCrisModule` states 07MU with `F` computed by it.  What
  keeps `BaseChangeMap07MT` carrying `F` as a parameter is that `crisModulePullback` takes its
  coefficients on the *big* site `CRIS(X'/S')`; `BaseChangeMap07MTOfPullback` remains the
  strictly less general open-immersion variant.
* **Nothing about [Stacks, Tag 07N5] beyond the source of its map is stated *here*.**  The tag
  itself is stated in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusInvertPrime.lean`, as
  `...SmallSite.Statement07N5`, which takes as a parameter `frobeniusMap`, the map
  `F_E ∘ (F_X)^*_cris` itself, which needs the action of the Frobenius morphism of crystalline
  topoi on module-valued cohomology and hence the same functoriality as (07MT).  That map is
  `...SmallSite.frobeniusMap07N5Canonical` of `SmallSite/FrobeniusDerivedGlobalSections.lean`, and
  the tag is proved at it, as `...SmallSite.statement07N5` of
  `SmallSite/Frobenius07N5Theorem.lean`.  That file's "What is and is not proved" is the full
  account.  The passage from a `Crystalline.FCrystal` — a sheaf on the *big* site — to a sheaf of
  `𝒪_{X/S}`-modules on the small site is `...SmallSite.restrictSheafOfModules`, used there as
  `...SmallSite.toSmallFCrystal`.

  The third of the three arrows the source's proof factors its map into *is* proved, as
  `...SmallSite.becomesIsoAfterInvertingPrime_frobeniusCohomologyMap` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusCohomologyIsogeny.lean`: that
  arrow is induced by `F_E` and needs functoriality in the coefficients only.

  "Becomes an isomorphism after inverting `p`" does not require a localization of a derived
  category of modules at an element of the ring: inverting `p` is **not** a localization of
  the category but a change of coefficient ring `A ⟶ A[1/p]`, and the assertion is that the image
  of the map under `- ⊗_A A[1/p]` is an isomorphism.  `A[1/p]` is flat over `A`, so extension of
  scalars along it is exact and no derived functor is needed.  It is formalized as
  `...SmallSite.invertPrime` with the predicate
  `...SmallSite.BecomesIsoAfterInvertingPrime`, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusInvertPrime.lean`, where
  `...isIso_nsmul_id_invertPrime_obj` checks that the functor really does invert `p`.
* **No `@[stacks]` attribute is placed by this file.**  The derived tensor product is
  infrastructure, and `BaseChangeMap07MT` and `FrobeniusMap07N5` are types of maps, not
  assertions.  [Stacks, Tag 07MU] and [Stacks, Tag 07N5] are each stated elsewhere — in
  `SmallSite/BaseChangeIsomorphism.lean` and `SmallSite/FrobeniusInvertPrime.lean` — and neither
  is proved, so neither tag is carried anywhere in the library.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wS' wA wA'

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}}

/-! ### The derived tensor product `- ⊗^L_{A'} A` -/

section Tensor

variable [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The derived extension-of-scalars data along `baseChangeRingHom f : A' ⟶ A`**, at the ring
universe `u` and the module universe `u + 1` of the chapter's module-valued crystalline
cohomology.

This is `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, whose module
universe parameter is taken to be `u + 1` while both ring universes stay at `u`; the two derived
categories are its instance arguments and are supplied from the ambient context, so the models
this chapter uses are the ones the functor is built at.  The bundle carries more than the
functor: the comparison with degreewise extension of scalars, the universal property exhibiting
the functor as its total left derived functor, and the two computations by bounded above
complexes of projectives and by K-flat complexes. -/
def derivedBaseChangeTensorBundle (f : S.S ⟶ S'.S) :
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u + 1, u, wA', wA}
      (baseChangeRingHom f) :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u + 1, wA', wA}
    (baseChangeRingHom f)

/-- **The derived tensor product `- ⊗^L_{A'} A : D(Mod_{A'}) ⥤ D(Mod_A)`** along the ring map
`A' = Γ(S', 𝒪_{S'}) ⟶ A = Γ(S, 𝒪_S)` induced by a morphism `f : S ⟶ S'` of divided power bases.

This is the functor the base change map (07MT) of [Stacks, Tag 07MS] and the theorem
[Stacks, Tag 07N5] are written with.  Its target is the unbounded derived category because a
left derived functor is only right t-exact; see `isLE_derivedBaseChangeTensor_obj`. -/
@[sga "4 XVII 4.2.8" "special case"]
def derivedBaseChangeTensor (f : S.S ⟶ S'.S) :
    DerivedCategory (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (derivedBaseChangeTensorBundle f).functor

/-- The derived tensor product is additive. -/
instance derivedBaseChangeTensor_additive (f : S.S ⟶ S'.S) :
    (derivedBaseChangeTensor f).Additive :=
  (derivedBaseChangeTensorBundle f).additive

/-- The derived tensor product commutes with the shift of the derived categories, which is part
of [Stacks, Tag 06Y6]. -/
instance derivedBaseChangeTensor_commShift (f : S.S ⟶ S'.S) :
    (derivedBaseChangeTensor f).CommShift ℤ :=
  (derivedBaseChangeTensorBundle f).commShift

/-- **The derived tensor product is an exact functor of triangulated categories**, again
[Stacks, Tag 06Y6]: the third object of a distinguished triangle on two K-flat complexes is
K-flat. -/
instance derivedBaseChangeTensor_isTriangulated (f : S.S ⟶ S'.S) :
    (derivedBaseChangeTensor f).IsTriangulated :=
  (derivedBaseChangeTensorBundle f).isTriangulated

/-- **The derived tensor product preserves every upper cohomological cutoff**: it is right
t-exact.  This is why it is a functor on the *unbounded* derived category, and why the base
change map (07MT) is a map of `D(A)` and not of `D⁺(A)`. -/
theorem isLE_derivedBaseChangeTensor_obj (f : S.S ⟶ S'.S)
    (X : DerivedCategory (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))) (n : ℤ) [X.IsLE n] :
    ((derivedBaseChangeTensor f).obj X).IsLE n :=
  (derivedBaseChangeTensorBundle f).maps_t_le X n

/-- **A K-flat complex of `A'`-modules computes the derived tensor product**: the comparison from
the derived to the degreewise extension of scalars is an isomorphism there.  This is the defining
property of [Stacks, Tag 06Y5], and is what pins the functor down. -/
theorem isIso_comparison_derivedBaseChangeTensor_of_kFlat (f : S.S ⟶ S'.S)
    (P : CochainComplex (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) ℤ)
    (hP : CochainComplex.KFlat.{u, u + 1} P) :
    IsIso ((derivedBaseChangeTensorBundle f).comparison.app P) :=
  (derivedBaseChangeTensorBundle f).comparison_isIso_of_kFlat P hP

/-- **A bounded above complex of projective `A'`-modules computes the derived tensor product.**
This is the route of [Stacks, Tag 064F]; together with the K-flat computation it is what makes
the functor the expected one on the objects one can resolve. -/
theorem isIso_comparison_derivedBaseChangeTensor_of_projective (f : S.S ⟶ S'.S)
    (P : CochainComplex (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) ℤ) (n : ℤ) [P.IsStrictlyLE n]
    [∀ i, Projective (P.X i)] :
    IsIso ((derivedBaseChangeTensorBundle f).comparison.app P) :=
  (derivedBaseChangeTensorBundle f).comparison_isIso_of_projective P n

end Tensor

/-! ### The source of the base change map (07MT) -/

section BaseChange

variable [HasDerivedCategory.{wS} (ModuleSheaf S)] [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A`, as an object of `D(Mod_A)`.**  This is the source of the
base change map (07MT) of [Stacks, Tag 07MS], and the object [Stacks, Tag 07MU] asserts to be
isomorphic to `RΓ(Cris(X/S), F)`.

The derived global sections are
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULiftDerivedGlobalSections`, an object of
`D⁺(Mod_{A'})` for `F'` a sheaf of `𝒪_{X'/S'}`-modules at the module universe the chapter's
crystal and quasi-coherence predicates are stated at; it is carried into the unbounded derived
category along `CategoryTheory.DerivedCategory.Plus.ι` before the derived tensor product is
applied, because `- ⊗^L_{A'} A` is only right t-exact. -/
def derivedBaseChangeTensorGlobalSections (f : S.S ⟶ S'.S)
    (F' : SheafOfModules.{u} (structureSheaf S')) :
    DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (derivedBaseChangeTensor f).obj
    (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections S' F'))

/-- **The type of the base change map (07MT) of [Stacks, Tag 07MS]**:
`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)` in `D(A)`.

Both `F'` on `Cris(X'/S')` and `F` on `Cris(X/S)` are parameters, `F` at the module universe
`u` of the chapter's crystal and quasi-coherence predicates.

A term of this type is constructed for `g` an open immersion, with `F` the pullback of `F'`:
`Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeMap07MT` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapConstruction.lean`.  For an
arbitrary `g` the map of [Stacks, Tag 07MS] is
`Crystalline.GlobalCrystallineSituation.SmallSite.crisGlobalBaseChangeMap` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapGlobal07MS.lean`,
whose pullback
`F = f_cris^*F'` lives at the raised module universe of the cohomology. -/
abbrev BaseChangeMap07MT (f : S.S ⟶ S'.S) (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S)) :=
  derivedBaseChangeTensorGlobalSections f F' ⟶
    DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections S F)

/-- **The type of the base change map (07MT) with `F` pinned to the pullback of `F'`**, in the
generality in which that pullback exists: `g : X ⟶ X'` an open immersion, which is
[Stacks, Tag 07KL] and not [Stacks, Tag 07MJ].  The pullback is
`Crystalline.GlobalCrystallineSituation.SmallSite.smallChangeBaseModulePullback` applied to the
universe lift `Crystalline.GlobalCrystallineSituation.SmallSite.moduleULift` of `F'`, that
pullback being stated at the raised module universe. -/
abbrev BaseChangeMap07MTOfPullback (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] (F' : SheafOfModules.{u} (structureSheaf S')) :=
  derivedBaseChangeTensorGlobalSections f F' ⟶
    DerivedCategory.Plus.ι.obj
      ((derivedModuleGlobalSections S).obj
        ((smallChangeBaseModulePullback S S' f g h).obj ((moduleULift S').obj F')))

end BaseChange

/-! ### The Frobenius twist of [Stacks, Tag 07N5] -/

section Frobenius

variable (T : Crystalline.FCrystalSituation.{u})

/-- **The ring map that the Frobenius base change extends scalars along is `σ`.**  In a Frobenius
crystal situation [Stacks, Tag 07N2] the divided power endomorphism `σ` of `A = Γ(S, 𝒪_S)` becomes
the endomorphism `Spec(σ)` of the divided power base, and
`Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeRingHom` of `Spec(σ)` is `σ` again:
the ring map induced on global sections by `Spec(σ)` is `Spec(σ)` read on global sections, which
is `Crystalline.FCrystalSituation.specSigma_appTop`.

This is what makes `frobeniusDerivedBaseChangeTensor` the twist `- ⊗^L_{A, σ} A` of
[Stacks, Tag 07N5] rather than the untwisted `- ⊗^L_A A`. -/
theorem baseChangeRingHom_specSigma :
    baseChangeRingHom (S := T.global) (S' := T.global) T.specSigma = T.sigma.toRingHom := by
  ext a
  have h : T.specSigma.hom.appTop a = T.sigma a :=
    ConcreteCategory.congr_hom T.specSigma_appTop a
  change (Scheme.Γ.map T.specSigma.hom.op).hom a = _
  rw [Scheme.Γ_map_op]
  exact h

variable [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- **The `σ`-twisted derived tensor product `- ⊗^L_{A, σ} A : D(Mod_A) ⥤ D(Mod_A)`** of
[Stacks, Tag 07N5], the derived extension of scalars along the Frobenius lift `σ` of a Frobenius
crystal situation [Stacks, Tag 07N2].

It is `derivedBaseChangeTensor` of `Spec(σ)`, which extends scalars along `σ` by
`baseChangeRingHom_specSigma`. -/
def frobeniusDerivedBaseChangeTensor :
    DerivedCategory (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) :=
  derivedBaseChangeTensor T.specSigma

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]

/-- **`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A`, as an object of `D(Mod_A)`**: the source of the canonical
map of [Stacks, Tag 07N5].

`E` is here a sheaf of `𝒪_{X/S}`-modules; in the theorem it is the underlying module of a
nondegenerate `F`-crystal `Crystalline.FCrystal`, restricted from the big crystalline site to
this one by `Crystalline.GlobalCrystallineSituation.SmallSite.toSmallFCrystal`. -/
def frobeniusDerivedBaseChangeTensorGlobalSections
    (E : SheafOfModules.{u} (structureSheaf T.global)) :
    DerivedCategory (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) :=
  (frobeniusDerivedBaseChangeTensor T).obj
    (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global E))

/-- **The type of the canonical map of [Stacks, Tag 07N5]**,
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)` in `D(A)`.

The canonical term of this type is
`Crystalline.GlobalCrystallineSituation.SmallSite.frobeniusMap07N5Canonical` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusDerivedGlobalSections.lean`:
the map
`F_E ∘ (F_X)^*_cris`, built by deriving the big-site comparison on global sections along change of
divided power base; the action of the Frobenius morphism of crystalline topoi it uses is the
canonical comparison of [Stacks, Tag 05T2], which exists with no acyclicity hypothesis. The
assertion that such a map becomes an isomorphism after inverting `p` is
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5`, which takes the map as a
parameter, and it is proved at the canonical map as `...SmallSite.statement07N5`. -/
abbrev FrobeniusMap07N5 (E : SheafOfModules.{u} (structureSheaf T.global)) :=
  frobeniusDerivedBaseChangeTensorGlobalSections T E ⟶
    DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global E)

end Frobenius

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
