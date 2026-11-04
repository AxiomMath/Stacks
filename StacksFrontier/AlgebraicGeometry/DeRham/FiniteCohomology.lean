module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DegreeZeroCohomology
import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# Finiteness of de Rham hypercohomology over a Noetherian affine base

Let `A` be a Noetherian ring and `p : X ⟶ Spec A` a proper morphism. The relative de Rham
complex has coherent cohomology sheaves after derived direct image, and over an affine base the
cohomology of derived global sections of a complex with quasi-coherent cohomology is the global
sections of its cohomology sheaves. Combining the two makes each de Rham hypercohomology module
`Hⁱ(RΓ(Spec A, Rp_*Ω^•_{X/Spec A}))` a finite `A`-module.

## Main results

* `AlgebraicGeometry.moduleFinite_moduleSpecΓ_of_isCoherent`: on `Spec R` with `R` Noetherian a
  coherent module has a finite `R`-module of global sections.
* `AlgebraicGeometry.moduleFinite_homology_derivedGlobalSectionsQuasicoherent`: for `E` in
  `D_QCoh(𝒪_{Spec R})` whose `i`-th cohomology sheaf is coherent, `Hⁱ(RΓ(Spec R, E))` is a finite
  `R`-module.

In the namespace `AlgebraicGeometry.DeRhamFiniteCohomology`:

* `deRhamDirectImageComplex` and `deRhamDirectImageComplexHomologyIso`: a cochain complex of
  `𝒪_S`-modules representing `Rp_*Ω^•_{X/S}`, and the identification of its homology with the
  cohomology sheaves of `Rp_*Ω^•_{X/S}`.
* `isQuasicoherent_homology_deRhamDirectImageComplex`,
  `isCoherent_homology_deRhamDirectImageComplex_of_isProper` and
  `isCoherent_homology_deRhamDirectImageComplex_of_isFinite`: quasi-coherence of its homology,
  and coherence for a proper morphism and for a finite morphism, all unconditionally.
* `derivedDeRhamGlobalSections`: `RΓ(Spec A, Rp_*Ω^•_{X/Spec A})` as an object of `D(A)`.
* `moduleFinite_homology_derivedDeRhamGlobalSections_of_isProper` and
  `moduleFinite_homology_derivedDeRhamGlobalSections_of_isFinite`: finiteness of its cohomology
  modules, for a proper and for a finite morphism, both unconditionally.

## Implementation notes

**Two derived categories are in play and the complex is what crosses between them.** The
coherence of the cohomology sheaves of `Rp_*Ω^•_{X/S}` is available only at
`CategoryTheory.HasDerivedCategory.standard`, whose morphisms live in `Type (u + 1)`: that is the
model `Stacks.DeRhamDirectImage.derivedDeRhamDirectImage` and the quasi-coherence of the higher
direct images feeding it are baked at. The affine comparison
`AlgebraicGeometry.homologyDerivedGlobalSectionsQuasicoherentObjIso` carries no derived-category
binder and so is baked at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphisms live in `Type u`. The two
derived categories are equivalent and not equal, so no statement about one is a statement about
the other. What is model-free is a *cochain complex*: `deRhamDirectImageComplex` is a complex
whose image under the standard localization is `Rp_*Ω^•_{X/S}`, its homology is computed in the
abelian category and carries no derived category at all, and feeding it to the locally small
localization transports the coherence across the two models with no comparison of models needed.
This is why the de Rham results below are stated for `RΓ` of that complex.

**The `@[stacks 0FLZ]` attribute is suffixed, and the suffix names the object.**

* *No hypothesis is owed.* [Stacks, Tag 0FLZ] is unconditional, and its whole proof is "this is
  a special case of [Stacks, Tag 0FLY]". That lemma is unconditional here too: the coherence of
  the higher direct images it consumes — [Stacks, Tag 02O5] — is reduced in
  `StacksFrontier/AlgebraicGeometry/ProperCoherentImage/` to the `Prop`
  `HigherDirectImageIsCoherentOverAffineBase`, proved *equivalent* to the tag, and that `Prop`
  is discharged by
  `AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`. The
  proper statement below therefore takes no hypothesis, exactly as
  `isCoherent_homology_derivedDeRhamDirectImage_of_isProper` of
  `StacksFrontier/AlgebraicGeometry/DeRham/CoherentDirectImage.lean` takes none. The `IsFinite`
  variant strengthens `IsProper`, so it carries no attribute.
* *The object.* [Stacks, Tag 0FLZ] is about `H^i_{dR}(X/S) = H^i(RΓ(X, Ω^•_{X/S}))`, which in
  this library is `AlgebraicGeometry.SheafOfModules.deRhamCohomology`, a module over
  `Γ(X, p^{-1}𝒪_S)`. What is proved here is finiteness of `H^i(RΓ(S, Rp_*Ω^•_{X/S}))` over the
  base ring, so the suffix says which object the finiteness is asserted of. The tag itself, for
  `H^i_{dR}(X/S)`, is registered unsuffixed in
  `StacksFrontier/AlgebraicGeometry/DeRham/DeRhamCohomologyDirectImage.lean`, on
  `AlgebraicGeometry.DeRhamCohomologyDirectImage`'s
  `moduleFinite_deRhamCohomologyBaseModule_of_isProper`, which derives it from the statement
  below.

**The comparison with `deRhamCohomology`, and where it lives.** The two objects agree by
[Stacks, Tag 0D5W], proved for a morphism of ringed spaces as
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison_top`. Invoking it needs two further
comparisons, both of which are in
`StacksFrontier/AlgebraicGeometry/DeRham/DeRhamCohomologyDirectImage.lean`: derived sections
compared across the restriction of scalars that turns `Γ(X, p^{-1}𝒪_S)`-modules into
`Γ(S, 𝒪_S)`-modules, which is
`Stacks.Cohomology.DerivedSectionsRestrictScalars.derivedSectionsRestrictIso` — Tag 0D5W's own
`derivedPreimageSections` restricts scalars *before* deriving, whereas `H^i_{dR}` restricts
*after* — and the bounded-below derived direct image compared with the unbounded one, which is
`AlgebraicGeometry.DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso`, built from
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso` and the equality
by `rfl` of `relativePushforward p` with `modulePushforward (inverseImageBaseProjection p)`.

The apparent instance diamond on `Modules Y` is not an obstruction:
with `CategoryTheory.HasDerivedCategory.standard` pinned at raised priority, as it is here and in
`StacksFrontier/AlgebraicGeometry/DeRham/CoherentDirectImage.lean`, both spellings of modules on a
ringed space select the same instance, and `DerivedCategory.Plus` of the two agree by `rfl`.

## References

* [Stacks Project, Tag 0FLZ](https://stacks.math.columbia.edu/tag/0FLZ)
* [Stacks Project, Tag 0FLY](https://stacks.math.columbia.edu/tag/0FLY)
* [Stacks Project, Tag 0FLX](https://stacks.math.columbia.edu/tag/0FLX)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w₁ w₂ u

namespace AlgebraicGeometry

/-! ### Finiteness over an affine Noetherian base -/

/-- **A coherent module on `Spec R` with `R` Noetherian has a finite module of global
sections.** A coherent module is quasi-coherent, hence the associated sheaf of its global
sections, and being of finite type it is the associated sheaf of a finite module. -/
theorem moduleFinite_moduleSpecΓ_of_isCoherent (R : CommRingCat.{u}) [IsNoetherianRing R]
    (F : (Spec R).Modules) (h : F.IsCoherent) :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj F) := by
  have hpair : F.IsQuasicoherent ∧ F.IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae (Spec R) F).out 1 2).mp h
  let e : tilde ((moduleSpecΓFunctor (R := R)).obj F) ≅ F :=
    (ObjectProperty.ι _).mapIso ((tildeEquiv (R := R)).counitIso.app ⟨F, hpair.1⟩)
  have hft := ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae (Spec R) _).out 1 2).mp
    (Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := (Spec R).ringCatSheaf) e)
  exact (tilde_isFiniteType_iff _).mp hft.2

/-- **Hypercohomology over a Noetherian affine base is finite in a degree where the cohomology
sheaf is coherent.** On an affine scheme the `i`-th cohomology of derived global sections of a
complex with quasi-coherent cohomology is the global sections of its `i`-th cohomology sheaf. -/
theorem moduleFinite_homology_derivedGlobalSectionsQuasicoherent (R : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]
    [IsNoetherianRing R] (i : ℤ)
    (E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (h : ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E.obj).IsCoherent) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derivedGlobalSectionsQuasicoherent R).obj E)) :=
  have := moduleFinite_moduleSpecΓ_of_isCoherent R _ h
  Module.Finite.equiv
    (((moduleSpecΓIsoGlobalSectionsOver R).app _) ≪≫
      (homologyDerivedGlobalSectionsQuasicoherentObjIso R i E).symm).toLinearEquiv

end AlgebraicGeometry

namespace AlgebraicGeometry.DeRhamFiniteCohomology

open Stacks.DeRhamDirectImage

section StandardModel

attribute [local instance 2000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **A cochain complex of `𝒪_S`-modules representing `Rp_*Ω^•_{X/S}`**: a preimage of that
object under the localization functor, which exists because the localization is essentially
surjective. Its homology is an object of the abelian category and so does not depend on a choice
of derived category. -/
def deRhamDirectImageComplex : CochainComplex S.Modules ℤ :=
  DerivedCategory.Q.objPreimage (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage p))

/-- The homology of the representing complex is the cohomology sheaf of `Rp_*Ω^•_{X/S}`:
cohomology of the localization of a complex is the homology of the complex. -/
def deRhamDirectImageComplexHomologyIso (i : ℤ) :
    (deRhamDirectImageComplex p).homology i ≅
      (DerivedCategory.Plus.homologyFunctor S.Modules i).obj (derivedDeRhamDirectImage p) :=
  ((DerivedCategory.homologyFunctorFactors S.Modules i).app (deRhamDirectImageComplex p)).symm ≪≫
    (DerivedCategory.homologyFunctor S.Modules i).mapIso
      (DerivedCategory.Q.objObjPreimageIso _)

/-- **The homology of the representing complex is quasi-coherent**, in every degree, for a
quasi-compact and quasi-separated morphism: this is the conclusion of [Stacks, Tag 0FLX] read on
the complex. -/
theorem isQuasicoherent_homology_deRhamDirectImageComplex [QuasiCompact p] [QuasiSeparated p]
    (i : ℤ) : ((deRhamDirectImageComplex p).homology i).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (deRhamDirectImageComplexHomologyIso p i).symm
    (isQuasicoherent_homology_derivedDeRhamDirectImage p i)

/-- **The homology of the representing complex is coherent for a proper morphism over a locally
Noetherian base**, unconditionally: this is the conclusion of [Stacks, Tag 0FLY] read on the
complex. -/
theorem isCoherent_homology_deRhamDirectImageComplex_of_isProper
    [IsLocallyNoetherian S] [IsProper p] (i : ℤ) :
    ((deRhamDirectImageComplex p).homology i).IsCoherent :=
  have := DeRhamCoherentDirectImage.isCoherent_homology_derivedDeRhamDirectImage_of_isProper p i
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
    (deRhamDirectImageComplexHomologyIso p i)

/-- **The homology of the representing complex is coherent for a finite morphism over a locally
Noetherian base**, unconditionally: the higher direct images along a finite morphism of a
coherent module are coherent. -/
theorem isCoherent_homology_deRhamDirectImageComplex_of_isFinite [IsLocallyNoetherian S]
    [IsFinite p] (i : ℤ) : ((deRhamDirectImageComplex p).homology i).IsCoherent :=
  isCoherent_homology_deRhamDirectImageComplex_of_isProper p i

end StandardModel

/-! ### Derived global sections over an affine base -/

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))

/-- The cohomology of the localization of the representing complex is its homology, read in the
locally small derived category of `𝒪_{Spec A}`-modules. -/
def deRhamDirectImageComplexLocalizationHomologyIso (i : ℤ) :
    (DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
        (DerivedCategory.Q.obj (deRhamDirectImageComplex p)) ≅
      (deRhamDirectImageComplex p).homology i :=
  (DerivedCategory.homologyFunctorFactors (Spec (CommRingCat.of A)).Modules i).app _

/-- **`Rp_*Ω^•_{X/Spec A}` as an object of `D_QCoh(𝒪_{Spec A})`**: the representing complex,
localized, all of whose cohomology sheaves are quasi-coherent by [Stacks, Tag 0FLX]. -/
def deRhamDirectImageQuasicoherent [QuasiCompact p] [QuasiSeparated p] :
    (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).FullSubcategory :=
  ⟨DerivedCategory.Q.obj (deRhamDirectImageComplex p), fun n =>
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf).prop_of_iso
      (deRhamDirectImageComplexLocalizationHomologyIso p n).symm
      (isQuasicoherent_homology_deRhamDirectImageComplex p n)⟩

/-- **`RΓ(Spec A, Rp_*Ω^•_{X/Spec A})` as an object of `D(A)`**: the derived global sections, over
the base ring, of the derived direct image of the relative de Rham complex. -/
def derivedDeRhamGlobalSections [QuasiCompact p] [QuasiSeparated p] :
    DerivedCategory (ModuleCat.{u} (CommRingCat.of A)) :=
  (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj (deRhamDirectImageQuasicoherent p)

/-- **[Stacks, Tag 0FLZ] for `RΓ(Spec A, Rp_*Ω^•)`.** For a proper morphism to the spectrum of a
Noetherian ring the de Rham hypercohomology modules `Hⁱ(RΓ(Spec A, Rp_*Ω^•_{X/Spec A}))` are
finite `A`-modules: the cohomology sheaves of `Rp_*Ω^•_{X/Spec A}` are coherent by
[Stacks, Tag 0FLY], and over an affine base the global sections of a coherent module are
finite. -/
theorem moduleFinite_homology_derivedDeRhamGlobalSections_of_isProper
    [IsNoetherianRing A] [IsProper p] (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (CommRingCat.of A)) i).obj (derivedDeRhamGlobalSections p)) :=
  have := isCoherent_homology_deRhamDirectImageComplex_of_isProper p i
  moduleFinite_homology_derivedGlobalSectionsQuasicoherent (CommRingCat.of A) i
    (deRhamDirectImageQuasicoherent p)
    (Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (R := (Spec (CommRingCat.of A)).ringCatSheaf)
      (deRhamDirectImageComplexLocalizationHomologyIso p i))

/-- **For a finite morphism to the spectrum of a Noetherian ring the de Rham hypercohomology
modules `Hⁱ(RΓ(Spec A, Rp_*Ω^•_{X/Spec A}))` are finite `A`-modules**, unconditionally: the
higher direct images along a finite morphism of a coherent module are coherent. -/
theorem moduleFinite_homology_derivedDeRhamGlobalSections_of_isFinite
    [IsNoetherianRing A] [IsFinite p] (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (CommRingCat.of A)) i).obj (derivedDeRhamGlobalSections p)) :=
  moduleFinite_homology_derivedDeRhamGlobalSections_of_isProper p i

end AlgebraicGeometry.DeRhamFiniteCohomology

end
