module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerRestrict
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusTrivialization
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower

/-!
# The reflexive powers are trivial on a trivializing open

Let `X` be an integral locally Noetherian scheme and `ℱ` a coherent reflexive `𝒪_X`-module.  If
`U ⊆ X` is an open on which `ℱ` is trivial, `ℱ|_U ≅ 𝒪_U`, then every reflexive tensor power of
[Stacks, Tag 0EBN] is trivial on `U` as well:

`ℱ^{[n]}|_U ≅ 𝒪_U`.

This holds with **no hypothesis on `U` whatsoever** — in particular neither integrality nor
nonemptiness.  That is the point of the file.  The open `U` of [Stacks, Tag 0EBN] attached to a
global section `s` of `ℱ`, on which `ℱ` is trivial by
`AlgebraicGeometry.sectionIsomorphismOpenTrivialization`, is empty exactly when `s` generates no
stalk, for instance when `s = 0`; so the comparison
`AlgebraicGeometry.CoherentReflexive.reflexivePowerRestrictIso`, which requires its open to be
integral, cannot be used there, and the isomorphism below is what replaces it.

## Main results

* `AlgebraicGeometry.CoherentReflexive.isReflexive_restrict_tensorObj_of_unitIso`: the ordinary
  tensor product of two modules trivial on `U` is reflexive on `U`, which is why the reflexive
  hull does nothing there.
* `AlgebraicGeometry.CoherentReflexive.tensorObjRestrictUnitIso`: **the hull tensor product of
  [Stacks, Tag 0EBH] is trivial on an open on which both factors are.**
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerRestrictUnitIso`: **`ℱ^{[n]}|_U ≅ 𝒪_U`.**

## Implementation notes

**Why integrality of the open is avoided, and how.**
`AlgebraicGeometry.CoherentReflexive.reflexivePowerRestrictIso` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/ReflexivePowerRestrict.lean` already compares
the reflexive powers with ordinary tensor powers on an open on which `ℱ` is invertible, but it
requires that open to be *integral*, because it reaches reflexivity of the tensor product there
through an invertible-implies-reflexive step that is stated on an integral scheme.  The way round
that is to ask for trivializations rather than invertibility: on `U` the tensor product is then
not merely invertible but *isomorphic to the structure sheaf*, and the structure sheaf is
reflexive on any scheme at all, by
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_unit`.  So the isomorphism of the ordinary
tensor product with the unit is assembled from the two given trivializations by
`Stacks.SheafOfModules.Invertible.tensorProductIso` and `tensorProductLeftUnitor`, and
reflexivity is transported along it; the hull then does nothing on `U` by
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual`, which needs only
that the restriction be reflexive and carries no hypothesis on the complement of `U`.

**Where this is used.**  The trivializations below supply the hypothesis on the second factor
in `AlgebraicGeometry.CoherentReflexive.isIso_restrict_reflexivePowerStep`, which makes
multiplication by `s` invertible on the open `U` of [Stacks, Tag 0EBN]; the cocone of reflexive
powers over `j_*𝒪_U` is built from those inverses
(`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/ReflexivePowerColimitCocone.lean`), and its
colimit property is proved in
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/ReflexivePowerColimit.lean`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive toDoubleDual unitModule
  isReflexive_unit)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)

omit [IsIntegral X] in
/-- **The ordinary tensor product of two modules trivial on `U` is reflexive on `U`.**  It is
isomorphic there to the structure sheaf, which is reflexive on any scheme. -/
theorem isReflexive_restrict_tensorObj_of_unitIso (A B : CoherentReflexiveModules X)
    (eA : Scheme.Modules.restrict A.obj.obj U.ι ≅ unitModule U.toScheme)
    (eB : Scheme.Modules.restrict B.obj.obj U.ι ≅ unitModule U.toScheme) :
    IsReflexive ((Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict U.ι) := by
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have eT : Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
      (Scheme.Modules.restrict B.obj.obj U.ι) ≅ unitModule U.toScheme :=
    Stacks.SheafOfModules.Invertible.tensorProductIso U.toScheme.sheaf.obj
        U.toScheme.ringCatSheaf.property eA eB ≪≫
      Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor U.toScheme.sheaf.obj
        U.toScheme.ringCatSheaf.property (unitModule U.toScheme)
  have hTinv : SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property
      (Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
        (Scheme.Modules.restrict B.obj.obj U.ι)) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso eT.symm (SheafOfModules.isInvertible_unit _ _)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hTinv
  have : (Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
      (Scheme.Modules.restrict B.obj.obj U.ι)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible U.toScheme _
  have hcoh : _root_.SheafOfModules.IsCoherent (Scheme.Modules.tensorObj A.obj.obj B.obj.obj) :=
    (ordinaryTensor A B).property
  have : ((Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict U.ι).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isCoherent X U _ hcoh
  let e : (Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict U.ι ≅
      Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
        (Scheme.Modules.restrict B.obj.obj U.ι) :=
    Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso U.ι A.obj.obj B.obj.obj
  exact Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_of_iso (e ≪≫ eT).symm
    (isReflexive_unit U.toScheme)

/-- **On an open on which both factors are trivial, the hull tensor product of
[Stacks, Tag 0EBH] is trivial.**  The ordinary tensor product of the restrictions is isomorphic
to the structure sheaf there, hence reflexive there, so the canonical map to the double dual
restricts to an isomorphism on that open. -/
def tensorObjRestrictUnitIso (A B : CoherentReflexiveModules X)
    (eA : Scheme.Modules.restrict A.obj.obj U.ι ≅ unitModule U.toScheme)
    (eB : Scheme.Modules.restrict B.obj.obj U.ι ≅ unitModule U.toScheme) :
    Scheme.Modules.restrict (tensorObj A B).obj.obj U.ι ≅ unitModule U.toScheme := by
  haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have eT : Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
      (Scheme.Modules.restrict B.obj.obj U.ι) ≅ unitModule U.toScheme :=
    Stacks.SheafOfModules.Invertible.tensorProductIso U.toScheme.sheaf.obj
        U.toScheme.ringCatSheaf.property eA eB ≪≫
      Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor U.toScheme.sheaf.obj
        U.toScheme.ringCatSheaf.property (unitModule U.toScheme)
  haveI hTinv : SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property
      (Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
        (Scheme.Modules.restrict B.obj.obj U.ι)) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso eT.symm (SheafOfModules.isInvertible_unit _ _)
  haveI := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hTinv
  haveI : (Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
      (Scheme.Modules.restrict B.obj.obj U.ι)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible U.toScheme _
  haveI hcoh : _root_.SheafOfModules.IsCoherent (Scheme.Modules.tensorObj A.obj.obj B.obj.obj) :=
    (ordinaryTensor A B).property
  haveI : ((Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict U.ι).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isCoherent X U _ hcoh
  let e : (Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict U.ι ≅
      Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj U.ι)
        (Scheme.Modules.restrict B.obj.obj U.ι) :=
    Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso U.ι A.obj.obj B.obj.obj
  haveI : IsReflexive ((Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict U.ι) :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_of_iso (e ≪≫ eT).symm
      (isReflexive_unit U.toScheme)
  haveI := Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual U
    (Scheme.Modules.tensorObj A.obj.obj B.obj.obj) ‹_›
  exact (asIso ((Scheme.Modules.restrictFunctor U.ι).map
    (toDoubleDual (Scheme.Modules.tensorObj A.obj.obj B.obj.obj)))).symm ≪≫ e ≪≫ eT

/-- **`ℱ^{[n]}|_U ≅ 𝒪_U`**: every reflexive tensor power of [Stacks, Tag 0EBN] is trivial on an
open on which the module itself is, by induction on the recursion defining the powers.  No
hypothesis on `U` is needed. -/
def reflexivePowerRestrictUnitIso (F : CoherentReflexiveModules X)
    (eF : Scheme.Modules.restrict F.obj.obj U.ι ≅ unitModule U.toScheme) :
    ∀ n : ℕ, Scheme.Modules.restrict (reflexivePower F n).obj.obj U.ι ≅ unitModule U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 =>
    tensorObjRestrictUnitIso U F (reflexivePower F n) eF
      (reflexivePowerRestrictUnitIso F eF n)

end AlgebraicGeometry.CoherentReflexive

end
