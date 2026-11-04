module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneInvertibleOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePower
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections

/-!
# The reflexive powers on an open where the module is invertible

Let `X` be an integral locally Noetherian scheme, let `ℱ` be a coherent reflexive `𝒪_X`-module
and let `V ⊆ X` be an integral open subscheme on which `ℱ` is invertible.  The reflexive powers
`ℱ^{[n]}` of [Stacks, Tag 0EBN] are the iterates of the hull tensor product of
[Stacks, Tag 0EBH], and on `V` the hull does nothing, because the ordinary tensor product of
invertible modules is again invertible, hence reflexive.  So

`ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`

with the *ordinary* tensor power of [Stacks, Tag 01CU] on the right.  This is the first step of
the colimit assertion of [Stacks, Tag 0EBN], which rewrites `Γ(W, ℱ^{[n]})` as a space of
twisted sections over `V ∩ W` so that [Stacks, Tag 01PW] (2) applies.

## Main results

* `AlgebraicGeometry.CoherentReflexive.isInvertible_tensorObj_restrict_modules` — the ordinary
  tensor product of the restrictions of two modules invertible on `V` is invertible on `V`.
* `AlgebraicGeometry.CoherentReflexive.tensorObjRestrictIso` — **on an open on which both
  factors are invertible the hull tensor product is the ordinary tensor product**:
  `(ℱ ⊗_𝒞 𝒢)|_V ≅ ℱ|_V ⊗_{𝒪_V} 𝒢|_V`.
* `AlgebraicGeometry.CoherentReflexive.isInvertible_reflexivePower_restrict` — every reflexive
  power of `ℱ` is invertible on `V`.
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerRestrictIso` — **the identification
  `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`.**

## Implementation notes

**Where the two halves come from.**  The restriction of an ordinary tensor product is the
tensor product of the restrictions by [Stacks, Tag 01CD]:
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso`, whose statement is written at
the `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` spelling of the tensor product,
which is definitionally the `AlgebraicGeometry.Scheme.Modules.tensorObj` spelling used here, so
it is quoted with no bridge.  The hull half is
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual`: it needs only that
the restriction be reflexive, with no hypothesis on the complement of `V`, so neither the
codimension nor the depth condition appears below.

`AlgebraicGeometry.CoherentReflexive.rankOneTensorObjRestrictIso` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassMultiplicative.lean` is the
same comparison for two *rank one* modules on an open whose complement has codimension at least
two; `tensorObjRestrictIso` below drops both restrictions, because the recursion
`ℱ^{[n + 1]} = (ℱ ⊗ ℱ^{[n]})^{∨∨}` tensors `ℱ` with a power, and the powers are not presented
as rank one modules.

**Why the target is the integer tensor power.**  `(ℱ|_V)^{⊗ n}` is
`Stacks.SheafOfModules.Invertible.tensorPower` of [Stacks, Tag 01CU], the spelling in which
[Stacks, Tag 01PW] states its graded section module, rather than a fresh `ℕ`-recursion; the
induction step is then the successor comparison `tensorPowerSuccIso` of that tag, composed with
the braiding, since the reflexive power recursion tensors the new factor on the left and
`tensorPowerSuccIso` adds it on the right.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive toDoubleDual unitModule)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (V : X.Opens)

/-! ### The hull tensor product restricted to an open where both factors are invertible -/

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The ordinary tensor product of the restrictions of two `𝒪_X`-modules invertible on `V` is
invertible on `V`, by [Stacks, Tag 01CT] (1). -/
theorem isInvertible_tensorObj_restrict_modules (A B : X.Modules)
    (hA : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (A.restrict V.ι))
    (hB : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (B.restrict V.ι)) :
    SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.tensorObj (A.restrict V.ι) (B.restrict V.ι)) := by
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hA
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hB
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _).toAlgebraicGeometry

/-- **On an open subscheme on which both factors are invertible, the hull tensor product of
[Stacks, Tag 0EBH] is the ordinary tensor product of the restrictions.**  The ordinary tensor
product restricts to the tensor product of the restrictions by [Stacks, Tag 01CD], which is
invertible, hence reflexive; so the canonical map to the double dual restricts to an
isomorphism on that open. -/
def tensorObjRestrictIso (hV : IsIntegral V.toScheme) (A B : CoherentReflexiveModules X)
    (hA : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict A.obj.obj V.ι))
    (hB : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict B.obj.obj V.ι)) :
    Scheme.Modules.restrict (tensorObj A B).obj.obj V.ι ≅
      Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj V.ι)
        (Scheme.Modules.restrict B.obj.obj V.ι) :=
  haveI := hV
  haveI : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  haveI hT : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj V.ι)
        (Scheme.Modules.restrict B.obj.obj V.ι)) :=
    isInvertible_tensorObj_restrict_modules V A.obj.obj B.obj.obj hA hB
  haveI hcoh : _root_.SheafOfModules.IsCoherent
      (Scheme.Modules.tensorObj A.obj.obj B.obj.obj) :=
    (ordinaryTensor A B).property
  haveI : (Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj V.ι)
      (Scheme.Modules.restrict B.obj.obj V.ι)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible V.toScheme _
  haveI : ((Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict V.ι).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isCoherent X V _ hcoh
  let e : (Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict V.ι ≅
      Scheme.Modules.tensorObj (Scheme.Modules.restrict A.obj.obj V.ι)
        (Scheme.Modules.restrict B.obj.obj V.ι) :=
    Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso V.ι A.obj.obj B.obj.obj
  haveI : IsReflexive ((Scheme.Modules.tensorObj A.obj.obj B.obj.obj).restrict V.ι) :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_of_iso e.symm
      (isReflexive_of_isInvertible V.toScheme _)
  haveI := Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual V
    (Scheme.Modules.tensorObj A.obj.obj B.obj.obj) ‹_›
  (asIso ((Scheme.Modules.restrictFunctor V.ι).map
    (toDoubleDual (Scheme.Modules.tensorObj A.obj.obj B.obj.obj)))).symm ≪≫ e

/-! ### The reflexive powers on the open -/

variable (F : CoherentReflexiveModules X)

/-- **Every reflexive power of `ℱ` is invertible on an open where `ℱ` is**, by induction: the
zeroth power is the structure sheaf, and the hull tensor product restricts to the ordinary
tensor product of two invertible modules. -/
theorem isInvertible_reflexivePower_restrict (hV : IsIntegral V.toScheme)
    (hF : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict F.obj.obj V.ι)) :
    ∀ n : ℕ, SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict (reflexivePower F n).obj.obj V.ι)
  | 0 =>
    have : Stacks.SheafOfModules.IsInvertible V.toScheme.presheaf V.toScheme.ringCatSheaf.2
        (Scheme.Modules.restrict (unitModule X) V.ι) :=
      Stacks.SheafOfModules.isInvertible_of_iso _ _
        (Scheme.Modules.restrictUnitIso V.ι).symm
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ ‹_›
  | n + 1 =>
    have := isInvertible_reflexivePower_restrict hV hF n
    have hT := isInvertible_tensorObj_restrict_modules V F.obj.obj
      (reflexivePower F n).obj.obj hF ‹_›
    have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hT
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (Stacks.SheafOfModules.isInvertible_of_iso _ _
        (tensorObjRestrictIso V hV F (reflexivePower F n) hF ‹_›).symm)

/-- **`ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`.**  On an open subscheme on which `ℱ` is invertible the
reflexive powers of [Stacks, Tag 0EBN] restrict to the ordinary integer tensor powers of
[Stacks, Tag 01CU] of the restriction: the hull does nothing on `V`, by
`tensorObjRestrictIso`, so the recursion `ℱ^{[n + 1]} = (ℱ ⊗ ℱ^{[n]})^{∨∨}` becomes the
ordinary recursion, matched with the successor comparison of tensor powers through the
braiding. -/
def reflexivePowerRestrictIso (hV : IsIntegral V.toScheme)
    [hF : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict F.obj.obj V.ι)] :
    ∀ n : ℕ,
      Scheme.Modules.restrict (reflexivePower F n).obj.obj V.ι ≅
        Stacks.SheafOfModules.Invertible.tensorPower V.toScheme.sheaf.obj
          V.toScheme.ringCatSheaf.property (Scheme.Modules.restrict F.obj.obj V.ι) (n : ℤ)
  | 0 => Scheme.Modules.restrictUnitIso V.ι
  | n + 1 =>
    haveI := isInvertible_reflexivePower_restrict V F hV hF n
    tensorObjRestrictIso V hV F (reflexivePower F n) hF ‹_› ≪≫
      Stacks.SheafOfModules.Invertible.tensorProductIso V.toScheme.sheaf.obj
          V.toScheme.ringCatSheaf.property (Iso.refl (Scheme.Modules.restrict F.obj.obj V.ι))
          (reflexivePowerRestrictIso hV n) ≪≫
        Stacks.SheafOfModules.Invertible.tensorProductBraiding V.toScheme.sheaf.obj
            V.toScheme.ringCatSheaf.property _ _ ≪≫
          Stacks.SheafOfModules.Invertible.tensorPowerSuccIso V.toScheme.sheaf.obj
              V.toScheme.ringCatSheaf.property (Scheme.Modules.restrict F.obj.obj V.ι)
              (n : ℤ) ≪≫
            Stacks.SheafOfModules.Invertible.tensorPowerReindex V.toScheme.sheaf.obj
              V.toScheme.ringCatSheaf.property (Scheme.Modules.restrict F.obj.obj V.ι)
              (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

end AlgebraicGeometry.CoherentReflexive

end
