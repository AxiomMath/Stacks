module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRhamKoszul
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed immersions of étale schemes into smooth ones

Let `π : X ⟶ S` be smooth of relative dimension `d` and let `i : Z ⟶ X` be a closed immersion
such that `Z ⟶ S` is smooth and formally unramified — for instance a `k`-rational point of a
smooth `k`-scheme, where `Z ≅ Spec k`. Then `i` satisfies the hypotheses of the Gysin
construction of [Stacks, Tag 0G86] and [Stacks, Tag 0G8A] with `c = d`:

* its conormal sheaf is finite locally free of rank `d`: the conormal sequence
  `0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is exact ([Stacks, Tag 06AA]) and `Ω_{Z/S} = 0`,
  so `𝒞_{Z/X} ≅ i^*Ω_{X/S}`;
* it is a Koszul-regular immersion: it is a regular immersion by [Stacks, Tag 067U];
* hence `ℋ^j_Z(Ω^{m + d}_{X/S}) = 0` for `j < d`, the vanishing hypothesis of Tag 0G8A.

## Main results

* `Stacks.Gysin.conormalRank_of_formallyUnramified`
* `Stacks.Gysin.isKoszulRegularImmersion_of_smooth_of_smooth`
* `Stacks.Gysin.supportVanishing_of_formallyUnramified`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Gysin

open Stacks.AlgebraicGeometry.ConormalEquations Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)

/-- **The conormal sheaf of a closed immersion of a smooth formally unramified `S`-scheme into a
scheme smooth of relative dimension `d` over `S` is finite locally free of rank `d`.** -/
theorem conormalRank_of_formallyUnramified (d : ℕ) [SmoothOfRelativeDimension d π]
    [Smooth (i ≫ π)] [FormallyUnramified (i ≫ π)] : ConormalRank i d := by
  have hSE := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i π inferInstance
  have hZ : IsZero (Stacks.ConormalSequenceRight.conormalShortComplex i π).X₃ :=
    Scheme.Hom.isZero_relativeDifferentials_of_formallyUnramified (i ≫ π)
  have : IsIso (Stacks.ConormalSequenceRight.conormalShortComplex i π).f :=
    hSE.isIso_f_iff.2 hZ
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials π d
  have hP : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := structureSheafRing Z.toRingedSpace)
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials π)) d :=
    isFiniteLocallyFreeOfRank_pullback i (Scheme.Hom.relativeDifferentials π) d
  let e : ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials π) :
      _root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) ≅
        Stacks.Conormal.conormalSheaf i :=
    (asIso (Stacks.ConormalSequenceRight.conormalShortComplex i π).f).symm ≪≫
      Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e hP

/-- **A closed immersion of a smooth `S`-scheme into a smooth `S`-scheme is Koszul-regular**, by
[Stacks, Tag 067U]. -/
@[sga "6 VII 1.10" "special case",
  sga "6 VIII 1.1" "partial",
  sga "6 VIII 1.3" "(iii), special case",
  sga "6 VIII 1.8" "partial",
  sga "6 VIII 2.4" "special case"]
theorem isKoszulRegularImmersion_of_smooth_of_smooth [Smooth π] [Smooth (i ≫ π)] :
    IsKoszulRegularImmersion i :=
  isKoszulRegularImmersion_of_isRegularImmersion i
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i π)

/-- **The vanishing hypothesis of [Stacks, Tag 0G8A]** for a closed immersion of a smooth formally
unramified `S`-scheme into a scheme smooth of relative dimension `d` over `S`:
`ℋ^j_Z(Ω^{m + d}_{X/S}) = 0` for `j < d`. -/
theorem supportVanishing_of_formallyUnramified [LocallyOfFinitePresentation i] (d : ℕ)
    [SmoothOfRelativeDimension d π] [Smooth (i ≫ π)] [FormallyUnramified (i ≫ π)] (m : ℕ) :
    Stacks.DeRham.GysinCohomologyDeRham.SupportVanishing X.toRingedSpace (Set.range i.base)
      (isClosed_range_base i) d (Scheme.Hom.relativeDifferentialForms π ((m : ℤ) + (d : ℤ))) :=
  have : Smooth π := SmoothOfRelativeDimension.smooth d π
  Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms i π
    (isKoszulRegularImmersion_of_smooth_of_smooth i π) d
    (conormalRank_of_formallyUnramified i π d) m

end Stacks.Gysin
