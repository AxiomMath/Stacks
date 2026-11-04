module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.PushforwardIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **On a reduced algebraic space, the structure map to the direct image of the structure sheaf
along a surjective representable morphism is a monomorphism**: over every étale chart `U` it is
pullback of functions along the surjective base change `U ×_X Y ⟶ U` onto the reduced `U`. -/
theorem mono_unitToPushforwardObjUnit_smallBaseChangeSharp {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom) (hfs : IsSurjective B S hS f.hom)
    (hred : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    Mono (SheafOfModules.unitToPushforwardObjUnit (smallBaseChangeSharp B S hS f hf)) := by
  let := isContinuous_smallBaseChange B S hS f hf
  refine (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun U => ?_)
  have hsurj := (presheafSurjective_of_isSurjective B S hS f.hom hf hfs).2 U.unop.1.hom _ _
    (hf.isPullback U.unop.1.hom)
  have : IsReduced (chartScheme U.unop) := isReduced_chartScheme B S hS X hred U.unop
  exact @Scheme.Hom.appTop_injective_of_surjective_of_isReduced _ _ _ hsurj this

end AlgebraicGeometry.Space
