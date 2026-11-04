module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic

/-!
# Completion projections, and base change along the closed subscheme of a kernel

* `Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ` — the projection of a
  coherent module onto a term of its completion, read back on the quotient `F / 𝓘ⁿ⁺¹F` that the
  term is by definition, is the cokernel projection.
* `Stacks.Algebraization.isIso_pullback_snd_ker_subschemeι` — if base change along a closed
  immersion `j` is an isomorphism, so is base change along the closed immersion of the closed
  subscheme cut out by `ker j`, which is isomorphic to `j` over the target.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.Algebraization

/-- The projection onto the `n`-th term of the completion, followed by any identification of that
term with `F / 𝓘ⁿ⁺¹F` (such as `completionFunctor_obj`), is the cokernel projection. -/
public theorem completionProjection_comp_eqToHom_cokernelπ {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (h : ((completionFunctor X I).obj F).obj.obj (op n) = idealPowerQuotient I (n + 1) F.obj :=
      completionFunctor_obj X I F n) :
    completionProjection X I F n ≫ eqToHom h =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι := by
  have h1 : eqToHom (completionFunctor_obj X I F n).symm ≫ eqToHom h =
      𝟙 (idealPowerQuotient I (n + 1) F.obj) := by
    rw [eqToHom_trans, eqToHom_refl]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => cokernel.π (C := X.Modules)
        (idealPowerMultiple I (n + 1) F.obj).ι ≫ k) h1).trans (Category.comp_id _))

/-- Base change along the closed subscheme of an ideal sheaf `J` is an isomorphism as soon as base
change along a closed immersion `j` with kernel `J` is. -/
public lemma isIso_pullback_snd_ker_subschemeι
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z) [IsClosedImmersion j]
    [IsIso (pullback.snd f j)] (J : Z.IdealSheafData) (hJ : j.ker = J := by rfl) :
    IsIso (pullback.snd f J.subschemeι) := by
  subst hJ
  let a := pullback.map f j f j.ker.subschemeι (𝟙 _) j.toImage (𝟙 _)
    (by simp) (by simp)
  have : IsIso a := inferInstance
  have : IsIso (a ≫ pullback.snd f j.ker.subschemeι) := by
    dsimp [a]
    rw [pullback.lift_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left a _

end Stacks.Algebraization

end
