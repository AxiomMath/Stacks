module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs

/-!
# Quasi-coherence of the graded sum of the higher direct images of the ideal-power multiples

Let `f : X ⟶ Y` be a morphism of schemes, `F` a quasi-coherent `𝒪_X`-module and `I` a
quasi-coherent sheaf of ideals on `Y`. [Stacks, Tag 02O9] considers, for a cohomological degree
`p`, the graded module
`M = ⨁_{n ≥ 0} R ᵖ f_* (I ⁿ F)`
over the Rees algebra `A = ⨁_{n ≥ 0} I ⁿ`, and asserts that it is quasi-coherent and of finite
type. This file proves the quasi-coherence, for `f` quasi-compact and quasi-separated, `F`
quasi-coherent and every degree `p : ℤ`.

## Main results

* `Stacks.Algebraization.isQuasicoherent_sigma_higherDirectImage_idealPowerMultiple` — the
  quasi-coherence clause of [Stacks, Tag 02O9].
* `Stacks.Algebraization.isQuasicoherent_higherDirectImage_idealPowerMultiple` — the same for a
  single summand, registered as an instance.
* `Stacks.Algebraization.higherDirectImageReesMultipleSmul` — the map
  `R ᵖ f_* (I ⁿ F) ⟶ R ᵖ f_* (I ⁿ⁺ⁱ F)` induced by a global section of `I ⁱ`
  ([Stacks, Tag 02O7]).

## References

* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

/-- The subsheaf `I ⁿ F` of a quasi-coherent sheaf of modules is quasi-coherent. -/
public instance isQuasicoherent_idealPowerMultiple {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (F : X.Modules) [F.IsQuasicoherent] :
    (idealPowerMultiple I n F).toSheafOfModules.IsQuasicoherent :=
  idealPowerMultiple_isQuasicoherent I n F

/-- **Stacks Project, Tag 02O9**, one summand. For a quasi-compact and quasi-separated
morphism `f : X ⟶ Y`, a quasi-coherent `𝒪_X`-module `F` and a quasi-coherent sheaf of ideals
`I` on `Y`, the higher direct image `R ᵖ f_* (I ⁿ F)` is quasi-coherent. -/
public instance isQuasicoherent_higherDirectImage_idealPowerMultiple {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (I : Y.IdealSheafData) (n : ℕ) (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj
      (idealPowerMultiple (I.comap f) n F).toSheafOfModules).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage f
    (idealPowerMultiple (I.comap f) n F).toSheafOfModules p

/-- **The quasi-coherence clause of [Stacks, Tag 02O9], in the coproduct model.** For a
quasi-compact and quasi-separated morphism of schemes `f : X ⟶ Y`, a quasi-coherent
`𝒪_X`-module `F` and a quasi-coherent sheaf of ideals `I` on `Y`, the graded module
`⨁_{n ≥ 0} R ᵖ f_* (I ⁿ F)` is quasi-coherent. -/
public theorem isQuasicoherent_sigma_higherDirectImage_idealPowerMultiple {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (I : Y.IdealSheafData) (p : ℤ) :
    (∐ fun n : ℕ ↦ ((Scheme.Modules.pushforward f).rightDerivedPlus p).obj
      (idealPowerMultiple (I.comap f) n F).toSheafOfModules).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit _ fun n ↦
    isQuasicoherent_higherDirectImage_idealPowerMultiple f F I n.as p

/-- **Stacks Project, Tag 02O7**, the functoriality step. For a global section `r` of `I ⁱ`,
the map `R ᵖ f_* (I ⁿ F) ⟶ R ᵖ f_* (I ⁿ⁺ⁱ F)` obtained by applying the higher direct image
functor to multiplication by `r`, the morphism of sheaves `I ⁿ F ⟶ I ⁿ⁺ⁱ F` on `X`. -/
public noncomputable def higherDirectImageReesMultipleSmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : ℤ) (I : Y.IdealSheafData) (F : X.Modules) (n i : ℤ)
    (r : (Stacks.Blowup.reesPiece (I.comap f) i).val.sections) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus p).obj
        (Stacks.Blowup.reesMultiple (I.comap f) n F).toSheafOfModules ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus p).obj
        (Stacks.Blowup.reesMultiple (I.comap f) (n + i) F).toSheafOfModules :=
  ((Scheme.Modules.pushforward f).rightDerivedPlus p).map
    (Stacks.Blowup.reesMultipleSmulHom (I.comap f) F n i r)

end Stacks.Algebraization

end

end
