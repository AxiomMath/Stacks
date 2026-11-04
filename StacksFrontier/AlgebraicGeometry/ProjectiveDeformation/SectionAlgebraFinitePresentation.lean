module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.UniformDegreeBound
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.NoetherianApproximation

/-!
# The truncated section algebra of a deformation is of finite presentation

This file proves `TruncatedSectionAlgebraFinitePresentationOf`, clause (3) of
[Stacks, Tag 0D4F] for the truncated section algebra `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} (f')_* (ℒ')^{⊗ d}`
of an admissible deformation: if `ℒ'` is ample relative to `f'` and the pieces `𝒜'_d`, `d ≥ d₀`,
are finite locally free, then over every affine open `U ⊆ S'` the ring of sections `𝒜'(U)` is a
finitely presented `Γ(S', U)`-algebra.

The proof is `Stacks.AlgebraicGeometry.SectionRingBaseChange.finitePresentation_tailAlgebra_strHom`
— Noetherian approximation of the base, finite generation over the Noetherian model
([Stacks, Tag 0B5T]), cohomology and base change ([Stacks, Tag 0D4E] (2)) and the algebra of
steps (c)–(i) of the source — whose one remaining input, the finite presentation of the sections
of `(f')_* (ℒ')^{⊗ d}` over `U` for `d ≥ d₀`, is the finite local freeness of `𝒜'_d`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.truncatedSectionAlgebraFinitePresentationOf`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

open PolarizedFamily PolarizedFamily.AdmissibleDeformation

/-- The sections over an affine open of a degree-`d` piece of the Laurent algebra pushed forward
along `f'` are finitely presented once `𝒜'_d` is finite locally free. -/
theorem moduleFinitePresentation_laurentPushforward_sections {P : PolarizedFamily.{u}}
    (D : P.AdmissibleDeformation) (d : ℕ)
    (hd : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := D.S'.ringCatSheaf) (D.sectionPiece d)) (U : D.S'.Opens) (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(D.S', U)
      Γ((Scheme.Modules.pushforward D.f').obj
        ((Stacks.RelativeAmple.laurentPowers D.L').piece (d : ℤ)), U) := by
  have := _root_.AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree
    (D.sectionPiece d) hd
  have := _root_.AlgebraicGeometry.finitePresentation_sections_on_affine (D.sectionPiece d)
    ⟨U, hU⟩
  let φ : (Scheme.Modules.pushforward D.f').obj
      ((Stacks.RelativeAmple.laurentPowers D.L').piece (d : ℤ)) ≅ D.sectionPiece d :=
    (Scheme.Modules.pushforward D.f').mapIso
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso D.X' D.L' (d : ℤ))
  exact Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective
    (Scheme.Modules.sectionsLinearMap φ.inv U)
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.bijective_iso_hom_app' φ.symm (op U)))

/-- **Clause (3) of [Stacks, Tag 0D4F] for the truncated section algebra.**  For an admissible
deformation with `ℒ'` ample relative to `f'` and `𝒜'_d` finite locally free for `d ≥ d₀`, the
ring of sections of `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` over every affine open `U ⊆ S'` is a finitely
presented `Γ(S', U)`-algebra. -/
theorem truncatedSectionAlgebraFinitePresentationOf :
    TruncatedSectionAlgebraFinitePresentationOf.{u} := by
  intro P D d₀ hd₀ hamp hlf U hU
  exact Stacks.AlgebraicGeometry.SectionRingBaseChange.finitePresentation_tailAlgebra_strHom
    D.f' D.L' U D.finitePresentation hamp d₀ hd₀ hU
    fun n hn => moduleFinitePresentation_laurentPushforward_sections D n (hlf n hn) U hU

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
