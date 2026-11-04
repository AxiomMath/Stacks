module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.FramedBasis
public import StacksFrontier.RingTheory.FormsTrace.AnyFrame

/-!
# The local trace maps on forms of a finite syntomic morphism

Let `f : Y ⟶ X` be finite, flat and locally of finite presentation. Over an affine open `U` of
`X` write `A = Γ(X, U)` and `B = Γ(Y, f⁻¹U)`. If `B` admits a frame or is zero (`U` is a framed
open, `Stacks.FormsTrace.IsFramedOpen`), the trace maps `Θ_{B/A}` of
`Stacks.FormsTrace.frameTrace` are defined, and they are compatible with the restriction maps
between framed affine opens.

## Main definitions

* `Stacks.FormsTrace.localTrace`: the trace map `Θ_{B/A}` on forms over an open `U` of `X`.

## Main results

* `Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen`: the framing condition through
  `Stacks.FormsTrace.AnyFrame`.
* `Stacks.FormsTrace.localTrace_restrict`: compatibility with the restriction maps.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.FormsTrace

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Over a framed open `U`, `Γ(Y, f⁻¹U)` is zero or admits a frame over `Γ(X, U)`. -/
theorem framed_or_subsingleton_of_isFramedOpen {U : X.Opens} (hU : IsFramedOpen f U) :
    letI := (f.app U).hom.toAlgebra
    Subsingleton Γ(Y, f ⁻¹ᵁ U) ∨ Nonempty (AnyFrame Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) := by
  let := (f.app U).hom.toAlgebra
  rcases hU.2 with h | ⟨d, hd, ⟨F⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨d, F⟩⟩

/-- **The local trace maps on forms** over an open `U` of `X`: `Θ_{B/A}` for
`A = Γ(X, U)`, `B = Γ(Y, f⁻¹U)`. -/
abbrev localTrace (U : X.Opens) (p : ℕ) :
    letI := (f.app U).hom.toAlgebra
    ⋀[Γ(Y, f ⁻¹ᵁ U)]^p Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄ℤ] :=
  letI := (f.app U).hom.toAlgebra
  frameTrace Γ(X, U) Γ(Y, f ⁻¹ᵁ U) p

variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **The local trace maps commute with restriction** between framed affine opens `V ≤ U`. -/
theorem localTrace_restrict (U V : X.affineOpens) (h : V.1 ≤ U.1) (hU : IsFramedOpen f U.1)
    (hV : IsFramedOpen f V.1) (p : ℕ)
    (η : ⋀[Γ(Y, f ⁻¹ᵁ U.1)]^p Ω[Γ(Y, f ⁻¹ᵁ U.1)⁄ℤ]) :
    letI := X.restrictAlgebra h
    letI := Y.restrictAlgebra (f.preimage_mono h)
    localTrace f V.1 p (formsMap Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ V.1) p η) =
      formsMap Γ(X, U.1) Γ(X, V.1) p (localTrace f U.1 p η) := by
  let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, V.1) := X.restrictAlgebra h
  let : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ V.1) := Y.restrictAlgebra (f.preimage_mono h)
  let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (f.app U.1 ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.toAlgebra
  have hsq := f.isPushout_app_restrict U V h
  have : IsScalarTower Γ(X, U.1) Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change (f.app U.1 ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom x =
        (X.presheaf.map (homOfLE h).op ≫ f.app V.1).hom x
      rw [hsq.w]
  have : IsScalarTower Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Algebra.IsPushout Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (CommRingCat.isPushout_iff_isPushout.mp hsq.flip).symm
  exact frameTrace_formsMap_of_isPushout Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1)
    (framed_or_subsingleton_of_isFramedOpen f hU) (framed_or_subsingleton_of_isFramedOpen f hV)
    p η

end Stacks.FormsTrace

end
