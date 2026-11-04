module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyProjectiveSpace

/-!
# The projective bundle of a module of rank `n + 1` is Zariski-locally `ℙⁿ`

Let `ℰ` be a module on a scheme `X`, finite locally free of constant rank `n + 1`, and
`π : 𝐏(ℰ) ⟶ X` the projection of its projective bundle. Every point of `X` has an open
neighbourhood `U` on which `ℰ` is free, so that `π ⁻¹ U` is the bundle `𝐏(𝒪_U^{n+1})` over `U`
(`Stacks.ProjectiveBundle.exists_iso_morphismRestrict_free`), which is `ℙⁿ_U` over `U`
(Stacks 01OE, `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace`). Hence `π` is
Zariski-locally on `X` the projective space `ℙⁿ` (Stacks 01OF), and in particular every fibre
of `π` over a point `x` is `ℙⁿ_{κ(x)}`.

The property of being Zariski-locally `ℙⁿ` only depends on the morphism up to isomorphism over
its target, so it transports to any other model of the bundle.

## Main results

* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.of_iso`: the property transports along an
  isomorphism over the target.
* `Stacks.ProjectiveBundle.isLocallyProjectiveSpace_toBase`: **the projection of the projective
  bundle of a module of rank `n + 1` is Zariski-locally `ℙⁿ`.**

## References

* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundle

/-- **Being Zariski-locally `ℙᵐ` transports along an isomorphism over the target.** -/
theorem IsLocallyProjectiveSpace.of_iso {H H' P : Scheme.{u}} {f : H ⟶ P} {m : ℕ}
    (e : H' ≅ H) (h : IsLocallyProjectiveSpace f m) :
    IsLocallyProjectiveSpace (e.hom ≫ f) m := by
  intro y
  obtain ⟨V, hyV, e₀, he₀⟩ := h y
  have : IsIso (e.hom ∣_ (f ⁻¹ᵁ V)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme.{u})
      (MorphismProperty.isomorphisms.infer_property e.hom) _
  let e₁ : (e.hom ⁻¹ᵁ f ⁻¹ᵁ V).toScheme ≅ (f ⁻¹ᵁ V).toScheme := asIso (e.hom ∣_ (f ⁻¹ᵁ V))
  refine ⟨V, hyV, e₁ ≪≫ e₀, ?_⟩
  exact (Category.assoc e₁.hom e₀.hom _).trans
    ((congrArg (e₁.hom ≫ ·) he₀).trans (morphismRestrict_comp e.hom f V).symm)

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- **Stacks 02TX with 01OE: the projection of the projective bundle of a module finite locally
free of constant rank `n + 1` is Zariski-locally on the base the projective space `ℙⁿ`.** Over an
open trivialising the module the projection is that of `𝐏(𝒪^{n+1})`, which is `ℙⁿ` over the
open. -/
theorem isLocallyProjectiveSpace_toBase (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    IsLocallyProjectiveSpace (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase n := by
  intro x
  obtain ⟨U, hxU, Φ, hΦ⟩ := exists_iso_morphismRestrict_free E hqc n x
  refine ⟨U, hxU, Φ.symm ≪≫ projectiveBundleIsoProjectiveSpace (X := U.toScheme) n, ?_⟩
  rw [Iso.trans_hom, Category.assoc]
  refine (congrArg (Φ.symm.hom ≫ ·)
    (projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := U.toScheme) n)).trans ?_
  rw [Iso.symm_hom, Iso.inv_comp_eq, hΦ]

end Stacks.ProjectiveBundle

end
