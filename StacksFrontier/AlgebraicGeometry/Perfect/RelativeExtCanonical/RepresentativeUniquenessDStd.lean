module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.RepresentativeUniqueness
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.QCohDerived

/-!
# Uniqueness of a representing object, in the spelling of [Stacks, Tag 08IF]

`Stacks.Cohomology.RelativeExtCanonical.exists_iso_of_representing` restated for the spelling
`Stacks.Cohomology.RelativeExt.DStd` of the derived category used by [Stacks, Tag 08IF], with
`D_QCoh` read as `Stacks.Cohomology.RelativeExt.qcohDerived`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.exists_iso_of_representing_dStd`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry

namespace Stacks.Cohomology.RelativeExtCanonical

/-- **`exists_iso_of_representing` in the spelling `Stacks.Cohomology.RelativeExt.DStd` of the
derived category used by [Stacks, Tag 08IF]**, with `D_QCoh` read as
`Stacks.Cohomology.RelativeExt.qcohDerived`. -/
theorem exists_iso_of_representing_dStd {S : Scheme.{u}} {𝒟 : Type*} [Category 𝒟]
    (Φ : Stacks.Cohomology.RelativeExt.DStd S ⥤ 𝒟) (E : 𝒟)
    (P : ObjectProperty (Stacks.Cohomology.RelativeExt.DStd S))
    (hPge : ∀ N, P N → ∃ m : ℤ, N.IsGE m)
    (L L' : Stacks.Cohomology.RelativeExt.DStd S)
    (hL : Stacks.Cohomology.RelativeExt.qcohDerived S L)
    (hL' : Stacks.Cohomology.RelativeExt.qcohDerived S L')
    (hPL : ∀ n : ℕ, P ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L))
    (hPL' : ∀ n : ℕ, P ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L'))
    (θ : ∀ N, P N → ((L ⟶ N) ≃ (E ⟶ Φ.obj N)))
    (hθ : ∀ {N N'} (hN : P N) (hN' : P N') (g : N ⟶ N') (x : L ⟶ N),
      θ N' hN' (x ≫ g) = θ N hN x ≫ Φ.map g)
    (θ' : ∀ N, P N → ((L' ⟶ N) ≃ (E ⟶ Φ.obj N)))
    (hθ' : ∀ {N N'} (hN : P N) (hN' : P N') (g : N ⟶ N') (x : L' ⟶ N),
      θ' N' hN' (x ≫ g) = θ' N hN x ≫ Φ.map g) :
    ∃ φ : L' ≅ L, ∀ N (hN : P N) (x : L ⟶ N), θ' N hN (φ.hom ≫ x) = θ N hN x :=
  exists_iso_of_representing (X := S) Φ E P hPge L L' hL hL' hPL hPL' θ hθ θ' hθ'

end Stacks.Cohomology.RelativeExtCanonical

end
