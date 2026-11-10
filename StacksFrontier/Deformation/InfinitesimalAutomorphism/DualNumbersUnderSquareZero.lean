module

public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermSequence
public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow

/-!
# The dual numbers under a base object are the square-zero extension `k[ε]`

For an object `A` of `𝒞_Λ`, the canonical dual numbers under `A` of
`Deformation.dualNumbersUnder` are, as an object of `𝒞_Λ`, the square-zero extension
`k[ε] = k ⊕ k ε` of `squareZeroExtensionArtinian`: both are `TrivSqZeroExt k k` with the
`Λ`-algebra structure through `k`, the composite `Λ ⟶ A ⟶ k` being the structure map of `k`.
Under this identification the scalings `ε ↦ c ε` of the dual numbers under `A` are the scalings
of `k[ε]`, and for `A = k` the structure arrow `k ⟶ k[ε]` is the inclusion.

## Main results

* `Deformation.algebrasUnder_artinianDualNumbers_right_eq`.
* `Deformation.algebrasUnder_map_squareZero_right_eq`.
* `Deformation.algebrasUnder_artinianDualNumbers_hom_eq`.
-/

@[expose] public noncomputable section

namespace Deformation

open CategoryTheory

universe u

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Two objects of `𝒞_Λ` on the same ring with equal `Λ`-algebra structures and residue
identifications agreeing on residues are equal. -/
theorem ArtinianLocalAlgCat.mk_eq_mk {C : Type u} [CommRing C] [IsArtinianRing C]
    [IsLocalRing C] (i₁ i₂ : Algebra Λ C) (h : i₁ = i₂)
    (e₁ : letI := i₁; IsLocalRing.ResidueField C ≃ₐ[Λ] k)
    (e₂ : letI := i₂; IsLocalRing.ResidueField C ≃ₐ[Λ] k)
    (he : ∀ x : C, e₁ (IsLocalRing.residue C x) = e₂ (IsLocalRing.residue C x)) :
    (letI := i₁; ArtinianLocalAlgCat.mk C e₁ : ArtinianLocalAlgCat.{u, u, u} Λ k) =
      (letI := i₂; ArtinianLocalAlgCat.mk C e₂) := by
  subst h
  congr 1
  exact AlgEquiv.ext fun x => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact he y

/-- **The dual numbers under `A` are `k[ε]`.** -/
theorem algebrasUnder_artinianDualNumbers_right_eq (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    letI := residueAlgebra A
    ((algebrasUnder A).obj (artinianDualNumbers.{u, u, u} A k)).right =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k)) := by
  let := residueAlgebra A
  refine ArtinianLocalAlgCat.mk_eq_mk _ _ (Algebra.algebra_ext _ _ fun t => ?_) _ _ fun x => rfl
  change TrivSqZeroExt.inl (A.residueEquiv (IsLocalRing.residue A (algebraMap Λ A t))) =
    TrivSqZeroExt.inl (algebraMap Λ k t)
  exact congrArg TrivSqZeroExt.inl (A.residueEquiv.commutes t)

/-- **The identification of the dual numbers under `A` with `k[ε]` is the comparison
`Deformation.squareZeroCross`**: both are the identity of `TrivSqZeroExt k k`. -/
theorem eqToHom_algebrasUnder_artinianDualNumbers_right_eq (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    eqToHom (algebrasUnder_artinianDualNumbers_right_eq A) =
      squareZeroCross.{u, u, u} A (FGModuleCat.of k (ULift.{u} k)) :=
  ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun t => eq_of_heq (hom_eqToHom_apply_heq _ t))

/-- **The scalings of the dual numbers under `A` are those of `k[ε]`**, through any
identifications of an object of `𝒞_Λ` with the dual numbers under `A`. -/
theorem eqToHom_comp_algebrasUnder_map_comp_eqToHom (A X : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (h₁ : X = (letI := residueAlgebra A; (algebrasUnder A).obj
      (artinianDualNumbers.{u, u, u} A k)).right)
    (h₂ : (letI := residueAlgebra A; (algebrasUnder A).obj
      (artinianDualNumbers.{u, u, u} A k)).right = X)
    (hd : X = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k)))
    (φ : FGModuleCat.of k (ULift.{u} k) ⟶ FGModuleCat.of k (ULift.{u} k)) :
    eqToHom h₁ ≫ (letI := residueAlgebra A; (algebrasUnder A).map
        ((squareZeroExtensionArtinian.{u, u, u} A k).map φ)).right ≫
        eqToHom h₂ =
      eqToHom hd ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map φ ≫ eqToHom hd.symm := by
  subst h₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← cancel_mono (eqToHom hd), Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id, eqToHom_algebrasUnder_artinianDualNumbers_right_eq]
  exact squareZeroCross_naturality.{u, u, u} A φ

/-- **The structure arrow of the dual numbers under `A` is the one of `k[ε]` re-based at `A`**,
through any identification of the dual numbers under `A` with `k[ε]`. -/
theorem dualNumbers_hom_comp_eqToHom (A Y : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (h₂ : (letI := residueAlgebra A; (algebrasUnder A).obj
      (artinianDualNumbers.{u, u, u} A k)).right = Y)
    (hY : Y = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k))) :
    (letI := residueAlgebra A; (algebrasUnder A).obj
        (artinianDualNumbers.{u, u, u} A k)).hom ≫ eqToHom h₂ =
      (squareZeroCrossUnder.{u, u, u} A (FGModuleCat.of k (ULift.{u} k))).hom ≫
        eqToHom hY.symm := by
  subst h₂
  rw [eqToHom_refl, Category.comp_id]
  have e : ((squareZeroCrossUnder.{u, u, u} A (FGModuleCat.of k (ULift.{u} k))).hom :
        A ⟶ (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k))) =
      (let := residueAlgebra A; (algebrasUnder A).obj
        (artinianDualNumbers.{u, u, u} A k)).hom ≫ eqToHom hY := by
    rw [eqToHom_algebrasUnder_artinianDualNumbers_right_eq]
    rfl
  refine ((congrArg (· ≫ eqToHom hY.symm) e).trans ?_).symm
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- **The structure arrow of the dual numbers under the residue field is the inclusion
`k ⟶ k[ε]`**, through identifications of the objects of `𝒞_Λ` involved. -/
theorem eqToHom_comp_dualNumbers_hom_comp_eqToHom (A X Y : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : A = residueFieldObject.{u, u, u} Λ k) (h₁ : X = A)
    (h₂ : (letI := residueAlgebra A; (algebrasUnder A).obj
      (artinianDualNumbers.{u, u, u} A k)).right = Y)
    (hb : X = residueFieldObject.{u, u, u} Λ k)
    (hY : Y = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k))) :
    eqToHom h₁ ≫ (letI := residueAlgebra A; (algebrasUnder A).obj
        (artinianDualNumbers.{u, u, u} A k)).hom ≫ eqToHom h₂ =
      eqToHom hb ≫ ((squareZeroCrossUnder.{u, u, u} (residueFieldObject.{u, u, u} Λ k)
        (FGModuleCat.of k (ULift.{u} k))).hom :
          residueFieldObject.{u, u, u} Λ k ⟶
            (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k))) ≫
        eqToHom hY.symm := by
  subst h₁
  subst hA
  simp only [eqToHom_refl, Category.id_comp]
  exact dualNumbers_hom_comp_eqToHom _ Y h₂ hY

end Deformation

end
