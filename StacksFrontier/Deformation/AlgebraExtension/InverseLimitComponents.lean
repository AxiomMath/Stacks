module

public import StacksFrontier.Deformation.AlgebraExtension.InverseLimit

/-!
# The components of a section of `lim ℳₙ` in the middle terms

For an inverse system `Fₙ` of sheaves of rings with compatible identifications
`Fₙ ≅ 𝒪'ₙ` with the middle terms of algebra extensions `0 → ℳₙ → 𝒪'ₙ → 𝒪 → 0`, the `n`-th
component of a section of `lim ℳₙ`, included in `𝒪'ₙ`, is the `n`-th component of its image in
`lim Fₙ`, carried along `Fₙ ≅ 𝒪'ₙ`.

## Main results

* `Deformation.AlgebraExtension.InverseLimit.incl_idealComponent`: the `n`-th component of a
  section of `lim ℳₙ`, included in `𝒪'ₙ`, is the `n`-th component of its image in `lim Fₙ`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Deformation.AlgebraExtension.InverseLimit

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}} (F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u}) [HasLimit F]
  (ρ : F ⟶ (Functor.const _).obj O)
  {A : ℕ → Sheaf J CommRingCat.{u}} {a : ∀ n, A n ⟶ O}
  {M : ℕ → SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
  (P : ∀ n, AlgebraExtension (a n) (M n)) (e : ∀ n, F.obj (op n) ≅ (P n).extension)
  (he : ∀ n, (e n).hom ≫ (P n).reduction = ρ.app (op n))

/-- **The `n`-th component of a section of `lim ℳₙ`, in the middle term `𝒪'ₙ`**, is the `n`-th
component of its image in `lim Fₙ`, carried along `Fₙ ≅ 𝒪'ₙ`. -/
theorem incl_idealComponent (U : Cᵒᵖ) (n : ℕ) (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    (P n).incl (idealComponent F ρ P e he U n s) =
      (e n).hom.hom.app U ((limit.π F (op n)).hom.app U
        ((kernelInclusion F ρ P e he).val.app U s)) :=
  (hom_app_inv_app (e n) U _).symm.trans (congrArg ((e n).hom.hom.app U)
    ((congrArg ((limit.π F (op n)).hom.app U) (kernelInclusion_val_app F ρ P e he U s)).trans
      (π_kernelSection F ρ P e he U s n)).symm)

end Deformation.AlgebraExtension.InverseLimit

end
