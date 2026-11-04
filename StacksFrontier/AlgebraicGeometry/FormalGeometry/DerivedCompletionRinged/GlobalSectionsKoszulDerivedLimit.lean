module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulKFlat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionKoszulTower
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit

/-!
# `RΓ(𝒞, ℱ^∧)` is a derived limit of the Koszul Hom tower

Let `(𝒞, 𝒪)` be a ringed site, let `A` be a commutative ring with `ρ : A ⟶ Γ(𝒞, 𝒪)`, let
`f_1, …, f_r` be global sections of `𝒪` and let `ℐ = (f_1, …, f_r)` be the sheaf of ideals they
generate. For `K ∈ D(𝒪)` this file proves

`RΓ(𝒞, K^∧) = R lim_n RΓ(𝒞, R𝑆heafHom_𝒪(K^n, K))`,   `K^n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})`,

the derived completion being the reflector of [Stacks, Tag 099F] along `ℐ`. This is the sheaf
side of the identity `RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)` of [Stacks, Tag 0BLX].

## Main results

* `CategoryTheory.Pretriangulated.nonempty_iso_of_isDerivedLimit`: two derived limits of one
  system are isomorphic.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHomSystem_derivedCompletion`: the
  reflector of [Stacks, Tag 099F] at `ℐ = (f_1, …, f_r)` is a derived limit of the tower
  `n ↦ R𝑆heafHom_𝒪(K^n, K)`.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem`:
  `RΓ(𝒞, K^∧)` is a derived limit of the tower `n ↦ RΓ(𝒞, R𝑆heafHom_𝒪(K^n, K))`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

/-! ## Two derived limits of one system -/

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Two derived limits of one inverse system are isomorphic.** -/
theorem nonempty_iso_of_isDerivedLimit {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj (op n)]
    {K K' : D} (hK : IsDerivedLimit F K) (hK' : IsDerivedLimit F K') : Nonempty (K ≅ K') := by
  obtain ⟨p, δ, hδ⟩ := hK
  obtain ⟨p', δ', hδ'⟩ := hK'
  have e := isoTriangleOfIso₁₂ _ _ (rot_of_distTriang _ hδ) (rot_of_distTriang _ hδ')
    (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact ⟨(shiftFunctor D (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩

end CategoryTheory.Pretriangulated

/-! ## The formula -/

namespace AlgebraicGeometry.RingedSite

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] hasFiniteBiproducts_sheafOfModules
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf

section Formula

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The derived completion along `ℐ = (f_1, …, f_r)` is a derived limit of the tower
`n ↦ R𝑆heafHom_𝒪(K^n, K)`**, the derived completion being the reflector of [Stacks, Tag 099F]
at `ℐ` and `K^n` the Koszul complex on `f_1^{n+1}, …, f_r^{n+1}`. -/
theorem isDerivedLimit_derivedSheafHomSystem_derivedCompletion
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦
      (derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)] :
    IsDerivedLimit (derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K)
      ((derivedCompletion X (generatedIdealSheaf f)).obj K) :=
  IsDerivedLimit.of_isoObj (reflectorIsoCompletionFunctor X f K).symm
    (isDerivedLimit_derivedSheafHom_of_isHomotopyColimit' X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K (isHomotopyColimit_koszulPowerSystem X f))

variable (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- **`RΓ(𝒞, K^∧) = R lim_n RΓ(𝒞, R𝑆heafHom_𝒪(K^n, K))`**, for `𝒪` a sheaf of `A`-algebras on a
ringed site and `K` an object of `D(𝒪)`, where `K^∧` is the derived completion along the ideal
sheaf `ℐ = (f_1, …, f_r)`, the reflector of [Stacks, Tag 099F]: the image of the tower
`n ↦ R𝑆heafHom_𝒪(K^n, K)` under `RΓ(𝒞, -)` has a product, and `RΓ(𝒞, K^∧)` is a derived limit of
it. -/
theorem isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦
      (derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)] :
    ∃ _ : HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
        (koszulPowerSystem X f ⋙ DerivedCategory.Q) K ⋙
          derivedGlobalSectionsOverUnbounded X A ρ).obj (op n),
      IsDerivedLimit (derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K ⋙
          derivedGlobalSectionsOverUnbounded X A ρ)
        ((derivedGlobalSectionsOverUnbounded X A ρ).obj
          ((derivedCompletion X (generatedIdealSheaf f)).obj K)) :=
  isDerivedLimit_map_derivedGlobalSectionsOverUnbounded X A ρ
    (derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K) _
    (isDerivedLimit_derivedSheafHomSystem_derivedCompletion X f K)

end Formula

end AlgebraicGeometry.RingedSite

end

