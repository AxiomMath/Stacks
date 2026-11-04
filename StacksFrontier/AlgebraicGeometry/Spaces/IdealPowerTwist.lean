module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerGradedFamily
public import StacksFrontier.CategoryTheory.Abelian.JointlyEpiSubobjectTransport

/-!
# Powers of an ideal sheaf along an exact linear functor

Let `I ⊆ 𝒪_X` be a sheaf of ideals generated, on the affine étale charts of an algebraic space
`X`, by finitely many global functions `x₁, …, x_r`, and let `Φ` be an exact additive endofunctor
of the `𝒪_X`-modules which commutes with multiplication by global functions — the twist
`− ⊗ ℒ` by an invertible module is the example.  Then `Φ (Iⁿ M) ≅ Iⁿ (Φ M)` over `Φ M`, and
consequently `Φ (IⁿM/Iⁿ⁺¹M) ≅ Iⁿ(Φ M)/Iⁿ⁺¹(Φ M)`.

Both sides are images: `Iⁿ⁺¹ M` is the image of the multiplications `xᵢ : Iⁿ M ⟶ M`
(`AlgebraicGeometry.Space.eq_zero_of_comp_idealSmulHom_eq_zero`), and an exact functor carries
images to images (`Stacks.Abelian.subobjectIsoOfJointlyEpi`).

## Main definitions

* `AlgebraicGeometry.Space.idealPowTwistIso`: `Φ (Iⁿ M) ≅ Iⁿ (Φ M)`.
* `AlgebraicGeometry.Space.idealPowGradedPieceTwistIso`: `Φ (IⁿM/Iⁿ⁺¹M) ≅ Iⁿ(Φ M)/Iⁿ⁺¹(Φ M)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules (globalSmul)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

section

variable (I : IdealSheaves B S hS X.1 X.2) {r : ℕ}
  (x : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
  (hx : ∀ i (W : SmallEtale B S hS X.1), (x i).1 (op W) ∈ I.obj (op W))
  (hgen : ∀ A : SmallEtale B S hS X.1,
    IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
    ∀ b ∈ I.obj (op A), ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op A), b = ∑ i, c i * (x i).1 (op A))
  (Φ : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2) [Φ.Additive]
  [Φ.PreservesEpimorphisms] [Φ.PreservesMonomorphisms]
  (hΦ : ∀ (a : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (M : Modules.{u, u} B S hS X.1 X.2), Φ.map (globalSmul _ a M) = globalSmul _ a (Φ.obj M))
  (M : Modules.{u, u} B S hS X.1 X.2)

/-- The inclusion of `I⁰ M = M` has a section. -/
def idealPowZeroSection : M ⟶ (idealPowSubmodule I 0 M).toSheafOfModules :=
  (idealPowSubmodule I 0 M).factorThru (𝟙 M) fun W y => by
    rw [idealPowSubmodule_zero]
    exact Stacks.SheafOfModules.mem_top_obj y

/-- The section `idealPowZeroSection` composed with the inclusion `I⁰ M ⟶ M` is the identity of
`M`. -/
@[reassoc (attr := simp)]
theorem idealPowZeroSection_ι : idealPowZeroSection I M ≫ (idealPowSubmodule I 0 M).ι = 𝟙 M :=
  (idealPowSubmodule I 0 M).factorThru_ι _ _

/-- The inclusion `I⁰ M ⟶ M` composed with `idealPowZeroSection` is the identity of `I⁰ M`. -/
theorem ι_idealPowZeroSection :
    (idealPowSubmodule I 0 M).ι ≫ idealPowZeroSection I M = 𝟙 _ := by
  rw [← cancel_mono (idealPowSubmodule I 0 M).ι, Category.assoc, idealPowZeroSection_ι,
    Category.comp_id, Category.id_comp]

include hx hgen hΦ in
/-- An isomorphism `Φ (Iⁿ M) ≅ Iⁿ (Φ M)` together with its compatibility with the inclusions into
`Φ M`. -/
def idealPowTwistIsoAux : (n : ℕ) →
    {ψ : Φ.obj (idealPowSubmodule I n M).toSheafOfModules ≅
        (idealPowSubmodule I n (Φ.obj M)).toSheafOfModules //
      ψ.hom ≫ (idealPowSubmodule I n (Φ.obj M)).ι = Φ.map (idealPowSubmodule I n M).ι}
  | 0 => ⟨Stacks.Abelian.subobjectIsoOfJointlyEpi Φ (J := Unit)
      (fun _ => idealPowZeroSection I M) (idealPowSubmodule I 0 M).ι
      (fun Q g hg => by
        rw [← Category.id_comp g, ← ι_idealPowZeroSection, Category.assoc, hg (), comp_zero])
      (fun _ => idealPowZeroSection I (Φ.obj M)) (idealPowSubmodule I 0 (Φ.obj M)).ι
      (fun Q g hg => by
        rw [← Category.id_comp g, ← ι_idealPowZeroSection, Category.assoc, hg (), comp_zero])
      (fun _ => Iso.refl _) (fun _ => by
        rw [idealPowZeroSection_ι, Iso.refl_hom, idealPowZeroSection_ι, Category.id_comp,
          Φ.map_id]),
      Stacks.Abelian.subobjectIsoOfJointlyEpi_hom_comp _ _ _ _ _ _ _ _ _⟩
  | n + 1 =>
    ⟨Stacks.Abelian.subobjectIsoOfJointlyEpi Φ
      (fun i => idealPowSmulHom I M (x i) (hx i) n) (idealPowSubmodule I (n + 1) M).ι
      (fun Q g hg => eq_zero_of_comp_idealSmulHom_eq_zero I x hx hgen _ _
        (idealSmul_idealPowSubmodule I M n) g hg)
      (fun i => idealPowSmulHom I (Φ.obj M) (x i) (hx i) n)
      (idealPowSubmodule I (n + 1) (Φ.obj M)).ι
      (fun Q g hg => eq_zero_of_comp_idealSmulHom_eq_zero I x hx hgen _ _
        (idealSmul_idealPowSubmodule I (Φ.obj M) n) g hg)
      (fun _ => (idealPowTwistIsoAux n).1) (fun i => by
        have h2 := (idealPowTwistIsoAux n).2
        simp only [idealSmulHom_ι, Φ.map_comp, hΦ]
        rw [← Category.assoc, h2]),
      Stacks.Abelian.subobjectIsoOfJointlyEpi_hom_comp _ _ _ _ _ _ _ _ _⟩

/-- **`Φ (Iⁿ M) ≅ Iⁿ (Φ M)`.** -/
def idealPowTwistIso (n : ℕ) : Φ.obj (idealPowSubmodule I n M).toSheafOfModules ≅
    (idealPowSubmodule I n (Φ.obj M)).toSheafOfModules :=
  (idealPowTwistIsoAux I x hx hgen Φ hΦ M n).1

/-- The isomorphism `idealPowTwistIso` is compatible with the inclusions `Iⁿ (Φ M) ⟶ Φ M` and
`Φ (Iⁿ M) ⟶ Φ M`. -/
@[reassoc (attr := simp)]
theorem idealPowTwistIso_hom_ι (n : ℕ) :
    (idealPowTwistIso I x hx hgen Φ hΦ M n).hom ≫ (idealPowSubmodule I n (Φ.obj M)).ι =
      Φ.map (idealPowSubmodule I n M).ι :=
  (idealPowTwistIsoAux I x hx hgen Φ hΦ M n).2

/-- The isomorphisms `idealPowTwistIso` for `n + 1` and `n` commute with the inclusions
`Iⁿ⁺¹ ⊆ Iⁿ` on `M` and on `Φ M`. -/
theorem homOfLE_comp_idealPowTwistIso_hom (n : ℕ) :
    Φ.map (Stacks.SheafOfModules.Submodule.homOfLE (idealPowSubmodule_succ_le I n M)) ≫
        (idealPowTwistIso I x hx hgen Φ hΦ M n).hom =
      (idealPowTwistIso I x hx hgen Φ hΦ M (n + 1)).hom ≫
        Stacks.SheafOfModules.Submodule.homOfLE (idealPowSubmodule_succ_le I n (Φ.obj M)) := by
  rw [← cancel_mono (idealPowSubmodule I n (Φ.obj M)).ι, Category.assoc, Category.assoc,
    idealPowTwistIso_hom_ι, Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, ← Φ.map_comp,
    Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, idealPowTwistIso_hom_ι]

/-- **`Φ (IⁿM/Iⁿ⁺¹M) ≅ Iⁿ(Φ M)/Iⁿ⁺¹(Φ M)`.** -/
def idealPowGradedPieceTwistIso [PreservesFiniteColimits Φ] (n : ℕ) :
    Φ.obj (idealPowGradedPiece I M n) ≅ idealPowGradedPiece I (Φ.obj M) n :=
  PreservesCokernel.iso Φ _ ≪≫ cokernel.mapIso _ _
    (idealPowTwistIso I x hx hgen Φ hΦ M (n + 1)) (idealPowTwistIso I x hx hgen Φ hΦ M n)
    (homOfLE_comp_idealPowTwistIso_hom I x hx hgen Φ hΦ M n)

end

end AlgebraicGeometry.Space

end
