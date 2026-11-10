module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageEssentialSurjectivityModules
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.AbelianULiftIntConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.Annihilator
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible abelian sheaves on a limit of schemes come from a finite stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms. Every constructible abelian sheaf on `X_étale` is, up to
isomorphism, the inverse image of a constructible abelian sheaf on some `(X_i)_étale`. This is the
essential surjectivity assertion of Tag 09YU, clause (2).

## Main results

* `Stacks.EtaleCohomology.exists_isConstructibleEtaleAbelianSheaf_etaleAbelianInverseImage_iso` —
  **Stacks 09YU, the essential-surjectivity assertion**, clause (2).

## Implementation notes

The source proves clause (2) like clause (1). Here it is deduced from clause (3) at the Noetherian
ring `Λ = ULift.{u + 1} ℤ`,
`Stacks.EtaleCohomology.exists_isConstructibleEtaleModule_etaleModuleInverseImage_iso`, through the
equivalence `Stacks.EtaleCohomology.etaleModuleULiftIntEquivalence` of abelian sheaves with sheaves
of `ULift ℤ`-modules. That equivalence carries constructible abelian sheaves to constructible
sheaves of modules but not conversely: the sheaf of modules found on the stage need not be torsion.
It is replaced by its `n`-torsion, for an integer `n > 0` killing `ℱ` (a constructible sheaf on a
quasi-compact scheme is killed by one), which is again constructible (Tag 03RZ), is torsion, hence
a constructible abelian sheaf, and still has inverse image `ℱ`, inverse image being exact.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **Stacks 09YU, the essential-surjectivity assertion, clause (2).** Let `X = lim X_i` be the
limit of a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms. Every constructible abelian sheaf on `X_étale` is isomorphic to the inverse
image of a constructible abelian sheaf on some `(X_i)_étale`.

The sheaf `ℱ` is a constructible torsion sheaf of `ULift ℤ`-modules `𝒢`
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj`),
killed by some `n > 0` since `X` is quasi-compact
(`Stacks.EtaleCohomology.exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule`). Clause (3) at
`ULift ℤ` gives a constructible `𝒢₀` on a stage with `π⁻¹𝒢₀ ≅ 𝒢`; the kernel `𝒢₀[n]` of
multiplication by `n` is constructible and killed by `n`, so its underlying abelian sheaf is a
constructible abelian sheaf
(`Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt`), and
`π⁻¹(𝒢₀[n]) ≅ 𝒢[n] = 𝒢`, inverse image being exact and commuting with forgetting the module
structure. -/
theorem exists_isConstructibleEtaleAbelianSheaf_etaleAbelianInverseImage_iso
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    ∃ (i : Iᵒᵖ) (F₀ : Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F₀ ∧
        Nonempty ((etaleAbelianInverseImage.{u, 0} (c.π.app i)).obj F₀ ≅ F) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let E := etaleModuleULiftIntEquivalence.{0} c.pt
  let G := E.inverse.obj F
  have hG : IsConstructibleEtaleModule (ULift.{u + 1} ℤ) G :=
    isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj F hF
  have hGt : IsTorsionEtaleModule (ULift.{u + 1} ℤ) c.pt G :=
    (Stacks.Torsion.torsionSheafProperty _).prop_of_iso (E.counitIso.app F).symm
      (torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf F hF)
  obtain ⟨n, hn, -, hnG⟩ := exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule
    (ULift.{u + 1} ℤ) 1 G hG ((isTorsionPrimeToEtaleModule_one_iff _ _ G).2 hGt)
  obtain ⟨i, G₀, hG₀, ⟨e⟩⟩ :=
    exists_isConstructibleEtaleModule_etaleModuleInverseImage_iso (ULift.{u + 1} ℤ) D c hc G hG
  let φ : G₀ ⟶ G₀ := n • 𝟙 G₀
  have hK : IsConstructibleEtaleModule (ULift.{u + 1} ℤ) (kernel φ) :=
    (IsConstructibleEtaleModule (ULift.{u + 1} ℤ)).prop_kernel φ hG₀ hG₀
  have hnK : n • 𝟙 (kernel φ) = 0 := by
    rw [← cancel_mono (kernel.ι φ), zero_comp, Preadditive.nsmul_comp, Category.id_comp]
    simpa [φ] using kernel.condition φ
  let P := etaleModuleInverseImage.{u, u + 1} (ULift.{u + 1} ℤ) (c.π.app i)
  have hP : P.map φ = 0 := by
    rw [show P.map φ = e.hom ≫ (n • 𝟙 G) ≫ e.inv by simp [φ, P], hnG, zero_comp, comp_zero]
  let eK : P.obj (kernel φ) ≅ G :=
    PreservesKernel.iso P φ ≪≫ kernelIsoOfEq hP ≪≫ kernelZeroIsoSource ≪≫ e
  exact ⟨i, (etaleModuleForgetAb.{u, u + 1} (ULift.{u + 1} ℤ) (D.obj i)).obj (kernel φ),
    isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt _ hK
      (isTorsionEtaleModule_of_nsmul_id_eq_zero (ULift.{u + 1} ℤ) hn hnK),
    ⟨asIso ((etaleModuleInverseImageForget.{u, u + 1} (ULift.{u + 1} ℤ)
        (c.π.app i)).app (kernel φ)) ≪≫
      (etaleModuleForgetAb.{u, u + 1} (ULift.{u + 1} ℤ) c.pt).mapIso eK ≪≫ E.counitIso.app F⟩⟩

end Stacks.EtaleCohomology

end
