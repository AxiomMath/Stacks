module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AdicFibreKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.BaseIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhoodImmersion

/-!
# The ideal of an adic fibre is a power of `I 𝒪_X`

Let `A` be a ring, `I ⊆ A` an ideal and `X` an algebraic space over `Spec A`, with adic fibres
`ι_n : X_n = X ×_{Spec A} Spec (A / I ^ (n + 1)) ⟶ X`. The kernel ideal sheaf of `ι_n` is the
`(n + 1)`-st power of the sheaf of ideals `I 𝒪_X`, and consequently the submodule
`ker(ι_n♯) · M` of any `𝒪_X`-module `M` is `(I 𝒪_X) ^ (n + 1) M`.

This is the identification that compares the two descriptions of a formal coherent sheaf in
Stacks 08BF: systems `(F_n)` of coherent modules on the adic fibres, and coherent adic systems
along `I 𝒪_X` (Stacks 08BE). In `StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem`
it is the hypothesis `hker` under which the restriction to the tower of thickenings followed by
the direct image is the completion functor.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSheaf_adicFibreFstHom_eq_idealPow`: the kernel ideal
  sheaf of `ι_n` is `(I 𝒪_X) ^ (n + 1)`.
* `AlgebraicGeometry.Space.kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple`:
  `ker(ι_n♯) · M = (I 𝒪_X) ^ (n + 1) M` for every `𝒪_X`-module `M`.

## Implementation notes

Both sheaves of ideals are determined by their sections over the affine étale charts
(`AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine`). There the kernel of `ι_n`
is the extension of `I ^ (n + 1)`
(`AlgebraicGeometry.Space.kernelIdealSheaf_adicFibreFstHom_obj_of_isAffine`), and the sections of
the power of the quasi-coherent ideal `I 𝒪_X` are the power of its sections
(`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isAffine`), which are the
extension of `I` (`AlgebraicGeometry.Space.baseIdealSheaf_obj_of_isAffine`).

## References

* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
* [Stacks Project, Tag 08B7](https://stacks.math.columbia.edu/tag/08B7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))

/-- On an affine étale chart, the sections of the `(n + 1)`-st power of `I 𝒪_X` are the
`(n + 1)`-st power of the extension of `I`. -/
theorem idealPow_baseIdealSheaf_obj_of_isAffine (n : ℕ) (V : SmallEtale B (Spec (.of A)) hA X)
    (hV : IsAffine ((SmallEtale.toOver B (Spec (.of A)) hA X ⋙
      BigFppfOver.toScheme B (Spec (.of A)) hA).obj V)) :
    (Stacks.Sites.idealPow (baseIdealSheaf A ⟨X, hX⟩ I) (n + 1)).obj (op V) =
      Ideal.map (chartBaseRingHom A ⟨X, hX⟩ V) I ^ (n + 1) := by
  have h := chartSubmodule_idealPowSubmodule_eq_of_isAffine B (Spec (.of A)) hA X hX
    (baseIdealSheaf A ⟨X, hX⟩ I) (unitModule B (Spec (.of A)) hA hX) isCartesianOnAffineCharts_unit
    (isCartesianOnAffineCharts_baseIdealSheaf A ⟨X, hX⟩ I) (n + 1) hV
  rw [idealPowSubmodule_unit_eq_idealPow] at h
  change (Stacks.Sites.idealPow (baseIdealSheaf A ⟨X, hX⟩ I) (n + 1)).obj (op V) = _ at h
  refine h.trans ?_
  change chartSectionIdeal B (Spec (.of A)) hA X hX (baseIdealSheaf A ⟨X, hX⟩ I) V ^ (n + 1) •
    (⊤ : Ideal (chartRing B (Spec (.of A)) hA X hX V)) = _
  rw [smul_eq_mul, Ideal.mul_top]
  exact congrArg (· ^ (n + 1)) (baseIdealSheaf_obj_of_isAffine A ⟨X, hX⟩ I V hV)

/-- Extending the `k`-th power of an extended ideal along a second ring map is extending the
`k`-th power of the ideal along the composite. -/
theorem map_map_pow_of_comp_eq {R₀ R T : Type*} [CommRing R₀] [CommRing R] [CommRing T]
    (φ : R →+* T) (e : R₀ →+* R) (ψ : R₀ →+* T) (h : φ.comp e = ψ) (J : Ideal R₀) (k : ℕ) :
    Ideal.map φ (Ideal.map e J ^ k) = Ideal.map ψ J ^ k := by
  rw [← Ideal.map_pow, Ideal.map_map, h, Ideal.map_pow]

/-- The ring map of an étale chart to the base, read through `Γ(Spec A) ≅ A`, is the structure
ring map of the chart. -/
theorem appTop_chartToBaseObject_comp_ΓSpecIso_inv (V : SmallEtale B (Spec (.of A)) hA X) :
    ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (chartToBaseObject A B hA V)).appTop.hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom =
      chartBaseRingHom A ⟨X, hX⟩ V :=
  RingHom.ext fun _ => rfl

/-- **The kernel ideal sheaf of `ι_n : X_n ⟶ X` is `(I 𝒪_X) ^ (n + 1)`.** -/
theorem kernelIdealSheaf_adicFibreFstHom_eq_idealPow (n : ℕ) :
    kernelIdealSheaf B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f n) =
      Stacks.Sites.idealPow (baseIdealSheaf A ⟨X, hX⟩ I) (n + 1) := by
  refine structureSubmodule_ext_of_forall_isAffine B (Spec (.of A)) hA ⟨X, hX⟩ _ _
    fun V hV => ?_
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V.1.left) := hV
  rw [kernelIdealSheaf_adicFibreFstHom_obj_of_isAffine]
  refine Eq.trans ?_ (idealPow_baseIdealSheaf_obj_of_isAffine A I B hA hX n V hV).symm
  exact map_map_pow_of_comp_eq _ _ _ (appTop_chartToBaseObject_comp_ΓSpecIso_inv A B hA hX V) I
    (n + 1)

/-- **`ker(ι_n♯) · M = (I 𝒪_X) ^ (n + 1) M`** for every `𝒪_X`-module `M`: the hypothesis `hker`
of the comparison of the systems on the adic fibres with the coherent adic systems along
`I 𝒪_X`. -/
theorem kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple (n : ℕ)
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) :
    kerIdealSmul B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f n) M =
      idealPowerMultiple B (Spec (.of A)) hA X hX (baseIdealSheaf A ⟨X, hX⟩ I) (n + 1) M := by
  have hK : SheafOfModules.kerIdeal
      (structureSharp B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f n)) =
      Stacks.Sites.idealPow (baseIdealSheaf A ⟨X, hX⟩ I) (n + 1) := by
    refine Eq.trans ?_ (kernelIdealSheaf_adicFibreFstHom_eq_idealPow A I B hA hX f n)
    ext U a
    exact SheafOfModules.mem_kerIdeal _ U a
  exact (kerIdealSmul_eq_idealSmul B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f n) M).trans
    ((congrArg (fun K => Stacks.Sites.idealSmul K (⊤ : M.Submodule)) hK).trans
      (idealPowerMultiple_eq_idealPowSubmodule B (Spec (.of A)) hA X hX _ (n + 1) M).symm)

end AlgebraicGeometry.Space

end
