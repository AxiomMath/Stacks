module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AbelianUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparisonEpi
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian

/-!
# The restriction `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` is exact

Let `S` be a scheme and `(Sch/S)_τ` a chosen big site over `S`, for `τ` any of the five
topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`. The functor
`v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`, `𝓖 ↦ 𝓖|_{S_Zar}`, of [Stacks, Tag 06VN] is exact. This is the
exactness the source invokes in the proof of [Stacks, Tag 06ZN] ("the kernel of the exact
functor `v`").

## Main results

* `Stacks.Adequate.BigSite.surjective_app_opensToBig_of_shortExact` — for a short exact sequence
  `0 → 𝓕' → 𝓕 → 𝓕'' → 0` of `𝒪`-modules with `𝓕'` adequate, the map `𝓕(U) → 𝓕''(U)` is
  surjective for every affine open `U ⊆ S`, because `H¹(U, 𝓕') = 0` by [Stacks, Tag 06VM] (3).
* `Stacks.Adequate.BigSite.epi_zariskiRestrictModule_map_of_shortExact` — hence
  `𝓕|_{S_Zar} → 𝓕''|_{S_Zar}` is an epimorphism of `𝒪_S`-modules, the affine opens forming a
  basis of `S`.
* `Stacks.Adequate.BigSite.additive_restrictModuleQCoh`,
  `Stacks.Adequate.BigSite.preservesFiniteLimits_restrictModuleQCoh` and
  `Stacks.Adequate.BigSite.preservesFiniteColimits_restrictModuleQCoh` — `v` is additive and
  exact.

## Implementation notes

Left exactness is formal: `v` is the direct image of sheaves of modules along a morphism of
ringed sites composed with the inclusion of `Adeq(𝒪)`, both of which preserve finite limits
([Stacks, Tag 06VQ] (2) for the inclusion). Right exactness is the content: a short exact
sequence of adequate modules is short exact in all `𝒪`-modules ([Stacks, Tag 06VQ] (2)), its
kernel is adequate, so sections over the affine opens of `S` are surjective by the vanishing of
`H¹` on affine objects ([Stacks, Tag 06VM] (3),
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`), and a map of
`𝒪_S`-modules which is surjective on the sections over a basis of opens is an epimorphism
(`Stacks.FundamentalGroup.epi_of_isLocallySurjective`).

The abelian structure on `Adeq(𝒪)` is `Stacks.Adequate.abelian_adequate`, installed with
`let` inside the proofs; the statements here involve only the preadditive structure the full
subcategory inherits. The abelian structure on `QCoh(𝒪_S)` is the instance
`AlgebraicGeometry.quasicoherentModules_abelian`.

## References

* [Stacks Project, Tag 06ZN](https://stacks.math.columbia.edu/tag/06ZN)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

attribute [local instance] HasDerivedCategory.standard

/-- For a short exact sequence `0 → 𝓕' → 𝓕 → 𝓕'' → 0` of `𝒪`-modules on a chosen big site
over `S` whose first term is adequate, the map `𝓕(U) → 𝓕''(U)` is surjective on the sections
over every affine open `U ⊆ S`: the obstruction lies in `H¹(U, 𝓕')`, which vanishes by
[Stacks, Tag 06VM] (3). -/
public theorem BigSite.surjective_app_opensToBig_of_shortExact
    (T : ShortComplex (SheafOfModules.{u} B.structureSheaf)) (hT : T.ShortExact)
    (h₁ : IsAdequate B T.X₁) (U : S.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (T.g.val.app (op (B.opensToBig.obj U))) := by
  have := hT.mono_f
  have := hT.epi_g
  let Φ := SheafOfModules.toSheaf.{u} B.structureSheaf
  have hS : (T.map Φ).ShortExact :=
    ShortComplex.ShortExact.mk' ((T.map Φ).exact_of_f_is_kernel
      (isLimitForkMapOfIsLimit' Φ T.zero hT.fIsKernel)) (Φ.map_mono _) (Φ.map_epi _)
  have : IsAffine (B.opensToBig.obj U).left.obj := hU
  let Γ := (sheafSections B.topology AddCommGrpCat.{u}).obj (op (B.opensToBig.obj U))
  have : PreservesFiniteLimits Γ :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf B.topology AddCommGrpCat.{u} ⋙
      (evaluation _ _).obj (op (B.opensToBig.obj U))))
  exact (AddCommGrpCat.epi_iff_surjective _).1
    (Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one Γ hS
      (B.isZero_rightDerived_sections_of_isAdequate.{u, u} T.X₁ h₁ _ 1 one_pos))

/-- For a short exact sequence `0 → 𝓕' → 𝓕 → 𝓕'' → 0` of `𝒪`-modules on a chosen big site
over `S` whose first term is adequate, the restriction `𝓕|_{S_Zar} → 𝓕''|_{S_Zar}` is an
epimorphism of `𝒪_S`-modules: it is surjective on the sections over every affine open, and the
affine opens form a basis of the topology of `S`. -/
public theorem BigSite.epi_zariskiRestrictModule_map_of_shortExact
    (T : ShortComplex (SheafOfModules.{u} B.structureSheaf)) (hT : T.ShortExact)
    (h₁ : IsAdequate B T.X₁) : Epi (B.zariskiRestrictModule.map T.g) := by
  refine Stacks.FundamentalGroup.epi_of_isLocallySurjective _ fun U t x hx => ?_
  obtain ⟨V, hVmem, hxV, hVU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hx
  obtain ⟨s, hs⟩ := B.surjective_app_opensToBig_of_shortExact T hT h₁ V hVmem
    ((B.zariskiRestrictModule.obj T.X₃).presheaf.map (homOfLE hVU).op t)
  exact ⟨V, hVU, hxV, s, hs⟩

/-- **`v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` is additive**: it is the additive restriction to the small
Zariski site lifted to the quasi-coherent modules, and additivity descends along the faithful
inclusion of a full subcategory. -/
public instance BigSite.additive_restrictModuleQCoh : B.restrictModuleQCoh.Additive :=
  letI : (B.restrictModuleQCoh ⋙ (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι).Additive :=
    inferInstanceAs ((adequate.{u, u} B).ι ⋙ B.restrictModuleOfSheaf).Additive
  Functor.additive_of_comp_faithful _ (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι

/-- **`v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` is left exact**: the inclusion of the adequate modules preserves
finite limits ([Stacks, Tag 06VQ] (2)), so does the direct image along the morphism of ringed
sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`, and the inclusion of `QCoh(𝒪_S)` reflects them. -/
public instance BigSite.preservesFiniteLimits_restrictModuleQCoh :
    PreservesFiniteLimits B.restrictModuleQCoh := by
  have : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
  have : PreservesFiniteLimits
      (B.restrictModuleQCoh ⋙ (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι) :=
    inferInstanceAs (PreservesFiniteLimits ((adequate.{u, u} B).ι ⋙ B.restrictModuleOfSheaf))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι

/-- **`v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` is right exact.** A short exact sequence of adequate modules is
short exact in all `𝒪`-modules by [Stacks, Tag 06VQ] (2); its first term being adequate, the
restriction of its second map is an epimorphism
(`Stacks.Adequate.BigSite.epi_zariskiRestrictModule_map_of_shortExact`), and `v` is left exact. -/
public instance BigSite.preservesFiniteColimits_restrictModuleQCoh :
    PreservesFiniteColimits B.restrictModuleQCoh := by
  let := abelian_adequate B
  refine (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2 fun T hT => ⟨?_, ?_⟩
  · exact ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).1 inferInstance
      T hT).1
  · have : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    have : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.epi_of_epi_map
      (B.epi_zariskiRestrictModule_map_of_shortExact (T.map (adequate.{u, u} B).ι)
        (hT.map_of_exact _) T.X₁.property)

end Stacks.Adequate

end
