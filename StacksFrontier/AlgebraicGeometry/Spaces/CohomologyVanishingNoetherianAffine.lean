module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSectionApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffineness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian

/-!
# Vanishing of the first cohomology of coherent modules characterizes affine Noetherian spaces

Let `X` be a Noetherian algebraic space over a scheme `S`.  Stacks 0D2V asserts that if
`H¹(X, 𝓕) = 0` for every coherent `𝒪_X`-module `𝓕`, then `X` is an affine scheme.

The source deduces `H¹(X, 𝓕) = 0` for every quasi-coherent `𝓕` by writing `𝓕` as a filtered
colimit of coherent modules (Stacks 07UV) and commuting cohomology with the colimit
(Stacks 073E), and then applies Serre's criterion, Stacks 07V6.  Here the colimit is replaced by
a direct argument on global sections, which is all Serre's criterion
(`AlgebraicGeometry.Space.isAffineSpace_of_surjective_sectionsMap`) consumes: for an
epimorphism `g : 𝓜 → 𝓝` of quasi-coherent modules and a global section `t` of `𝓝`, the
pullback `𝓟 = 𝓜 ×_𝓝 𝒪_X` along `t` maps onto `𝒪_X`, the section `1` lifts to `𝓟` over an
affine surjective étale chart `U`, and that lift lies in a coherent submodule `𝓖 ⊆ 𝓟`
(`AlgebraicGeometry.Space.exists_isCoherent_mem_submodule_of_chart`, the core of Stacks 07UV).
Then `𝓖 → 𝒪_X` is an epimorphism with coherent kernel, so by the vanishing of `H¹` of that
kernel `1` lifts to a global section of `𝓖`, whose image in `𝓜` lifts `t`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_forall_isCoherent_isZero_rightDerived_one`:
  **Stacks 0D2V.**

## Implementation notes

Cohomology is that of `𝒪_X`-modules on the small étale site, for modules whose sections lie in
the universe of the structure sheaf, the convention of Stacks 07V6
(`AlgebraicGeometry.Space.isAffineSpace_iff_forall_isZero_rightDerived`).  "Affine scheme" is
`AlgebraicGeometry.Space.IsAffineSpace`: representable by an object of the site whose underlying
scheme is affine.

## References

* [Stacks Project, Tag 0D2V](https://stacks.math.columbia.edu/tag/0D2V)
* [Stacks Project, Tag 07V6](https://stacks.math.columbia.edu/tag/07V6)
* [Stacks Project, Tag 07UV](https://stacks.math.columbia.edu/tag/07UV)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))


attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

/-- A global section of a sheaf of modules on the small étale site which vanishes on a chart
covering the space vanishes. -/
theorem sections_eq_zero_of_val_eq_zero {X : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2} (U : SmallEtale B S hS X.1)
    (hsurj : IsSurjective B S hS U.1.hom) (s : M.sections) (hs : s.val (op U) = 0) : s = 0 := by
  ext W
  refine (SheafOfModules.Submodule.ker (𝟙 M)).isSheaf (s.val W)
    ((SmallEtale.topology B S hS X.1).superset_covering ?_
      (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 U hsurj W.unop))
  intro Z g hg
  obtain ⟨_, ⟨a⟩⟩ := hg
  have h1 : M.val.map g.op (s.val W) = s.val (op Z) := s.property g.op
  have h2 : M.val.map a.op (s.val (op U)) = s.val (op Z) := s.property a.op
  change M.val.map g.op (s.val W) = 0
  rw [h1, ← h2, hs]
  exact (ModuleCat.Hom.hom _).map_zero

/-- A morphism of sheaves of modules lands in the kernel of its cokernel. -/
private theorem val_app_mem_ker_cokernel_π {X : AlgebraicSpaces B S hS}
    {G N : Modules.{u, u} B S hS X.1 X.2} (ψ : G ⟶ N)
    (W : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ) (x : G.val.obj W) :
    ψ.val.app W x ∈ (SheafOfModules.Submodule.ker (cokernel.π ψ)).obj W := by
  change (ψ ≫ cokernel.π ψ).val.app W x = 0
  rw [cokernel.condition]
  rfl

/-- The corestriction of a morphism of sheaves of modules to the kernel of its cokernel is an
epimorphism. -/
private theorem epi_factorThru_ker_cokernel_π {X : AlgebraicSpaces B S hS}
    {G N : Modules.{u, u} B S hS X.1 X.2} (ψ : G ⟶ N) :
    Epi ((SheafOfModules.Submodule.ker (cokernel.π ψ)).factorThru ψ
      (val_app_mem_ker_cokernel_π B S hS ψ)) := by
  have hq : (SheafOfModules.Submodule.ker (cokernel.π ψ)).factorThru ψ
      (val_app_mem_ker_cokernel_π B S hS ψ) =
      Abelian.factorThruImage (C := Modules.{u, u} B S hS X.1 X.2) ψ ≫
        (SheafOfModules.Submodule.kerIsoKernel _).inv := by
    rw [← cancel_mono (SheafOfModules.Submodule.ker (cokernel.π ψ)).ι]
    simp only [SheafOfModules.Submodule.factorThru_ι, Category.assoc]
    rw [← SheafOfModules.Submodule.kerIsoKernel_hom_comp_ι, Iso.inv_hom_id_assoc]
    exact (Abelian.image.fac (C := Modules.{u, u} B S hS X.1 X.2) ψ).symm
  have h1 : Epi (Abelian.factorThruImage (C := Modules.{u, u} B S hS X.1 X.2) ψ) :=
    Abelian.instEpiFactorThruImage (C := Modules.{u, u} B S hS X.1 X.2) ψ
  have h2 : Epi (SheafOfModules.Submodule.kerIsoKernel (cokernel.π ψ)).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  rw [hq]
  exact @epi_comp _ _ _ _ _ _ h1 _ h2

/-- **Global sections are right exact on quasi-coherent modules of a Noetherian algebraic space
whose coherent modules have vanishing first cohomology.**  See the module docstring. -/
theorem surjective_sectionsMap_of_forall_isCoherent_isZero_rightDerived_one
    {X : AlgebraicSpaces B S hS} (hN : IsNoetherian B S hS hZ X.1)
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj F))
    {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N) (hg : Epi g)
    (hM : M.IsQuasicoherentOnSite) (hN' : N.IsQuasicoherentOnSite) :
    Function.Surjective (SheafOfModules.sectionsMap g) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
  have := isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS X.1 X.2
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS X.1 X.2
  have hXN : Fact (HasEtaleLocalProperty B S hS X.1 IsLocallyNoetherian) := ⟨hN.2.2⟩
  intro t
  -- a surjective affine chart, and a lift over it
  obtain ⟨U, hU, hUsurj, -⟩ := exists_surjective_isNoetherianAffineChart B S hS hZ X hN
  have hsurj : IsSurjective B S hS U.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U.1.left U.1.hom).1 hUsurj
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj U)) := hU.1
  obtain ⟨m, hm⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite g hg hM hN' U hUaff
    (t.val (op U))
  -- a coherent submodule of `M` through the lift
  obtain ⟨G, hG, hmG⟩ := exists_isCoherent_mem_submodule_of_chart B S hS hZ X hN U hUaff hsurj
    M hM U (have := hUaff; inferInstance) m
  set ψ := G.ι ≫ g
  set J := SheafOfModules.Submodule.ker (cokernel.π ψ)
  -- `t` is a section of the image of `ψ`
  have ht0 : SheafOfModules.sectionsMap (cokernel.π ψ) t = 0 := by
    refine sections_eq_zero_of_val_eq_zero B S hS U hsurj _ ?_
    change (cokernel.π ψ).val.app (op U) (t.val (op U)) = 0
    rw [← hm]
    exact val_app_mem_ker_cokernel_π B S hS ψ (op U) ⟨m, hmG⟩
  let t' : J.toSheafOfModules.sections :=
    PresheafOfModules.sectionsMk (fun W => ⟨t.val W,
      show (cokernel.π ψ).val.app W (t.val W) = 0 from congrArg (fun s => s.val W) ht0⟩)
      (fun _ _ f => Subtype.ext (t.property f))
  -- the corestriction of `ψ` to its image is an epimorphism with coherent kernel
  let q : G.toSheafOfModules ⟶ J.toSheafOfModules :=
    J.factorThru ψ (val_app_mem_ker_cokernel_π B S hS ψ)
  have hJq : J.toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (SheafOfModules.Submodule.kerIsoKernel _).symm
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_kernel _ hN'
        ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_cokernel ψ
          hG.toIsQuasicoherentOnSite hN'))
  have hqepi : Epi q := epi_factorThru_ker_cokernel_π B S hS ψ
  have hJ : IsCoherent B S hS X.1 X.2 J.toSheafOfModules :=
    isCoherent_of_epi_of_isQuasicoherentOnSite B S hS X.1 X.2 q hJq hG
  have hK : IsCoherent B S hS X.1 X.2 (kernel q) := isCoherent_kernel B S hS X.1 X.2 hG hJ q
  have hSE : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel q)
      epi_g := hqepi }
  obtain ⟨s', hs'⟩ := (show Function.Surjective (SheafOfModules.sectionsMap q) from
    (ModuleCat.epi_iff_surjective _).1
      (Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one _ hSE (h _ hK))) t'
  refine ⟨SheafOfModules.sectionsMap G.ι s', ?_⟩
  rw [← SheafOfModules.sectionsMap_comp,
    show G.ι ≫ g = q ≫ J.ι from (SheafOfModules.Submodule.factorThru_ι J ψ _).symm,
    SheafOfModules.sectionsMap_comp, hs']
  rfl

/-- **Stacks 0D2V.**  A Noetherian algebraic space all of whose coherent modules have vanishing
first cohomology is an affine scheme.

Cohomology is that of `𝒪_X`-modules on the small étale site, as in Stacks 07V6
(`AlgebraicGeometry.Space.isAffineSpace_iff_forall_isZero_rightDerived`).  Global sections are
right exact on quasi-coherent modules
(`AlgebraicGeometry.Space.surjective_sectionsMap_of_forall_isCoherent_isZero_rightDerived_one`),
which on a quasi-compact and quasi-separated space is Serre's criterion
`AlgebraicGeometry.Space.isAffineSpace_of_surjective_sectionsMap`. -/
theorem isAffineSpace_of_forall_isCoherent_isZero_rightDerived_one (X : AlgebraicSpaces B S hS)
    (hN : IsNoetherian B S hS hZ X.1)
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj F)) :
    IsAffineSpace B S hS X.1 :=
  isAffineSpace_of_surjective_sectionsMap B S hS hZ
    (fun _ _ g hg hM hN' =>
      surjective_sectionsMap_of_forall_isCoherent_isZero_rightDerived_one B S hS hZ hN h g hg hM
          hN')
    hN.1 hN.2.1

end AlgebraicGeometry.Space

end
