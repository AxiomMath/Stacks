module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosedImageGenericLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The cokernel of the extended generators is killed by a power of the ideal

In the proof of [Stacks, Tag 0GUZ] the maps `s'_i : ℐ^{n_i} ⟶ 𝒢` restrict, over `V = Y ∖ V(ℐ)`,
to generators of `𝒢|_V`.  So the cokernel `𝒬` of `⨁ s'_i : ⨁ ℐ^{n_i} ⟶ 𝒢` vanishes on `V`, its
support lies in `V(ℐ)`, and by [Stacks, Tag 07UK] it is killed by a power `ℐ^m`.  The direct image
along the affine morphism `π` keeps `π_*𝒬` the cokernel of `π_*(⨁ s'_i)`.

These are the two inputs `hK` and `hcok` of
`AlgebraicGeometry.Space.epi_etaleModulePullback_map_comp_counit_of_killed`.

## Main results

* `AlgebraicGeometry.Space.idealSheafPow_eq_idealPowSubmodule`: the two spellings of `ℐⁿ`.
* `AlgebraicGeometry.Space.exists_factor_modulePushforward_map_cokernelπ`: an affine direct image
  keeps the cokernel of a map of quasi-coherent modules with quasi-coherent kernel of its
  cokernel.
* `AlgebraicGeometry.Space.exists_idealPowModule_homs_cokernel_smul_eq_zero`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The abelian structure on modules, pinned at the universes in use: instance search otherwise
tries an instance at a module universe it cannot unify with `u` and stops there. -/
noncomputable local instance (priority := high) abelianModules_resolutionPropertyCokernel
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-- **The power `ℐⁿ` of `AlgebraicGeometry.Space.idealSheafPowPushforward` is the submodule
`ℐⁿ𝒪` of Stacks 07UM.**  Both are the sheafified `n`-th power of `ℐ`, by
`AlgebraicGeometry.Space.idealSheafPow_eq_idealPow` and `Stacks.Sites.idealSmul_top_eq`. -/
theorem idealSheafPow_eq_idealPowSubmodule (Z : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Z)).Submodule) (n : ℕ) :
    SheafOfModules.idealSheafPow I n =
      idealPowSubmodule I n (SheafOfModules.unit (structureRingSheaf B S hS Z)) :=
  Eq.trans (idealSheafPow_eq_idealPow B S hS Z I n)
    (Stacks.Sites.idealSmul_top_eq.{u, u + 1, u} _).symm

/-- **An affine direct image keeps a cokernel.**  For an affine `h` and a map `ψ : 𝒜 ⟶ 𝒢` of
quasi-coherent modules whose cokernel and the kernel of the cokernel map are quasi-coherent, every
map out of `h_*𝒢` killing `h_*ψ` factors through `h_*(coker ψ)`.

`ψ` factors as an epimorphism `𝒜 ⟶ 𝒦` followed by `𝒦 = ker(𝒢 ⟶ coker ψ) ⟶ 𝒢`; the direct image
keeps the epimorphism (Stacks 03DW over affine charts) and the short exact sequence
`0 ⟶ 𝒦 ⟶ 𝒢 ⟶ coker ψ ⟶ 0`, being a right adjoint for the kernel. -/
theorem exists_factor_modulePushforward_map_cokernelπ {Z W : AlgebraicSpaces B S hS} (h : Z ⟶ W)
    (hh : IsAffineHom B S hS h.hom) {A G : Modules.{u, u} B S hS Z.1 Z.2} (ψ : A ⟶ G)
    (hA : A.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite)
    (hK : (kernel (cokernel.π ψ)).IsQuasicoherentOnSite)
    (hQ : (cokernel ψ).IsQuasicoherentOnSite) {T : Modules.{u, u} B S hS W.1 W.2}
    (d : (modulePushforward B S hS h).obj G ⟶ T)
    (hd : (modulePushforward B S hS h).map ψ ≫ d = 0) :
    ∃ d'' : (modulePushforward B S hS h).obj (cokernel ψ) ⟶ T,
      d = (modulePushforward B S hS h).map (cokernel.π ψ) ≫ d'' := by
  have he : Epi (kernel.lift (cokernel.π ψ) ψ (cokernel.condition ψ)) :=
    Stacks.SheafOfModules.FiniteTypeKernel.epi_kernelLift_of_isColimit ψ (cokernel.π ψ) _
      (cokernelIsCokernel ψ)
  have he' : Epi ((modulePushforward B S hS h).map
      (kernel.lift (cokernel.π ψ) ψ (cokernel.condition ψ))) :=
    epi_modulePushforward_map_of_isAffineHom h hh hA hK _
  have hk : (modulePushforward B S hS h).map (kernel.ι (cokernel.π ψ)) ≫ d = 0 := by
    rw [← cancel_epi ((modulePushforward B S hS h).map
      (kernel.lift (cokernel.π ψ) ψ (cokernel.condition ψ))), ← Functor.map_comp_assoc,
      kernel.lift_ι, hd, comp_zero]
  let SC := ShortComplex.mk (kernel.ι (cokernel.π ψ)) (cokernel.π ψ) (kernel.condition _)
  have hSE : SC.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π ψ)) }
  have : PreservesLimits (modulePushforward B S hS h) :=
    (modulePullbackAdjunction B S hS h).rightAdjoint_preservesLimits
  have hfk := KernelFork.mapIsLimit _ hSE.fIsKernel (modulePushforward B S hS h)
  have hSE' : (SC.map (modulePushforward B S hS h)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ hfk
      mono_f := mono_of_isLimit_fork hfk
      epi_g := epi_modulePushforward_map_of_isAffineHom h hh hG hQ (cokernel.π ψ) }
  obtain ⟨d'', hd''⟩ := CokernelCofork.IsColimit.desc' hSE'.gIsCokernel d hk
  exact ⟨d'', hd''.symm⟩

variable (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **The cokernel of the extended generators is killed by a power of `ℐ`.**  For a coherent
`𝒪_Y`-module `𝒢` in the situation of Stacks 0GUY with `X` Noetherian there are finitely many maps
`s'_i : ℐ^{n_i}𝒪_Y ⟶ 𝒢` (from
`AlgebraicGeometry.Space.exists_idealPowModule_homs_eq_zero_of_restrict`) and an `m` with
`ℐ^m · coker(⨁ s'_i) = 0` section by section; the cokernel is coherent.

The cokernel restricts to zero on `U = Y ∖ V(ℐ)`, restriction being a left adjoint, so its support
misses the unit locus of `ℐ` (support commutes with the flat pullback along `U ⟶ Y`), and Stacks
07UK gives `m`.  The exponents `n_i` can be taken `≥ N` for any prescribed `N`, by
`AlgebraicGeometry.Space.exists_idealPowModule_homs_eq_zero_of_restrict_of_le`. -/
theorem exists_idealPowModule_homs_cokernel_smul_eq_zero_of_le (hX : IsNoetherian B S hS hZ X.1)
    (G : Modules.{u, u} B S hS D.Y.1 D.Y.2) (hG : IsCoherent B S hS D.Y.1 D.Y.2 G) (N : ℕ) :
    ∃ (r : ℕ) (n : Fin r → ℕ) (_ : HasBiproduct fun i => idealPowModule D.I (n i)
        (SheafOfModules.unit (structureRingSheaf B S hS D.Y)))
      (Ψ : ∀ i, idealPowModule D.I (n i)
        (SheafOfModules.unit (structureRingSheaf B S hS D.Y)) ⟶ G) (m : ℕ), (∀ i, N ≤ n i) ∧
      IsCoherent B S hS D.Y.1 D.Y.2 (⨁ fun i => idealPowModule D.I (n i)
        (SheafOfModules.unit (structureRingSheaf B S hS D.Y))) ∧
      IsCoherent B S hS D.Y.1 D.Y.2 (cokernel (biproduct.desc Ψ)) ∧
      ∀ (W : (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).Cᵒᵖ)
        (a : (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj.obj W),
        a ∈ (SheafOfModules.idealSheafPow D.I m).obj W →
          ∀ q : (cokernel (biproduct.desc Ψ)).val.obj W, a • q = 0 := by
  obtain ⟨r, n, Ψ, hN, hΨ⟩ :=
    exists_idealPowModule_homs_eq_zero_of_restrict_of_le B S hS hZ X hqc hqs D hX G hG N
  have hB : HasBiproduct fun i => idealPowModule D.I (n i)
      (SheafOfModules.unit (structureRingSheaf B S hS D.Y)) := HasBiproduct.of_hasProduct _
  have hPow : ∀ i, IsCoherent B S hS D.Y.1 D.Y.2 (idealPowModule D.I (n i)
      (SheafOfModules.unit (structureRingSheaf B S hS D.Y))) := fun i =>
    (isCoherent.{u, u} B S hS _ _).prop_of_iso
      (eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
        (idealSheafPow_eq_idealPowSubmodule B S hS D.Y D.I (n i))))
      (isCoherent_idealSheafPow_of_resolutionSituation B S hS hZ X hqc hqs D hX (n i))
  have hsum := isCoherent_biproduct B S hS D.Y.1 D.Y.2 _ hPow
  have hQ := isCoherent_cokernel B S hS D.Y.1 D.Y.2 hsum hG (biproduct.desc Ψ)
  have hι := isEtale_idealComplementι B S hS D.Y D.I
  -- the cokernel vanishes on the open complement
  have := (etaleModulePullbackAdjunction B S hS (idealComplementι B S hS D.Y D.I) hι).isLeftAdjoint
  have hc : ∀ i, Ψ i ≫ cokernel.π (biproduct.desc Ψ) = 0 := fun i => by
    rw [← biproduct.ι_desc Ψ i, Category.assoc, cokernel.condition, comp_zero]
  have h0 : (etaleModulePullback B S hS (idealComplementι B S hS D.Y D.I) hι).map
      (cokernel.π (biproduct.desc Ψ)) = 0 :=
    hΨ _ fun i => by
      show (etaleModulePullback B S hS (idealComplementι B S hS D.Y D.I) hι).map (Ψ i) ≫
        (etaleModulePullback B S hS (idealComplementι B S hS D.Y D.I) hι).map
          (cokernel.π (biproduct.desc Ψ)) = 0
      rw [← Functor.map_comp, hc i, Functor.map_zero]
  have hz : IsZero ((etaleModulePullback B S hS (idealComplementι B S hS D.Y D.I) hι).obj
      (cokernel (biproduct.desc Ψ))) := IsZero.of_epi_eq_zero _ h0
  -- so its support lies in the zero locus, and Stacks 07UK applies
  obtain ⟨m, hm⟩ := (exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus B S hS hZ
    D.Y (isNoetherian_Y_of_resolutionSituation B S hS hZ X hqc hqs D hX) _ hQ D.I
    D.isFiniteTypeQuasicoherent_I.1).2 (by
      intro y hy hyU
      rw [← range_pointsMap_idealComplementι B S hS D.Y D.I] at hyU
      obtain ⟨u, rfl⟩ := hyU
      have hu := (Set.ext_iff.1 (supportOfSheaf_modulePullback_eq_preimage_of_isFlat B S hS
        (idealComplementι B S hS D.Y D.I) (isFlat_of_isEtale B S hS hι)
        (cokernel (biproduct.desc Ψ))) u).2 hy
      rwa [supportOfSheaf_eq_of_iso B S hS _
        ((modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS D.Y D.I) hι).app _),
        supportOfSheaf_eq_empty_of_isZero B S hS _ hz] at hu)
  exact ⟨r, n, hB, Ψ, m, hN, hsum, hQ,
    smul_eq_zero_of_idealSmul_idealPow_top_eq_bot B S hS D.Y D.I m _ hm⟩

/-- **The cokernel of the extended generators is killed by a power of `ℐ`**:
`AlgebraicGeometry.Space.exists_idealPowModule_homs_cokernel_smul_eq_zero_of_le` with no lower
bound on the exponents. -/
theorem exists_idealPowModule_homs_cokernel_smul_eq_zero (hX : IsNoetherian B S hS hZ X.1)
    (G : Modules.{u, u} B S hS D.Y.1 D.Y.2) (hG : IsCoherent B S hS D.Y.1 D.Y.2 G) :
    ∃ (r : ℕ) (n : Fin r → ℕ) (_ : HasBiproduct fun i => idealPowModule D.I (n i)
        (SheafOfModules.unit (structureRingSheaf B S hS D.Y)))
      (Ψ : ∀ i, idealPowModule D.I (n i)
        (SheafOfModules.unit (structureRingSheaf B S hS D.Y)) ⟶ G) (m : ℕ),
      IsCoherent B S hS D.Y.1 D.Y.2 (⨁ fun i => idealPowModule D.I (n i)
        (SheafOfModules.unit (structureRingSheaf B S hS D.Y))) ∧
      IsCoherent B S hS D.Y.1 D.Y.2 (cokernel (biproduct.desc Ψ)) ∧
      ∀ (W : (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).Cᵒᵖ)
        (a : (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj.obj W),
        a ∈ (SheafOfModules.idealSheafPow D.I m).obj W →
          ∀ q : (cokernel (biproduct.desc Ψ)).val.obj W, a • q = 0 := by
  obtain ⟨r, n, hB, Ψ, m, -, h⟩ :=
    exists_idealPowModule_homs_cokernel_smul_eq_zero_of_le B S hS hZ X hqc hqs D hX G hG 0
  exact ⟨r, n, hB, Ψ, m, h⟩

end AlgebraicGeometry.Space

end
