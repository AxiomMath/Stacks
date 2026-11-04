module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineAdequateColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineExtensionsSplitting
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness

/-!
# Closure properties of adequate modules on a big site

The adequate sheaves of modules on one of the five big `τ`-sites over a scheme `S` contain the
zero sheaf and are closed under kernels, finite products and extensions inside all sheaves of
modules on the site; and cokernels and colimits of sheaves of modules on the site are
sheafifications of the corresponding presheaf constructions. These are the inputs of
[Stacks, Tag 06VQ], whose four clauses are stated in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AbelianUnconditional.lean`, except for
clause (3), which is stated here.

## Main definitions

* `Stacks.Adequate.sheafification` and `Stacks.Adequate.toSheafification` — sheafification of
  presheaves of modules on the site and the canonical locally bijective map into it.
* `Stacks.Adequate.CokernelIsSheafified` and `Stacks.Adequate.ColimitIsSheafified` — the
  reflectivity of the sheaves of modules inside the presheaves of modules, as named
  statements.

## Main results

* `Stacks.Adequate.isAdequate_kernel` and
  `Stacks.Adequate.adequate_isClosedUnderFiniteProducts` — kernels and finite products of
  adequate modules are adequate.
* `Stacks.Adequate.shortExact_affineSections_of_isAdequate` — the affine-section functors are
  exact on a short exact sequence whose first term is adequate, by the vanishing of `H¹` on
  affines of [Stacks, Tag 06VM] (3).
* `Stacks.Adequate.isAdequate_of_shortExact` — **[Stacks, Tag 06VQ] (3).**
* `Stacks.Adequate.cokernelIsSheafified` and `Stacks.Adequate.colimitIsSheafified` — those two
  statements, proved, with no hypothesis.

## Implementation notes

The closure properties of adequacy for module-valued functors on the algebras of the site are
proved below this module: kernels, cokernels and finite products are
`Stacks.Adequate.affineAdequateKernels`, `Stacks.Adequate.affineAdequateCokernels` and
`Stacks.Adequate.affineAdequateFiniteProducts`
(`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSectionExactness.lean`),
extensions is `Stacks.Adequate.affineAdequateExtensions`
(`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineExtensionsSplitting.lean`) and
colimits is `Stacks.Adequate.affineAdequateColimits`
(`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineAdequateColimits.lean`). Kernels
and finite products are proved here for sheaves of modules of any value universe `max u m`;
clause (3) of [Stacks, Tag 06VQ] is stated at the value universe `u` of the site.

The conclusion of [Stacks, Tag 06VI] for every adequate sheaf of modules at once,
`Stacks.Adequate.affineLocalAdequacy`, is what makes two adequate sheaves of modules adequate
over a *common* affine scheme of the site.

The reflectivity of the sheaves of modules inside the presheaves of modules is not assumed.
`Stacks.Adequate.sheafification` is the left adjoint of `SheafOfModules.forget` of
`PresheafOfModules.sheafificationAdjunction`, whose counit is an isomorphism; a left adjoint
preserves colimits, so a colimit of sheaves of modules — in particular a cokernel — is the
sheafification of the colimit formed in the presheaves of modules, up to the counit. That is
`Stacks.Adequate.cokernelIsSheafified` and `Stacks.Adequate.colimitIsSheafified`.

## References

* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06V8](https://stacks.math.columbia.edu/tag/06V8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace Stacks.Adequate

open scoped ZeroObject

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-! ### Kernels and finite products of adequate modules -/

/-- The affine-section functor of the big site preserves finite limits. -/
private instance preservesFiniteLimits_affineSectionsFunctor (A : CommRingCat.{u})
    (f : Spec A ⟶ S) : PreservesFiniteLimits (affineSectionsFunctor.{u, max u m} B A f) :=
  comp_preservesFiniteLimits _ _

/-- The kernel of a map of adequate modules is adequate: kernels of sheaves of modules are
computed on sections, so the affine-section functor of the kernel is the kernel of the
affine-section functors. -/
public theorem isAdequate_kernel
    {F G : SheafOfModules.{max u m} B.structureSheaf} (φ : F ⟶ G) [HasKernel φ]
    (hF : IsAdequate B F) (hG : IsAdequate B G) :
    IsAdequate B (kernel φ) := by
  refine isAdequate_of_forall_affineSectionFunctor B (kernel φ) fun A f hA => ?_
  exact (affineAdequateKernels.{u, m} B A hA
    ((affineSectionsFunctor.{u, max u m} B A f).map φ) (affineLocalAdequacy.{u, m} B F hF A f hA)
    (affineLocalAdequacy.{u, m} B G hG A f hA)).of_iso
      (PreservesKernel.iso (affineSectionsFunctor.{u, max u m} B A f) φ)

/-- A finite product of adequate modules is adequate: products of sheaves of modules are
computed on sections. -/
public theorem isAdequate_of_isLimit_discrete
    (J : Type) [Finite J]
    (K : Discrete J ⥤ SheafOfModules.{max u m} B.structureSheaf) {c : Cone K} (hc : IsLimit c)
    (hK : ∀ j, IsAdequate B (K.obj j)) :
    IsAdequate B c.pt := by
  have := Fintype.ofFinite J
  refine isAdequate_of_forall_affineSectionFunctor B c.pt fun A f hA => ?_
  exact affineAdequateFiniteProducts.{u, m} B A hA J ‹_›
    (K ⋙ affineSectionsFunctor.{u, max u m} B A f)
    ((affineSectionsFunctor.{u, max u m} B A f).mapCone c)
    (isLimitOfPreserves (affineSectionsFunctor.{u, max u m} B A f) hc)
    fun j => affineLocalAdequacy.{u, m} B (K.obj j) (hK j) A f hA

/-- Adequacy of sheaves of modules is closed under kernels. -/
public theorem adequate_isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels (adequate.{u, max u m} B) where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (adequate.{u, max u m} B).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit (parallelPair φ 0)) hk)
      (isAdequate_kernel B φ hF hG)

/-- Adequacy of sheaves of modules is closed under finite products. -/
public theorem adequate_isClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts (adequate.{u, max u m} B) :=
  ⟨fun J _ => ObjectProperty.IsClosedUnderLimitsOfShape.mk' fun _ ⟨K, hK⟩ =>
    isAdequate_of_isLimit_discrete B J K (limit.isLimit K) hK⟩

/-! ### Exactness of affine sections on an extension of adequate modules -/

section AffineSections

attribute [local instance] HasDerivedCategory.standard

/-- The affine object of the site underlying an algebra of the site over an affine `Spec A`. -/
public instance isAffine_affineSpecOver_obj (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (Z : (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ) :
    IsAffine ((affineSpecOver B A f).obj Z).left.obj :=
  inferInstanceAs (IsAffine (Spec _))

/-- **The sections over an affine object of the site are exact on an extension of an adequate
module.** For a short exact sequence `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` of `𝒪`-modules on the site with
`𝓕₁` adequate, and every affine scheme `Spec A` of the site over `S`, the induced sequence of
affine-section functors is short exact. Sections over an object are left exact, and they are
right exact at an affine object `V` because `H¹(V, 𝓕₁) = 0` by [Stacks, Tag 06VM] (3),
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`. This is the step of the
source's proof of [Stacks, Tag 06VQ] (3). -/
public theorem shortExact_affineSections_of_isAdequate
    (T : ShortComplex (SheafOfModules.{max u m} B.structureSheaf)) (hT : T.ShortExact)
    (h₁ : IsAdequate B T.X₁) (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    (T.map (affineSectionsFunctor.{u, max u m} B A f)).ShortExact := by
  have := hT.mono_f
  have := hT.epi_g
  let Φ := SheafOfModules.toSheaf.{max u m} B.structureSheaf
  have hS : (T.map Φ).ShortExact :=
    ShortComplex.ShortExact.mk' ((T.map Φ).exact_of_f_is_kernel
      (isLimitForkMapOfIsLimit' Φ T.zero hT.fIsKernel)) (Φ.map_mono _) (Φ.map_epi _)
  refine PresheafOfModules.shortExact_of_objectwise _ fun X => ?_
  refine CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (ModuleCat.{max u m} _) AddCommGrpCat.{max u m}) ?_
  let U : B.category := (affineSpecOver B A f).obj X.unop
  let Γ := (sheafSections B.topology AddCommGrpCat.{max u m}).obj (Opposite.op U)
  have : PreservesFiniteLimits Γ :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf B.topology AddCommGrpCat.{max u m} ⋙
      (evaluation _ _).obj (Opposite.op U)))
  have := hS.mono_f
  exact (ShortComplex.ShortExact.mk' (((T.map Φ).map Γ).exact_of_f_is_kernel
    (isLimitForkMapOfIsLimit' Γ (T.map Φ).zero hS.fIsKernel)) (Γ.map_mono (T.map Φ).f)
    (Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one Γ hS
      (B.isZero_rightDerived_sections_of_isAdequate.{u, m} T.X₁ h₁ U 1 one_pos)) :
    ((T.map Φ).map Γ).ShortExact)

end AffineSections

/-- **[Stacks, Tag 06VQ] (3).** Let `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` be a short exact sequence of
`𝒪`-modules on the chosen big `τ`-site over `S`. If `𝓕₁` and `𝓕₃` are adequate, then `𝓕₂` is
adequate.

As in the source: over every affine scheme `Spec A` of the site the induced sequence of
affine-section functors is short exact, because `H¹` of the adequate `𝓕₁` vanishes on affines
([Stacks, Tag 06VM] (3), through
`Stacks.Adequate.shortExact_affineSections_of_isAdequate`); its outer terms are adequate
([Stacks, Tag 06VI]), so its middle term is adequate ([Stacks, Tag 06V8] on the algebras of the
site, `Stacks.Adequate.affineAdequateExtensions`). The values of the modules lie in the universe
of the site. -/
@[stacks 06VQ "(3)"]
public theorem isAdequate_of_shortExact
    (T : ShortComplex (SheafOfModules.{u} B.structureSheaf)) (hT : T.ShortExact)
    (h₁ : IsAdequate B T.X₁) (h₃ : IsAdequate B T.X₃) :
    IsAdequate B T.X₂ :=
  isAdequate_of_forall_affineSectionFunctor B T.X₂ fun A f hA =>
    affineAdequateExtensions.{u, u} B A hA _
      (shortExact_affineSections_of_isAdequate.{u, u} B T hT h₁ A f)
      (affineLocalAdequacy.{u, u} B T.X₁ h₁ A f hA) (affineLocalAdequacy.{u, u} B T.X₃ h₃ A f hA)

/-- Adequacy of sheaves of modules is closed under extensions. -/
public theorem adequate_isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions (adequate.{u, u} B) where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := isAdequate_of_shortExact B T hT h₁ h₃

/-! ### Sheafification on the big site -/

section Sheafify

/-- Sheafification of presheaves of modules on the chosen big site. -/
public noncomputable abbrev sheafification :
    PresheafOfModules.{max u m} B.structureSheaf.obj ⥤
      SheafOfModules.{max u m} B.structureSheaf :=
  PresheafOfModules.sheafification (𝟙 B.structureSheaf.obj)

/-- The canonical map from a presheaf of modules on the site to its sheafification. -/
public noncomputable def toSheafification
    (P : PresheafOfModules.{max u m} B.structureSheaf.obj) :
    P ⟶ ((sheafification.{u, m} B).obj P).val :=
  PresheafOfModules.toSheafify (𝟙 B.structureSheaf.obj)
    (CategoryTheory.toSheafify B.topology P.presheaf)

/-- The map into the sheafification is locally injective. -/
public instance toSheafification_isLocallyInjective
    (P : PresheafOfModules.{max u m} B.structureSheaf.obj) :
    PresheafOfModules.IsLocallyInjective B.topology (toSheafification.{u, m} B P) :=
  inferInstanceAs (PresheafOfModules.IsLocallyInjective B.topology
    (PresheafOfModules.toSheafify (𝟙 B.structureSheaf.obj)
      (CategoryTheory.toSheafify B.topology P.presheaf)))

/-- The map into the sheafification is locally surjective. -/
public instance toSheafification_isLocallySurjective
    (P : PresheafOfModules.{max u m} B.structureSheaf.obj) :
    PresheafOfModules.IsLocallySurjective B.topology (toSheafification.{u, m} B P) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective B.topology
    (PresheafOfModules.toSheafify (𝟙 B.structureSheaf.obj)
      (CategoryTheory.toSheafify B.topology P.presheaf)))

/-- The cokernel of a map of sheaves of modules on the site is the sheafification of the
cokernel formed in the presheaves of modules. This is the reflectivity of the sheaves of
modules inside the presheaves of modules: `Stacks.Adequate.sheafification` is a left adjoint of
`SheafOfModules.forget` whose counit is an isomorphism. -/
public abbrev CokernelIsSheafified : Prop :=
  ∀ {F G : SheafOfModules.{max u m} B.structureSheaf} (φ : F ⟶ G),
    Nonempty ((sheafification.{u, m} B).obj
      (cokernel ((SheafOfModules.forget B.structureSheaf).map φ)) ≅ cokernel φ)

/-- A colimit of sheaves of modules on the site is the sheafification of the colimit formed in
the presheaves of modules, by the same reflectivity. -/
public abbrev ColimitIsSheafified (J : Type (max u m)) [Category.{max u m} J] : Prop :=
  ∀ (K : J ⥤ SheafOfModules.{max u m} B.structureSheaf)
    [HasColimit (K ⋙ SheafOfModules.forget B.structureSheaf)] [HasColimit K],
    Nonempty ((sheafification.{u, m} B).obj
      (colimit (K ⋙ SheafOfModules.forget B.structureSheaf)) ≅ colimit K)

/-- The counit isomorphism of the sheafification adjunction for presheaves of modules on the
site: sheafifying the underlying presheaf of modules of a sheaf of modules returns that sheaf
of modules. -/
public noncomputable def sheafificationCounitIso :
    (SheafOfModules.forget B.structureSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 B.structureSheaf.obj)) ⋙
      sheafification.{u, m} B ≅ 𝟭 _ :=
  asIso (PresheafOfModules.sheafificationAdjunction.{max u m} (𝟙 B.structureSheaf.obj)).counit

/-- **`Stacks.Adequate.CokernelIsSheafified`, proved.** The cokernel of a map of sheaves of
modules on the site is the sheafification of the cokernel formed in the presheaves of modules.
Sheafification is a left adjoint of `SheafOfModules.forget`, hence preserves the cokernel, and
the counit of that adjunction is an isomorphism, so the cokernel of the sheafified presheaf map
is the cokernel of the original map. -/
public theorem cokernelIsSheafified : CokernelIsSheafified.{u, m} B := by
  intro F G φ
  let e := sheafificationCounitIso.{u, m} B
  exact ⟨PreservesCokernel.iso (sheafification.{u, m} B)
      ((SheafOfModules.forget B.structureSheaf).map φ) ≪≫
    cokernel.mapIso _ φ (e.app F) (e.app G)
      ((PresheafOfModules.sheafificationAdjunction.{max u m}
        (𝟙 B.structureSheaf.obj)).counit.naturality φ)⟩

/-- **`Stacks.Adequate.ColimitIsSheafified`, proved.** A colimit of sheaves of modules on the
site is the sheafification of the colimit formed in the presheaves of modules, by the same
adjunction as `Stacks.Adequate.cokernelIsSheafified`. -/
public theorem colimitIsSheafified (J : Type (max u m)) [Category.{max u m} J] :
    ColimitIsSheafified.{u, m} B J := by
  intro K _ _
  let eK : (K ⋙ SheafOfModules.forget B.structureSheaf) ⋙ sheafification.{u, m} B ≅ K :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft K (sheafificationCounitIso.{u, m} B) ≪≫ K.rightUnitor
  let : HasColimit ((K ⋙ SheafOfModules.forget B.structureSheaf) ⋙
    sheafification.{u, m} B) := hasColimit_of_iso eK
  exact ⟨preservesColimitIso (sheafification.{u, m} B)
    (K ⋙ SheafOfModules.forget B.structureSheaf) ≪≫ HasColimit.isoOfNatIso eK⟩

/-! ### The zero module -/

/-- The zero sheaf of modules is adequate: its affine-section functors are zero. -/
public instance adequate_containsZero : (adequate.{u, max u m} B).ContainsZero where
  exists_zero :=
    ⟨0, isZero_zero _, isAdequate_of_forall_affineSectionFunctor B 0 fun A f _ =>
      AdequateFunctor.isAdequate_of_isZero _
        (Functor.map_isZero (affineSectionsFunctor.{u, max u m} B A f) (isZero_zero _))⟩

end Sheafify

end Stacks.Adequate

end

