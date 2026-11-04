module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformFiniteStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTripleCoordinates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierLevelSheafBasePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LowerShriekGysin
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

/-!
# The Fourier transform on `𝔸¹_{k'}` read on Laumon's plane `Spec k'[x][t]`

Let `k'` be a finite field, `Λ` a finite commutative ring and `ψ` an additive character of `k'`
with values in `Λ`. The Fourier transform `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)`
(`Stacks.EtaleCohomology.fourierTransform`) is computed on the fibre product `𝔸¹ ×_{k'} 𝔸¹`,
`μ(x, t) = xt`. Laumon's family lives on the plane `Spec k'[x][t]`, with projections
`laumonFamilyPr₁` (`x`) and `laumonFamilyProjection` (`t`). The plane is that fibre product
(`Stacks.EtaleCohomology.isPullback_laumonFamilyPr₁_laumonFamilyProjection`); through the
comparison `e : Spec k'[x][t] ≅ 𝔸¹ ×_{k'} 𝔸¹` the multiplication `μ` is the spectrum of
`X ↦ x t` (`Stacks.EtaleCohomology.laumonPlaneIso_hom_comp_affineLineMul`), so the Fourier kernel
`μ⁻¹ L_ψ(X)` is the Artin–Schreier sheaf `L_ψ(x t)` of the plane. Base change for `Rf_!` along
the isomorphism `e` and the independence of the compactification ([Stacks, Tag 0F7L] and
[Stacks, Tag 0F7I]) then give

`H¹(Φ(F[0])) ≅ R¹pr₂!(pr₁⁻¹ F ⊗ L_ψ(x t))`

for every sheaf `F` of `Λ`-modules on `𝔸¹_x` and every compactification of `pr₂`
(`Stacks.EtaleCohomology.nonempty_homology_fourierTransform_iso_laumonFamily`). This is piece
P2 of the proof of the absolute irreducibility of the Fourier family in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

**Sign.** There is no sign to adjust: both the Fourier kernel and the Laumon family twist use
`Stacks.ArtinSchreier.artinSchreierCharacter` (`σ ↦ ψ(-χ(σ))`) with the same character `ψ`.

## Main results

* `Stacks.EtaleCohomology.laumonPlaneIso`: `Spec k'[x][t] ≅ 𝔸¹ ×_{k'} 𝔸¹`.
* `Stacks.EtaleCohomology.laumonPlaneIso_hom_comp_affineLineMul`: `μ ∘ e = Spec(X ↦ x t)`.
* `Stacks.EtaleCohomology.nonempty_laumonPlaneIso_inverseImage_fourierIntegrand_iso`:
  `e⁻¹(pr₁⁻¹ F ⊗ μ⁻¹ L_ψ) ≅ pr₁⁻¹ F ⊗ L_ψ(x t)`.
* `Stacks.EtaleCohomology.nonempty_homology_fourierTransform_iso_laumonFamily`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier Stacks.Blowup

universe u

namespace Stacks.EtaleCohomology

section Plane

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))

local notation "𝔸f" => affineLineStructureMap k'

/-- **Laumon's plane is the fibre product `𝔸¹_x ×_{k'} 𝔸¹_t`**: the comparison isomorphism
`Spec k'[x][t] ≅ 𝔸¹ ×_{k'} 𝔸¹`, whose components are `pr₁` and `pr₂`. -/
def laumonPlaneIso :
    Spec (.of (Polynomial (Polynomial k'))) ≅ pullback 𝔸f 𝔸f :=
  (isPullback_laumonFamilyPr₁_laumonFamilyProjection k' B hS hL).isoPullback

omit [Fintype k'] in
/-- The first component of `laumonPlaneIso` is `pr₁ : Spec k'[x][t] ⟶ Spec k'[x]`. -/
theorem laumonPlaneIso_hom_fst :
    (laumonPlaneIso k' B hS hL).hom ≫ pullback.fst 𝔸f 𝔸f = laumonFamilyPr₁ k' :=
  IsPullback.isoPullback_hom_fst _

omit [Fintype k'] in
/-- The second component of `laumonPlaneIso` is `pr₂ : Spec k'[x][t] ⟶ Spec k'[t]`. -/
theorem laumonPlaneIso_hom_snd :
    (laumonPlaneIso k' B hS hL).hom ≫ pullback.snd 𝔸f 𝔸f =
      B.inclusion.map (laumonFamilyProjection k' B hS hL) :=
  IsPullback.isoPullback_hom_snd _

/-- The `k'`-algebra map `k'[X] → k'[x][t]`, `X ↦ x t`. -/
abbrev laumonPlaneMulAlgHom : Polynomial k' →ₐ[k'] Polynomial (Polynomial k') :=
  Polynomial.aeval (Polynomial.C Polynomial.X * Polynomial.X)

omit [Fintype k'] in
/-- **On Laumon's plane the multiplication `μ` is `(x, t) ↦ x t`**: `μ ∘ e` is the spectrum of
`X ↦ x t`. -/
theorem laumonPlaneIso_hom_comp_affineLineMul :
    (laumonPlaneIso k' B hS hL).hom ≫ affineLineMul k' =
      Spec.map (CommRingCat.ofHom (laumonPlaneMulAlgHom k').toRingHom) := by
  refine hom_ext_of_specHomRingHom ?_
  rw [specHomRingHom_comp, specHomRingHom_affineLineMul, specHomRingHom_specMap]
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      ← specHomRingHom_comp_apply, ← Category.assoc, laumonPlaneIso_hom_fst,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C,
      specHomRingHom_comp_specMap, specHomRingHom_specMap]
    rfl
  · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul,
      ← specHomRingHom_comp_apply, ← specHomRingHom_comp_apply, laumonPlaneIso_hom_fst,
      laumonPlaneIso_hom_snd, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X, map_mul, specHomRingHom_specMap,
      show B.inclusion.map (laumonFamilyProjection k' B hS hL) = laumonFamilyPr₂ k' from rfl,
      specHomRingHom_specMap]
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]

end Plane

section Kernel

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal

variable (k' : Type u) [Field k'] [Fintype k'] (Λ : Type) [CommRing Λ] [Finite Λ]
  (ψ : AddChar k' Λ) (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj (cover k' (Polynomial k') Polynomial.X))
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (pK : (finiteEtaleFiberFunctor z).obj
    (cover k' (Polynomial (Polynomial k')) (Polynomial.C Polynomial.X * Polynomial.X)))

local notation "𝔸f" => affineLineStructureMap k'

/-- **The Fourier kernel on Laumon's plane is `L_ψ(x t)`**: `e⁻¹ μ⁻¹ L_ψ(X) ≅ L_ψ(x t)`, at any
base point of the plane, `μ ∘ e` being the spectrum of `X ↦ x t`. -/
theorem nonempty_laumonPlaneIso_inverseImage_fourierKernel_iso :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (laumonPlaneIso k' B hS hL).hom).obj
        ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k')).obj
          (affineLineArtinSchreierSheaf k' Λ ψ B p₀)) ≅
      artinSchreierLevelSheaf k' (Polynomial (Polynomial k'))
        (Polynomial.C Polynomial.X * Polynomial.X) Λ ψ B hS z pK) := by
  have key : ∀ (g : Polynomial (Polynomial k')) (hg : laumonPlaneMulAlgHom k' Polynomial.X = g)
      (p : (finiteEtaleFiberFunctor z).obj (cover k' (Polynomial (Polynomial k')) g)),
      Nonempty ((etaleModuleInverseImage.{u, 0} Λ
          (Spec.map (CommRingCat.ofHom (laumonPlaneMulAlgHom k').toRingHom))).obj
          (affineLineArtinSchreierSheaf k' Λ ψ B p₀) ≅
        artinSchreierLevelSheaf k' (Polynomial (Polynomial k')) g Λ ψ B hS z p) := by
    intro g hg p
    subst hg
    exact nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint
      (Polynomial k') Λ ψ B (schemeSizeBelow_spec_polynomial k' B) (laumonPlaneMulAlgHom k') hS
      p₀ z p
  obtain ⟨a⟩ := key _ (Polynomial.aeval_X _) pK
  exact ⟨((etaleModuleInverseImageCompIso Λ (laumonPlaneIso k' B hS hL).hom
      (affineLineMul k')).app _).symm ≪≫
    eqToIso (congrArg (fun h => (etaleModuleInverseImage.{u, 0} Λ h).obj
      (affineLineArtinSchreierSheaf k' Λ ψ B p₀))
        (laumonPlaneIso_hom_comp_affineLineMul k' B hS hL)) ≪≫
    a⟩

/-- **The Fourier integrand on Laumon's plane**: `e⁻¹(pr₁⁻¹ F ⊗ μ⁻¹ L_ψ) ≅ pr₁⁻¹ F ⊗ L_ψ(x t)`
for a sheaf `F` of `Λ`-modules on `𝔸¹_x`. -/
theorem nonempty_laumonPlaneIso_inverseImage_fourierIntegrand_iso
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k')))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (laumonPlaneIso k' B hS hL).hom).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj F ⊗
          (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k')).obj
            (affineLineArtinSchreierSheaf k' Λ ψ B p₀)) ≅
      (etaleModuleInverseImage.{u, 0} Λ (laumonFamilyPr₁ k')).obj F ⊗
        artinSchreierLevelSheaf k' (Polynomial (Polynomial k'))
          (Polynomial.C Polynomial.X * Polynomial.X) Λ ψ B hS z pK) := by
  obtain ⟨a⟩ := nonempty_laumonPlaneIso_inverseImage_fourierKernel_iso k' Λ ψ B p₀ hS hL z pK
  let J := etaleModuleInverseImage.{u, 0} Λ (laumonPlaneIso k' B hS hL).hom
  exact ⟨(Functor.Monoidal.μIso J _ _).symm ≪≫
    ((((etaleModuleInverseImageCompIso Λ (laumonPlaneIso k' B hS hL).hom
      (pullback.fst 𝔸f 𝔸f)).app F).symm ≪≫
      eqToIso (congrArg (fun h => (etaleModuleInverseImage.{u, 0} Λ h).obj F)
        (laumonPlaneIso_hom_fst k' B hS hL))) ⊗ᵢ a)⟩

end Kernel

section Transform

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (k' : Type u) [Field k'] [Fintype k'] (Λ : Type) [CommRing Λ] [Finite Λ]
  (ψ : AddChar k' Λ) (B : BigEtaleSite.{u})

local notation "𝔸f" => affineLineStructureMap k'

/-- **`H¹` of the Fourier transform is `R¹` of Laumon's projection** (piece P2 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) through Laumon's Fourier transform): for a
sheaf `F` of `Λ`-modules on `𝔸¹_x`,
`H¹(Φ(F[0])) ≅ R¹pr₂!(pr₁⁻¹ F ⊗ L_ψ(x t))` on `𝔸¹_t`, for any compactification `jg` of
`pr₂ : Spec k'[x][t] → Spec k'[t]` and any base points of the Artin–Schreier sheaves. Laumon's
plane is the fibre product `𝔸¹ ×_{k'} 𝔸¹`, on which the Fourier kernel is `L_ψ(x t)`; base change
along the comparison isomorphism and the independence of the compactification
([Stacks, Tag 0F7L] and [Stacks, Tag 0F7I]) identify the two `R¹pr₂!`. -/
theorem nonempty_homology_fourierTransform_iso_laumonFamily
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
      (cover k' (Polynomial k') Polynomial.X))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k')))
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (pK : (finiteEtaleFiberFunctor z).obj (cover k' (Polynomial (Polynomial k'))
      (Polynomial.C Polynomial.X * Polynomial.X)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k')))) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((fourierTransform k' Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      (lowerShriekHomology Λ (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1).obj
        ((etaleModuleInverseImage.{u, 0} Λ (laumonFamilyPr₁ k')).obj F ⊗
          artinSchreierLevelSheaf k' (Polynomial (Polynomial k'))
            (Polynomial.C Polynomial.X * Polynomial.X) Λ ψ B hS z pK)) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k')).obj
    (affineLineArtinSchreierSheaf k' Λ ψ B p₀)
  have h𝓛e := isExactTensorRight_fourierKernel k' Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj F ⊗ 𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  let eT : (fourierTransform k' Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app F) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  let e := laumonPlaneIso k' B hS hL
  have sq : IsPullback e.hom (B.inclusion.map (laumonFamilyProjection k' B hS hL)) pr₂ (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact laumonPlaneIso_hom_snd k' B hS hL⟩
  have : CompactSpace ↥(B.inclusion.obj (specObject (Polynomial k') B hL)) :=
    inferInstanceAs (CompactSpace (Spec (.of (Polynomial k'))))
  have : QuasiSeparatedSpace ↥(B.inclusion.obj (specObject (Polynomial k') B hL)) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (Polynomial k'))))
  obtain ⟨b⟩ := nonempty_lowerShriekHomology_inverseImage_iso Λ sq jP jg G (Nat.card Λ)
    Nat.card_pos (natCard_nsmul_id_etaleModules Λ G) 1
  obtain ⟨c⟩ := nonempty_laumonPlaneIso_inverseImage_fourierIntegrand_iso k' Λ ψ B p₀ hS hL z pK F
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ 1).mapIso eT ≪≫
    ((lowerShriekHomologyIsoSingle Λ pr₂ jP 1).app G).symm ≪≫
    ((etaleModuleInverseImageIdIso Λ _).app _).symm ≪≫ b.symm ≪≫
    (lowerShriekHomology Λ (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1).mapIso c⟩

end Transform

end Stacks.EtaleCohomology

end
