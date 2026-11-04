module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologyGeometricFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt

/-!
# `R pr_!(pr⁻¹ G ⊗ L_ψ(T)) = 0` on a relative affine line

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `L = L_ψ(x)` the Artin–Schreier
sheaf on `𝔸¹_k`. For a `k`-scheme `W` and the affine line `P = 𝔸¹_W` over it, with projection
`pr : P ⟶ W` and coordinate `T : P ⟶ 𝔸¹_k`, and a sheaf `G` of `Λ`-modules on `W` with finite
geometric stalks,

`R pr_!(pr⁻¹ G ⊗ T⁻¹ L) = 0`.

At a geometric point `w̄ : Spec Ω ⟶ W` proper base change (Tag 0F7L) identifies the inverse image
with `R(𝔸¹_Ω ⟶ Spec Ω)_!` of `M ⊗ L|_{𝔸¹_Ω}`, `M` the stalk of `G` (over a separably closed field a
sheaf is constant on its global sections), and this is the inverse image to `Spec Ω` of
`Rf_!(M ⊗ L) = 0` (Tag 0F7L again, and the vanishing of the kernel on `𝔸¹_k`). This is the
vanishing of the Fourier kernel off the antidiagonal, in the coordinates `t' = t(x + u)`.

## Main results

* `isZero_derivedLowerShriek_inverseImage_tensor_affineLineArtinSchreierSheaf`:
  `R pr_!(pr⁻¹ G ⊗ T⁻¹ L) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **Over a separably closed field a sheaf is the constant sheaf on its global sections.** -/
def etaleModuleConstantSheafGlobalSectionsIso (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (G : EtaleModules.{u, 0} Λ (Spec (.of Ω))) :
    etaleModuleConstantSheaf Λ ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj G)
      (Spec (.of Ω)) ≅ G :=
  haveI : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  haveI := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  asIso ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)

include ψ in
/-- **`R pr_!(pr⁻¹ G ⊗ T⁻¹ L_ψ) = 0`** on the affine line `P = 𝔸¹_W` over a `k`-scheme `W`, for a
sheaf `G` of `Λ`-modules with finite geometric stalks: at the geometric points of `W` this is
`Rf_!(M ⊗ L_ψ) = 0` on `𝔸¹_k`, by proper base change (Tag 0F7L) twice. -/
theorem isZero_derivedLowerShriek_inverseImage_tensor_affineLineArtinSchreierSheaf
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) {W P : Scheme.{u}}
    (πW : W ⟶ Spec (.of k)) {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr (affineLineStructureMap k) πW) (G : EtaleModules.{u, 0} Λ W)
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ W),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G))) :
    IsZero ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ pr).obj G ⊗
          (etaleModuleInverseImage.{u, 0} Λ T).obj
            (affineLineArtinSchreierSheaf k Λ ψ B p₀)))) := by
  let 𝔸f := affineLineStructureMap k
  let L := affineLineArtinSchreierSheaf k Λ ψ B p₀
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ P) 0).obj
    ((etaleModuleInverseImage.{u, 0} Λ pr).obj G ⊗ (etaleModuleInverseImage.{u, 0} Λ T).obj L)
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFiniteType pr :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : IsSeparated pr := MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact pr := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  refine isZero_of_forall_isZero_etaleModuleDerivedInverseImagePlus Λ
    (fun w : W => (GeometricPoint.ofPoint W w).hom) (iUnion_range_geometricPoint_ofPoint W) _
    fun w => ?_
  let Ω := (GeometricPoint.ofPoint W w).residueField
  let g : Spec (.of Ω) ⟶ W := (GeometricPoint.ofPoint W w).hom
  let sq₁ : IsPullback (pullback.fst pr g) (pullback.snd pr g) pr g :=
    IsPullback.of_hasPullback pr g
  let sq₂ : IsPullback (pullback.fst pr g ≫ T) (pullback.snd pr g) 𝔸f (g ≫ πW) :=
    sq₁.paste_horiz sq
  let M := (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
    ((etaleModuleInverseImage.{u, 0} Λ g).obj G)
  have : Finite M := hG Ω g
  -- the sheaf on the geometric fibre
  let fst := pullback.fst pr g
  let snd := pullback.snd pr g
  let I := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => etaleModuleInverseImage.{u, 0} Λ a
  let eG : (I fst).obj ((I pr).obj G) ≅ etaleModuleConstantSheaf Λ M (pullback pr g) :=
    ((etaleModuleInverseImageCompIso Λ fst pr).app G).symm ≪≫
      eqToIso (by rw [pullback.condition]) ≪≫ (etaleModuleInverseImageCompIso Λ snd g).app G ≪≫
      (I snd).mapIso (etaleModuleConstantSheafGlobalSectionsIso Λ Ω _).symm ≪≫
      (etaleModuleInverseImageConstantIso Λ snd).app M
  let e₀ : (I fst).obj ((I pr).obj G ⊗ (I T).obj L) ≅ (I (fst ≫ T)).obj
      (etaleModuleConstantSheaf Λ M (Spec (.of (Polynomial k))) ⊗ L) :=
    (Functor.Monoidal.μIso (I fst) _ _).symm ≪≫
      (eG ⊗ᵢ ((etaleModuleInverseImageCompIso Λ fst T).app L).symm) ≪≫
      (((etaleModuleInverseImageConstantIso Λ (fst ≫ T)).app M).symm ⊗ᵢ Iso.refl _) ≪≫
      Functor.Monoidal.μIso (I (fst ≫ T)) _ _
  let K₀ := (DerivedCategory.Plus.singleFunctor
      (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) 0).obj
    (etaleModuleConstantSheaf Λ M (Spec (.of (Polynomial k))) ⊗ L)
  let eK : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ fst).obj K ≅
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (fst ≫ T)).obj K₀ :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (I fst) 0).app _ ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e₀ ≪≫
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (I (fst ≫ T)) 0).app _).symm
  -- proper base change twice, and the vanishing of the kernel on `𝔸¹_k`
  have := isIso_derivedLowerShriekBaseChange_app Λ sq₁ (j.baseChange sq) K
    (isTorsionPlus_of_finite Λ P K)
  have := isIso_derivedLowerShriekBaseChange_app Λ sq₂ j K₀
    (isTorsionPlus_of_finite Λ _ K₀)
  have h0 : IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (g ≫ πW)).obj
      ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj K₀)) :=
    Functor.map_isZero _
      (isZero_derivedLowerShriek_constantSheaf_tensor_affineLineArtinSchreierSheaf k Λ ψ B p₀
        hψ hq j M)
  let c := (derivedLowerShriekCompactificationIso snd
    ((j.baseChange sq).baseChange sq₁) (j.baseChange sq₂) Λ).app
      ⟨_, isTorsionPlus_of_finite Λ _ ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ fst).obj K)⟩
  exact h0.of_iso (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq₁ (j.baseChange sq)).app K) ≪≫
    c ≪≫ (derivedLowerShriek.{u, 0} snd (j.baseChange sq₂) Λ).mapIso eK ≪≫
    (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq₂ j).app K₀)).symm)

end Stacks.EtaleCohomology

end
