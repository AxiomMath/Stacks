module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineConstantCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeKernelVanishing

/-!
# `R pr_!(pr⁻¹ G)` on a relative affine line lives in degree two and detects `G`

Let `k` be a finite field, `Λ` a finite commutative ring in which `#k` is invertible, `W` a
`k`-scheme and `pr : P ⟶ W` the affine line over `W` (a base change of `𝔸¹_k ⟶ Spec k`). For a
sheaf `G` of `Λ`-modules on `W` with finite geometric stalks,

* `Hⁱ(R pr_!(pr⁻¹ G)) = 0` for `i ≠ 2`;
* `H²(R pr_!(pr⁻¹ G)) = 0` only when `G = 0`.

At a geometric point `w̄ : Spec Ω ⟶ W`, proper base change (Tag 0F7L) twice identifies the inverse
image of `R pr_!(pr⁻¹ G)` with the inverse image to `Spec Ω` of `Rf_!(M_{𝔸¹})`, `M` the stalk of
`G` at `w̄`, and the cohomology sheaves commute with these exact inverse images. The statements on
`Spec k` are `isZero_homology_derivedLowerShriek_constantSheaf_affineLine` and
`subsingleton_of_isZero_homology_two_derivedLowerShriek_constantSheaf_affineLine`.

These are the properties of the functor `D` (the composite of two Fourier transforms) used in
the irreducibility argument of Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): `D` is exact into degree two and reflects
zero objects.

## Main results

* `etaleModuleInverseImageHomologyIso`.
* `nonempty_inverseImage_homology_derivedLowerShriek_affineLine_iso`.
* `isZero_homology_derivedLowerShriek_inverseImage_affineLine`.
* `isZero_of_isZero_homology_two_derivedLowerShriek_inverseImage_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- **Inverse image commutes with cohomology sheaves**: `a⁻¹ Hⁱ(K) ≅ Hⁱ(a⁻¹ K)`, inverse image
being exact. -/
def etaleModuleInverseImageHomologyIso (Λ : Type) [Ring Λ] {X X' : Scheme.{u}} (a : X' ⟶ X)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (i : ℤ) :
    (etaleModuleInverseImage.{u, 0} Λ a).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj K) ≅
      (DerivedCategory.Plus.homologyFunctor _ i).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ a).obj K) :=
  ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (etaleModuleInverseImage.{u, 0} Λ a) i).app K).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ i).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso
        (etaleModuleInverseImage.{u, 0} Λ a)).app K).symm

/-- The structure morphism of a nonempty scheme over the spectrum of a field is surjective. -/
theorem iUnion_range_toSpecField (k : Type u) [Field k] {Y : Scheme.{u}} [Nonempty Y]
    (g : Y ⟶ Spec (.of k)) : ⋃ _a : PUnit.{u + 1}, Set.range g.base = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit, ?_⟩
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact ⟨y, Subsingleton.elim _ _⟩

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]

omit [Fintype k] in
/-- **The geometric fibres of `R pr_!(pr⁻¹ G)` on a relative affine line**: at a geometric point
`g : Spec Ω ⟶ W`, `g⁻¹ Hⁱ(R pr_!(pr⁻¹ G))` is the inverse image to `Spec Ω` of `Hⁱ(Rf_!(M_{𝔸¹}))`,
`M = Γ(g⁻¹ G)` (Tag 0F7L twice). -/
theorem nonempty_inverseImage_homology_derivedLowerShriek_affineLine_iso
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) {W P : Scheme.{u}}
    (πW : W ⟶ Spec (.of k)) {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr (affineLineStructureMap k) πW) (G : EtaleModules.{u, 0} Λ W)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ W)
    [Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ g).obj G))] (i : ℤ) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ g).obj
        ((DerivedCategory.Plus.homologyFunctor _ i).obj
          ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleInverseImage.{u, 0} Λ pr).obj G)))) ≅
      (etaleModuleInverseImage.{u, 0} Λ (g ≫ πW)).obj
        ((DerivedCategory.Plus.homologyFunctor _ i).obj
          ((derivedLowerShriek.{u, 0} (affineLineStructureMap k) j Λ).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((affineLineConstantSheaf k Λ).obj ((etaleModuleGlobalSections.{u, 0} Λ
                (Spec (.of Ω))).obj ((etaleModuleInverseImage.{u, 0} Λ g).obj G))))))) := by
  let 𝔸f := affineLineStructureMap k
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFiniteType pr :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : IsSeparated pr := MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact pr := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ P) 0).obj
    ((etaleModuleInverseImage.{u, 0} Λ pr).obj G)
  let sq₁ : IsPullback (pullback.fst pr g) (pullback.snd pr g) pr g :=
    IsPullback.of_hasPullback pr g
  let sq₂ : IsPullback (pullback.fst pr g ≫ T) (pullback.snd pr g) 𝔸f (g ≫ πW) :=
    sq₁.paste_horiz sq
  let M := (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
    ((etaleModuleInverseImage.{u, 0} Λ g).obj G)
  let fst := pullback.fst pr g
  let snd := pullback.snd pr g
  let I := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => etaleModuleInverseImage.{u, 0} Λ a
  let eG : (I fst).obj ((I pr).obj G) ≅ etaleModuleConstantSheaf Λ M (pullback pr g) :=
    ((etaleModuleInverseImageCompIso Λ fst pr).app G).symm ≪≫
      eqToIso (by rw [pullback.condition]) ≪≫ (etaleModuleInverseImageCompIso Λ snd g).app G ≪≫
      (I snd).mapIso (etaleModuleConstantSheafGlobalSectionsIso Λ Ω _).symm ≪≫
      (etaleModuleInverseImageConstantIso Λ snd).app M
  let e₀ : (I fst).obj ((I pr).obj G) ≅ (I (fst ≫ T)).obj ((affineLineConstantSheaf k Λ).obj M) :=
    eG ≪≫ ((etaleModuleInverseImageConstantIso Λ (fst ≫ T)).app M).symm
  let K₀ := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ
    (Spec (.of (Polynomial k)))) 0).obj ((affineLineConstantSheaf k Λ).obj M)
  let eK : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ fst).obj K ≅
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (fst ≫ T)).obj K₀ :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (I fst) 0).app _ ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e₀ ≪≫
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (I (fst ≫ T)) 0).app _).symm
  have := isIso_derivedLowerShriekBaseChange_app Λ sq₁ (j.baseChange sq) K
    (isTorsionPlus_of_finite Λ P K)
  have := isIso_derivedLowerShriekBaseChange_app Λ sq₂ j K₀
    (isTorsionPlus_of_finite Λ _ K₀)
  let c := (derivedLowerShriekCompactificationIso snd
    ((j.baseChange sq).baseChange sq₁) (j.baseChange sq₂) Λ).app
      ⟨_, isTorsionPlus_of_finite Λ _ ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ fst).obj K)⟩
  let E : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).obj
        ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj K) ≅
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (g ≫ πW)).obj
        ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj K₀) :=
    asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq₁ (j.baseChange sq)).app K) ≪≫
      c ≪≫ (derivedLowerShriek.{u, 0} snd (j.baseChange sq₂) Λ).mapIso eK ≪≫
      (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq₂ j).app K₀)).symm
  exact ⟨etaleModuleInverseImageHomologyIso Λ g _ i ≪≫
    (DerivedCategory.Plus.homologyFunctor _ i).mapIso E ≪≫
    (etaleModuleInverseImageHomologyIso Λ (g ≫ πW) _ i).symm⟩

/-- **`Hⁱ(R pr_!(pr⁻¹ G)) = 0` for `i ≠ 2`** on the affine line `P = 𝔸¹_W` over a `k`-scheme
`W`, for a sheaf `G` with finite geometric stalks, `#k` invertible in `Λ`. -/
theorem isZero_homology_derivedLowerShriek_inverseImage_affineLine
    (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) {W P : Scheme.{u}}
    (πW : W ⟶ Spec (.of k)) {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr (affineLineStructureMap k) πW) (G : EtaleModules.{u, 0} Λ W)
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ W),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G))) (i : ℤ) (hi : i ≠ 2) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ pr).obj G)))) := by
  refine isZero_of_forall_isZero_etaleModuleInverseImage Λ
    (fun w : W => (GeometricPoint.ofPoint W w).hom) (iUnion_range_geometricPoint_ofPoint W) _
    fun w => ?_
  have := hG _ (GeometricPoint.ofPoint W w).hom
  obtain ⟨e⟩ := nonempty_inverseImage_homology_derivedLowerShriek_affineLine_iso k Λ j πW sq G
    (GeometricPoint.ofPoint W w).hom i
  exact (Functor.map_isZero _ (isZero_homology_derivedLowerShriek_constantSheaf_affineLine k Λ hq
    j _ i hi)).of_iso e

/-- **`H²(R pr_!(pr⁻¹ G)) = 0` only for `G = 0`** on the affine line `P = 𝔸¹_W` over a
`k`-scheme `W`, for a sheaf `G` with finite geometric stalks, `#k` invertible in `Λ`. -/
theorem isZero_of_isZero_homology_two_derivedLowerShriek_inverseImage_affineLine
    (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) {W P : Scheme.{u}}
    (πW : W ⟶ Spec (.of k)) {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr (affineLineStructureMap k) πW) (G : EtaleModules.{u, 0} Λ W)
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ W),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G)))
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ pr).obj G))))) :
    IsZero G := by
  refine isZero_of_forall_isZero_etaleModuleInverseImage Λ
    (fun w : W => (GeometricPoint.ofPoint W w).hom) (iUnion_range_geometricPoint_ofPoint W) _
    fun w => ?_
  let g := (GeometricPoint.ofPoint W w).hom
  let Ω := (GeometricPoint.ofPoint W w).residueField
  have := hG _ g
  obtain ⟨e⟩ := nonempty_inverseImage_homology_derivedLowerShriek_affineLine_iso k Λ j πW sq G g 2
  have h1 := (Functor.map_isZero (etaleModuleInverseImage.{u, 0} Λ g) h).of_iso e.symm
  have h2 := isZero_of_forall_isZero_etaleModuleInverseImage Λ (ι := PUnit.{u + 1})
    (fun _ => g ≫ πW) (iUnion_range_toSpecField k (g ≫ πW)) _ fun _ => h1
  have := subsingleton_of_isZero_homology_two_derivedLowerShriek_constantSheaf_affineLine k Λ hq j
    _ h2
  have hM : IsZero ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ g).obj G)) := ModuleCat.isZero_of_subsingleton _
  exact (Functor.map_isZero (constantSheaf (Spec (.of Ω)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) hM).of_iso (etaleModuleConstantSheafGlobalSectionsIso Λ Ω _).symm

end Stacks.EtaleCohomology

end
