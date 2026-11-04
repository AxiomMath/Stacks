module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBound
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.BoundedCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenPushforwardAdjunction

/-!
# Approximation for triples on an affine scheme

Let `X` be an affine scheme and `(T, E, m)` a triple with `E` in `D_QCoh(𝒪_X)` such that, for an
integer `r ≥ 0`, `E` is `m`-pseudo-coherent, `Hⁱ(E)` is supported on `T` for `i ≥ m - r + 1`, and
`X ∖ T` is the union of `r` affine opens. Then approximation holds for `(T, E, m)`. This is the
first assertion of [Stacks, Tag 08EQ].

## Main results

* `AlgebraicGeometry.PerfectApproximation.isZero_rightDerivedPlus_secF_preimage_of_affineCover`:
  on a union `W` of `r` affine opens of a scheme with affine diagonal, quasi-coherent cohomology
  over `W ∩ V` vanishes in degrees `≥ r` for every affine open `V`.
* `Stacks.AffineTilde.eq_zero_of_isZero_homology_zero`: on `Spec R`, a morphism from `𝒪[0]` to
  an object of `D_QCoh` with `H⁰ = 0` is zero.
* `Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift_of_affineCover`: the Koszul lift
  of [Stacks, Tag 08E3] for `T = V(f₁, …, f_n)` when `Spec R ∖ T` is a union of `r` affine opens
  and the cohomology of the target vanishes off `T` in the degrees `-r + 1, …, 0` only.
* `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_affineCover_spec` and
  `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_affineCover`: the first
  assertion of [Stacks, Tag 08EQ], on `Spec R` and on an arbitrary affine scheme.

## Implementation notes

Everything is at the model `CategoryTheory.HasDerivedCategory.standard` of the derived category;
at that model `Stacks.Duality.derivedPushforward` and the derived pushforward of ringed spaces of
[Stacks, Tag 08D5] are the same functor.

## References

* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.TransportAlongIso (ringedSpaceIsoOfSchemeIso)

namespace AlgebraicGeometry.PerfectApproximation

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- Stalks of the underlying presheaves of isomorphic modules are simultaneously zero. -/
private theorem isZero_stalk_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : N ≅ M) (x : X)
    (h : IsZero (TopCat.Presheaf.stalk (X := X) M.val.presheaf x)) :
    IsZero (TopCat.Presheaf.stalk (X := X) N.val.presheaf x) :=
  h.of_iso
    ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso e)

/-- Let `X` be a scheme with affine diagonal and let `W = U₁ ∪ ⋯ ∪ U_r` be a union of `r` affine
opens. For every affine open `V` of `X` the cohomology of a quasi-coherent module on `W` over
`W ∩ V` vanishes in every degree `≥ r`. -/
theorem isZero_rightDerivedPlus_secF_preimage_of_affineCover {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))] {r : ℕ} (U : Fin r → X.Opens)
    (hU : ∀ k, IsAffineOpen (U k)) {W : X.Opens} (hW : ⨆ k, U k = W) (V : X.Opens)
    (hV : IsAffineOpen V) (M : W.toScheme.Modules) (hM : M.IsQuasicoherent) (p : ℤ)
    (hp : (r : ℤ) ≤ p) :
    IsZero (((secF W.toScheme.ringCatSheaf (W.ι ⁻¹ᵁ V)).rightDerivedPlus p).obj M) := by
  have : M.IsQuasicoherent := hM
  have : (secF W.toScheme.ringCatSheaf (W.ι ⁻¹ᵁ V)).Additive :=
    secFAdditive W.toScheme.ringCatSheaf (W.ι ⁻¹ᵁ V)
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (secF W.toScheme.ringCatSheaf (W.ι ⁻¹ᵁ V)) rfl M).2 ?_
  let P : W.toScheme.Opens → Prop := fun Y =>
    ∃ V' : X.Opens, IsAffineOpen V' ∧ V' ≤ W ∧ Y = W.ι ⁻¹ᵁ V'
  have hPinf : ∀ Y Y', P Y → P Y' → P (Y ⊓ Y') := by
    rintro _ _ ⟨V₁, h₁, hle₁, rfl⟩ ⟨V₂, h₂, hle₂, rfl⟩
    exact ⟨V₁ ⊓ V₂, h₁.inf h₂, inf_le_left.trans hle₁, by rw [Scheme.Hom.preimage_inf]⟩
  have hPaff : ∀ Y, P Y → IsAffineOpen Y := by
    rintro _ ⟨V', h', hle, rfl⟩
    exact h'.preimage_of_isOpenImmersion W.ι (by rwa [Scheme.Opens.opensRange_ι])
  have hcover : ⨆ k, W.ι ⁻¹ᵁ (V ⊓ U k) = W.ι ⁻¹ᵁ V := by
    rw [← Scheme.Hom.preimage_iSup, ← inf_iSup_eq, Scheme.Hom.preimage_inf, hW,
      Scheme.Opens.ι_preimage_self, inf_top_eq]
  exact (Stacks.Cohomology.AffineCover.isZero_hgroup_iff_isZero_cohomologyPresheaf _ M n).2
    (Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_infClosed_cover P hPinf hPaff
      (fun k => W.ι ⁻¹ᵁ (V ⊓ U k))
      (fun k => ⟨V ⊓ U k, hV.inf (hU k), inf_le_right.trans (hW ▸ le_iSup U k), rfl⟩)
      _ hcover M n (by omega))

/-- If the stalks of `Hⁱ(E)` vanish at every point of the open `W`, then `Hⁱ` of the restriction
of `E` to `W` is zero. -/
theorem isZero_homology_derivedRestriction_of_isZero_stalk (X : Scheme.{u}) (W : X.Opens)
    (R : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (ExtensionByZeroModules.resRing W X.ringCatSheaf))
    (hR : R = ExtensionByZeroModules.jStar W X.ringCatSheaf)
    [hRa : R.Additive] [hRl : PreservesFiniteLimits R] [hRc : PreservesFiniteColimits R]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) (i : ℤ)
    (hE : ∀ x : X, x ∈ W → IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor _ i).obj E).val.presheaf) x)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj (R.mapDerivedCategory.obj E)) := by
  subst hR
  exact (Stacks.Cohomology.PushforwardRestriction.isZero_jStar_obj_of_stalk_isZero _ W _
    hE).of_iso ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (ExtensionByZeroModules.jStar W X.ringCatSheaf) i).app E)

/-- If the restriction of `E` to the open `W` is zero, then every cohomology sheaf of `E` has
vanishing stalks at the points of `W`. -/
theorem isZero_stalk_homology_of_isZero_derivedRestriction (X : Scheme.{u}) (W : X.Opens)
    (R : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (ExtensionByZeroModules.resRing W X.ringCatSheaf))
    (hR : R = ExtensionByZeroModules.jStar W X.ringCatSheaf)
    [hRa : R.Additive] [hRl : PreservesFiniteLimits R] [hRc : PreservesFiniteColimits R]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : IsZero (R.mapDerivedCategory.obj E)) (i : ℤ) (x : X) (hx : x ∈ W) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor _ i).obj E).val.presheaf) x) := by
  subst hR
  let M := (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj E
  have hRestrict : IsZero ((ExtensionByZeroModules.jStar W X.ringCatSheaf).obj M) :=
    (Functor.map_isZero (DerivedCategory.homologyFunctor _ i) hE).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (ExtensionByZeroModules.jStar W X.ringCatSheaf) i).app E).symm
  let xW : W := ⟨x, hx⟩
  have hS := Functor.map_isZero
    (SheafOfModules.toSheaf (ExtensionByZeroModules.resRing W X.ringCatSheaf)) hRestrict
  exact ((TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mp hS xW).of_iso
    (TopCat.Presheaf.stalkRestrictIso W M.val.presheaf xW).symm

/-- The restriction to an open subscheme of an object with quasi-coherent cohomology has
quasi-coherent cohomology. -/
theorem isQuasicoherent_homology_derivedRestriction (X : Scheme.{u}) (W : X.Opens)
    (R : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (ExtensionByZeroModules.resRing W X.ringCatSheaf))
    (hR : R = ExtensionByZeroModules.jStar W X.ringCatSheaf)
    [hRa : R.Additive] [hRl : PreservesFiniteLimits R] [hRc : PreservesFiniteColimits R]
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
      E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} W.toScheme.ringCatSheaf) i).obj
      (R.mapDerivedCategory.obj E)).IsQuasicoherent := by
  subst hR
  let M : X.Modules :=
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj E
  have : M.IsQuasicoherent := hE i
  have hM : ((ExtensionByZeroModules.jStar W X.ringCatSheaf).obj M).IsQuasicoherent := by
    rw [Stacks.Duality.OpenImmersion.jStar_eq_restrictFunctor X W]
    exact Scheme.Modules.isQuasicoherent_restrictFunctor W.ι M
  exact (SheafOfModules.isQuasicoherent.{u} W.toScheme.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (ExtensionByZeroModules.jStar W X.ringCatSheaf) i).app E).symm hM

end AlgebraicGeometry.PerfectApproximation

namespace Stacks.AffineTilde

open _root_.AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : CommRingCat.{u}}

/-- On `Spec R`, every morphism from `𝒪[0]` to an object of `D_QCoh(𝒪_{Spec R})` whose cohomology
sheaf in degree zero vanishes is zero. -/
theorem eq_zero_of_isZero_homology_zero (L : DerivedCategory (Spec R).Modules)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj L).IsQuasicoherent)
    (h0 : IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules 0).obj L))
    (g : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶ L) : g = 0 := by
  let _instM : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  obtain ⟨E, ⟨hEL⟩⟩ := exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard L hqc
  have : PreservesFiniteLimits (tilde.functor R) := AlgebraicGeometry.tilde.preservesFiniteLimits R
  have : PreservesFiniteColimits (tilde.functor R) := preservesFiniteColimits_tildeFunctor R
  let ι : DerivedCategory.Q.obj (structureSheafSingleComplex R) ≅
      (tilde.functor R).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
    (DerivedCategory.Q.mapIso (tildeSingleSelfIso R)).symm ≪≫
      ((tilde.functor R).mapDerivedCategoryFactors.app
        (((CochainComplex.singleFunctors (ModuleCat.{u} R)).functor 0).obj
          (ModuleCat.of R R))).symm
  let FF := mapDerivedCategoryTildeFullyFaithful.{u + 1, u + 1} R
  have hH0 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj E) := by
    have hz : IsZero ((tilde.functor R).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj E)) :=
      h0.of_iso (((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (tilde.functor R) 0).app E).symm ≪≫
          (DerivedCategory.homologyFunctor (Spec R).Modules 0).mapIso hEL)
    refine (IsZero.iff_id_eq_zero _).2 (tilde.fullyFaithfulFunctor.map_injective ?_)
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hz
  have hh : FF.preimage (ι.inv ≫ g ≫ hEL.inv) = 0 := by
    apply (DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of R R) E 0).injective
    rw [map_zero]
    exact hH0.eq_of_tgt _ _
  have hg : ι.inv ≫ g ≫ hEL.inv = 0 := by
    rw [← FF.map_preimage (ι.inv ≫ g ≫ hEL.inv), hh, Functor.map_zero]
  simpa using hg

/-- Let `T = V(f₁, …, f_n) ⊆ Spec R` and suppose `Spec R ∖ T = U₁ ∪ ⋯ ∪ U_r` with each `U_k`
affine. Let `G` be an object of `D_QCoh(𝒪_{Spec R})` with `Hⁱ(G) = 0` for `i > 0` whose
cohomology sheaves vanish on `Spec R ∖ T` in the degrees `-r + 1, …, 0`. Then every morphism
`𝒪[0] ⟶ G` factors through the sheafified Koszul complex on the `(e+1)`-st powers of the `f_i`,
for some `e`, and that complex is a perfect object supported on `T`. -/
theorem exists_isAdmissible_koszulPowerTilde_lift_of_affineCover {n r : ℕ} (f : Fin n → R)
    (U : Fin r → (Spec R).Opens) (hU : ∀ k, IsAffineOpen (U k))
    (hcover : ∀ x : PrimeSpectrum R,
      x ∈ ⨆ k, U k ↔ x ∉ PrimeSpectrum.zeroLocus (Set.range f))
    (G : DerivedCategory (Spec R).Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj G).IsQuasicoherent)
    (hpos : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj G))
    (hvan : ∀ i : ℤ, -(r : ℤ) + 1 ≤ i → i ≤ 0 → ∀ x : PrimeSpectrum R,
      x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
      IsZero (TopCat.Presheaf.stalk
        (((DerivedCategory.homologyFunctor (Spec R).Modules i).obj G).val.presheaf) x))
    (s : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶ G) :
    ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ G,
      PerfectApproximation.IsAdmissible (Spec R) (PrimeSpectrum.zeroLocus (Set.range f))
          (DerivedCategory.Q.obj (koszulPowerTildeComplex f e)) ∧
        s = DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t := by
  let W : (Spec R).Opens := ⨆ k, U k
  have hWcpt : IsCompact ((⨆ k, U k : (Spec R).Opens) : Set (Spec R)) := by
    rw [Opens.coe_iSup]
    exact isCompact_iUnion fun k => (hU k).isCompact
  have hWc : CompactSpace W := isCompact_iff_compactSpace.1 hWcpt
  let a := Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction W.ι
  let jG := (Stacks.Duality.OpenImmersion.derivedRestrict W.ι).obj G
  let L := (Stacks.Duality.derivedPushforward W.ι).obj jG
  have hres : IsIso ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).map (a.unit.app G)) := by
    have h : (Stacks.Duality.OpenImmersion.derivedRestrict W.ι).map (a.unit.app G) ≫
        a.counit.app ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).obj G) = 𝟙 _ :=
      a.left_triangle_components G
    have hcomp : IsIso ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).map (a.unit.app G) ≫
        a.counit.app ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).obj G)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (a.counit.app ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).obj G))
  obtain ⟨C, g, δ, hDist⟩ := distinguished_cocone_triangle (a.unit.app G)
  have hCW : IsZero ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).obj C) :=
    Triangle.isZero₃_of_isIso₁
      ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).mapTriangle.obj (Triangle.mk _ g δ))
      ((Stacks.Duality.OpenImmersion.derivedRestrict W.ι).map_distinguished _ hDist) hres
  have hC : ∀ (i : ℤ) (x : PrimeSpectrum R), x ∈ W →
      IsZero (TopCat.Presheaf.stalk
        (((DerivedCategory.homologyFunctor (Spec R).Modules i).obj C).val.presheaf) x) :=
    PerfectApproximation.isZero_stalk_homology_of_isZero_derivedRestriction (Spec R) W
      (Stacks.DerivedQCoh.modulesRestrict W) (Stacks.DerivedQCoh.modulesRestrict_eq_jStar W)
      (hRa := Stacks.DerivedQCoh.modulesRestrict_additive_resRing W)
      (hRl := Stacks.DerivedQCoh.modulesRestrict_preservesFiniteLimits_resRing W)
      (hRc := Stacks.DerivedQCoh.modulesRestrict_preservesFiniteColimits_resRing W) C hCW
  have hqcj : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor W.toScheme.Modules i).obj jG).IsQuasicoherent :=
    PerfectApproximation.isQuasicoherent_homology_derivedRestriction (Spec R) W
      (Stacks.DerivedQCoh.modulesRestrict W) (Stacks.DerivedQCoh.modulesRestrict_eq_jStar W)
      (hRa := Stacks.DerivedQCoh.modulesRestrict_additive_resRing W)
      (hRl := Stacks.DerivedQCoh.modulesRestrict_preservesFiniteLimits_resRing W)
      (hRc := Stacks.DerivedQCoh.modulesRestrict_preservesFiniteColimits_resRing W) G hqc
  have hqcL : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj L).IsQuasicoherent :=
    isQuasicoherent_derivedPushforward W.ι ⟨jG, hqcj⟩
  have hLEj : jG.IsLE (-(r : ℤ)) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    refine PerfectApproximation.isZero_homology_derivedRestriction_of_isZero_stalk (Spec R) W
      (Stacks.DerivedQCoh.modulesRestrict W) (Stacks.DerivedQCoh.modulesRestrict_eq_jStar W)
      (hRa := Stacks.DerivedQCoh.modulesRestrict_additive_resRing W)
      (hRl := Stacks.DerivedQCoh.modulesRestrict_preservesFiniteLimits_resRing W)
      (hRc := Stacks.DerivedQCoh.modulesRestrict_preservesFiniteColimits_resRing W) G i
      fun x hx => ?_
    by_cases hi0 : 0 < i
    · exact Functor.map_isZero (Scheme.Modules.toPresheaf (Spec R) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) (hpos i hi0)
    · exact hvan i (by omega) (by omega) x ((hcover x).1 hx)
  have hL0 : IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules 0).obj L) :=
    isZero_homology_derivedPushforward_of_isBasis (N := r) W.ι (Spec R).isBasis_affineOpens
      (fun V hV M hM p hp =>
        PerfectApproximation.isZero_rightDerivedPlus_secF_preimage_of_affineCover U hU rfl V hV
          M hM p hp)
      jG hqcj (-(r : ℤ)) hLEj 0 (by omega)
  have hsη : s ≫ a.unit.app G = 0 := eq_zero_of_isZero_homology_zero L hqcL hL0 _
  have hDist' := inv_rot_of_distTriang _ hDist
  obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ hDist' s hsη
  have hP := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre (Spec R)
  have hqcC : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      (C⟦(-1 : ℤ)⟧)).IsQuasicoherent :=
    DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _ hP _
      (inv_rot_of_distTriang _ hDist')
      (DerivedCategoryB.derivedCategoryB_shift_mem _ hP (-1) hqcL) hqc
  have hvanC : ∀ i : ℤ, -(n : ℤ) + 1 ≤ i → i ≤ 0 → ∀ x : PrimeSpectrum R,
      x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
      IsZero (TopCat.Presheaf.stalk
        (((DerivedCategory.homologyFunctor (Spec R).Modules i).obj (C⟦(-1 : ℤ)⟧)).val.presheaf)
          x) := by
    intro i _ _ x hx
    exact PerfectApproximation.isZero_stalk_of_iso
      ((PerfectApproximation.homologyShiftIso (Spec R).Modules (-1) i (-1 + i) rfl).app C) x
      (hC (-1 + i) x ((hcover x).2 hx))
  obtain ⟨e, t, hadm, ht⟩ :=
    exists_isAdmissible_koszulPowerTilde_lift_of_isZero_stalk_homology f (C⟦(-1 : ℤ)⟧) hqcC
      hvanC v
  exact ⟨e, t ≫ (Triangle.mk (a.unit.app G) g δ).invRotate.mor₁, hadm,
    hv.trans ((congrArg (· ≫ (Triangle.mk (a.unit.app G) g δ).invRotate.mor₁) ht).trans
      (Category.assoc _ _ _))⟩

end Stacks.AffineTilde

namespace AlgebraicGeometry.PerfectApproximation

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- Let `T ⊆ Spec R` be a subset whose complement is the union of `r` affine opens, and let `E` be
an object of `D_QCoh(𝒪_{Spec R})` which is `m`-pseudo-coherent and whose cohomology sheaves are
supported on `T` in all degrees `≥ m - r + 1`. Then approximation holds for `(T, E, m)`. -/
theorem approximationHolds_of_affineCover_spec (R : CommRingCat.{u}) (T : Set (Spec R))
    {r : ℕ} (U : Fin r → (Spec R).Opens) (hU : ∀ k, IsAffineOpen (U k))
    (hcover : ((⨆ k, U k : (Spec R).Opens) : Set (Spec R)) = Tᶜ)
    (E : DerivedCategory.{u + 1} (Spec R).Modules) (m : ℤ)
    (hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent)
    (hpc : RingedSpace.IsPseudoCoherentFrom (X := (Spec R).toRingedSpace) E m)
    (hsupp : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i → ∀ x : Spec R, x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := Spec R)
        (((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).val.presheaf) x)) :
    ApproximationHolds (Spec R) T E m := by
  classical
  let _instOX : HasDerivedCategory.{u + 1}
    (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace) := inferInstance
  let _instM : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  have hTc : IsCompact (Tᶜ : Set (Spec R)) ∧ IsOpen (Tᶜ : Set (Spec R)) := by
    rw [← hcover, Opens.coe_iSup]
    exact ⟨isCompact_iUnion fun k => (hU k).isCompact, isOpen_iUnion fun k => (U k).isOpen⟩
  obtain ⟨s, hs⟩ := PrimeSpectrum.isCompact_isOpen_iff.1 hTc
  set f : Fin s.card → R := fun i => (s.equivFin.symm i : R) with hf
  have hrange : Set.range f = (↑s : Set R) := by
    refine Set.eq_of_subset_of_subset ?_ fun x hx => ?_
    · rintro _ ⟨i, rfl⟩
      simp [hf]
    · exact ⟨s.equivFin ⟨x, hx⟩, by simp [hf]⟩
  have hTz : T = PrimeSpectrum.zeroLocus (Set.range f) := by
    rw [hrange]
    ext x
    exact (not_iff_not.1 (Set.ext_iff.1 hs x)).symm
  subst hTz
  have hcover' : ∀ x : PrimeSpectrum R,
      x ∈ ⨆ k, U k ↔ x ∉ PrimeSpectrum.zeroLocus (Set.range f) := fun x =>
    Set.ext_iff.1 hcover x
  have hcpt : CompactSpace (Spec R).toRingedSpace.carrier :=
    inferInstanceAs (CompactSpace (Spec R))
  obtain ⟨b, hb⟩ := RingedSpace.exists_isZero_homology_of_isPseudoCoherentFrom
    (X := (Spec R).toRingedSpace) E m hpc
  refine approximationHolds_of_oneStep_approximationClass (Spec R)
    (PrimeSpectrum.zeroLocus (Set.range f)) m (m - (r : ℤ) + 1)
    (fun F hF t hmt hvanF => ?_) E ⟨hqc, hpc, hsupp⟩ (b - 1) (fun i hi => hb i (by omega))
  refine Stacks.AffineTilde.exists_isAdmissible_epi_homology_of_lift f m _ F hF t hmt hvanF
    fun σ => ?_
  obtain ⟨hqcF, -, hsuppF⟩ := hF
  refine Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift_of_affineCover f U hU
    hcover' (F⟦t⟧) (fun n => ?_) (fun n hn => ?_) (fun n hn hn' x hx => ?_) σ
  · exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      ((homologyShiftIso (Spec R).Modules t n (t + n) rfl).app F).symm (hqcF (t + n))
  · exact (hvanF (t + n) (by omega)).of_iso
      ((homologyShiftIso (Spec R).Modules t n (t + n) rfl).app F)
  · exact isZero_stalk_of_iso ((homologyShiftIso (Spec R).Modules t n (t + n) rfl).app F) x
      (hsuppF (t + n) (by omega) x hx)

/-- Let `X` be an affine scheme. Approximation holds for every triple `(T, E, m)` with `E` an
object of `D_QCoh(𝒪_X)` for which there is an integer `r ≥ 0` such that

1. `E` is `m`-pseudo-coherent,
2. `Hⁱ(E)` is supported on `T` for `i ≥ m - r + 1`,
3. `X ∖ T` is the union of `r` affine opens `U₁, …, U_r`. -/
@[stacks 08EQ "first assertion: approximation for triples on an affine scheme"]
theorem approximationHolds_of_affineCover (X : Scheme.{u}) [IsAffine X] (T : Set X)
    {r : ℕ} (U : Fin r → X.Opens) (hU : ∀ k, IsAffineOpen (U k))
    (hcover : ((⨆ k, U k : X.Opens) : Set X) = Tᶜ)
    (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hpc : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m)
    (hsupp : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i → ∀ x : X, x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules i).obj E).val.presheaf) x)) :
    ApproximationHolds X T E m := by
  set e := X.isoSpec with he
  let := preservesFiniteLimits_modulePullback_of_isIso e.inv
  set E' := (derivedPullback e.inv.toLRSHom.toShHom).obj E with hE'
  have hbase : ∀ x : X, e.inv.base (e.hom.base x) = x := fun x => by simp
  have happ : ApproximationHolds (Spec Γ(X, ⊤)) (e.inv.base ⁻¹' T) E' m := by
    refine approximationHolds_of_affineCover_spec Γ(X, ⊤) (e.inv.base ⁻¹' T)
      (fun k => e.inv ⁻¹ᵁ U k) (fun k => (hU k).preimage e.inv) ?_ E' m (fun i => ?_) ?_
      (fun i hi y hy => ?_)
    · have h : ((⨆ k, e.inv ⁻¹ᵁ U k : (Spec Γ(X, ⊤)).Opens) : Set (Spec Γ(X, ⊤))) =
          e.inv.base ⁻¹' ((⨆ k, U k : X.Opens) : Set X) := by
        rw [Opens.coe_iSup, Opens.coe_iSup, Set.preimage_iUnion]
        rfl
      rw [h, hcover, Set.preimage_compl]
    · exact Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel e.inv E hqc i
    · exact AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
        e.inv.toLRSHom.toShHom E m hpc
    · exact isZero_stalk_homology_derivedPullback e.inv.toLRSHom.toShHom E i y (hsupp i hi _ hy)
  have hpull := approximationHolds_derivedPullback e.hom (e.inv.base ⁻¹' T) E' m happ
  have hset : e.hom.base ⁻¹' (e.inv.base ⁻¹' T) = T := by
    ext x
    simp [Set.mem_preimage, hbase x]
  rw [hset] at hpull
  exact hpull.of_iso
    ((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackInvHomIso
      (ringedSpaceIsoOfSchemeIso e)).app E)

end AlgebraicGeometry.PerfectApproximation
