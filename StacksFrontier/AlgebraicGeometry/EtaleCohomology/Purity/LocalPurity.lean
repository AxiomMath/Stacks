module

import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.DenseOpenSmoothDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.Flag
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeTwistTransport
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SmoothClosedImmersionCoordinates
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local purity for smooth pairs

Let `k` be algebraically closed, `ℓ` a prime invertible in `k`, `Λ = ℤ/ℓ`, `Y` smooth over `k` of
relative dimension `d + c` and `i : T ⟶ Y` a closed immersion with `T` smooth of relative dimension
`d`. Every point of `T` has an open neighbourhood `N ⊆ Y` such that `T ∩ N ⟶ N` has a purity class
of degree `2c` (`Stacks.EtaleCohomology.Purity.localPurity`, PDd6's
`Stacks.EtaleCohomology.LocalPurity`).

The proof follows SGA 4 XVI 3.7. Stacks 0FUE
(`Stacks.AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback`) gives an open
`N ∋ x` with an étale `π : N ⟶ 𝔸^{m+n}_k` such that `T ∩ N = π⁻¹(𝔸^m_k)`. A relative dimension
count (étale morphisms preserve local dimension, Stacks 04N4) gives `m = d` and `n = c`. The
coordinate subspace `𝔸^m_k ⊆ 𝔸^{m+n}_k` is a flag of `n` principal smooth divisors, each the fibre
over the origin of a coordinate projection (`isPrincipalFlag_coordinateSubspaceEmbedding`), and
such flags pull back along smooth morphisms (`IsPrincipalFlag.of_isPullback`). Purity along flags
is `Stacks.EtaleCohomology.Purity.exists_purityClass_of_isPrincipalFlag`; codimension zero is
`exists_purityClassFun_of_isIso`.

## Main results

* `Stacks.EtaleCohomology.Purity.localPurityFun`, at level `ℤ/N`, and
  `Stacks.EtaleCohomology.Purity.localPurity`, PDd6's form at a prime `ℓ`.
* `Stacks.EtaleCohomology.Purity.isPrincipalFlag_coordinateSubspaceEmbedding`.
* `Stacks.EtaleCohomology.Purity.IsPrincipalFlag.of_isPullback`.
* `Stacks.EtaleCohomology.Purity.IsPurityClassFun.isPurityClass` and
  `Stacks.EtaleCohomology.IsPurityClass.isPurityClassFun`: the two forms of purity classes agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.Purity

open AlgebraicGeometry.AffineSpace Stacks.AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The origin of the affine line is the point all of whose coordinates vanish. -/
theorem origin_eq_homOfVector :
    origin k = homOfVector (𝟙 (Spec (.of k))) (fun _ => 0) := by
  ext1
  · rw [homOfVector_over, origin, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
      ← Spec.map_id]
    congr 1
    ext x
    simp
  · rename_i i
    rw [homOfVector_appTop_coord, origin, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    simp

/-- The origin is a section of the affine line. -/
@[reassoc (attr := simp)]
theorem origin_over : origin k ≫ (affineLine k ↘ Spec (.of k)) = 𝟙 _ := by
  rw [origin_eq_homOfVector, homOfVector_over]

/-- Under `𝔸^{M+1}_k ≅ 𝔸^M_{𝔸¹_k}`, the coordinate hyperplane `𝔸^M_k ⊆ 𝔸^{M+1}_k` is the base
change of the origin of `𝔸¹_k`. -/
theorem coordinateSubspaceEmbedding_one_comp_affineSpaceSuccIso (M : ℕ) :
    coordinateSubspaceEmbedding (Spec (.of k)) M 1 ≫
        (Stacks.Chow.affineSpaceSuccIso (Spec (.of k)) M).hom =
      AffineSpace.map (ULift.{u} (Fin M)) (origin k) := by
  have hover : (Stacks.Chow.affineSpaceSuccIso (Spec (.of k)) M).hom ≫
      (𝔸(ULift.{u} (Fin M); affineLine k) ↘ affineLine k) =
        reindex ((Stacks.Chow.uliftFinSuccSumEquiv.{u} M).symm ∘ Sum.inr) (Spec (.of k)) := by
    rw [Stacks.Chow.affineSpaceSuccIso, Iso.trans_hom, Category.assoc,
      Stacks.Chow.affineSpaceSumIso_hom_over]
    exact Stacks.Chow.affineSpace_reindex_comp _ _ _
  ext1
  · rw [map_over, Category.assoc, hover]
    ext1
    · rw [Category.assoc, reindex_over, coordinateSubspaceEmbedding_over, Category.assoc,
        origin_over, Category.comp_id]
    · rename_i i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, origin_eq_homOfVector,
        homOfVector_appTop_coord, map_zero]
      obtain ⟨i⟩ := i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact coordinateSubspaceEmbedding_lastCoordinate _ M 1 0
  · rename_i i
    rw [map_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Stacks.Chow.affineSpaceSuccIso, Iso.trans_hom, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, Stacks.Chow.affineSpaceSumIso]
    simp only [homOfVector_appTop_coord, Stacks.Chow.affineSpaceReindexIso]
    rw [reindex_appTop_coord]
    exact coordinateSubspaceEmbedding_firstCoordinate _ M 1 i.down

/-- The last coordinate `𝔸^{M+1}_k ⟶ 𝔸¹_k`, read through `𝔸^{M+1}_k ≅ 𝔸^M_{𝔸¹_k}`. -/
def lastCoordinateProjection (M : ℕ) :
    𝔸(ULift.{u} (Fin (M + 1)); Spec (.of k)) ⟶ affineLine k :=
  (Stacks.Chow.affineSpaceSuccIso (Spec (.of k)) M).hom ≫
    (𝔸(ULift.{u} (Fin M); affineLine k) ↘ affineLine k)

/-- The last coordinate projection `𝔸^{M+1}_k ⟶ 𝔸¹_k` is smooth. -/
instance smooth_lastCoordinateProjection (M : ℕ) : Smooth (lastCoordinateProjection k M) := by
  have := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver (affineLine k) M
  have : Smooth (𝔸(ULift.{u} (Fin M); affineLine k) ↘ affineLine k) :=
    SmoothOfRelativeDimension.smooth M _
  rw [lastCoordinateProjection]
  infer_instance

/-- **The coordinate hyperplane is the fibre of the last coordinate over the origin.** -/
theorem isPullback_coordinateSubspaceEmbedding_one (M : ℕ) :
    IsPullback (coordinateSubspaceEmbedding (Spec (.of k)) M 1)
      (𝔸(ULift.{u} (Fin M); Spec (.of k)) ↘ Spec (.of k)) (lastCoordinateProjection k M)
      (origin k) := by
  have h₁ := AffineSpace.isPullback_map (n := ULift.{u} (Fin M)) (origin k)
  have h₂ : IsPullback (Stacks.Chow.affineSpaceSuccIso (Spec (.of k)) M).inv
      (𝔸(ULift.{u} (Fin M); affineLine k) ↘ affineLine k) (lastCoordinateProjection k M)
      (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [lastCoordinateProjection]⟩
  have h := h₁.paste_horiz h₂
  rwa [Category.comp_id, ← coordinateSubspaceEmbedding_one_comp_affineSpaceSuccIso,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] at h

/-- The coordinate subspace of codimension `n + 1` is that of codimension `n` followed by a
coordinate hyperplane. -/
theorem coordinateSubspaceEmbedding_succ (S : Scheme.{u}) (m n : ℕ) :
    coordinateSubspaceEmbedding S m (n + 1) =
      coordinateSubspaceEmbedding S m n ≫ coordinateSubspaceEmbedding S (m + n) 1 := by
  ext1
  · change _ = _ ≫ _ ≫ (𝔸(ULift.{u} (Fin (m + n + 1)); S) ↘ S)
    rw [coordinateSubspaceEmbedding_over S m (n + 1), coordinateSubspaceEmbedding_over S (m + n) 1,
      coordinateSubspaceEmbedding_over S m n]
  · rename_i i
    obtain ⟨i⟩ := i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have h₁ := fun (j : Fin (m + n)) => congrArg (coordinateSubspaceEmbedding S m n).appTop.hom
      (coordinateSubspaceEmbedding_firstCoordinate S (m + n) 1 j)
    induction i using Fin.addCases with
    | left j =>
      exact (coordinateSubspaceEmbedding_firstCoordinate S m (n + 1) j).trans
        ((coordinateSubspaceEmbedding_firstCoordinate S m n j).symm.trans (h₁ _).symm)
    | right j =>
      induction j using Fin.addCases with
      | left j =>
        exact (coordinateSubspaceEmbedding_lastCoordinate S m (n + 1) _).trans
          ((coordinateSubspaceEmbedding_lastCoordinate S m n j).symm.trans (h₁ _).symm)
      | right j =>
        refine (coordinateSubspaceEmbedding_lastCoordinate S m (n + 1) _).trans ?_
        rw [← map_zero (coordinateSubspaceEmbedding S m n).appTop.hom,
          ← coordinateSubspaceEmbedding_lastCoordinate S (m + n) 1 j]
        congr 4
        ext
        simp

/-- The coordinate subspace of codimension zero is the identity. -/
theorem coordinateSubspaceEmbedding_zero (S : Scheme.{u}) (m : ℕ) :
    coordinateSubspaceEmbedding S m 0 = 𝟙 _ := by
  ext1
  · rw [coordinateSubspaceEmbedding_over, Category.id_comp]
    rfl
  · rename_i i
    obtain ⟨i⟩ := i
    exact coordinateSubspaceEmbedding_firstCoordinate S m 0 i

/-! ### Flags of principal smooth divisors -/

private theorem isPrincipalFlag_of_isPullback_aux {T X : Scheme.{u}} {ι : T ⟶ X} {c : ℕ}
    (hf : IsPrincipalFlag k ι c) :
    ∀ {T' X' : Scheme.{u}} {ι' : T' ⟶ X'} {g' : T' ⟶ T} {g : X' ⟶ X}, Smooth g →
      IsPullback ι' g' g ι → IsPrincipalFlag k ι' c := by
  induction hf with
  | single i φ ψ hφ hT =>
    intro T' X' ι' g' g hg h
    exact .single ι' (g ≫ φ) (g' ≫ ψ) inferInstance (h.paste_vert hT)
  | cons i' i h₀ φ ψ hφ hT ih =>
    intro T' X' ι' g' g hg h
    have hY := IsPullback.of_hasPullback g i
    have h'' : IsPullback (pullback.lift ι' (g' ≫ i') (by rw [h.w, Category.assoc]))
        g' (pullback.snd g i) i' :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact h) (pullback.lift_snd _ _ _) hY
    have := IsPrincipalFlag.cons _ (pullback.fst g i) (ih inferInstance h'') (g ≫ φ)
      (pullback.snd g i ≫ ψ) inferInstance (hY.paste_vert hT)
    rwa [pullback.lift_fst] at this

/-- **A flag of principal smooth divisors pulls back along a smooth morphism**: the fibre of a
smooth `φ : X ⟶ 𝔸¹` over the origin pulls back to that of the smooth `φ ∘ g`. -/
theorem IsPrincipalFlag.of_isPullback {T X : Scheme.{u}} {ι : T ⟶ X} {c : ℕ}
    (hf : IsPrincipalFlag k ι c) {T' X' : Scheme.{u}} {ι' : T' ⟶ X'} {g' : T' ⟶ T}
    {g : X' ⟶ X} [Smooth g] (h : IsPullback ι' g' g ι) : IsPrincipalFlag k ι' c :=
  isPrincipalFlag_of_isPullback_aux k hf inferInstance h

/-- **The coordinate flag** `𝔸^m_k ⊆ 𝔸^{m+1}_k ⊆ ⋯ ⊆ 𝔸^{m+n}_k`: for `n ≥ 1` the coordinate
subspace of codimension `n` is a flag of principal smooth divisors of length `n`, each step the
fibre of a coordinate projection over the origin. -/
theorem isPrincipalFlag_coordinateSubspaceEmbedding (m n : ℕ) (hn : 1 ≤ n) :
    IsPrincipalFlag k (coordinateSubspaceEmbedding (Spec (.of k)) m n) n := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact .single _ (lastCoordinateProjection k m) _ inferInstance
      (isPullback_coordinateSubspaceEmbedding_one k m)
  | succ n hn ih =>
    rw [coordinateSubspaceEmbedding_succ]
    exact .cons _ _ ih (lastCoordinateProjection k (m + n)) _ inferInstance
      (isPullback_coordinateSubspaceEmbedding_one k (m + n))

/-! ### The relative dimension count -/

/-- An open of a scheme smooth of relative dimension `d` over a field that is étale over affine
`r`-space has `d = r`, provided it is nonempty. -/
theorem eq_of_etale_affineSpace {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (d : ℕ)
    [SmoothOfRelativeDimension d p] (U : Y.Opens) (y : U) (r : ℕ)
    (π : U.toScheme ⟶ 𝔸(ULift.{u} (Fin r); Spec (.of k))) [Etale π] : d = r := by
  have := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver (Spec (.of k)) r
  have h₁ := topologicalKrullDimAt_eq_of_etale U.ι y
  have h₂ := topologicalKrullDimAt_eq_of_etale π y
  rw [topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field d p] at h₁
  rw [topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field r
    (𝔸(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k))] at h₂
  exact_mod_cast h₁.symm.trans h₂

end Stacks.EtaleCohomology.Purity

namespace Stacks.EtaleCohomology.Purity

open Stacks.AlgebraicGeometry

variable {ℓ : ℕ}

/-- A purity class in the sense of `Stacks.EtaleCohomology.Purity.IsPurityClassFun` for a direct
image along a closed immersion is one in the sense of `Stacks.EtaleCohomology.IsPurityClass`. -/
theorem IsPurityClassFun.isPurityClass [Fact ℓ.Prime] {T Y : Scheme.{u}} {i : T ⟶ Y}
    [IsClosedImmersion i] {A : EtaleModules.{u, 0} (ZMod ℓ) Y} {c : ℕ}
    {γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) A c}
    (h : IsPurityClassFun ℓ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) A γ) :
    IsPurityClass i A γ :=
  ⟨fun G q => h.1 G q _ rfl, h.2⟩

/-- A purity class in the sense of `Stacks.EtaleCohomology.IsPurityClass` is one in the sense of
`Stacks.EtaleCohomology.Purity.IsPurityClassFun`. -/
theorem _root_.Stacks.EtaleCohomology.IsPurityClass.isPurityClassFun [Fact ℓ.Prime]
    {T Y : Scheme.{u}} {i : T ⟶ Y} [IsClosedImmersion i] {A : EtaleModules.{u, 0} (ZMod ℓ) Y}
    {c : ℕ} {γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) A c}
    (h : IsPurityClass i A γ) :
    IsPurityClassFun ℓ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) A γ :=
  isPurityClassFun_of_rfl _ _ γ h.1 h.2

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **Purity in codimension zero**: along a closed immersion that is an isomorphism, the
identification `i_* Λ_T ≅ Λ_Y` is a purity class of degree `0`. -/
theorem exists_purityClassFun_of_isIso {T Y : Scheme.{u}} (i : T ⟶ Y) [IsClosedImmersion i]
    [IsIso i] :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
        (unitSheaf (X := Y) ℓ) 0,
      IsPurityClassFun ℓ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) (unitSheaf (X := Y) ℓ) γ := by
  have : (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).IsEquivalence :=
    isEquivalence_smallEtalePushforward_hom (asIso i) (ModuleCat.{u + 1} (ZMod ℓ))
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i
  have : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  let eT : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Y) ℓ) ≅
      unitSheaf (X := T) ℓ :=
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) i).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  let e : (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ) ≅
      unitSheaf (X := Y) ℓ :=
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).mapIso eT.symm ≪≫
      (asIso (adj.unit.app (unitSheaf (X := Y) ℓ))).symm
  refine ⟨Ext.mk₀ e.hom, isPurityClassFun_of_rfl _ _ _ (fun G q => ?_)
    (fun G q hq => absurd hq (Nat.not_lt_zero q))⟩
  exact (bijective_comp_mk₀_iso e q).comp
    (bijective_mapExtAddHom_etaleModuleDirectImage_closedImmersion (ZMod ℓ) i G _ q)

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Local cohomological purity for smooth pairs, with coefficients `ℤ/N`** (SGA 4 XVI 3.7,
local form). Let `k` be algebraically closed, `N` an integer invertible in `k`, `Y` smooth over
`k` of relative dimension `d + c` and `i : T ⟶ Y` a closed immersion with `T` smooth over `k` of
relative dimension `d`. Every point of `T` has an open neighbourhood `U ⊆ Y` over which
`T ∩ U ⟶ U` has a purity class in degree `2c` for `Λ = ℤ/N`.

Proof: by Stacks 0FUE there are an open `U ∋ x` and an étale `π : U ⟶ 𝔸^{m+n}_k` with
`T ∩ U = π⁻¹(𝔸^m_k)`; counting dimensions, `m = d` and `n = c`. The coordinate subspace
`𝔸^m_k ⊆ 𝔸^{m+n}_k` is a flag of `n` principal smooth divisors, whose pullback along `π` is a flag
of principal smooth divisors from `T ∩ U` to `U`; purity along such flags is
`Stacks.EtaleCohomology.Purity.exists_purityClass_of_isPrincipalFlag`. For `c = 0` the inclusion
`T ∩ U ⟶ U` is an isomorphism. -/
@[sga "5 I 5.1" "Purity clause of I 5.1"]
theorem localPurityFun (N : ℕ) (hN : IsUnit (N : k)) (Y T : Scheme.{u}) (p : Y ⟶ Spec (.of k))
    (i : T ⟶ Y) [IsClosedImmersion i] (d c : ℕ) [SmoothOfRelativeDimension (d + c) p]
    [SmoothOfRelativeDimension d (i ≫ p)] (x : T) :
    ∃ U : Y.Opens, i.base x ∈ U ∧
      ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U)).obj
          (unitSheaf (X := (i ⁻¹ᵁ U).toScheme) N)) (unitSheaf (X := U.toScheme) N) (2 * c),
        IsPurityClassFun N (etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U))
          (unitSheaf (X := U.toScheme) N) γ := by
  have : Smooth p := SmoothOfRelativeDimension.smooth (d + c) p
  have : Smooth (i ≫ p) := SmoothOfRelativeDimension.smooth d (i ≫ p)
  obtain ⟨m, n, U, hxU, π, q, hπ, -, hpb⟩ :=
    exists_etale_coordinateSubspaceEmbedding_isPullback p i x
  have : Etale q := MorphismProperty.of_isPullback (P := @Etale) hpb hπ
  have : Smooth π := SmoothOfRelativeDimension.smooth 0 π
  have hU : d + c = m + n := eq_of_etale_affineSpace k p (d + c) U ⟨i.base x, hxU⟩ (m + n) π
  have hV : d = m := eq_of_etale_affineSpace k (i ≫ p) d (i ⁻¹ᵁ U) ⟨x, hxU⟩ m q
  obtain rfl : n = c := by omega
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hpb
  refine ⟨U, hxU, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsIso (coordinateSubspaceEmbedding (Spec (.of k)) m 0) := by
      rw [coordinateSubspaceEmbedding_zero]
      infer_instance
    have : IsIso (i ∣_ U) := hpb.isIso_fst_of_isIso
    exact exists_purityClassFun_of_isIso (ℓ := N) (i ∣_ U)
  · exact exists_purityClass_of_isPrincipalFlag (ℓ := N) hN
      ((isPrincipalFlag_coordinateSubspaceEmbedding k m n hn).of_isPullback k hpb)

/-- **Local cohomological purity for smooth pairs** (SGA 4 XVI 3.7, local form), in the form of
`Stacks.EtaleCohomology.LocalPurity`: for `ℓ` a prime invertible in the algebraically closed
field `k`, `Y` smooth of relative dimension `d + c` and `T ⊆ Y` closed and smooth of relative
dimension `d`, every point of `T` has an open neighbourhood `N ⊆ Y` over which `T ∩ N ⟶ N` has a
purity class in degree `2c` for `Λ = ℤ/ℓ`. This is `localPurityFun` at `N = ℓ`. -/
@[sga "4 XIX 3.2" "special case", sga "5 I 5.1" "Purity clause of I 5.1"]
theorem localPurity (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) : LocalPurity ℓ k := by
  intro Y T p i _ d c _ _ x
  obtain ⟨U, hxU, γ, hγ⟩ := localPurityFun k ℓ hℓ Y T p i d c x
  exact ⟨U, hxU, γ, hγ.isPurityClass⟩

end Stacks.EtaleCohomology.Purity

end
