module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.BaseChangeUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unit `H ⟶ j_* j⁻¹ H` along an étale divisor of a smooth relative curve

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement of `Z` and `N` an integer
invertible in `k`. For every locally constant sheaf `H` of finite type of `ℤ/N`-modules on `U`,
the unit `H ⟶ j_* j⁻¹ H` is an isomorphism: this is `(P0)` of
`Stacks.EtaleCohomology.RelativeCurvePuritySheafInput`
(`Stacks.EtaleCohomology.Purity.purityUnitIso_of_affineLine`), given that the unit along
`𝐆_m ⊆ 𝐀¹_k` is an isomorphism at constant torsion sheaves
(`Stacks.EtaleCohomology.Purity.AffineLineConstantUnitIso k`).

As for `(P2)` (`Stacks.EtaleCohomology.Purity.purityHigherDirectImageVanishing_of_affineLine`)
the statement is checked after inverse image along a jointly surjective family of étale maps. Over
`U₀` the restriction of the unit is invertible by the triangle identity. Around a point of `Z`,
on an étale `T ⟶ U` through a chart where `H` is constant, the underived base change map is
invertible by smooth base change, so `e⁻¹` of the unit of `j` is invertible exactly when the unit
of the complement of the fibre of `T ⟶ 𝐀¹_k` over the origin is
(`Stacks.EtaleCohomology.Purity.isIso_smallEtalePullbackAb_map_unit_iff`); the latter is reduced
in the same way to `𝐀¹_k` (`Stacks.EtaleCohomology.Purity.isIso_unit_of_isPullback_affineLine`).

## Main definitions

* `Stacks.EtaleCohomology.Purity.AffineLineConstantUnitIso`.

## Main results

* `Stacks.EtaleCohomology.Purity.isIso_unit_of_isPullback_affineLine`.
* `Stacks.EtaleCohomology.Purity.purityUnitIso_of_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- The base instance
`Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek` (reachable
through `ProperBaseChange.LowerShriekCompactification`) leaves the searches for
`(smallEtalePullbackAb _).PreservesZeroMorphisms` below stuck at a universe constraint; it is not
used here. -/
attribute [-instance] Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek

universe u

namespace Stacks.EtaleCohomology.Purity

/-- **The unit `A ⟶ j_* j⁻¹ A` along `j : 𝐆_m ⟶ 𝐀¹_k` is an isomorphism at the constant sheaf on
an abelian group killed by an integer invertible in `k`**, as a proposition about `k`. -/
def AffineLineConstantUnitIso (k : Type u) [Field k] : Prop :=
  ∀ (M : Ab.{u + 1}) (n : ℕ), 0 < n → IsUnit (n : k) → n • 𝟙 M = 0 →
    IsIso ((smallEtaleAdjunctionAb (punctured k).ι).unit.app
      ((constantSheaf (smallEtaleTopology (affineLine k)) Ab.{u + 1}).obj M))

/-- A component of a natural transformation at an object isomorphic to one where it is invertible
is invertible. -/
theorem isIso_app_of_iso_of_isIso {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (α : F ⟶ G) {X Y : C} (c : X ≅ Y) (h : IsIso (α.app X)) : IsIso (α.app Y) := by
  have e : α.app Y = F.map c.inv ≫ α.app X ≫ G.map c.hom := by
    rw [← α.naturality, ← CategoryTheory.Functor.map_comp_assoc, c.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [e]
  infer_instance

/-- An additive functor sends an object killed by `n` to an object killed by `n`. -/
private theorem nsmul_id_obj_eq_zero {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {X : C} {n : ℕ} (h : n • 𝟙 X = 0) :
    n • 𝟙 (F.obj X) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

/-- A constant abelian sheaf on a group killed by `n` is killed by `n`. -/
theorem nsmul_id_constantSheaf {T : Scheme.{u}} {M : Ab.{u + 1}} {n : ℕ} (hM : n • 𝟙 M = 0) :
    n • 𝟙 ((constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj M) = 0 :=
  nsmul_id_obj_eq_zero _ hM

variable {k : Type u} [Field k]

/-- **Transport of the unit along a smooth `φ : Y ⟶ 𝐀¹_k`.** For a cartesian square
`h : Y₀ ⟶ Y`, `φ₀ : Y₀ ⟶ 𝐆_m` over `φ` and `j : 𝐆_m ⟶ 𝐀¹_k`, and an abelian group `M` killed by
`n` invertible in `k`, the unit of `h` at the constant sheaf `M` on `Y` is invertible given
`Stacks.EtaleCohomology.Purity.AffineLineConstantUnitIso k`: by smooth base change in degree zero
the underived base change map is invertible, so `φ⁻¹` of the unit of `j` is carried to the unit
of `h`. -/
theorem isIso_unit_of_isPullback_affineLine (hB : AffineLineConstantUnitIso k)
    {Y Y₀ : Scheme.{u}} (φ : Y ⟶ affineLine k) [Smooth φ] (h : Y₀ ⟶ Y)
    (φ₀ : Y₀ ⟶ (punctured k).toScheme) (sq : IsPullback h φ₀ φ (punctured k).ι)
    (M : Ab.{u + 1}) (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k)) (hM : n • 𝟙 M = 0) :
    IsIso ((smallEtaleAdjunctionAb h).unit.app
      ((constantSheaf (smallEtaleTopology Y) Ab.{u + 1}).obj M)) := by
  have : IsSeparated (punctured k).ι := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated (punctured k).ι := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  let A := (constantSheaf (smallEtaleTopology (affineLine k)) Ab.{u + 1}).obj M
  have hn' : IsUnit ((n : ℤ) : Γ(affineLine k, ⊤)) := by
    exact_mod_cast isUnit_natCast_globalSections_of_over (ℓ := n) (affineLine k ↘ Spec (.of k)) hnk
  have hjA : n • 𝟙 ((smallEtalePullbackAb (punctured k).ι).obj A) = 0 := by
    exact nsmul_id_obj_eq_zero _ (nsmul_id_constantSheaf hM)
  have hβ0 := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth φ h φ₀ (punctured k).ι sq
    ((smallEtalePullbackAb (punctured k).ι).obj A)
    (fun t a => ⟨n, hn, hn', nsmul_eq_zero_stalk_of_nsmul_id hjA t a⟩) 0
  have hβ := (isIso_higherBaseChangeMapAb_zero_app_iff φ (punctured k).ι h φ₀ sq.w _).1 hβ0
  have := hB M n hn hnk hM
  have hu := (isIso_smallEtalePullbackAb_map_unit_iff φ (punctured k).ι h φ₀ sq.w A hβ).1
    inferInstance
  exact isIso_app_of_iso_of_isIso _ ((smallEtalePullbackAbConstantIso φ).app M) hu

/-- The restriction/direct-image adjunction of abelian sheaves along an étale `j`. -/
abbrev etaleRestrictionAbAdj {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) [Etale j] :=
  (smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := Ab.{u + 1})
    (smallEtaleTopology U₀) (smallEtaleTopology U)

/-- The underlying abelian map of the unit of the restriction/direct-image adjunction of sheaves
of modules is the unit of the abelian one. -/
theorem etaleModuleForgetUniv_map_restrictionDirectImageUnit (Λ : Type) [Ring Λ]
    {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) [Etale j] (H : EtaleModules.{u, 0} Λ U) :
    (etaleModuleForgetAb.{u, 0} Λ U).map
        ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H) =
      (etaleRestrictionAbAdj j).unit.app ((etaleModuleForgetAb.{u, 0} Λ U).obj H) :=
  rfl

/-- To show that the inverse image of the unit of sheaves of `ℤ/N`-modules is invertible, it
suffices to show it for the underlying abelian unit. -/
theorem isIso_etaleModuleInverseImage_map_unit_of_ab {N : ℕ} {U₀ U T : Scheme.{u}}
    (j : U₀ ⟶ U) [Etale j] (e : T ⟶ U) (H : EtaleModules.{u, 0} (ZMod N) U)
    (h : IsIso ((smallEtalePullbackAb e).map
      ((etaleRestrictionAbAdj j).unit.app ((etaleModuleForgetAb.{u, 0} (ZMod N) U).obj H)))) :
    IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) e).map
      ((etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j).unit.app H)) := by
  have h2 : IsIso ((etaleModuleForgetAb.{u, 0} (ZMod N) T).map
      ((etaleModuleInverseImage.{u, 0} (ZMod N) e).map
        ((etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j).unit.app H))) := by
    have h3 : IsIso ((etaleAbelianInverseImage.{u, 0} e).map
        ((etaleModuleForgetAb.{u, 0} (ZMod N) U).map
          ((etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j).unit.app H))) := by
      rw [etaleModuleForgetUniv_map_restrictionDirectImageUnit]
      exact (NatIso.isIso_map_iff (smallEtalePullbackAbIsoEtaleAbelianInverseImage e) _).1 h
    exact (NatIso.isIso_map_iff (etaleModuleForgetInverseImageIso.{u, 0} (ZMod N) e) _).1 h3
  exact (Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful (X := T) N).isIso_of_isIso_map _

/-- `N` kills a module over `ℤ/N`. -/
theorem nsmul_id_forget₂_zmod {N : ℕ} (E : ModuleCat.{u + 1} (ZMod N)) :
    N • 𝟙 ((forget₂ (ModuleCat.{u + 1} (ZMod N)) Ab.{u + 1}).obj E) = 0 := by
  refine nsmul_id_obj_eq_zero _ ?_
  ext x
  show N • x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]

/-- The restriction along an étale monomorphism `j` of the unit `F ⟶ j_* j⁻¹ F` is invertible,
by the triangle identity. -/
private theorem isIso_etaleRestriction_map_unit {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) [Etale j]
    [Mono j] (F : Sheaf (smallEtaleTopology U) Ab.{u + 1}) :
    IsIso ((etaleRestriction.{u, 0} j).map ((etaleRestrictionAbAdj j).unit.app F)) := by
  have := isIso_smallEtaleRestrictionAdjunctionAb_counit j
  have ht : (etaleRestriction.{u, 0} j).map ((etaleRestrictionAbAdj j).unit.app F) ≫
      (etaleRestrictionAbAdj j).counit.app ((etaleRestriction.{u, 0} j).obj F) = 𝟙 _ :=
    (etaleRestrictionAbAdj j).left_triangle_components F
  have hc : IsIso ((etaleRestrictionAbAdj j).counit.app ((etaleRestriction.{u, 0} j).obj F)) :=
    NatIso.isIso_app_of_isIso _ _
  have h1 : IsIso ((etaleRestriction.{u, 0} j).map ((etaleRestrictionAbAdj j).unit.app F) ≫
      (etaleRestrictionAbAdj j).counit.app ((etaleRestriction.{u, 0} j).obj F)) := by
    rw [ht]
    exact IsIso.id _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hc h1

/-- An open immersion `s : P ⟶ T` onto the preimage of `𝐆_m` under `φT : T ⟶ 𝐀¹_k` is the base
change of `𝐆_m ⊆ 𝐀¹_k` along `φT`. -/
private theorem exists_isPullback_punctured_of_preimage_eq {T P : Scheme.{u}} (s : P ⟶ T)
    [IsOpenImmersion s] (φT : T ⟶ affineLine k)
    (H' : φT ⁻¹ᵁ (punctured k).ι.opensRange = s.opensRange) :
    ∃ φ₀ : P ⟶ (punctured k).toScheme, IsPullback s φ₀ φT (punctured k).ι := by
  have hsub : Set.range (s ≫ φT).base ⊆ Set.range (punctured k).ι.base := by
    rintro _ ⟨y, rfl⟩
    have : s.base y ∈ (s.opensRange : Set _) := ⟨y, rfl⟩
    rwa [← H'] at this
  exact ⟨IsOpenImmersion.lift (punctured k).ι (s ≫ φT) hsub,
    (IsOpenImmersion.isPullback _ s (punctured k).ι φT
      (IsOpenImmersion.lift_fac _ _ _).symm H').flip⟩

/-- **The unit of an open immersion `j` after a smooth `e` over `𝐀¹_k`.** If `j⁻¹ A` is killed by
`N` invertible in `k`, `e⁻¹ A` is constant on a group killed by `N`, and the base change of `j`
along `e` is the base change of `𝐆_m ⊆ 𝐀¹_k` along a smooth `φT`, then `e⁻¹` of the unit
`A ⟶ j_* j⁻¹ A` is invertible given `Stacks.EtaleCohomology.Purity.AffineLineConstantUnitIso k`. -/
private theorem isIso_smallEtalePullbackAb_map_unit_of_affineLine
    (hB : AffineLineConstantUnitIso k) {U U₀ T : Scheme.{u}} (j : U₀ ⟶ U) [QuasiCompact j]
    [QuasiSeparated j] (e : T ⟶ U) [Smooth e] (φT : T ⟶ affineLine k) [Smooth φT]
    (φ₀ : pullback j e ⟶ (punctured k).toScheme)
    (sq : IsPullback (pullback.snd j e) φ₀ φT (punctured k).ι) (N : ℕ) (hN0 : 0 < N)
    (hN : IsUnit (N : k)) (hunit : IsUnit ((N : ℤ) : Γ(U, ⊤)))
    (A : Sheaf (smallEtaleTopology U) Ab.{u + 1}) (hA : N • 𝟙 ((smallEtalePullbackAb j).obj A) = 0)
    (M : Ab.{u + 1}) (hM : N • 𝟙 M = 0)
    (cT : (smallEtalePullbackAb e).obj A ≅
      (constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj M) :
    IsIso ((smallEtalePullbackAb e).map ((smallEtaleAdjunctionAb j).unit.app A)) := by
  have sqU : IsPullback (pullback.snd j e) (pullback.fst j e) e j :=
    (IsPullback.of_hasPullback j e).flip
  have hβ0 := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth e
    (pullback.snd j e) (pullback.fst j e) j sqU ((smallEtalePullbackAb j).obj A)
    (fun t a => ⟨N, hN0, hunit, nsmul_eq_zero_stalk_of_nsmul_id hA t a⟩) 0
  have hβ := (isIso_higherBaseChangeMapAb_zero_app_iff e j (pullback.snd j e)
    (pullback.fst j e) sqU.w _).1 hβ0
  rw [isIso_smallEtalePullbackAb_map_unit_iff e j (pullback.snd j e) (pullback.fst j e) sqU.w
    A hβ]
  exact isIso_app_of_iso_of_isIso _ cT.symm
    (isIso_unit_of_isPullback_affineLine hB φT (pullback.snd j e) φ₀ sq M N hN0 hN hM)

/-- **`(P0)` of relative purity near a point of the divisor.** In the setting of
`Stacks.EtaleCohomology.Purity.purityUnitIso_of_affineLine`, every point of `Z` lies in the image
of an étale `e : T ⟶ U` along which the inverse image of the unit `H ⟶ j_* j⁻¹ H` is
invertible. -/
private theorem exists_isIso_inverseImage_unit_of_mem_divisor (k : Type u) [Field k] (N : ℕ)
    (hN : IsUnit (N : k)) (hB : AffineLineConstantUnitIso k) {U W Z U₀ : Scheme.{u}}
    (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
    (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) (H : EtaleModules.{u, 0} (ZMod N) U)
    (hH : lccModules U N H) (z : Z) :
    ∃ (T : Scheme.{u}) (e : T ⟶ U), i.base z ∈ Set.range e.base ∧
      IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) e).map
        ((etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j).unit.app H)) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h => hN.ne_zero (by rw [h, Nat.cast_zero])
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pW)
  have : IsSeparated j := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated j := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  set Ha := (etaleModuleForgetAb.{u, 0} (ZMod N) U).obj H
  obtain ⟨V, hzV, π, ψ, hπ, -, hsm, hpb⟩ := exists_smooth_affineLine_chart k pW g i z
  obtain ⟨T₁, e₁, he₁, E, ⟨t₁, ht₁⟩, -, ⟨c⟩⟩ :=
    exists_etale_inverseImage_constant_of_isFiniteTypeLocallyConstant (ZMod N) H hH (i.base z)
  let T : T₁.Opens := e₁ ⁻¹ᵁ V
  let e : T.toScheme ⟶ U := T.ι ≫ e₁
  have : Etale e := inferInstance
  have : Smooth e := SmoothOfRelativeDimension.smooth 0 e
  let φV : V.toScheme ⟶ affineLine k := π ≫ affineLineBaseMap k pW
  let φT : T.toScheme ⟶ affineLine k := (e₁ ∣_ V) ≫ φV
  have : Smooth (e₁ ∣_ V) := by
    have : Etale (e₁ ∣_ V) := MorphismProperty.of_isPullback (P := @Etale)
      (isPullback_morphismRestrict e₁ V).flip inferInstance
    exact SmoothOfRelativeDimension.smooth 0 _
  have : Smooth φT := inferInstance
  have he : e = (e₁ ∣_ V) ≫ V.ι := (morphismRestrict_ι e₁ V).symm
  have ht₁T : t₁ ∈ T := by
    show e₁.base t₁ ∈ V
    rw [ht₁]
    exact hzV
  refine ⟨T.toScheme, e, ⟨⟨t₁, ht₁T⟩, ht₁⟩, isIso_etaleModuleInverseImage_map_unit_of_ab j e H ?_⟩
  have hmem : ∀ t : T.toScheme,
      φT.base t ∈ (punctured k : Set (affineLine k)) ↔ e.base t ∈ Set.range j.base := by
    intro t
    have h1 := mem_range_iff_of_isPullback_origin (i ∣_ V) ψ φV hpb ((e₁ ∣_ V).base t)
    have h2 := mem_range_morphismRestrict_iff i V ((e₁ ∣_ V).base t)
    have h3 : e.base t = V.ι.base ((e₁ ∣_ V).base t) := by
      rw [he, Scheme.Hom.comp_apply]
    rw [hj, Set.mem_compl_iff, h3, ← h2]
    show φV.base ((e₁ ∣_ V).base t) ∈ _ ↔ _
    exact ⟨fun hp hm => h1.1 hm hp, fun hn => by_contra fun hp => hn (h1.2 hp)⟩
  have H' : φT ⁻¹ᵁ (punctured k).ι.opensRange = (pullback.snd j e).opensRange := by
    ext t
    show φT.base t ∈ Set.range (punctured k).ι.base ↔ t ∈ Set.range (pullback.snd j e).base
    rw [Scheme.Opens.range_ι, Scheme.Pullback.range_snd]
    exact hmem t
  obtain ⟨φ₀, sq⟩ := exists_isPullback_punctured_of_preimage_eq (pullback.snd j e) φT H'
  have hκ : (smallEtaleAdjunctionAb j).unit.app Ha ≫ (smallEtalePushforwardAb j).map
      ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app Ha) =
      (etaleRestrictionAbAdj j).unit.app Ha :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ Ha
  suffices hu : IsIso ((smallEtalePullbackAb e).map ((smallEtaleAdjunctionAb j).unit.app Ha)) by
    have key : IsIso ((smallEtalePullbackAb e).map ((smallEtaleAdjunctionAb j).unit.app Ha ≫
        (smallEtalePushforwardAb j).map
          ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app Ha))) := by
      rw [CategoryTheory.Functor.map_comp]
      infer_instance
    exact hκ ▸ key
  have hjH : N • 𝟙 ((smallEtalePullbackAb j).obj Ha) = 0 := by
    exact nsmul_id_obj_eq_zero _ (nsmul_id_etaleModuleForgetUniv_zmod H)
  have hunit : IsUnit ((N : ℤ) : Γ(U, ⊤)) := by
    exact_mod_cast isUnit_natCast_globalSections_of_over (ℓ := N) (g ≫ pW) hN
  obtain ⟨cT⟩ := nonempty_smallEtalePullbackAb_forget_iso_constant (ZMod N) H e₁ E c T.ι
  exact isIso_smallEtalePullbackAb_map_unit_of_affineLine hB j e φT φ₀ sq N hN0 hN hunit Ha hjH
    _ (nsmul_id_forget₂_zmod E) cT

/-- **`(P0)` of relative purity along an étale divisor of a smooth relative curve**, given that
the unit along `𝐆_m ⊆ 𝐀¹_k` is invertible at constant torsion sheaves
(`Stacks.EtaleCohomology.Purity.AffineLineConstantUnitIso k`): for `W` smooth over `k`,
`g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a closed immersion with `Z ⟶ W`
étale, `j : U₀ ⟶ U` the open complement and `N` invertible in `k`, the unit `H ⟶ j_* j⁻¹ H` is
an isomorphism for every locally constant sheaf `H` of finite type of `ℤ/N`-modules. -/
@[sga "4 XIX 3.2" "Codimension-one case"]
theorem purityUnitIso_of_affineLine (k : Type u) [Field k] (N : ℕ) (hN : IsUnit (N : k))
    (hB : AffineLineConstantUnitIso k) {U W Z U₀ : Scheme.{u}}
    (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
    (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) :
    PurityUnitIso N j := by
  intro H hH
  have hloc : ∀ x : U, ∃ (T : Scheme.{u}) (e : T ⟶ U), x ∈ Set.range e.base ∧
      IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) e).map
        ((etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j).unit.app H)) := by
    intro x
    by_cases hx : x ∈ Set.range j.base
    · refine ⟨U₀, j, hx, isIso_etaleModuleInverseImage_map_unit_of_ab j j H ?_⟩
      rw [NatIso.isIso_map_iff (smallEtalePullbackAbIsoEtaleRestriction j)]
      exact isIso_etaleRestriction_map_unit j _
    · obtain ⟨z, rfl⟩ : x ∈ Set.range i.base := by
        by_contra h
        exact hx (hj ▸ h)
      exact exists_isIso_inverseImage_unit_of_mem_divisor k N hN hB pW g i j hj H hH z
  choose T e he hiso using hloc
  exact isIso_of_isIso_etaleModuleInverseImage_family (ZMod N) e
    (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, he x⟩) _ hiso

end Stacks.EtaleCohomology.Purity

end
