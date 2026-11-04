module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineChartVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveChart
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.EtaleNeighbourhoodConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageFamilyVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `R^q j_*(j⁻¹ H) = 0` for `q ≥ 2` along an étale divisor of a smooth relative curve

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement of `Z` and `N` an integer
invertible in `k`. For every locally constant sheaf `H` of finite type of `ℤ/N`-modules on `U`,
`R^q j_*(j⁻¹ H) = 0` for `q ≥ 2`: this is `(P2)` of
`Stacks.EtaleCohomology.RelativeCurvePuritySheafInput`
(`Stacks.EtaleCohomology.Purity.purityHigherDirectImageVanishing_of_affineLine`), given the
vanishing of `R^q j_*` in degrees `≥ 2` along `𝐆_m ⊆ 𝐀¹_k`
(`Stacks.EtaleCohomology.Purity.AffineLineTorsionVanishing k`).

The vanishing is checked after inverse image along a jointly surjective family of étale maps to
`U` (`Stacks.EtaleCohomology.isZero_of_forall_isZero_etaleModuleInverseImage`). Over `U₀` the
restriction of `R^q j_*` vanishes for `q ≥ 1`. Around a point of `Z` choose a chart
`φ : V ⟶ 𝐀¹_k`, smooth with `Z ∩ V = φ⁻¹(0)`
(`Stacks.EtaleCohomology.Purity.exists_smooth_affineLine_chart`), and an étale `T ⟶ V` on which
`H` is constant
(`Stacks.EtaleCohomology.exists_etale_inverseImage_constant_of_isFiniteTypeLocallyConstant`). By
smooth base change (Stacks 0EYU) along the étale `e : T ⟶ U`, `e⁻¹ R^q j_*(j⁻¹ H)` is `R^q h_*`
of a constant sheaf along the complement `h` of the fibre of the smooth `T ⟶ 𝐀¹_k` over the
origin, and a constant sheaf there is the inverse image of the constant sheaf on `𝐆_m`; that
vanishes by `Stacks.EtaleCohomology.Purity.isZero_rightDerived_of_isPullback_affineLine`.

## Main results

* `Stacks.EtaleCohomology.Purity.purityHigherDirectImageVanishing_of_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

/-- The underlying abelian sheaf of a sheaf of `ℤ/N`-modules is killed by `N`. -/
theorem nsmul_id_etaleModuleForgetUniv_zmod {X : Scheme.{u}} {N : ℕ}
    (M : EtaleModules.{u, 0} (ZMod N) X) :
    N • 𝟙 ((etaleModuleForgetAb.{u, 0} (ZMod N) X).obj M) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
    nsmul_id_sheaf_zmod_eq M (a := N) (b := 0) (by simp), zero_smul, Functor.map_zero]

/-- To show that the inverse image of a higher direct image of sheaves of modules vanishes, it
suffices to show it for the underlying abelian sheaves. -/
theorem isZero_etaleModuleInverseImage_rightDerived_of_ab (Λ : Type) [Ring Λ]
    {U U₀ T : Scheme.{u}} (j : U₀ ⟶ U) (e : T ⟶ U) (F : EtaleModules.{u, 0} Λ U₀) (q : ℕ)
    (h : IsZero ((smallEtalePullbackAb e).obj (((smallEtalePushforwardAb j).rightDerived q).obj
      ((etaleModuleForgetAb.{u, 0} Λ U₀).obj F)))) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ e).obj
      (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj F)) :=
  isZero_of_isZero_etaleModuleForget_obj Λ T <| h.of_iso <|
    ((etaleModuleForgetInverseImageIso.{u, 0} Λ e).app _).symm ≪≫
      (etaleAbelianInverseImage.{u, 0} e).mapIso
        (etaleModuleForgetRightDerivedDirectImageIso Λ j F q) ≪≫
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage e).app _).symm

variable {k : Type u} [Field k]

/-- A natural number invertible in a field is positive. -/
private theorem pos_of_isUnit_natCast {k : Type*} [Field k] {N : ℕ} (hN : IsUnit (N : k)) :
    0 < N :=
  Nat.pos_of_ne_zero fun h => hN.ne_zero (by rw [h, Nat.cast_zero])

/-- A scheme smooth of relative dimension one over a smooth `k`-scheme is locally noetherian. -/
private theorem isLocallyNoetherian_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {U W : Scheme.{u}} (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W)
    [SmoothOfRelativeDimension 1 g] : IsLocallyNoetherian U := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  exact LocallyOfFiniteType.isLocallyNoetherian (g ≫ pW)

/-- A point of the source of a cartesian square over the origin of `𝐀¹_k` is in the image of the
top map exactly when its image in `𝐀¹_k` is not in `𝐆_m`. -/
theorem mem_range_iff_of_isPullback_origin {V T : Scheme.{u}} (ι : T ⟶ V)
    (ψ : T ⟶ Spec (.of k)) (φ : V ⟶ affineLine k) (hpb : IsPullback ι ψ φ (origin k)) (v : V) :
    v ∈ Set.range ι.base ↔ φ.base v ∉ (punctured k : Set (affineLine k)) := by
  have hι : Set.range ι.base = φ.base ⁻¹' Set.range (origin k).base := by
    rw [← hpb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      ← Scheme.Pullback.range_fst]
    exact Function.Surjective.range_comp (Scheme.homeoOfIso hpb.isoPullback).surjective _
  rw [hι, range_origin]
  rfl

/-- A point of an open `V` is in the image of the restriction of `i` to `V` exactly when its image
is in the image of `i`. -/
theorem mem_range_morphismRestrict_iff {Z U : Scheme.{u}} (i : Z ⟶ U) (V : U.Opens) (v : V) :
    v ∈ Set.range (i ∣_ V).base ↔ V.ι.base v ∈ Set.range i.base := by
  have hc : ∀ w, V.ι.base ((i ∣_ V).base w) = i.base ((i ⁻¹ᵁ V).ι.base w) := fun w => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, (hc w).symm⟩
  · rintro ⟨z, hz⟩
    have hzV : z ∈ i ⁻¹ᵁ V := by
      show i.base z ∈ V
      rw [hz]
      exact v.2
    exact ⟨⟨z, hzV⟩, V.ι.isOpenEmbedding.injective ((hc _).trans hz)⟩

/-- The constant sheaf of a trivialization, after a further inverse image, on the underlying
abelian sheaves. -/
theorem nonempty_smallEtalePullbackAb_forget_iso_constant (Λ : Type) [Ring Λ]
    {U T S : Scheme.{u}} (H : EtaleModules.{u, 0} Λ U) (e : T ⟶ U)
    (E : ModuleCat.{u + 1} Λ)
    (c : (etaleModuleInverseImage.{u, 0} Λ e).obj H ≅
      (constantSheaf (smallEtaleTopology T) (ModuleCat.{u + 1} Λ)).obj E) (s : S ⟶ T) :
    Nonempty ((smallEtalePullbackAb (s ≫ e)).obj ((etaleModuleForgetAb.{u, 0} Λ U).obj H) ≅
      (constantSheaf (smallEtaleTopology S) Ab.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).obj E)) :=
  ⟨((smallEtalePullbackAbCompIso' s e (s ≫ e) rfl).app _).symm ≪≫
    (smallEtalePullbackAb s).mapIso
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage e).app _ ≪≫
        (etaleModuleForgetInverseImageIso.{u, 0} Λ e).app H ≪≫
        (etaleModuleForgetAb.{u, 0} Λ T).mapIso c ≪≫
        (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ (smallEtaleTopology T)).app E) ≪≫
    (smallEtalePullbackAbConstantIso s).app _⟩

/-- For a constant sheaf on a trivialization `e₁`, the restriction along an open immersion `j`,
pulled back along a commutative square from `j` to `e₁`, is the inverse image of the constant
sheaf along any further map, on the underlying abelian sheaves. -/
theorem nonempty_smallEtalePullbackAb_restriction_iso_constant (Λ : Type) [Ring Λ]
    {U U₀ T₁ Y S : Scheme.{u}} (H : EtaleModules.{u, 0} Λ U) (j : U₀ ⟶ U) [IsOpenImmersion j]
    (e₁ : T₁ ⟶ U) (E : ModuleCat.{u + 1} Λ)
    (c : (etaleModuleInverseImage.{u, 0} Λ e₁).obj H ≅
      (constantSheaf (smallEtaleTopology T₁) (ModuleCat.{u + 1} Λ)).obj E)
    (a : Y ⟶ U₀) (s : Y ⟶ T₁) (hw : s ≫ e₁ = a ≫ j) (φ : Y ⟶ S) :
    Nonempty ((smallEtalePullbackAb a).obj ((etaleModuleForgetAb.{u, 0} Λ U₀).obj
        ((etaleModuleRestriction.{u, 0} Λ j).obj H)) ≅
      (smallEtalePullbackAb φ).obj ((etaleModuleForgetAb.{u, 0} Λ S).obj
        ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u + 1} Λ)).obj E))) := by
  obtain ⟨cY⟩ := nonempty_smallEtalePullbackAb_forget_iso_constant Λ H e₁ E c s
  exact ⟨(smallEtalePullbackAb a).mapIso
      ((etaleModuleForgetAb.{u, 0} Λ U₀).mapIso
        ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app H).symm ≪≫
      ((etaleModuleForgetInverseImageIso.{u, 0} Λ j).app H).symm ≪≫
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage j).app _).symm) ≪≫
    (smallEtalePullbackAbCompIso' a j (s ≫ e₁) hw).app _ ≪≫ cY ≪≫
    ((smallEtalePullbackAbConstantIso φ).app _).symm ≪≫
    (smallEtalePullbackAb φ).mapIso
      ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ (smallEtaleTopology S)).app E).symm⟩

/-- On a chart `φ : V ⟶ 𝐀¹_k` with `Z ∩ V = φ⁻¹(0)`, a point of `V` maps into `𝐆_m` exactly when
it lies in the open complement `U₀` of `Z`. -/
theorem mem_punctured_iff_mem_range_of_isPullback_origin {Z U U₀ : Scheme.{u}} (i : Z ⟶ U)
    (j : U₀ ⟶ U) (hj : Set.range j.base = (Set.range i.base)ᶜ) (V : U.Opens)
    (ψ : (i ⁻¹ᵁ V).toScheme ⟶ Spec (.of k)) (φ : V.toScheme ⟶ affineLine k)
    (hpb : IsPullback (i ∣_ V) ψ φ (origin k)) (v : V) :
    φ.base v ∈ (punctured k : Set (affineLine k)) ↔ V.ι.base v ∈ Set.range j.base := by
  have h₁ := mem_range_iff_of_isPullback_origin (i ∣_ V) ψ φ hpb v
  have h₂ := mem_range_morphismRestrict_iff i V v
  rw [hj, Set.mem_compl_iff]
  exact ⟨fun hp hm => h₁.1 (h₂.2 hm) hp, fun hn => by_contra fun hp => hn (h₂.1 (h₁.2 hp))⟩

/-- If `φ : T ⟶ 𝐀¹_k` sends exactly the points over the open `U₀ ⊆ U` into `𝐆_m`, then the
restriction of `T` to `U₀` is the inverse image of `𝐆_m` under `φ`. -/
theorem exists_isPullback_punctured_of_mem_range {U U₀ T : Scheme.{u}} (j : U₀ ⟶ U)
    [IsOpenImmersion j] (e : T ⟶ U) (φ : T ⟶ affineLine k)
    (h : ∀ t, φ.base t ∈ (punctured k : Set (affineLine k)) ↔ e.base t ∈ Set.range j.base) :
    ∃ φ₀ : pullback j e ⟶ (punctured k).toScheme,
      IsPullback (pullback.snd j e) φ₀ φ (punctured k).ι := by
  have H' : φ ⁻¹ᵁ (punctured k).ι.opensRange = (pullback.snd j e).opensRange := by
    ext t
    show φ.base t ∈ Set.range (punctured k).ι.base ↔ t ∈ Set.range (pullback.snd j e).base
    rw [Scheme.Opens.range_ι, Scheme.Pullback.range_snd]
    exact h t
  have hsub : Set.range (pullback.snd j e ≫ φ).base ⊆ Set.range (punctured k).ι.base := by
    rintro _ ⟨y, rfl⟩
    have : (pullback.snd j e).base y ∈ ((pullback.snd j e).opensRange : Set _) := ⟨y, rfl⟩
    rw [← H'] at this
    exact this
  let φ₀ := IsOpenImmersion.lift (punctured k).ι (pullback.snd j e ≫ φ) hsub
  exact ⟨φ₀, (IsOpenImmersion.isPullback φ₀ (pullback.snd j e) (punctured k).ι φ
    (IsOpenImmersion.lift_fac _ _ _).symm H').flip⟩

/-- Around a point of `Z`, the higher direct images `R^q j_*(j⁻¹ H)`, `q ≥ 2`, vanish after
inverse image along an étale map, given the vanishing along `𝐆_m ⊆ 𝐀¹_k`. -/
theorem exists_etale_isZero_inverseImage_rightDerived_of_mem_range (k : Type u) [Field k]
    (N : ℕ) (hN : IsUnit (N : k)) (hA : AffineLineTorsionVanishing k) {U W Z U₀ : Scheme.{u}}
    (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
    (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) (H : EtaleModules.{u, 0} (ZMod N) U)
    (hH : lccModules U N H) (q : ℕ) (hq : 2 ≤ q)
    (htors : ∀ (t : GeometricPoint U₀) (a : (smallEtaleStalkAb t.hom).obj
        ((etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj
          ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(U, ⊤)) ∧ n • a = 0) (z : Z) :
    ∃ (T : Scheme.{u}) (e : T ⟶ U), i.base z ∈ Set.range e.base ∧
      IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) e).obj
        (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived q).obj
          ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))) := by
  have hN0 := pos_of_isUnit_natCast hN
  have := isLocallyNoetherian_of_smoothOfRelativeDimension pW g
  have : IsSeparated j := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated j := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  set Fa := (etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj
    ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H)
  obtain ⟨V, hzV, π, ψ, hπ, -, hsm, hpb⟩ := exists_smooth_affineLine_chart k pW g i z
  obtain ⟨T₁, e₁, he₁, E, ⟨t₁, ht₁⟩, -, ⟨c⟩⟩ :=
    exists_etale_inverseImage_constant_of_isFiniteTypeLocallyConstant (ZMod N) H hH (i.base z)
  let T : T₁.Opens := e₁ ⁻¹ᵁ V
  let e : T.toScheme ⟶ U := T.ι ≫ e₁
  have : Etale e := inferInstance
  have : Smooth e := SmoothOfRelativeDimension.smooth 0 e
  let φV : V.toScheme ⟶ affineLine k := π ≫ affineLineBaseMap k pW
  let φT : T.toScheme ⟶ affineLine k := (e₁ ∣_ V) ≫ φV
  have : Etale (e₁ ∣_ V) := MorphismProperty.of_isPullback (P := @Etale)
    (isPullback_morphismRestrict e₁ V).flip inferInstance
  have : Smooth (e₁ ∣_ V) := SmoothOfRelativeDimension.smooth 0 _
  have : Smooth φT := inferInstance
  have he : e = (e₁ ∣_ V) ≫ V.ι := (morphismRestrict_ι e₁ V).symm
  have ht₁T : e₁.base t₁ ∈ V := ht₁ ▸ hzV
  refine ⟨T.toScheme, e, ⟨⟨t₁, ht₁T⟩, ht₁⟩,
    isZero_etaleModuleInverseImage_rightDerived_of_ab _ j e _ q ?_⟩
  have sqU : IsPullback (pullback.snd j e) (pullback.fst j e) e j :=
    (IsPullback.of_hasPullback j e).flip
  obtain ⟨φ₀, sq⟩ := exists_isPullback_punctured_of_mem_range j e φT fun t => by
    have h₃ : e.base t = V.ι.base ((e₁ ∣_ V).base t) := by rw [he, Scheme.Hom.comp_apply]
    rw [h₃]
    exact mem_punctured_iff_mem_range_of_isPullback_origin i j hj V ψ φV hpb _
  let G := (etaleModuleForgetAb.{u, 0} (ZMod N) (punctured k).toScheme).obj
    ((constantSheaf (smallEtaleTopology (punctured k).toScheme)
      (ModuleCat.{u + 1} (ZMod N))).obj E)
  have hz := isZero_rightDerived_of_isPullback_affineLine hA φT (pullback.snd j e) φ₀ sq G N
    hN0 hN (nsmul_id_etaleModuleForgetUniv_zmod _) q hq
  obtain ⟨eF⟩ := nonempty_smallEtalePullbackAb_restriction_iso_constant (ZMod N) H j e₁ E c
    (pullback.fst j e) (pullback.snd j e ≫ T.ι)
    (by rw [Category.assoc]; exact (pullback.condition (f := j) (g := e)).symm) φ₀
  have := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth e (pullback.snd j e)
    (pullback.fst j e) j sqU Fa htors q
  exact (hz.of_iso (((smallEtalePushforwardAb (pullback.snd j e)).rightDerived q).mapIso
    eF)).of_iso (asIso ((higherBaseChangeMapAb e j (pullback.snd j e) (pullback.fst j e)
      sqU.w q).app Fa))

/-- **`(P2)` of relative purity along an étale divisor of a smooth relative curve**, given the
vanishing of `R^q j_*` in degrees `≥ 2` along `𝐆_m ⊆ 𝐀¹_k`
(`Stacks.EtaleCohomology.Purity.AffineLineTorsionVanishing k`): for `W` smooth over `k`,
`g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a closed immersion with `Z ⟶ W`
étale, `j : U₀ ⟶ U` the open complement and `N` invertible in `k`, `R^q j_*(j⁻¹ H) = 0` for
`q ≥ 2` and every locally constant sheaf `H` of finite type of `ℤ/N`-modules. -/
@[sga "4 XIX 3.2" "special case"]
theorem purityHigherDirectImageVanishing_of_affineLine (k : Type u) [Field k] (N : ℕ)
    (hN : IsUnit (N : k)) (hA : AffineLineTorsionVanishing k) {U W Z U₀ : Scheme.{u}}
    (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
    (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) :
    PurityHigherDirectImageVanishing N j := by
  intro H hH q hq
  have hN0 := pos_of_isUnit_natCast hN
  have := isLocallyNoetherian_of_smoothOfRelativeDimension pW g
  set F := (etaleModuleRestriction.{u, 0} (ZMod N) j).obj H
  set Fa := (etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj F
  have hunit : IsUnit ((N : ℤ) : Γ(U, ⊤)) := by
    exact_mod_cast isUnit_natCast_globalSections_of_over (ℓ := N) (g ≫ pW) hN
  have htors : ∀ (t : GeometricPoint U₀) (a : (smallEtaleStalkAb t.hom).obj Fa),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(U, ⊤)) ∧ n • a = 0 := fun t a =>
    ⟨N, hN0, hunit, nsmul_eq_zero_stalk_of_nsmul_id (nsmul_id_etaleModuleForgetUniv_zmod F) t a⟩
  have hloc : ∀ x : U, ∃ (T : Scheme.{u}) (e : T ⟶ U), x ∈ Set.range e.base ∧
      IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) e).obj
        (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived q).obj F)) := by
    intro x
    by_cases hx : x ∈ Set.range j.base
    · refine ⟨U₀, j, hx, isZero_etaleModuleInverseImage_rightDerived_of_ab _ j j F q ?_⟩
      exact (isZero_restriction_rightDerived_of_isOpenImmersion j Fa htors q (by omega)).of_iso
        ((smallEtalePullbackAbIsoEtaleRestriction j).app _)
    · obtain ⟨z, rfl⟩ : x ∈ Set.range i.base := by
        by_contra h
        exact hx (hj ▸ h)
      exact exists_etale_isZero_inverseImage_rightDerived_of_mem_range k N hN hA pW g i j hj H hH
        q hq htors z
  choose T e he hz using hloc
  exact isZero_of_forall_isZero_etaleModuleInverseImage (ZMod N) e
    (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, he x⟩) _ hz

end Stacks.EtaleCohomology.Purity

end
