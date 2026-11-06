module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.TorsionReduction

/-!
# Torsion sheaves as filtered colimits of constructible ones, and the reduction of Tag 03SC

Let `X` be a quasi-compact quasi-separated scheme and `G` an abelian sheaf on `X_étale` killed by
a positive integer `ℓ`. Then `G` is a sheaf of modules over the finite ring `ℤ/ℓℤ`, so by Stacks
Tag 03SA (3) it is a filtered colimit of constructible sheaves of `ℤ/ℓℤ`-modules; a sheaf of
modules over a finite ring which is constructible is a constructible abelian sheaf, because a
finitely generated module over a finite ring is finite. This is the step of the proof of Stacks
Tag 03SC which reduces the eight assertions to constructible sheaves.

## Main results

* `Stacks.EtaleCohomology.isConstructibleAbelianSheaf_forget₂`: a constructible sheaf of modules
  over a finite Noetherian ring is a constructible abelian sheaf.
* `Stacks.EtaleCohomology.exists_isColimit_isConstructibleEtaleSheaf_of_nsmul_id_eq_zero`: an
  abelian sheaf killed by `ℓ` is a filtered colimit of constructible sheaves killed by `ℓ`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_constructible`: if the eight assertions hold
  for every constructible sheaf killed by a prime, they hold for every torsion sheaf.

## Implementation notes

The module structure is `Stacks.ModuleCatLift.sheafOfEndAction`, whose underlying abelian sheaf is
the original sheaf on the nose. Tag 03SA (3) is available on the small étale site of Tag 021B and
is transported to Mathlib's small étale site along `AlgebraicGeometry.SmallEtale.sheafEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The forgetful functor from `Λ`-modules to abelian groups is a left adjoint. -/
theorem isLeftAdjoint_forget₂_moduleCat :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
    ⟨_, ⟨ModuleCat.restrictCoextendScalarsAdj.{u + 1} (Int.castRingHom Λ)⟩⟩
  show (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  infer_instance

attribute [local instance] isLeftAdjoint_forget₂_moduleCat

/-- Over a finite ring `Λ`, a sheaf of `Λ`-modules which is locally constant with finitely
generated values is finite locally constant as an abelian sheaf. -/
theorem isFiniteLocallyConstant_forget₂ [Finite Λ] {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{u + 1} Λ)]
    (N : Sheaf J (ModuleCat.{u + 1} Λ))
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ J (ModuleCat.isFG Λ) N) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((sheafCompose J (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj N) where
  exists_finite_cover U := by
    obtain ⟨I, V, f, hf, h⟩ := hN U
    refine ⟨I, V, f, hf, fun i => ?_⟩
    obtain ⟨E, hE, ⟨e⟩⟩ := h i
    have : Module.Finite Λ E := (ModuleCat.isFG_iff _).1 hE
    have : Finite E := Module.finite_of_finite Λ
    exact ⟨(forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj E, this,
      ⟨((constantCommuteCompose (J.over (V i))
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app E).symm ≪≫
        (sheafCompose (J.over (V i))
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso e⟩⟩

variable (B : BigEtaleSite.{u})

/-- Pushforward of sheaves of `Λ`-modules along small étale base change is a right adjoint, at the
coefficient universe `u + 1`. -/
local instance isRightAdjoint_pushforward_moduleCat (S T : B.Scheme) (f : T ⟶ S) :
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1} B Λ f

/-- Weak sheafification of presheaves of `Λ`-modules on a localization of the small étale site,
at the coefficient universe `u + 1`. -/
local instance hasWeakSheafify_over_moduleCat (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ) :=
  SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1} B Λ T V

/-- Inverse image along small étale base change commutes with forgetting a module structure. -/
theorem nonempty_sheafPullback_forget₂_iso {X T : B.Scheme} (g : T ⟶ X)
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    Nonempty ((sheafCompose (SmallEtale.topology B T.obj T.property)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPullback (ModuleCat.{u + 1} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B T.obj T.property)).obj M) ≅
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B T.obj T.property)).obj
        ((sheafCompose (SmallEtale.topology B X.obj X.property)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M)) := by
  let Φ := AlgebraicGeometry.smallEtaleBaseChange B g
  let _ : ∀ P : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Y => by
    let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Y) (ModuleCat.{u + 1} Λ)
    infer_instance
  let _ : ∀ P : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Y => by
    let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Y) AddCommGrpCat.{u + 1}
    infer_instance
  let _ : ∀ Y : (SmallEtale B T.obj T.property)ᵒᵖ,
      PreservesColimitsOfShape (CostructuredArrow Φ.op Y)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := fun Y => inferInstance
  exact ⟨(Φ.sheafPullbackSheafComposeIso (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B T.obj T.property)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M).symm⟩

/-- **A constructible sheaf of modules over a finite ring is a constructible abelian sheaf.** -/
theorem isConstructibleAbelianSheaf_forget₂ [Finite Λ] [IsNoetherianRing Λ] (X : B.Scheme)
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hM : IsConstructibleModuleSheaf B X Λ M) :
    IsConstructibleAbelianSheaf B X ((sheafCompose (SmallEtale.topology B X.obj X.property)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M) := by
  intro U
  obtain ⟨s, hs⟩ := hM U
  refine ⟨s, fun i => ?_⟩
  obtain ⟨e⟩ := nonempty_sheafPullback_forget₂_iso Λ B (s.inclusion i) M
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _ e
    (hF := isFiniteLocallyConstant_forget₂ Λ _ _ (hs i))

section ZMod

variable (ℓ : ℕ)

/-- An object of a preadditive category killed by `ℓ` is a module over `ℤ/ℓℤ`: the ring map from
`ℤ/ℓℤ` (lifted to the universe `u + 1`) to its endomorphism ring. -/
def uliftZModEndRingHom {D : Type*} [Category D] [Preadditive D] (A : D) (h : ℓ • 𝟙 A = 0) :
    ULift.{u + 1} (ZMod ℓ) →+* End A :=
  haveI : CharP (End A) (ringChar (End A)) := ringChar.charP _
  (ZMod.castHom (ringChar.dvd (by
      rw [← nsmul_one]; apply End.addEquiv.injective
      rw [map_nsmul, map_zero]; exact h)) (End A)).comp
    (ULift.ringEquiv (R := ZMod ℓ)).toRingHom

/-- A sheaf of modules over `ℤ/ℓℤ` is killed by `ℓ` as an abelian sheaf. -/
theorem nsmul_id_sheafCompose_forget₂_eq_zero {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    (N : Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    ℓ • 𝟙 ((sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      AddCommGrpCat.{u + 1})).obj N) = 0 := by
  have key : ∀ (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) (y : M), ℓ • y = 0 := by
    intro M y
    have h0 : (ℓ : ULift.{u + 1} (ZMod ℓ)) = 0 := by
      apply ULift.ext
      simp
    rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod ℓ)), h0, zero_smul]
  ext U x
  exact key (N.obj.obj U) x

end ZMod

/-- **An abelian sheaf killed by `ℓ` is a filtered colimit of constructible sheaves killed by
`ℓ`.** On a quasi-compact quasi-separated scheme, Stacks Tag 03SA (3) for the Noetherian ring
`ℤ/ℓℤ`, read on Mathlib's small étale site. -/
theorem exists_isColimit_isConstructibleEtaleSheaf_of_nsmul_id_eq_zero (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (ℓ : ℕ) [NeZero ℓ]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : ℓ • 𝟙 G = 0) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (c : Cocone D),
      Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ G) ∧
        ∀ i, IsConstructibleSmallEtaleSheaf (D.obj i) ∧ ℓ • 𝟙 (D.obj i) = 0 := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  let XB : B.Scheme := B.obj X hX
  have : CompactSpace XB.obj := ‹CompactSpace X›
  have : QuasiSeparatedSpace XB.obj := ‹QuasiSeparatedSpace X›
  let Λ := ULift.{u + 1} (ZMod ℓ)
  let GB := (toBoundedSiteAb B hX).obj G
  let eqv := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have : eqv.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eqv.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have hGB : ℓ • 𝟙 GB = 0 := by
    show ℓ • 𝟙 (eqv.inverse.obj G) = 0
    rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul, hG, Functor.map_zero]
  let M := Stacks.ModuleCatLift.sheafOfEndAction Λ (SmallEtale.topology B X hX) GB
    (uliftZModEndRingHom ℓ GB hGB)
  let F₁ := sheafCompose (SmallEtale.topology B X hX)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  obtain ⟨I, hI, hf, D, ι, ⟨hcol⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs B XB Λ M
  have : PreservesColimitsOfShape I F₁ := preservesColimitsOfShape_sheafCompose _ _ I
  refine ⟨I, hI, hf, D ⋙ F₁ ⋙ eqv.functor, (F₁ ⋙ eqv.functor).mapCocone (Cocone.mk M ι),
    ⟨isColimitOfPreserves _ hcol⟩, ⟨eqv.functor.mapIso (Iso.refl GB) ≪≫ eqv.counitIso.app G⟩,
    fun i => ⟨⟨B, hX, ?_⟩, ?_⟩⟩
  · exact isConstructibleAbelianSheaf_congr B XB (eqv.unitIso.app (F₁.obj (D.obj i)))
      (isConstructibleAbelianSheaf_forget₂ Λ B XB _ (hD i))
  · show ℓ • 𝟙 (eqv.functor.obj (F₁.obj (D.obj i))) = 0
    rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul,
      nsmul_id_sheafCompose_forget₂_eq_zero, Functor.map_zero]

section Zero

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

/-- Every section of an abelian sheaf killed by `ℓ` is killed by `ℓ`. -/
theorem nsmul_section_eq_zero_of_nsmul_id_eq_zero {ℓ : ℕ} {G : Sheaf J AddCommGrpCat.{u + 1}}
    (hG : ℓ • 𝟙 G = 0) {U : Cᵒᵖ} (x : G.obj.obj U) : ℓ • x = 0 := by
  have := congrArg (fun φ : G ⟶ G => φ.hom.app U x) hG
  simp only at this
  rw [← natCast_zsmul, Stacks.Cohomology.ZModSheaf.zsmul_app_apply] at this
  simpa using this

/-- An abelian sheaf killed by `ℓ` is locally killed by `ℓ`. -/
theorem locallyKilledBy_of_nsmul_id_eq_zero {P : ℕ → Prop} {ℓ : ℕ} (hℓ : P ℓ)
    {G : Sheaf J AddCommGrpCat.{u + 1}} (hG : ℓ • 𝟙 G = 0) :
    Stacks.Torsion.LocallyKilledBy J P G := fun U x =>
  ⟨⊤, J.top_mem U, fun _ _ _ => ⟨ℓ, hℓ, nsmul_section_eq_zero_of_nsmul_id_eq_zero J hG _⟩⟩

/-- An abelian sheaf killed by `ℓ` and locally killed by integers prime to `ℓ` is zero. -/
theorem isZero_of_locallyKilledBy_of_nsmul_id_eq_zero {P : ℕ → Prop} {ℓ : ℕ}
    (hP : ∀ n, P n → Nat.Coprime n ℓ) {G : Sheaf J AddCommGrpCat.{u + 1}}
    (hG : Stacks.Torsion.LocallyKilledBy J P G) (hℓ : ℓ • 𝟙 G = 0) : IsZero G := by
  have hsep : Presieve.IsSeparated J (G.obj ⋙ forget AddCommGrpCat.{u + 1}) :=
    ((isSheaf_iff_isSheaf_of_type J _).1
      ((sheafCompose J (forget AddCommGrpCat.{u + 1})).obj G).2).isSeparated
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext U x
  show x = 0
  obtain ⟨R, hR, h⟩ := hG U.unop x
  refine (hsep R hR).ext fun V f hf => ?_
  obtain ⟨n, hn, hx⟩ := h V f hf
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr (hP n hn)
  have hl := nsmul_section_eq_zero_of_nsmul_id_eq_zero J hℓ (G.obj.map f.op x)
  show G.obj.map f.op x = G.obj.map f.op 0
  rw [map_zero, ← one_zsmul (G.obj.map f.op x), ← hab, add_zsmul, mul_zsmul, mul_zsmul,
    natCast_zsmul, natCast_zsmul, hx, hl, zsmul_zero, zsmul_zero, add_zero]

end Zero

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [AlgebraicGeometry.IsNoetherian X] [QuasiCompact f] [QuasiSeparated f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The reduction of Stacks Tag 03SC to constructible sheaves killed by a prime.** On a
Noetherian scheme `X` with a quasi-compact quasi-separated morphism to `Spec k`, if the eight
assertions hold for every constructible abelian sheaf killed by a prime number, they hold for every
torsion abelian sheaf. -/
theorem of_constructible
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsConstructibleSmallEtaleSheaf G → ℓ • 𝟙 G = 0 → TorsionCurveAssertions f G)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    TorsionCurveAssertions f F := by
  refine of_torsion f (fun ℓ hℓ G hG => ?_) F hF
  by_cases hz : IsZero G
  · exact of_isZero f hz
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨I, _, _, D, c, ⟨hc⟩, ⟨e⟩, hD⟩ :=
    exists_isColimit_isConstructibleEtaleSheaf_of_nsmul_id_eq_zero X ℓ G hG
  have hcℓ : ℓ • 𝟙 c.pt = 0 :=
    calc ℓ • 𝟙 c.pt = e.hom ≫ (ℓ • 𝟙 G) ≫ e.inv := by
          simp [Preadditive.comp_nsmul, Preadditive.nsmul_comp]
      _ = 0 := by simp [hG]
  have hnz : ¬ IsZero c.pt := fun h' => hz (h'.of_iso e.symm)
  refine of_iso f e (of_isColimit f hc (fun i => h ℓ hℓ _ (hD i).1 (hD i).2) ?_ ?_ ?_)
  · intro p hp i
    rw [Stacks.Torsion.isPrimePowerTorsion_iff_locallyKilledBy] at hp ⊢
    by_cases hdvd : ℓ ∣ p
    · obtain ⟨m, rfl⟩ := hdvd
      refine locallyKilledBy_of_nsmul_id_eq_zero _ ⟨1, one_pos, (pow_one _).symm⟩ ?_
      rw [mul_nsmul, (hD i).2, smul_zero]
    · exact (hnz (isZero_of_locallyKilledBy_of_nsmul_id_eq_zero _ (fun n ⟨r, _, hn⟩ => by
        rw [hn]
        exact (Nat.coprime_comm.mp ((hℓ.coprime_iff_not_dvd).mpr hdvd)).pow_left _) hp hcℓ)).elim
  · intro hp i
    rw [Stacks.Torsion.isPrimeToCharacteristicTorsion_iff_locallyKilledBy] at hp ⊢
    by_cases hcop : Nat.Coprime ℓ (ringExpChar k)
    · exact locallyKilledBy_of_nsmul_id_eq_zero _ ⟨hℓ.pos, hcop⟩ (hD i).2
    · have hdvd : ℓ ∣ ringExpChar k := (Nat.Prime.dvd_iff_not_coprime hℓ).mpr hcop
      exact (hnz (isZero_of_locallyKilledBy_of_nsmul_id_eq_zero _ (fun n ⟨_, hn⟩ =>
        Nat.Coprime.coprime_dvd_right hdvd hn) hp hcℓ)).elim
  · intro hcons
    obtain ⟨m, hm, hmF⟩ := exists_nsmul_id_eq_zero_of_isConstructibleEtaleSheaf hcons
      (Stacks.Torsion.torsionSheafProperty_of_isPrimePowerTorsion _ hℓ.pos
        ((Stacks.Torsion.isPrimePowerTorsion_iff_locallyKilledBy _ ℓ _).mpr
          (locallyKilledBy_of_nsmul_id_eq_zero _ ⟨1, one_pos, (pow_one _).symm⟩ hcℓ)))
    exact of_nsmul_id_eq_zero f IsConstructibleSmallEtaleSheaf
      (fun S hS h₂ => isConstructibleEtaleSheaf_outer hS h₂)
      (fun ℓ' hℓ' G' hG' hG'' => h ℓ' hℓ' G' hG' hG'') m hm.ne' c.pt hcons hmF

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
