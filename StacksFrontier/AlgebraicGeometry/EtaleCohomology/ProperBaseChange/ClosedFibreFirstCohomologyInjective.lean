module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePushforwardModuleEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.MainstreamTransportDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomologyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FilteredColimitClasses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.EtaleCoverRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSurjectiveCoverRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.AbelianSheavesAsConstantModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding

/-!
# First cohomology of an injective sheaf of `ℤ/ℓℤ`-modules on the closed fibre

Let `A` be a henselian local ring, `X` proper over `A` with closed fibre `i : X₀ ⟶ X`, `ℓ > 0`,
and `𝓘` an injective sheaf of `ℤ/ℓℤ`-modules on `X_étale`. Then `H¹(X₀, 𝓘|_{X₀}) = 0`. This is
the case `q = 1` of [Stacks, Tag 0A5H], for any `X` proper over `A`.

Injectivity of `𝓘` is used among sheaves annihilated by `ℓ`: the forgetful functor from sheaves
of `ℤ/ℓℤ`-modules to abelian sheaves is fully faithful
(`Stacks.Cohomology.ZModSheaf.toSheafFullyFaithful`) and every abelian sheaf annihilated by `ℓ`
lies in its essential image (`Stacks.Cohomology.ZModSheaf.torsionSheafToModulesIso`).

## Main results

* `Stacks.EtaleCohomology.exists_comp_eq_of_injective_toSheaf` — the extension property of the
  underlying abelian sheaf of an injective sheaf of `ℤ/ℓℤ`-modules.
* `Stacks.EtaleCohomology.subsingleton_H_one_closedFibre_of_injective` — `H¹(X₀, 𝓘|_{X₀}) = 0`,
  the case `q = 1` of [Stacks, Tag 0A5H], for any `X` proper over `A`.

## References

* [Stacks Project, Tag 0A5H](https://stacks.math.columbia.edu/tag/0A5H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.Cohomology.ZModSheaf

universe u

attribute [local instance 3000] Abelian.hasFiniteBiproducts

namespace Stacks.EtaleCohomology

section Extension

variable {X : Scheme.{u}} (ℓ : ℕ)

/-- **The extension property of an injective sheaf of `ℤ/ℓℤ`-modules among sheaves killed by
`ℓ`.** Let `𝓘` be an injective sheaf of `ℤ/ℓℤ`-modules on `X_étale`, `m : P ⟶ Q` a monomorphism of
abelian sheaves whose sections are killed by `ℓ`, and `g : P ⟶ 𝓘` a map of abelian sheaves. Then
`g` extends along `m`. -/
theorem exists_comp_eq_of_injective_toSheaf
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective J]
    {P Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hP : ∀ (U : X.Etaleᵒᵖ) (x : ToType (P.obj.obj U)), ℓ • x = 0)
    (hQ : ∀ (U : X.Etaleᵒᵖ) (x : ToType (Q.obj.obj U)), ℓ • x = 0)
    (m : P ⟶ Q) [Mono m] (g : P ⟶ (SheafOfModules.toSheaf _).obj J) :
    ∃ h : Q ⟶ (SheafOfModules.toSheaf _).obj J, m ≫ h = g := by
  let T := SheafOfModules.toSheaf.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)
  let hT := toSheafFullyFaithful.{u + 1, u + 1} X.smallEtaleTopology ℓ
  let P' := torsionSheafToModules.{u + 1, u + 1} X.smallEtaleTopology ℓ P hP
  let Q' := torsionSheafToModules.{u + 1, u + 1} X.smallEtaleTopology ℓ Q hQ
  let eP := torsionSheafToModulesIso.{u + 1, u + 1} X.smallEtaleTopology ℓ P hP
  let eQ := torsionSheafToModulesIso.{u + 1, u + 1} X.smallEtaleTopology ℓ Q hQ
  let m' : P' ⟶ Q' := hT.preimage (eP.hom ≫ m ≫ eQ.inv)
  have hm' : T.map m' = eP.hom ≫ m ≫ eQ.inv := hT.map_preimage _
  have := hT.faithful
  have : Mono m' := T.mono_of_mono_map (by rw [hm']; infer_instance)
  let g' : P' ⟶ J := hT.preimage (eP.hom ≫ g)
  refine ⟨eQ.inv ≫ T.map (Injective.factorThru g' m'), ?_⟩
  have h := congrArg T.map (Injective.comp_factorThru g' m')
  rw [T.map_comp, hm', hT.map_preimage] at h
  simpa using (cancel_epi eP.hom).1 (by simpa [Category.assoc] using h)

/-- The underlying abelian sheaf of a sheaf of `ℤ/ℓℤ`-modules on `X_étale` is killed by `ℓ`. -/
private theorem zsmul_id_toSheaf_zmodRingSheaf_eq_zero
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) :
    ((ℓ : ℤ) • 𝟙 ((SheafOfModules.toSheaf _).obj J)) = 0 := by
  apply Sheaf.hom_ext
  ext U x
  rw [zsmul_app_apply]
  change ((ℓ : ℤ) • x) = 0
  rw [natCast_zsmul]
  exact nsmul_toSheaf_eq_zero.{u + 1, u + 1} X.smallEtaleTopology ℓ J U x

end Extension


section Biproduct

/-- Yoneda composition with `Ext.mk₀` of a finite sum of morphisms is the sum of the
compositions. -/
theorem ext_comp_mk₀_sum {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C] {A B D : C}
    {q : ℕ} (y : Ext.{u + 1} A B q) {ι : Type*} (s : Finset ι) (g : ι → (B ⟶ D)) :
    y.comp (Ext.mk₀ (∑ j ∈ s, g j)) (add_zero q) =
      ∑ j ∈ s, y.comp (Ext.mk₀ (g j)) (add_zero q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ext.mk₀_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Ext.mk₀_add, Ext.comp_add, ih]

end Biproduct


section Transport

/-- `ULift (ZMod ℓ)` is Noetherian for `ℓ > 0`, being finite. -/
private instance isNoetherianRing_uliftZMod' (ℓ : ℕ) [NeZero ℓ] :
    IsNoetherianRing (ULift.{u + 1} (ZMod ℓ)) :=
  isNoetherianRing_of_ringEquiv (ZMod ℓ) ULift.ringEquiv.symm

variable (B : BigEtaleSite.{u}) (S : B.Scheme) (ℓ : ℕ)

/-- **The transport of a sheaf of `ℤ/ℓℤ`-modules is killed by `ℓ`, sectionwise.** -/
theorem nsmul_moduleSheafToEtale_eq_zero
    (G : Sheaf (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (U : S.obj.Etaleᵒᵖ)
    (x : ToType (((SmallEtale.moduleSheafToEtale B S (ULift.{u + 1} (ZMod ℓ))).obj G).obj.obj U)) :
    ℓ • x = 0 := by
  let E := SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let G' := (sheafCompose (SmallEtale.topology B S.obj S.property)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat.{u + 1})).obj G
  have h0 : ((ℓ : ℤ) • 𝟙 G') = 0 := by
    apply Sheaf.hom_ext
    ext V y
    rw [zsmul_app_apply]
    let y' : ToType (G.obj.obj V) := y
    have : ((ℓ : ℕ) : ULift.{u + 1} (ZMod ℓ)) = 0 := congrArg ULift.up (ZMod.natCast_self ℓ)
    change (ℓ : ℤ) • y' = 0
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod ℓ)), this, zero_smul]
  have h1 : ((ℓ : ℤ) • 𝟙 (E.functor.obj G')) = 0 := by
    rw [← E.functor.map_id, ← Functor.map_zsmul, h0, E.functor.map_zero]
  rw [← natCast_zsmul]
  exact congrArg (fun φ => φ.hom.app U x) h1

/-- **The transport of sheaves of modules preserves monomorphisms.** -/
theorem mono_moduleSheafToEtale_map (Λ : Type (u + 1)) [Ring Λ]
    {G H : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)} (φ : G ⟶ H)
    [Mono φ] : Mono ((SmallEtale.moduleSheafToEtale B S Λ).map φ) := by
  let E := SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}
  let F := sheafCompose (SmallEtale.topology B S.obj S.property)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hF : Mono (F.map φ) := by
    have h1 : Mono ((sheafToPresheaf _ _).map φ) := Functor.map_mono _ _
    have h2 : ∀ V, Mono (φ.hom.app V) := fun V => (NatTrans.mono_iff_mono_app _).1 h1 V
    have h3 : ∀ V, Mono ((F.map φ).hom.app V) := fun V => by
      change Mono ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (φ.hom.app V))
      exact Functor.map_mono _ _
    have : Mono (F.map φ).hom := NatTrans.mono_of_mono_app _
    exact Sheaf.Hom.mono_of_presheaf_mono _ _ _
  change Mono (E.functor.map (F.map φ))
  exact Functor.map_mono _ _

/-- **Surjectivity of restriction on cohomology passes to the transport of a finite direct
sum.** -/
private theorem surjective_etaleCohomologyRestrictionMap_moduleSheafToEtale_biproduct
    (Λ : Type (u + 1)) [Ring Λ]
    [HasSheafify (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)]
    {Y : Scheme.{u}} (i : Y ⟶ S.obj) (q : ℕ) {n : ℕ}
    (G : Fin n → Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ))
    (hG : ∀ j, Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i
      ((SmallEtale.moduleSheafToEtale B S Λ).obj (G j)) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i
      ((SmallEtale.moduleSheafToEtale B S Λ).obj (⨁ G)) q) := by
  let T := SmallEtale.moduleSheafToEtale B S Λ
  have : PreservesColimitsOfSize.{u + 1, u + 1} T :=
    SmallEtale.moduleSheafToEtale_preservesColimits B S Λ
  have : PreservesColimitsOfSize.{0, 0} T := preservesColimitsOfSize_shrink T
  have : T.IsLeftAdjoint := SmallEtale.moduleSheafToEtale_isLeftAdjoint B S Λ
  have : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint T
  have : PreservesBiproduct G T := preservesBiproduct_of_preservesCoproduct T
  exact surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse i (T.mapBiproduct G).symm q
    (surjective_etaleCohomologyRestrictionMap_biproduct i _ q hG)

end Transport


section Main

/-- **Restriction to the closed fibre is surjective on `H¹` for the transport of the direct image
of a constant sheaf of finite `ℤ/ℓℤ`-modules along a finite morphism.** -/
private theorem surjective_etaleCohomologyRestrictionMap_pushforward_constantSheaf
    (A : Type u) [CommRing A] [HenselianLocalRing A] (B : BigEtaleSite.{u}) (S : B.Scheme)
    (p : S.obj ⟶ Spec (.of A)) [IsProper p] (ℓ : ℕ) [NeZero ℓ] {T : B.Scheme} (f : T ⟶ S)
    [IsFinite (B.inclusion.map f)] (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    [Module.Finite (ULift.{u + 1} (ZMod ℓ)) M] :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion A p)
      ((SmallEtale.moduleSheafToEtale B S (ULift.{u + 1} (ZMod ℓ))).obj
        (((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj
          ((constantSheaf (SmallEtale.topology B T.obj T.property)
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj M))) 1) := by
  have : Finite M := Module.finite_of_finite (ULift.{u + 1} (ZMod ℓ))
  have : Finite
      ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat.{u + 1}).obj M) :=
    inferInstanceAs (Finite M)
  exact surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse _
    (SmallEtale.moduleSheafToEtaleDirectImageConstantIso B _ f M).symm 1
    (surjective_etaleCohomologyRestrictionMap_directImage_closedFibre_one A p
      (B.inclusion.map f) _)

/-- **[Stacks, Tag 0A5H] for `q = 1`, for any `X` proper over `A`.** Let `A` be a henselian local
ring, `p : X ⟶ Spec A` proper with closed fibre `i : X₀ ⟶ X`, `ℓ > 0`, and `𝓘` an injective sheaf
of `ℤ/ℓℤ`-modules on `X_étale`. Then `H¹(X₀, 𝓘|_{X₀}) = 0`. -/
theorem subsingleton_H_one_closedFibre_of_injective (A : Type u) [CommRing A]
    [HenselianLocalRing A] {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [IsProper p] (ℓ : ℕ)
    [NeZero ℓ] (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ))
    [Injective J] :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (closedFibreInclusion A p)).obj ((SheafOfModules.toSheaf _).obj J)) 1) := by
  let i := closedFibreInclusion A p
  let Λ := ULift.{u + 1} (ZMod ℓ)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  have : IsClosedImmersion i := isClosedImmersion_closedFibreInclusion A p
  have : CompactSpace (closedFibre A p) := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace (closedFibre A p) := quasiSeparatedSpace_of_quasiSeparated i
  let TJ := (SheafOfModules.toSheaf _).obj J
  let B := BigEtaleSite.containing X
  let XB : B.Scheme := B.obj X (BigEtaleSite.contains_containing X)
  have : CompactSpace XB.obj := ‹CompactSpace X›
  have : QuasiSeparatedSpace XB.obj := ‹QuasiSeparatedSpace X›
  let : HasSheafify (SmallEtale.topology B XB.obj XB.property) (ModuleCat.{u + 1} Λ) :=
    SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B XB Λ
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible B XB ℓ TJ
      (zsmul_id_toSheaf_zmodRingSheaf_eq_zero ℓ J)
  let T := SmallEtale.moduleSheafToEtale B XB Λ
  let Ti := etaleAbelianInverseImage.{u, 0} i
  have : PreservesColimitsOfSize.{u + 1, u + 1} Ti :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).leftAdjoint_preservesColimits
  refine subsingleton_of_forall_eq (0 : Sheaf.H.{u + 1} (Ti.obj TJ) 1) fun ξ => ?_
  obtain ⟨k, ζ, hζ⟩ :=
    exists_comp_mk₀_eq_of_isColimit (closedFibre A p) _ _ (isColimitOfPreserves Ti hc) 1 ξ
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hφ⟩ :=
    AlgebraicGeometry.exists_mono_biproduct_pushforward_constantSheaf_of_isConstructibleModuleSheaf
      B Λ XB (D.obj k) (hD k)
  have : Mono (T.map φ) := mono_moduleSheafToEtale_map B XB Λ φ
  obtain ⟨h, hh⟩ := exists_comp_eq_of_injective_toSheaf ℓ J
    (nsmul_moduleSheafToEtale_eq_zero B XB ℓ (D.obj k))
    (nsmul_moduleSheafToEtale_eq_zero B XB ℓ _) (T.map φ) (ι.app k)
  obtain ⟨η, hη⟩ :=
    surjective_etaleCohomologyRestrictionMap_moduleSheafToEtale_biproduct B XB Λ i 1 _ (fun j =>
      have : IsFinite (B.inclusion.map (f j)) := hf j
      have : Module.Finite Λ (M j) := hM j
      surjective_etaleCohomologyRestrictionMap_pushforward_constantSheaf
        A B XB p ℓ (f j) (M j))
    (ζ.comp (Ext.mk₀ (Ti.map (T.map φ))) (add_zero 1))
  have hξ : ξ = etaleCohomologyRestrictionMap.{u, 0, u + 1} i TJ 1
      (η.comp (Ext.mk₀ h) (add_zero 1)) := by
    rw [etaleCohomologyRestrictionMap_comp_mk₀, hη, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, ← Ti.map_comp, hh, ← hζ]
    rfl
  have : Subsingleton (Sheaf.H.{u + 1} TJ 1) := subsingleton_H_toSheaf_of_injective J 1 one_pos
  rw [hξ, Subsingleton.elim (η.comp (Ext.mk₀ h) (add_zero 1)) 0, map_zero]

end Main

end Stacks.EtaleCohomology

end
