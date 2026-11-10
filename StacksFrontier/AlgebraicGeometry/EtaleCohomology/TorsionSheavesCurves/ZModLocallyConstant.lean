module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Finite locally constant sheaves killed by a prime as sheaves of `F_ℓ`-vector spaces

An abelian sheaf `G` killed by `ℓ` is a sheaf of `ZMod ℓ`-modules
(`Stacks.ModuleCatLift.sheafOfEndAction` with the ring map `ZMod ℓ → End G`), and its underlying
abelian sheaf is `G` on the nose. If `G` is finite locally constant, this sheaf of `ZMod ℓ`-modules
is locally constant of finite type: on a slice where `G` is the constant sheaf on a finite group
`E`, it is the constant sheaf on the `F_ℓ`-vector space `E / ℓE` (the constant sheaf functor
preserves cokernels, and multiplication by `ℓ` is zero on the slice), and an isomorphism of abelian
sheaves between sheaves of `ZMod ℓ`-modules is `ZMod ℓ`-linear, the forgetful functor
`ModuleCat (ZMod ℓ) ⥤ AddCommGrpCat` being fully faithful.

## Main results

* `Stacks.EtaleCohomology.fullyFaithfulForget₂ZMod`: the forgetful functor from `ZMod ℓ`-modules
  to abelian groups is fully faithful.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_sheafOfEndAction_zmod`: a finite locally
  constant abelian sheaf killed by `ℓ` is a locally constant sheaf of `ZMod ℓ`-modules of finite
  type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ)

/-- The forgetful functor from `ZMod ℓ`-modules to abelian groups is fully faithful: an additive
map between `ZMod ℓ`-modules is `ZMod ℓ`-linear. -/
def fullyFaithfulForget₂ZMod :
    (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w}).FullyFaithful where
  preimage {_M _N} f := ModuleCat.ofHom (AddMonoidHom.toZModLinearMap ℓ f.hom)
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- An object of a preadditive category killed by `ℓ` is a module over `ℤ/ℓℤ`. -/
def zmodEndRingHomOf {D : Type*} [Category D] [Preadditive D] (A : D) (h : ℓ • 𝟙 A = 0) :
    ZMod ℓ →+* End A :=
  haveI : CharP (End A) (ringChar (End A)) := ringChar.charP _
  ZMod.castHom (ringChar.dvd (by rw [← nsmul_one]; exact End.ext h)) (End A)

/-- The constant sheaf functor on abelian groups is additive. -/
theorem constantSheaf_additive {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}] :
    (constantSheaf J AddCommGrpCat.{w}).Additive := by
  have : (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ _).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have : (presheafToSheaf J AddCommGrpCat.{w}).Additive := by
    have : HasBinaryBiproducts (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
      HasBinaryBiproducts.of_hasBinaryProducts
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (presheafToSheaf J AddCommGrpCat.{w})
    exact Functor.additive_of_preservesBinaryBiproducts _
  change (Functor.const Cᵒᵖ ⋙ presheafToSheaf J AddCommGrpCat.{w}).Additive
  infer_instance

/-- The constant sheaf `Z/ℓZ` is killed by `ℓ`. -/
theorem nsmul_id_constantSheaf_zmod {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}] :
    ℓ • 𝟙 ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} (ZMod ℓ)))) =
      0 := by
  have := constantSheaf_additive.{w} J
  have h : ℓ • 𝟙 (AddCommGrpCat.of (ULift.{w} (ZMod ℓ))) = 0 := by
    ext x
    change (ℓ • x).down = (0 : ULift.{w} (ZMod ℓ)).down
    simp
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

/-- The constant sheaf on an abelian group `E` is the constant sheaf on `E / ℓE` when
multiplication by `ℓ` is zero on it. -/
theorem isIso_constantSheaf_map_cokernel_π {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}] (E : AddCommGrpCat.{w})
    (h : ℓ • 𝟙 ((constantSheaf J AddCommGrpCat.{w}).obj E) = 0) :
    IsIso ((constantSheaf J AddCommGrpCat.{w}).map (cokernel.π (ℓ • 𝟙 E))) := by
  let K := constantSheaf J AddCommGrpCat.{w}
  have : PreservesColimitsOfSize.{0, 0} K := by
    change PreservesColimitsOfSize.{0, 0} (Functor.const Cᵒᵖ ⋙ presheafToSheaf J _)
    infer_instance
  have : K.Additive := constantSheaf_additive J
  exact CokernelCofork.IsColimit.isIso_π _ (isColimitOfHasCokernelOfPreservesColimit K _)
    (by rw [Functor.map_nsmul, K.map_id, h])

section Conversion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} (ZMod ℓ))]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})]
  [∀ U : C, (J.over U).PreservesSheafification
    (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})]

omit [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})] in
/-- **A finite locally constant abelian sheaf killed by `ℓ` is a finite type locally constant
sheaf of `F_ℓ`-vector spaces.** -/
theorem isFiniteTypeLocallyConstant_sheafOfEndAction_zmod (G : Sheaf J AddCommGrpCat.{w})
    (hG : ℓ • 𝟙 G = 0) (hlcc : Stacks.ConstantSheaf.IsFiniteLocallyConstant J G) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) J
      (Stacks.ModuleCatLift.sheafOfEndAction (ZMod ℓ) J G (zmodEndRingHomOf ℓ G hG)) := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hlcc.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  set A := (J.overPullback AddCommGrpCat.{w} (V i)).obj G
  have hA : ℓ • 𝟙 A = 0 := by
    apply Sheaf.hom_ext
    ext X x
    exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app
      (Opposite.op ((Over.forget (V i)).obj X.unop))) hG) x
  have hcE : ℓ • 𝟙 ((constantSheaf (J.over (V i)) AddCommGrpCat.{w}).obj E) = 0 := by
    calc ℓ • 𝟙 ((constantSheaf (J.over (V i)) AddCommGrpCat.{w}).obj E) =
          e.hom ≫ (ℓ • 𝟙 A) ≫ e.inv := by
            simp
      _ = 0 := by simp [hA]
  have hiso := isIso_constantSheaf_map_cokernel_π ℓ (J.over (V i)) E hcE
  set Q := cokernel (ℓ • 𝟙 E)
  have hQ : ℓ • 𝟙 Q = 0 := by
    rw [← cancel_epi (cokernel.π (ℓ • 𝟙 E)), Preadditive.comp_nsmul, Category.comp_id,
      comp_zero]
    calc ℓ • cokernel.π (ℓ • 𝟙 E) = (ℓ • 𝟙 E) ≫ cokernel.π (ℓ • 𝟙 E) := by
          rw [Preadditive.nsmul_comp, Category.id_comp]
      _ = 0 := cokernel.condition _
  have hQx : ∀ x : Q, ℓ • x = 0 := fun x => by simpa using ConcreteCategory.congr_hom hQ x
  let : Module (ZMod ℓ) Q := AddCommGroup.zmodModule hQx
  have : Finite E := hE
  have : Finite Q :=
    Finite.of_surjective _ ((AddCommGrpCat.epi_iff_surjective (cokernel.π (ℓ • 𝟙 E))).mp
      inferInstance)
  let E' := ModuleCat.of (ZMod ℓ) Q
  refine ⟨E', (ModuleCat.isFG_iff _).2 Module.Finite.of_finite, ⟨?_⟩⟩
  exact (fullyFaithfulSheafCompose (J.over (V i)) (fullyFaithfulForget₂ZMod.{w} ℓ)).preimageIso <|
    (constantCommuteCompose (J.over (V i))
      (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})).app E' ≪≫
    (asIso ((constantSheaf (J.over (V i)) AddCommGrpCat.{w}).map
      (cokernel.π (ℓ • 𝟙 E)))).symm ≪≫ e

end Conversion

end Stacks.EtaleCohomology

end
