module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseOpenUnitIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# A locally constant sheaf on an integral normal scheme is a direct image from a dense open

Let `X` be an integral normal scheme, `h : V ⟶ X` an open immersion with `V` nonempty, `Λ` a ring
and `F` a locally constant sheaf of `Λ`-modules on `X_étale`. Then the unit `F ⟶ h_* h⁻¹ F` is an
isomorphism (`Stacks.EtaleCohomology.lisseOpenUnitIsoInput`).

As `h` is étale, `h⁻¹` is restriction and the unit on sections over an étale `U ⟶ X` is the
restriction `F(U) ⟶ F(U ×_X V)` along the projection. If `F|_U` is the sheaf of locally constant
`E`-valued maps, this is the restriction of locally constant maps along the dense open
`U ×_X V ⊆ U`, which is bijective because every point of `U` has an irreducible open
neighbourhood ([Tag 09Z5](https://stacks.math.columbia.edu/tag/09Z5) (2),
`Stacks.EtaleCohomology.isIso_locallyConstantMapsModuleDirectImageMap_of_isOpenImmersion`).
Every étale `X`-scheme is covered by such `U`, so the unit is locally injective and locally
surjective, hence an isomorphism of sheaves.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleModuleRestrictionDirectImageAdj_unit_app_of_iso`: the
  unit is bijective on sections over an étale `U` on which `F` is constant.
* `Stacks.EtaleCohomology.lisseOpenUnitIsoInput`: the proposition
  `Stacks.EtaleCohomology.LisseOpenUnitIsoInput` holds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasSheafify_over_etaleModules_locallyConstantSections

/-- **The unit `F ⟶ h_* h⁻¹ F` is bijective over an étale `U` on which `F` is constant.** For an
open immersion `h : Y ⟶ X` with `Y` nonempty into an integral normal scheme and an étale
`X`-scheme `U` with `F|_U` isomorphic to the sheaf of locally constant `E`-valued maps, the unit
of restriction against direct image is bijective on sections over `U`: it is restriction of
locally constant maps along the dense open `U ×_X Y ⊆ U` (Tag 09Z5 (2)). -/
theorem bijective_etaleModuleRestrictionDirectImageAdj_unit_app_of_iso {X Y : Scheme.{u}}
    [IsIntegral X] [IsNormal X] (h : Y ⟶ X) [IsOpenImmersion h] [Nonempty Y] (Λ : Type) [Ring Λ]
    (F : EtaleModules.{u, 0} Λ X) (U : X.Etale) (E : ModuleCat.{u + 1} Λ)
    (eU : (etaleModuleRestriction.{u, 0} Λ U.hom).obj F ≅
      smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} Λ U.left E) :
    Function.Bijective
      (((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ h).unit.app F).hom.app (op U)) := by
  let C := Scheme.Etale.smallEtaleCompose U.hom
  let T : U.left.Etale := Scheme.Etale.mk (𝟙 U.left)
  let T' : U.left.Etale := Scheme.Etale.mk (pullback.fst U.hom h)
  let π : T' ⟶ T := MorphismProperty.Over.homMk (pullback.fst U.hom h) (Category.comp_id _) trivial
  let c := (Scheme.Etale.smallEtaleComposeBaseChangeAdj h).counit.app U
  let a : C.obj T ≅ U := MorphismProperty.Over.isoMk (Iso.refl _)
  let b : (Scheme.Etale.smallEtaleCompose h).obj ((smallEtaleBaseChange h).obj U) ≅ C.obj T' :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      show 𝟙 _ ≫ pullback.fst U.hom h ≫ U.hom = pullback.snd U.hom h ≫ h
      rw [Category.id_comp, pullback.condition])
  have hc : c = b.hom ≫ C.map π ≫ a.hom := by
    apply MorphismProperty.Over.Hom.ext
    show pullback.fst U.hom h = 𝟙 _ ≫ pullback.fst U.hom h ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  have hφ : ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ h).unit.app F).hom.app (op U) =
      F.obj.map a.hom.op ≫ F.obj.map (C.map π).op ≫ F.obj.map b.hom.op := by
    show F.obj.map c.op = _
    rw [hc, op_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc]
  let Θ : ∀ U' : U.left.Etale, F.obj.obj (op (C.obj U')) →ₗ[Λ] LocallyConstant U'.left E :=
    fun U' => (eU.hom.hom.app (op U')).hom
  have hΘ : ∀ U', Function.Bijective (Θ U') := fun U' =>
    ConcreteCategory.bijective_of_isIso (eU.hom.hom.app (op U'))
  have hΘnat : ∀ x : F.obj.obj (op (C.obj T)),
      Θ T' ((F.obj.map (C.map π).op).hom x) = (Θ T x).comap (pullback.fst U.hom h).base.hom :=
    fun x => ConcreteCategory.congr_hom (eU.hom.hom.naturality π.op) x
  have hcomap : Function.Bijective
      (fun s : LocallyConstant U.left E => s.comap (pullback.fst U.hom h).base.hom) :=
    have := isIso_locallyConstantMapsModuleDirectImageMap_of_isOpenImmersion Λ h E
    ConcreteCategory.bijective_of_isIso
      ((locallyConstantMapsModuleDirectImageMap Λ h E).hom.app (op U))
  have hmid : Function.Bijective (F.obj.map (C.map π).op).hom := by
    refine (Function.Bijective.of_comp_iff' (hΘ T') _).1 ?_
    rw [show Θ T' ∘ (F.obj.map (C.map π).op).hom =
      (fun s : LocallyConstant U.left E => s.comap (pullback.fst U.hom h).base.hom) ∘ Θ T from
        funext hΘnat]
    exact hcomap.comp (hΘ T)
  rw [hφ]
  show Function.Bijective (fun x => (F.obj.map b.hom.op).hom
    ((F.obj.map (C.map π).op).hom ((F.obj.map a.hom.op).hom x)))
  exact (ConcreteCategory.bijective_of_isIso (F.obj.map b.hom.op)).comp
    (hmid.comp (ConcreteCategory.bijective_of_isIso (F.obj.map a.hom.op)))

/-- **[Tag 09Z5](https://stacks.math.columbia.edu/tag/09Z5) (2) for locally constant sheaves.**
For a locally constant sheaf `F` of `Λ`-modules on an integral normal scheme `X` and an open
immersion `h : V ⟶ X` with `V` nonempty, the unit `F ⟶ h_* h⁻¹ F` is an isomorphism. -/
theorem lisseOpenUnitIsoInput : LisseOpenUnitIsoInput.{u} := by
  intro X V _ _ h _ _ Λ _ Q F hF
  let φ := (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ h).unit.app F
  let G := (etaleModuleDirectImage.{u, 0} Λ h).obj ((etaleModuleRestriction.{u, 0} Λ h).obj F)
  have hnat : ∀ {A B : X.Etaleᵒᵖ} (g : A ⟶ B) (x : F.obj.obj A),
      φ.hom.app B (F.obj.map g x) = G.obj.map g (φ.hom.app A x) := fun g x =>
    ConcreteCategory.congr_hom (φ.hom.naturality g) x
  have hcov : ∀ W : X.Etale, ∃ (I : Type (u + 1)) (Vi : I → X.Etale) (fi : ∀ i, Vi i ⟶ W),
      Sieve.ofArrows Vi fi ∈ X.smallEtaleTopology W ∧
        ∀ i, Function.Bijective (φ.hom.app (op (Vi i))) := by
    intro W
    obtain ⟨I, Vi, fi, hI, htriv⟩ := hF W
    refine ⟨I, Vi, fi, hI, fun i => ?_⟩
    obtain ⟨E, -, ⟨e⟩⟩ := htriv i
    exact bijective_etaleModuleRestrictionDirectImageAdj_unit_app_of_iso h Λ F (Vi i) E
      (((etaleModuleInverseImageRestrictionIso.{u, 0} Λ (Vi i).hom).app F).symm ≪≫
        etaleModuleInverseImageIsoConstantOfOverPullback (Vi i) Λ F E e ≪≫
        smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0} Λ (Vi i).left E)
  have : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ h).unit.app F) := by
    have : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u + 1} Λ)) :=
      ModuleCat.forget_preservesLimitsOfSize.{u, u + 1, u + 1, 0}
    have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u + 1} Λ)) :=
      CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize X.smallEtaleTopology
        (F := forget (ModuleCat.{u + 1} Λ))
    refine (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨⟨fun {W} x y hxy => ?_⟩, ⟨fun {W} s => ?_⟩⟩
    · obtain ⟨I, Vi, fi, hI, hb⟩ := hcov W.unop
      refine X.smallEtaleTopology.superset_covering ?_ hI
      rintro _ _ ⟨_, k, _, ⟨i⟩, rfl⟩
      have hi : F.obj.map (fi i).op x = F.obj.map (fi i).op y := by
        refine (hb i).1 ?_
        rw [hnat, hnat]
        exact congrArg _ hxy
      show F.obj.map (k ≫ fi i).op x = F.obj.map (k ≫ fi i).op y
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hi]
    · obtain ⟨I, Vi, fi, hI, hb⟩ := hcov W
      refine X.smallEtaleTopology.superset_covering ?_ hI
      rintro _ _ ⟨_, k, _, ⟨i⟩, rfl⟩
      obtain ⟨t, ht⟩ := (hb i).2 (G.obj.map (fi i).op s)
      refine ⟨F.obj.map k.op t, ?_⟩
      show φ.hom.app _ (F.obj.map k.op t) = G.obj.map (k ≫ fi i).op s
      rw [hnat, ht, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have : (etaleModuleInverseImageAdj.{u, 0} Λ h).unit.app F =
      (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ h).unit.app F ≫
      (etaleModuleDirectImage.{u, 0} Λ h).map
        (((etaleModuleInverseImageAdj.{u, 0} Λ h).leftAdjointUniq
          (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ h)).inv.app F) := by
    rw [← (etaleModuleInverseImageAdj.{u, 0} Λ h).unit_leftAdjointUniq_hom_app
        (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ h) F, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  rw [this]
  infer_instance

end Stacks.EtaleCohomology

end
