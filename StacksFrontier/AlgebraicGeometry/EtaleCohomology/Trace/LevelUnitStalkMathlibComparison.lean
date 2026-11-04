module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageLevelStalkBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicStalkSheafFiberLimit

/-!
# The unit of `f⁻¹ ⊣ f_*` level by level, on the two small étale sites

Let `f : X ⟶ Y` be a morphism of the big étale site and `F` an ℓ-adic sheaf on `Y`. At level `n`
the unit `Fₙ → f_* f⁻¹ Fₙ` lives on the bounded small étale sites (Stacks 021B), while the
compactly supported cohomology of the levels is formed on Mathlib's small étale sites. This file
identifies the two units: read on Mathlib's site of `Y`, the unit of the bounded sites is the unit
`Fₙ → f_* f⁻¹ Fₙ` of Mathlib's sites followed by the direct image of the comparison of inverse
images `Stacks.EtaleCohomology.padicLevelInverseImageIso`. Both comparisons are mates of strict
commutations of direct images, so this is the compatibility of mates with units.

On stalks this gives that the stalk at a geometric point of the unit of the bounded site
(`Stacks.EtaleCohomology.levelUnitStalkMap`) is injective as soon as the stalk of the unit of
Mathlib's site is: the input from Mathlib's site in the absence of punctual sections of `R¹pr₂!`
in Laumon's degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `AlgebraicGeometry.SmallEtale.sheafEquiv_map_unit_comp_pushforwardBaseChangeIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.CategoryTheory

open _root_.CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {CS : Type u₁} {CT : Type u₂} {MS : Type u₃} {MT : Type u₄} [Category.{v₁} CS]
  [Category.{v₂} CT] [Category.{v₃} MS] [Category.{v₄} MT] (ES : CS ≌ MS) (ET : CT ≌ MT)
  {RB : CT ⥤ CS} {RM : MT ⥤ MS} {LB : CS ⥤ CT} {LM : MS ⥤ MT} (adjB : LB ⊣ RB) (adjM : LM ⊣ RM)
  (ρ : RM ⋙ ES.inverse ≅ ET.inverse ⋙ RB)

/-- **Transporting a unit along equivalences.** Let `ES`, `ET` be equivalences, `LB ⊣ RB` and
`LM ⊣ RM` adjunctions on the two sides and `ρ : RM ⋙ ES⁻¹ ≅ ET⁻¹ ⋙ RB`. Then the unit of
`LB ⊣ RB`, transported by `ES` and followed by the comparison `RB ⋙ ES ≅ ET ⋙ RM` induced by `ρ`,
is the unit of `LM ⊣ RM` followed by `RM` of the comparison `ES ⋙ LM ≅ LB ⋙ ET` of left adjoints
induced by `ρ`. -/
theorem equivalence_map_unit_comp_isoWhiskerRight_hom_app (P : CS) :
    ES.functor.map (adjB.unit.app P) ≫
        (Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
          Functor.isoWhiskerRight ET.unitIso _ ≪≫ Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ ρ.symm ≪≫ (Functor.associator _ _ _).symm) _ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ES.counitIso ≪≫
          Functor.rightUnitor _).hom.app (LB.obj P) =
      adjM.unit.app (ES.functor.obj P) ≫ RM.map ((Adjunction.leftAdjointUniq
        ((ES.toAdjunction.comp adjM).ofNatIsoRight ρ) (adjB.comp ET.toAdjunction)).hom.app P) := by
  set lam := Adjunction.leftAdjointUniq ((ES.toAdjunction.comp adjM).ofNatIsoRight ρ)
    (adjB.comp ET.toAdjunction)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ES.toAdjunction.comp adjM).ofNatIsoRight ρ) (adjB.comp ET.toAdjunction) P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  dsimp only [Equiv.trans_apply] at h
  have ha := (Iso.eq_comp_inv (ρ.app _)).2 h
  have key := (ES.toAdjunction.homEquiv _ _).symm_apply_apply (adjM.homEquiv _ _ (lam.hom.app P))
  rw [Adjunction.homEquiv_counit, ha, Adjunction.homEquiv_unit] at key
  rw [← key]
  simp [Adjunction.comp_unit_app]

/-- An equivalence carries zero objects to zero objects (with no assumption on zero morphisms):
maps out of and into `E.functor.obj P` correspond to maps out of and into `P`. -/
theorem isZero_equivalence_functor_obj {C D : Type*} [Category* C] [Category* D] (E : C ≌ D)
    {P : C} (hP : IsZero P) : IsZero (E.functor.obj P) :=
  ⟨fun _ => ⟨⟨⟨(E.toAdjunction.homEquiv _ _).symm (hP.to_ _)⟩,
      fun _ => (E.toAdjunction.homEquiv _ _).injective (hP.eq_of_src _ _)⟩⟩,
    fun _ => ⟨⟨⟨E.symm.toAdjunction.homEquiv _ _ (hP.from_ _)⟩,
      fun _ => (E.symm.toAdjunction.homEquiv _ _).symm.injective (hP.eq_of_tgt _ _)⟩⟩⟩

end Stacks.CategoryTheory

namespace AlgebraicGeometry.SmallEtale

universe v' u'

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (A : Type u') [Category.{v'} A]
  [HasLimitsOfSize.{u, u} A]
  {LU : Sheaf S.obj.smallEtaleTopology A ⥤ Sheaf T.obj.smallEtaleTopology A}
  {LB : Sheaf (topology B S.obj S.property) A ⥤ Sheaf (topology B T.obj T.property) A}
  (adjU : LU ⊣ (Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous A
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology)
  (adjB : LB ⊣ (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (topology B S.obj S.property) (topology B T.obj T.property))

/-- **The comparisons of inverse and direct images of the two presentations of the small étale
site are compatible with the units**: the unit of the bounded sites, read on Mathlib's site and
followed by the comparison of direct images, is the unit of Mathlib's sites followed by the
direct image of the comparison of inverse images. -/
theorem sheafEquiv_map_unit_comp_pushforwardBaseChangeIso
    (P : Sheaf (topology B S.obj S.property) A) :
    (sheafEquiv B S.1 S.property A).functor.map (adjB.unit.app P) ≫
        (sheafEquivFunctorPushforwardBaseChangeIso B f A).hom.app (LB.obj P) =
      adjU.unit.app ((sheafEquiv B S.1 S.property A).functor.obj P) ≫
        ((Stacks.EtaleCohomology.smallEtaleBaseChange
              (B.inclusion.map f)).sheafPushforwardContinuous
          A S.obj.smallEtaleTopology T.obj.smallEtaleTopology).map
          ((sheafEquivPullbackBaseChangeIso B f A adjU adjB).hom.app P) :=
  Stacks.CategoryTheory.equivalence_map_unit_comp_isoWhiskerRight_hom_app
    (sheafEquiv B S.1 S.property A) (sheafEquiv B T.1 T.property A) adjB adjU
    (toEtaleSitePushforwardBaseChangeIso B f A) P

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

section Level

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The unit of `f⁻¹ ⊣ f_*` at level `n`, read on Mathlib's site**: the unit of the bounded
sites for a sheaf `G` of `ℤ/ℓⁿ⁺¹`-modules on `Y`, read as a map of sheaves of `ℤ_ℓ`-modules on
Mathlib's site of `Y` and followed by the comparison of direct images, is the unit of Mathlib's
sites followed by the direct image of the comparison of inverse images
`Stacks.EtaleCohomology.padicLevelInverseImageIso`. -/
theorem padicSheafEquiv_map_levelUnit_comp (n : ℕ) (G : FiniteLevelSheaf.{u, u + 1} B Y ℓ n) :
    (padicSheafEquiv B ℓ Y).map ((padicRestrict B ℓ Y n).map
        ((LAdicSheaf.levelAdjunction f n).unit.app G)) ≫
      (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f (ModuleCat.{u + 1} ℤ_[ℓ])).hom.app
        ((padicRestrict B ℓ X n).obj ((LAdicSheaf.levelPullback f n).obj G)) =
    (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).unit.app
        ((padicSheafEquiv B ℓ Y).obj ((padicRestrict B ℓ Y n).obj G)) ≫
      (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
        (padicLevelInverseImageIso B f ℓ n G).hom := by
  have hu := coefficientSheafPullbackTwoSquare_unit (AlgebraicGeometry.smallEtaleBaseChange B f)
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (p := ℓ) (n + 1))) G
  have hPB := (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f
    (ModuleCat.{u + 1} ℤ_[ℓ])).hom.naturality ((padicRestrictInverseImage B f ℓ n).app G)
  have h1 := SmallEtale.sheafEquiv_map_unit_comp_pushforwardBaseChangeIso B f
    (ModuleCat.{u + 1} ℤ_[ℓ]) (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map f))
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafAdjunctionContinuous
      (ModuleCat.{u + 1} ℤ_[ℓ]) _ _) ((padicRestrict B ℓ Y n).obj G)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hPB
  calc _ = (padicSheafEquiv B ℓ Y).map
          (((AlgebraicGeometry.smallEtaleBaseChange B f).sheafAdjunctionContinuous
            (ModuleCat.{u + 1} ℤ_[ℓ]) _ _).unit.app ((padicRestrict B ℓ Y n).obj G)) ≫
        ((padicSheafEquiv B ℓ Y).map ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).map
          ((padicRestrictInverseImage B f ℓ n).app G)) ≫
        (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f
          (ModuleCat.{u + 1} ℤ_[ℓ])).hom.app _) :=
        (congrArg (· ≫ _) ((congrArg (padicSheafEquiv B ℓ Y).map hu).trans
          ((padicSheafEquiv B ℓ Y).map_comp _ _))).trans (Category.assoc _ _ _)
    _ = _ := congrArg (_ ≫ ·) hPB
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ _) h1
    _ = _ := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map_comp _ _).symm)

variable {f} (s : GeometricPoint Y.1) [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- **The stalk of the unit of the bounded sites through Mathlib's unit**: the stalk at `s̄` of
`Fₙ → f_* f⁻¹ Fₙ` on the bounded sites, read on Mathlib's site
(`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap` of the identity), is the stalk of the unit
`Fₙ → f_* f⁻¹ Fₙ` of Mathlib's sites followed by the stalk of the direct image of the comparison
`Stacks.EtaleCohomology.padicLevelInverseImageIso`. -/
theorem levelAdjunctPadicStalkMap_id_apply (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n : ℕ)
    (w : finiteLevelStalk B Y ℓ F s n) :
    (levelAdjunctPadicStalkMap f s F _
        (𝟙 (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F)) n).hom w =
      ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
          (padicLevelInverseImageIso B f ℓ n (F.level n)).hom)).hom
        (((Scheme.pointSmallEtale s.hom).sheafFiber.map
          ((etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).unit.app
            ((SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
              (LAdicSheaf.padicLevel B Y ℓ F n)))).hom
          ((padicLevelStalkFiberMap s F n).hom w)) := by
  let Φ := (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])
  let g := (padicRestrict B ℓ Y n).map ((LAdicSheaf.levelAdjunction f n).unit.app (F.level n))
  have key := padicSheafEquiv_map_levelUnit_comp B f ℓ n (F.level n)
  have k2 := (Φ.map_comp _ _).symm.trans ((congrArg Φ.map key).trans (Φ.map_comp _ _))
  have hext := etaleStalk_addMonoidHom_ext Y.1 Y.2 s (R := ZMod (ℓ ^ (n + 1))) (F.level n).obj
    (g₁ := (levelAdjunctPadicStalkMap f s F _
      (𝟙 (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F)) n).hom.toAddMonoidHom)
    (g₂ := ((padicLevelStalkFiberMap s F n) ≫ Φ.map
        ((etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).unit.app
          ((SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
            (LAdicSheaf.padicLevel B Y ℓ F n))) ≫
        Φ.map ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
          (padicLevelInverseImageIso B f ℓ n (F.level n)).hom)).hom.toAddMonoidHom) (fun j x => by
      have e1 := levelAdjunctPadicStalkMap_germ f s F _
        (𝟙 (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F)) n j x
      have e3 := sheafEquivCompSheafFiberIso_inv_germ_naturality s g j x
      have e4 := padicLevelStalkFiberMap_germ s F n j x
      show (levelAdjunctPadicStalkMap f s F _ _ n).hom _ =
        (Φ.map _).hom ((Φ.map _).hom ((padicLevelStalkFiberMap s F n).hom _))
      have hid : (LAdicSheaf.levelAdjunction f n).homEquiv _ _
          ((𝟙 (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F) :
            AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶
              AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F).app n) =
          (LAdicSheaf.levelAdjunction f n).unit.app (F.level n) :=
        Adjunction.homEquiv_id _ _
      rw [hid] at e1
      rw [e1, e4, directImageStalkBridge_hom_app]
      exact (congrArg (Φ.map ((SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f
        (ModuleCat.{u + 1} ℤ_[ℓ])).hom.app ((padicRestrict B ℓ X n).obj
          ((LAdicSheaf.levelPullback f n).obj (F.level n))))).hom e3.symm).trans
        (ConcreteCategory.congr_hom k2 _))
  exact DFunLike.congr_fun hext w

/-- **The stalk of the unit of the bounded sites is injective once Mathlib's is**: if the stalk
at `s̄` of the unit `Fₙ → f_* f⁻¹ Fₙ` of Mathlib's sites is injective, so is
`Stacks.EtaleCohomology.levelUnitStalkMap`. -/
theorem levelUnitStalkMap_eq_zero_imp (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n : ℕ)
    (hinj : Function.Injective ((Scheme.pointSmallEtale s.hom).sheafFiber.map
      ((etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).unit.app
        ((SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
          (LAdicSheaf.padicLevel B Y ℓ F n)))).hom)
    (w : finiteLevelStalk B Y ℓ F s n) (hw : (levelUnitStalkMap f F s n).hom w = 0) : w = 0 := by
  have h0 : (levelAdjunctPadicStalkMap f s F _
      (𝟙 (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F)) n).hom w = 0 := by
    have hw' : (levelAdjunctStalkMap f s F _ (𝟙 _) n).hom w = 0 := by
      rwa [levelAdjunctStalkMap_id]
    show ((preservesColimitIso (ModuleCat.restrictScalars.{u + 1}
        (PadicInt.toZModPow (p := ℓ) (n + 1)))
      ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
        ((LAdicSheaf.levelPushforward f n).obj
          ((AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F).level n)).obj)).hom ≫
      (directImageStalkBridge f s ℓ).hom.app (LAdicSheaf.padicLevel B X ℓ
        (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F) n)).hom
      ((levelAdjunctStalkMap f s F _ (𝟙 _) n).hom w) = 0
    rw [hw']
    exact map_zero _
  rw [levelAdjunctPadicStalkMap_id_apply] at h0
  have h1 := ((Scheme.pointSmallEtale s.hom).sheafFiber.mapIso
    ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).mapIso
      (padicLevelInverseImageIso B f ℓ n (F.level n)))).toLinearEquiv.injective
    (h0.trans (map_zero _).symm)
  exact (padicLevelStalkFiberIso s F n).toLinearEquiv.injective
    ((hinj (h1.trans (map_zero _).symm)).trans (map_zero _).symm)

end Level

end Stacks.EtaleCohomology
