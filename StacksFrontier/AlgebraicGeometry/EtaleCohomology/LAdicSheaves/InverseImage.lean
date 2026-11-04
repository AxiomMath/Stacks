module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheaves

/-!
# Inverse image of ℓ-adic sheaves

Let `f : X ⟶ Y` be a morphism of Noetherian schemes. The inverse image of an ℓ-adic sheaf
`F = (Fₙ)` on `Y` is the system `f⁻¹F = (f⁻¹Fₙ)` of constructible sheaves, whose transition maps
are the adjoints of `F_{n+1} → Fₙ → f_* f⁻¹ Fₙ`; its scalar reductions are again isomorphisms.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage`: the ℓ-adic sheaf `f⁻¹F`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap`: the inverse image of a morphism.

## Main results

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.isIso_inverseImage_scalarReductionMap`: the reduction
  maps of `f⁻¹F` are isomorphisms.

## References

* [SGA 5, V 3.1.4]
* [SGA 4½, Rapport, 2.6]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

namespace LAdicSheaf

/-- The pullback `f⁻¹` at level `n`. -/
public abbrev levelPullback (n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B Y ℓ n ⥤ FiniteLevelSheaf.{u, u + 1} B X ℓ n :=
  (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- The pushforward `f_*` at level `n`. -/
public abbrev levelPushforward (n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B X ℓ n ⥤ FiniteLevelSheaf.{u, u + 1} B Y ℓ n :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- The adjunction `f⁻¹ ⊣ f_*` at level `n`. -/
public abbrev levelAdjunction (n : ℕ) : levelPullback (ℓ := ℓ) f n ⊣ levelPushforward f n :=
  (smallEtaleBaseChange B f).sheafAdjunctionContinuous (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- The adjunction between scalar reduction and restriction of scalars at level `n`. -/
public abbrev reductionAdjunction (Z : B.Scheme) (n : ℕ) :
    (Sheaf.composeAndSheafify (SmallEtale.topology B Z.obj Z.property)
      (ModuleCat.extendScalars.{0, 0, u + 1} (finiteLevelRingHom ℓ n))) ⊣
    sheafCompose (SmallEtale.topology B Z.obj Z.property)
      (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n)) :=
  Sheaf.adjunction (SmallEtale.topology B Z.obj Z.property)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))

/-- Restriction of scalars from level `n` to level `n + 1` on `Z`. -/
public abbrev levelRestrict (Z : B.Scheme) (n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B Z ℓ n ⥤ FiniteLevelSheaf.{u, u + 1} B Z ℓ (n + 1) :=
  sheafCompose (SmallEtale.topology B Z.obj Z.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))

/-- The pushforward commutes with restriction of scalars (on the nose). -/
public def levelPushforwardRestrictIso (n : ℕ) :
    levelRestrict X n ⋙ levelPushforward f (n + 1) ≅
      levelPushforward (ℓ := ℓ) f n ⋙ levelRestrict Y n :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

variable [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- The transition maps of `f⁻¹F`: the adjoints of `F_{n+1} → Fₙ → f_* f⁻¹ Fₙ`. -/
public def inverseImageTransition (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n : ℕ) :
    (levelPullback f (n + 1)).obj (F.level (n + 1)) ⟶
      (levelRestrict X n).obj ((levelPullback f n).obj (F.level n)) :=
  ((levelAdjunction f (n + 1)).homEquiv _ _).symm
    (F.transition n ≫ (levelRestrict Y n).map ((levelAdjunction f n).unit.app (F.level n)) ≫
      (levelPushforwardRestrictIso f n).inv.app _)

omit [IsNoetherian X.obj] in
/-- The reduction maps of `f⁻¹F` are isomorphisms. -/
public theorem isIso_inverseImage_scalarReductionMap (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n : ℕ) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B X ℓ n _ _ (inverseImageTransition f F n)) := by
  have := F.reduction_isIso n
  refine isIso_of_coyoneda_map_bijective _ fun T => ?_
  have key : (fun x : (levelPullback f n).obj (F.level n) ⟶ T =>
      FiniteLevelSheaf.scalarReductionMap B X ℓ n _ _ (inverseImageTransition f F n) ≫ x) =
      ((reductionAdjunction X n).homEquiv _ _).symm ∘
        ((levelAdjunction f (n + 1)).homEquiv _ _).symm ∘
        (fun z => z ≫ (levelPushforwardRestrictIso f n).inv.app T) ∘
        ((reductionAdjunction Y n).homEquiv _ _) ∘
        (fun y => FiniteLevelSheaf.scalarReductionMap B Y ℓ n _ _ (F.transition n) ≫ y) ∘
        ((levelAdjunction f n).homEquiv _ _) := by
    funext x
    simp only [Function.comp_apply]
    rw [FiniteLevelSheaf.scalarReductionMap, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    rw [inverseImageTransition, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    rw [Adjunction.homEquiv_naturality_right, FiniteLevelSheaf.scalarReductionMap_comp,
      Adjunction.homEquiv_unit]
    have h := (levelPushforwardRestrictIso f n).inv.naturality x
    simp only [Functor.comp_map] at h
    simp only [Category.assoc, Functor.map_comp, h]
  rw [key]
  have hc := (isIso_iff_yoneda_map_bijective
    ((levelPushforwardRestrictIso f n).inv.app T)).1 inferInstance (F.level (n + 1))
  exact ((reductionAdjunction X n).homEquiv _ _).symm.bijective.comp
    (((levelAdjunction f (n + 1)).homEquiv _ _).symm.bijective.comp
      (hc.comp (((reductionAdjunction Y n).homEquiv _ _).bijective.comp
        ((isIso_iff_coyoneda_map_bijective _).1 inferInstance _ |>.comp
          ((levelAdjunction f n).homEquiv _ _).bijective))))

/-- **The inverse image `f⁻¹F` of an ℓ-adic sheaf.** -/
public def inverseImage (F : LAdicSheaf.{u, u + 1} B Y ℓ) : LAdicSheaf.{u, u + 1} B X ℓ where
  level n := (levelPullback f n).obj (F.level n)
  constructible n := isConstructibleModuleSheaf_pullback B (ZMod (ℓ ^ (n + 1))) f _
    (F.constructible n)
  transition := inverseImageTransition f F
  reduction_isIso := isIso_inverseImage_scalarReductionMap f F

/-- The level `n` of `f⁻¹F` is `f⁻¹Fₙ`. -/
public theorem inverseImage_level (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n : ℕ) :
    (inverseImage f F).level n = (levelPullback f n).obj (F.level n) :=
  rfl

/-- **The inverse image of a morphism of ℓ-adic sheaves.** -/
public def inverseImageMap {F G : LAdicSheaf.{u, u + 1} B Y ℓ} (φ : F ⟶ G) :
    inverseImage f F ⟶ inverseImage f G where
  app n := (levelPullback f n).map (φ.app n)
  naturality n := by
    change (levelPullback f (n + 1)).map (φ.app (n + 1)) ≫ inverseImageTransition f G n =
      inverseImageTransition f F n ≫ (levelRestrict X n).map ((levelPullback f n).map (φ.app n))
    rw [inverseImageTransition, inverseImageTransition,
      ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    have h := (levelPushforwardRestrictIso f n).inv.naturality ((levelPullback f n).map (φ.app n))
    simp only [Functor.comp_map] at h
    have hu := (levelAdjunction f n).unit.naturality (φ.app n)
    simp only [Functor.id_map, Functor.comp_map] at hu
    have hφ : φ.app (n + 1) ≫ G.transition n = F.transition n ≫ (levelRestrict Y n).map (φ.app n) :=
      φ.naturality n
    rw [← Category.assoc, hφ]
    simp only [Category.assoc, ← h, ← Functor.map_comp_assoc, hu]

/-- `f⁻¹` is a functor on ℓ-adic sheaves. -/
public def inverseImageFunctor : LAdicSheaf.{u, u + 1} B Y ℓ ⥤ LAdicSheaf.{u, u + 1} B X ℓ where
  obj := inverseImage f
  map := inverseImageMap f
  map_id _ := LAdicSheaf.Hom.ext (h := fun n => (levelPullback f n).map_id _)
  map_comp _ _ := LAdicSheaf.Hom.ext (h := fun n => (levelPullback f n).map_comp _ _)

end LAdicSheaf

end AlgebraicGeometry.SmallEtale
