module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Stalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm

/-!
# Stalks of the inverse image of an ℓ-adic sheaf

For `f : X ⟶ Y` and a geometric point `x̄` of `X`, the stalk of `f⁻¹F` at `x̄` is the stalk of `F`
at `f(x̄)`: at each finite level this is Tag 03Q1
(`AlgebraicGeometry.etaleStalkSmallEtalePullObjIso`), and these isomorphisms commute with the
transition maps, because on germs both are computed by the unit `F_{n+1} → f_* f⁻¹ F_{n+1}`, which
the transitions of `f⁻¹F` are adjoint to.

## Main definitions

* `Stacks.EtaleCohomology.inverseImageFiniteLevelStalkIso`: at level `n`.
* `Stacks.EtaleCohomology.inverseImageStalkEquiv`: the ℓ-adic stalks, as `ℤ_ℓ`-modules.

## Main results

* `Stacks.EtaleCohomology.inverseImageFiniteLevelStalkIso_inv_transition`: compatibility with the
  transition maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Opposite

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
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
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- A germ followed by the transition map of stalks is the transition map of sections followed by
the germ. -/
@[reassoc]
public theorem germ_finiteLevelStalkTransition {Z : B.Scheme} [IsNoetherian Z.obj]
    (F : LAdicSheaf B Z ℓ) (s : GeometricPoint Z.obj) (n : ℕ)
    (V : (geometricPointFiber B Z.obj Z.property s).Elements) :
    colimit.ι ((Functor.Elements.π (geometricPointFiber B Z.obj Z.property s)).op ⋙
        (F.level (n + 1)).obj) (op V) ≫ finiteLevelStalkTransition B Z ℓ F s n =
      (F.transition n).hom.app (op V.1) ≫ (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
        (colimit.ι ((Functor.Elements.π (geometricPointFiber B Z.obj Z.property s)).op ⋙
          (F.level n).obj) (op V)) := by
  have h1 := ι_colimMap_assoc ((Functor.Elements.π (geometricPointFiber B Z.obj Z.property
    s)).op.whiskerLeft (F.transition n).hom) (op V)
    (preservesColimitIso (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
      ((Functor.Elements.π (geometricPointFiber B Z.obj Z.property s)).op ⋙ (F.level n).obj)).inv
  have h2 := ι_preservesColimitIso_inv (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
    ((Functor.Elements.π (geometricPointFiber B Z.obj Z.property s)).op ⋙ (F.level n).obj) (op V)
  exact h1.trans (congrArg (fun g => (F.transition n).hom.app (op V.1) ≫ g) h2)

/-- **The finite-level stalks of `f⁻¹F` at `x̄` are those of `F` at `f(x̄)`** (Tag 03Q1). -/
public def inverseImageFiniteLevelStalkIso (F : LAdicSheaf B Y ℓ) (x : GeometricPoint X.obj)
    (n : ℕ) :
    finiteLevelStalk B X ℓ (LAdicSheaf.inverseImage f F) x n ≅
      finiteLevelStalk B Y ℓ F (x.map (B.inclusion.map f)) n :=
  let : HasProducts.{u} (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
    fun _ => ModuleCat.hasLimitsOfShape
  etaleStalkSmallEtalePullObjIso B f x _ (F.level n)

/-- On germs, the inverse of the stalk comparison is the unit of `f⁻¹ ⊣ f_*`. -/
@[reassoc]
public theorem germ_inverseImageFiniteLevelStalkIso_inv (F : LAdicSheaf B Y ℓ)
    (x : GeometricPoint X.obj) (n : ℕ)
    (V : (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map f))).Elements) :
    colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.obj Y.property
        (x.map (B.inclusion.map f)))).op ⋙ (F.level n).obj) (op V) ≫
        (inverseImageFiniteLevelStalkIso B f F x n).inv =
      ((LAdicSheaf.levelAdjunction f n).unit.app (F.level n)).hom.app (op V.1) ≫
        colimit.ι ((Functor.Elements.π (geometricPointFiber B X.obj X.property x)).op ⋙
          ((LAdicSheaf.levelPullback f n).obj (F.level n)).obj)
          (op (Functor.elementsMk _ ((smallEtaleBaseChange B f).obj V.1)
            (geometricPointFiberBaseChangeEquiv B f x V.1 V.2))) := by
  let : HasProducts.{u} (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
    fun _ => ModuleCat.hasLimitsOfShape
  refine (Iso.comp_inv_eq _).2 ?_
  have h := etaleStalkSmallEtalePullObjIso_germ B f x _ (F.level n)
    (Functor.elementsMk _ ((smallEtaleBaseChange B f).obj V.1)
      (geometricPointFiberBaseChangeEquiv B f x V.1 V.2)) V
    (𝟙 _) (geometricPointFiberBaseChangeEquiv_ha B f x V.1 V.2)
  rw [AlgebraicGeometry.pullbackSectionAlongHom_id] at h
  exact h.symm.trans (Category.assoc _ _ _).symm

omit [AlgebraicGeometry.IsNoetherian X.obj] in
/-- The unit followed by the pushforward of the transition of `f⁻¹F` is the transition of `F`
followed by the unit. -/
public theorem unit_comp_inverseImageTransition (F : LAdicSheaf B Y ℓ) (n : ℕ) :
    (LAdicSheaf.levelAdjunction f (n + 1)).unit.app (F.level (n + 1)) ≫
        (LAdicSheaf.levelPushforward f (n + 1)).map (LAdicSheaf.inverseImageTransition f F n) =
      F.transition n ≫ (LAdicSheaf.levelRestrict Y n).map
        ((LAdicSheaf.levelAdjunction f n).unit.app (F.level n)) ≫
        (LAdicSheaf.levelPushforwardRestrictIso f n).inv.app _ := by
  refine ((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv_unit _ _ _).symm.trans ?_
  rw [LAdicSheaf.inverseImageTransition]
  exact Equiv.apply_symm_apply _ _

/-- **The stalk comparisons commute with the transition maps.** -/
public theorem inverseImageFiniteLevelStalkIso_inv_transition (F : LAdicSheaf B Y ℓ)
    (x : GeometricPoint X.obj) (n : ℕ) :
    (inverseImageFiniteLevelStalkIso B f F x (n + 1)).inv ≫
        finiteLevelStalkTransition B X ℓ (LAdicSheaf.inverseImage f F) x n =
      finiteLevelStalkTransition B Y ℓ F (x.map (B.inclusion.map f)) n ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (inverseImageFiniteLevelStalkIso B f F x n).inv := by
  refine colimit.hom_ext fun V => ?_
  set U : (geometricPointFiber B X.obj X.property x).Elements :=
    Functor.elementsMk _ ((smallEtaleBaseChange B f).obj V.unop.1)
      (geometricPointFiberBaseChangeEquiv B f x V.unop.1 V.unop.2)
  have e1 := germ_inverseImageFiniteLevelStalkIso_inv B f F x (n + 1) V.unop
  have e2 := germ_finiteLevelStalkTransition B (LAdicSheaf.inverseImage f F) x n U
  have e3 := germ_finiteLevelStalkTransition B F (x.map (B.inclusion.map f)) n V.unop
  have e4 := germ_inverseImageFiniteLevelStalkIso_inv B f F x n V.unop
  have key : ((LAdicSheaf.levelAdjunction f (n + 1)).unit.app (F.level (n + 1))).hom.app
        (op V.unop.1) ≫ (LAdicSheaf.inverseImageTransition f F n).hom.app (op U.1) =
      (F.transition n).hom.app (op V.unop.1) ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (((LAdicSheaf.levelAdjunction f n).unit.app (F.level n)).hom.app (op V.unop.1)) :=
    (congrArg (fun φ => φ.hom.app (op V.unop.1)) (unit_comp_inverseImageTransition B f F n) :)
  erw [← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, key, Category.assoc,
    ← Category.assoc (colimit.ι _ _), e3, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, e4]
  rfl

/-- The stalk comparison at level `n` as a map of `ℤ_ℓ`-modules. -/
public def inverseImageFiniteLevelStalkLinearEquiv (F : LAdicSheaf B Y ℓ) (x : GeometricPoint X.obj)
    (n : ℕ) :
    finiteLevelStalk B X ℓ (LAdicSheaf.inverseImage f F) x n ≃ₗ[ℤ_[ℓ]]
      finiteLevelStalk B Y ℓ F (x.map (B.inclusion.map f)) n where
  toFun := (inverseImageFiniteLevelStalkIso B f F x n).hom
  invFun := (inverseImageFiniteLevelStalkIso B f F x n).inv
  left_inv v := Iso.hom_inv_id_apply _ v
  right_inv v := Iso.inv_hom_id_apply _ v
  map_add' := map_add _
  map_smul' c v := map_smul (inverseImageFiniteLevelStalkIso B f F x n).hom.hom
    (PadicInt.toZModPow (n + 1) c) v

/-- **The ℓ-adic stalk of `f⁻¹F` at `x̄` is the stalk of `F` at `f(x̄)`.** -/
public def inverseImageStalkEquiv (F : LAdicSheaf B Y ℓ) (x : GeometricPoint X.obj) :
    LAdicSheaf.stalk B X ℓ (LAdicSheaf.inverseImage f F) x ≃ₗ[ℤ_[ℓ]]
      LAdicSheaf.stalk B Y ℓ F (x.map (B.inclusion.map f)) := by
  refine
    { toFun := fun a => ⟨fun n => (inverseImageFiniteLevelStalkIso B f F x n).hom (a.1 n),
        fun n => ?_⟩
      invFun := fun a => ⟨fun n => (inverseImageFiniteLevelStalkIso B f F x n).inv (a.1 n),
        fun n => ?_⟩
      left_inv := fun a => Subtype.ext (funext fun n => Iso.hom_inv_id_apply _ _)
      right_inv := fun a => Subtype.ext (funext fun n => Iso.inv_hom_id_apply _ _)
      map_add' := fun a b => Subtype.ext (funext fun n => map_add _ _ _)
      map_smul' := fun c a => Subtype.ext (funext fun n =>
        (inverseImageFiniteLevelStalkLinearEquiv B f F x n).map_smul c (a.1 n)) }
  · have h := ConcreteCategory.congr_hom
      (inverseImageFiniteLevelStalkIso_inv_transition B f F x n)
      ((inverseImageFiniteLevelStalkIso B f F x (n + 1)).hom (a.1 (n + 1)))
    simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at h
    exact (Iso.inv_hom_id_apply (inverseImageFiniteLevelStalkIso B f F x n) _).symm.trans
      (congrArg (inverseImageFiniteLevelStalkIso B f F x n).hom (h.symm.trans (a.2 n)))
  · have h := ConcreteCategory.congr_hom
      (inverseImageFiniteLevelStalkIso_inv_transition B f F x n) (a.1 (n + 1))
    simp only [ConcreteCategory.comp_apply] at h
    change (finiteLevelStalkTransition B X ℓ _ x n).hom _ = _
    rw [h]
    exact congrArg _ (a.2 n)

end Stacks.EtaleCohomology
