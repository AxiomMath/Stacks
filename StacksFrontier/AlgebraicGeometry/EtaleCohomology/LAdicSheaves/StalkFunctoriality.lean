module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk

/-!
# Functoriality of the stalks of ℓ-adic sheaves

A morphism `φ = {φₙ}` of ℓ-adic sheaves induces a map of level-`n` stalks at every geometric point,
the colimit over étale neighbourhoods of the whiskered `φₙ`.  These maps commute with the
transitions between consecutive finite-level stalks, so they assemble into a `ℤ_ℓ`-linear map of
ℓ-adic stalks `F_x̄ = lim_n F_{n, x̄}`, and after extending scalars into a `ℚ_ℓ`-linear map of
rational stalks.  The construction is functorial and additive, and it commutes with the action of
every endomorphism of the geometric point, in particular with the geometric Frobenius.

## Main definitions

* `Stacks.EtaleCohomology.finiteLevelStalkMap`: the map of level-`n` stalks.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkMap`: the `ℤ_ℓ`-linear map of ℓ-adic stalks.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalStalkMap`: the `ℚ_ℓ`-linear map of rational stalks.

## Main results

* `Stacks.EtaleCohomology.finiteLevelStalkMap_transition`: compatibility with the transitions.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkMap_id`, `.stalkMap_comp`, `.stalkMap_add`,
  `.stalkMap_zero`: functoriality and additivity.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkEnd_comp_stalkMap`: the maps commute with the action
  of endomorphisms of the geometric point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

section Colimits

variable {J : Type*} [Category J] {C : Type*} [Category C] {D : Type*} [Category D]
  [HasColimitsOfShape J C] [HasColimitsOfShape J D]

/-- A square of natural transformations into the composite with a functor `R` preserving the
relevant colimits induces a commutative square of colimits, read through the comparison
isomorphisms for `R`. -/
lemma colim_map_comp_preservesColimitIso_inv (R : C ⥤ D) {A A' : J ⥤ D} {G G' : J ⥤ C}
    (α : A ⟶ A') (β : A ⟶ G ⋙ R) (β' : A' ⟶ G' ⋙ R) (γ : G ⟶ G')
    [PreservesColimit G R] [PreservesColimit G' R]
    (h : α ≫ β' = β ≫ Functor.whiskerRight γ R) :
    colim.map α ≫ colim.map β' ≫ (preservesColimitIso R G').inv =
      (colim.map β ≫ (preservesColimitIso R G).inv) ≫ R.map (colim.map γ) := by
  apply colimit.hom_ext
  intro j
  have hj := congrArg (fun t => t.app j) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hj
  simp only [colimit.ι_map_assoc, ι_preservesColimitIso_inv, Category.assoc,
    ι_preservesColimitIso_inv_assoc, ← Functor.map_comp, colimit.ι_map, Functor.comp_obj]
  rw [← Category.assoc, hj, Category.assoc, Functor.map_comp]

/-- `colim.map` is additive: `colim.map (α + β) = colim.map α + colim.map β`. -/
lemma colim_map_add [Preadditive D] {A A' : J ⥤ D} (α β : A ⟶ A') :
    colim.map (α + β) = colim.map α + colim.map β := by
  refine colimit.hom_ext fun j => ?_
  simp only [colimit.ι_map, Preadditive.comp_add, NatTrans.app_add, Preadditive.add_comp]

/-- `colim.map` sends the zero natural transformation to zero. -/
lemma colim_map_zero [Preadditive D] (A A' : J ⥤ D) :
    colim.map (0 : A ⟶ A') = 0 := by
  refine colimit.hom_ext fun j => ?_
  simp only [colimit.ι_map, NatTrans.app_zero, Limits.zero_comp, Limits.comp_zero]

end Colimits

variable {B X ℓ}

/-! ### Finite levels -/

/-- The map of level-`n` stalks at `x̄` induced by a morphism of ℓ-adic sheaves: the colimit over
the étale neighbourhoods of `x̄` of its level-`n` component. -/
public def finiteLevelStalkMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (s : GeometricPoint X.1)
    (n : ℕ) : finiteLevelStalk B X ℓ F s n ⟶ finiteLevelStalk B X ℓ G s n :=
  colim.map (Functor.whiskerLeft
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op) (φ.app n).hom)

/-- The map of level-`n` stalks induced by `φ`, composed with the colimit inclusion at an étale
neighbourhood `j` of `x̄`, is the component of `φₙ` at `j` followed by the inclusion at `j`. -/
@[reassoc (attr := simp)]
public theorem ι_finiteLevelStalkMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (s : GeometricPoint X.1) (n : ℕ) (j : (geometricPointFiber B X.1 X.property s).Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
        (F.level n).obj) j ≫ finiteLevelStalkMap φ s n =
      (φ.app n).hom.app _ ≫ colimit.ι ((CategoryOfElements.π
        (geometricPointFiber B X.1 X.property s)).op ⋙ (G.level n).obj) j :=
  colimit.ι_map _ j

/-- The maps of finite-level stalks commute with the transitions. -/
@[reassoc]
public theorem finiteLevelStalkMap_transition {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (s : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalkMap φ s (n + 1) ≫ finiteLevelStalkTransition B X ℓ G s n =
      finiteLevelStalkTransition B X ℓ F s n ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (finiteLevelStalkMap φ s n) := by
  have hφ : Functor.whiskerLeft
      ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op) (φ.app (n + 1)).hom ≫
      Functor.whiskerLeft ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op)
        (G.transition n).hom =
      Functor.whiskerLeft ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op)
        (F.transition n).hom ≫
      Functor.whiskerRight (Functor.whiskerLeft
        ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op) (φ.app n).hom)
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)) := by
    ext j : 2
    exact congrArg (fun t => t.hom.app
      (((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op).obj j))
      (φ.naturality n)
  exact colim_map_comp_preservesColimitIso_inv _ _ _ _ _ hφ

/-- The maps of finite-level stalks commute with the action of an endomorphism of the geometric
point. -/
@[reassoc]
public theorem finiteLevelStalkMap_finiteLevelStalkEnd {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) (n : ℕ) :
    finiteLevelStalkMap φ s n ≫ finiteLevelStalkEnd B X ℓ G a n =
      finiteLevelStalkEnd B X ℓ F a n ≫ finiteLevelStalkMap φ s n :=
  (geometricPointStalkMap B X.1 X.property a
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).naturality (φ.app n).hom

/-- The map of level-`n` stalks induced by the identity is the identity. -/
@[simp]
public theorem finiteLevelStalkMap_id (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalkMap (𝟙 F) s n = 𝟙 _ :=
  colim.map_id _

/-- The map of level-`n` stalks induced by a composite is the composite of the induced maps. -/
public theorem finiteLevelStalkMap_comp {F G H : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ H)
    (s : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalkMap (φ ≫ ψ) s n = finiteLevelStalkMap φ s n ≫ finiteLevelStalkMap ψ s n := by
  unfold finiteLevelStalkMap
  exact colim.map_comp (Functor.whiskerLeft _ (φ.app n).hom) (Functor.whiskerLeft _ (ψ.app n).hom)

/-- The map of level-`n` stalks induced by a sum of morphisms is the sum of the induced maps. -/
public theorem finiteLevelStalkMap_add {F G : LAdicSheaf B X ℓ} (φ ψ : F ⟶ G)
    (s : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalkMap (φ + ψ) s n = finiteLevelStalkMap φ s n + finiteLevelStalkMap ψ s n := by
  unfold finiteLevelStalkMap
  exact colim_map_add (Functor.whiskerLeft _ (φ.app n).hom) (Functor.whiskerLeft _ (ψ.app n).hom)

/-- The map of level-`n` stalks induced by the zero morphism is zero. -/
public theorem finiteLevelStalkMap_zero (F G : LAdicSheaf B X ℓ) (s : GeometricPoint X.1)
    (n : ℕ) : finiteLevelStalkMap (0 : F ⟶ G) s n = 0 := by
  unfold finiteLevelStalkMap
  exact colim_map_zero _ _

/-! ### The ℓ-adic stalk -/

/-- **The map of ℓ-adic stalks** induced by a morphism of ℓ-adic sheaves: a compatible family of
finite-level germs goes to the family of its images. -/
public def LAdicSheaf.stalkMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (s : GeometricPoint X.1) :
    LAdicSheaf.stalk B X ℓ F s →ₗ[PadicInt ℓ] LAdicSheaf.stalk B X ℓ G s where
  toFun v :=
    ⟨fun n => (finiteLevelStalkMap φ s n).hom (v.1 n), fun n => by
      have h := congrArg (fun g => g.hom (v.1 (n + 1))) (finiteLevelStalkMap_transition φ s n)
      change LAdicSheaf.stalkTransition B X ℓ G s n _ =
        (finiteLevelStalkMap φ s n).hom (LAdicSheaf.stalkTransition B X ℓ F s n (v.1 (n + 1)))
        at h
      exact h.trans (congrArg (finiteLevelStalkMap φ s n).hom (v.2 n))⟩
  map_add' v w := Subtype.ext <| funext fun n ↦
    map_add (finiteLevelStalkMap φ s n).hom (v.1 n) (w.1 n)
  map_smul' c v := Subtype.ext <| funext fun n ↦
    map_smul (finiteLevelStalkMap φ s n).hom (PadicInt.toZModPow (n + 1) c) (v.1 n)

/-- The map of ℓ-adic stalks is the finite-level map at every level. -/
public theorem LAdicSheaf.stalkProjection_stalkMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (s : GeometricPoint X.1) (n : ℕ) (v : LAdicSheaf.stalk B X ℓ F s) :
    LAdicSheaf.stalkProjection B X ℓ G s n (LAdicSheaf.stalkMap φ s v) =
      (finiteLevelStalkMap φ s n).hom (LAdicSheaf.stalkProjection B X ℓ F s n v) :=
  rfl

/-- The map of ℓ-adic stalks induced by the identity is the identity. -/
@[simp]
public theorem LAdicSheaf.stalkMap_id (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) :
    LAdicSheaf.stalkMap (𝟙 F) s = LinearMap.id := by
  ext v n
  exact congrArg (fun g => g.hom (v.1 n)) (finiteLevelStalkMap_id F s n)

/-- The map of ℓ-adic stalks induced by a composite is the composite of the induced maps. -/
public theorem LAdicSheaf.stalkMap_comp {F G H : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ H)
    (s : GeometricPoint X.1) :
    LAdicSheaf.stalkMap (φ ≫ ψ) s = LAdicSheaf.stalkMap ψ s ∘ₗ LAdicSheaf.stalkMap φ s := by
  ext v n
  exact congrArg (fun g => g.hom (v.1 n)) (finiteLevelStalkMap_comp φ ψ s n)

/-- The map of ℓ-adic stalks induced by a sum of morphisms is the sum of the induced maps. -/
public theorem LAdicSheaf.stalkMap_add {F G : LAdicSheaf B X ℓ} (φ ψ : F ⟶ G)
    (s : GeometricPoint X.1) :
    LAdicSheaf.stalkMap (φ + ψ) s = LAdicSheaf.stalkMap φ s + LAdicSheaf.stalkMap ψ s := by
  ext v n
  exact congrArg (fun g => g.hom (v.1 n)) (finiteLevelStalkMap_add φ ψ s n)

/-- The map of ℓ-adic stalks induced by the zero morphism is zero. -/
@[simp]
public theorem LAdicSheaf.stalkMap_zero (F G : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) :
    LAdicSheaf.stalkMap (0 : F ⟶ G) s = 0 := by
  ext v n
  exact congrArg (fun g => g.hom (v.1 n)) (finiteLevelStalkMap_zero F G s n)

/-- **The maps of ℓ-adic stalks commute with the action of endomorphisms of the geometric
point**, in particular with the geometric Frobenius. -/
public theorem LAdicSheaf.stalkEnd_comp_stalkMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    LAdicSheaf.stalkEnd B X ℓ G a ∘ₗ LAdicSheaf.stalkMap φ s =
      LAdicSheaf.stalkMap φ s ∘ₗ LAdicSheaf.stalkEnd B X ℓ F a := by
  ext v n
  exact congrArg (fun g => g.hom (v.1 n)) (finiteLevelStalkMap_finiteLevelStalkEnd φ a n)

/-- The ring homomorphism `End F → End_{ℤ_ℓ}(F_x̄)` by which endomorphisms of an ℓ-adic sheaf act
on its stalk. -/
public def LAdicSheaf.stalkEndRingHom (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) :
    End F →+* Module.End (PadicInt ℓ) (LAdicSheaf.stalk B X ℓ F s) where
  toFun φ := LAdicSheaf.stalkMap φ.asHom s
  map_one' := LAdicSheaf.stalkMap_id F s
  map_mul' φ ψ := LAdicSheaf.stalkMap_comp ψ.asHom φ.asHom s
  map_zero' := LAdicSheaf.stalkMap_zero F F s
  map_add' φ ψ := LAdicSheaf.stalkMap_add φ.asHom ψ.asHom s

/-! ### The rational stalk -/

/-- The map of rational stalks `ℚ_ℓ ⊗ F_x̄ → ℚ_ℓ ⊗ G_x̄` induced by a morphism of ℓ-adic
sheaves. -/
public def LAdicSheaf.rationalStalkMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkLeft B X ℓ F s →ₗ[Padic ℓ] LAdicSheaf.rationalStalkLeft B X ℓ G s :=
  LinearMap.baseChange (Padic ℓ) (LAdicSheaf.stalkMap φ s)

/-- The maps of rational stalks commute with the action of endomorphisms of the geometric
point. -/
public theorem LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap {F G : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    LAdicSheaf.rationalStalkEnd B X ℓ G a ∘ₗ LAdicSheaf.rationalStalkMap φ s =
      LAdicSheaf.rationalStalkMap φ s ∘ₗ LAdicSheaf.rationalStalkEnd B X ℓ F a := by
  simp only [LAdicSheaf.rationalStalkEnd, LAdicSheaf.rationalStalkMap,
    ← LinearMap.baseChange_comp, LAdicSheaf.stalkEnd_comp_stalkMap]

/-- The ring homomorphism `End F → End_{ℚ_ℓ}(ℚ_ℓ ⊗ F_x̄)`. -/
public def LAdicSheaf.rationalStalkEndRingHom (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) :
    End F →+* Module.End (Padic ℓ) (LAdicSheaf.rationalStalkLeft B X ℓ F s) where
  toFun φ := LAdicSheaf.rationalStalkMap φ.asHom s
  map_one' := by
    change LinearMap.baseChange _ (LAdicSheaf.stalkMap (𝟙 F) s) = _
    rw [LAdicSheaf.stalkMap_id, LinearMap.baseChange_id]
    rfl
  map_mul' φ ψ := by
    change LinearMap.baseChange _ (LAdicSheaf.stalkMap (ψ.asHom ≫ φ.asHom) s) = _
    rw [LAdicSheaf.stalkMap_comp, LinearMap.baseChange_comp]
    rfl
  map_zero' := by
    change LinearMap.baseChange _ (LAdicSheaf.stalkMap (0 : F ⟶ F) s) = _
    rw [LAdicSheaf.stalkMap_zero, LinearMap.baseChange_zero]
  map_add' φ ψ := by
    change LinearMap.baseChange _ (LAdicSheaf.stalkMap (φ.asHom + ψ.asHom) s) = _
    rw [LAdicSheaf.stalkMap_add, LinearMap.baseChange_add]
    rfl

end Stacks.EtaleCohomology

end
