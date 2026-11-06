module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Additive

/-!
# Functoriality of `Hⁱ_c(X_k̄, F)` in the ℓ-adic sheaf

A morphism `φ = {φₙ}` of ℓ-adic sheaves induces maps `Hⁱ_c(X_k̄, Fₙ) → Hⁱ_c(X_k̄, Gₙ)` compatible
with the inverse systems, hence a map of limits `Hⁱ_c(X_k̄, F) → Hⁱ_c(X_k̄, G)`.  The construction
is functorial and additive, and it commutes with every natural endomorphism of `RΓ_c(X_k̄, -)`, in
particular with the canonical geometric Frobenius `π_X^*`.  So a ring acting on an ℓ-adic sheaf by
endomorphisms acts on its compactly supported cohomology, and `π_X^*` is linear for that action.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.padicLevelMap`: a morphism at level `n`, as a map of sheaves
  of `ℤ_[ℓ]`-modules.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologyMap`: the induced map
  `Hⁱ_c(X_k̄, F) → Hⁱ_c(X_k̄, G)`.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologyEndRingHom`: the ring
  homomorphism `End F → End_{ℤ_ℓ}(Hⁱ_c(X_k̄, F))`.

## Main results

* `Stacks.EtaleCohomology.additive_compactSupportFrobeniusFunctor`: `RΓ_c(X_k̄, -)` is additive.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius`: the
  induced maps commute with `π_X^*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

section Additivity

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- The functor induced on bounded below cochain complexes by an additive functor is additive. -/
public instance additive_mapCochainComplexPlus (F : C ⥤ D) [F.Additive] :
    F.mapCochainComplexPlus.Additive := by
  have : (F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D).Additive :=
    Functor.additive_of_iso (F.mapCochainComplexPlusCompι).symm
  exact Functor.additive_of_comp_faithful _ (CochainComplex.Plus.ι D)

end Additivity

section AdditivityQ

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The localization functor to the bounded below derived category is additive. -/
public instance additive_derivedCategoryPlusQ : (DerivedCategory.Plus.Q (C := C)).Additive := by
  have : (DerivedCategory.Plus.Q (C := C) ⋙ DerivedCategory.Plus.ι).Additive :=
    Functor.additive_of_iso (Iso.refl (CochainComplex.Plus.ι C ⋙ DerivedCategory.Q))
  exact Functor.additive_of_comp_faithful _ DerivedCategory.Plus.ι

end AdditivityQ

section CompactSupport

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`RΓ_c(X_k̄, -)` is additive.** -/
public instance additive_compactSupportFrobeniusFunctor :
    (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).Additive := by
  dsimp only [compactSupportFrobeniusFunctor]
  infer_instance

/-- Placing a sheaf of modules in degree zero is additive. -/
public theorem additive_liftSingle (X : Scheme.{u})
    (h : ∀ M : EtaleModules.{u, 0} Λ X, CochainComplex.plus _
      ((HomologicalComplex.single (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0).obj M)) :
    (ObjectProperty.lift _ (HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
      (ComplexShape.up ℤ) 0) h).Additive :=
  inferInstance

end CompactSupport

/-- `limMap` is additive. -/
public lemma limMap_add {J C : Type*} [Category* J] [Category* C] [Preadditive C]
    [HasLimitsOfShape J C] {A A' : J ⥤ C} (α β : A ⟶ A') :
    limMap (α + β) = limMap α + limMap β := by
  apply limit.hom_ext
  intro j
  simp only [limMap_π, Preadditive.add_comp, NatTrans.app_add, Preadditive.comp_add]

/-- The functor of an equivalence of preadditive categories is additive. -/
public theorem Equivalence.additive_functor' {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryProducts C] (e : C ≌ D) : e.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### Functoriality of `Hⁱ_c(X_k̄, F)` in the ℓ-adic sheaf -/

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
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

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- `Hⁱ_c(X_k̄, -|_{X_k̄})` with `ℤ_[ℓ]`-coefficients is additive. -/
public instance additive_geometricCompactSupportPadicCohomology (i : ℤ) :
    (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).Additive := by
  have := Equivalence.additive_functor'
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ]))
  have := additive_liftSingle ℤ_[ℓ] X.1 (fun _ => ⟨0, inferInstance⟩)
  have : (padicCoefficientComplex B X ℓ).Additive := by
    dsimp only [padicCoefficientComplex]
    infer_instance
  dsimp only [geometricCompactSupportPadicCohomology]
  infer_instance

variable {B X ℓ}

/-- The level-`n` component of a morphism of ℓ-adic sheaves, read on the levels as sheaves of
`ℤ_[ℓ]`-modules. -/
public def LAdicSheaf.padicLevelMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (n : ℕ) :
    LAdicSheaf.padicLevel B X ℓ F n ⟶ LAdicSheaf.padicLevel B X ℓ G n :=
  (sheafCompose (SmallEtale.topology B X.1 X.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (n + 1)))).map (φ.app n)

/-- On sections, `padicLevelMap φ n` acts as the level-`n` component of `φ`. -/
@[simp]
public theorem LAdicSheaf.padicLevelMap_hom_app_apply {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (n : ℕ) (V : (SmallEtale B X.1 X.property)ᵒᵖ) (x : (F.level n).obj.obj V) :
    ((LAdicSheaf.padicLevelMap φ n).hom.app V).hom x = ((φ.app n).hom.app V).hom x :=
  rfl

/-- The level components commute with the transitions, read as sheaves of `ℤ_[ℓ]`-modules. -/
@[reassoc]
public theorem LAdicSheaf.padicLevelMap_padicTransition {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (n : ℕ) :
    LAdicSheaf.padicLevelMap φ (n + 1) ≫ LAdicSheaf.padicTransition B X ℓ G n =
      LAdicSheaf.padicTransition B X ℓ F n ≫ LAdicSheaf.padicLevelMap φ n := by
  have h := φ.naturality n
  ext V x
  exact ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app V) h)
    (show (F.level (n + 1)).obj.obj V from x)

/-- The map of inverse systems `n ↦ Hⁱ_c(X_k̄, Fₙ) → Hⁱ_c(X_k̄, Gₙ)` induced by a morphism of
ℓ-adic sheaves. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologySystemMap {F G : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ⟶
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar G i :=
  NatTrans.ofOpSequence
    (fun n => (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
      (LAdicSheaf.padicLevelMap φ n))
    (fun n => by
      rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ,
        LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ]
      change (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map _ ≫
          (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map _ =
        (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map _ ≫
          (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        LAdicSheaf.padicLevelMap_padicTransition])

/-- **The map `Hⁱ_c(X_k̄, F) → Hⁱ_c(X_k̄, G)` induced by a morphism of ℓ-adic sheaves**: the limit
of the maps on the finite levels. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologyMap {F G : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i ⟶
      LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar G i :=
  limMap (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i)

/-- The map `Hⁱ_c(X_k̄, F) → Hⁱ_c(X_k̄, G)` commutes with the projections to the finite levels. -/
@[reassoc (attr := simp)]
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_π {F G : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (i : ℤ) (n : ℕ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar G i n =
      LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n ≫
        (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
          (LAdicSheaf.padicLevelMap φ n) :=
  limMap_π _ (Opposite.op n)

/-- `padicLevelMap` sends the identity to the identity. -/
@[simp]
public theorem LAdicSheaf.padicLevelMap_id (F : LAdicSheaf B X ℓ) (n : ℕ) :
    LAdicSheaf.padicLevelMap (𝟙 F) n = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- `padicLevelMap` sends a composite to the composite of the level maps. -/
public theorem LAdicSheaf.padicLevelMap_comp {F G H : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ H)
    (n : ℕ) :
    LAdicSheaf.padicLevelMap (φ ≫ ψ) n = LAdicSheaf.padicLevelMap φ n ≫
      LAdicSheaf.padicLevelMap ψ n :=
  CategoryTheory.Functor.map_comp _ _ _

/-- `padicLevelMap` is additive in the morphism. -/
public theorem LAdicSheaf.padicLevelMap_add {F G : LAdicSheaf B X ℓ} (φ ψ : F ⟶ G) (n : ℕ) :
    LAdicSheaf.padicLevelMap (φ + ψ) n = LAdicSheaf.padicLevelMap φ n +
      LAdicSheaf.padicLevelMap ψ n := by
  ext U : 3
  rfl

/-- Morphisms of inverse systems indexed by `ℕᵒᵖ` are equal if they agree at each `op n`. -/
private theorem natTrans_op_nat_ext {C : Type*} [Category* C] {A A' : ℕᵒᵖ ⥤ C} {α β : A ⟶ A'}
    (h : ∀ n : ℕ, α.app (op n) = β.app (op n)) : α = β := by
  ext n : 2
  induction n using Opposite.rec with | op n => exact h n

/-- The map of inverse systems induced by the identity is the identity. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemMap_id
    (F : LAdicSheaf B X ℓ) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar (𝟙 F) i = 𝟙 _ := by
  refine natTrans_op_nat_ext fun n => ?_
  simp only [LAdicSheaf.geometricCompactlySupportedCohomologySystemMap,
    LAdicSheaf.padicLevelMap_id, CategoryTheory.Functor.map_id, NatTrans.id_app]
  rfl

/-- The map of inverse systems induced by a composite is the composite of the maps. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemMap_comp
    {F G H : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ H) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar (φ ≫ ψ) i =
      LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i := by
  refine natTrans_op_nat_ext fun n => ?_
  simp only [LAdicSheaf.geometricCompactlySupportedCohomologySystemMap,
    LAdicSheaf.padicLevelMap_comp, CategoryTheory.Functor.map_comp, NatTrans.comp_app]
  rfl

/-- The map of inverse systems is additive in the morphism. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemMap_add
    {F G : LAdicSheaf B X ℓ} (φ ψ : F ⟶ G) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar (φ + ψ) i =
      LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i +
        LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i := by
  refine natTrans_op_nat_ext fun n => ?_
  simp only [LAdicSheaf.geometricCompactlySupportedCohomologySystemMap,
    LAdicSheaf.padicLevelMap_add, Functor.map_add, NatTrans.app_add]
  rfl

/-- The map on `Hⁱ_c(X_k̄, -)` induced by the identity is the identity. -/
@[simp]
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_id (F : LAdicSheaf B X ℓ)
    (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (𝟙 F) i = 𝟙 _ := by
  show limMap _ = _
  rw [LAdicSheaf.geometricCompactlySupportedCohomologySystemMap_id]
  exact lim.map_id _

/-- The map on `Hⁱ_c(X_k̄, -)` induced by a composite is the composite of the maps. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp {F G H : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (ψ : G ⟶ H) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (φ ≫ ψ) i =
      LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i := by
  show limMap _ = limMap _ ≫ limMap _
  rw [LAdicSheaf.geometricCompactlySupportedCohomologySystemMap_comp]
  exact lim.map_comp _ _

/-- The map on `Hⁱ_c(X_k̄, -)` is additive in the morphism. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_add {F G : LAdicSheaf B X ℓ}
    (φ ψ : F ⟶ G) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (φ + ψ) i =
      LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i +
        LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i := by
  show limMap _ = limMap _ + limMap _
  rw [LAdicSheaf.geometricCompactlySupportedCohomologySystemMap_add]
  exact limMap_add _ _

/-- The zero morphism induces the zero map on `Hⁱ_c(X_k̄, -)`. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_zero (F G : LAdicSheaf B X ℓ)
    (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (0 : F ⟶ G) i = 0 := by
  have h := LAdicSheaf.geometricCompactlySupportedCohomologyMap_add f j kbar (0 : F ⟶ G) 0 i
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- **The maps on `Hⁱ_c(X_k̄, -)` commute with every endomorphism of `RΓ_c(X_k̄, -)`**, in
particular with the geometric Frobenius `π_X^*`. -/
@[reassoc]
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_pullback
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (i : ℤ)
    (θ : compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⟶
      compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyPullback B X ℓ f j kbar G i θ =
      LAdicSheaf.geometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i θ ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i := by
  show limMap _ ≫ limMap _ = limMap _ ≫ limMap _
  refine (lim.map_comp _ _).symm.trans (Eq.trans (congrArg lim.map ?_) (lim.map_comp _ _))
  refine natTrans_op_nat_ext fun n => ?_
  exact (geometricCompactSupportPadicCohomologyPullback B X ℓ f j kbar i θ).naturality
    (LAdicSheaf.padicLevelMap φ n)

/-- **`π_X^*` on `Hⁱ_c(X_k̄, -)` commutes with the maps induced by morphisms of ℓ-adic
sheaves.** -/
@[reassoc]
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i ≫
        LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard G i =
      LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i :=
  LAdicSheaf.geometricCompactlySupportedCohomologyMap_pullback f j kbar φ i _

/-- The ring homomorphism `End F → End_{ℤ_ℓ}(Hⁱ_c(X_k̄, F))` by which endomorphisms of an ℓ-adic
sheaf act on its compactly supported cohomology. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologyEndRingHom (F : LAdicSheaf B X ℓ)
    (i : ℤ) :
    End F →+* Module.End ℤ_[ℓ] (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i)
    where
  toFun φ := (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ.asHom i).hom
  map_one' := by
    change (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (𝟙 F) i).hom = _
    rw [LAdicSheaf.geometricCompactlySupportedCohomologyMap_id]
    rfl
  map_mul' φ ψ := by
    change (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (ψ.asHom ≫ φ.asHom) i).hom = _
    rw [LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp]
    rfl
  map_zero' := by
    change (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (0 : F ⟶ F) i).hom = _
    rw [LAdicSheaf.geometricCompactlySupportedCohomologyMap_zero]
    rfl
  map_add' φ ψ := by
    change (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (φ.asHom + ψ.asHom) i).hom = _
    rw [LAdicSheaf.geometricCompactlySupportedCohomologyMap_add]
    rfl

end Stacks.EtaleCohomology

end
