module

public import StacksFrontier.CategoryTheory.Abelian.ScalarQuotientTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StableKernel

/-!
# The underlying tower of abelian sheaves of an ℓ-adic sheaf

Forgetting the module structure sends a finite level of an ℓ-adic sheaf to a sheaf of abelian
groups, and the transition maps turn the levels into an inverse system indexed by `ℕᵒᵖ`. The
forgetful functor on a finite level is additive, full, faithful, preserves monomorphisms and
kernels, and carries a finite level of an ℓ-adic sheaf to a Noetherian object.

## Main definitions

* `Stacks.EtaleCohomology.underlyingLevelFunctor`: the forgetful functor on a finite level.
* `Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdicTower`: the inverse system of underlying
  abelian sheaves of an ℓ-adic sheaf.
* `Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdicFunctor`: the functor producing it.

## Main results

* `Stacks.EtaleCohomology.noetherian_of_full_subobject_lift`: a full and faithful functor
  preserving monomorphisms carries a Noetherian object to a Noetherian object once every
  subobject of the image is in its range.
* `Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdicFunctor_full` and `_faithful`: the
  underlying tower determines the ℓ-adic sheaf and all its morphisms.
* `Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdicLevel_noetherian`: each level of the
  underlying tower is a Noetherian object.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u u₁ u₂ u₃ v₁ v₂ v₃

namespace Stacks.EtaleCohomology

section SubobjectTransport

/-- The image of a subobject under a functor preserving monomorphisms. -/
public def subobjectFunctorMap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.PreservesMonomorphisms] (P : C) (S : Subobject P) :
    Subobject (F.obj P) := Subobject.mk (F.map S.arrow)

/-- A full and faithful functor preserving monomorphisms reflects the order on subobjects. -/
public theorem subobjectFunctorMap_le_iff
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (P : C) (S T : Subobject P) :
    subobjectFunctorMap F P S ≤ subobjectFunctorMap F P T ↔ S ≤ T := by
  refine ⟨fun h => Subobject.le_of_comm
    (F.preimage (Subobject.ofMkLEMk (F.map S.arrow) (F.map T.arrow) h)) (F.map_injective ?_),
    fun h => Subobject.mk_le_mk_of_comm (F.map (S.ofLE T h))
      (by rw [← Functor.map_comp, Subobject.ofLE_arrow])⟩
  rw [Functor.map_comp, Functor.map_preimage]
  exact Subobject.ofMkLEMk_comp h

/-- The image of the subobject presented by a monomorphism is presented by its image. -/
public theorem subobjectFunctorMap_mk
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.PreservesMonomorphisms] {P Q : C} (i : Q ⟶ P) [Mono i] :
    subobjectFunctorMap F P (Subobject.mk i) = Subobject.mk (F.map i) := by
  apply Subobject.mk_eq_mk_of_comm _ _ (F.mapIso (Subobject.underlyingIso i))
  change F.map (Subobject.underlyingIso i).hom ≫ F.map i = _
  rw [← Functor.map_comp]
  exact F.congr_map (Subobject.underlyingIso_hom_comp_eq_mk i)

/-- A full and faithful functor preserving monomorphisms carries a Noetherian object to a
Noetherian object, provided every subobject of the image comes from a subobject of the source. -/
public theorem noetherian_of_full_subobject_lift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (P : C) [IsNoetherianObject P]
    (hlift : ∀ S : Subobject (F.obj P), ∃ (Q : C) (i : Q ⟶ P) (_ : Mono i),
      ∃ e : F.obj Q ≅ Subobject.underlying.obj S, e.hom ≫ S.arrow = F.map i) :
    IsNoetherianObject (F.obj P) := by
  let e : Subobject P ↪o Subobject (F.obj P) :=
    OrderEmbedding.ofMapLEIff (subobjectFunctorMap F P) (subobjectFunctorMap_le_iff F P)
  have he : Function.Surjective e := fun S ↦ by
    obtain ⟨Q, i, hi, a, ha⟩ := hlift S
    refine ⟨Subobject.mk i, ?_⟩
    change subobjectFunctorMap F P (Subobject.mk i) = S
    rw [subobjectFunctorMap_mk]
    exact Subobject.mk_eq_of_comm _ a ha
  let e' := OrderIso.ofSurjective e he
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro s
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ((show Subobject (F.obj P) →o Subobject P from ⟨e'.symm, e'.symm.monotone⟩).comp s)
  exact ⟨n, fun m hm => e'.symm.injective (hn m hm)⟩

end SubobjectTransport

section AnnihilatedAbelianSheaf

/-- Multiplication by a natural number on a morphism of sheaves of abelian groups is computed
sectionwise. -/
public theorem abelianSheaf_nsmul_app
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Q : Sheaf J AddCommGrpCat.{u₂}}
    (f : P ⟶ Q) (r : ℕ) (U : Cᵒᵖ) (x : P.obj.obj U) :
    ((r • f).hom.app U).hom x = r • (f.hom.app U).hom x := by
  change ((((sheafToPresheaf J AddCommGrpCat).map (r • f)).app U).hom x) = _
  rw [Functor.map_nsmul]
  rfl

/-- Forgetting the `ℤ/nℤ`-module structure of a module is full: an additive map between modules
annihilated by `n` is automatically linear. -/
public theorem forget₂_zmod_full (n : ℕ) :
    (forget₂ (ModuleCat.{u₁} (ZMod n)) AddCommGrpCat).Full where
  map_surjective {M N} f :=
    ⟨ModuleCat.ofHom (AddMonoidHom.toZModLinearMap n (M := M) (M₁ := N) f.hom), rfl⟩

/-- A sheaf of abelian groups annihilated by `n`, read as a sheaf of `ℤ/nℤ`-modules. -/
public def zmodSheafOfAnnihilated
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (n : ℕ)
    (P : Sheaf J AddCommGrpCat.{max u₁ v₁ u₂})
    (h : ∀ U (x : P.obj.obj U), n • x = 0) :
    Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod n)) := by
  letI (U : Cᵒᵖ) : Module (ZMod n) (P.obj.obj U) := AddCommGroup.zmodModule (h U)
  refine ⟨{
    obj U := ModuleCat.of (ZMod n) (P.obj.obj U)
    map i := ModuleCat.ofHom ((P.obj.map i).hom.toZModLinearMap n)
    map_id U := by ext x; exact ConcreteCategory.congr_hom (P.obj.map_id U) x
    map_comp i j := by ext x; exact ConcreteCategory.congr_hom (P.obj.map_comp i j) x }, ?_⟩
  exact Presheaf.isSheaf_of_isSheaf_comp J _
    (forget₂ (ModuleCat.{max u₁ v₁ u₂} (ZMod n)) AddCommGrpCat) P.property

/-- Forgetting the module structure of `Stacks.EtaleCohomology.zmodSheafOfAnnihilated` returns
the sheaf of abelian groups it was built from. -/
public def zmodSheafOfAnnihilatedIso
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (n : ℕ)
    (P : Sheaf J AddCommGrpCat.{max u₁ v₁ u₂})
    (h : ∀ U (x : P.obj.obj U), n • x = 0) :
    (sheafCompose J (forget₂ (ModuleCat.{max u₁ v₁ u₂} (ZMod n)) AddCommGrpCat)).obj
      (zmodSheafOfAnnihilated.{u₁, u₂, v₁} J n P h) ≅ P where
  hom := ⟨{ app U := AddCommGrpCat.ofHom (AddMonoidHom.id _) }⟩
  inv := ⟨{ app U := AddCommGrpCat.ofHom (AddMonoidHom.id _) }⟩

/-- A subobject of the underlying sheaf of abelian groups of a sheaf of `ℤ/nℤ`-modules is itself
annihilated by `n`. -/
public theorem zmodSheaf_subobject_annihilated
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (n : ℕ)
    (P : Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod n)))
    (S : Sheaf J AddCommGrpCat.{max u₁ v₁ u₂})
    (i : S ⟶ (sheafCompose J (forget₂ (ModuleCat.{max u₁ v₁ u₂} (ZMod n)) AddCommGrpCat)).obj P)
    [Mono i] : ∀ U (x : S.obj.obj U), n • x = 0 := by
  have ht : n • (𝟙 ((sheafCompose J
      (forget₂ (ModuleCat.{max u₁ v₁ u₂} (ZMod n)) AddCommGrpCat)).obj P)) = 0 := by
    ext U x
    rw [abelianSheaf_nsmul_app]
    change n • (x : P.obj.obj U) = 0
    exact ZModModule.char_nsmul_eq_zero n (show P.obj.obj U from x)
  have hs : n • (𝟙 S) = 0 := by
    apply (cancel_mono i).1
    rw [zero_comp, Preadditive.nsmul_comp, Category.id_comp]
    simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero] using
      congrArg (fun f => i ≫ f) ht
  intro U x
  have he := congrArg (fun f : S ⟶ S ↦ (f.hom.app U).hom x) hs
  rwa [abelianSheaf_nsmul_app] at he

end AnnihilatedAbelianSheaf

/-- The category of `ℤ/kℤ`-modules in `Type (u + 1)` has finite limits. -/
public instance zmodModuleCat_hasFiniteLimits (k : ℕ) :
    HasFiniteLimits (ModuleCat.{u + 1} (ZMod k)) :=
  Abelian.hasFiniteLimits

/-- The category of `ℤ/kℤ`-modules in `Type (u + 1)` has kernels. -/
public instance zmodModuleCat_hasLimitsOfShape_walkingParallelPair (k : ℕ) :
    HasLimitsOfShape WalkingParallelPair (ModuleCat.{u + 1} (ZMod k)) :=
  HasFiniteLimits.out WalkingParallelPair

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

/-- Forgetting the module structure of a finite level, as a functor into sheaves of abelian
groups. -/
public abbrev underlyingLevelFunctor (n : ℕ) :=
  sheafCompose (SmallEtale.topology B X.1 X.property)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The forgetful functor on a finite level is additive. -/
public theorem underlyingLevelFunctor_additive (n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).Additive := by
  let I := sheafToPresheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}
  have : (underlyingLevelFunctor B X ℓ n ⋙ I).Additive := by
    change (sheafToPresheaf _ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat)).Additive
    infer_instance
  exact Functor.additive_of_comp_faithful _ I

attribute [local instance] underlyingLevelFunctor_additive

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The forgetful functor on a finite level preserves monomorphisms. -/
public theorem underlyingLevelFunctor_preservesMonomorphisms (n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).PreservesMonomorphisms := by
  let I := sheafToPresheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}
  have : (underlyingLevelFunctor B X ℓ n ⋙ I).PreservesMonomorphisms := by
    change (sheafToPresheaf _ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat)).PreservesMonomorphisms
    infer_instance
  exact Functor.preservesMonomorphisms_of_preserves_of_reflects _ I

attribute [local instance] underlyingLevelFunctor_preservesMonomorphisms

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The forgetful functor on a finite level is a left adjoint. -/
public theorem underlyingLevelFunctor_isLeftAdjoint (n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).IsLeftAdjoint := by
  have : (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat).IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom (ZMod (ℓ ^ (n + 1)))) ⋙
      forget₂ (ModuleCat ℤ) AddCommGrpCat).IsLeftAdjoint
    infer_instance
  exact sheafCompose_isLeftAdjoint _ _

attribute [local instance] underlyingLevelFunctor_isLeftAdjoint

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The forgetful functor on a finite level preserves kernels. -/
public theorem underlyingLevelFunctor_preservesKernels (n : ℕ) :
    PreservesLimitsOfShape WalkingParallelPair (underlyingLevelFunctor B X ℓ n) := by
  let I := sheafToPresheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}
  have : PreservesLimitsOfShape WalkingParallelPair
      (underlyingLevelFunctor B X ℓ n ⋙ I) := by
    change PreservesLimitsOfShape WalkingParallelPair
      (sheafToPresheaf (SmallEtale.topology B X.1 X.property)
          (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ I

attribute [local instance] underlyingLevelFunctor_preservesKernels

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The forgetful functor on a finite level is full: an additive map of sheaves annihilated by
`ℓⁿ⁺¹` is linear. -/
public theorem underlyingLevelFunctor_full (n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).Full := by
  let := forget₂_zmod_full.{u + 1} (ℓ ^ (n + 1))
  infer_instance

attribute [local instance] underlyingLevelFunctor_full

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- Restriction of scalars is invisible to the forgetful functor. -/
public theorem underlyingLevelFunctor_restrict_map (n : ℕ)
    {F G : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (f : F ⟶ G) :
    (underlyingLevelFunctor B X ℓ (n + 1)).map ((restrictScalarsFunctor B X ℓ n).map f) =
      (underlyingLevelFunctor B X ℓ n).map f := rfl

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

/-- The underlying sheaf of abelian groups of a finite level of an ℓ-adic sheaf. -/
public abbrev underlyingLAdicLevel (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :=
  (underlyingLevelFunctor B X ℓ n).obj (F.level n)

/-- The transition map of the underlying tower. -/
public def underlyingLAdicTransition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    underlyingLAdicLevel B X ℓ F (n + 1) ⟶ underlyingLAdicLevel B X ℓ F n :=
  (underlyingLevelFunctor B X ℓ (n + 1)).map (F.transition n)

/-- The Verschiebung of the underlying tower. -/
public def underlyingLAdicVerschiebung (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    underlyingLAdicLevel B X ℓ F n ⟶ underlyingLAdicLevel B X ℓ F (n + 1) :=
  (underlyingLevelFunctor B X ℓ (n + 1)).map (verschiebung F n)

/-- An additive functor carries a composite equal to multiplication by `r` to the same
multiplication. -/
private theorem map_comp_eq_nsmul_id
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (G : C ⥤ D) [G.Additive] {P Q : C} (f : P ⟶ Q) (g : Q ⟶ P) (r : ℕ)
    (h : f ≫ g = r • 𝟙 P) : G.map f ≫ G.map g = r • 𝟙 (G.obj P) := by
  rw [← Functor.map_comp, h, Functor.map_nsmul, G.map_id]

/-- The transition map followed by the Verschiebung is multiplication by `ℓ`. -/
public theorem underlyingLAdicTransition_verschiebung (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    underlyingLAdicTransition B X ℓ F n ≫ underlyingLAdicVerschiebung B X ℓ F n =
      ℓ • (𝟙 (underlyingLAdicLevel B X ℓ F (n + 1))) :=
  map_comp_eq_nsmul_id _ _ _ _ (transition_verschiebung F n)

/-- The Verschiebung followed by the transition map is multiplication by `ℓ`. -/
public theorem underlyingLAdicVerschiebung_transition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    underlyingLAdicVerschiebung B X ℓ F n ≫ underlyingLAdicTransition B X ℓ F n =
      ℓ • (𝟙 (underlyingLAdicLevel B X ℓ F n)) :=
  map_comp_eq_nsmul_id _ _ _ _ (verschiebung_transition F n)

/-- The inverse system of underlying sheaves of abelian groups of an ℓ-adic sheaf. -/
public def underlyingLAdicTower (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    ℕᵒᵖ ⥤ Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence (underlyingLAdicTransition B X ℓ F)

/-- The map of underlying towers induced by a morphism of ℓ-adic sheaves. -/
public def underlyingLAdicTowerMap {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) :
    underlyingLAdicTower B X ℓ F ⟶ underlyingLAdicTower B X ℓ G :=
  NatTrans.ofOpSequence (fun n => (underlyingLevelFunctor B X ℓ n).map (f.app n))
    (fun n => by
      simp only [underlyingLAdicTower, Functor.ofOpSequence_map_homOfLE_succ]
      change (underlyingLevelFunctor B X ℓ (n + 1)).map (F.transition n) ≫
        (underlyingLevelFunctor B X ℓ (n + 1)).map
          ((restrictScalarsFunctor B X ℓ n).map (f.app n)) =
        (underlyingLevelFunctor B X ℓ (n + 1)).map (f.app (n + 1)) ≫
        (underlyingLevelFunctor B X ℓ (n + 1)).map (G.transition n)
      rw [← Functor.map_comp, ← Functor.map_comp, f.naturality])

/-- Passing to the underlying tower of abelian sheaves, as a functor. -/
public def underlyingLAdicFunctor :
    LAdicSheaf.{u, u + 1} B X ℓ ⥤
      (ℕᵒᵖ ⥤ Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}) where
  obj := underlyingLAdicTower B X ℓ
  map := underlyingLAdicTowerMap B X ℓ
  map_id F := NatTrans.ext <| funext fun n =>
    (underlyingLevelFunctor B X ℓ n.unop).map_id (F.level n.unop)
  map_comp f g := NatTrans.ext <| funext fun n =>
    (underlyingLevelFunctor B X ℓ n.unop).map_comp (f.app n.unop) (g.app n.unop)

/-- A morphism of ℓ-adic sheaves is determined by the map of underlying towers. -/
public theorem underlyingLAdicFunctor_faithful : (underlyingLAdicFunctor B X ℓ).Faithful where
  map_injective {F G} f g h := by
    apply AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext
    exact fun n => (underlyingLevelFunctor B X ℓ n).map_injective (NatTrans.congr_app h ⟨n⟩)

/-- The morphism of ℓ-adic sheaves whose levels are the preimages of the levels of a map of
underlying towers. -/
public def underlyingLAdicFunctor_preimage {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (η : underlyingLAdicTower B X ℓ F ⟶ underlyingLAdicTower B X ℓ G) : F ⟶ G where
  app n := (underlyingLevelFunctor B X ℓ n).preimage (η.app ⟨n⟩)
  naturality n := by
    have hp : ∀ m : ℕ, (underlyingLevelFunctor B X ℓ m).map
        ((underlyingLevelFunctor B X ℓ m).preimage (η.app ⟨m⟩)) = η.app ⟨m⟩ :=
      fun m => (underlyingLevelFunctor B X ℓ m).map_preimage _
    apply (underlyingLevelFunctor B X ℓ (n + 1)).map_injective
    rw [Functor.map_comp, Functor.map_comp, hp (n + 1),
      underlyingLevelFunctor_restrict_map, hp n]
    have h := (η.naturality (homOfLE (Nat.le_add_right n 1)).op).symm
    simp only [underlyingLAdicTower, Functor.ofOpSequence_map_homOfLE_succ] at h
    exact h

/-- Every map of underlying towers comes from a morphism of ℓ-adic sheaves. -/
public theorem underlyingLAdicFunctor_full : (underlyingLAdicFunctor B X ℓ).Full where
  map_surjective {_ _} η := ⟨underlyingLAdicFunctor_preimage B X ℓ η,
    NatTrans.ext <| funext fun n => (underlyingLevelFunctor B X ℓ n.unop).map_preimage (η.app n)⟩

/-- Each level of the underlying tower of an ℓ-adic sheaf is a Noetherian object. -/
public theorem underlyingLAdicLevel_noetherian (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    IsNoetherianObject (underlyingLAdicLevel B X ℓ F n) := by
  have : IsNoetherianObject (F.level n) := isNoetherianObject_level F n
  refine noetherian_of_full_subobject_lift (underlyingLevelFunctor B X ℓ n) (F.level n) ?_
  intro S
  let hS := zmodSheaf_subobject_annihilated.{u + 1, u + 1, u}
    (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1))
    (F.level n) (Subobject.underlying.obj S) S.arrow
  let Q := zmodSheafOfAnnihilated.{u + 1, u + 1, u}
    (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1))
    (Subobject.underlying.obj S) hS
  let e : (underlyingLevelFunctor B X ℓ n).obj Q ≅ Subobject.underlying.obj S :=
    zmodSheafOfAnnihilatedIso.{u + 1, u + 1, u}
      (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1))
      (Subobject.underlying.obj S) hS
  let i : Q ⟶ F.level n := (underlyingLevelFunctor B X ℓ n).preimage (e.hom ≫ S.arrow)
  have hi : (underlyingLevelFunctor B X ℓ n).map i = e.hom ≫ S.arrow :=
    (underlyingLevelFunctor B X ℓ n).map_preimage _
  exact ⟨Q, i, (underlyingLevelFunctor B X ℓ n).mono_of_mono_map (by rw [hi]; infer_instance), e,
    hi.symm⟩

end LAdicSheaf

end Stacks.EtaleCohomology

end
