module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison

/-!
# Tensoring with a finite locally free module, and its dual, on the derived category

Let `X` be a scheme and `ℰ` a finite locally free `𝒪_X`-module with dual `ℰ^∨ = 𝓗om(ℰ, 𝒪_X)`.
The dual is a left dual of `ℰ` for the tensor product of `𝒪_X`-modules ([Stacks, Tag 0FNV]), so
`- ⊗ ℰ ⊣ - ⊗ ℰ^∨`, and both functors are exact. This file records the consequences used by
[Stacks, Tag 0BS4]:

* `Stacks.Duality.LocallyFreeTwist.twistAdjunction` — `- ⊗ ℰ ⊣ - ⊗ ℰ^∨` on `𝒪_X`-modules;
* `Stacks.Duality.LocallyFreeTwist.derivedTwistAdjunction` — the induced adjunction between the
  derived functors on `D(𝒪_X)`, at the locally small model;
* `Stacks.Duality.LocallyFreeTwist.twist_linear` — for a scheme over a field `k`, `- ⊗ 𝒩` is a
  `k`-linear functor, so that the derived adjunction is `k`-linear on Hom-spaces;
* `Stacks.Duality.LocallyFreeTwist.mapDerivedTwistQIso` — at the class of a complex `L`, the
  derived functor of `- ⊗ ℰ^∨` is the derived tensor product `L ⊗^L ℰ^∨[0]` of
  [Stacks, Tag 06YU], `ℰ^∨` placed in degree zero being K-flat.

## Implementation notes

The monoidal structure is `Stacks.SheafOfModules.OnSpace.monoidal`, whose tensor product is the
sheaf tensor product by `rfl`; `tensorRightIsoTwist` records that its `tensorRight` is the flipped
`Stacks.SheafOfModules.Tensor.sheafTensor` as a functor. Exactness of `- ⊗ ℰ` and of `- ⊗ ℰ^∨` is
read off adjunctions together with [Stacks, Tag 05NB]: `- ⊗ ℰ^∨` is a right adjoint, `- ⊗ ℰ` is
isomorphic by the symmetry to `ℰ ⊗ -`, the right adjoint of `ℰ^∨ ⊗ -`.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Duality.LocallyFreeTwist

open Stacks.SheafOfModules.OnSpace

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X` of `X`, as a sheaf of commutative rings. -/
abbrev R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  X.toRingedSpace.sheaf

/-- `𝒪_X`-modules in the spelling of the monoidal structure of [Stacks, Tag 01CA]. -/
abbrev Mod : Type (u + 1) := SheafOfModules.{u} (structureSheafRing X.toRingedSpace)

/-- `- ⊗ N` on `𝒪_X`-modules. -/
abbrev twist (N : Mod X) : Mod X ⥤ Mod X :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).flip.obj N

variable {X}

/-- `tensorRight N` of the monoidal structure of [Stacks, Tag 01CA] is `twist X N`. -/
def tensorRightIsoTwist (N : Mod X) : MonoidalCategory.tensorRight (C := Mod X) N ≅ twist X N :=
  NatIso.ofComponents (fun A => Iso.refl ((twist X N).obj A)) (fun {A A'} f => by
    have h := monoidal_tensorHom X.toRingedSpace f (𝟙 N)
    change 𝟙 _ ≫ (MonoidalCategory.tensorHom (C := Mod X) f (𝟙 N)) ≫ 𝟙 _ = _ at h
    rw [Category.id_comp, Category.comp_id, tensorHom_id] at h
    change MonoidalCategory.whiskerRight (C := Mod X) f N ≫ 𝟙 _ = 𝟙 _ ≫ _
    refine (Category.comp_id _).trans (h.trans (Eq.trans ?_ (Category.id_comp _).symm))
    exact (congrArg (fun z => _ ≫ z) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _))

/-- `tensorLeft N` of the monoidal structure is `sheafTensor.obj N`. -/
def tensorLeftIsoTensor (N : Mod X) :
    MonoidalCategory.tensorLeft (C := Mod X) N ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj N :=
  NatIso.ofComponents
    (fun A => Iso.refl
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj N).obj A))
    (fun {A A'} f => by
      have h := monoidal_tensorHom X.toRingedSpace (𝟙 N) f
      change 𝟙 _ ≫ (MonoidalCategory.tensorHom (C := Mod X) (𝟙 N) f) ≫ 𝟙 _ = _ at h
      rw [Category.id_comp, Category.comp_id, id_tensorHom] at h
      change MonoidalCategory.whiskerLeft (C := Mod X) N f ≫ 𝟙 _ = 𝟙 _ ≫ _
      refine (Category.comp_id _).trans (h.trans (Eq.trans ?_ (Category.id_comp _).symm))
      change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).map (𝟙 N)).app A ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj N).map f = _
      exact (congrArg (fun z => NatTrans.app z A ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj N).map f)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).map_id N)).trans
        (Category.id_comp _))

variable (E : Mod X) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The dual `E^∨ = 𝓗om(E, 𝒪_X)`. -/
abbrev dual : Mod X := dualSheaf X.toRingedSpace E

/-- The exact pairing of [Stacks, Tag 0FNV] between `E` and its dual. -/
@[instance_reducible]
def pairing : ExactPairing E (dual E) :=
  dualSheafExactPairing X.toRingedSpace E
    (@isLocallyFiniteFreeSummand_of_isFiniteLocallyFree X.toRingedSpace E hE)

/-- **`- ⊗ E ⊣ - ⊗ E^∨`** for a finite locally free `E`. -/
def twistAdjunction : twist X E ⊣ twist X (dual E) :=
  letI := pairing E
  ((tensorRightAdjunction E (dual E)).ofNatIsoLeft (tensorRightIsoTwist E)).ofNatIsoRight
    (tensorRightIsoTwist (dual E))

/-- **`E ⊗ - ⊣ ... `**: `tensorLeft E` is a right adjoint. -/
def tensorLeftAdjunctionE :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj (dual E) ⊣
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj E :=
  letI := pairing E
  ((tensorLeftAdjunction E (dual E)).ofNatIsoLeft (tensorLeftIsoTensor (dual E))).ofNatIsoRight
    (tensorLeftIsoTensor E)

variable {X : Scheme.{u}}

example : DerivedCategory (Mod X) = DerivedCategory X.Modules := rfl

example : (inferInstance : Category (DerivedCategory (Mod X))) =
    (inferInstance : Category (DerivedCategory X.Modules)) := rfl

/-- `- ⊗ N` preserves finite colimits. -/
instance (N : Mod X) : PreservesFiniteColimits (twist X N) :=
  Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj (R X) N

variable (E : Mod X) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- `- ⊗ E^∨` preserves finite limits. -/
instance : PreservesFiniteLimits (twist X (dual E)) :=
  have : PreservesLimitsOfSize.{0, 0} (twist X (dual E)) :=
    (twistAdjunction E).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- `- ⊗ E` preserves finite limits. -/
instance : PreservesFiniteLimits (twist X E) :=
  have : PreservesLimitsOfSize.{0, 0}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj E) :=
    (tensorLeftAdjunctionE E).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{0, 0} (twist X E) :=
    @preservesLimits_of_natIso _ _ _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding (R X)).app E) this
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- `- ⊗ E` is additive. -/
instance : (twist X E).Additive :=
  have := (twistAdjunction E).isLeftAdjoint
  Functor.additive_of_preserves_binary_products _

/-- `- ⊗ E^∨` is additive. -/
instance : (twist X (dual E)).Additive :=
  have := (twistAdjunction E).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- The dual of a finite locally free module is flat. -/
theorem isFlat_dual :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R X) (dual E) :=
  ⟨(inferInstance : PreservesFiniteLimits (twist X (dual E))),
    (inferInstance : PreservesFiniteColimits (twist X (dual E)))⟩

/-- The derived adjunction `(- ⊗ E)~ ⊣ (- ⊗ E^∨)~` on `D(𝒪_X)`. -/
def derivedTwistAdjunction :
    (twist X E).mapDerivedCategory ⊣ (twist X (dual E)).mapDerivedCategory :=
  (twistAdjunction E).mapDerivedCategory

variable {X : Scheme.{u}}

/-- `- ⊗ N` on a morphism is the right whiskering of the monoidal structure. -/
theorem twist_map_eq (N : Mod X) {A B : Mod X} (g : A ⟶ B) :
    (twist X N).map g = MonoidalCategory.whiskerRight (C := Mod X) g N :=
  ((Category.comp_id _).symm.trans ((tensorRightIsoTwist N).hom.naturality g)).trans
    (Category.id_comp _) |>.symm

section Linear

/-- The image of a local pure tensor is `𝒪_X`-linear in its first factor. -/
theorem tensorObjTmul_smul_left (A B : Mod X) (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (r : (structureSheafRing X.toRingedSpace).obj.obj U) (z : A.val.obj U) (y : B.val.obj U) :
    tensorObjTmul X.toRingedSpace A B U (r • z) y =
      r • (tensorObjTmul X.toRingedSpace A B U z y :
        (MonoidalCategory.tensorObj (C := Mod X) A B).val.obj U) :=
  (congrArg (SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A B U)
    (TensorProduct.smul_tmul' (show X.presheaf.obj U from r) z y).symm).trans
    (((SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace
      (PresheafOfModules.tensorObj (O := X.presheaf) A.val B.val)).app U).hom.map_smul
      (show (SheafOfModules.TensorStalkRingedSpace.O X.toRingedSpace).obj U from r) (z ⊗ₜ y))

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- **`- ⊗ N` commutes with the action of `k`**: a scalar acts on a sheaf of modules through
its image in `Γ(X, 𝒪_X)`, and the tensor product is `𝒪_X`-bilinear on local sections. -/
theorem twist_map_smul (N : Mod X) (a : k) {A B : Mod X} (g : A ⟶ B) :
    letI : Linear k (Mod X) := Scheme.Modules.linearOverBase f
    (twist X N).map (a • g) = a • (twist X N).map g := by
  let : Linear k (Mod X) := Scheme.Modules.linearOverBase f
  rw [twist_map_eq, twist_map_eq]
  apply tensor_hom_ext X.toRingedSpace
  intro U x y
  have h1 := whiskerRight_tmul X.toRingedSpace (a • g) N U x y
  have h2 := whiskerRight_tmul X.toRingedSpace g N U x y
  have s1 := Stacks.SheafOfModules.smul_val_app X.ringCatSheaf k ⊤ isTerminalTop
    (Stacks.LocalCohomology.baseScalars k f) a g U x
  have s2 := Stacks.SheafOfModules.smul_val_app X.ringCatSheaf k ⊤ isTerminalTop
    (Stacks.LocalCohomology.baseScalars k f) a
    (MonoidalCategory.whiskerRight (C := Mod X) g N) U (tensorObjTmul X.toRingedSpace A N U x y)
  refine h1.trans (Eq.trans ?_ (s2.trans (congrArg _ h2)).symm)
  refine (congrArg (fun z => tensorObjTmul X.toRingedSpace B N U z y) s1).trans ?_
  exact tensorObjTmul_smul_left B N U _ _ y

/-- **`- ⊗ N` is a `k`-linear functor** for the `k`-linear structure over the base. -/
theorem twist_linear (N : Mod X) :
    letI : Linear k (Mod X) := Scheme.Modules.linearOverBase f
    (twist X N).Linear k :=
  let : Linear k (Mod X) := Scheme.Modules.linearOverBase f
  ⟨fun g a => twist_map_smul f N a g⟩

end Linear

section Comparison

variable (E : Mod X) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **`(- ⊗ E^∨)~ (K) ≅ K ⊗^L E^∨[0]`** at the class of a complex. -/
def mapDerivedTwistQIso (L : CochainComplex (Mod X) ℤ) :
    (twist X (dual E)).mapDerivedCategory.obj (DerivedCategory.Q.obj L) ≅
      ((Stacks.Duality.derivedTensor X).obj (DerivedCategory.Q.obj L)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Mod X) (ComplexShape.up ℤ) 0).obj (dual E))) :=
  (twist X (dual E)).mapDerivedCategoryFactors.app L ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)) L (dual E)).symm ≪≫
    ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonRight L _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat (R X) (dual E)
        (isFlat_dual E) 0)).symm

end Comparison

section Naturality

/-- A square of coevaluations, whiskered on the left by `A` and reassociated. -/
theorem unit_whisker_square {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] {A Y₁ Y₂ Z₁ Z₂ : 𝒞}
    {p₁ : 𝟙_ 𝒞 ⟶ Y₁ ⊗ Z₁} {p₂ : 𝟙_ 𝒞 ⟶ Y₂ ⊗ Z₂} (d : Z₂ ⟶ Z₁) (g : Y₁ ⟶ Y₂)
    (h : p₂ ≫ Y₂ ◁ d = p₁ ≫ g ▷ Z₁) :
    ((ρ_ A).inv ≫ A ◁ p₂ ≫ (α_ A Y₂ Z₂).inv) ≫ (A ⊗ Y₂) ◁ d =
      ((ρ_ A).inv ≫ A ◁ p₁ ≫ (α_ A Y₁ Z₁).inv) ≫ (A ◁ g) ▷ Z₁ := by
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_inv_naturality_right,
    ← MonoidalCategory.associator_inv_naturality_middle,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, h]

/-- `E` has `E^∨` as a right dual. -/
@[instance_reducible]
def hasRightDual (E : Mod X)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    HasRightDual E :=
  @HasRightDual.mk _ _ _ E (dual E) (pairing E)

variable {E₁ E₂ : Mod X} [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂]

/-- **The dual `g^∨ : E₂^∨ ⟶ E₁^∨` of `g : E₁ ⟶ E₂`**, its right adjoint mate for the exact
pairings of [Stacks, Tag 0FNV]. -/
def dualMap (g : E₁ ⟶ E₂) : dual E₂ ⟶ dual E₁ :=
  @rightAdjointMate _ _ _ E₁ E₂ (hasRightDual E₁) (hasRightDual E₂) g

/-- `- ⊗ c` for a morphism `c : N ⟶ N'`. -/
def twistMap {N N' : Mod X} (c : N ⟶ N') : twist X N ⟶ twist X N' :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).flip.map c

/-- The component of `twistMap c` at `A` is the left whiskering `A ◁ c`. -/
theorem twistMap_app {N N' : Mod X} (c : N ⟶ N') (A : Mod X) :
    (twistMap c).app A = MonoidalCategory.whiskerLeft (C := Mod X) A c :=
  ((Category.comp_id _).symm.trans ((tensorLeftIsoTensor A).hom.naturality c)).trans
    (Category.id_comp _) |>.symm

/-- The unit of `- ⊗ E ⊣ - ⊗ E^∨` at `A` is `A ≅ A ⊗ 𝟙 ⟶ A ⊗ (E ⊗ E^∨) ≅ (A ⊗ E) ⊗ E^∨`,
through the coevaluation. -/
theorem twistAdjunction_unit_app (E : Mod X)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (A : Mod X) :
    (twistAdjunction E).unit.app A =
      letI := pairing E
      (ρ_ A).inv ≫ A ◁ η_ E (dual E) ≫ (α_ A E (dual E)).inv := by
  let := pairing E
  simp only [Functor.id_obj, Functor.comp_obj, twistAdjunction, tensorRightAdjunction,
    tensorRightHomEquiv, tensorRightIsoTwist, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoLeft_unit, Category.assoc, NatTrans.comp_app, Functor.flip_obj_obj,
    curriedTensor_obj_obj, Adjunction.mkOfHomEquiv_unit_app, tensor_whiskerLeft, Equiv.coe_fn_mk,
    id_whiskerRight, Category.comp_id, Functor.whiskerRight_app, Functor.flip_obj_map,
    curriedTensor_map_app, Functor.whiskerLeft_app]
  show _ ≫ _ ≫ _ ≫ MonoidalCategory.whiskerRight (C := Mod X) (𝟙 _) (dual E) ≫ 𝟙 _ = _
  rw [MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id]

/-- **The units of `- ⊗ E ⊣ - ⊗ E^∨` are natural in `E`**, for the dual map `g^∨`: this is the
naturality of the coevaluation, `CategoryTheory.coevaluation_comp_rightAdjointMate`. -/
theorem twistAdjunction_unit_dualMap (g : E₁ ⟶ E₂) (A : Mod X) :
    (twistAdjunction E₂).unit.app A ≫
        (Functor.whiskerLeft (twist X E₂) (twistMap (dualMap g))).app A =
      (twistAdjunction E₁).unit.app A ≫
        (Functor.whiskerRight (twistMap g) (twist X (dual E₁))).app A := by
  rw [Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let := hasRightDual E₁
  let := hasRightDual E₂
  rw [twistAdjunction_unit_app, twistAdjunction_unit_app, twistMap_app, twistMap_app]
  refine Eq.trans ?_ (congrArg (fun z => _ ≫ z) (twist_map_eq (dual E₁) (A ◁ g)).symm)
  exact unit_whisker_square (dualMap g) g (coevaluation_comp_rightAdjointMate (C := Mod X) g)

end Naturality

end Stacks.Duality.LocallyFreeTwist
