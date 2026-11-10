module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffinePushforwardMulBy
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffinePushforwardTilde
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.RegularAction

/-!
# Right exact tensor functors out of `QCoh(𝒪_𝒳)` along an affine morphism from a scheme

Let `𝒳` be an algebraic stack, `R` a ring and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor
functor commuting with direct sums.  Let `g : U ⟶ 𝒳` be an affine 1-morphism from a scheme `U`
with ring of global functions `A`.  Then `C = F(g_{QCoh,*}𝒪_U)` is a commutative `R`-algebra,
there is a ring map `A → C`, and `M ↦ F(g_{QCoh,*} M~)` is `M ↦ M ⊗_A C` viewed as an
`R`-module.  This is Stacks 0GRK.

## Main definitions

* `AlgebraicGeometry.Stack.affineTensorAlgebra`: the commutative `R`-algebra `C`.
* `AlgebraicGeometry.Stack.affineTensorRingHom`: the ring map `A → C`, `a ↦ F(κ(a))(1)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology
  AlgebraicStacks.modulesMonoidalCategory AlgebraicStacks.modulesSymmetricCategory
  FibredSite.monoidalCategoryQuasicoherentModules

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y
local notation "𝒪c[" Y "]" => AlgebraicStacks.fppfStructureSheaf _ _ _ Y

section Symmetric

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The symmetric monoidal structure on `QCoh(𝒪_𝒴)`**: the full symmetric monoidal subcategory
of `Mod(𝒪_𝒴)` cut out by quasi-coherence. -/
@[instance_reducible]
noncomputable def AlgebraicStacks.quasicoherentSymmetricCategory
    (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    SymmetricCategory (AlgebraicStacks.quasicoherentModules B S hS 𝒴) :=
  ObjectProperty.fullSymmetricSubcategory _

end Symmetric

attribute [local instance] AlgebraicStacks.quasicoherentSymmetricCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)

/-- The structure sheaf `𝒪_U`, as an object of `QCoh(𝒪_U)`. -/
noncomputable abbrev quasicoherentStructureSheaf :
    AlgebraicStacks.quasicoherentModules B S hS (schemeStack.{u, w} B S hS U) :=
  ⟨SheafOfModules.unit 𝒪[schemeStack.{u, w} B S hS U],
    SheafOfModules.isQuasicoherentOnSite_unit _⟩

/-- **`g_{QCoh,*}𝒪_U`**, an object of `QCoh(𝒪_𝒳)`. -/
noncomputable abbrev affineQuasicoherentStructureSheaf :
    AlgebraicStacks.quasicoherentModules B S hS 𝒳 :=
  (affineQuasicoherentPushforward g hg).obj (quasicoherentStructureSheaf.{u, w} (U := U))

/-- **`g_{QCoh,*}𝒪_U` is a monoid object of `QCoh(𝒪_𝒳)`** (Stacks 0GQR, 0GQM). -/
@[instance_reducible]
noncomputable def monObjAffineQuasicoherentStructureSheaf :
    MonObj (affineQuasicoherentStructureSheaf g hg) :=
  @ObjectProperty.monObjOfObj _ _ _ _ _ (affineQuasicoherentStructureSheaf g hg)
    (monObjAffinePushforwardStructureSheaf g hg)

attribute [local instance] monObjAffineQuasicoherentStructureSheaf

/-- **`g_{QCoh,*}𝒪_U` is a commutative monoid object of `QCoh(𝒪_𝒳)`.** -/
theorem isCommMonObjAffineQuasicoherentStructureSheaf :
    IsCommMonObj (affineQuasicoherentStructureSheaf g hg) :=
  @ObjectProperty.isCommMonObjOfObj _ _ _ _ _ _ (affineQuasicoherentStructureSheaf g hg)
    (monObjAffinePushforwardStructureSheaf g hg) (isCommMonObjAffinePushforwardStructureSheaf g hg)

/-- **`κ(a)`: multiplication by `a ∈ A` on `g_{QCoh,*}𝒪_U`.** -/
noncomputable def affineGlobalMul (a : schemeGlobalRing U) :
    affineQuasicoherentStructureSheaf g hg ⟶ affineQuasicoherentStructureSheaf g hg :=
  (affineQuasicoherentPushforward g hg).map (ObjectProperty.homMk (globalMul.{u, w} U a))

/-- **The square of the proof of Stacks 0GRK commutes**: `(κ(a) ⊗ 1) ≫ μ = μ ≫ κ(a)`. -/
theorem affineGlobalMul_whiskerRight_mul (a : schemeGlobalRing U) :
    affineGlobalMul g hg a ▷ affineQuasicoherentStructureSheaf g hg ≫ MonObj.mul =
      MonObj.mul ≫ affineGlobalMul g hg a :=
  @ObjectProperty.whiskerRight_mul_monObjOfObj _ _ _ _ _ (affineQuasicoherentStructureSheaf g hg)
    (monObjAffinePushforwardStructureSheaf g hg) (affineGlobalMul g hg a)
    (affinePushforward_map_globalMul_whiskerRight_mul g hg a)

section GlobalMul

variable (U) in
/-- The global function `1` pulls back to `1` over every object `T ⟶ U`. -/
lemma globalSection_one (T : (Over U)ᵒᵖ) : globalSection.{u, w} U 1 T = 1 :=
  map_one ((schemeGlobalRingHom U).app T).hom

variable (U) in
/-- The global function `0` pulls back to `0` over every object `T ⟶ U`. -/
lemma globalSection_zero (T : (Over U)ᵒᵖ) : globalSection.{u, w} U 0 T = 0 :=
  map_zero ((schemeGlobalRingHom U).app T).hom

variable (U) in
/-- Pulling back global functions to `T ⟶ U` is multiplicative. -/
lemma globalSection_mul (a b : schemeGlobalRing U) (T : (Over U)ᵒᵖ) :
    globalSection.{u, w} U (a * b) T = globalSection.{u, w} U a T * globalSection.{u, w} U b T :=
  map_mul ((schemeGlobalRingHom U).app T).hom a b

variable (U) in
/-- Pulling back global functions to `T ⟶ U` is additive. -/
lemma globalSection_add (a b : schemeGlobalRing U) (T : (Over U)ᵒᵖ) :
    globalSection.{u, w} U (a + b) T = globalSection.{u, w} U a T + globalSection.{u, w} U b T :=
  map_add ((schemeGlobalRingHom U).app T).hom a b

/-- Two endomorphisms of the structure sheaf of `U` are equal if they agree on every section. -/
private theorem unit_hom_ext (U : BigFppfOver B S hS)
    {φ ψ : SheafOfModules.unit 𝒪[schemeStack.{u, w} B S hS U] ⟶
      SheafOfModules.unit 𝒪[schemeStack.{u, w} B S hS U]}
    (h : ∀ (T : (Over U)ᵒᵖ) x, (φ.val.app T).hom x = (ψ.val.app T).hom x) : φ = ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T =>
    ModuleCat.hom_ext (LinearMap.ext (h T)))

/-- On sections over `T ⟶ U`, multiplication by `a` is multiplication by `a` pulled back to `T`. -/
private theorem globalMul_app_hom (U : BigFppfOver B S hS) (a : schemeGlobalRing U) (T : (Over U)ᵒᵖ)
    (x : (SheafOfModules.unit 𝒪[schemeStack.{u, w} B S hS U]).val.obj T) :
    ((globalMul.{u, w} U a).val.app T).hom x = globalSection.{u, w} U a T *
      PresheafOfModules.unitToRing (A := (𝒪c[schemeStack.{u, w} B S hS U]).obj) x :=
  rfl

variable (U) in
/-- Multiplication by `1` on the structure sheaf of `U` is the identity. -/
theorem globalMul_one : globalMul.{u, w} U 1 = 𝟙 _ :=
  unit_hom_ext.{u, w} U fun T x => by
    rw [globalMul_app_hom U, globalSection_one, one_mul]
    rfl

variable (U) in
/-- Multiplication by `a * b` on the structure sheaf of `U` is multiplication by `b` followed by
multiplication by `a`. -/
theorem globalMul_mul (a b : schemeGlobalRing U) :
    globalMul.{u, w} U (a * b) = globalMul.{u, w} U b ≫ globalMul.{u, w} U a :=
  unit_hom_ext.{u, w} U fun T x => by
    rw [globalMul_app_hom U, globalSection_mul, mul_assoc]
    rfl

variable (U) in
/-- Multiplication by `a + b` on the structure sheaf of `U` is the sum of multiplication by `a`
and multiplication by `b`. -/
theorem globalMul_add (a b : schemeGlobalRing U) :
    globalMul.{u, w} U (a + b) = globalMul.{u, w} U a + globalMul.{u, w} U b :=
  unit_hom_ext.{u, w} U fun T x => by
    rw [globalMul_app_hom U, globalSection_add, add_mul]
    rfl

variable (U) in
/-- Multiplication by `0` on the structure sheaf of `U` is the zero morphism. -/
theorem globalMul_zero : globalMul.{u, w} U 0 = 0 :=
  unit_hom_ext.{u, w} U fun T x => by
    rw [globalMul_app_hom U, globalSection_zero, zero_mul]
    rfl

/-- `g_{QCoh,*}` is additive on morphisms. -/
theorem affineQuasicoherentPushforward_map_add
    {M N : AlgebraicStacks.quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)}
    (f f' : M ⟶ N) :
    (affineQuasicoherentPushforward g hg).map (f + f') =
      (affineQuasicoherentPushforward g hg).map f + (affineQuasicoherentPushforward g hg).map f' :=
  rfl

/-- `g_{QCoh,*}` sends the zero morphism to the zero morphism. -/
theorem affineQuasicoherentPushforward_map_zero
    {M N : AlgebraicStacks.quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)} :
    (affineQuasicoherentPushforward g hg).map (0 : M ⟶ N) = 0 :=
  rfl

/-- `κ(1)` is the identity of `g_{QCoh,*}𝒪_U`. -/
theorem affineGlobalMul_one : affineGlobalMul g hg 1 = 𝟙 _ := by
  rw [affineGlobalMul, globalMul_one]
  exact (affineQuasicoherentPushforward g hg).map_id _

/-- `κ(a * b) = κ(b) ≫ κ(a)`. -/
theorem affineGlobalMul_mul (a b : schemeGlobalRing U) :
    affineGlobalMul g hg (a * b) = affineGlobalMul g hg b ≫ affineGlobalMul g hg a := by
  rw [affineGlobalMul, affineGlobalMul, affineGlobalMul, globalMul_mul,
    ← Functor.map_comp]
  rfl

/-- `κ(a + b) = κ(a) + κ(b)`. -/
theorem affineGlobalMul_add (a b : schemeGlobalRing U) :
    affineGlobalMul g hg (a + b) = affineGlobalMul g hg a + affineGlobalMul g hg b := by
  rw [affineGlobalMul, affineGlobalMul, affineGlobalMul, globalMul_add]
  exact affineQuasicoherentPushforward_map_add g hg _ _

/-- `κ(0) = 0`. -/
theorem affineGlobalMul_zero : affineGlobalMul g hg 0 = 0 := by
  rw [affineGlobalMul, globalMul_zero]
  exact affineQuasicoherentPushforward_map_zero g hg

end GlobalMul

section Functor

variable {R : Type u} [CommRing R]
  (F : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.LaxBraided]
  [F.Additive]

/-- **`C = F(g_{QCoh,*}𝒪_U)`**, with the structure of a commutative `R`-algebra
(`AlgebraicGeometry.Stack.instCommRingAffineTensorAlgebra`,
`AlgebraicGeometry.Stack.instAlgebraAffineTensorAlgebra`). -/
def affineTensorAlgebra : Type u := F.obj (affineQuasicoherentStructureSheaf g hg)

/-- `C` is a commutative ring: `F` carries the commutative monoid `g_{QCoh,*}𝒪_U` to a
commutative monoid of `Mod_R`. -/
noncomputable instance instCommRingAffineTensorAlgebra : CommRing (affineTensorAlgebra g hg F) :=
  haveI := isCommMonObjAffineQuasicoherentStructureSheaf g hg
  Functor.tensorFunctorCommRing F (affineQuasicoherentStructureSheaf g hg)

/-- `C` is an `R`-algebra. -/
noncomputable instance instAlgebraAffineTensorAlgebra : Algebra R (affineTensorAlgebra g hg F) :=
  Functor.tensorFunctorAlgebraStr F (affineQuasicoherentStructureSheaf g hg)

omit [F.Additive] in
/-- **`κ'(a) = F(κ(a))` is multiplication by `F(κ(a))(1)`** on `C`. -/
theorem map_affineGlobalMul_apply (a : schemeGlobalRing U) (c : affineTensorAlgebra g hg F) :
    @id (affineTensorAlgebra g hg F) ((F.map (affineGlobalMul g hg a)).hom c) =
      @id (affineTensorAlgebra g hg F)
        ((F.map (affineGlobalMul g hg a)).hom (1 : affineTensorAlgebra g hg F)) * c :=
  Functor.tensorFunctor_map_eq_mul F _ _ (affineGlobalMul_whiskerRight_mul g hg a) c

/-- **The ring map `A → C`, `a ↦ F(κ(a))(1)`** of Stacks 0GRK. -/
noncomputable def affineTensorRingHom : schemeGlobalRing U →+* affineTensorAlgebra g hg F where
  toFun a := @id (affineTensorAlgebra g hg F)
    ((F.map (affineGlobalMul g hg a)).hom (1 : affineTensorAlgebra g hg F))
  map_one' := by
    rw [affineGlobalMul_one, F.map_id]
    rfl
  map_mul' a b := by
    simp only [affineGlobalMul_mul, Functor.map_comp, ModuleCat.hom_comp]
    exact map_affineGlobalMul_apply g hg F a _
  map_zero' := by
    rw [affineGlobalMul_zero, F.map_zero]
    rfl
  map_add' a b := by
    rw [affineGlobalMul_add, F.map_add]
    rfl

/-- The ring map `A → C` sends `a` to `F(κ(a))(1)`. -/
theorem affineTensorRingHom_apply (a : schemeGlobalRing U) :
    affineTensorRingHom g hg F a = @id (affineTensorAlgebra g hg F)
      ((F.map (affineGlobalMul g hg a)).hom (1 : affineTensorAlgebra g hg F)) := rfl

end Functor

section Tilde

variable (U) in
/-- **`M ↦ M~`, `Mod_A ⥤ QCoh(𝒪_U)`**: the quasi-coherent module attached to an `A`-module. -/
noncomputable def tildeQuasicoherent :
    ModuleCat.{u} (schemeGlobalRing U) ⥤
      AlgebraicStacks.quasicoherentModules B S hS (schemeStack.{u, w} B S hS U) :=
  ObjectProperty.lift _ (tildeFunctor.{u, w} U) fun M => isQuasicoherentOnSite_tilde.{u, w} M

variable (U) in
/-- `A~ ≅ 𝒪_U` in `QCoh(𝒪_U)`. -/
noncomputable def tildeQuasicoherentSelfIso :
    (tildeQuasicoherent.{u, w} U).obj (ModuleCat.of _ (schemeGlobalRing U)) ≅
      quasicoherentStructureSheaf.{u, w} (U := U) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso (tildeSelfIso.{u, w} U)

variable (U) in
/-- Under `A~ ≅ 𝒪_U`, the image of multiplication by `a` on `A` is multiplication by `a` on
`𝒪_U`. -/
theorem tildeQuasicoherent_map_regularMul (a : schemeGlobalRing U) :
    (tildeQuasicoherent.{u, w} U).map (ModuleCat.regularMul _ a) ≫
        (tildeQuasicoherentSelfIso.{u, w} U).hom =
      (tildeQuasicoherentSelfIso.{u, w} U).hom ≫ ObjectProperty.homMk (globalMul.{u, w} U a) :=
  ObjectProperty.hom_ext _ (tildeFunctor_map_regularMul.{u, w} U a)

/-- **`M ↦ g_{QCoh,*} M~` preserves colimits** (Stacks 0GQY for the affine `g`). -/
instance preservesColimits_tildeQuasicoherent_comp :
    PreservesColimitsOfSize.{u, u}
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg) := by
  have e : tildeFunctor.{u, w} U ⋙ affinePushforward.{u, w, u} g hg ≅
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg) ⋙
        ObjectProperty.ι _ :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have : PreservesColimitsOfSize.{u, u}
      ((tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg) ⋙
        ObjectProperty.ι _) :=
    preservesColimits_of_natIso e
  exact preservesColimits_of_reflects_of_preserves _ (ObjectProperty.ι _)

end Tilde

section Main

variable {R : Type u} [CommRing R]
  (F : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.LaxBraided]
  [F.Additive] [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]

/-- **`M ↦ F(g_{QCoh,*} M~)` preserves colimits**: `M ↦ g_{QCoh,*} M~` does, and `F` is right
exact and commutes with direct sums. -/
instance preservesColimits_tildeQuasicoherent_comp_comp :
    PreservesColimitsOfSize.{u, u}
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F) := by
  have : PreservesColimitsOfSize.{0, 0}
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  have : PreservesColimitsOfShape WalkingParallelPair
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F) :=
    comp_preservesColimitsOfShape (tildeQuasicoherent.{u, w} U ⋙
      affineQuasicoherentPushforward g hg) F
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F) := fun _ =>
    comp_preservesColimitsOfShape (tildeQuasicoherent.{u, w} U ⋙
      affineQuasicoherentPushforward g hg) F
  exact preservesColimits_of_preservesCoequalizers_and_coproducts _

/-- `C = F(g_{QCoh,*}𝒪_U)` as an `R`-module is `C` with `R` acting through `R → C`. -/
noncomputable def affineTensorAlgebraRestrictIso :
    F.obj (affineQuasicoherentStructureSheaf g hg) ≅
      (ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).obj
        (@ModuleCat.of (affineTensorAlgebra g hg F) _ (affineTensorAlgebra g hg F) _
          Semiring.toModule) :=
  { hom := ModuleCat.ofHom (X := F.obj (affineQuasicoherentStructureSheaf g hg))
      (Y := (ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).obj
        (@ModuleCat.of (affineTensorAlgebra g hg F) _ (affineTensorAlgebra g hg F) _
          Semiring.toModule))
      { toFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => Algebra.smul_def (A := affineTensorAlgebra g hg F) r x }
    inv := ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).obj
        (@ModuleCat.of (affineTensorAlgebra g hg F) _ (affineTensorAlgebra g hg F) _
          Semiring.toModule))
      (Y := F.obj (affineQuasicoherentStructureSheaf g hg))
      { toFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => (Algebra.smul_def (A := affineTensorAlgebra g hg F) r x).symm }
    hom_inv_id := rfl
    inv_hom_id := rfl }

/-- **`F(g_{QCoh,*} A~) ≅ A ⊗_A C`**, the value of both sides on the free module `A`. -/
noncomputable def affineTensorFreeIso :
    (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F).obj
        (ModuleCat.of _ (schemeGlobalRing U)) ≅
      (ModuleCat.extendScalars (affineTensorRingHom g hg F) ⋙
        ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).obj
          (ModuleCat.of _ (schemeGlobalRing U)) :=
  F.mapIso ((affineQuasicoherentPushforward g hg).mapIso (tildeQuasicoherentSelfIso.{u, w} U)) ≪≫
    affineTensorAlgebraRestrictIso g hg F ≪≫
      (ModuleCat.restrictScalars _).mapIso
        (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).symm

omit [F.LaxBraided] [F.Additive] [PreservesFiniteColimits F]
  [∀ (J : Type u), PreservesColimitsOfShape (Discrete J) F] in
/-- Under `F(g_{QCoh,*} A~) ≅ F(g_{QCoh,*}𝒪_U)`, the image of multiplication by `a` on `A` is
`F(κ(a))`. -/
theorem affineTensorFreeIso_step₁ (a : schemeGlobalRing U) :
    (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F).map
        (ModuleCat.regularMul _ a) ≫
      F.map ((affineQuasicoherentPushforward g hg).map (tildeQuasicoherentSelfIso.{u, w} U).hom) =
    F.map ((affineQuasicoherentPushforward g hg).map (tildeQuasicoherentSelfIso.{u, w} U).hom) ≫
      F.map (affineGlobalMul g hg a) := by
  simp only [Functor.comp_map, ← Functor.map_comp, tildeQuasicoherent_map_regularMul]
  rfl

omit [PreservesFiniteColimits F] [∀ (J : Type u), PreservesColimitsOfShape (Discrete J) F] in
/-- Under `C ≅ A ⊗_A C` as `R`-modules, `F(κ(a))` corresponds to multiplication by `a` on the
free module `A`, extended to `A ⊗_A C`. -/
theorem affineTensorFreeIso_step₂ (a : schemeGlobalRing U) :
    F.map (affineGlobalMul g hg a) ≫ (affineTensorAlgebraRestrictIso g hg F).hom ≫
        ((ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).mapIso
          (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).symm).hom =
      (affineTensorAlgebraRestrictIso g hg F).hom ≫
        ((ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).mapIso
          (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).symm).hom ≫
        (ModuleCat.extendScalars (affineTensorRingHom g hg F) ⋙
          ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).map
            (ModuleCat.regularMul _ a) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.symm_hom, Functor.mapIso_hom,
    Functor.comp_map]
  change Stacks.PullbackModel.tmul (M := ModuleCat.of _ (schemeGlobalRing U))
      (affineTensorRingHom g hg F)
      (@id (affineTensorAlgebra g hg F) ((F.map (affineGlobalMul g hg a)).hom c)) 1 =
    Stacks.PullbackModel.tmul (M := ModuleCat.of _ (schemeGlobalRing U))
      (affineTensorRingHom g hg F) (@id (affineTensorAlgebra g hg F) c) (a * 1)
  exact (congrArg (fun z : affineTensorAlgebra g hg F =>
      Stacks.PullbackModel.tmul (M := ModuleCat.of _ (schemeGlobalRing U))
        (affineTensorRingHom g hg F) z 1) (map_affineGlobalMul_apply g hg F a c)).trans
    (TensorProduct.smul_tmul (R := schemeGlobalRing U)
      (M := (ModuleCat.restrictScalars (affineTensorRingHom g hg F)).obj
        (@ModuleCat.of (affineTensorAlgebra g hg F) _ (affineTensorAlgebra g hg F) _
          Semiring.toModule)) a c 1)

omit [PreservesFiniteColimits F] [∀ (J : Type u), PreservesColimitsOfShape (Discrete J) F] in
/-- `affineTensorFreeIso` commutes with the action of multiplication by `a ∈ A` on the free
module `A`. -/
theorem affineTensorFreeIso_hom_comm (a : schemeGlobalRing U) :
    (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F).map
        (ModuleCat.regularMul _ a) ≫ (affineTensorFreeIso g hg F).hom =
      (affineTensorFreeIso g hg F).hom ≫
        (ModuleCat.extendScalars (affineTensorRingHom g hg F) ⋙
          ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F))).map
            (ModuleCat.regularMul _ a) := by
  simp only [affineTensorFreeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, affineTensorFreeIso_step₁, Category.assoc]
  exact congrArg (F.map ((affineQuasicoherentPushforward g hg).map
    (tildeQuasicoherentSelfIso.{u, w} U).hom) ≫ ·) (affineTensorFreeIso_step₂ g hg F a)

/-- **Stacks 0GRK, for an affine 1-morphism `g : U ⟶ 𝒳` out of a scheme**: the functor
`M ↦ F(g_{QCoh,*} M~)` is `M ↦ M ⊗_A C` viewed as an `R`-module, with `C = F(g_{QCoh,*}𝒪_U)` and
the ring map `A → C` of `AlgebraicGeometry.Stack.affineTensorRingHom`. -/
noncomputable def affineTensorFunctorIso :
    tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F ≅
      ModuleCat.extendScalars (affineTensorRingHom g hg F) ⋙
        ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F)) :=
  ModuleCat.isoOfRegularAction (schemeGlobalRing U) R _ _ (affineTensorFreeIso g hg F)
    (affineTensorFreeIso_hom_comm g hg F)

end Main

end AlgebraicGeometry.Stack
