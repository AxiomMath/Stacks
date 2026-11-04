module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheafPreadditive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additive structure on the category of ℓ-adic sheaves

Morphisms of ℓ-adic sheaves add levelwise, the levelwise zero system is a zero object, the
levelwise biproduct of two ℓ-adic sheaves is again one and so is the levelwise cokernel of a
morphism. So the category of ℓ-adic sheaves on a Noetherian scheme is additive and has
cokernels.

## Main definitions

* `Stacks.EtaleCohomology.scalarAdjunction`: scalar reduction is left adjoint to restriction of
  scalars between consecutive coefficient rings.
* `Stacks.EtaleCohomology.LAdicSheaf.zeroSystem`, `.biprodSystem` and `.cokernelSystem`: the
  levelwise zero system, biproduct and cokernel, each with its transition maps.

## Main results

* `Stacks.EtaleCohomology.isWeakSerreClass_constructible`: Tag 03RZ (3) at the finite-level
  coefficients.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.preadditive`: ℓ-adic sheaves form a preadditive
  category (imported, Stacks 03UO).
* `Stacks.EtaleCohomology.LAdicSheaf.hasZeroObject`: the levelwise zero system is a zero object.
* `Stacks.EtaleCohomology.LAdicSheaf.hasFiniteBiproducts`: ℓ-adic sheaves have finite
  biproducts, so the category is additive.
* `Stacks.EtaleCohomology.LAdicSheaf.hasCokernels`: ℓ-adic sheaves have cokernels.

## Implementation notes

Scalar reduction `Stacks.EtaleCohomology.FiniteLevelSheaf.scalarReduction` is the left adjoint of
restriction of scalars between consecutive coefficient rings, and the compatibility condition on
an ℓ-adic sheaf says exactly that the mate of its transition map under that adjunction is an
isomorphism. The zero object, the biproduct and the cokernel are therefore all produced by one
statement about mates: the mate of a construction applied to two squares whose own mates are
isomorphisms is again an isomorphism, because the left adjoint preserves that construction. For
the biproduct this is preservation of biproducts by a left adjoint, for the cokernel
preservation of cokernels, which is where the right exactness of `· ⊗ ℤ/ℓⁿℤ` enters.

Constructibility of the zero sheaf, of a biproduct of constructible sheaves and of a cokernel of
a morphism of constructible sheaves is Tag 03RZ (3),
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf`: a weak Serre class
contains the zero object and is closed under biproducts and cokernels. Its coefficient universe
`max (u + 1) w` is instantiated at `w := u + 1`, which is the coefficient universe `u + 1` of
Tag 03UM's ℓ-adic sheaves.

**This is only part of Tag 03UO**, which asserts that the category of ℓ-adic sheaves is abelian,
so each result here carries that tag with a clause string naming what it covers and nothing
carries it unqualified. Kernels are missing, and with them normality of monomorphisms and
epimorphisms. The levelwise kernel is not a kernel in this category: the compatibility condition
fails for it, because `· ⊗ ℤ/ℓⁿℤ` is not left exact. The source instead takes the kernel of
`Φ = {φₙ}` to be the inverse system `{⋂_{m ≥ n} Im(Ker(φₘ) → Ker(φₙ))}`, which needs the
descending chain of those images to stabilise — the Noetherian object property of Tag 09YV and
the Serre, not merely weak Serre, property of constructible sheaves of modules, Tag 09BH, which
the library carries for sheaves of sets and of abelian groups but not for sheaves of modules.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open scoped ZeroObject

universe u

namespace Stacks.EtaleCohomology

section Mates

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- The mate of a commuting square along an adjunction commutes. -/
private theorem mateSquare {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A' B' : C} {A B : D} (f' : A' ⟶ B') (f : A ⟶ B)
    (tA : A' ⟶ R.obj A) (tB : B' ⟶ R.obj B) (w : f' ≫ tB = tA ≫ R.map f) :
    L.map f' ≫ (adj.homEquiv B' B).symm tB = (adj.homEquiv A' A).symm tA ≫ f := by
  apply (adj.homEquiv A' B).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simpa only [Equiv.apply_symm_apply] using w

variable [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]

private theorem mapBiprod_inv_map_fst (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (Y Z : C) [Limits.HasBinaryBiproduct Y Z] [Limits.PreservesBinaryBiproduct Y Z F] :
    (F.mapBiprod Y Z).inv ≫ F.map Limits.biprod.fst = Limits.biprod.fst := by
  rw [← Limits.biprod.lift_fst (F.map (Limits.biprod.fst : Y ⊞ Z ⟶ Y))
    (F.map (Limits.biprod.snd : Y ⊞ Z ⟶ Z)), ← Functor.mapBiprod_hom, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

private theorem mapBiprod_inv_map_snd (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (Y Z : C) [Limits.HasBinaryBiproduct Y Z] [Limits.PreservesBinaryBiproduct Y Z F] :
    (F.mapBiprod Y Z).inv ≫ F.map Limits.biprod.snd = Limits.biprod.snd := by
  rw [← Limits.biprod.lift_snd (F.map (Limits.biprod.fst : Y ⊞ Z ⟶ Y))
    (F.map (Limits.biprod.snd : Y ⊞ Z ⟶ Z)), ← Functor.mapBiprod_hom, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- A cokernel of mates is a mate: if the mates of the two vertical maps of a commuting square
are isomorphisms, so is the mate of the induced map on cokernels. -/
private theorem isIso_mate_cokernel [Limits.HasCokernels C] [Limits.HasCokernels D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A' B' : C} {A B : D} (f' : A' ⟶ B') (f : A ⟶ B)
    (tA : A' ⟶ R.obj A) (tB : B' ⟶ R.obj B) (w : f' ≫ tB = tA ≫ R.map f)
    [IsIso ((adj.homEquiv A' A).symm tA)] [IsIso ((adj.homEquiv B' B).symm tB)]
    (tC : Limits.cokernel f' ⟶ R.obj (Limits.cokernel f))
    (fac : Limits.cokernel.π f' ≫ tC = tB ≫ R.map (Limits.cokernel.π f)) :
    IsIso ((adj.homEquiv (Limits.cokernel f') (Limits.cokernel f)).symm tC) := by
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : Epi (Limits.cokernel.π f') := by
    show Epi (Limits.coequalizer.π f' 0); infer_instance
  have : Epi (L.map (Limits.cokernel.π f')) := inferInstance
  set β := (adj.homEquiv B' B).symm tB with hβ
  have heq : (adj.homEquiv (Limits.cokernel f') (Limits.cokernel f)).symm tC =
      (Limits.PreservesCokernel.iso L f').hom ≫
        (Limits.cokernel.mapIso (L.map f') f (asIso ((adj.homEquiv A' A).symm tA)) (asIso β)
          (mateSquare adj f' f tA tB w)).hom := by
    apply (cancel_epi (L.map (Limits.cokernel.π f'))).1
    rw [mateSquare adj _ _ tB tC fac, ← Category.assoc,
      Limits.PreservesCokernel.π_iso_hom]
    simp [Limits.cokernel.mapIso, Limits.cokernel.map, hβ]
  rw [heq]
  infer_instance

/-- A biproduct of mates is a mate: if the mates of two vertical maps are isomorphisms, so is the
mate of their biproduct. -/
private theorem isIso_mate_biprod [Preadditive C] [Limits.HasBinaryBiproducts C]
    [Preadditive D] [Limits.HasBinaryBiproducts D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    {A₁ A₂ : C} {B₁ B₂ : D}
    [Limits.PreservesBinaryBiproduct A₁ A₂ L] [Limits.PreservesBinaryBiproduct B₁ B₂ R]
    (t₁ : A₁ ⟶ R.obj B₁) (t₂ : A₂ ⟶ R.obj B₂)
    [IsIso ((adj.homEquiv A₁ B₁).symm t₁)] [IsIso ((adj.homEquiv A₂ B₂).symm t₂)] :
    IsIso ((adj.homEquiv (A₁ ⊞ A₂) (B₁ ⊞ B₂)).symm
      (Limits.biprod.map t₁ t₂ ≫ (R.mapBiprod B₁ B₂).inv)) := by
  have heq : (adj.homEquiv (A₁ ⊞ A₂) (B₁ ⊞ B₂)).symm
      (Limits.biprod.map t₁ t₂ ≫ (R.mapBiprod B₁ B₂).inv) =
      (L.mapBiprod A₁ A₂ ≪≫ Limits.biprod.mapIso (asIso ((adj.homEquiv A₁ B₁).symm t₁))
        (asIso ((adj.homEquiv A₂ B₂).symm t₂))).hom := by
    apply Limits.biprod.hom_ext
    · rw [← adj.homEquiv_naturality_right_symm, Category.assoc, mapBiprod_inv_map_fst,
        Limits.biprod.map_fst, adj.homEquiv_naturality_left_symm]
      show L.map Limits.biprod.fst ≫ (adj.homEquiv A₁ B₁).symm t₁ =
        (Limits.biprod.lift (L.map Limits.biprod.fst) (L.map Limits.biprod.snd) ≫
          Limits.biprod.map ((adj.homEquiv A₁ B₁).symm t₁)
            ((adj.homEquiv A₂ B₂).symm t₂)) ≫ Limits.biprod.fst
      rw [Category.assoc, Limits.biprod.map_fst, ← Category.assoc, Limits.biprod.lift_fst]
    · rw [← adj.homEquiv_naturality_right_symm, Category.assoc, mapBiprod_inv_map_snd,
        Limits.biprod.map_snd, adj.homEquiv_naturality_left_symm]
      show L.map Limits.biprod.snd ≫ (adj.homEquiv A₂ B₂).symm t₂ =
        (Limits.biprod.lift (L.map Limits.biprod.fst) (L.map Limits.biprod.snd) ≫
          Limits.biprod.map ((adj.homEquiv A₁ B₁).symm t₁)
            ((adj.homEquiv A₂ B₂).symm t₂)) ≫ Limits.biprod.snd
      rw [Category.assoc, Limits.biprod.map_snd, ← Category.assoc, Limits.biprod.lift_snd]
  rw [heq]
  infer_instance

end Mates

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

/-- Restriction of scalars along the quotient of consecutive coefficient rings, as a functor. -/
public abbrev restrictScalarsFunctor (n : ℕ) :
    FiniteLevelSheaf B X ℓ n ⥤ FiniteLevelSheaf B X ℓ (n + 1) :=
  sheafCompose (SmallEtale.topology B X.1 X.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))

/-- Sheafified extension of scalars along the quotient of consecutive coefficient rings, as a
functor; it is left adjoint to restriction of scalars. -/
public abbrev scalarReductionFunctor (n : ℕ) :
    FiniteLevelSheaf B X ℓ (n + 1) ⥤ FiniteLevelSheaf B X ℓ n :=
  Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.extendScalars.{0, 0, u + 1} (finiteLevelRingHom ℓ n))

/-- The adjunction between scalar reduction and restriction of scalars on sheaves. -/
public abbrev scalarAdjunction (n : ℕ) :
    scalarReductionFunctor B X ℓ n ⊣ restrictScalarsFunctor B X ℓ n :=
  Sheaf.adjunction (SmallEtale.topology B X.1 X.property)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))

/-- Restriction of scalars between consecutive coefficient rings is additive on sheaves, being
additive on modules and acting componentwise. -/
public instance additive_restrictScalarsFunctor (n : ℕ) :
    (restrictScalarsFunctor B X ℓ n).Additive := by
  constructor
  intro F G f g
  ext U : 3
  rfl

/-- Restriction of scalars is a right adjoint, so it preserves binary biproducts. -/
public instance preservesBinaryBiproduct_restrictScalarsFunctor (n : ℕ)
    (F G : FiniteLevelSheaf B X ℓ n) :
    PreservesBinaryBiproduct F G (restrictScalarsFunctor B X ℓ n) := by
  have : (restrictScalarsFunctor B X ℓ n).IsRightAdjoint :=
    (scalarAdjunction B X ℓ n).isRightAdjoint
  exact preservesBinaryBiproduct_of_preservesBinaryProduct _

/-- Scalar reduction is a left adjoint, so it preserves binary biproducts. -/
public instance preservesBinaryBiproduct_scalarReductionFunctor (n : ℕ)
    (F G : FiniteLevelSheaf B X ℓ (n + 1)) :
    PreservesBinaryBiproduct F G (scalarReductionFunctor B X ℓ n) := by
  have : (scalarReductionFunctor B X ℓ n).IsLeftAdjoint :=
    (scalarAdjunction B X ℓ n).isLeftAdjoint
  exact preservesBinaryBiproduct_of_preservesBinaryCoproduct _

variable [Fact ℓ.Prime]

omit [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **Stacks 03RZ (3)** at the finite-level coefficients: the constructible sheaves of
`ℤ/ℓⁿ⁺¹ℤ`-modules form a weak Serre class inside all such sheaves. -/
public theorem isWeakSerreClass_constructible (n : ℕ) :
    ObjectProperty.IsWeakSerreClass
      (fun F : FiniteLevelSheaf B X ℓ n =>
        IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) F) :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, 0} B X
    (ZMod (ℓ ^ (n + 1)))

variable [IsNoetherian X.1]

@[simp]
public theorem LAdicSheaf.comp_app {F G H : LAdicSheaf B X ℓ} (f : F ⟶ G) (g : G ⟶ H) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- The levelwise zero system, with zero transition maps. -/
public def LAdicSheaf.zeroSystem : LAdicSheaf.{u, u + 1} B X ℓ where
  level n := (0 : FiniteLevelSheaf.{u, u + 1} B X ℓ n)
  constructible n := by
    have := isWeakSerreClass_constructible B X ℓ n
    exact ObjectProperty.prop_zero _
  transition _ := 0
  reduction_isIso n := by
    have hzero : IsZero ((scalarReductionFunctor B X ℓ n).obj
        (0 : FiniteLevelSheaf.{u, u + 1} B X ℓ (n + 1))) :=
      (Functor.mapZeroObject (scalarReductionFunctor B X ℓ n)).isZero_iff.mpr (isZero_zero _)
    exact hzero.isIso (isZero_zero _) _

/-- The levelwise zero system is a zero object. -/
public theorem LAdicSheaf.zeroSystem_isZero : IsZero (LAdicSheaf.zeroSystem B X ℓ) := by
  apply IsInitial.isZero
  apply IsInitial.ofUniqueHom
    (fun G : LAdicSheaf.{u, u + 1} B X ℓ =>
      (⟨fun _ => 0, by intro n; simp⟩ : LAdicSheaf.zeroSystem B X ℓ ⟶ G))
  intro G m
  exact LAdicSheaf.Hom.ext _ _ _ fun n =>
    (isZero_zero (FiniteLevelSheaf.{u, u + 1} B X ℓ n)).eq_of_src _ _

@[simp]
public theorem LAdicSheaf.zeroSystem_level (n : ℕ) :
    (LAdicSheaf.zeroSystem B X ℓ).level n = 0 := rfl

/-- The category of ℓ-adic sheaves has a zero object. -/
@[stacks 03UO "zero object"]
public instance LAdicSheaf.hasZeroObject : HasZeroObject (LAdicSheaf B X ℓ) :=
  ⟨⟨LAdicSheaf.zeroSystem B X ℓ, LAdicSheaf.zeroSystem_isZero B X ℓ⟩⟩

namespace LAdicSheaf

variable {B X ℓ}

/-! ### Biproducts -/

/-- The transition map of the levelwise biproduct of two ℓ-adic sheaves: the biproduct of the
two transition maps, read in the restriction of scalars of the biproduct. -/
public def biprodTransition (F G : LAdicSheaf B X ℓ) (n : ℕ) :
    (F.level (n + 1) ⊞ G.level (n + 1)) ⟶
      (restrictScalarsFunctor B X ℓ n).obj (F.level n ⊞ G.level n) :=
  biprod.map (F.transition n) (G.transition n) ≫
    ((restrictScalarsFunctor B X ℓ n).mapBiprod (F.level n) (G.level n)).inv

public theorem biprodTransition_fac (F G : LAdicSheaf B X ℓ) (n : ℕ) :
    biprodTransition F G n ≫
        ((restrictScalarsFunctor B X ℓ n).mapBiprod (F.level n) (G.level n)).hom =
      biprod.map (F.transition n) (G.transition n) := by
  rw [biprodTransition, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The compatibility condition holds for the levelwise biproduct, because scalar reduction
preserves biproducts. -/
public theorem biprodTransition_reduction_isIso (F G : LAdicSheaf B X ℓ) (n : ℕ) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B X ℓ n
      (F.level (n + 1) ⊞ G.level (n + 1)) (F.level n ⊞ G.level n)
      (biprodTransition F G n)) := by
  have hF : IsIso (((scalarAdjunction B X ℓ n).homEquiv
      (F.level (n + 1)) (F.level n)).symm (F.transition n)) := F.reduction_isIso n
  have hG : IsIso (((scalarAdjunction B X ℓ n).homEquiv
      (G.level (n + 1)) (G.level n)).symm (G.transition n)) := G.reduction_isIso n
  exact isIso_mate_biprod (scalarAdjunction B X ℓ n) (F.transition n) (G.transition n)

/-- The levelwise biproduct of two ℓ-adic sheaves. -/
public def biprodSystem (F G : LAdicSheaf B X ℓ) : LAdicSheaf B X ℓ where
  level n := F.level n ⊞ G.level n
  constructible n := by
    have := isWeakSerreClass_constructible B X ℓ n
    exact ObjectProperty.prop_biprod _ (F.constructible n) (G.constructible n)
  transition n := biprodTransition F G n
  reduction_isIso n := biprodTransition_reduction_isIso F G n

@[simp]
public theorem biprodSystem_level (F G : LAdicSheaf B X ℓ) (n : ℕ) :
    (biprodSystem F G).level n = (F.level n ⊞ G.level n) := rfl

/-- The first projection off the levelwise biproduct. -/
public def biprodFst (F G : LAdicSheaf B X ℓ) : biprodSystem F G ⟶ F where
  app _ := biprod.fst
  naturality n := by
    change (biprod.fst : F.level (n + 1) ⊞ G.level (n + 1) ⟶ _) ≫ F.transition n =
      biprodTransition F G n ≫ (restrictScalarsFunctor B X ℓ n).map biprod.fst
    rw [← biprod.map_fst (F.transition n) (G.transition n), ← biprodTransition_fac F G n,
      Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst]

/-- The second projection off the levelwise biproduct. -/
public def biprodSnd (F G : LAdicSheaf B X ℓ) : biprodSystem F G ⟶ G where
  app _ := biprod.snd
  naturality n := by
    change (biprod.snd : F.level (n + 1) ⊞ G.level (n + 1) ⟶ _) ≫ G.transition n =
      biprodTransition F G n ≫ (restrictScalarsFunctor B X ℓ n).map biprod.snd
    rw [← biprod.map_snd (F.transition n) (G.transition n), ← biprodTransition_fac F G n,
      Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd]

/-- The map into the levelwise biproduct determined by a pair of maps. -/
public def biprodLift {H F G : LAdicSheaf B X ℓ} (f : H ⟶ F) (g : H ⟶ G) :
    H ⟶ biprodSystem F G where
  app n := biprod.lift (f.app n) (g.app n)
  naturality n := by
    change biprod.lift (f.app (n + 1)) (g.app (n + 1)) ≫ biprodTransition F G n =
      H.transition n ≫
        (restrictScalarsFunctor B X ℓ n).map (biprod.lift (f.app n) (g.app n))
    apply (cancel_mono
      ((restrictScalarsFunctor B X ℓ n).mapBiprod (F.level n) (G.level n)).hom).1
    rw [Category.assoc, biprodTransition_fac, Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst, biprod.lift_fst_assoc]
      exact f.naturality n
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd, biprod.lift_snd_assoc]
      exact g.naturality n

@[simp]
public theorem biprodLift_fst {H F G : LAdicSheaf B X ℓ} (f : H ⟶ F) (g : H ⟶ G) :
    biprodLift f g ≫ biprodFst F G = f :=
  LAdicSheaf.Hom.ext _ _ _ fun _ => biprod.lift_fst _ _

@[simp]
public theorem biprodLift_snd {H F G : LAdicSheaf B X ℓ} (f : H ⟶ F) (g : H ⟶ G) :
    biprodLift f g ≫ biprodSnd F G = g :=
  LAdicSheaf.Hom.ext _ _ _ fun _ => biprod.lift_snd _ _

public theorem biprodLift_unique {H F G : LAdicSheaf B X ℓ} (f : H ⟶ F) (g : H ⟶ G)
    (h : H ⟶ biprodSystem F G) (hf : h ≫ biprodFst F G = f) (hg : h ≫ biprodSnd F G = g) :
    h = biprodLift f g := by
  refine LAdicSheaf.Hom.ext _ _ _ fun n => biprod.hom_ext _ _ ?_ ?_
  · show h.app n ≫ biprod.fst = biprod.lift (f.app n) (g.app n) ≫ biprod.fst
    rw [biprod.lift_fst]
    exact congrArg (fun t : H ⟶ F => t.app n) hf
  · show h.app n ≫ biprod.snd = biprod.lift (f.app n) (g.app n) ≫ biprod.snd
    rw [biprod.lift_snd]
    exact congrArg (fun t : H ⟶ G => t.app n) hg

public instance hasBinaryProduct (F G : LAdicSheaf B X ℓ) : HasBinaryProduct F G :=
  HasLimit.mk ⟨BinaryFan.mk (biprodFst F G) (biprodSnd F G),
    BinaryFan.IsLimit.mk _ (fun f g => biprodLift f g) (fun f g => biprodLift_fst f g)
      (fun f g => biprodLift_snd f g) (fun f g h hf hg => biprodLift_unique f g h hf hg)⟩

variable (B X ℓ)

public instance hasBinaryProducts : HasBinaryProducts (LAdicSheaf B X ℓ) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- The category of ℓ-adic sheaves has finite products. -/
public instance hasFiniteProducts : HasFiniteProducts (LAdicSheaf B X ℓ) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **Stacks 03UO**, the additive part: the category of ℓ-adic sheaves on a Noetherian scheme
has finite biproducts, the biproduct being formed levelwise. -/
@[stacks 03UO "additive: finite biproducts, formed levelwise"]
public instance hasFiniteBiproducts : HasFiniteBiproducts (LAdicSheaf B X ℓ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

public instance hasBinaryBiproducts : HasBinaryBiproducts (LAdicSheaf B X ℓ) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-! ### Cokernels -/

variable {B X ℓ}

/-- The transition map of the levelwise cokernel of a morphism of ℓ-adic sheaves. -/
public def cokernelTransition {F G : LAdicSheaf B X ℓ} (f : F ⟶ G) (n : ℕ) :
    cokernel (f.app (n + 1)) ⟶ (restrictScalarsFunctor B X ℓ n).obj (cokernel (f.app n)) :=
  cokernel.desc _ (G.transition n ≫ (restrictScalarsFunctor B X ℓ n).map (cokernel.π (f.app n)))
    (by rw [← Category.assoc, f.naturality n, Category.assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero])

public theorem cokernelTransition_fac {F G : LAdicSheaf B X ℓ} (f : F ⟶ G) (n : ℕ) :
    cokernel.π (f.app (n + 1)) ≫ cokernelTransition f n =
      G.transition n ≫ (restrictScalarsFunctor B X ℓ n).map (cokernel.π (f.app n)) :=
  cokernel.π_desc _ _ _

/-- The compatibility condition holds for the levelwise cokernel, because scalar reduction is a
left adjoint and so preserves cokernels. -/
public theorem cokernelTransition_reduction_isIso {F G : LAdicSheaf B X ℓ} (f : F ⟶ G) (n : ℕ) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B X ℓ n
      (cokernel (f.app (n + 1))) (cokernel (f.app n)) (cokernelTransition f n)) := by
  have hF : IsIso (((scalarAdjunction B X ℓ n).homEquiv
      (F.level (n + 1)) (F.level n)).symm (F.transition n)) := F.reduction_isIso n
  have hG : IsIso (((scalarAdjunction B X ℓ n).homEquiv
      (G.level (n + 1)) (G.level n)).symm (G.transition n)) := G.reduction_isIso n
  exact isIso_mate_cokernel (scalarAdjunction B X ℓ n) (f.app (n + 1)) (f.app n)
    (F.transition n) (G.transition n) (f.naturality n) (cokernelTransition f n)
    (cokernelTransition_fac f n)

/-- The levelwise cokernel of a morphism of ℓ-adic sheaves. -/
@[sga "4½ Rapport 2.7" "Cokernel clause of 2.7"]
public def cokernelSystem {F G : LAdicSheaf B X ℓ} (f : F ⟶ G) : LAdicSheaf B X ℓ where
  level n := cokernel (f.app n)
  constructible n := by
    have := isWeakSerreClass_constructible B X ℓ n
    exact ObjectProperty.prop_cokernel _ (f.app n) (F.constructible n) (G.constructible n)
  transition n := cokernelTransition f n
  reduction_isIso n := cokernelTransition_reduction_isIso f n

@[simp]
public theorem cokernelSystem_level {F G : LAdicSheaf B X ℓ} (f : F ⟶ G) (n : ℕ) :
    (cokernelSystem f).level n = cokernel (f.app n) := rfl

/-- The projection onto the levelwise cokernel. -/
public def cokernelSystemπ {F G : LAdicSheaf B X ℓ} (f : F ⟶ G) : G ⟶ cokernelSystem f where
  app n := cokernel.π (f.app n)
  naturality n := cokernelTransition_fac f n

public theorem comp_cokernelSystemπ {F G : LAdicSheaf B X ℓ} (f : F ⟶ G) :
    f ≫ cokernelSystemπ f = 0 :=
  LAdicSheaf.Hom.ext _ _ _ fun n => cokernel.condition (f.app n)

/-- The map out of the levelwise cokernel determined by a morphism killing `f`. -/
public def cokernelSystemDesc {F G H : LAdicSheaf B X ℓ} (f : F ⟶ G) (h : G ⟶ H)
    (w : ∀ n, f.app n ≫ h.app n = 0) : cokernelSystem f ⟶ H where
  app n := cokernel.desc _ (h.app n) (w n)
  naturality n := by
    change cokernel.desc _ (h.app (n + 1)) (w (n + 1)) ≫ H.transition n =
      cokernelTransition f n ≫
        (restrictScalarsFunctor B X ℓ n).map (cokernel.desc _ (h.app n) (w n))
    have hepi : Epi (cokernel.π (f.app (n + 1))) := by
      change Epi (coequalizer.π (f.app (n + 1)) 0)
      infer_instance
    apply (cancel_epi (cokernel.π (f.app (n + 1)))).1
    rw [← Category.assoc, cokernel.π_desc, ← Category.assoc, cokernelTransition_fac,
      Category.assoc, ← Functor.map_comp, cokernel.π_desc]
    exact h.naturality n

/-- **Stacks 03UO**, the cokernel part: the category of ℓ-adic sheaves on a Noetherian scheme has
cokernels, formed levelwise. -/
@[stacks 03UO "cokernels, formed levelwise"]
public instance hasCokernels : HasCokernels (LAdicSheaf B X ℓ) where
  has_colimit {F G} f := HasColimit.mk
    ⟨CokernelCofork.ofπ (cokernelSystemπ f) (comp_cokernelSystemπ f),
      CokernelCofork.IsColimit.ofπ _ _
        (fun h wh => cokernelSystemDesc f h
          (fun n => by
            simpa only [LAdicSheaf.comp_app, LAdicSheaf.Hom.zero_app] using
              congrArg (fun t : F ⟶ _ => t.app n) wh))
        (fun h wh => LAdicSheaf.Hom.ext _ _ _ fun n => cokernel.π_desc _ _ _)
        (fun h wh d hd => LAdicSheaf.Hom.ext _ _ _ fun n => by
          have hepi : Epi (cokernel.π (f.app n)) := by
            change Epi (coequalizer.π (f.app n) 0)
            infer_instance
          apply (cancel_epi (cokernel.π (f.app n))).1
          change cokernel.π (f.app n) ≫ d.app n =
            cokernel.π (f.app n) ≫ cokernel.desc _ (h.app n) _
          rw [cokernel.π_desc]
          exact congrArg (fun t : G ⟶ _ => t.app n) hd)⟩

end LAdicSheaf

end Stacks.EtaleCohomology

end
