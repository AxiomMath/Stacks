module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Additive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantFree

/-!
# The constant ℓ-adic sheaf

The levels `ℤ/ℓⁿ⁺¹ℤ` of the ℓ-adic coefficients carry, on a quasi-compact quasi-separated
scheme, the extensions by zero `j_{U!}\underline{ℤ/ℓⁿ⁺¹ℤ}_U` of the constant free rank-one
module sheaves at a fixed quasi-compact quasi-separated étale object `U`. Each is
constructible ([Stacks, Tag 03S8]), and the successive scalar reductions of the system are
isomorphisms, so the system is an ℓ-adic sheaf in the sense of [Stacks, Tag 03UM]. At the final
object `X / X` of the small étale site it is the constant ℓ-adic sheaf.

## Main definitions

* `AlgebraicGeometry.moduleShriekConstantGenerator`: the section of
  `j_{U!}\underline{R}_U` over `U` corresponding to the identity morphism; a morphism out of
  `j_{U!}\underline{R}_U` is determined by, and determines, its value on it.
* `Stacks.EtaleCohomology.LAdicSheaf.shriekConstantTransition`: the transition map of the
  system, the morphism corresponding to the generator at the previous level.
* `Stacks.EtaleCohomology.LAdicSheaf.shriekConstantSystem`: the ℓ-adic sheaf
  `(j_{U!}\underline{ℤ/ℓⁿ⁺¹ℤ}_U)ₙ`.
* `Stacks.EtaleCohomology.LAdicSheaf.constantSystem`: the constant ℓ-adic sheaf
  `(\underline{ℤ/ℓⁿ⁺¹ℤ})ₙ`, the system at the final object of the small étale site.

## Main results

* `AlgebraicGeometry.moduleShriekConstantSectionEquiv_apply`: a morphism out of
  `j_{U!}\underline{R}_U` corresponds to its value on the generator.
* `Stacks.EtaleCohomology.LAdicSheaf.isIso_shriekConstantReduction`: the mate of the
  transition map is an isomorphism, which is the compatibility condition of [Stacks, Tag 03UM].

## References

* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Opposite

universe u r

namespace AlgebraicGeometry

section Generator

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type r) [CommRing R]
  (U : SmallEtale B X.1 X.property)

/-- The generator of `j_{U!}\underline{R}_U`: the section over `U` of the extension by zero at
`U` of the constant free rank-one module sheaf that corresponds, under
`AlgebraicGeometry.moduleShriekConstantSectionEquiv`, to the identity morphism. -/
public def moduleShriekConstantGenerator :
    (forget (ModuleCat.{max (u + 1) r} R)).obj
      ((moduleShriekConstant.{u, r, r} B X R U).obj.obj (op U)) :=
  moduleShriekConstantSectionEquiv.{u, r, r} B X R U _ (𝟙 _)

/-- The section over `U` that `AlgebraicGeometry.moduleShriekConstantSectionEquiv` attaches to a
morphism out of `j_{U!}\underline{R}_U` is the image under it of
`AlgebraicGeometry.moduleShriekConstantGenerator`. -/
public theorem moduleShriekConstantSectionEquiv_apply
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} R))
    (g : moduleShriekConstant.{u, r, r} B X R U ⟶ F) :
    moduleShriekConstantSectionEquiv.{u, r, r} B X R U F g =
      (g.hom.app (op U)).hom (moduleShriekConstantGenerator B X R U) := by
  have h := NatTrans.naturality_apply
    (moduleShriekConstantCoyonedaIso.{u, r, r} B X R U).hom g
    (𝟙 (moduleShriekConstant.{u, r, r} B X R U))
  rwa [show (coyoneda.obj (op (moduleShriekConstant.{u, r, r} B X R U))).map g
      (𝟙 (moduleShriekConstant.{u, r, r} B X R U)) = g from Category.id_comp g] at h

/-- A morphism out of `j_{U!}\underline{R}_U` built from a section by
`AlgebraicGeometry.moduleShriekConstantSectionEquiv` carries the generator to that section. -/
private theorem moduleShriekConstantSectionEquiv_symm_generator
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} R))
    (s : (forget (ModuleCat.{max (u + 1) r} R)).obj (F.obj.obj (op U))) :
    (((moduleShriekConstantSectionEquiv.{u, r, r} B X R U F).symm s).hom.app (op U)).hom
      (moduleShriekConstantGenerator B X R U) = s := by
  rw [← moduleShriekConstantSectionEquiv_apply]
  exact (moduleShriekConstantSectionEquiv.{u, r, r} B X R U F).apply_symm_apply _

end Generator

section Final

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The final object of the small étale site of a quasi-compact scheme is quasi-compact. -/
public instance SmallEtale.compactSpace_final [CompactSpace S] :
    CompactSpace (SmallEtale.final B S hS).obj.left.obj :=
  inferInstanceAs (CompactSpace S)

/-- The final object of the small étale site of a quasi-separated scheme is
quasi-separated. -/
public instance SmallEtale.quasiSeparatedSpace_final [QuasiSeparatedSpace S] :
    QuasiSeparatedSpace (SmallEtale.final B S hS).obj.left.obj :=
  inferInstanceAs (QuasiSeparatedSpace S)

end Final

end AlgebraicGeometry

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

variable (U : SmallEtale B X.1 X.property)

/-- The level `n` sheaf of the system: the extension by zero at `U` of the constant free
rank-one `ℤ/ℓⁿ⁺¹ℤ`-module sheaf. -/
public abbrev LAdicSheaf.shriekConstantLevel (n : ℕ) : FiniteLevelSheaf.{u, u + 1} B X ℓ n :=
  moduleShriekConstant.{u, 0, 0} B X (ZMod (ℓ ^ (n + 1))) U

/-- The transition map of the system: the morphism out of the level `n + 1` sheaf into the
restriction of scalars of the level `n` sheaf whose section over `U` is the generator at level
`n`. -/
public def LAdicSheaf.shriekConstantTransition (n : ℕ) :
    LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1) ⟶
      (restrictScalarsFunctor B X ℓ n).obj (LAdicSheaf.shriekConstantLevel B X ℓ U n) :=
  (moduleShriekConstantSectionEquiv.{u, 0, 0} B X (ZMod (ℓ ^ (n + 1 + 1))) U _).symm
    (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) U)

/-- The mate of `Stacks.EtaleCohomology.LAdicSheaf.shriekConstantTransition` under the scalar
reduction/restriction adjunction, out of the scalar reduction of the level `n + 1` sheaf. -/
public def LAdicSheaf.shriekConstantReduction (n : ℕ) :
    (scalarReductionFunctor B X ℓ n).obj (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1)) ⟶
      LAdicSheaf.shriekConstantLevel B X ℓ U n :=
  ((scalarAdjunction B X ℓ n).homEquiv _ _).symm
    (LAdicSheaf.shriekConstantTransition B X ℓ U n)

/-- The section over `U` of the scalar reduction of the level `n + 1` sheaf given by the unit of
the scalar reduction/restriction adjunction. -/
public def LAdicSheaf.shriekConstantUnitSection (n : ℕ) :
    (forget (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
      (((scalarReductionFunctor B X ℓ n).obj
        (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1))).obj.obj (op U)) :=
  moduleShriekConstantSectionEquiv.{u, 0, 0} B X (ZMod (ℓ ^ (n + 1 + 1))) U _
    ((scalarAdjunction B X ℓ n).unit.app (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1)))

/-- The morphism out of the level `n` sheaf whose section over `U` is
`Stacks.EtaleCohomology.LAdicSheaf.shriekConstantUnitSection`. -/
public def LAdicSheaf.shriekConstantReductionInv (n : ℕ) :
    LAdicSheaf.shriekConstantLevel B X ℓ U n ⟶
      (scalarReductionFunctor B X ℓ n).obj
        (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1)) :=
  (moduleShriekConstantSectionEquiv.{u, 0, 0} B X (ZMod (ℓ ^ (n + 1))) U _).symm
    (LAdicSheaf.shriekConstantUnitSection B X ℓ U n)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify
    (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The transition map carries the generator at level `n + 1` to the generator at level `n`. -/
public theorem LAdicSheaf.shriekConstantTransition_generator (n : ℕ) :
    ((LAdicSheaf.shriekConstantTransition B X ℓ U n).hom.app (op U)).hom
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) U)
      = moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) U := by
  exact moduleShriekConstantSectionEquiv_symm_generator B X _ U _ _

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The unit of the scalar reduction/restriction adjunction carries the generator at level
`n + 1` to `Stacks.EtaleCohomology.LAdicSheaf.shriekConstantUnitSection`. -/
public theorem LAdicSheaf.shriekConstantUnit_generator (n : ℕ) :
    (((scalarAdjunction B X ℓ n).unit.app
        (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1))).hom.app (op U)).hom
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) U)
      = LAdicSheaf.shriekConstantUnitSection B X ℓ U n :=
  (moduleShriekConstantSectionEquiv_apply B X (ZMod (ℓ ^ (n + 1 + 1))) U _ _).symm

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- `Stacks.EtaleCohomology.LAdicSheaf.shriekConstantReductionInv` carries the generator at
level `n` to `Stacks.EtaleCohomology.LAdicSheaf.shriekConstantUnitSection`. -/
public theorem LAdicSheaf.shriekConstantReductionInv_generator (n : ℕ) :
    ((LAdicSheaf.shriekConstantReductionInv B X ℓ U n).hom.app (op U)).hom
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) U)
      = LAdicSheaf.shriekConstantUnitSection B X ℓ U n := by
  exact moduleShriekConstantSectionEquiv_symm_generator B X _ U _ _

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The mate of the transition map corresponds to the transition map under the scalar
reduction/restriction adjunction. -/
public theorem LAdicSheaf.homEquiv_shriekConstantReduction (n : ℕ) :
    (scalarAdjunction B X ℓ n).homEquiv (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1))
        (LAdicSheaf.shriekConstantLevel B X ℓ U n)
        (LAdicSheaf.shriekConstantReduction B X ℓ U n)
      = LAdicSheaf.shriekConstantTransition B X ℓ U n :=
  ((scalarAdjunction B X ℓ n).homEquiv _ _).apply_symm_apply _

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The mate of the transition map carries
`Stacks.EtaleCohomology.LAdicSheaf.shriekConstantUnitSection` to the generator at level `n`. -/
public theorem LAdicSheaf.shriekConstantReduction_unitSection (n : ℕ) :
    ((LAdicSheaf.shriekConstantReduction B X ℓ U n).hom.app (op U)).hom
        (LAdicSheaf.shriekConstantUnitSection B X ℓ U n)
      = moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) U := by
  have h := moduleShriekConstantSectionEquiv_apply B X (ZMod (ℓ ^ (n + 1 + 1))) U _
    ((scalarAdjunction B X ℓ n).unit.app
        (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1)) ≫
      (restrictScalarsFunctor B X ℓ n).map (LAdicSheaf.shriekConstantReduction B X ℓ U n))
  rw [show ((((scalarAdjunction B X ℓ n).unit.app
        (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1)) ≫
      (restrictScalarsFunctor B X ℓ n).map
        (LAdicSheaf.shriekConstantReduction B X ℓ U n))).hom.app (op U)).hom
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) U)
      = ((LAdicSheaf.shriekConstantReduction B X ℓ U n).hom.app (op U)).hom
        ((((scalarAdjunction B X ℓ n).unit.app
          (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1))).hom.app (op U)).hom
            (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) U)) from rfl,
    LAdicSheaf.shriekConstantUnit_generator, ← Adjunction.homEquiv_unit,
    LAdicSheaf.homEquiv_shriekConstantReduction] at h
  rw [← h]
  exact (moduleShriekConstantSectionEquiv.{u, 0, 0}
    B X (ZMod (ℓ ^ (n + 1 + 1))) U _).apply_symm_apply _

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The mate of the transition map of the system of extensions by zero of the constant free
rank-one module sheaves is an isomorphism, with inverse
`Stacks.EtaleCohomology.LAdicSheaf.shriekConstantReductionInv`. -/
public theorem LAdicSheaf.isIso_shriekConstantReduction (n : ℕ) :
    IsIso (LAdicSheaf.shriekConstantReduction B X ℓ U n) := by
  refine ⟨LAdicSheaf.shriekConstantReductionInv B X ℓ U n, ?_, ?_⟩
  · have hr : (scalarAdjunction B X ℓ n).homEquiv _ _
        (𝟙 ((scalarReductionFunctor B X ℓ n).obj
          (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1))))
        = (scalarAdjunction B X ℓ n).unit.app
          (LAdicSheaf.shriekConstantLevel B X ℓ U (n + 1)) := by
      rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    apply ((scalarAdjunction B X ℓ n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right,
      LAdicSheaf.homEquiv_shriekConstantReduction, hr]
    apply (moduleShriekConstantSectionEquiv.{u, 0, 0}
      B X (ZMod (ℓ ^ (n + 1 + 1))) U _).injective
    rw [moduleShriekConstantSectionEquiv_apply, moduleShriekConstantSectionEquiv_apply,
      show ((LAdicSheaf.shriekConstantTransition B X ℓ U n ≫
        (restrictScalarsFunctor B X ℓ n).map
          (LAdicSheaf.shriekConstantReductionInv B X ℓ U n)).hom.app (op U)).hom
          (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) U)
        = ((LAdicSheaf.shriekConstantReductionInv B X ℓ U n).hom.app (op U)).hom
          (((LAdicSheaf.shriekConstantTransition B X ℓ U n).hom.app (op U)).hom
            (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) U)) from rfl,
      LAdicSheaf.shriekConstantTransition_generator,
      LAdicSheaf.shriekConstantReductionInv_generator,
      LAdicSheaf.shriekConstantUnit_generator]
  · apply (moduleShriekConstantSectionEquiv.{u, 0, 0}
      B X (ZMod (ℓ ^ (n + 1))) U _).injective
    rw [moduleShriekConstantSectionEquiv_apply, moduleShriekConstantSectionEquiv_apply,
      show ((LAdicSheaf.shriekConstantReductionInv B X ℓ U n ≫
        LAdicSheaf.shriekConstantReduction B X ℓ U n).hom.app (op U)).hom
          (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) U)
        = ((LAdicSheaf.shriekConstantReduction B X ℓ U n).hom.app (op U)).hom
          (((LAdicSheaf.shriekConstantReductionInv B X ℓ U n).hom.app (op U)).hom
            (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) U)) from rfl,
      LAdicSheaf.shriekConstantReductionInv_generator,
      LAdicSheaf.shriekConstantReduction_unitSection]
    rfl

section System

variable [Fact ℓ.Prime] [IsNoetherian X.1]
  [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]

/-- The ℓ-adic sheaf of extensions by zero of the constant free rank-one module sheaves at a
quasi-compact quasi-separated étale object `U`, whose level `n` is
`j_{U!}\underline{ℤ/ℓⁿ⁺¹ℤ}_U`. -/
public def LAdicSheaf.shriekConstantSystem
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    LAdicSheaf.{u, u + 1} B X ℓ where
  level n := LAdicSheaf.shriekConstantLevel B X ℓ U n
  constructible n :=
    isConstructibleModuleSheaf_moduleShriekConstant B X (ZMod (ℓ ^ (n + 1))) U
  transition n := LAdicSheaf.shriekConstantTransition B X ℓ U n
  reduction_isIso n := LAdicSheaf.isIso_shriekConstantReduction B X ℓ U n

/-- The level `n` of `Stacks.EtaleCohomology.LAdicSheaf.shriekConstantSystem` is the extension
by zero at `U` of the constant free rank-one `ℤ/ℓⁿ⁺¹ℤ`-module sheaf. -/
@[simp]
public theorem LAdicSheaf.shriekConstantSystem_level
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] (n : ℕ) :
    (LAdicSheaf.shriekConstantSystem B X ℓ U).level n =
      moduleShriekConstant.{u, 0, 0} B X (ZMod (ℓ ^ (n + 1))) U := rfl

/-- The constant ℓ-adic sheaf: the system at the final object `X / X` of the small étale site,
whose level `n` is the constant free rank-one `ℤ/ℓⁿ⁺¹ℤ`-module sheaf. -/
public def LAdicSheaf.constantSystem : LAdicSheaf.{u, u + 1} B X ℓ :=
  LAdicSheaf.shriekConstantSystem B X ℓ (SmallEtale.final B X.1 X.property)

/-- The level `n` of `Stacks.EtaleCohomology.LAdicSheaf.constantSystem` is the extension by zero
at the final object of the small étale site of the constant free rank-one `ℤ/ℓⁿ⁺¹ℤ`-module
sheaf. -/
@[simp]
public theorem LAdicSheaf.constantSystem_level (n : ℕ) :
    (LAdicSheaf.constantSystem B X ℓ).level n =
      moduleShriekConstant.{u, 0, 0} B X (ZMod (ℓ ^ (n + 1)))
        (SmallEtale.final B X.1 X.property) := rfl

end System

end Stacks.EtaleCohomology

end
