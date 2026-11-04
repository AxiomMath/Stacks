module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.ReflexiveHullExtension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.DeRham.FiniteDifferentialsCoherent
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Specialization
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.CodimensionOneTrace
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.PurelyInseparableFibre
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.Topology.Sheaves.Stalk.PushforwardLocalIso
public import StacksFrontier.LinearAlgebra.ExteriorPower.LocalizationSupplement

/-!
# Further results on `ReflexiveHullExtension`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.ReflexiveHullExtension` that need
imports beyond those of that module.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.RelativeDifferentialStalkMap
open scoped KaehlerDifferential

universe u

namespace AlgebraicGeometry

/-- A linear map from the generic stalk of `f_*Ω^{t+1}_{Y/S}` to the generic stalk of
`Ω^{t+1}_{X/S}` which, at every point of codimension one, carries the image of the source stalk
into the image of the target stalk extends to a map of `𝒪_X`-modules
`f_*Ω^{t+1}_{Y/S} ⟶ (Ω^{t+1}_{X/S})^∨∨` in exactly one way.  Existence is the criterion of
[Stacks, Tag 0AY7]; uniqueness holds because the reflexive hull is torsion free. -/
theorem existsUnique_lift_toReflexiveHull_relativeDifferentialForms_unconditional
    {S X Y : Scheme.{u}} (p : X ⟶ S) (f : Y ⟶ X) (t : ℕ)
    [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsFinite f]
    [(Scheme.Hom.relativeDifferentialForms p ((t + 1 : ℕ) : ℤ)).IsCoherent]
    [(Scheme.Hom.relativeDifferentialForms (f ≫ p) ((t + 1 : ℕ) : ℤ)).IsCoherent]
    (T : (((Scheme.Modules.pushforward f).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ p) ((t + 1 : ℕ) : ℤ))).presheaf.stalk
            (genericPoint X)) →ₗ[X.functionField]
        ((Scheme.Hom.relativeDifferentialForms p ((t + 1 : ℕ) : ℤ)).presheaf.stalk
          (genericPoint X)))
    (hT : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      let h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
      Set.MapsTo T
        (Set.range (((Scheme.Modules.pushforward f).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ p)
            ((t + 1 : ℕ) : ℤ))).presheaf.stalkSpecializes h))
        (Set.range ((Scheme.Hom.relativeDifferentialForms p
          ((t + 1 : ℕ) : ℤ)).presheaf.stalkSpecializes h))) :
    ∃! Tr : (Scheme.Modules.pushforward f).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ p) ((t + 1 : ℕ) : ℤ)) ⟶
        reflexiveHull (Scheme.Hom.relativeDifferentialForms p ((t + 1 : ℕ) : ℤ)),
      ∀ m, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X) Tr)) m =
        ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X)
            (toReflexiveHull (Scheme.Hom.relativeDifferentialForms p
              ((t + 1 : ℕ) : ℤ))).1)) (T m) :=
  existsUnique_lift_toReflexiveHull_of_codimension_one X _ _ T hT

/-! ### The identification of the stalk of `Ω^n_{X/S}` along a specialization -/

section FormsStalkSpecialization

open Stacks.ModuleStalkSpecialization

variable {S X : Scheme.{u}}

/-- **`AlgebraicGeometry.formsStalkEquiv` restated in the spelling the comparison maps along a
specialization are stated in.**  This is `AlgebraicGeometry.formsStalkEquiv`, as a linear
equivalence over the stalk `𝒪_{X,x}`. -/
noncomputable def formsStalkEquivₗ (q : X ⟶ S) (n : ℕ) (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))] :
    letI := stalkMapAlgebra q x
    letI := stalkModule (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) x
    ((Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q)
          (n : ℤ)).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^n
        (Ω[(ToType (X.presheaf.stalk x))⁄(ToType (S.presheaf.stalk (q.base x)))])) :=
  letI := stalkMapAlgebra q x
  letI := stalkModule (Scheme.Hom.relativeDifferentials q) x
  (Scheme.Modules.exteriorPowerStalkEquivₗ (Scheme.Hom.relativeDifferentials q) n x).trans
    (extCongr n (relativeDifferentialsStalkKaehlerEquivₗ q x))

/-- `AlgebraicGeometry.formsStalkEquivₗ` is `AlgebraicGeometry.formsStalkEquiv`: the restatement
changes the spelling of the stalk and of the scalar ring, and nothing else. -/
theorem formsStalkEquivₗ_apply (q : X ⟶ S) (n : ℕ) (x : X)
    (ω : (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q)
      (n : ℤ)).presheaf.stalk x) :
    letI := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds x))
    formsStalkEquivₗ q n x ω = formsStalkEquiv q n x ω :=
  rfl

/-- **`AlgebraicGeometry.genericFormsStalkEquiv` is inverse to
`AlgebraicGeometry.formsStalkEquivₗ` at the generic point.**  Both are
`AlgebraicGeometry.formsStalkEquiv` there, read over the two spellings of the scalar ring. -/
theorem formsStalkEquivₗ_genericFormsStalkEquiv (q : X ⟶ S) [IsIntegral X] (n : ℕ) :
    letI := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds (genericPoint X)))
    ∀ ξ, formsStalkEquivₗ q n (genericPoint X) (genericFormsStalkEquiv q n ξ) = ξ :=
  fun ξ => (formsStalkEquiv q n (genericPoint X)).apply_symm_apply ξ

/-- `AlgebraicGeometry.formsStalkEquivₗ_genericFormsStalkEquiv` the other way round. -/
theorem genericFormsStalkEquiv_formsStalkEquivₗ (q : X ⟶ S) [IsIntegral X] (n : ℕ) :
    letI := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds (genericPoint X)))
    ∀ v, genericFormsStalkEquiv q n (formsStalkEquivₗ q n (genericPoint X) v) = v :=
  fun v => (formsStalkEquiv q n (genericPoint X)).symm_apply_apply v

/-- The inverse of `AlgebraicGeometry.extCongr` sends a decomposable element to the decomposable
element of the transported vectors. -/
private theorem extCongr_symm_ιMulti {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) (e : M ≃ₗ[R] N) (v : Fin n → N) :
    (extCongr n e).symm (exteriorPower.ιMulti _ n v) =
      exteriorPower.ιMulti _ n fun i ↦ e.symm (v i) :=
  exteriorPower.map_apply_ιMulti e.symm.toLinearMap v

/-- **Comparing the stalks of `Ω^n_{X/S}` along a specialization `y ⤳ x`.**  Under the
identification of `AlgebraicGeometry.formsStalkEquivₗ` at the two points, the comparison
`(Ω^n_{X/S})_x → (Ω^n_{X/S})_y` of stalks is `exteriorPower.mapTower n` of
`KaehlerDifferential.map` of the commuting square of local rings that `q` supplies.

This is the composite of the two squares the identification is composed of —
`AlgebraicGeometry.Scheme.Modules.stalkSpecializesₗ_comp_exteriorPowerStalkEquivₗ_symm` for the
exterior power and
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquivₗ_stalkSpecializes`
for the Kähler differentials — joined by `exteriorPower.map_comp_mapTower` and
`exteriorPower.mapTower_comp_map`, which turn the `mapTower` conjugated by the two
identifications back into a single `mapTower`. -/
theorem stalkSpecializesₗ_comp_formsStalkEquivₗ_symm (q : X ⟶ S) (n : ℕ) {x y : X} (h : y ⤳ x)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds y))] :
    letI := stalkMapAlgebra q x
    letI := stalkMapAlgebra q y
    letI := baseStalkSpecializesBaseAlgebra q h
    letI := stalkSpecializesAlgebra X h
    letI := baseStalkSpecializesAlgebra q h
    haveI := isScalarTower_stalkMap_stalkSpecializes q h
    haveI := isScalarTower_baseStalkSpecializes q h
    haveI := smulCommClass_stalkMap_stalkSpecializes q h
    letI := stalkModule (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) x
    letI := stalkModule (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) y
    letI := stalkSpecializesModule (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
    haveI := isScalarTower_stalkSpecializes_stalk (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
    stalkSpecializesₗ (Scheme.Modules.exteriorPower
            (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h ∘ₗ
          (formsStalkEquivₗ q n x).symm.toLinearMap =
      (formsStalkEquivₗ q n y).symm.toLinearMap.restrictScalars (X.presheaf.stalk x) ∘ₗ
        exteriorPower.mapTower (S := X.presheaf.stalk y) n
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
            (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
            (ToType (X.presheaf.stalk y))) := by
  let := stalkMapAlgebra q x
  let := stalkMapAlgebra q y
  let := baseStalkSpecializesBaseAlgebra q h
  let := stalkSpecializesAlgebra X h
  let := baseStalkSpecializesAlgebra q h
  have := isScalarTower_stalkMap_stalkSpecializes q h
  have := isScalarTower_baseStalkSpecializes q h
  have := smulCommClass_stalkMap_stalkSpecializes q h
  let := stalkModule (Scheme.Hom.relativeDifferentials q) x
  let := stalkModule (Scheme.Hom.relativeDifferentials q) y
  let := stalkSpecializesModule (Scheme.Hom.relativeDifferentials q) h
  have := isScalarTower_stalkSpecializes_stalk (Scheme.Hom.relativeDifferentials q) h
  let := stalkModule (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) x
  let := stalkModule (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) y
  let := stalkSpecializesModule (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
  have := isScalarTower_stalkSpecializes_stalk (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  show stalkSpecializesₗ (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
        ((formsStalkEquivₗ q n x).symm (exteriorPower.ιMulti _ n v)) =
    (formsStalkEquivₗ q n y).symm
      (exteriorPower.mapTower (S := X.presheaf.stalk y) n
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
          (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
          (ToType (X.presheaf.stalk y))) (exteriorPower.ιMulti _ n v))
  have hκ : ∀ ω, (relativeDifferentialsStalkKaehlerEquivₗ q y)
        (stalkSpecializesₗ (Scheme.Hom.relativeDifferentials q) h
          ((relativeDifferentialsStalkKaehlerEquivₗ q x).symm ω)) =
      KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
        (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
        (ToType (X.presheaf.stalk y)) ω :=
    LinearMap.congr_fun (relativeDifferentialsStalkKaehlerEquivₗ_stalkSpecializes q h)
  have hxsymm : (formsStalkEquivₗ q n x).symm (exteriorPower.ιMulti _ n v) =
      (Scheme.Modules.exteriorPowerStalkEquivₗ (Scheme.Hom.relativeDifferentials q) n x).symm
        (exteriorPower.ιMulti _ n fun i ↦
          (relativeDifferentialsStalkKaehlerEquivₗ q x).symm (v i)) := by
    show (Scheme.Modules.exteriorPowerStalkEquivₗ (Scheme.Hom.relativeDifferentials q) n x).symm
        ((extCongr n (relativeDifferentialsStalkKaehlerEquivₗ q x)).symm
          (exteriorPower.ιMulti _ n v)) = _
    rw [extCongr_symm_ιMulti]
  have hE : stalkSpecializesₗ (Scheme.Modules.exteriorPower
          (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
        ((Scheme.Modules.exteriorPowerStalkEquivₗ (Scheme.Hom.relativeDifferentials q) n x).symm
          (exteriorPower.ιMulti _ n fun i ↦
            (relativeDifferentialsStalkKaehlerEquivₗ q x).symm (v i))) =
      (Scheme.Modules.exteriorPowerStalkEquivₗ (Scheme.Hom.relativeDifferentials q) n y).symm
        (exteriorPower.mapTower (S := X.presheaf.stalk y) n
          (stalkSpecializesₗ (Scheme.Hom.relativeDifferentials q) h)
          (exteriorPower.ιMulti _ n fun i ↦
            (relativeDifferentialsStalkKaehlerEquivₗ q x).symm (v i))) :=
    LinearMap.congr_fun (Scheme.Modules.stalkSpecializesₗ_comp_exteriorPowerStalkEquivₗ_symm
      (Scheme.Hom.relativeDifferentials q) n h) _
  have hbottom : exteriorPower.mapTower (S := X.presheaf.stalk y) n
          (stalkSpecializesₗ (Scheme.Hom.relativeDifferentials q) h)
          (exteriorPower.ιMulti _ n fun i ↦
            (relativeDifferentialsStalkKaehlerEquivₗ q x).symm (v i)) =
      (extCongr n (relativeDifferentialsStalkKaehlerEquivₗ q y)).symm
        (exteriorPower.mapTower (S := X.presheaf.stalk y) n
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
            (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
            (ToType (X.presheaf.stalk y))) (exteriorPower.ιMulti _ n v)) := by
    rw [exteriorPower.mapTower_ιMulti, exteriorPower.mapTower_ιMulti, extCongr_symm_ιMulti]
    refine congrArg (exteriorPower.ιMulti _ n) (funext fun i ↦ ?_)
    show stalkSpecializesₗ (Scheme.Hom.relativeDifferentials q) h
        ((relativeDifferentialsStalkKaehlerEquivₗ q x).symm (v i)) =
      (relativeDifferentialsStalkKaehlerEquivₗ q y).symm
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
          (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
          (ToType (X.presheaf.stalk y)) (v i))
    rw [← hκ (v i), LinearEquiv.symm_apply_apply]
  rw [hxsymm, hE, hbottom]
  rfl

/-- **The image of the stalk of `Ω^n_{X/S}` at `x` inside the stalk at `y`, read through the
identification of `AlgebraicGeometry.formsStalkEquivₗ`.**  For `y ⤳ x` the identification at `y`
carries the image of `(Ω^n_{X/S})_x` onto the image of `exteriorPower.mapTower n` of
`KaehlerDifferential.map` of the square of local rings. -/
theorem formsStalkEquivₗ_image_range_stalkSpecializes (q : X ⟶ S) (n : ℕ) {x y : X} (h : y ⤳ x)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds y))] :
    letI := stalkMapAlgebra q x
    letI := stalkMapAlgebra q y
    letI := baseStalkSpecializesBaseAlgebra q h
    letI := stalkSpecializesAlgebra X h
    letI := baseStalkSpecializesAlgebra q h
    haveI := isScalarTower_stalkMap_stalkSpecializes q h
    haveI := isScalarTower_baseStalkSpecializes q h
    haveI := smulCommClass_stalkMap_stalkSpecializes q h
    letI := stalkModule (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) y
    formsStalkEquivₗ q n y ''
          Set.range ((Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q)
            (n : ℤ)).presheaf.stalkSpecializes h) =
      Set.range (exteriorPower.mapTower (S := X.presheaf.stalk y) n
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
          (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
          (ToType (X.presheaf.stalk y)))) := by
  let := stalkMapAlgebra q x
  let := stalkMapAlgebra q y
  let := baseStalkSpecializesBaseAlgebra q h
  let := stalkSpecializesAlgebra X h
  let := baseStalkSpecializesAlgebra q h
  have := isScalarTower_stalkMap_stalkSpecializes q h
  have := isScalarTower_baseStalkSpecializes q h
  have := smulCommClass_stalkMap_stalkSpecializes q h
  let := stalkModule (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) x
  let := stalkModule (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) y
  let := stalkSpecializesModule (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
  have := isScalarTower_stalkSpecializes_stalk (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
  have key (ξ : ⋀[X.presheaf.stalk x]^n
      (Ω[(ToType (X.presheaf.stalk x))⁄(ToType (S.presheaf.stalk (q.base x)))])) :
      formsStalkEquivₗ q n y
          (stalkSpecializesₗ (Scheme.Modules.exteriorPower
            (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
              ((formsStalkEquivₗ q n x).symm ξ)) =
        exteriorPower.mapTower (S := X.presheaf.stalk y) n
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
            (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
            (ToType (X.presheaf.stalk y))) ξ := by
    have hsq : stalkSpecializesₗ (Scheme.Modules.exteriorPower
          (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
            ((formsStalkEquivₗ q n x).symm ξ) =
        (formsStalkEquivₗ q n y).symm
          (exteriorPower.mapTower (S := X.presheaf.stalk y) n
            (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
              (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
              (ToType (X.presheaf.stalk y))) ξ) :=
      LinearMap.congr_fun (stalkSpecializesₗ_comp_formsStalkEquivₗ_symm q n h) ξ
    rw [hsq, LinearEquiv.apply_symm_apply]
  rw [← Scheme.Modules.range_stalkSpecializesₗ (Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h]
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro - ⟨-, ⟨ω, rfl⟩, rfl⟩
    refine ⟨formsStalkEquivₗ q n x ω, ?_⟩
    rw [← key, LinearEquiv.symm_apply_apply]
  · rintro - ⟨ξ, rfl⟩
    exact ⟨stalkSpecializesₗ (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials q) (n : ℤ)) h
        ((formsStalkEquivₗ q n x).symm ξ), ⟨_, rfl⟩, key ξ⟩

end FormsStalkSpecialization

/-! ### The generic stalk of a finite direct image -/

/-- **The fibre of a finite dominant morphism over the generic point of the target is the
generic point of the source.**  The fibre of a finite morphism is a discrete subspace, and the
generic point of the source specializes to every point of the source, so a second point of the
fibre would be a proper specialization inside a discrete space. -/
theorem preimage_genericPoint_of_isFinite {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsFinite f] [IsDominant f] :
    f ⁻¹' {genericPoint X} = {genericPoint Y} := by
  have hmem : genericPoint Y ∈ f ⁻¹' {genericPoint X} := map_genericPoint_of_isDominant f
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun y hy => ?_⟩
  have hdisc : DiscreteTopology ↥(f ⁻¹' {genericPoint X}) :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (genericPoint X))
  have hsp : (⟨genericPoint Y, hmem⟩ : ↥(f ⁻¹' {genericPoint X})) ⤳ ⟨y, hy⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp (genericPoint_specializes y)
  exact (congrArg Subtype.val (specializes_iff_eq.mp hsp)).symm

/-- The image of the generic point of the source of a dominant morphism of irreducible schemes,
read as a generalization of the generic point of the target: the equality
`AlgebraicGeometry.map_genericPoint_of_isDominant` as a specialization. -/
theorem specializes_genericPoint_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f] :
    f.base (genericPoint Y) ⤳ genericPoint X :=
  (Inseparable.of_eq (map_genericPoint_of_isDominant f)).le

/-- **The comparison map on stalks of a direct image at a point with a one-point fibre is a
linear equivalence.**  Invertibility is
`TopCat.Presheaf.isIso_stalkPushforward_of_exists_preimage_le`, whose hypothesis is supplied by
`AlgebraicGeometry.exists_open_preimage_le`; additivity and semilinearity over the stalk map of
`f` are `Stacks.Chow.stalkPushforwardComparison_add` and
`Stacks.Chow.stalkPushforwardComparison_smul`. -/
noncomputable def pushforwardStalkEquivOfPreimageSingleton {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] (G : Y.Modules) (y : Y) (hfiber : f ⁻¹' {f.base y} = {y}) :
    letI : Module (X.presheaf.stalk (f.base y)) (G.presheaf.stalk y) :=
      Module.compHom _ (f.stalkMap y).hom
    ((Scheme.Modules.pushforward f).obj G).presheaf.stalk (f.base y)
      ≃ₗ[X.presheaf.stalk (f.base y)] G.presheaf.stalk y :=
  letI : Module (X.presheaf.stalk (f.base y)) (G.presheaf.stalk y) :=
    Module.compHom _ (f.stalkMap y).hom
  have _ : IsIso (TopCat.Presheaf.stalkPushforward Ab.{u} f.base G.val.presheaf y) :=
    TopCat.Presheaf.isIso_stalkPushforward_of_exists_preimage_le _ _ _ fun W hW =>
      exists_open_preimage_le f y (f.base y) rfl hfiber W hW
  have hbij : Function.Bijective (Stacks.Chow.stalkPushforwardComparison f G y) :=
    let hb := ConcreteCategory.bijective_of_isIso
      (TopCat.Presheaf.stalkPushforward Ab.{u} f.base G.val.presheaf y)
    ⟨fun _ _ hab => hb.1 hab, fun c => hb.2 c⟩
  { toFun := Stacks.Chow.stalkPushforwardComparison f G y
    map_add' := Stacks.Chow.stalkPushforwardComparison_add f G y
    map_smul' := Stacks.Chow.stalkPushforwardComparison_smul f G y
    invFun := Function.surjInv hbij.2
    left_inv := Function.leftInverse_surjInv hbij
    right_inv := Function.rightInverse_surjInv hbij.2 }

/-- **The comparison map on stalks of a direct image at a point with a one-point fibre is
bijective.**  This is the content of
`AlgebraicGeometry.pushforwardStalkEquivOfPreimageSingleton` before the module structures are
put on it. -/
theorem bijective_stalkPushforwardComparison_of_preimage_singleton {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] (G : Y.Modules) (y : Y) (hfiber : f ⁻¹' {f.base y} = {y}) :
    Function.Bijective (Stacks.Chow.stalkPushforwardComparison f G y) :=
  (pushforwardStalkEquivOfPreimageSingleton f G y hfiber).bijective

/-- **The comparison map on stalks of a direct image is compatible with specialization.**  For
`y' ⤳ y` on `Y`, the square whose two horizontal edges are the comparison maps
`(f_*G)_{f y} → G_y` and `(f_*G)_{f y'} → G_{y'}` of
`Stacks.Chow.stalkPushforwardComparison` and whose two vertical edges are the comparisons along
`y' ⤳ y` and along its image `f y' ⤳ f y` commutes: both routes send the germ at `f y` of a
section `t` of `f_*G` over `U` to the germ of `t` at `y'`, read as a section of `G` over
`f ⁻¹ᵁ U`.

This is the square for a direct image that
`AlgebraicGeometry.stalkSpecializesₗ_comp_formsStalkEquivₗ_symm` is for a module on `X`. -/
theorem stalkPushforwardComparison_stalkSpecializes {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Y.Modules) {y y' : Y} (h : y' ⤳ y)
    (s : ((Scheme.Modules.pushforward f).obj G).presheaf.stalk (f.base y)) :
    Stacks.Chow.stalkPushforwardComparison f G y'
        (((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes
          (f.base.hom.map_specializes h) s) =
      G.presheaf.stalkSpecializes h (Stacks.Chow.stalkPushforwardComparison f G y s) := by
  obtain ⟨U, hU, t, rfl⟩ := ((Scheme.Modules.pushforward f).obj G).presheaf.exists_germ_eq s
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply,
    Stacks.Chow.stalkPushforwardComparison_germ, Stacks.Chow.stalkPushforwardComparison_germ]
  exact (TopCat.Presheaf.germ_stalkSpecializes_apply G.presheaf hU h t).symm

/-- **The image of the stalk of `f_*G` at `f y` inside the stalk at `f y'`, read on `Y`.**  For
`y' ⤳ y` and a one-point fibre over `f y`, the comparison map at `y'` carries the image of
`(f_*G)_{f y}` in `(f_*G)_{f y'}` onto the image of `G_y` in `G_{y'}`. -/
theorem stalkPushforwardComparison_image_range_stalkSpecializes {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] (G : Y.Modules) {y y' : Y} (h : y' ⤳ y)
    (hfiber : f ⁻¹' {f.base y} = {y}) :
    Stacks.Chow.stalkPushforwardComparison f G y' ''
          Set.range (((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes
            (f.base.hom.map_specializes h)) =
      Set.range (G.presheaf.stalkSpecializes h) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro - ⟨-, ⟨s, rfl⟩, rfl⟩
    exact ⟨Stacks.Chow.stalkPushforwardComparison f G y s,
      (stalkPushforwardComparison_stalkSpecializes f G h s).symm⟩
  · rintro - ⟨u, rfl⟩
    obtain ⟨s, rfl⟩ :=
      (bijective_stalkPushforwardComparison_of_preimage_singleton f G y hfiber).2 u
    exact ⟨_, ⟨s, rfl⟩, stalkPushforwardComparison_stalkSpecializes f G h s⟩

/-- The point `(f ≫ q) η_Y` of `S` is a generalization of `q η_X`: for `f` dominant the two
points are equal, and this is that equality in the form the comparison maps on stalks of `S`
are indexed by. -/
theorem specializes_genericPoint_comp {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f] :
    (f ≫ q).base (genericPoint Y) ⤳ q.base (genericPoint X) :=
  q.base.hom.map_specializes (specializes_genericPoint_map f)

/-- **The generic stalk of the direct image of a module along a finite dominant morphism is the
generic stalk of the module**, linearly over the function field of the target acting through
`AlgebraicGeometry.functionFieldMap`.  The fibre over the generic point is a single point by
`AlgebraicGeometry.preimage_genericPoint_of_isFinite`, so the comparison map of
`AlgebraicGeometry.pushforwardStalkEquivOfPreimageSingleton` applies there; the generic stalk on
`X` is carried to that point by the specialization comparison, invertible because the two points
are equal. -/
noncomputable def genericPushforwardStalkEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsFinite f] [IsDominant f] (G : Y.Modules) :
    letI : Module ↑X.functionField (G.presheaf.stalk (genericPoint Y)) :=
      Module.compHom _ (functionFieldMap f)
    ((Scheme.Modules.pushforward f).obj G).presheaf.stalk (genericPoint X)
      ≃ₗ[↑X.functionField] G.presheaf.stalk (genericPoint Y) :=
  letI : Module ↑X.functionField (G.presheaf.stalk (genericPoint Y)) :=
    Module.compHom _ (functionFieldMap f)
  have hfib : f ⁻¹' {f.base (genericPoint Y)} = {genericPoint Y} := by
    rw [show f.base (genericPoint Y) = genericPoint X from map_genericPoint_of_isDominant f]
    exact preimage_genericPoint_of_isFinite f
  let E := pushforwardStalkEquivOfPreimageSingleton f G (genericPoint Y) hfib
  let σ := ((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes
    (specializes_genericPoint_map f)
  have hσ : IsIso σ := by
    have hcongr : σ = (((Scheme.Modules.pushforward f).obj G).presheaf.stalkCongr
        (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom := rfl
    rw [hcongr]
    infer_instance
  have hbij : Function.Bijective (fun s => E (σ s)) :=
    E.bijective.comp (ConcreteCategory.bijective_of_isIso σ)
  LinearEquiv.ofBijective
    ({ toFun := fun s => E (σ s)
       map_add' := fun a b => by simp
       map_smul' := fun r s => by
         change E (σ (r • s)) = _
         rw [Stacks.ModuleStalkSpecialization.stalkSpecializes_smul, E.map_smul]
         rfl } : _ →ₗ[↑X.functionField] _) hbij

/-- **The image of the stalk of `f_*G` at `f y` inside the generic stalk, read on `Y`.**  The
identification `AlgebraicGeometry.genericPushforwardStalkEquiv` of the generic stalk of `f_*G`
with the generic stalk of `G` carries the image of `(f_*G)_{f y}` into the image of `G_y`. -/
theorem genericPushforwardStalkEquiv_image_range_stalkSpecializes {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsFinite f] [IsDominant f] (G : Y.Modules) (y : Y)
    (h : genericPoint X ⤳ f.base y) :
    genericPushforwardStalkEquiv f G ''
        Set.range (((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes h) ⊆
      Set.range (G.presheaf.stalkSpecializes (genericPoint_specializes y)) := by
  rintro - ⟨-, ⟨s, rfl⟩, rfl⟩
  refine ⟨Stacks.Chow.stalkPushforwardComparison f G y s, ?_⟩
  have hkey : genericPushforwardStalkEquiv f G
        (((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes h s) =
      Stacks.Chow.stalkPushforwardComparison f G (genericPoint Y)
        (((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes
          (f.base.hom.map_specializes (genericPoint_specializes y)) s) := by
    show Stacks.Chow.stalkPushforwardComparison f G (genericPoint Y)
        (((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes
          (specializes_genericPoint_map f)
            (((Scheme.Modules.pushforward f).obj G).presheaf.stalkSpecializes h s)) = _
    congr 1
    obtain ⟨U, hU, t, rfl⟩ := ((Scheme.Modules.pushforward f).obj G).presheaf.exists_germ_eq s
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply,
      TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [hkey, stalkPushforwardComparison_stalkSpecializes f G (genericPoint_specializes y) s]

/-- `𝒪_{S,(f ≫ q) η_Y}` as an algebra over `𝒪_{S,q η_X}`, through the comparison of stalks of
`S` along `AlgebraicGeometry.specializes_genericPoint_comp`. -/
noncomputable abbrev genericBaseStalkAlgebra {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) :=
  (S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f)).hom.toAlgebra

/-- The function field of `Y` as an algebra over `𝒪_{S,q η_X}`, through the stalk map of `f ≫ q`
at the generic point of `Y`.  This is the base ring `Λ` of the source's `Ω^i_{L/Λ}`: the local
ring of `S` below the generic point of `X`. -/
noncomputable abbrev genericBaseFunctionFieldAlgebra {S X Y : Scheme.{u}} (q : X ⟶ S)
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑Y.functionField :=
  (S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f) ≫
    (f ≫ q).stalkMap (genericPoint Y)).hom.toAlgebra

/-- **`Ω_{L/Λ}` does not depend on which of the two equal points of `S` the base ring is the
stalk at.**  The comparison `𝒪_{S,q η_X} ⟶ 𝒪_{S,(f ≫ q) η_Y}` is an isomorphism, the two points
being equal, so the change-of-base map of Kähler differentials is a linear equivalence by
`Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective`. -/
noncomputable def genericKaehlerBaseEquiv {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    letI := genericBaseFunctionFieldAlgebra q f
    letI : Algebra (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
      ↑Y.functionField := algebraStalkMap (f ≫ q) (genericPoint Y)
    (Ω[↑Y.functionField⁄ToType (S.presheaf.stalk (q.base (genericPoint X)))])
      ≃ₗ[↑Y.functionField]
      (Ω[↑Y.functionField⁄ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))]) :=
  letI := genericBaseStalkAlgebra q f
  letI := genericBaseFunctionFieldAlgebra q f
  letI : Algebra (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
      ↑Y.functionField := algebraStalkMap (f ≫ q) (genericPoint Y)
  haveI : IsScalarTower (ToType (S.presheaf.stalk (q.base (genericPoint X))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) ↑Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsurj : Function.Surjective (algebraMap
      (ToType (S.presheaf.stalk (q.base (genericPoint X))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))) := by
    have hiso : IsIso (S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f)) := by
      have hcongr : S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f) =
          (S.presheaf.stalkCongr (Inseparable.of_eq
            (congrArg q.base (map_genericPoint_of_isDominant f)).symm)).hom := rfl
      rw [hcongr]
      exact Iso.isIso_hom _
    exact (ConcreteCategory.bijective_of_isIso
      (S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f))).2
  Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective _ _ _ hsurj

/-- `AlgebraicGeometry.genericKaehlerBaseEquiv` is the change-of-base map
`KaehlerDifferential.map` of the comparison `𝒪_{S,q η_X} ⟶ 𝒪_{S,(f ≫ q) η_Y}` and nothing else.

Together with `KaehlerDifferential.map_base_comp_map` this is what identifies a form on `Y`
pulled back from a local ring, read over the stalk of `S` below the point of `Y`, with the same
form read over the stalk of `S` below its image in `X`. -/
theorem genericKaehlerBaseEquiv_apply {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    letI := genericBaseStalkAlgebra q f
    letI := genericBaseFunctionFieldAlgebra q f
    letI : Algebra (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
      ↑Y.functionField := algebraStalkMap (f ≫ q) (genericPoint Y)
    haveI : IsScalarTower (ToType (S.presheaf.stalk (q.base (genericPoint X))))
        (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) ↑Y.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∀ ω : Ω[↑Y.functionField⁄ToType (S.presheaf.stalk (q.base (genericPoint X)))],
      genericKaehlerBaseEquiv q f ω =
        KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (genericPoint X))))
          (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) ↑Y.functionField
          ↑Y.functionField ω :=
  fun _ => rfl

/-- **The generic stalk of `f_*Ω^n_{Y/S}` is `⋀ⁿ Ω_{L/Λ}`**, for `L` the function field of `Y`
and `Λ` the local ring of `S` below the generic point of `X`.  This is the identification of the
source of the trace map of [Stacks, Tag 0AX5] with the generic stalk of the direct image: the
generic stalk of the direct image is the generic stalk of `Ω^n_{Y/S}` by
`AlgebraicGeometry.genericPushforwardStalkEquiv`, that stalk is `⋀ⁿ Ω_{L/Λ'}` for `Λ'` the stalk
of `S` at `(f ≫ q) η_Y` by `AlgebraicGeometry.genericFormsStalkEquiv`, and `Λ' = Λ` by
`AlgebraicGeometry.genericKaehlerBaseEquiv`. -/
noncomputable def genericPushforwardFormsEquiv {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X)
    (n : ℕ) [IsIntegral X] [IsIntegral Y] [IsFinite f] [IsDominant f] :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
      algebraStalkMap q (genericPoint X)
    letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
    letI := genericBaseFunctionFieldAlgebra q f
    (⋀[↑Y.functionField]^n
        (Ω[↑Y.functionField⁄ToType (S.presheaf.stalk (q.base (genericPoint X)))]))
      ≃ₗ[↑X.functionField]
      ↑(((Scheme.Modules.pushforward f).obj
        (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((n : ℕ) : ℤ))).presheaf.stalk
          (genericPoint X)) :=
  letI : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
    algebraStalkMap q (genericPoint X)
  letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
  letI := genericBaseFunctionFieldAlgebra q f
  letI : Algebra (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
      ↑Y.functionField := algebraStalkMap (f ≫ q) (genericPoint Y)
  let Φ := (extCongr n (genericKaehlerBaseEquiv q f)).trans
    (genericFormsStalkEquiv (f ≫ q) n)
  let Ψ := genericPushforwardStalkEquiv f
    (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((n : ℕ) : ℤ))
  LinearEquiv.ofBijective
    ({ toFun := fun w => Ψ.symm (Φ w)
       map_add' := fun a b => by simp
       map_smul' := fun r w => by
         rw [← IsScalarTower.algebraMap_smul (↑Y.functionField) r w, Φ.map_smul]
         exact Ψ.symm.map_smul r (Φ w) } : _ →ₗ[↑X.functionField] _)
    (Ψ.symm.bijective.comp Φ.bijective)

/-- **`AlgebraicGeometry.genericPushforwardFormsEquiv` unfolded.**  It is the identification
`AlgebraicGeometry.genericFormsStalkEquiv` of the generic stalk of `Ω^n_{Y/S}`, preceded by the
transport `AlgebraicGeometry.genericKaehlerBaseEquiv` of the base ring and followed by the
identification `AlgebraicGeometry.genericPushforwardStalkEquiv` of the generic stalk of the
direct image. -/
theorem genericPushforwardFormsEquiv_apply {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X) (n : ℕ)
    [IsIntegral X] [IsIntegral Y] [IsFinite f] [IsDominant f] :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
      algebraStalkMap q (genericPoint X)
    letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
    letI := genericBaseFunctionFieldAlgebra q f
    letI : Algebra (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
        ↑Y.functionField := algebraStalkMap (f ≫ q) (genericPoint Y)
    ∀ ω, genericPushforwardFormsEquiv q f n ω =
      (genericPushforwardStalkEquiv f
          (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((n : ℕ) : ℤ))).symm
        (genericFormsStalkEquiv (f ≫ q) n
          (exteriorPower.map n (genericKaehlerBaseEquiv q f).toLinearMap ω)) :=
  fun _ => rfl

/-- The scalar tower `𝒪_{S,q η_X} → K → L` at the generic point: the stalk map of `f ≫ q` at the
generic point of `Y` is the stalk map of `q` at the generic point of `X` followed by that of `f`,
once the stalks of `S` at the two equal points `(f ≫ q) η_Y` and `q η_X` are compared. -/
theorem isScalarTower_genericBaseFunctionField {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
      algebraStalkMap q (genericPoint X)
    letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
    letI := genericBaseFunctionFieldAlgebra q f
    IsScalarTower (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField
      ↑Y.functionField := by
  let : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
    algebraStalkMap q (genericPoint X)
  let : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
  let := genericBaseFunctionFieldAlgebra q f
  have h2 := q.stalkSpecializes_stalkMap (f.base (genericPoint Y)) (genericPoint X)
    (specializes_genericPoint_map f)
  have hc : (f ≫ q).stalkMap (genericPoint Y) =
      q.stalkMap (f.base (genericPoint Y)) ≫ f.stalkMap (genericPoint Y) :=
    Scheme.Hom.stalkMap_comp f q (genericPoint Y)
  have key : S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f) ≫
      (f ≫ q).stalkMap (genericPoint Y) =
      q.stalkMap (genericPoint X) ≫ X.presheaf.stalkSpecializes
        (specializes_genericPoint_map f) ≫ f.stalkMap (genericPoint Y) :=
    calc S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f) ≫
          (f ≫ q).stalkMap (genericPoint Y)
        = S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f) ≫
            q.stalkMap (f.base (genericPoint Y)) ≫ f.stalkMap (genericPoint Y) :=
          congrArg (fun g => S.presheaf.stalkSpecializes
            (specializes_genericPoint_comp q f) ≫ g) hc
      _ = (S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f) ≫
            q.stalkMap (f.base (genericPoint Y))) ≫ f.stalkMap (genericPoint Y) :=
          (Category.assoc _ _ _).symm
      _ = (q.stalkMap (genericPoint X) ≫ X.presheaf.stalkSpecializes
            (specializes_genericPoint_map f)) ≫ f.stalkMap (genericPoint Y) :=
          congrArg (fun g => g ≫ f.stalkMap (genericPoint Y)) h2
      _ = _ := Category.assoc _ _ _
  exact IsScalarTower.of_algebraMap_eq fun x => congrArg (fun g => g.hom x) key

/-- The stalk map of `F` at a point, compared along `y' ⤳ y`, is the stalk map at `y'` after the
comparison along `F y' ⤳ x ⤳ F y` through any intermediate point `x`. -/
private theorem stalkSpecializes_stalkMap_apply_of_specializes_trans {X Y : Scheme.{u}}
    (F : Y ⟶ X) {y' y : Y} (hy : y' ⤳ y) {x : X} (h₁ : x ⤳ F.base y) (h₂ : F.base y' ⤳ x)
    (z : X.presheaf.stalk (F.base y)) :
    (Y.presheaf.stalkSpecializes hy).hom ((F.stalkMap y).hom z) =
      (F.stalkMap y').hom ((X.presheaf.stalkSpecializes h₂).hom
        ((X.presheaf.stalkSpecializes h₁).hom z)) := by
  exact (Scheme.Hom.stalkSpecializes_stalkMap_apply F y' y hy z).symm.trans
    (congrArg (F.stalkMap y').hom
      (congrArg (fun g => g.hom z) (TopCat.Presheaf.stalkSpecializes_comp X.presheaf h₂ h₁)).symm)

/-! ### The codimension-one condition -/

/-- **The trace map preserves the stalks at points of codimension one** (third paragraph of the
proof of [Stacks, Tag 0AX6]).  At a point `x` of `X` of codimension one the trace map of
[Stacks, Tag 0AX5], read through the identifications
`AlgebraicGeometry.genericPushforwardFormsEquiv` and
`AlgebraicGeometry.genericFormsStalkEquiv` of the two generic stalks, carries the image of the
stalk of `f_*Ω^{t+1}_{Y/S}` at `x` into the image of the stalk of `Ω^{t+1}_{X/S}` at `x`. -/
theorem higherTrace_mapsTo_range_stalkSpecializes {S X Y : Scheme.{u}} (q : X ⟶ S) (f : Y ⟶ X)
    {p t : ℕ} (hp : p.Prime)
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsNormal X] [IsFinite f] [IsDominant f]
    [CharP (ToType (S.presheaf.stalk (q.base (genericPoint X)))) p] :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
      algebraStalkMap q (genericPoint X)
    letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
    letI := genericBaseFunctionFieldAlgebra q f
    haveI := isScalarTower_genericBaseFunctionField q f
    ∀ (a : ↑X.functionField)
      (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[↑X.functionField]
        ↑Y.functionField)
      (x : X), ringKrullDim (X.presheaf.stalk x) = 1 →
      let h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
      Set.MapsTo ((genericFormsStalkEquiv q (t + 1)).toLinearMap ∘ₗ
          (KaehlerDifferential.higherTrace hp a e).comp
            (genericPushforwardFormsEquiv q f (t + 1)).symm.toLinearMap)
        (Set.range (((Scheme.Modules.pushforward f).obj
          (Scheme.Hom.relativeDifferentialForms (f ≫ q)
            ((t + 1 : ℕ) : ℤ))).presheaf.stalkSpecializes h))
        (Set.range ((Scheme.Hom.relativeDifferentialForms q
          ((t + 1 : ℕ) : ℤ)).presheaf.stalkSpecializes h)) := by
  let : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
    algebraStalkMap q (genericPoint X)
  let : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
  let := genericBaseFunctionFieldAlgebra q f
  have := isScalarTower_genericBaseFunctionField q f
  intro a e x hdim
  have : CharP ↑X.functionField p :=
    charP_of_natCast_eq_zero hp (natCast_eq_zero_of_charP
      (Λ := ToType (S.presheaf.stalk (q.base (genericPoint X)))) p)
  have : CharP ↑Y.functionField p :=
    charP_of_natCast_eq_zero hp (natCast_eq_zero_of_charP (Λ := ↑X.functionField) p)
  obtain ⟨y, hfib⟩ := exists_preimage_singleton_of_algEquiv_adjoinRoot f hp
    (CharP.cast_eq_zero _ p) a e x
  have hfy : f.base y = x := by
    have hm : y ∈ f ⁻¹' {x} := by rw [hfib]; rfl
    exact hm
  subst hfy
  intro h
  have hy : genericPoint Y ⤳ y := genericPoint_specializes y
  let := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds (genericPoint X)))
  let := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds (f.base y)))
  let := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds (genericPoint Y)))
  let := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds y))
  -- the local ring at the codimension-one point is a discrete valuation ring
  have hco : Order.coheight (f.base y) = 1 := by
    have h0 := (ringKrullDim_stalk_eq_coheight (f.base y)).symm.trans hdim
    exact_mod_cast h0
  have : IsDiscreteValuationRing (ToType (X.presheaf.stalk (f.base y))) :=
    isDiscreteValuationRing_stalk_of_coheight_eq_one hco
  -- the square of local rings at `(x, y)` and at the two generic points
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (X.presheaf.stalk (f.base y))) := stalkMapAlgebra q (f.base y)
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (Y.presheaf.stalk y)) := stalkMapAlgebra (f ≫ q) y
  let : Algebra (ToType (X.presheaf.stalk (f.base y))) (ToType (Y.presheaf.stalk y)) :=
    stalkMapAlgebra f y
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (S.presheaf.stalk (q.base (genericPoint X)))) :=
    baseStalkSpecializesBaseAlgebra q h
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base y)))) ↑X.functionField :=
    baseStalkSpecializesAlgebra q h
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base y)))) ↑Y.functionField :=
    baseStalkSpecializesAlgebra (f ≫ q) hy
  let : Algebra (ToType (X.presheaf.stalk (f.base y))) ↑Y.functionField :=
    baseStalkSpecializesAlgebra f hy
  let : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) := genericBaseStalkAlgebra q f
  let : Algebra (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
      ↑Y.functionField := algebraStalkMap (f ≫ q) (genericPoint Y)
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) :=
    baseStalkSpecializesBaseAlgebra (f ≫ q) hy
  -- the towers the square supplies
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (X.presheaf.stalk (f.base y))) ↑X.functionField :=
    isScalarTower_stalkMap_stalkSpecializes q h
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
    isScalarTower_baseStalkSpecializes q h
  have : IsScalarTower (ToType (X.presheaf.stalk (f.base y))) (ToType (Y.presheaf.stalk y))
      ↑Y.functionField := isScalarTower_stalkMap_stalkSpecializes f hy
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (Y.presheaf.stalk y)) ↑Y.functionField :=
    isScalarTower_stalkMap_stalkSpecializes (f ≫ q) hy
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) ↑Y.functionField :=
    isScalarTower_baseStalkSpecializes (f ≫ q) hy
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (genericPoint X))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) ↑Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the comparisons of stalks of `S` and of `X` along the two specializations compose
  have hScomp : S.presheaf.stalkSpecializes (q.base.hom.map_specializes h) ≫
        S.presheaf.stalkSpecializes (specializes_genericPoint_comp q f) =
      S.presheaf.stalkSpecializes ((f ≫ q).base.hom.map_specializes hy) :=
    TopCat.Presheaf.stalkSpecializes_comp S.presheaf (specializes_genericPoint_comp q f)
      (q.base.hom.map_specializes h)
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (S.presheaf.stalk (q.base (genericPoint X))))
      (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y)))) :=
    IsScalarTower.of_algebraMap_eq fun w =>
      (congrArg (fun g => CommRingCat.Hom.hom g w) hScomp).symm
  have : IsScalarTower (ToType (X.presheaf.stalk (f.base y))) ↑X.functionField
      ↑Y.functionField := IsScalarTower.of_algebraMap_eq
    (stalkSpecializes_stalkMap_apply_of_specializes_trans f hy h (specializes_genericPoint_map f))
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑Y.functionField :=
    IsScalarTower.of_algebraMap_eq
      (stalkSpecializes_stalkMap_apply_of_specializes_trans (f ≫ q) hy
        (q.base.hom.map_specializes h) (specializes_genericPoint_comp q f))
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (X.presheaf.stalk (f.base y))) ↑Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun w => by
    show (Y.presheaf.stalkSpecializes hy).hom (((f ≫ q).stalkMap y).hom w) =
      (Y.presheaf.stalkSpecializes hy).hom
        ((f.stalkMap y).hom ((q.stalkMap (f.base y)).hom w))
    exact congrArg (fun z => (Y.presheaf.stalkSpecializes hy).hom z)
      (congrArg (fun g => CommRingCat.Hom.hom g w) (Scheme.Hom.stalkMap_comp f q y))
  have : IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base y))))
      (ToType (X.presheaf.stalk (f.base y))) (ToType (Y.presheaf.stalk y)) :=
    IsScalarTower.of_algebraMap_eq fun w =>
      congrArg (fun g => CommRingCat.Hom.hom g w) (Scheme.Hom.stalkMap_comp f q y)
  -- module-finiteness above, and the function fields purely inseparable of degree `p`
  have : Module.Finite (ToType (X.presheaf.stalk (f.base y))) (ToType (Y.presheaf.stalk y)) :=
    RingHom.finite_algebraMap.mp (finite_stalkMap_of_preimage_singleton f y hfib)
  have : ExpChar ↑X.functionField p := ExpChar.prime hp
  have : IsPurelyInseparable ↑X.functionField ↑Y.functionField :=
    (isPurelyInseparable_iff_pow_mem (↑X.functionField) p).mpr fun z =>
      ⟨1, by simpa using pow_mem_range_of_algEquiv_adjoinRoot hp a e z⟩
  have hdegree : Module.finrank (↑X.functionField) (↑Y.functionField) = p := by
    rw [← LinearEquiv.finrank_eq e.toLinearEquiv,
      (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C a hp.pos.ne')).finrank,
      AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]
  -- the assembly
  intro u hu
  have hpush : genericPushforwardStalkEquiv f
        (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((t + 1 : ℕ) : ℤ)) u ∈
      Set.range ((Scheme.Hom.relativeDifferentialForms (f ≫ q)
        ((t + 1 : ℕ) : ℤ)).presheaf.stalkSpecializes hy) :=
    genericPushforwardStalkEquiv_image_range_stalkSpecializes f _ y h ⟨u, hu, rfl⟩
  have hYrange : formsStalkEquivₗ (f ≫ q) (t + 1) (genericPoint Y) ''
        Set.range ((Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (f ≫ q))
          ((t + 1 : ℕ) : ℤ)).presheaf.stalkSpecializes hy) =
      Set.range (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
          (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
          (ToType (Y.presheaf.stalk y)) ↑Y.functionField)) :=
    formsStalkEquivₗ_image_range_stalkSpecializes (f ≫ q) (t + 1) hy
  obtain ⟨w, hw⟩ : formsStalkEquivₗ (f ≫ q) (t + 1) (genericPoint Y)
        (genericPushforwardStalkEquiv f
          (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((t + 1 : ℕ) : ℤ)) u) ∈
      Set.range (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
          (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
          (ToType (Y.presheaf.stalk y)) ↑Y.functionField)) := by
    rw [← hYrange]
    exact Set.mem_image_of_mem _ hpush
  -- the transport of the base ring across the two equal points of `S`
  have hgkb : (genericKaehlerBaseEquiv q f).toLinearMap =
      KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (genericPoint X))))
        (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
        ↑Y.functionField ↑Y.functionField :=
    LinearMap.ext (genericKaehlerBaseEquiv_apply q f)
  have htrans : exteriorPower.map (t + 1) (genericKaehlerBaseEquiv q f).toLinearMap
        (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
            (ToType (S.presheaf.stalk (q.base (genericPoint X))))
            (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w) =
      exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
          (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
          (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w :=
    KaehlerDifferential.map_mapTower_of_base (t + 1) hgkb w
  have key : genericFormsStalkEquiv (f ≫ q) (t + 1)
        (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
            (ToType (S.presheaf.stalk ((f ≫ q).base (genericPoint Y))))
            (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w) =
      genericPushforwardStalkEquiv f
        (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((t + 1 : ℕ) : ℤ)) u := by
    refine Eq.trans ?_ (genericFormsStalkEquiv_formsStalkEquivₗ (f ≫ q) (t + 1)
      (genericPushforwardStalkEquiv f
        (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((t + 1 : ℕ) : ℤ)) u))
    exact congrArg (fun z => genericFormsStalkEquiv (f ≫ q) (t + 1) z) hw
  have hEY : genericPushforwardFormsEquiv q f (t + 1)
        (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
            (ToType (S.presheaf.stalk (q.base (genericPoint X))))
            (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w) = u := by
    refine (genericPushforwardFormsEquiv_apply q f (t + 1) _).trans ?_
    rw [htrans, key]
    exact (genericPushforwardStalkEquiv f _).symm_apply_apply u
  have hEYsymm : (genericPushforwardFormsEquiv q f (t + 1)).symm u =
      exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
          (ToType (S.presheaf.stalk (q.base (genericPoint X))))
          (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w :=
    (genericPushforwardFormsEquiv q f (t + 1)).symm_apply_eq.mpr hEY.symm
  -- the trace lands in the image of `⋀ⁱ Ω[𝒪_{X,x}⁄Λ]`, which is the stalk at `x` on `X`
  have htrace : KaehlerDifferential.higherTrace hp a e
        (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
            (ToType (S.presheaf.stalk (q.base (genericPoint X))))
            (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w) ∈
      Set.range (exteriorPower.mapTower (S := ↑X.functionField) (t + 1)
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
          (ToType (S.presheaf.stalk (q.base (genericPoint X))))
          (ToType (X.presheaf.stalk (f.base y))) ↑X.functionField)) :=
    LinearMap.mem_range.mp
      (KaehlerDifferential.higherTrace_mem_range_mapExteriorPowerTower_of_isPurelyInseparable
        (t := t) hp hdegree a e w)
  have hXrange : formsStalkEquivₗ q (t + 1) (genericPoint X) ''
        Set.range ((Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q)
          ((t + 1 : ℕ) : ℤ)).presheaf.stalkSpecializes h) =
      Set.range (exteriorPower.mapTower (S := ↑X.functionField) (t + 1)
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
          (ToType (S.presheaf.stalk (q.base (genericPoint X))))
          (ToType (X.presheaf.stalk (f.base y))) ↑X.functionField)) :=
    formsStalkEquivₗ_image_range_stalkSpecializes q (t + 1) h
  obtain ⟨v, hv, hv2⟩ : formsStalkEquivₗ q (t + 1) (genericPoint X)
        (genericFormsStalkEquiv q (t + 1)
          (KaehlerDifferential.higherTrace hp a e
            (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
              (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
                (ToType (S.presheaf.stalk (q.base (genericPoint X))))
                (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w))) ∈
      formsStalkEquivₗ q (t + 1) (genericPoint X) ''
        Set.range ((Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials q)
          ((t + 1 : ℕ) : ℤ)).presheaf.stalkSpecializes h) := by
    rw [hXrange]
    exact Set.mem_of_eq_of_mem (formsStalkEquivₗ_genericFormsStalkEquiv q (t + 1) _) htrace
  have hveq : v = genericFormsStalkEquiv q (t + 1)
      (KaehlerDifferential.higherTrace hp a e
        (exteriorPower.mapTower (S := ↑Y.functionField) (t + 1)
          (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base y))))
            (ToType (S.presheaf.stalk (q.base (genericPoint X))))
            (ToType (Y.presheaf.stalk y)) ↑Y.functionField) w)) :=
    (formsStalkEquivₗ q (t + 1) (genericPoint X)).injective hv2
  have hfinal : genericFormsStalkEquiv q (t + 1)
      (KaehlerDifferential.higherTrace hp a e
        ((genericPushforwardFormsEquiv q f (t + 1)).symm u)) = v := by
    rw [hEYsymm]
    exact hveq.symm
  exact Set.mem_of_eq_of_mem hfinal hv

/-- Let `f : Y ⟶ X` be a finite dominant morphism of integral
schemes over `S` with `X` normal and locally Noetherian, let the extension of function fields
`L/K` that `f` induces be presented as `L ≅ K[x]/(xᵖ - a)`, and let `i = t + 1 ≥ 1`.  Then there
is a unique map of `𝒪_X`-modules

`Tr : f_*Ω^i_{Y/S} ⟶ (Ω^i_{X/S})^∨∨`

whose stalk at the generic point of `X` is the trace map of [Stacks, Tag 0AX5] on
`⋀ⁱ Ω_{L/Λ} ⟶ ⋀ⁱ Ω_{K/Λ}`, where `Λ` is the local ring of `S` below the generic point, the
left-hand side is the generic stalk of `f_*Ω^i_{Y/S}` by
`AlgebraicGeometry.genericPushforwardFormsEquiv` and the right-hand side is the generic stalk of
`Ω^i_{X/S}` by `AlgebraicGeometry.genericFormsStalkEquiv`.  The trace does not depend on the
presentation (`KaehlerDifferential.higherTrace_eq_of_presentations`), so quantifying over `a` and
`e` rather than fixing them is what makes `Tr` canonical. -/
@[stacks 0AX6 "the existence and uniqueness of the canonical trace map \
`f_*Ω^i_{Y/S} ⟶ (Ω^i_{X/S})^∨∨` whose stalk at the generic point is the trace map of \
[Stacks, Tag 0AX5], through the constructed identifications of both generic stalks"]
theorem existsUnique_higherTraceExtension_relativeDifferentials {S X Y : Scheme.{u}} (q : X ⟶ S)
    (f : Y ⟶ X)
    {p t : ℕ} (hp : p.Prime)
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsNormal X] [IsFinite f] [IsDominant f]
    [(Scheme.Hom.relativeDifferentials q).IsCoherent]
    [CharP (ToType (S.presheaf.stalk (q.base (genericPoint X)))) p] :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
      algebraStalkMap q (genericPoint X)
    letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
    letI := genericBaseFunctionFieldAlgebra q f
    haveI := isScalarTower_genericBaseFunctionField q f
    ∀ (a : ↑X.functionField)
      (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[↑X.functionField]
        ↑Y.functionField),
      ∃! Tr : (Scheme.Modules.pushforward f).obj
            (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((t + 1 : ℕ) : ℤ)) ⟶
          reflexiveHull (Scheme.Hom.relativeDifferentialForms q ((t + 1 : ℕ) : ℤ)),
        ∀ ω, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
              (Scheme.Modules.Hom.mapPresheaf (X := X) Tr))
                (genericPushforwardFormsEquiv q f (t + 1) ω) =
            ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
              (Scheme.Modules.Hom.mapPresheaf (X := X)
                (toReflexiveHull (Scheme.Hom.relativeDifferentialForms q
                  ((t + 1 : ℕ) : ℤ))).1))
              (genericFormsStalkEquiv q (t + 1)
                (KaehlerDifferential.higherTrace hp a e ω)) := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isFinite f
  have : (Scheme.Hom.relativeDifferentialForms q ((t + 1 : ℕ) : ℤ)).IsCoherent :=
    Scheme.Modules.isCoherent_exteriorPower (Scheme.Hom.relativeDifferentials q) (t + 1)
  have : (Scheme.Hom.relativeDifferentialForms (f ≫ q) ((t + 1 : ℕ) : ℤ)).IsCoherent :=
    Scheme.Hom.isCoherent_relativeDifferentialForms_comp_of_isFinite q f (t + 1)
  let : Algebra (ToType (S.presheaf.stalk (q.base (genericPoint X)))) ↑X.functionField :=
    algebraStalkMap q (genericPoint X)
  let : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
  let := genericBaseFunctionFieldAlgebra q f
  have := isScalarTower_genericBaseFunctionField q f
  intro a e
  set EY := genericPushforwardFormsEquiv q f (t + 1)
  obtain ⟨Tr, hTr, huniq⟩ :=
    existsUnique_lift_toReflexiveHull_relativeDifferentialForms_unconditional q f t
      ((genericFormsStalkEquiv q (t + 1)).toLinearMap ∘ₗ
        (KaehlerDifferential.higherTrace hp a e).comp EY.symm.toLinearMap)
      (higherTrace_mapsTo_range_stalkSpecializes q f hp a e)
  refine ⟨Tr, fun ω => ?_, fun Tr' hTr' => huniq Tr' fun m => ?_⟩
  · simpa using hTr (EY ω)
  · obtain ⟨ω, rfl⟩ := EY.surjective m
    simpa using hTr' ω

end AlgebraicGeometry

end
