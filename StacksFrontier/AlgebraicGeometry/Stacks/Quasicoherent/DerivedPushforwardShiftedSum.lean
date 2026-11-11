module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFreeModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.UnboundedDerivedPushforwardModules

/-!
# The derived direct image of `⊕_{m ≥ 0} 𝒪_𝒳[m]` (towards Stacks 07DD)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated `1`-morphism of algebraic stacks and let

`E = ⊕_{m ≥ 0} 𝒪_𝒳[m] ∈ D(𝒪_𝒳)`.

This file proves the two facts about `E` on which **Stacks 07DD** rests.

* `E` lies in `D_{LQCoh^fbc}(𝒪_𝒳)`: its cohomology sheaves are `𝒪_𝒳` in degrees `≤ 0` and zero
  in positive degrees.
* If `Rf_*(E)` lies in `D_{LQCoh^fbc}(𝒪_𝒴)`, then `H = H⁰(Rf_*(E))` lies in `LQCoh^fbc(𝒪_𝒴)`
  and over every object `y` of `𝒴` lying over an affine scheme

  `Γ(y, H) ≅ ∏_{m ≥ 0} Γ(y, R^m f_* 𝒪_𝒳)`,

  as `𝒪_𝒴(y)`-modules, naturally in `y`.

The second is the computation in the source's argument: `E ≅ ∏_m 𝒪_𝒳[m]` by **Stacks 08IZ**, so
`Rf_*(E)` is computed by the K-injective complex `f_*(∏_m I[m])` for an injective resolution
`𝒪_𝒳 ⟶ I`; the sections over `y` of its cohomology sheaves are computed sectionwise (**Stacks
0BKZ**), as are those of `R^m f_* 𝒪_𝒳 = H^m(f_* I)`, which lie in `LQCoh^fbc(𝒪_𝒴)` (**Stacks
0771** part (4)).  The general computation is
`Stacks.DerivedFunctor.exists_linearEquiv_sections_homology_zero_totalRightDerived_sigma`.

We also record that over every such `y`, `Γ(y, R^m f_* 𝒪_𝒳)` is the `m`-th right derived functor
of `Γ(y, f_*(-))` at `𝒪_𝒳`.

## Main results

* `AlgebraicGeometry.Stack.fppfModulesShiftedUnitSum`: the object `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]`.
* `AlgebraicGeometry.Stack.derivedCategoryB_lqcohSheafFbcFppfModules_fppfModulesShiftedUnitSum`:
  `E ∈ D_{LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_homology_zero_and_exists_linearEquiv_sections`:
  the computation of `Γ(y, H⁰(Rf_*(E)))`.
* `AlgebraicGeometry.Stack.fppfModulesHigherDirectImageSectionsIsoRightDerived`:
  `Γ(y, R^m f_* 𝒪_𝒳) ≅ R^m(Γ(y, f_*(-)))(𝒪_𝒳)`.

## Implementation notes

The models of the derived categories are instance arguments.  The library's **Stacks 08IZ**,
`AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedSingleFamily_algebraicStack`, and the
cohomology of sums of shifted objects are stated in the standard model; they are transported to an
arbitrary model by `Stacks.DerivedFunctor.isIso_piLift_sigmaπ_singleFunctor_of_standard` and
`Stacks.DerivedFunctor.nonempty_homologyFunctor_obj_sigma_singleFunctor_iso_standard`.  In every
model `E` is `∐ shiftedSingleFamily (fun _ => 𝒪_𝒳)`
(`AlgebraicGeometry.Stack.fppfModulesShiftedUnitSum_eq_sigma_shiftedSingleFamily`).

The higher direct images are written `((fppfModulesPushforward f).rightDerived m).obj 𝒪_𝒳`,
which is by definition the library's `(fppfModulesHigherDirectImage f m).obj 𝒪_𝒳`
(`AlgebraicGeometry.Stack.fppfModulesHigherDirectImage_obj_unit_eq`, proved by `rfl`).  The latter
is typed over the ring sheaf `Stacks.RelativeCech.moduleRingSheaf`, the former over the ring
sheaf of `fppfModules`; the two are equal by definition, but instance search does not see through
the first, so the module structures on the sections are only found in the second form.

## References

* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
* [Stacks Project, Tag 08IZ](https://stacks.math.columbia.edu/tag/08IZ)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  Stacks.Cohomology.AcyclicCover.evaluation_additive
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall

section Sum

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) [HasDerivedCategory (fppfModules B S hS 𝒳)]

/-- **The object `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]` of `D(𝒪_𝒳)`** of Stacks 07DD: the direct sum of the
structure sheaf placed in the degrees `-m`, `m ≥ 0`. -/
def fppfModulesShiftedUnitSum : DerivedCategory (fppfModules B S hS 𝒳) :=
  ∐ fun m : ℕ => (DerivedCategory.singleFunctor (fppfModules B S hS 𝒳) (-(m : ℤ))).obj
    (SheafOfModules.unit _)

/-- `⊕_{m ≥ 0} 𝒪_𝒳[m]` is the sum of the family `AlgebraicGeometry.Stack.shiftedSingleFamily` of
Stacks 08IZ for the constant family `𝒪_𝒳`. -/
theorem fppfModulesShiftedUnitSum_eq_sigma_shiftedSingleFamily :
    fppfModulesShiftedUnitSum B S hS 𝒳 =
      ∐ shiftedSingleFamily B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (fun _ => SheafOfModules.unit _) :=
  rfl

omit [HasDerivedCategory (fppfModules B S hS 𝒳)] in
/-- The structure sheaf of an algebraic stack lies in `LQCoh^fbc(𝒪_𝒳)`. -/
theorem lqcohSheafFbcFppfModules_unit :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 (SheafOfModules.unit _) :=
  locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_unit B E h S hS _ _

include E h in
/-- **Stacks 08IZ for `E`**, in any model of the derived category: the canonical map
`⊕_{m ≥ 0} 𝒪_𝒳[m] ⟶ ∏_{m ≥ 0} 𝒪_𝒳[m]` is an isomorphism. -/
theorem isIso_piLift_sigmaπ_shiftedUnit :
    IsIso (Pi.lift (Sigma.π fun m : ℕ =>
      (DerivedCategory.singleFunctor (fppfModules B S hS 𝒳) (-(m : ℤ))).obj
        (SheafOfModules.unit _))) :=
  Stacks.DerivedFunctor.isIso_piLift_sigmaπ_singleFunctor_of_standard
    (H' := HasDerivedCategory.standard _) (fun _ => SheafOfModules.unit _)
    (isIso_coproductToProduct_shiftedSingleFamily_algebraicStack B E h S hS 𝒳
      (fun _ => SheafOfModules.unit _) (fun _ => lqcohSheafFbcFppfModules_unit B E h S hS 𝒳))

/-- **`E = ⊕_{m ≥ 0} 𝒪_𝒳[m]` lies in `D_{LQCoh^fbc}(𝒪_𝒳)`**: its cohomology sheaf in degree
`-m ≤ 0` is `𝒪_𝒳`, which lies in `LQCoh^fbc(𝒪_𝒳)`, and its cohomology sheaves in positive
degrees vanish. -/
theorem derivedCategoryB_lqcohSheafFbcFppfModules_fppfModulesShiftedUnitSum :
    DerivedCategoryB.derivedCategoryB (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳)
      (fppfModulesShiftedUnitSum B S hS 𝒳) := by
  intro n
  obtain ⟨e⟩ := Stacks.DerivedFunctor.nonempty_homologyFunctor_obj_sigma_singleFunctor_iso_standard
    (H' := HasDerivedCategory.standard _) (fun _ : ℕ => (SheafOfModules.unit _ : fppfModules B S hS 𝒳)) n
  refine (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).prop_of_iso e.symm ?_
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let F := shiftedSingleFamily B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (fun _ => (SheafOfModules.unit _ : fppfModules B S hS 𝒳))
  have hge : ∀ m : ℕ, (F m).IsGE (-(m : ℤ)) := fun m => by
    dsimp only [F, shiftedSingleFamily]; infer_instance
  have hle : ∀ m : ℕ, (F m).IsLE (-(m : ℤ)) := fun m => by
    dsimp only [F, shiftedSingleFamily]; infer_instance
  change lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
    ((DerivedCategory.homologyFunctor
      (fppfSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) n).obj (∐ F))
  rcases lt_or_ge 0 n with hn | hn
  · exact (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).prop_of_isZero
      (Stacks.ShiftedSum.isZero_homologyCoproduct_of_pos F hle n hn)
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)
    obtain rfl : n = -(k : ℤ) := by omega
    exact (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).prop_of_iso
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-(k : ℤ))).app _).symm ≪≫
        (Stacks.ShiftedSum.homologyCoproductIso F hge hle k).symm)
      (lqcohSheafFbcFppfModules_unit B E h S hS 𝒳)

end Sum

section Pushforward

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  [HasDerivedCategory (fppfModules B S hS 𝒳)] [HasDerivedCategory (fppfModules B S hS 𝒴)]

omit [HasDerivedCategory (fppfModules B S hS 𝒳)] [HasDerivedCategory (fppfModules B S hS 𝒴)] in
/-- The library's higher direct image `AlgebraicGeometry.Stack.fppfModulesHigherDirectImage` of
the structure sheaf is, by definition, the right derived functor of
`AlgebraicGeometry.Stack.fppfModulesPushforward` at `𝒪_𝒳`; the results of this file are stated
with the latter. -/
theorem fppfModulesHigherDirectImage_obj_unit_eq (m : ℕ) :
    (fppfModulesHigherDirectImage B S hS f m).obj (SheafOfModules.unit _) =
      ((fppfModulesPushforward B S hS f).rightDerived m).obj (SheafOfModules.unit _) :=
  rfl

omit [HasDerivedCategory (fppfModules B S hS 𝒳)] [HasDerivedCategory (fppfModules B S hS 𝒴)] in
include E h in
/-- For a quasi-compact and quasi-separated `f`, the higher direct images `R^m f_* 𝒪_𝒳` have no
higher cohomology over the objects of `𝒴` lying over an affine scheme. -/
theorem isZero_rightDerived_evaluation_fppfModulesHigherDirectImage_unit
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (V : 𝒴.val.val.obj) (hV : IsAffineOver B S hS (𝒴.val.val.p.obj V)) (p : ℕ) (hp : 0 < p)
    (m : ℕ) :
    IsZero (((SheafOfModules.evaluation
      (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf)
        (op V)).rightDerived p).obj
          ((fppfModulesHigherDirectImage B S hS f m).obj (SheafOfModules.unit _))) :=
  isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack B E h S hS 𝒴 _
    (lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs _
      (lqcohSheafFbcFppfModules_unit B E h S hS 𝒳) m) V hV p hp

/-- **The computation in the proof of Stacks 07DD.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and
quasi-separated `1`-morphism of algebraic stacks and `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]`.  If `Rf_*(E)` lies in
`D_{LQCoh^fbc}(𝒪_𝒴)`, then `H = H⁰(Rf_*(E))` lies in `LQCoh^fbc(𝒪_𝒴)`, and over every object `y`
of `𝒴` lying over an affine scheme there is an `𝒪_𝒴(y)`-linear isomorphism

`α_y : Γ(y, H) ≅ ∏_{m ≥ 0} Γ(y, R^m f_* 𝒪_𝒳)`,

natural in `y`: for `ι : y ⟶ y'` between such objects,
`α_y (s|_y) m = (α_{y'} s m)|_y`. -/
theorem lqcohSheafFbcFppfModules_homology_zero_and_exists_linearEquiv_sections
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hE : DerivedCategoryB.derivedCategoryB (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴)
      ((fppfModulesDerivedPushforward B S hS f).obj (fppfModulesShiftedUnitSum B S hS 𝒳))) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
        ((DerivedCategory.homologyFunctor _ 0).obj
          ((fppfModulesDerivedPushforward B S hS f).obj (fppfModulesShiftedUnitSum B S hS 𝒳))) ∧
      ∃ α : ∀ y : 𝒴.val.val.obj, IsAffineOver B S hS (𝒴.val.val.p.obj y) →
        ((((DerivedCategory.homologyFunctor _ 0).obj
          ((fppfModulesDerivedPushforward B S hS f).obj
            (fppfModulesShiftedUnitSum B S hS 𝒳))).val.obj (op y)) ≃ₗ[
              (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
                .fppf).obj.obj (op y)]
          ((m : ℕ) → (((fppfModulesPushforward B S hS f).rightDerived m).obj
            (SheafOfModules.unit _)).val.obj (op y))),
        ∀ (y y' : 𝒴.val.val.obj) (hy : IsAffineOver B S hS (𝒴.val.val.p.obj y))
          (hy' : IsAffineOver B S hS (𝒴.val.val.p.obj y')) (ι : y ⟶ y')
          (s : ((DerivedCategory.homologyFunctor _ 0).obj
            ((fppfModulesDerivedPushforward B S hS f).obj
              (fppfModulesShiftedUnitSum B S hS 𝒳))).val.obj (op y')) (m : ℕ),
          α y hy (((DerivedCategory.homologyFunctor _ 0).obj
            ((fppfModulesDerivedPushforward B S hS f).obj
              (fppfModulesShiftedUnitSum B S hS 𝒳))).val.map ι.op s) m =
            (((fppfModulesPushforward B S hS f).rightDerived m).obj
              (SheafOfModules.unit _)).val.map ι.op (α y' hy' s m) := by
  have := preservesFiniteLimits_fppfModulesPullback B S hS f
  refine ⟨hE 0, ?_⟩
  have key :=
    Stacks.DerivedFunctor.exists_linearEquiv_sections_homology_zero_totalRightDerived_sigma
    (hA := inferInstanceAs (IsGrothendieckAbelian.{u} (fppfModules B S hS 𝒳)))
    (hO := inferInstanceAs (IsGrothendieckAbelian.{u} (fppfModules B S hS 𝒴)))
    (hP := (fppfModulesPullbackPushforwardAdjunction B S hS f).right_adjoint_additive)
    (fppfModulesPushforward B S hS f) (fppfModulesPullbackPushforwardAdjunction B S hS f)
    (SheafOfModules.unit _) (isIso_piLift_sigmaπ_shiftedUnit B E h S hS 𝒳)
    (fun y => IsAffineOver B S hS (𝒴.val.val.p.obj y))
    (hasEnoughObjects_isAffineOver_of_essentiallySmall B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids)
    (fun V hV p hp n => isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack
      B E h S hS 𝒴 _ (hE n) V hV p hp)
    (isZero_rightDerived_evaluation_fppfModulesHigherDirectImage_unit B E h S hS f hqc hqs)
  exact key

/-- **Sections of `R^m f_* 𝒪_𝒳` over affine objects.** For a quasi-compact and quasi-separated
`f` and an object `y` of `𝒴` lying over an affine scheme, `Γ(y, R^m f_* 𝒪_𝒳)` is, as an
`𝒪_𝒴(y)`-module, the `m`-th right derived functor of `Γ(y, f_*(-))` at `𝒪_𝒳`. -/
def fppfModulesHigherDirectImageSectionsIsoRightDerived
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (m : ℕ) (y : 𝒴.val.val.obj) (hy : IsAffineOver B S hS (𝒴.val.val.p.obj y)) :
    (((fppfModulesPushforward B S hS f).rightDerived m).obj (SheafOfModules.unit _)).val.obj
        (op y) ≅
      ((fppfModulesPushforward B S hS f ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y)).rightDerived m).obj (SheafOfModules.unit _) :=
  have := preservesFiniteLimits_fppfModulesPullback B S hS f
  Stacks.DerivedFunctor.sectionsRightDerivedIsoRightDerivedSections
    (hO := inferInstanceAs (IsGrothendieckAbelian.{u} (fppfModules B S hS 𝒴)))
    (hP := (fppfModulesPullbackPushforwardAdjunction B S hS f).right_adjoint_additive)
    (fppfModulesPushforward B S hS f) (fppfModulesPullbackPushforwardAdjunction B S hS f)
    (SheafOfModules.unit _) (fun y => IsAffineOver B S hS (𝒴.val.val.p.obj y))
    (hasEnoughObjects_isAffineOver_of_essentiallySmall B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids)
    (isZero_rightDerived_evaluation_fppfModulesHigherDirectImage_unit B E h S hS f hqc hqs) m hy

end Pushforward

end AlgebraicGeometry.Stack

end
