module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineBlowupLift.Chart
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Pullback of a module of Tor dimension at most one to a blowup

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on it and `b : Bl_I(X) ⟶ X` the blowup of
`X` in `I`. For an `𝒪_X`-module `ℱ` of Tor dimension at most one the derived pullback `Lb^*ℱ` is
the ordinary pullback `b^*ℱ`, and if `ℱ` is moreover perfect then `b^*ℱ` is a perfect
`𝒪_{Bl_I(X)}`-module of Tor dimension at most one.

The mathematical content is a statement about the affine blowup algebras. Tor dimension at most
one means that `ℱ` is the cokernel of an injection `𝒦 ↪ 𝒢` of flat `𝒪_X`-modules, and what has to
be seen is that this injection stays injective after pullback. On the standard affine chart of
the blowup attached to a section `a` of `I` over an affine open `U`, pullback is base change
along `Γ(X, U) → Γ(X, U)[I/a]`, and `Γ(X, U)[I/a]` is a subalgebra of the localization
`Γ(X, U)_a`, which is flat over `Γ(X, U)`; tensoring an injection with flat source by a
subalgebra of a flat algebra keeps it injective.

## Main definitions

* `AlgebraicGeometry.derivedPullbackBlowUpToBaseIso`: the canonical isomorphism
  `Lb^*ℱ ≅ (b^*ℱ)[0]`.

## Main results

* `AlgebraicGeometry.isIso_derivedPullbackComparison_blowUpToBase`: the canonical comparison
  `Lb^*ℱ ⟶ b^*ℱ` of Stacks 06YJ is invertible on an `𝒪_X`-module of Tor dimension at most one.
* `AlgebraicGeometry.isPerfect_modulePullback_blowUpToBase`: the ordinary pullback of a perfect
  module of Tor dimension at most one is perfect.
* `AlgebraicGeometry.hasTorAmplitude_modulePullback_blowUpToBase`: the ordinary pullback again
  has Tor dimension at most one.

## Implementation notes

Tor dimension at most `n` is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude X ℱ[0] (-n) 0`, the
spelling of Stacks 08CG built on the derived tensor product of Stacks 06YU, which is the one
carrying the flat-representative criterion of Stacks 08CI that the proof consumes. Perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, the spelling of Stacks 08CM that the derived
pullback theorem of Stacks 09UA is stated at.

Everything is at the ringed space underlying the scheme, with modules in the spelling
`StrictlyPerfect.OXMod` and with `RingedSpaceModuleAdjunction.modulePullback` for the pullback:
that is where the derived pullback of Stacks 06YJ and its comparison morphism live.

The two clauses about the ordinary pullback are stated with the hypotheses of the source, while
the clause identifying the derived pullback is stated without the perfectness hypothesis, which
its proof does not use.

## References

* [Stacks Project, Tag 0ESS](https://stacks.math.columbia.edu/tag/0ESS)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 09U8](https://stacks.math.columbia.edu/tag/09U8)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect TensorProduct
open TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Injectivity after tensoring with an affine blowup algebra -/

/-- If `S` embeds into a flat `R`-algebra `T` and `M` is a flat `R`-module, then tensoring an
injective map of `R`-modules with `S` keeps it injective: the composite with the injection of
`S ⊗ N` into `T ⊗ N` factors through `T ⊗ M`, where injectivity holds by flatness of `T`. -/
private theorem lTensor_injective_of_injective_into_flat
    {R S T M N : Type*} [CommRing R]
    [AddCommGroup S] [Module R S] [AddCommGroup T] [Module R T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R T] [Module.Flat R M]
    (g : S →ₗ[R] T) (hg : Function.Injective g)
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (f.lTensor S) := by
  have hc : (f.lTensor T).comp (g.rTensor M) = (g.rTensor N).comp (f.lTensor S) := by
    ext s m
    rfl
  have h := (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.rTensor_preserves_injective_linearMap g hg)
  rw [← LinearMap.coe_comp, hc, LinearMap.coe_comp] at h
  exact h.of_comp

/-- Tensoring an injective map of `R`-modules with flat source by the affine blowup algebra
`R[I/a]` keeps it injective: that algebra is a subalgebra of the localization `R_a`, which is
flat over `R`. -/
private theorem lTensor_injective_affineBlowupAlgebra
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] (I : Ideal R) (a : R)
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (f.lTensor (affineBlowupAlgebra I a (Localization.Away a))) :=
  lTensor_injective_of_injective_into_flat
    (affineBlowupAlgebra I a (Localization.Away a)).val.toLinearMap
    Subtype.val_injective f hf

/-- Injectivity after tensoring with an `R`-algebra `S` passes to a flat `S`-algebra `T`. -/
private theorem lTensor_injective_of_flat_extension
    {R S T M N : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat S T] (f : M →ₗ[R] N)
    (h : Function.Injective (f.lTensor S)) : Function.Injective (f.lTensor T) := by
  rw [← AlgebraTensorModule.coe_lTensor (A := T),
    ← EquivLike.injective_comp (AlgebraTensorModule.cancelBaseChange R S T T M),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp,
    AlgebraTensorModule.lTensor_comp_cancelBaseChange,
    LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  exact Module.Flat.lTensor_preserves_injective_linearMap (f.baseChange S) h

/-- For a localization `A` of `R` and modules over `A`, injectivity after tensoring with an
`R`-algebra `B` can be checked after restricting scalars to `R`: the two base changes are
identified by `IsLocalization.moduleTensorEquiv`. -/
private theorem lTensor_injective_of_localization_base
    {R A B M N : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[A] N) (h : Function.Injective ((f.restrictScalars R).lTensor B)) :
    Function.Injective (f.lTensor B) := by
  let eM := IsLocalization.moduleTensorEquiv S A B M
  let eN := IsLocalization.moduleTensorEquiv S A B N
  have hc : ∀ t, eN (f.lTensor B t) = (f.restrictScalars R).lTensor B (eM t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact fun x y hxy => eM.injective (h (by rw [← hc, ← hc, hxy]))

/-! ### The standard affine chart of a blowup -/

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The standard affine chart of the blowup of `X` in `I` attached to a section `a` of `I` over
an affine open `U`: the spectrum of the affine blowup algebra `Γ(X, U)[I/a]`, mapped into the
blowup through the chart of the relative `Proj` of the Rees algebra. -/
private def affineBlowupChart (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
      (Localization.Away (a : X.presheaf.obj (op U.1))))) ⟶ blowUp I :=
  (affineBlowupStandardOpenIso I U a).hom ≫
    Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp I U a

/-- The chart lies over `X` through the structure map of the affine blowup algebra. -/
private theorem affineBlowupChart_blowUpToBase (U : X.affineOpens) (a : I.ideal U) :
    affineBlowupChart I U a ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.obj (op U.1))
          (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
            (Localization.Away (a : X.presheaf.obj (op U.1)))))) ≫
        U.2.isoSpec.inv ≫ U.1.ι := by
  have hover := congrArg (fun t => t ≫ U.1.ι) (affineBlowupStandardOpenIso_over I U a)
  simp only [Category.assoc] at hover
  simp only [affineBlowupChart, Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp,
    Category.assoc,
    (Stacks.RelativeProj.Situation.relativeProjChart_isPullback (reesSituation I) U).w]
  exact hover

/-- The charts attached to the sections of `I` over the affine opens of `X` cover the blowup. -/
private theorem exists_affineBlowupChart_preimage (x : blowUp I) :
    ∃ (U : X.affineOpens) (a : I.ideal U), ∃ y, affineBlowupChart I U a y = x := by
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := blowUpToBase I x) (U := ⊤) trivial
  let U : X.affineOpens := ⟨V, hV⟩
  have hx' : x ∈ (blowUpToBase I ⁻¹ᵁ U.1).carrier := hx
  rw [← blownUpAffine_chart_cover I U] at hx'
  obtain ⟨a, z, hz⟩ := Set.mem_iUnion.mp hx'
  refine ⟨U, a, (affineBlowupStandardOpenIso I U a).inv z, ?_⟩
  have hcancel : (affineBlowupStandardOpenIso I U a).hom
      ((affineBlowupStandardOpenIso I U a).inv z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hz]
  show (Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp I U a)
    ((affineBlowupStandardOpenIso I U a).hom
      ((affineBlowupStandardOpenIso I U a).inv z)) = _
  rw [hcancel]
  rfl

/-- The chart is an open immersion. -/
private instance affineBlowupChart_isOpenImmersion (U : X.affineOpens) (a : I.ideal U) :
    IsOpenImmersion (affineBlowupChart I U a) := by
  have : IsOpenImmersion
      (Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (Stacks.RelativeProj.Situation.relativeProjChart_isPullback (reesSituation I) U).flip
      inferInstance
  dsimp only [affineBlowupChart, Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp]
  infer_instance

/-! ### Stalks along an affine chart -/

/-- The germ map of an affine open, composed with the stalk map of `Spec Γ(X, U) ⟶ X`, is the
canonical map of `Γ(X, U)` to the stalk of the structure sheaf of its spectrum. -/
private theorem fromSpec_germ {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (y : Spec (X.presheaf.obj (op U))) (hy : hU.fromSpec y ∈ U) :
    X.presheaf.germ U (hU.fromSpec y) hy ≫ hU.fromSpec.stalkMap y =
      StructureSheaf.toStalk (X.presheaf.obj (op U)) y := by
  rw [Scheme.Hom.germ_stalkMap, hU.fromSpec_app_self, Category.assoc]
  exact congrArg (fun t => (Scheme.ΓSpecIso Γ(X, U)).inv ≫ t)
    ((Spec Γ(X, U)).presheaf.germ_res (eqToHom hU.fromSpec_preimage_self) y hy)

/-- For an affine chart `j : Spec S ⟶ Y` of a scheme over an affine open `U` of `X`, the germ
map at `U` followed by the two stalk maps is the structure map `Γ(X, U) ⟶ S` followed by the
canonical map of `S` to the stalk of `Spec S` at the chosen point. -/
private theorem chart_germ {X Y : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U)
    (S : CommRingCat.{u}) (α : X.presheaf.obj (op U) ⟶ S)
    (j : Spec S ⟶ Y) (hj : j ≫ f = Spec.map α ≫ hU.fromSpec)
    (y : Spec S) (hy : f (j y) ∈ U) :
    X.presheaf.germ U (f (j y)) hy ≫ f.stalkMap (j y) ≫ j.stalkMap y =
      α ≫ StructureSheaf.toStalk S y := by
  rw [← Scheme.Hom.stalkMap_comp]
  show X.presheaf.germ U ((j ≫ f) y) hy ≫ (j ≫ f).stalkMap y = _
  change (j ≫ f) y ∈ U at hy
  revert hy
  rw [hj]
  intro hy
  have hy' : hU.fromSpec (Spec.map α y) ∈ U := hy
  have key : X.presheaf.germ U (hU.fromSpec (Spec.map α y)) hy' ≫
      hU.fromSpec.stalkMap (Spec.map α y) ≫ (Spec.map α).stalkMap y =
      α ≫ StructureSheaf.toStalk S y := by
    rw [← Category.assoc, fromSpec_germ hU (Spec.map α y) hy']
    exact stalkMap_toStalk α y
  rw [Scheme.Hom.stalkMap_comp]
  exact key

/-- **Injectivity after tensoring passes from an affine chart to the stalks it covers.** Let
`j : Spec S ⟶ Y` be an open immersion lying over an affine open `U` of `X` through a morphism
`f : Y ⟶ X`, with `S` a `Γ(X, U)`-algebra. If tensoring an injective map of `Γ(X, U)`-modules
with flat source by `S` keeps it injective, then the same holds at every point of the chart for
the stalk of `𝒪_X` at the image point and the stalk of `𝒪_Y`.

The stalks are localizations of `Γ(X, U)` and of `S`, and localization is flat, so both the
passage to `Γ(X, U)` and the passage from `S` are flat base changes. -/
private theorem lTensor_stalk_injective_of_chart
    {X Y : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (S : CommRingCat.{u}) [Algebra Γ(X, U) S]
    (j : Spec S ⟶ Y) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫ hU.fromSpec)
    (hS : ∀ {M N : Type u} [AddCommGroup M] [Module Γ(X, U) M]
        [AddCommGroup N] [Module Γ(X, U) N] [Module.Flat Γ(X, U) M]
        (φ : M →ₗ[Γ(X, U)] N), Function.Injective φ →
        Function.Injective (φ.lTensor S))
    (y : Spec S) {M N : Type u}
    [AddCommGroup M] [Module (X.presheaf.stalk (f (j y))) M]
    [AddCommGroup N] [Module (X.presheaf.stalk (f (j y))) N]
    (hflat : Module.Flat (X.presheaf.stalk (f (j y))) M)
    (φ : M →ₗ[X.presheaf.stalk (f (j y))] N) (hφ : Function.Injective φ) :
    let := (f.stalkMap (j y)).hom.toAlgebra
    Function.Injective (φ.lTensor (Y.presheaf.stalk (j y))) := by
  let R := Γ(X, U)
  let A := X.presheaf.stalk (f (j y))
  let B := Y.presheaf.stalk (j y)
  let T := (Spec S).presheaf.stalk y
  have : y.asIdeal.IsPrime := y.isPrime
  have hx : f (j y) ∈ U := by
    show (j ≫ f) y ∈ U
    rw [hj]
    have hm : hU.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) y) ∈
      hU.fromSpec.opensRange := ⟨_, rfl⟩
    simpa only [Scheme.Hom.comp_apply, hU.opensRange_fromSpec] using hm
  let : Algebra R A := X.presheaf.algebra_section_stalk ⟨f (j y), hx⟩
  have : IsLocalization.AtPrime A (hU.primeIdealOf ⟨f (j y), hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨f (j y), hx⟩
  let : Algebra A B := (f.stalkMap (j y)).hom.toAlgebra
  let : Algebra R B := (algebraMap A B).comp (algebraMap R A) |>.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let e : B ≃+* T := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  let : Algebra S T := StructureSheaf.stalkAlgebra (R := S) y
  have : IsLocalization.AtPrime T y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (R := S) y
  let : Algebra S B := (e.symm.toRingHom.comp (algebraMap S T)).toAlgebra
  have : IsLocalization.AtPrime B y.asIdeal :=
    (IsLocalization.isLocalization_iff_of_ringEquiv y.asIdeal.primeCompl e.symm).mp
      (inferInstanceAs (IsLocalization.AtPrime T y.asIdeal))
  have : IsScalarTower R S B := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    apply e.injective
    show (j.stalkMap y) ((f.stalkMap (j y)) (X.presheaf.germ U (f (j y)) hx r)) =
      e (e.symm ((algebraMap S T) (algebraMap R S r)))
    rw [e.apply_symm_apply]
    exact congrArg (fun k => k r)
      (chart_germ f hU S (CommRingCat.ofHom (algebraMap R S)) j hj y hx)
  let : Module R M := Module.compHom M (algebraMap R A)
  let : Module R N := Module.compHom N (algebraMap R A)
  have : IsScalarTower R A M := IsScalarTower.restrictScalars R A M
  have : IsScalarTower R A N := IsScalarTower.restrictScalars R A N
  have : Module.Flat R A := IsLocalization.flat A
    (hU.primeIdealOf ⟨f (j y), hx⟩).asIdeal.primeCompl
  have : Module.Flat S B := IsLocalization.flat B y.asIdeal.primeCompl
  have : Module.Flat R M := Module.Flat.trans R A M
  exact lTensor_injective_of_localization_base (R := R)
    (hU.primeIdealOf ⟨f (j y), hx⟩).asIdeal.primeCompl φ
    (lTensor_injective_of_flat_extension (S := S) (φ.restrictScalars R)
      (hS (φ.restrictScalars R) hφ))

/-- The module structure of the stalk of an `𝒪_X`-module over the stalk of the structure sheaf,
seated at the spelling of the ring sheaf used by the pullback adjunction. -/
@[reducible]
private instance stalkModule {Z : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing Z))
    (z : Z) : Module (Z.presheaf.stalk z) ↑(TopCat.Presheaf.stalk M.val.presheaf z) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Z.presheaf) M.val z

/-- The module structure of the stalk of an `𝒪_X`-module on a scheme, at the spelling in which
the structure sheaf of the scheme is written. -/
@[reducible]
private instance stalkModuleScheme {X : Scheme.{u}}
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (z : X) :
    Module (X.presheaf.stalk z) ↑(TopCat.Presheaf.stalk M.val.presheaf z) :=
  stalkModule M z

/-- The stalk map of a morphism of `𝒪_X`-modules sends the germ of a section to the germ of its
image. -/
private theorem stalkMapAdd_germ' {Z : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (φ : M ⟶ N) (z : Z)
    (V : Opens Z.carrier) (hz : z ∈ V) (s : M.val.obj (op V)) :
    OXModule.stalkMapAdd M N φ z (TopCat.Presheaf.germ M.val.presheaf V z hz s) =
      TopCat.Presheaf.germ N.val.presheaf V z hz (φ.val.app (op V) s) := by
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
      ((PresheafOfModules.toPresheaf _).map φ.val)
      (TopCat.Presheaf.germ M.val.presheaf V z hz s) = _
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply V z hz
    ((PresheafOfModules.toPresheaf _).map φ.val) s

/-- The stalk map of a morphism of `𝒪_X`-modules at a point, as a linear map of stalks. -/
private def stalkMapLinear {Z : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (φ : M ⟶ N) (z : Z) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf z) →ₗ[Z.presheaf.stalk z]
      ↑(TopCat.Presheaf.stalk N.val.presheaf z) :=
  OXModule.stalkLinearMap M N φ z

/-- `stalkMapLinear` sends the germ of a section to the germ of its image. -/
private theorem stalkMapLinear_germ {Z : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (φ : M ⟶ N) (z : Z)
    (V : Opens Z.carrier) (hz : z ∈ V) (s : M.val.obj (op V)) :
    stalkMapLinear φ z (TopCat.Presheaf.germ M.val.presheaf V z hz s) =
      TopCat.Presheaf.germ N.val.presheaf V z hz (φ.val.app (op V) s) := by
  show OXModule.stalkMapAdd M N φ z (TopCat.Presheaf.germ M.val.presheaf V z hz s) = _
  exact stalkMapAdd_germ' φ z V hz s

/-- **Injectivity of a map identified with a base change.** Let `eM` and `eN` identify two
`B`-modules with base changes `B ⊗_A M` and `B ⊗_A N`, and let `ψ` be a `B`-linear map between
them which, under those identifications, sends `1 ⊗ m` to `1 ⊗ σ m` for an `A`-linear `σ`. If
`σ ⊗_A B` is injective then so is `ψ`. -/
private theorem injective_of_one_tmul {A B M N M' N' : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    [AddCommMonoid M'] [Module B M'] [AddCommMonoid N'] [Module B N']
    (eM : M' ≃ₗ[B] TensorProduct A B M) (eN : N' ≃ₗ[B] TensorProduct A B N)
    (ψ : M' →ₗ[B] N') (σ : M →ₗ[A] N)
    (hkey : ∀ m : M, eN (ψ (eM.symm ((1 : B) ⊗ₜ[A] m))) = (1 : B) ⊗ₜ[A] σ m)
    (hinj : Function.Injective (σ.lTensor B)) :
    Function.Injective ψ := by
  have hF : ∀ t, eN (ψ (eM.symm t)) = σ.baseChange B t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [TensorProduct.tmul_eq_smul_one_tmul b m]
      simp only [map_smul, hkey, LinearMap.baseChange_tmul]
    | add s t hs ht => simp only [map_add, hs, ht]
  intro a b hab
  apply eM.injective
  apply hinj
  show σ.baseChange B (eM a) = σ.baseChange B (eM b)
  rw [← hF (eM a), ← hF (eM b), eM.symm_apply_apply, eM.symm_apply_apply, hab]

/-- **A pullback of modules is injective on a stalk as soon as the base change of the stalk map
is.** The stalk of a pullback at `x` is the base change along the germ map of the stalk at `f x`
(Stacks 0098), and under that identification the stalk map of `f^*φ` is the base change of the
stalk map of `φ`. -/
private theorem stalk_pullback_injective_of_tensor
    {Y Z : RingedSpace.{u, u}} (f : Y ⟶ Z)
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (φ : M ⟶ N) (x : Y)
    (h : letI : Algebra (Z.presheaf.stalk (f.hom.base x)) (Y.presheaf.stalk x) :=
        (f.hom.stalkMap x).hom.toAlgebra
      Function.Injective ((stalkMapLinear φ (f.hom.base x)).lTensor (Y.presheaf.stalk x))) :
    Function.Injective (OXModule.stalkMapAdd _ _ ((modulePullback f).map φ) x) := by
  let : Algebra (Z.presheaf.stalk (f.hom.base x)) (Y.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨eM, heM⟩ := exists_modulePullbackStalkLinearEquiv f M x
  obtain ⟨eN, heN⟩ := exists_modulePullbackStalkLinearEquiv f N x
  refine @injective_of_one_tmul ↑(Z.presheaf.stalk (f.hom.base x)) ↑(Y.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk M.val.presheaf (f.hom.base x))
    ↑(TopCat.Presheaf.stalk N.val.presheaf (f.hom.base x))
    ↑(TopCat.Presheaf.stalk ((modulePullback f).obj M).val.presheaf x)
    ↑(TopCat.Presheaf.stalk ((modulePullback f).obj N).val.presheaf x)
    inferInstance inferInstance inferInstance
    inferInstance (stalkModule M (f.hom.base x))
    inferInstance (stalkModule N (f.hom.base x))
    inferInstance (stalkModule ((modulePullback f).obj M) x)
    inferInstance (stalkModule ((modulePullback f).obj N) x)
    eM eN (stalkMapLinear ((modulePullback f).map φ) x)
    (stalkMapLinear φ (f.hom.base x)) (fun m => ?_) h
  obtain ⟨V, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  have hunit := congrArg (fun k => k.val.app (op V) s)
    ((modulePullbackPushforwardAdjunction f).unit.naturality φ)
  change ((modulePullbackPushforwardAdjunction f).unit.app N).val.app (op V)
      (φ.val.app (op V) s) =
    ((modulePullback f).map φ).val.app (op ((opensMap f).obj V))
      (((modulePullbackPushforwardAdjunction f).unit.app M).val.app (op V) s) at hunit
  have stepA := (congrArg eM.symm (heM V hx s)).symm.trans
    (eM.symm_apply_apply (TopCat.Presheaf.germ ((modulePullback f).obj M).val.presheaf
      ((opensMap f).obj V) x hx
      ((((modulePullbackPushforwardAdjunction f).unit.app M).val.app (op V)) s)))
  have stepB : stalkMapLinear ((modulePullback f).map φ) x
        (TopCat.Presheaf.germ ((modulePullback f).obj M).val.presheaf ((opensMap f).obj V) x hx
          ((((modulePullbackPushforwardAdjunction f).unit.app M).val.app (op V)) s)) =
      TopCat.Presheaf.germ ((modulePullback f).obj N).val.presheaf ((opensMap f).obj V) x hx
        ((((modulePullbackPushforwardAdjunction f).unit.app N).val.app (op V))
          (φ.val.app (op V) s)) := by
    rw [stalkMapLinear_germ ((modulePullback f).map φ) x ((opensMap f).obj V) hx
      ((((modulePullbackPushforwardAdjunction f).unit.app M).val.app (op V)) s), hunit]
  exact (congrArg (fun z => eN (stalkMapLinear ((modulePullback f).map φ) x z)) stepA).trans
    ((congrArg eN stepB).trans ((heN V hx (φ.val.app (op V) s)).trans
      (congrArg (fun z : ↑(TopCat.Presheaf.stalk N.val.presheaf (f.hom.base x)) =>
          (1 : Y.presheaf.stalk x) ⊗ₜ[Z.presheaf.stalk (f.hom.base x)] z)
        (stalkMapLinear_germ φ (f.hom.base x) V hx s).symm)))

/-- `lTensor_stalk_injective_of_chart` for the stalk map of a morphism of `𝒪_X`-modules. -/
private theorem lTensor_stalkMapLinear_injective_of_chart
    {X Y : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (S : CommRingCat.{u}) [Algebra Γ(X, U) S] (j : Spec S ⟶ Y) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫ hU.fromSpec)
    (hS : ∀ {M N : Type u} [AddCommGroup M] [Module Γ(X, U) M]
      [AddCommGroup N] [Module Γ(X, U) N] [Module.Flat Γ(X, U) M]
      (ψ : M →ₗ[Γ(X, U)] N), Function.Injective ψ →
      Function.Injective (ψ.lTensor S))
    (y : Spec S) {M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} (φ : M ⟶ N)
    (hflat : Module.Flat (X.presheaf.stalk (f (j y)))
      ↑(TopCat.Presheaf.stalk M.val.presheaf (f (j y))))
    (hφ : Function.Injective (stalkMapLinear φ (f (j y)))) :
    let := (f.stalkMap (j y)).hom.toAlgebra
    Function.Injective ((stalkMapLinear φ (f (j y))).lTensor (Y.presheaf.stalk (j y))) :=
  lTensor_stalk_injective_of_chart f hU S j hj hS y hflat (stalkMapLinear φ (f (j y))) hφ

/-! ### Pullback to a blowup preserves injections out of a flat module -/

/-- The structure map of the standard affine chart of the blowup, as a morphism over the
canonical morphism from the spectrum of the sections on the affine open. -/
private theorem affineBlowupChart_comp_eq_fromSpec (U : X.affineOpens) (a : I.ideal U) :
    affineBlowupChart I U a ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op U.1))
        (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
          (Localization.Away (a : X.presheaf.obj (op U.1)))))) ≫ U.2.fromSpec := by
  simpa only [IsAffineOpen.fromSpec, Category.assoc] using affineBlowupChart_blowUpToBase I U a

/-- **Pullback to a blowup keeps an injection with flat source injective.** On the standard
affine chart `Spec Γ(X, U)[I/a]` the structure map lands in the localization `Γ(X, U)_a`, and
tensoring an injection with flat source by a subalgebra of a flat algebra keeps it injective;
the stalks of `X` and of the blowup are localizations of `Γ(X, U)` and of `Γ(X, U)[I/a]`. -/
private theorem mono_modulePullback_blowUpToBase
    {M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} (φ : M ⟶ N)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) M)
    (hφ : Mono φ) :
    Mono ((modulePullback (blowUpToBase I).toLRSHom.toShHom).map φ) := by
  have := hφ
  apply OXModule.mono_of_stalkMapAdd_injective
  intro x
  obtain ⟨U, a, y, rfl⟩ := exists_affineBlowupChart_preimage I x
  refine stalk_pullback_injective_of_tensor (blowUpToBase I).toLRSHom.toShHom φ _ ?_
  exact lTensor_stalkMapLinear_injective_of_chart (blowUpToBase I) U.2
    (CommRingCat.of (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
      (Localization.Away (a : X.presheaf.obj (op U.1)))))
    (affineBlowupChart I U a) (affineBlowupChart_comp_eq_fromSpec I U a)
    (fun ψ hψ => lTensor_injective_affineBlowupAlgebra (I.ideal U)
      (a : X.presheaf.obj (op U.1)) ψ hψ) y φ
    ((AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.toRingedSpace.sheaf M).mp hM _)
    (by exact @OXModule.stalkMapAdd_injective_of_mono _ M N φ hφ _)

/-! ### From a two-term flat resolution to the comparison morphism -/

/-- A complex concentrated in degrees `≤ 0` whose class in the derived category is a module in
degree `0` admits a quasi-isomorphism to that module placed in degree `0`. -/
private theorem exists_quasiIso_to_single {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] [K.IsGE 0] (A : C)
    (e : DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor C 0).obj A) :
    ∃ q : K ⟶ (CochainComplex.singleFunctor C 0).obj A, QuasiIso q := by
  have : (K.truncGE 0).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE 0 i hi).of_iso (K.truncGEXIso 0 i hi)
  obtain ⟨B, ⟨eB⟩⟩ := (K.truncGE 0).exists_iso_single 0
  let qB := K.πTruncGE 0 ≫ eB.hom
  have : QuasiIso qB := by dsimp [qB]; infer_instance
  let eBA : (DerivedCategory.singleFunctor C 0).obj B ≅
      (DerivedCategory.singleFunctor C 0).obj A :=
    (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
      (asIso (DerivedCategory.Q.map qB)).symm ≪≫ e
  let iBA := (DerivedCategory.singleFunctor C 0).preimageIso eBA
  exact ⟨qB ≫ (CochainComplex.singleFunctor C 0).map iBA.hom, by infer_instance⟩

/-- An additive functor preserving finite colimits keeps a quasi-isomorphism in degree `0` a
quasi-isomorphism there, for complexes concentrated in degrees `≤ 0` with target concentrated
in degree `0`. -/
private theorem quasiIsoAt_zero_map_of_isStrictlyLE {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive] [PreservesFiniteColimits G]
    {K L : CochainComplex C ℤ} (hKLE : K.IsStrictlyLE 0) (hLLE : L.IsStrictlyLE 0)
    (hLGE : L.IsStrictlyGE 0) (q : K ⟶ L) (hq0 : QuasiIsoAt q 0) :
    QuasiIsoAt ((G.mapHomologicalComplex (.up ℤ)).map q) 0 := by
  have hK : K.d 0 1 = 0 := (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  have hL₁ : L.d (-1) 0 = 0 := (L.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _
  have hL₂ : L.d 0 1 = 0 := (L.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  have hq := (quasiIsoAt_iff' q (-1) 0 1 (by simp) (by simp)).mp inferInstance
  rw [ShortComplex.quasiIso_iff_of_zeros' _ hK hL₁ hL₂] at hq
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.quasiIso_iff_of_zeros' _
      (by change G.map (K.d 0 1) = 0; rw [hK, G.map_zero])
      (by change G.map (L.d (-1) 0) = 0; rw [hL₁, G.map_zero])
      (by change G.map (L.d 0 1) = 0; rw [hL₂, G.map_zero])]
  have : Epi (q.f 0) := hq.2
  exact ⟨hq.1.map_of_epi_of_preservesCokernel G hq.2 inferInstance,
    inferInstanceAs (Epi (G.map (q.f 0)))⟩

/-- A cochain complex concentrated in degrees `≥ -1` is exact in degree `-1` if and only if its
differential `d (-1) 0` is a monomorphism. -/
private theorem exactAt_neg_one_iff_mono {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) [K.IsStrictlyGE (-1)] :
    K.ExactAt (-1) ↔ Mono (K.d (-1) 0) := by
  rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.exact_iff_mono _ ((K.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_src _ _)]
  exact Iff.rfl

/-- An additive functor preserving finite colimits keeps a quasi-isomorphism from a two-term
complex to a module in degree `0` a quasi-isomorphism, provided it keeps the differential of
the two-term complex injective. -/
private theorem quasiIso_map_of_twoTerm_of_mono {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive] [PreservesFiniteColimits G]
    {K L : CochainComplex C ℤ} (hKGE : K.IsStrictlyGE (-1)) (hKLE : K.IsStrictlyLE 0)
    (hLLE : L.IsStrictlyLE 0) (hLGE : L.IsStrictlyGE 0) (q : K ⟶ L) (hq0 : QuasiIsoAt q 0)
    (hmono : Mono (G.map (K.d (-1) 0))) :
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map q) := by
  let K' : CochainComplex D ℤ := (G.mapHomologicalComplex (.up ℤ)).obj K
  let L' : CochainComplex D ℤ := (G.mapHomologicalComplex (.up ℤ)).obj L
  refine ⟨fun i => ?_⟩
  by_cases hi : i = 0
  · subst i
    exact quasiIsoAt_zero_map_of_isStrictlyLE G hKLE hLLE hLGE q hq0
  have hL : L'.ExactAt i := by
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact L'.exactAt_of_isGE 0 i hi
    · exact L'.exactAt_of_isLE 0 i hi
  apply (quasiIsoAt_iff_exactAt' _ i hL).mpr
  by_cases hi' : i = -1
  · subst i
    exact (exactAt_neg_one_iff_mono K').mpr hmono
  · rcases lt_or_gt_of_ne hi with hi | hi
    · exact K'.exactAt_of_isGE (-1) i (by omega)
    · exact K'.exactAt_of_isLE 0 i hi

/-! ### The comparison morphism on a module of Tor dimension at most one -/

/-- The canonical comparison `Lf^* ⟶ f^*` is invertible on a complex quasi-isomorphic to one on
which it is invertible, provided the degreewise pullback of the quasi-isomorphism is again a
quasi-isomorphism. -/
private theorem isIso_derivedPullbackComparison_of_quasiIso
    {X' X : RingedSpace.{u, u}} (f : X' ⟶ X)
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (q : K ⟶ L) (hq : QuasiIso q)
    (hqp : QuasiIso (((modulePullback f).mapHomologicalComplex (.up ℤ)).map q))
    (hcK : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f).app ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj L)) := by
  let qh := (HomotopyCategory.quotient _ (.up ℤ)).map q
  have hq₀ : IsIso (DerivedCategory.Qh.map qh) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) q).mpr inferInstance
  have hq : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy
      f).map qh) := by
    show IsIso ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).map
      (((modulePullback f).mapHomologicalComplex (.up ℤ)).map q))
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).mpr inferInstance
  have hq₁ : IsIso ((DerivedCategory.Qh ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map qh) := by
    show IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
      (DerivedCategory.Qh.map qh))
    infer_instance
  have hn := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
    f).naturality qh
  have : IsIso ((DerivedCategory.Qh ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map qh ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj L)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Qh ⋙
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map qh) _

/-- **Stacks 0ESS, the derived pullback.** For an `𝒪_X`-module of Tor dimension at most one the
canonical comparison `Lb^*ℱ ⟶ b^*ℱ` along the blowup of `X` in a quasi-coherent ideal is
invertible.

A two-term flat resolution of `ℱ` exists by Stacks 08CI; it is K-flat by Stacks 06YQ, so the
comparison is invertible on it by Stacks 06YJ, and its degreewise pullback is again a resolution
of `b^*ℱ` because pullback to the blowup keeps the injection of its first term injective. -/
@[stacks 0ESS "derived pullback agrees with ordinary pullback"]
theorem isIso_derivedPullbackComparison_blowUpToBase (F : OXMod.{u, u} X.toRingedSpace)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      (blowUpToBase I).toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (OXMod.{u, u} X.toRingedSpace) (.up ℤ)).obj
        ((CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F))) := by
  obtain ⟨K, hflat, hbound, ⟨e⟩⟩ :=
    (hasTorAmplitude_iff_exists_flat_representative (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F)
      (-1) 0 (by omega)).mp htor
  have hKLE : K.IsStrictlyLE 0 := (K.isStrictlyLE_iff 0).mpr
    (fun i hi => hbound i (by simp only [Set.mem_Icc]; omega))
  have hKGE : K.IsStrictlyGE (-1) := (K.isStrictlyGE_iff (-1)).mpr
    (fun i hi => hbound i (by simp only [Set.mem_Icc]; omega))
  have hKGE0 : K.IsGE 0 := (DerivedCategory.isGE_Q_obj_iff K 0).mp
    (DerivedCategory.TStructure.t.isGE_of_iso e.symm 0)
  have hm : Mono (K.d (-1) 0) :=
    (exactAt_neg_one_iff_mono K).mp (K.exactAt_of_isGE 0 (-1) (by omega))
  obtain ⟨q, hq⟩ := exists_quasiIso_to_single K F e
  have hFLE : ((CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F).IsStrictlyLE
      0 := inferInstance
  have hFGE : ((CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F).IsStrictlyGE
      0 := inferInstance
  have hpc : PreservesColimits (modulePullback (blowUpToBase I).toLRSHom.toShHom) :=
    Adjunction.leftAdjoint_preservesColimits
      (modulePullbackPushforwardAdjunction (blowUpToBase I).toLRSHom.toShHom)
  have hqp : QuasiIso (((modulePullback (blowUpToBase I).toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).map q) :=
    quasiIso_map_of_twoTerm_of_mono (modulePullback (blowUpToBase I).toLRSHom.toShHom)
      (L := (CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F)
      hKGE hKLE hFLE hFGE q (hq.quasiIsoAt 0)
      (mono_modulePullback_blowUpToBase I (K.d (-1) 0) (hflat (-1)) hm)
  have hcK : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      (blowUpToBase I).toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (OXMod.{u, u} X.toRingedSpace) (.up ℤ)).obj K)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      (blowUpToBase I).toLRSHom.toShHom K
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat
        X.toRingedSpace K ⟨0, inferInstance⟩ hflat)
  exact isIso_derivedPullbackComparison_of_quasiIso
    (blowUpToBase I).toLRSHom.toShHom q hq hqp hcK

/-! ### Perfectness and Tor dimension of the ordinary pullback -/

/-- **Stacks 0ESS, the identification `Lb^*ℱ = b^*ℱ`.** For an `𝒪_X`-module of Tor dimension at
most one, the derived pullback to the blowup of `X` in a quasi-coherent ideal is the ordinary
pullback, placed in degree `0`. -/
@[stacks 0ESS "derived pullback is the ordinary pullback"]
noncomputable def derivedPullbackBlowUpToBaseIso (F : OXMod.{u, u} X.toRingedSpace)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (blowUpToBase I).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) ≅
      (DerivedCategory.singleFunctor (OXMod.{u, u} (blowUp I).toRingedSpace) 0).obj
        ((modulePullback (blowUpToBase I).toLRSHom.toShHom).obj F) := by
  let G := modulePullback (blowUpToBase I).toLRSHom.toShHom
  let K : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ :=
    (CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F
  let eX : (DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (OXMod.{u, u} X.toRingedSpace) (ComplexShape.up ℤ)).obj K) :=
    (DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} X.toRingedSpace) 0).app F ≪≫
      ((DerivedCategory.quotientCompQhIso (OXMod.{u, u} X.toRingedSpace)).app K).symm
  let eOrd := DerivedCategory.Qh.mapIso
      ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso (OXMod.{u, u} (blowUp I).toRingedSpace)).app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapCochainComplexSingleFunctor G 0).app F) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} (blowUp I).toRingedSpace) 0).app
        (G.obj F)).symm
  exact (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (blowUpToBase I).toLRSHom.toShHom).mapIso eX ≪≫
    @asIso _ _ _ _ _ (isIso_derivedPullbackComparison_blowUpToBase I F htor) ≪≫
    eOrd

/-- **Stacks 0ESS, perfectness.** The ordinary pullback of a perfect `𝒪_X`-module of Tor
dimension at most one to a blowup is perfect. -/
@[stacks 0ESS "the ordinary pullback is perfect"]
theorem isPerfect_modulePullback_blowUpToBase (F : OXMod.{u, u} X.toRingedSpace)
    (hperfect : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F))
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (blowUp I).toRingedSpace) 0).obj
        ((modulePullback (blowUpToBase I).toLRSHom.toShHom).obj F)) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (blowUpToBase I).toLRSHom.toShHom
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) hperfect
  exact ⟨E, hE, ⟨eE ≪≫ derivedPullbackBlowUpToBaseIso I F htor⟩⟩

/-- **Stacks 0ESS, Tor dimension.** The ordinary pullback to a blowup of an `𝒪_X`-module of Tor
dimension at most one again has Tor dimension at most one. -/
@[stacks 0ESS "the ordinary pullback has Tor dimension at most one"]
theorem hasTorAmplitude_modulePullback_blowUpToBase (F : OXMod.{u, u} X.toRingedSpace)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (blowUp I).toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (blowUp I).toRingedSpace) 0).obj
        ((modulePullback (blowUpToBase I).toLRSHom.toShHom).obj F)) (-1) 0 := by
  have htor' := Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback
    (blowUpToBase I).toLRSHom.toShHom
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0 htor
  intro P i hi
  exact (htor' P i hi).of_iso ((DerivedCategory.homologyFunctor
    (OXMod.{u, u} (blowUp I).toRingedSpace) i).mapIso
    (((Stacks.Cohomology.TorAmplitude.derTensor (blowUp I).toRingedSpace).tensor.mapIso
      (derivedPullbackBlowUpToBaseIso I F htor).symm).app
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (blowUp I).toRingedSpace) 0).obj P)))

end AlgebraicGeometry

end
