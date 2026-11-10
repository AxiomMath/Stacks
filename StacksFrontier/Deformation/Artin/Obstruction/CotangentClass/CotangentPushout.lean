module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.Artin.Infinitesimal.CanonicalElement
public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveCotangentPresentation
public import StacksFrontier.Homology.DoubleExtend

/-!
# The cotangent obstruction class: its defining condition and the pushout algebra

The cohomology of the derived tensor product with its degree shift, the naive cotangent
complex of a square-zero thickening and the evaluation map, the defining condition
`IsCotangentObstructionClass`, the pushout algebra `C = A[Ω_{P/Λ} ⊗_P A]` of a presentation
and the conormal short exact sequence of deformation situations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-! ### Cohomology of the derived tensor product -/

/-- Degree-`n` cohomology of the derived tensor product with `K`, as a functor on the whole
derived category of `A`-modules. -/
public abbrev derivedTensorCohomology (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  CochainComplex.DerivedTensor.derivedTensorProduct K ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) n

/-- The functor `M ↦ Hⁿ(K ⊗ᴸ M)` on modules is the restriction of `Hⁿ(K ⊗ᴸ -)` along the
inclusion of modules as complexes concentrated in degree zero. -/
public theorem derivedCohomology_eq (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    derivedCohomology A K n =
      DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙ derivedTensorCohomology A K n :=
  rfl

/-- The identification `H¹(K ⊗ᴸ M[1]) ≅ H²(K ⊗ᴸ M)` for a module `M`. -/
public def shiftedCohomologyIso (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (M : ModuleCat.{u} A) :
    (derivedTensorCohomology A K 1).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).obj M) ≅
      (derivedCohomology A K 2).obj M := by
  refine (derivedTensorCohomology A K 1).mapIso
      (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (1 : ℤ) (-1) 0
        (by omega)).app M).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).mapIso
      (((CochainComplex.DerivedTensor.derivedTensorProduct K).commShiftIso
        (1 : ℤ)).app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≪≫ ?_
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
      (1 : ℤ) 1 2 (by omega)).app
    ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))

/-- The natural isomorphism `H¹(K ⊗ᴸ (-)[1]) ≅ H²(K ⊗ᴸ (-))` of functors on `A`-modules,
assembled from the three natural isomorphisms whose components compose to
`shiftedCohomologyIso`. -/
public def shiftedCohomologyNatIso (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1) ⋙ derivedTensorCohomology A K 1 ≅
      derivedCohomology A K 2 :=
  Functor.isoWhiskerRight
      (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (1 : ℤ) (-1) 0
        (by omega)).symm) (derivedTensorCohomology A K 1) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
      (Functor.isoWhiskerRight
          ((CochainComplex.DerivedTensor.derivedTensorProduct K).commShiftIso (1 : ℤ))
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1) ≪≫
        Functor.isoWhiskerLeft (CochainComplex.DerivedTensor.derivedTensorProduct K)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
            (1 : ℤ) 1 2 (by omega)))

/-- The components of `shiftedCohomologyNatIso` are the isomorphisms
`shiftedCohomologyIso`. -/
public theorem shiftedCohomologyNatIso_app (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (M : ModuleCat.{u} A) :
    (shiftedCohomologyNatIso A K).app M = shiftedCohomologyIso A K M :=
  rfl

/-- The identification `H¹(K ⊗ᴸ M[1]) ≅ H²(K ⊗ᴸ M)` is natural in the module. -/
public theorem shiftedCohomologyIso_naturality (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (derivedTensorCohomology A K 1).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map f) ≫
        (shiftedCohomologyIso A K N).hom =
      (shiftedCohomologyIso A K M).hom ≫ (derivedCohomology A K 2).map f :=
  (shiftedCohomologyNatIso A K).hom.naturality f

/-- The connecting map `H¹(K ⊗ᴸ X₃) ⟶ H²(K ⊗ᴸ X₁)` of a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of `A`-modules. -/
public def boundaryMap (A : Type u) [CommRing A] (K : DerivedCategory (ModuleCat.{u} A))
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) :
    (derivedCohomology A K 1).obj Sq.X₃ ⟶ (derivedCohomology A K 2).obj Sq.X₁ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ
    ((CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.obj
      hSq.singleTriangle) 1 2 (by omega)

/-! ### The naive cotangent complex of a square-zero thickening -/

/-- For a square-zero surjection `A' → A` the conormal module of the presentation given by
`A'` itself is the kernel of the surjection. -/
public def squareZeroKernelCotangentEquiv (A' A : Type u) [CommRing A'] [CommRing A]
    [Algebra A' A] (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hq hsq
    RingHom.ker (algebraMap A' A) ≃ₗ[A]
      (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).Cotangent := by
  letI := Stacks.Smooth.kerModule hq hsq
  let P := Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq
  letI : IsScalarTower A' A (RingHom.ker (algebraMap A' A)) :=
    IsScalarTower.of_algebraMap_smul fun a i => Stacks.Smooth.kerModule_smul hq hsq a i
  let f₀ : RingHom.ker (algebraMap A' A) →ₗ[A'] P.Cotangent :=
    Algebra.Extension.Cotangent.mk (P := P)
  refine LinearEquiv.ofBijective (f₀.extendScalarsOfSurjective hq) ⟨?_, ?_⟩
  · intro x y h
    have hz : f₀ (x - y) = 0 := by
      change f₀.extendScalarsOfSurjective hq (x - y) = 0
      rw [map_sub, h, sub_self]
    have hs := (Algebra.Extension.Cotangent.mk_eq_zero_iff (P := P) (x - y)).mp hz
    rw [show P.ker ^ 2 = ⊥ from hsq] at hs
    exact sub_eq_zero.mp (Subtype.ext hs)
  · exact Algebra.Extension.Cotangent.mk_surjective

/-- The comparison in the derived category between the naive cotangent complex of `A` over
`A'` and the two-term complex of the presentation given by a surjection `A' → A`. -/
public def relativeNaiveCotangentSurjectionMap (A' A : Type u) [CommRing A'] [CommRing A]
    [Algebra A' A] (hq : Function.Surjective (algebraMap A' A)) :
    derivedNaiveCotangentComplex A' A ⟶
      DerivedCategory.Q.obj
        (HomologicalComplex.double
          (ModuleCat.ofHom
            (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).cotangentComplex)
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)) := by
  let P := Algebra.Generators.self A' A
  let Q := Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq
  let g := Algebra.Extension.defaultHom A' A Q
  let f₁ : P.toExtension.Cotangent →ₗ[A] Q.Cotangent := Algebra.Extension.Cotangent.map g
  let f₀ : P.toExtension.CotangentSpace →ₗ[A] Q.CotangentSpace :=
    Algebra.Extension.CotangentSpace.map g
  let hrel : (ComplexShape.up ℤ).Rel (-1) 0 := rfl
  have hne : (-1 : ℤ) ≠ 0 := by omega
  exact DerivedCategory.Q.map (HomologicalComplex.mkHomFromDouble hrel hne
    (ModuleCat.ofHom f₁ ≫
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom Q.cotangentComplex) hrel).inv)
    (ModuleCat.ofHom f₀ ≫
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom Q.cotangentComplex) hrel hne).inv)
    (by
      rw [HomologicalComplex.double_d _ _ hne]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hmap : ModuleCat.ofHom f₁ ≫ ModuleCat.ofHom Q.cotangentComplex =
          ModuleCat.ofHom P.toExtension.cotangentComplex ≫ ModuleCat.ofHom f₀ :=
        ModuleCat.hom_ext <| LinearMap.ext fun x =>
          (Algebra.Extension.CotangentSpace.map_cotangentComplex g x).symm
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫
          (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom Q.cotangentComplex) hrel hne).inv)
        hmap)
    (fun k hk => by
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega)]
      simp))

/-- The canonical morphism `NL_{A/A'} ⟶ I[1]` attached to a square-zero surjection `A' → A`
with kernel `I`. -/
public def squareZeroCotangentClass (A' A : Type u) [CommRing A'] [CommRing A] [Algebra A' A]
    (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hq hsq
    derivedNaiveCotangentComplex A' A ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).obj
        (ModuleCat.of A (RingHom.ker (algebraMap A' A))) := by
  letI := Stacks.Smooth.kerModule hq hsq
  let d :=
    ModuleCat.ofHom (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).cotangentComplex
  let hrel : (ComplexShape.up ℤ).Rel (-1) 0 := rfl
  refine relativeNaiveCotangentSurjectionMap A' A hq ≫ DerivedCategory.Q.map
    (HomologicalComplex.mkHomToSingle
      ((HomologicalComplex.doubleXIso₀ d hrel).hom ≫
        ModuleCat.ofHom (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap) ?_)
  intro i hi
  have hi' : i + 1 = -1 := hi
  exact (HomologicalComplex.isZero_double_X d hrel i (by omega) (by omega)).eq_of_src _ _

/-- The extension class `NL_{A/Λ} ⟶ I[1]` of a square-zero thickening `A' → A` of
`Λ`-algebras, the base-change morphism followed by the square-zero identification. -/
public def cotangentExtensionClass (Λ A' A : Type u) [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] [Algebra A' A] [IsScalarTower Λ A' A]
    (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hq hsq
    derivedNaiveCotangentComplex Λ A ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).obj
        (ModuleCat.of A (RingHom.ker (algebraMap A' A))) :=
  naiveCotangentBaseMap Λ A' A ≫ squareZeroCotangentClass A' A hq hsq

/-- Evaluation of a class on `NL_{A/Λ}` at a square-zero thickening `A' → A` with kernel `I`,
the map `H¹(K ⊗ᴸ NL_{A/Λ}) ⟶ H²(K ⊗ᴸ I)` induced by the extension class. -/
public def obstructionEvaluation (Λ A' A : Type u) [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] [Algebra A' A] [IsScalarTower Λ A' A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hq hsq
    (derivedTensorCohomology A K 1).obj (derivedNaiveCotangentComplex Λ A) ⟶
      (derivedCohomology A K 2).obj (ModuleCat.of A (RingHom.ker (algebraMap A' A))) :=
  letI := Stacks.Smooth.kerModule hq hsq
  (derivedTensorCohomology A K 1).map (cotangentExtensionClass Λ A' A hq hsq) ≫
    (shiftedCohomologyIso A K (ModuleCat.of A (RingHom.ker (algebraMap A' A)))).hom

/-! ### Trivial square-zero extensions in the site -/

/-- A module finite over `A` has its trivial square-zero extension `A[M]` in any big fppf
site containing `Spec A`, since `A[M]` is then a finite `A`-algebra. -/
public theorem squareZero_mem_site_of_finite (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (M : ModuleCat.{u} A) (hA : B.Contains (Spec (.of A))) (hM : Module.Finite A M) :
    B.Contains (Spec (squareZeroRing A M)) := by
  have : Module.Finite A M := hM
  have hfin : Module.Finite A (TrivSqZeroExt A M) := by
    change Module.Finite A (A × (M : Type u))
    infer_instance
  have : Algebra.FiniteType A (TrivSqZeroExt A M) := Module.Finite.finiteType _
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A
    (TrivSqZeroExt A M) hA

/-- For `A` of finite type over `Λ` the trivial square-zero extension `A[Ω_{A/Λ}]` occurs in
any big fppf site containing `Spec A`. -/
public theorem differentialsSquareZero_mem_site (Λ A : Type u) [CommRing Λ] [CommRing A]
    [Algebra Λ A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (hft : Algebra.FiniteType Λ A) :
    B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))) := by
  have : Algebra.FiniteType Λ A := hft
  exact squareZero_mem_site_of_finite A B (differentialsModule Λ A) hA
    (by change Module.Finite A Ω[A⁄Λ]; infer_instance)

/-! ### Deformation situations that retract onto their closed subscheme -/

section Retraction

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

include hp in
/-- An object over `Spec A` lifts along any thickening of `Spec A` that retracts onto
`Spec A`: the lift is the pullback of the object along the retraction. -/
public def liftOfRetraction {Y : BigFppfOver B S hS}
    (a : algebraOver A B S hS toS hA ⟶ Y) (r : Y ⟶ algebraOver A B S hS toS hA)
    (ha : a ≫ r = 𝟙 (algebraOver A B S hS toS hA)) :
    (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a) : Under (p.obj x)) :=
  letI : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  Functor.pullbackFiber (Under.post p) (liftId A B S hS toS hA p x hx)
    (Under.homMk r (by
      change (eqToHom hx ≫ a) ≫ r = eqToHom hx
      rw [Category.assoc, ha, Category.comp_id]))

end Retraction

/-! ### The cotangent obstruction class -/

section Condition

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)

/-- A square-zero thickening whose closed immersion admits a retraction over the base carries
no obstruction, because `x` then lifts by pulling back along the retraction. -/
public theorem obstruction_eq_zero_of_retraction (A' : Type u) [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A')
    (r : (Over.mk D.toS' : BigFppfOver B S hS) ⟶ algebraOver A B S hS toS hA)
    (hr : D.arrow ≫ r = 𝟙 (algebraOver A B S hS toS hA)) :
    sit.obstruction A' D = 0 :=
  (sit.obstruction_iff_lift A' D).1
    ⟨liftOfRetraction A B S hS toS hA p sit.x sit.hx sit.fibered D.arrow r hr⟩

/-- A class on `NL_{A/Λ}` is a *cotangent obstruction class* for `x` when its evaluation at
every deformation situation is the obstruction element of that situation, and its image in
`H¹(K ⊗ᴸ Ω_{A/Λ})` is the canonical element of the tangent functor. -/
public def IsCotangentObstructionClass
    (ξ : (derivedTensorCohomology A sit.K 1).obj (derivedNaiveCotangentComplex Λ A)) : Prop :=
  (∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
      ∃ f : Λ →+* A',
        Spec.map (CommRingCat.ofHom f) ≫ sit.affineOpen = B.inclusion.map D.toS' ∧
        ∃ hf : D.q.comp f = algebraMap Λ A,
        letI : Algebra Λ A' := f.toAlgebra
        letI : Algebra A' A := D.q.toAlgebra
        letI : IsScalarTower Λ A' A :=
          IsScalarTower.of_algebraMap_eq fun r =>
            (congrArg (fun g : Λ →+* A => g r) hf).symm
        obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1
            D.squareZeroSurjection.2 ξ =
          sit.obstruction A' D) ∧
    sit.tangentMap
        (differentialsSiteModule Λ A B
          (differentialsSquareZero_mem_site Λ A B hA sit.finiteType))
        (canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar
          (differentialsSquareZero_mem_site Λ A B hA sit.finiteType)
          sit.affineOpen sit.factorization).element =
      (derivedTensorCohomology A sit.K 1).map (naiveCotangentToDifferentials Λ A) ξ

end Condition

/-! ### The pushout algebra of a presentation -/

section CotangentPushout

open TensorProduct

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The cotangent space of an extension, as an object of the module category. -/
public abbrev cotangentSpaceModule (E : Algebra.Extension.{u} Λ A) :
    ModuleCat.{u} A :=
  ModuleCat.of A E.CotangentSpace

/-- The pushout algebra of a presentation: the trivial square-zero extension of `A` by the
cotangent space of the presentation. -/
public abbrev cotangentPushout (E : Algebra.Extension.{u} Λ A) : Type u :=
  TrivSqZeroExt A (cotangentSpaceModule E)

/-- Moving a scalar of the presentation ring across the tensor product defining the
cotangent space turns it into its image in `A`. -/
public theorem one_tmul_smul (E : Algebra.Extension.{u} Λ A) (r : E.Ring)
    (ω : Ω[E.Ring⁄Λ]) :
    (1 : A) ⊗ₜ[E.Ring] (r • ω) =
      algebraMap E.Ring A r • ((1 : A) ⊗ₜ[E.Ring] ω) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1
  simp [Algebra.smul_def, smul_eq_mul]

/-- The underlying function `f ↦ (α f, df ⊗ 1)` of the canonical map of a presentation into
the pushout algebra. -/
public def cotangentPushoutFun (E : Algebra.Extension.{u} Λ A) (f : E.Ring) :
    cotangentPushout E :=
  TrivSqZeroExt.inl (algebraMap E.Ring A f) +
    TrivSqZeroExt.inr ((1 : A) ⊗ₜ[E.Ring] KaehlerDifferential.D Λ E.Ring f)

/-- The `A`-component of `cotangentPushoutFun E f` is the image of `f` in `A`. -/
@[simp] public theorem cotangentPushoutFun_fst (E : Algebra.Extension.{u} Λ A) (f : E.Ring) :
    (cotangentPushoutFun E f).fst = algebraMap E.Ring A f := by
  simp [cotangentPushoutFun]

/-- The module component of `cotangentPushoutFun E f` is `1 ⊗ df`. -/
@[simp] public theorem cotangentPushoutFun_snd (E : Algebra.Extension.{u} Λ A) (f : E.Ring) :
    (cotangentPushoutFun E f).snd =
      (1 : A) ⊗ₜ[E.Ring] KaehlerDifferential.D Λ E.Ring f := by
  simp [cotangentPushoutFun]

/-- The canonical map `P → A[Ω_{P/Λ} ⊗_P A]` of a presentation, `f ↦ (α f, df ⊗ 1)`. -/
public def cotangentPushoutMap (E : Algebra.Extension.{u} Λ A) :
    E.Ring →+* cotangentPushout E where
  toFun := cotangentPushoutFun E
  map_one' := by ext <;> simp [cotangentPushoutFun]
  map_zero' := by ext <;> simp [cotangentPushoutFun]
  map_add' f g := by ext <;> simp [cotangentPushoutFun, tmul_add]
  map_mul' f g := by
    ext
    · simp [cotangentPushoutFun]
    · simp only [cotangentPushoutFun, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, zero_add]
      rw [Derivation.leibniz, tmul_add, one_tmul_smul E f, one_tmul_smul E g]
      simp [op_smul_eq_smul, add_comm]

/-- The ring map `cotangentPushoutMap E` is given by `cotangentPushoutFun E`. -/
@[simp] public theorem cotangentPushoutMap_apply (E : Algebra.Extension.{u} Λ A)
    (f : E.Ring) : cotangentPushoutMap E f = cotangentPushoutFun E f := rfl

/-- The projection of the pushout algebra onto `A`. -/
public abbrev cotangentPushoutProj (E : Algebra.Extension.{u} Λ A) :
    cotangentPushout E →+* A :=
  (TrivSqZeroExt.fstHom A A (cotangentSpaceModule E)).toRingHom

/-- The pushout algebra is a square-zero thickening of `A`. -/
public theorem isDeformationSituation_cotangentPushout
    (E : Algebra.Extension.{u} Λ A) :
    IsDeformationSituation (cotangentPushoutProj E) :=
  ⟨fun a => ⟨TrivSqZeroExt.inl a, by simp⟩,
    TrivSqZeroExt.kerIdeal_sq A (cotangentSpaceModule E)⟩

/-- The canonical map of the presentation into the pushout algebra lies over `A`. -/
public theorem cotangentPushoutProj_comp_map (E : Algebra.Extension.{u} Λ A) :
    (cotangentPushoutProj E).comp (cotangentPushoutMap E) = algebraMap E.Ring A := by
  ext f
  exact cotangentPushoutFun_fst E f

/-- The canonical map into the pushout algebra kills the square of the kernel, because the
image of the kernel lands in the square-zero ideal. -/
public theorem ker_sq_le_ker_cotangentPushoutMap (E : Algebra.Extension.{u} Λ A) :
    E.ker ^ 2 ≤ RingHom.ker (cotangentPushoutMap E) := by
  rw [pow_two]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  have ha' : algebraMap E.Ring A a = 0 := ha
  have hb' : algebraMap E.Ring A b = 0 := hb
  rw [RingHom.mem_ker, map_mul]
  ext <;> simp [cotangentPushoutFun, ha', hb']

/-- `P/J² → A` is a square-zero thickening: the infinitesimal extension of a presentation is
a deformation situation. -/
public theorem isDeformationSituation_infinitesimal (E : Algebra.Extension.{u} Λ A) :
    IsDeformationSituation (algebraMap E.infinitesimal.Ring A) := by
  refine ⟨E.infinitesimal.algebraMap_surjective, ?_⟩
  change E.infinitesimal.ker ^ 2 = ⊥
  rw [E.ker_infinitesimal]
  exact Ideal.cotangentIdeal_square _

/-- The canonical map `P/J² → C` of the proof of 07YY: the map of the presentation into the
pushout algebra, descended along the quotient by `J²`. -/
public def cotangentPushoutInfinitesimalMap (E : Algebra.Extension.{u} Λ A) :
    E.infinitesimal.Ring →+* cotangentPushout E :=
  Ideal.Quotient.lift (E.ker ^ 2) (cotangentPushoutMap E)
    fun _ ha => ker_sq_le_ker_cotangentPushoutMap E ha

/-- On the class of `f` in `P/J²`, `cotangentPushoutInfinitesimalMap E` is
`cotangentPushoutMap E f`. -/
@[simp] public theorem cotangentPushoutInfinitesimalMap_mk (E : Algebra.Extension.{u} Λ A)
    (f : E.Ring) :
    cotangentPushoutInfinitesimalMap E (Ideal.Quotient.mk (E.ker ^ 2) f) =
      cotangentPushoutMap E f :=
  rfl

/-- The map `P/J² → C` lies over `A`. -/
public theorem cotangentPushoutProj_comp_infinitesimalMap (E : Algebra.Extension.{u} Λ A) :
    (cotangentPushoutProj E).comp (cotangentPushoutInfinitesimalMap E) =
      algebraMap E.infinitesimal.Ring A := by
  ext f
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
  exact cotangentPushoutFun_fst E g

/-- The trivial square-zero extension `A[M]` of `A` by a module, with its projection to `A`,
is a square-zero thickening. -/
public theorem isDeformationSituation_squareZeroExt (M : ModuleCat.{u} A) :
    IsDeformationSituation (TrivSqZeroExt.fstHom A A M).toRingHom :=
  ⟨fun a => ⟨TrivSqZeroExt.inl a, by simp⟩, TrivSqZeroExt.kerIdeal_sq A M⟩

/-- The map `A[M] → A[N]` of trivial square-zero extensions induced by a map of modules. -/
public def squareZeroExtMap {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    TrivSqZeroExt A M →+* TrivSqZeroExt A N :=
  (TrivSqZeroExt.map f.hom).toRingHom

/-- `A[M] → A[N]` is surjective when the map of modules is. -/
public theorem squareZeroExtMap_surjective {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (hf : Function.Surjective f.hom) : Function.Surjective (squareZeroExtMap f) := by
  intro y
  obtain ⟨m, hm⟩ := hf y.snd
  exact ⟨TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr m, by
    ext <;> simp [squareZeroExtMap, hm]⟩

/-- `A[M] → A[N]` lies over `A`. -/
public theorem fstHom_comp_squareZeroExtMap {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    ((TrivSqZeroExt.fstHom A A N).toRingHom).comp (squareZeroExtMap f) =
      (TrivSqZeroExt.fstHom A A M).toRingHom := by
  ext x
  simp [squareZeroExtMap]

/-- The surjection `C → A[Ω_{A/Λ}]` of the proof of 07YY, induced by the conormal surjection
of the cotangent space of the presentation onto the module of differentials. -/
public def cotangentPushoutToDifferentials (E : Algebra.Extension.{u} Λ A) :=
  squareZeroExtMap (M := cotangentSpaceModule E) (N := differentialsModule Λ A)
    (ModuleCat.ofHom E.toKaehler)

/-- The surjection `C → A[Ω_{A/Λ}]` is surjective, because the cotangent space of a
presentation surjects onto the module of differentials. -/
public theorem cotangentPushoutToDifferentials_surjective
    (E : Algebra.Extension.{u} Λ A) :
    Function.Surjective (cotangentPushoutToDifferentials E) :=
  squareZeroExtMap_surjective _ E.toKaehler_surjective

/-- The map `squareZeroExtMap f` is the identity on the `A`-component. -/
@[simp] public theorem fst_squareZeroExtMap {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (x : TrivSqZeroExt A M) : (squareZeroExtMap f x).fst = x.fst := by
  simp [squareZeroExtMap]

/-- The map `squareZeroExtMap f` applies `f` to the module component. -/
@[simp] public theorem snd_squareZeroExtMap {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (x : TrivSqZeroExt A M) : (squareZeroExtMap f x).snd = f.hom x.snd := by
  simp [squareZeroExtMap]

/-- The surjection `C → A[Ω_{A/Λ}]` is the identity on the `A`-component. -/
@[simp] public theorem fst_cotangentPushoutToDifferentials
    (E : Algebra.Extension.{u} Λ A) (x : cotangentPushout E) :
    (cotangentPushoutToDifferentials E x).fst = x.fst :=
  fst_squareZeroExtMap _ x

/-- The surjection `C → A[Ω_{A/Λ}]` applies `Ω_{P/Λ} ⊗_P A ⟶ Ω_{A/Λ}` to the module
component. -/
@[simp] public theorem snd_cotangentPushoutToDifferentials
    (E : Algebra.Extension.{u} Λ A) (x : cotangentPushout E) :
    (cotangentPushoutToDifferentials E x).snd = E.toKaehler x.snd :=
  snd_squareZeroExtMap _ x

/-! ### The conormal short exact sequence of deformation situations -/

/-- The trivial square-zero extension `A[M]` of `A` by a module of the module category. -/
@[ega "0 18.2.3" "special case"]
public abbrev squareZeroExt (M : ModuleCat.{u} A) : Type u := TrivSqZeroExt A M

/-- The projection `A[M] → A` of a trivial square-zero extension. -/
public abbrev squareZeroExtProj (M : ModuleCat.{u} A) : squareZeroExt M →+* A :=
  (TrivSqZeroExt.fstHom A A M).toRingHom

/-- The image `C'` of `P/J²` in the pushout algebra `C`, a subring whose kernel over `A` is
the image of the conormal module `J/J²` in `Ω_{P/Λ} ⊗_P A`. -/
public abbrev cotangentPushoutImage (E : Algebra.Extension.{u} Λ A) :
    Subring (cotangentPushout E) :=
  (cotangentPushoutInfinitesimalMap E).range

/-- The projection `C' → A`, the restriction of the projection of the pushout algebra. -/
public abbrev cotangentPushoutImageProj (E : Algebra.Extension.{u} Λ A) :
    cotangentPushoutImage E →+* A :=
  (cotangentPushoutProj E).comp (cotangentPushoutImage E).subtype

/-- `C' → A` is a square-zero thickening of `A`: it is surjective because `P/J² → A` is, and
its kernel squares to zero inside the square-zero ideal of `C`. -/
public theorem isDeformationSituation_cotangentPushoutImage
    (E : Algebra.Extension.{u} Λ A) :
    IsDeformationSituation (cotangentPushoutImageProj E) := by
  constructor
  · intro a
    obtain ⟨f, hf⟩ := E.infinitesimal.algebraMap_surjective a
    refine ⟨⟨cotangentPushoutInfinitesimalMap E f, RingHom.mem_range_self _ f⟩, ?_⟩
    exact (DFunLike.congr_fun (cotangentPushoutProj_comp_infinitesimalMap E) f).trans hf
  · rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    have hx' : (x : cotangentPushout E).fst = 0 := hx
    have hy' : (y : cotangentPushout E).fst = 0 := hy
    have hxy : (x : cotangentPushout E) * (y : cotangentPushout E) = 0 := by
      ext <;> simp [hx', hy']
    rw [Ideal.mem_bot]
    exact Subtype.ext (by simpa using hxy)

/-- The surjection `C ⟶ A[M]` of commutative rings induced by a map out of the cotangent
space of the presentation; for the conormal surjection onto `Ω_{A/Λ}` this is the map
`C ⟶ A[Ω_{A/Λ}]` of the proof of 07YY. -/
public abbrev cotangentPushoutHom (E : Algebra.Extension.{u} Λ A) {M : ModuleCat.{u} A}
    (f : cotangentSpaceModule E ⟶ M) : cotangentPushout E →+* squareZeroExt M :=
  (TrivSqZeroExt.map f.hom).toRingHom

/-- The map `cotangentPushoutHom E f` is the identity on the `A`-component. -/
@[simp] public theorem fst_cotangentPushoutHom (E : Algebra.Extension.{u} Λ A)
    {M : ModuleCat.{u} A} (f : cotangentSpaceModule E ⟶ M) (x : cotangentPushout E) :
    (cotangentPushoutHom E f x).fst = x.fst :=
  TrivSqZeroExt.fst_map f.hom x

/-- The map `cotangentPushoutHom E f` applies `f` to the module component. -/
@[simp] public theorem snd_cotangentPushoutHom (E : Algebra.Extension.{u} Λ A)
    {M : ModuleCat.{u} A} (f : cotangentSpaceModule E ⟶ M) (x : cotangentPushout E) :
    (cotangentPushoutHom E f x).snd = f.hom x.snd :=
  TrivSqZeroExt.snd_map f.hom x

/-- The kernel of the conormal surjection `Ω_{P/Λ} ⊗_P A ⟶ Ω_{A/Λ}` of a presentation is
the image of the conormal module `J/J²`. -/
public theorem toKaehler_eq_zero_iff (E : Algebra.Extension.{u} Λ A)
    (v : E.CotangentSpace) :
    E.toKaehler v = 0 ↔ ∃ c, E.cotangentComplex c = v :=
  E.exact_cotangentComplex_toKaehler v

/-- An element of the kernel of `C → A` lies in `C'` exactly when its module component is in
the image of the conormal module `J/J²`. -/
private theorem exists_image_eq_iff (E : Algebra.Extension.{u} Λ A)
    (y : RingHom.ker (cotangentPushoutProj E)) :
    (∃ z : RingHom.ker (cotangentPushoutImageProj E), (z.1 : cotangentPushout E) = y.1) ↔
      ∃ c, E.cotangentComplex c = (y.1 : cotangentPushout E).snd := by
  have hy : (y : cotangentPushout E).fst = 0 := y.2
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := RingHom.mem_range.1 z.1.2
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hgy : cotangentPushoutFun E g = (y : cotangentPushout E) := by
      rw [← hz, ← hw, cotangentPushoutInfinitesimalMap_mk, cotangentPushoutMap_apply]
    have hg : algebraMap E.Ring A g = 0 := by
      rw [← cotangentPushoutFun_fst E g, hgy]; exact hy
    exact ⟨Algebra.Extension.Cotangent.mk ⟨g, hg⟩, by
      rw [Algebra.Extension.cotangentComplex_mk, ← cotangentPushoutFun_snd E g, hgy]⟩
  · rintro ⟨c, hc⟩
    obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
    have hg : algebraMap E.Ring A g.1 = 0 := g.2
    have hval : cotangentPushoutInfinitesimalMap E (Ideal.Quotient.mk (E.ker ^ 2) g.1) =
        (y : cotangentPushout E) := by
      rw [cotangentPushoutInfinitesimalMap_mk, cotangentPushoutMap_apply]
      ext
      · rw [cotangentPushoutFun_fst, hg, hy]
      · rw [cotangentPushoutFun_snd, ← hc, Algebra.Extension.cotangentComplex_mk]
    exact ⟨⟨⟨(y : cotangentPushout E), RingHom.mem_range.2 ⟨_, hval⟩⟩, hy⟩, rfl⟩

/-- **The short exact sequence of deformation situations of the proof of 07YY.** Let
`f : Ω_{P/Λ} ⊗_P A ⟶ M` be surjective with kernel the image of the conormal module `J/J²`.
Then the triple `(x, A[M] → A) → (x, C → A) → (x, C' → A)` is a short exact sequence of
deformation situations, its kernel sequence being
`0 → Im(J/J² → Ω_{P/Λ} ⊗_P A) → Ω_{P/Λ} ⊗_P A → M → 0`. -/
public theorem isShortExactSequence_cotangentPushout (E : Algebra.Extension.{u} Λ A)
    (M : ModuleCat.{u} A) (f : cotangentSpaceModule E ⟶ M)
    (hf : Function.Surjective f.hom)
    (hfker : ∀ v : E.CotangentSpace, f.hom v = 0 ↔ ∃ c, E.cotangentComplex c = v) :
    IsShortExactSequence (squareZeroExtProj M) (cotangentPushoutProj E)
      (cotangentPushoutImageProj E) (cotangentPushoutHom E f)
      (cotangentPushoutImage E).subtype := by
  refine ⟨isDeformationSituation_squareZeroExt M,
    isDeformationSituation_cotangentPushout E,
    isDeformationSituation_cotangentPushoutImage E,
    RingHom.ext fun x => fst_cotangentPushoutHom E f x, rfl,
    fun z w h => Subtype.ext (Subtype.ext h), ?_, ?_⟩
  · intro y
    have hy : (y : cotangentPushout E).fst = 0 := y.2
    refine Iff.trans ?_ (exists_image_eq_iff E y).symm
    rw [← hfker, TrivSqZeroExt.ext_iff]
    simp [hy]
  · intro x
    have hx : (x : squareZeroExt M).fst = 0 := x.2
    obtain ⟨v, hv⟩ := hf (x : squareZeroExt M).snd
    refine ⟨⟨TrivSqZeroExt.inr v, ?_⟩, ?_⟩
    · rw [RingHom.mem_ker]
      exact TrivSqZeroExt.fst_inr A v
    · refine TrivSqZeroExt.ext ?_ ?_
      · rw [fst_cotangentPushoutHom, TrivSqZeroExt.fst_inr, hx]
      · rw [snd_cotangentPushoutHom, TrivSqZeroExt.snd_inr, hv]

/-- **The conormal short exact sequence of deformation situations of the proof of 07YY.**
The triple `(x, A[Ω_{A/Λ}] → A) → (x, C → A) → (x, C' → A)` is short exact, its kernel
sequence being the conormal sequence
`0 → Im(J/J² → Ω_{P/Λ} ⊗_P A) → Ω_{P/Λ} ⊗_P A → Ω_{A/Λ} → 0`. -/
public theorem isShortExactSequence_cotangentPushoutToDifferentials
    (E : Algebra.Extension.{u} Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    IsShortExactSequence (squareZeroExtProj (differentialsModule Λ A))
      (cotangentPushoutProj E) (cotangentPushoutImageProj E)
      (cotangentPushoutHom E (ModuleCat.ofHom E.toKaehler))
      (cotangentPushoutImage E).subtype :=
  isShortExactSequence_cotangentPushout E (differentialsModule Λ A)
    (ModuleCat.ofHom E.toKaehler) E.toKaehler_surjective (toKaehler_eq_zero_iff E)

/-- **The surjection `C ⟶ C̄ = A[Ω_{A/Λ}]` of the proof of 07YY**, `(a, v) ↦ (a, da - v̄)`.
Under the realization of the pushout algebra as `A[Ω_{P/Λ} ⊗_P A]` the source's surjection is
twisted by the universal derivation; it is a ring map by the Leibniz rule, and the twist is
what makes the section `A ⟶ C` followed by it the map `(1, d)`. -/
public def cotangentPushoutToDifferentialsTwisted (E : Algebra.Extension.{u} Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    cotangentPushout E →+* squareZeroExt (differentialsModule Λ A) :=
  letI := oppositeModule A (differentialsModule Λ A)
  letI := centralScalar A (differentialsModule Λ A)
  { toFun := fun x => TrivSqZeroExt.inl x.fst +
      TrivSqZeroExt.inr (KaehlerDifferential.D Λ A x.fst - E.toKaehler x.snd)
    map_one' := by ext <;> simp
    map_zero' := by ext <;> simp
    map_add' := fun x y => by
      ext <;> simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
      abel
    map_mul' := fun x y => by
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
          TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
          zero_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, map_add,
          Derivation.leibniz, op_smul_eq_smul, LinearMap.map_smul, smul_sub]
        abel }

/-- The twisted map `cotangentPushoutToDifferentialsTwisted E` is the identity on the
`A`-component. -/
@[simp] public theorem fst_cotangentPushoutToDifferentialsTwisted
    (E : Algebra.Extension.{u} Λ A) (x : cotangentPushout E) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    (cotangentPushoutToDifferentialsTwisted E x).fst = x.fst := by
  simp [cotangentPushoutToDifferentialsTwisted]

/-- The module component of `cotangentPushoutToDifferentialsTwisted E x` is
`d(x.fst)` minus the image of `x.snd` in `Ω_{A/Λ}`. -/
@[simp] public theorem snd_cotangentPushoutToDifferentialsTwisted
    (E : Algebra.Extension.{u} Λ A) (x : cotangentPushout E) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    (cotangentPushoutToDifferentialsTwisted E x).snd =
      KaehlerDifferential.D Λ A x.fst - E.toKaehler x.snd := by
  simp [cotangentPushoutToDifferentialsTwisted]

/-- **The conormal short exact sequence of deformation situations of the proof of 07YY**, for
the derivation-twisted surjection `C ⟶ C̄`. The triple
`(x, A[Ω_{A/Λ}] → A) → (x, C → A) → (x, C' → A)` is short exact: the twisted surjection has
the same kernel conditions as the untwisted one, the twist being invisible on elements with
vanishing image in `A`. -/
public theorem isShortExactSequence_cotangentPushoutToDifferentialsTwisted
    (E : Algebra.Extension.{u} Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    IsShortExactSequence (squareZeroExtProj (differentialsModule Λ A))
      (cotangentPushoutProj E) (cotangentPushoutImageProj E)
      (cotangentPushoutToDifferentialsTwisted E)
      (cotangentPushoutImage E).subtype := by
  refine ⟨isDeformationSituation_squareZeroExt (differentialsModule Λ A),
    isDeformationSituation_cotangentPushout E,
    isDeformationSituation_cotangentPushoutImage E,
    RingHom.ext fun x => fst_cotangentPushoutToDifferentialsTwisted E x, rfl,
    fun z w h => Subtype.ext (Subtype.ext h), ?_, ?_⟩
  · intro y
    have hy : (y : cotangentPushout E).fst = 0 := y.2
    refine Iff.trans ?_ (exists_image_eq_iff E y).symm
    rw [← toKaehler_eq_zero_iff, TrivSqZeroExt.ext_iff, fst_cotangentPushoutToDifferentialsTwisted,
      snd_cotangentPushoutToDifferentialsTwisted, hy, map_zero, TrivSqZeroExt.fst_zero,
      TrivSqZeroExt.snd_zero, zero_sub, neg_eq_zero, and_iff_right rfl]
  · intro x
    have hx : (x : squareZeroExt (differentialsModule Λ A)).fst = 0 := x.2
    obtain ⟨v, hv⟩ := E.toKaehler_surjective
      (-(x : squareZeroExt (differentialsModule Λ A)).snd)
    refine ⟨⟨TrivSqZeroExt.inr v, ?_⟩, ?_⟩
    · rw [RingHom.mem_ker]
      exact TrivSqZeroExt.fst_inr A v
    · refine TrivSqZeroExt.ext ?_ ?_
      · rw [fst_cotangentPushoutToDifferentialsTwisted, TrivSqZeroExt.fst_inr, hx]
      · rw [snd_cotangentPushoutToDifferentialsTwisted, TrivSqZeroExt.fst_inr,
          TrivSqZeroExt.snd_inr, map_zero, hv, zero_sub, neg_neg]

end CotangentPushout

end Deformation.Artin

end
