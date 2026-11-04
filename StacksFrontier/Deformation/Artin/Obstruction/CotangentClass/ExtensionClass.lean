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
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.CotangentPushout
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.Thickenings

/-!
# The extension class of a thickening from a presentation

The infinitesimal extension of a presentation inside a deformation situation, the derived
tensor product of the triangle of a presentation, the vanishing of the obstruction of the
pushout algebra, and the extension class of a thickening computed from an arbitrary
presentation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-! ### The infinitesimal extension of a presentation inside a deformation situation -/

section Presentation

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A] {ι : Type u}

/-- The map `P ⟶ A'` of the polynomial ring of a presentation of `A` into a square-zero
thickening of `A` over `Λ`, obtained by lifting each generator along the surjection. -/
public def presentationLift (P : Algebra.Generators Λ A ι) {A' : Type u} [CommRing A']
    (q : A' →+* A) (hq : Function.Surjective q) (f : Λ →+* A') :
    P.toExtension.Ring →+* A' :=
  MvPolynomial.eval₂Hom f fun i => (hq (P.val i)).choose

/-- The map `P ⟶ A'` lies over `A`, since it was built from preimages of the generators. -/
public theorem comp_presentationLift (P : Algebra.Generators Λ A ι) {A' : Type u}
    [CommRing A'] (q : A' →+* A) (hq : Function.Surjective q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) :
    q.comp (presentationLift P q hq f) = algebraMap P.toExtension.Ring A := by
  have hf : ∀ r : Λ, q (f r) = algebraMap Λ A r := fun r =>
    congrArg (fun g : Λ →+* A => g r) hqf
  have h : q.comp (MvPolynomial.eval₂Hom f fun i => (hq (P.val i)).choose) =
      (algebraMap P.Ring A : P.Ring →+* A) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [P.algebraMap_eq]
      simpa using hf r
    · rw [P.algebraMap_eq]
      simpa using (hq (P.val i)).choose_spec
  exact h

/-- Pointwise form of the compatibility of `P ⟶ A'` with the augmentations to `A`. -/
public theorem presentationLift_spec (P : Algebra.Generators Λ A ι) {A' : Type u}
    [CommRing A'] (q : A' →+* A) (hq : Function.Surjective q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) (x : P.toExtension.Ring) :
    q (presentationLift P q hq f x) = algebraMap P.toExtension.Ring A x :=
  congrArg (fun g : P.toExtension.Ring →+* A => g x) (comp_presentationLift P q hq f hqf)

/-- The map `P ⟶ A'` kills the square of the kernel of the presentation: the kernel is carried
into the square-zero kernel of `A' ⟶ A`. -/
public theorem ker_sq_le_ker_presentationLift (P : Algebra.Generators Λ A ι) {A' : Type u}
    [CommRing A'] (q : A' →+* A) (hq : Function.Surjective q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) (hsq : RingHom.ker q ^ 2 = ⊥) :
    P.toExtension.ker ^ 2 ≤ RingHom.ker (presentationLift P q hq f) := by
  rw [pow_two]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  have hmem : ∀ c ∈ P.toExtension.ker, presentationLift P q hq f c ∈ RingHom.ker q := fun c hc => by
    rw [RingHom.mem_ker, presentationLift_spec P q hq f hqf]
    exact hc
  have hmul : presentationLift P q hq f a * presentationLift P q hq f b ∈
      RingHom.ker q ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (hmem a ha) (hmem b hb)
  rw [hsq, Ideal.mem_bot] at hmul
  rw [RingHom.mem_ker, map_mul]
  exact hmul

/-- **The `Λ`-algebra map `P/J² ⟶ A'` over `A` of the proof of 07YY**, the descent of the
lift of the generators along the quotient by `J²`. -/
public def infinitesimalLift (P : Algebra.Generators Λ A ι) {A' : Type u} [CommRing A']
    (q : A' →+* A) (hq : Function.Surjective q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) (hsq : RingHom.ker q ^ 2 = ⊥) :
    P.toExtension.infinitesimal.Ring →+* A' :=
  Ideal.Quotient.lift (P.toExtension.ker ^ 2) (presentationLift P q hq f)
    fun _ ha => ker_sq_le_ker_presentationLift P q hq f hqf hsq ha

/-- The map `P/J² ⟶ A'` lies over `A`. -/
public theorem comp_infinitesimalLift (P : Algebra.Generators Λ A ι) {A' : Type u}
    [CommRing A'] (q : A' →+* A) (hq : Function.Surjective q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) (hsq : RingHom.ker q ^ 2 = ⊥) :
    q.comp (infinitesimalLift P q hq f hqf hsq) =
      algebraMap P.toExtension.infinitesimal.Ring A := by
  refine RingHom.ext fun y => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h := P.toExtension.toInfinitesimal.algebraMap_toRingHom g
  rw [Algebra.algebraMap_self, RingHom.id_apply] at h
  show q (presentationLift P q hq f g) = _
  rw [presentationLift_spec P q hq f hqf]
  exact h.symm

/-- The map `P/J² ⟶ A'` lies over the base `Λ`. -/
public theorem infinitesimalLift_comp_infinitesimalBaseMap (P : Algebra.Generators Λ A ι)
    {A' : Type u} [CommRing A'] (q : A' →+* A) (hq : Function.Surjective q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) (hsq : RingHom.ker q ^ 2 = ⊥) :
    (infinitesimalLift P q hq f hqf hsq).comp (infinitesimalBaseMap P.toExtension) = f := by
  have h : ∀ r : Λ, MvPolynomial.eval₂Hom f (fun i => (hq (P.val i)).choose)
      (algebraMap Λ P.Ring r) = f r := fun r => by simp
  exact RingHom.ext fun r => h r

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- **The morphism `(x, A' → A) → (x, P/J² → A)` of square-zero thickenings** attached to a
ring map `Λ ⟶ A'` over `A`: the infinitesimal extension of a presentation maps to every
square-zero thickening of `Spec A` that lies over the affine open of the base. -/
public def infinitesimalToThickeningHom (P : Algebra.Generators Λ A ι)
    (hE : B.Contains (Spec (.of P.Ring))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS)
    {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')
    (f : Λ →+* A')
    (hfS : Spec.map (CommRingCat.ofHom f) ≫ affineOpen = B.inclusion.map D.toS')
    (hqf : D.q.comp f = algebraMap Λ A) :
    SquareZeroThickening.Hom
      (infinitesimalThickening B S hS toS hA P.toExtension hE affineOpen hfact) D :=
  thickeningHom B S hS toS hA _ D
    (infinitesimalLift P D.q D.squareZeroSurjection.1 f hqf D.squareZeroSurjection.2)
    (comp_infinitesimalLift P D.q D.squareZeroSurjection.1 f hqf
      D.squareZeroSurjection.2)
    (by
      have hcomp : CommRingCat.ofHom (infinitesimalBaseMap P.toExtension) ≫
          CommRingCat.ofHom (infinitesimalLift P D.q D.squareZeroSurjection.1 f hqf
            D.squareZeroSurjection.2) = CommRingCat.ofHom f := by
        rw [← CommRingCat.ofHom_comp, infinitesimalLift_comp_infinitesimalBaseMap]
      change Spec.map (CommRingCat.ofHom (infinitesimalLift P D.q
          D.squareZeroSurjection.1 f hqf D.squareZeroSurjection.2)) ≫
        Spec.map (CommRingCat.ofHom (infinitesimalBaseMap P.toExtension)) ≫ affineOpen =
          B.inclusion.map D.toS'
      rw [← Category.assoc, ← Spec.map_comp, hcomp, hfS])

end Presentation

/-! ### The derived tensor product of the triangle of a presentation -/

section DerivedTensorTriangle

variable {A : Type u} [CommRing A]

/-- The distinguished triangle of the naive cotangent complex of a presentation, tensored
with `K`: for a two-term complex `d : N ⟶ M` of `A`-modules the triangle
`K ⊗ᴸ M[0] ⟶ K ⊗ᴸ (N ⟶ M) ⟶ K ⊗ᴸ N[-1] ⟶ (K ⊗ᴸ M[0])⟦1⟧`. -/
public def derivedTensorTwoTermTriangle (K : DerivedCategory (ModuleCat.{u} A))
    (T : TwoTerm.{u, u, u} A) : Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  (CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.obj
    (twoTermComplexTriangle T)

/-- The tensored triangle is distinguished, the derived tensor product being an exact functor
of triangulated categories. -/
public theorem derivedTensorTwoTermTriangle_distinguished
    (K : DerivedCategory (ModuleCat.{u} A)) (T : TwoTerm.{u, u, u} A) :
    derivedTensorTwoTermTriangle K T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) :=
  (CochainComplex.DerivedTensor.derivedTensorProduct K).map_distinguished _
    (twoTermComplexTriangle_distinguished T)

/-- The connecting map `H¹(K ⊗ᴸ N[-1]) ⟶ H²(K ⊗ᴸ M[0])` of the tensored triangle; for the
naive cotangent complex of a presentation it is the map `H²(K ⊗ᴸ J/J²) ⟶ H²(K ⊗ᴸ Ω_{P/Λ} ⊗ A)`
of the conormal sequence. -/
public abbrev derivedTensorTwoTermδ (K : DerivedCategory (ModuleCat.{u} A))
    (T : TwoTerm.{u, u, u} A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
        (derivedTensorTwoTermTriangle K T).obj₃ ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 2).obj
        (derivedTensorTwoTermTriangle K T).obj₁ :=
  DerivedCategory.HomologySequence.δ (derivedTensorTwoTermTriangle K T) 1 2 (by omega)

/-- **A class on the conormal module killed by the connecting map comes from the two-term
complex.** This is the long exact sequence step of the proof of 07YY: since `o_x(P/J²)` dies in
`H²(K ⊗ᴸ Ω_{P/Λ} ⊗_P A)` it is the image of a class in `H¹(K ⊗ᴸ NL(α))`. -/
public theorem exists_of_derivedTensorTwoTermδ_eq_zero (K : DerivedCategory (ModuleCat.{u} A))
    (T : TwoTerm.{u, u, u} A)
    (c : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
      (derivedTensorTwoTermTriangle K T).obj₃)
    (hc : derivedTensorTwoTermδ K T c = 0) :
    ∃ ξ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
      (derivedTensorTwoTermTriangle K T).obj₂,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
        (derivedTensorTwoTermTriangle K T).mor₂ ξ = c :=
  (ShortComplex.moduleCat_exact_iff _).1
    (DerivedCategory.HomologySequence.exact₃ (derivedTensorTwoTermTriangle K T)
      (derivedTensorTwoTermTriangle_distinguished K T) 1 2 (by omega)) c hc

/-- **Two classes on the two-term complex with the same image on the conormal module differ by
a class on the degree-zero term.** This is what makes the class of the proof of 07YY well
defined up to an element of `H¹(K ⊗ᴸ Ω_{P/Λ} ⊗_P A)`. -/
public theorem exists_of_derivedTensorTwoTerm_mor₂_eq_zero
    (K : DerivedCategory (ModuleCat.{u} A)) (T : TwoTerm.{u, u, u} A)
    (ξ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
      (derivedTensorTwoTermTriangle K T).obj₂)
    (hξ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
      (derivedTensorTwoTermTriangle K T).mor₂ ξ = 0) :
    ∃ η : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
      (derivedTensorTwoTermTriangle K T).obj₁,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
        (derivedTensorTwoTermTriangle K T).mor₁ η = ξ :=
  (ShortComplex.moduleCat_exact_iff _).1
    (DerivedCategory.HomologySequence.exact₂ (derivedTensorTwoTermTriangle K T)
      (derivedTensorTwoTermTriangle_distinguished K T) 1) ξ hξ

end DerivedTensorTriangle

/-! ### Vanishing of the obstruction of the pushout algebra -/

section ObstructionVanishing

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A] {ι : Type u}
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)

/-- A square-zero thickening over the affine open of the base whose surjection admits a
section over the base carries no obstruction. -/
public theorem obstruction_thickeningOverBase_eq_zero (A' : Type u) [CommRing A']
    (q : A' →+* A) (hq : IsDeformationSituation q) (hA' : B.Contains (Spec (.of A')))
    (g : Λ →+* A') (hg : q.comp g = algebraMap Λ A) (s : A →+* A')
    (hsg : s.comp (algebraMap Λ A) = g) (hs : q.comp s = RingHom.id A) :
    sit.obstruction A' (thickeningOverBase B S hS toS hA A' q hq hA' g hg
        sit.affineOpen sit.factorization) = 0 :=
  obstruction_eq_zero_of_retraction Λ A B S hS toS hA X p sit A' _
    (thickeningOverBaseRetraction B S hS toS hA A' q hq hA' g hg sit.affineOpen
      sit.factorization s hsg)
    (arrow_comp_thickeningOverBaseRetraction B S hS toS hA A' q hq hA' g hg sit.affineOpen
      sit.factorization s hsg hs)

/-- **The pushout algebra of a presentation carries no obstruction**, `o_x(C) = 0`: the class
of `f ∈ P` goes to the class of `(f, df)`, which is a section of `C ⟶ A` over the base, so `x`
lifts to `Spec C` by pulling back along it. -/
public theorem obstruction_cotangentPushout_eq_zero (E : Algebra.Extension.{u} Λ A)
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) :
    sit.obstruction (cotangentPushout E)
        (cotangentPushoutThickening B S hS toS hA E hC sit.affineOpen sit.factorization) = 0 :=
  obstruction_thickeningOverBase_eq_zero Λ A B S hS toS hA X p sit (cotangentPushout E)
    (cotangentPushoutProj E) (isDeformationSituation_cotangentPushout E) hC
    (cotangentPushoutBaseMap E) (cotangentPushoutBaseMap_spec E) (cotangentPushoutSection E)
    (cotangentPushoutSection_comp_algebraMap E) (cotangentPushoutProj_comp_section E)

/-- **The obstruction of `P/J²` dies on the cotangent space of the presentation**: its image
under the map of kernels of `P/J² ⟶ C` is the obstruction of `C`, which vanishes. -/
public theorem map_obstruction_infinitesimal_eq_zero (E : Algebra.Extension.{u} Λ A)
    (hE : B.Contains (Spec (.of E.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) :
    (derivedCohomology A sit.K 2).map
        (infinitesimalToPushoutHom B S hS toS hA E hE hC sit.affineOpen
          sit.factorization).kernelMap
        (sit.obstruction E.infinitesimal.Ring
          (infinitesimalThickening B S hS toS hA E hE sit.affineOpen
            sit.factorization)) = 0 := by
  rw [sit.obstructionNatural _ _ _ _
    (infinitesimalToPushoutHom B S hS toS hA E hE hC sit.affineOpen sit.factorization)]
  exact obstruction_cotangentPushout_eq_zero Λ A B S hS toS hA X p sit E hC

/-- **The obstruction of every deformation situation is the image of the obstruction of
`P/J²`.** Any square-zero thickening of `Spec A` receives the infinitesimal extension of a
presentation of `A` over `Λ`, through a ring map over `A` and over the affine open of the base,
and obstruction elements are carried to obstruction elements. -/
public theorem exists_obstruction_eq_map_obstruction_infinitesimal
    (P : Algebra.Generators Λ A ι) (hE : B.Contains (Spec (.of P.Ring)))
    {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A') :
    ∃ (f : Λ →+* A')
      (hfS : Spec.map (CommRingCat.ofHom f) ≫ sit.affineOpen = B.inclusion.map D.toS')
      (hqf : D.q.comp f = algebraMap Λ A),
      (derivedCohomology A sit.K 2).map
          (infinitesimalToThickeningHom B S hS toS hA P hE sit.affineOpen sit.factorization
            D f hfS hqf).kernelMap
          (sit.obstruction P.toExtension.infinitesimal.Ring
            (infinitesimalThickening B S hS toS hA P.toExtension hE sit.affineOpen
              sit.factorization)) = sit.obstruction A' D := by
  obtain ⟨f, hfS, hqf⟩ :=
    exists_baseRingHom B S hS toS hA D sit.affineOpen sit.openImmersion sit.factorization
  exact ⟨f, hfS, hqf, sit.obstructionNatural _ _ _ _
    (infinitesimalToThickeningHom B S hS toS hA P hE sit.affineOpen sit.factorization D f
      hfS hqf)⟩

end ObstructionVanishing

/-! ### The extension class of a thickening from an arbitrary presentation -/

section ExtensionClassThickening

variable (A' A : Type u) [CommRing A'] [CommRing A] [Algebra A' A]

/-- The two-term complex of the presentation of `A` given by a surjection `A' → A`. -/
private def surjectionTwoTerm (hq : Function.Surjective (algebraMap A' A)) :
    TwoTerm.{u, u, u} A where
  X₁ := (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).Cotangent
  X₀ := (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).CotangentSpace
  d := (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).cotangentComplex

/-- The comparison chain map from the canonical presentation of `A` over `A'`. -/
private def surjectionChainMap (hq : Function.Surjective (algebraMap A' A)) :
    ChainMap (nlRestrict A (canonicalGenerators A' A)) (surjectionTwoTerm A' A hq) where
  f₁ := Algebra.Extension.Cotangent.map (Algebra.Extension.defaultHom A' A
    (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq))
  f₀ := Algebra.Extension.CotangentSpace.map (Algebra.Extension.defaultHom A' A
    (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq))
  comm := by
    ext x
    exact (Algebra.Extension.CotangentSpace.map_cotangentComplex _ x).symm

/-- The projection of the two-term complex of a square-zero surjection onto its kernel. -/
private def kernelChainMap (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hq hsq
    twoTermComplex (surjectionTwoTerm A' A hq) ⟶
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj
        (ModuleCat.of A (RingHom.ker (algebraMap A' A))) := by
  letI := Stacks.Smooth.kerModule hq hsq
  refine HomologicalComplex.mkHomToSingle
    ((HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (surjectionTwoTerm A' A hq).d)
        upIntRelNegOneZero).hom ≫
      ModuleCat.ofHom (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap) ?_
  intro i hi
  have hi' : i + 1 = -1 := hi
  exact (HomologicalComplex.isZero_double_X _ upIntRelNegOneZero i (by omega)
    (by omega)).eq_of_src _ _

/-- The component of `kernelChainMap` in degree `-1`, through the identifications of the
components of the two-term and single complexes there. -/
private theorem kernelChainMap_f_neg_one (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hq hsq
    (kernelChainMap A' A hq hsq).f (-1) =
      ((HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (surjectionTwoTerm A' A hq).d)
          upIntRelNegOneZero).hom ≫
        ModuleCat.ofHom (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) _).inv :=
  HomologicalComplex.mkHomToSingle_f ..

end ExtensionClassThickening

section ExtensionClassPresentation

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A] {ι : Type u}

/-- The comparison of a presentation of `A` over `Λ` with a square-zero thickening. -/
private def presentationToThickening (P : Algebra.Generators Λ A ι)
    (φ : P.Hom (canonicalGenerators Λ A)) {A' : Type u} [CommRing A'] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] (hq : Function.Surjective (algebraMap A' A)) :
    P.toExtension.Hom (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq) :=
  (Algebra.Extension.defaultHom A' A
      (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq)).comp
    (((canonicalGenerators Λ A).defaultHom (canonicalGenerators A' A)).toExtensionHom.comp
      φ.toExtensionHom)

/-- A lift of a presentation into a square-zero thickening, as a hom of extensions. -/
private def liftToThickening (P : Algebra.Generators Λ A ι) {A' : Type u} [CommRing A']
    [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    (hq : Function.Surjective (algebraMap A' A)) (ψ : P.toExtension.Ring →+* A')
    (hψ : ∀ x, algebraMap A' A (ψ x) = algebraMap P.toExtension.Ring A x)
    (hψΛ : ∀ r : Λ, ψ (algebraMap Λ P.toExtension.Ring r) = algebraMap Λ A' r) :
    P.toExtension.Hom (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq) where
  toRingHom := ψ
  toRingHom_algebraMap := hψΛ
  algebraMap_toRingHom := hψ

/-- The homotopy between the two conormal maps attached to two lifts of a presentation. -/
private def thickeningHomotopyHom (P : Algebra.Generators Λ A ι)
    (φ : P.Hom (canonicalGenerators Λ A)) {A' : Type u} [CommRing A'] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) (ψ : P.toExtension.Ring →+* A')
    (hψ : ∀ x, algebraMap A' A (ψ x) = algebraMap P.toExtension.Ring A x)
    (hψΛ : ∀ r : Λ, ψ (algebraMap Λ P.toExtension.Ring r) = algebraMap Λ A' r) :
    letI := Stacks.Smooth.kerModule hq hsq
    ModuleCat.of A P.toExtension.CotangentSpace ⟶
      ModuleCat.of A (RingHom.ker (algebraMap A' A)) :=
  letI := Stacks.Smooth.kerModule hq hsq
  ModuleCat.ofHom ((squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap ∘ₗ
    Algebra.Extension.Hom.sub (presentationToThickening P φ hq)
      (liftToThickening P hq ψ hψ hψΛ))

/-- The extension class of a square-zero thickening, computed from an arbitrary presentation:
the comparison isomorphism followed by `NL_{A/Λ} ⟶ I[1]` is the projection of the two-term
complex onto its conormal module followed by the map `J/J² ⟶ I` induced by a lift of the
presentation into the thickening. -/
public theorem derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass
    (P : Algebra.Generators Λ A ι) (φ : P.Hom (canonicalGenerators Λ A))
    {A' : Type u} [CommRing A'] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (ψ : P.toExtension.Ring →+* A')
    (hψ : ∀ x, algebraMap A' A (ψ x) = algebraMap P.toExtension.Ring A x)
    (hψΛ : ∀ r : Λ, ψ (algebraMap Λ P.toExtension.Ring r) = algebraMap Λ A' r)
    (k : letI := Stacks.Smooth.kerModule hq hsq
      P.toExtension.Cotangent →ₗ[A] RingHom.ker (algebraMap A' A))
    (hk : ∀ x : P.toExtension.ker,
      (k (Algebra.Extension.Cotangent.mk x)).1 = ψ x.1) :
    letI := Stacks.Smooth.kerModule hq hsq
    (derivedNaiveCotangentComplexIso Λ A P φ).hom ≫ cotangentExtensionClass Λ A' A hq hsq =
      DerivedCategory.Q.map (twoTermProjection (ModuleCat.ofHom (nlRestrict A P).d)) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map (ModuleCat.ofHom k) := by
  have hk' : ∀ c : P.toExtension.Cotangent,
      (squareZeroKernelCotangentEquiv A' A hq hsq).symm
        (Algebra.Extension.Cotangent.map (liftToThickening P hq ψ hψ hψΛ) c) = k c := by
    intro c
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
    rw [LinearEquiv.symm_apply_eq]
    show Algebra.Extension.Cotangent.map (liftToThickening P hq ψ hψ hψΛ)
        (Algebra.Extension.Cotangent.mk x) =
      Algebra.Extension.Cotangent.mk (k (Algebra.Extension.Cotangent.mk x))
    rw [Algebra.Extension.Cotangent.map_mk]
    exact DFunLike.congr_arg Algebra.Extension.Cotangent.mk (Subtype.ext (hk x).symm)
  have hmaps : ∀ c : P.toExtension.Cotangent,
      Algebra.Extension.Cotangent.map (presentationToThickening P φ hq) c =
        Algebra.Extension.Cotangent.map (Algebra.Extension.defaultHom A' A
            (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq))
          (Algebra.Extension.Cotangent.map
            ((canonicalGenerators Λ A).defaultHom (canonicalGenerators A' A)).toExtensionHom
            (Algebra.Extension.Cotangent.map φ.toExtensionHom c)) := by
    intro c
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
    rfl
  have key : ∀ c : P.toExtension.Cotangent,
      Algebra.Extension.Cotangent.map (presentationToThickening P φ hq) c =
        Algebra.Extension.Hom.sub (presentationToThickening P φ hq)
            (liftToThickening P hq ψ hψ hψΛ) (P.toExtension.cotangentComplex c) +
          Algebra.Extension.Cotangent.map (liftToThickening P hq ψ hψ hψΛ) c := by
    intro c
    have hd := congrArg (fun m : P.toExtension.Cotangent →ₗ[A] _ => m c)
      (Algebra.Extension.Cotangent.map_sub_map (presentationToThickening P φ hq)
        (liftToThickening P hq ψ hψ hψΛ))
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at hd
    rw [← hd]
    abel
  have hcore : ∀ c : P.toExtension.Cotangent,
      (squareZeroKernelCotangentEquiv A' A hq hsq).symm
          (Algebra.Extension.Cotangent.map (Algebra.Extension.defaultHom A' A
              (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq))
            (Algebra.Extension.Cotangent.map
              ((canonicalGenerators Λ A).defaultHom (canonicalGenerators A' A)).toExtensionHom
              (Algebra.Extension.Cotangent.map φ.toExtensionHom c))) =
        (squareZeroKernelCotangentEquiv A' A hq hsq).symm
            (Algebra.Extension.Hom.sub (presentationToThickening P φ hq)
              (liftToThickening P hq ψ hψ hψΛ) (P.toExtension.cotangentComplex c)) + k c := by
    intro c
    rw [← hmaps c, key c, map_add, hk']
  have hL : (derivedNaiveCotangentComplexIso Λ A P φ).hom ≫
        cotangentExtensionClass Λ A' A hq hsq =
      DerivedCategory.Q.map (twoTermHom (nlMap P (canonicalGenerators Λ A) φ) ≫
        twoTermHom (nlMapBase A (canonicalGenerators Λ A) (canonicalGenerators A' A)
          ((canonicalGenerators Λ A).defaultHom (canonicalGenerators A' A))) ≫
        twoTermHom (surjectionChainMap A' A hq) ≫ kernelChainMap A' A hq hsq) := by
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    rfl
  have hR : ∀ {X Y : ModuleCat.{u} A} (g : X ⟶ Y),
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map g =
        DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} A)
          (ComplexShape.up ℤ) (-1)).map g) := fun _ => rfl
  rw [hL, hR, ← Functor.map_comp]
  refine DerivedCategory.Q_map_eq_of_homotopy (C := ModuleCat.{u} A) ?_
  refine
    { hom := fun i j => if hij : i = 0 ∧ j = -1 then
        eqToHom (by rw [hij.1]) ≫
          (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (nlRestrict A P).d)
            upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫
          thickeningHomotopyHom P φ hq hsq ψ hψ hψΛ ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) _).inv ≫
          eqToHom (by rw [hij.2])
      else 0
      zero := ?_
      comm := ?_ }
  · intro i j hr
    rw [dite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact absurd rfl hr
  · intro i
    by_cases hi : i = -1
    · subst hi
      rw [dNext_eq _ upIntRelNegOneZero,
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by decide),
        HomologicalComplex.double_d _ upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero]
      have hne2 : ¬((-1 : ℤ) = 0 ∧ (-2 : ℤ) = -1) := by omega
      simp only [HomologicalComplex.comp_f, twoTermHom_f_neg_one, kernelChainMap_f_neg_one,
        twoTermProjection_f_neg_one, HomologicalComplex.single_map_f_self, dite_eq_left,
        dite_eq_right hne2, eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
        Iso.inv_hom_id_assoc, Limits.zero_comp, add_zero, and_self]
      rw [← Preadditive.comp_add, cancel_epi]
      simp only [← Category.assoc]
      rw [← Preadditive.add_comp, cancel_mono]
      let := Stacks.Smooth.kerModule hq hsq
      exact ModuleCat.hom_ext (LinearMap.ext fun c => hcore c)
    · by_cases hi0 : i = 0
      · subst hi0
        exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1) _ 0
          (by omega)).eq_of_tgt _ _
      · exact (HomologicalComplex.isZero_double_X _ upIntRelNegOneZero i hi
          hi0).eq_of_src _ _

open TensorProduct in
/-- `Algebra.Extension.toKaehler` is natural in the presentation: composing the induced map
on cotangent spaces along a morphism of presentations with the target's `toKaehler` recovers
the source's `toKaehler`. This is what makes the comparison with an arbitrary presentation
commute with the projection of the naive cotangent complex onto the module of
differentials. -/
private theorem toKaehler_comp_cotangentSpaceMap {ι' : Type u} (P : Algebra.Generators Λ A ι)
    (P' : Algebra.Generators Λ A ι') (φ : P.Hom P') :
    P'.toExtension.toKaehler ∘ₗ Algebra.Extension.CotangentSpace.map φ.toExtensionHom =
      P.toExtension.toKaehler := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at *; rw [hx, hy]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add y z hy hz => simp only [map_add, tmul_add, LinearMap.comp_apply] at *; rw [hy, hz]
    | tmul y z =>
      simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', LinearMap.comp_apply,
        Algebra.Extension.CotangentSpace.map_tmul, Algebra.Extension.Hom.toAlgHom_apply,
        Algebra.Extension.toKaehler, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.map_D]
      congr 2
      exact φ.toExtensionHom.algebraMap_toRingHom z

/-- The presentation-level comparison `NL(P) ⟶ Ω_{A/Λ}[0]`: the projection of the two-term
complex of an arbitrary presentation `P` of `A` over `Λ` onto the module of differentials,
given in degree `0` by `Algebra.Extension.toKaehler`. -/
public def presentationToDifferentials (P : Algebra.Generators Λ A ι) :
    twoTermComplex (nlRestrict A P) ⟶
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (differentialsModule Λ A) :=
  HomologicalComplex.mkHomFromDouble upIntRelNegOneZero (by omega : (-1 : ℤ) ≠ 0) 0
    (ModuleCat.ofHom P.toExtension.toKaehler ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (differentialsModule Λ A)).inv)
    (by
      have h0 : ModuleCat.ofHom (nlRestrict A P).d ≫ ModuleCat.ofHom P.toExtension.toKaehler
          = 0 :=
        ModuleCat.hom_ext <| LinearMap.ext fun z =>
          P.toExtension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero z
      rw [Limits.zero_comp, ← Category.assoc, h0, Limits.zero_comp])
    (fun k _ => by rw [HomologicalComplex.single_obj_d, Limits.comp_zero])

/-- The canonical morphism `NL_{A/Λ} ⟶ Ω_{A/Λ}[0]`, computed from an arbitrary presentation:
the comparison isomorphism followed by `naiveCotangentToDifferentials` is the presentation-level
projection onto the module of differentials. -/
public theorem derivedNaiveCotangentComplexIso_hom_comp_naiveCotangentToDifferentials
    (P : Algebra.Generators Λ A ι) (φ : P.Hom (canonicalGenerators Λ A)) :
    (derivedNaiveCotangentComplexIso Λ A P φ).hom ≫ naiveCotangentToDifferentials Λ A =
      DerivedCategory.Q.map (presentationToDifferentials P) := by
  have hL : (derivedNaiveCotangentComplexIso Λ A P φ).hom ≫ naiveCotangentToDifferentials Λ A =
      DerivedCategory.Q.map
        (show twoTermComplex (nlRestrict A P) ⟶
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
              (differentialsModule Λ A)
          from twoTermHom (nlMap P (canonicalGenerators Λ A) φ) ≫
            naiveCotangentToDifferentialsChainMap Λ A) :=
    (Functor.map_comp DerivedCategory.Q (twoTermHom (nlMap P (canonicalGenerators Λ A) φ))
      (naiveCotangentToDifferentialsChainMap Λ A)).symm
  rw [hL]
  congr 1
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, twoTermHom_f_zero]
  simp only [naiveCotangentToDifferentialsChainMap, presentationToDifferentials,
    HomologicalComplex.mkHomFromDouble_f₁, Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  have hf₀ : (nlMap P (canonicalGenerators Λ A) φ).f₀ =
      Algebra.Extension.CotangentSpace.map φ.toExtensionHom := rfl
  rw [hf₀]
  exact DFunLike.congr_fun (toKaehler_comp_cotangentSpaceMap P (canonicalGenerators Λ A) φ) _

end ExtensionClassPresentation

end Deformation.Artin

end
